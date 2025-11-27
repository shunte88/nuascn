/*
 *  main.rs
 * 
 *  nuascn - systematic scraper
 *      (c) 2025-26 Stuart Hunter (shunte88)
 *
 *      TODO:
 *
 *      This program is free software: you can redistribute it and/or modify
 *      it under the terms of the GNU General Public License as published by
 *      the Free Software Foundation, either version 3 of the License, or
 *      (at your option) any later version.
 *
 *      This program is distributed in the hope that it will be useful,
 *      but WITHOUT ANY WARRANTY; without even the implied warranty of
 *      MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *      GNU General Public License for more details.
 *
 *      See <http://www.gnu.org/licenses/> to get a copy of the GNU General
 *      Public License.
 *
 */

#[allow(dead_code)]
#[allow(unused_imports)]
use anyhow::{Context, Result};
use log::{info, error, warn, LevelFilter};
use log4rs::append::console::ConsoleAppender;
use log4rs::append::file::FileAppender;
use log4rs::config::{Appender, Config, Root};
use log4rs::encode::pattern::PatternEncoder;
use rand_agents::user_agent;
use std::{
    collections::{HashMap, HashSet}, 
    env, 
    error::Error,
    fs, 
    fs::{File, OpenOptions}, 
    io::{BufRead, BufReader, Cursor, Write},
    path::{Path, PathBuf}, 
    time::Duration
};
use futures::future::join_all;
use chrono::{DateTime, FixedOffset, Utc, Local};
use chrono::Timelike;

use std::io::Seek;
use std::ops::Range;
use futures::{stream, StreamExt};
use reqwest::{Client, StatusCode};
use reqwest::header::{HeaderMap, HeaderValue, CONTENT_LENGTH, RANGE};
use rss::{Channel, ChannelBuilder, Item, ItemBuilder};
use scraper::{Html, Selector};
use tokio::time::{error::Elapsed, sleep};
use url::Url;
use regex::Regex;
use serde_json::Value;
use tokio::{process::Command, sync::mpsc};
use tokio::fs::create_dir_all;

/// Simple boxed error type
type BoxResult<T> = Result<T, Box<dyn Error + Send + Sync>>;

const INTEREST_FILE: &str = "tvshows.list";
const KV_PATH: &str = ".cache/seen_shows.db";
const BASE_FOLDER: &str = "/home/stuart/Downloads";
const CHUNK_SIZE: u64 = 1024 * 1024;
const BASE_URL: &str = "https://rapidmoviez.com/feature/x265";
const SHOWS_RSS: &str = "https://rapidmoviez.com/feed/s";
const MOVIE_RSS: &str = "https://rapidmoviez.com/feed/m";
const NF_LINK: &str = "NITROFLARE";
const OUTPUT_FILE: &str = "feed.rss";
const MAX_CONCURRENCY: usize = 8;
const REQUEST_TIMEOUT_SECS: u64 = 15;
const MAX_RETRIES: u32 = 3;
const VIDEO_RESOLUTION_1080: &str = "1080";
const VIDEO_RESOLUTION_720: &str = "720ZZZ";    // munged
const VIDEO_RESOLUTION_2160: &str = "2160ZZZ";  // munged
const SPECIAL_CASES: &[&str] = &[
    "USA","FBI","BBC","US","AU","PL","IE","NZ","FR","DE","JP","UK",
    "QI","XL","SAS","RAF","WWII","WPC","LOL","VI","VII","VIII","VIIII","IX","II","III","IV",
    "DCI","HD","W1A","HBO","100K"
];
const LOG_APPENDER_STDOUT: &str = "stdout";
const LOG_APPENDER_FILE: &str = "file";
const LOG_PATTERN: &str = "{d(%Y-%m-%d %H:%M:%S)(utc)} {h({l})} {m}{n}";

/// FILETYPES inclusion
const FILETYPES: &[&str] = &[
    ".mkv", ".mp4", ".avif", ".m4v",
];

#[derive(Clone, Debug)]
struct ProcessEntry {
    key: String,
    title: String,
    rerun: bool,
    show_name: String,
    folder: String,
    sanitized_name: String,
    pub extention: String,
    pub link: String,    // RM page
    pub nf_view: String, // NF view -> file_id
    pub file_id: String, // NF file details (supports multiple file_id)
    pub nf_down: String, // NF downloadable by file_id (singular)
}

struct Aria2cRerun {
    store: PathBuf,
    file: File,
    commands: Vec<String>,
}

impl Aria2cRerun {

    fn init(filename: String) -> BoxResult<Self> {
        let store = filename.into();
        let file = OpenOptions::new()
            .append(true)
            .write(true)
            .create(true)
            .open(&store)?;
        let commands: Vec<String> = Vec::new();

        let ret = Self {
            store,
            file,
            commands,
        };
        Ok(ret)
    }

    fn load_list(&mut self) -> BoxResult<()> {
        // Ensure file exists
        let file_for_read = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(&self.store)?;

        let reader = BufReader::new(file_for_read);

        // Load existing entries
        for line in reader.lines() {
            let line = line?;
            if line.trim().is_empty() || line.starts_with("#") {
                continue;
            }
            self.commands.push(line.clone());
        }

        Ok(())
    }

    fn write_rerun(&mut self, command: String) -> BoxResult<()> {
        if self.commands.contains(&command.clone()) {
            return Ok(());
        }
        writeln!(self.file, "{}", command.clone())?;
        self.file.flush()?;
        self.commands.push(command.clone());
        Ok(())
    }

}


struct Aria2cResult {
    good: bool,
    key: String,
}

impl Aria2cResult {

    fn init(key: String) -> BoxResult<Self> {
        let good = false;
        Ok(Self {
            good,
            key
        })
    }
}

struct KvStore {
    store: PathBuf,
    map: HashMap<String, String>,
    file: File, // append-only handle
}

impl KvStore {
    /// Open or create the KV store at `strore`.
    /// Format: one entry per line => "key|value\n"
    fn open(store: impl Into<PathBuf>) -> BoxResult<Self> {
        let store = store.into();

        // Ensure file exists
        let file_for_read = OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .open(&store)?;

        let mut map = HashMap::new();
        let reader = BufReader::new(file_for_read);

        // Load existing entries
        for line in reader.lines() {
            let line = line?;
            if line.trim().is_empty() {
                continue;
            }
            // Very simple format: key|value
            if let Some((k, v)) = line.split_once('|') {
                map.insert(k.to_string(), v.to_string());
            }
        }

        // Re-open in append mode for writing
        let file_for_append = OpenOptions::new()
            .append(true)
            .write(true)
            .create(true)
            .open(&store)?;

        Ok(KvStore {
            store,
            map,
            file: file_for_append,
        })
    }

    fn get(&self, key: &str) -> Option<&str> {
        self.map.get(key).map(|s| s.as_str())
    }

    fn insert(&mut self, key: &str, value: &str) -> BoxResult<()> {
        // Only write if it's new
        if self.map.contains_key(key) {
            return Ok(());
        }
        writeln!(self.file, "{}|{}", key, value)?;
        self.file.flush()?;
        self.map.insert(key.to_string(), value.to_string());
        Ok(())
    }

}

#[derive(Clone, Copy, Debug)]
enum Source {
    Html,
    RssShows,
    RssMovies,
}

impl Source {
    fn tag(&self) -> &'static str {
        match self {
            Source::Html => "HTML",
            Source::RssShows => "RSS-SHOW",
            Source::RssMovies => "RSS-MOVIE",
        }
    }
}

struct FeedItem {
    title: String,
    link: String,
    pub_date: DateTime<FixedOffset>, // normalized, parsed
    pub_date_str: String,            // RFC 2822 string used in RSS
    source: Source,
}

struct SceneDown {
    client: Client,
    ux: String,
    px: String,
    pub ntf_download_link: String,
    max_retries: u32,
}

impl SceneDown {

    fn init(ux: &str, px: &str) -> BoxResult<Self> {

        const NTFURL_API: &str = "https://nitroflare.com/api/v2";
        let ntf_download_link: String = format!("{NTFURL_API}/getDownloadLink");
        let agent = user_agent();
        let client = Client::builder()
            .user_agent(agent)
            .timeout(Duration::from_secs(20))
            .build()?;

        Ok(Self {
            client,
            ux: ux.to_string().clone(),
            px: px.to_string().clone(),
            ntf_download_link: ntf_download_link.clone(),
            max_retries: 3
        })
    }

    fn premium_params(&self) -> Vec<(&str, &str)> {
        vec![("user", self.ux.as_str()), ("premiumKey", self.px.as_str())]
    }

    async fn get_json_with_retries(
        &self,
        url: &str,
        params: &[(&str, &str)],
    ) -> BoxResult<Value> {
        let mut attempt = 0;
        loop {
            attempt += 1;
            let res = self
                .client
                .get(url)
                .query(params)
                .send()
                .await;

            match res {
                Ok(resp) => {
                    let status = resp.status();
                    if !status.is_success() {
                        if attempt >= self.max_retries {
                            return Err(format!(
                                "Non-success status {} for {} after {} attempts",
                                status, url, attempt
                            )
                            .into());
                        }
                    } else {
                        match resp.json::<Value>().await {
                            Ok(j) => return Ok(j),
                            Err(e) => {
                                if attempt >= self.max_retries {
                                    return Err(format!(
                                        "JSON decode error for {} after {} attempts: {}",
                                        url, attempt, e
                                    )
                                    .into());
                                } else {
                                    warn!(
                                        "JSON error for {} attempt {} – retrying: {}",
                                        url, attempt, e
                                    );
                                }
                            }
                        }
                    }
                }
                Err(e) => {
                    if attempt >= self.max_retries {
                        return Err(format!(
                            "Request error for {} after {} attempts: {}",
                            url, attempt, e
                        )
                        .into());
                    } else {
                        warn!(
                            "Request error for {} attempt {} – retrying: {}",
                            url, attempt, e
                        );
                    }
                }
            }

            let delay_ms = 500 * attempt as u64;
            sleep(Duration::from_millis(delay_ms)).await;
        }
    }

    /// Optional: sanity-check premium key once, similar to your KEYINFO call
    /// overhead - not needed
    /*
    async fn check_premium(&self) -> BoxResult<()> {

        let params = self.premium_params();
        let j = self.get_json_with_retries(self.ntf_keyinfo.clone().as_str(), &params).await?;
        if let Some(status) = j.get("result")
            .and_then(|r| r.get("status")
            .and_then(|s| s.as_str())) {
            if status.eq_ignore_ascii_case("success")||status.eq_ignore_ascii_case("active") {
                return Ok(());
            }
        }
        Err(format!("Nitroflare keyinfo reported error: {:?}", j).into())
    }
    */

    ///
    /// `files` is Vec of (Vec<uri>, tag)
    /// Returns Vec of (download_url, destination_path, tag)
    pub async fn get_download(
        &self,
        pm: &ProcessEntry,
    ) -> BoxResult<String> {

        let file_id = pm.file_id.as_str();
        let mut download = String::new();

        /* 

        let _ = self.check_premium().await?;

        // getFileInfo – we mostly use this as a sanity check
        let mut params = self.premium_params();
        let params_fileinfo = [("files", file_id)];
        params.extend_from_slice(&params_fileinfo);
        let j_fileinfo = self
            .get_json_with_retries(self.ntf_fileinfo.clone().as_str(), &params)
            .await?;
        // result->status
        if let Some(status) = j_fileinfo.get("type").and_then(|v| v.as_str()) {
            if !status.eq_ignore_ascii_case("success") {
                warn!(
                    "Fileinfo error for file_id={} status='{}' payload={:?}",
                    file_id, status, j_fileinfo
                );
                return Ok(download);
            }
        }
        */

        // getDownloadLink
        let mut params_dl = self.premium_params();
        params_dl.push(("file", file_id));

        let j_dl = self
            .get_json_with_retries(&self.ntf_download_link.clone().as_str(), &params_dl)
            .await?;

        let result = match j_dl.get("result") {
            Some(r) => r,
            None => {
                warn!(
                    "JSON broken for file_id={}: (payload={:?})",
                    file_id, j_dl
                );
                return Ok(download);
            }
        };

        download = match result.get("url").and_then(|v| v.as_str()) {
            Some(u) if !u.is_empty() => u.to_string(),
            _ => {
                warn!(
                    "JSON missing download url for file_id={}: (payload={:?})",
                    file_id, j_dl
                );
                return Ok(download);
            }
        };

        Ok(download)

    }

}

/// Normalize show name for comparison:
/// - trim
/// - trim leading/trailing '.'
/// - spaces -> '.'
/// - uppercase
fn normalize_show_name(name: &str) -> String {
    name.trim()
        .trim_matches('.')
        .replace(' ', ".")
        .to_ascii_uppercase()
}

/// Derive the "show only" from the sanitized key (without SxxEyy).
/// If SxxEyy is present, use the prefix; otherwise use the whole key.
fn extract_show_from_key(key: &str, re: &Regex) -> String {
    if let Some(caps) = re.captures(key) {
        if let Some(g1) = caps.get(1) {
            return normalize_show_name(g1.as_str());
        }
    }
    normalize_show_name(key)
}

/// shows of interest from tvshows.list
fn load_interest_list(path: &str) -> BoxResult<HashSet<String>> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    let mut set = HashSet::new();

    for line in reader.lines() {
        let line = line?;
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let norm = normalize_show_name(trimmed);
        if !norm.is_empty() {
            set.insert(norm);
        }
    }

    Ok(set)
}

#[tokio::main]
async fn main() -> BoxResult<()> {

    let h = Local::now();  // current time - used here to name the log, and later to drive runtime logic

    let stdout = ConsoleAppender::builder()
        .encoder(Box::new(PatternEncoder::new(LOG_PATTERN)))
        .build();
    let log_file_name = format!("./logs/nuascn.{}.log", h.timestamp());
    let log_file = FileAppender::builder()
        .encoder(Box::new(PatternEncoder::new(LOG_PATTERN)))
        .build(log_file_name)
        .unwrap();

    let config = Config::builder()
        .appender(Appender::builder().build(LOG_APPENDER_STDOUT, Box::new(stdout)))
        .appender(Appender::builder().build(LOG_APPENDER_FILE, Box::new(log_file)))
        .build(
            Root::builder()
                .appender(LOG_APPENDER_STDOUT)
                .appender(LOG_APPENDER_FILE)
                .build(LevelFilter::Info),
        )
        .unwrap();
    log4rs::init_config(config).unwrap();

    let ux = getenv("NTFLR_USERNAME", "");
    if ux.is_empty() {
        error!("NTFLR_USERNAME not set");
        return Ok(());
    }

    let sdx = SceneDown::init(
        ux.clone().as_str(),
        getenv("NTFLR_PREMIUM", "").as_str(),
    ).unwrap();

    let mut urls: Vec<String> = Vec::new();

    // seed urls with user-specified from command line
    if let Some(arg_url) = env::args().nth(1) {
        if arg_url.starts_with("http://") || arg_url.starts_with("https://") {
            urls.push(arg_url);
        }
    }

    // if we don't have a url we synthesize
    if urls.is_empty() {
        // Generate HTML page URLs
        // 21 first outing of the day, 1AM, else 8 pages
        let pages: i32 = if h.hour()==1 {21} else {8};
        urls = build_urls(BASE_URL, pages);
    }

    if urls.is_empty() {
        error!("No URLs generated/specified. Quitting...");
        return Ok(());
    }

    // we create a client that plays nice with lazy 
    // web-masters that are not on top of their certs
    let agent = user_agent();
    let client = Client::builder()
        .user_agent(agent)
        .danger_accept_invalid_certs(true)       // skips cert validation (use only for scraping)
        .danger_accept_invalid_hostnames(true)   // hostname mismatch accepted too
        .timeout(Duration::from_secs(REQUEST_TIMEOUT_SECS))
        .build()?;

    let selector = Selector::parse("a").expect("Selector parse for <a> should never fail");

    // Fetch and process all HTML pages in parallel with bounded concurrency
    let stream = stream::iter(urls.into_iter().map(|url| {

        let client = client.clone();
        let selector = selector.clone();
        let key: &str = "";

        async move {
            match process_page_with_retries(&client, &selector, &url, MAX_RETRIES, false, key, false).await {
                Ok(links) => {
                    if !links.is_empty() {
                        info!("Found {:>2} links for {}", links.len(), url);
                    }
                    links
                }
                Err(_e) => {
                    Vec::new()
                }
            }
        }
    }))
    .buffer_unordered(MAX_CONCURRENCY);

    let mut seen: HashSet<String> = HashSet::new();
    let mut feed_items: Vec<FeedItem> = Vec::new();

    // Collect items from HTML pages
    tokio::pin!(stream);
    while let Some(links) = stream.next().await {
        for (title, href) in links {
            if !seen.insert(href.clone()) {
                continue;
            }

            // HTML has no inherent date: fallback to "now"
            let now_utc = Utc::now();
            let now_fixed: DateTime<FixedOffset> = now_utc.into();
            let pub_date_str = now_fixed.to_rfc2822();

            feed_items.push(FeedItem {
                title,
                link: href,
                pub_date: now_fixed,
                pub_date_str,
                source: Source::Html,
            });
        }
    }

    // ---- Process RSS feeds with same retry + link_matches ----
    let rss_sources = &[(SHOWS_RSS, Source::RssShows), (MOVIE_RSS, Source::RssMovies)];

    for (rss_url, src) in rss_sources {
        match process_rss_with_retries(&client, rss_url, *src, MAX_RETRIES).await {
            Ok(items) => {
                if !items.is_empty() {
                    info!(
                        "Found {} matching RSS items for {}",
                        items.len(),
                        rss_url
                    );
                }

                for item in items {
                    if !seen.insert(item.link.clone()) {
                        continue;
                    }
                    feed_items.push(item);
                }
            }
            Err(e) => {
                error!("Processing RSS with error: {}", e);
            }
        }
    }

    if !feed_items.is_empty() {
        info!("Total unique items before sort: {}", feed_items.len());
    }

    // ---- Normalize & sort chronologically (newest first) ----
    feed_items.sort_by(|a, b| b.pub_date.cmp(&a.pub_date));

    // Latest pub_date for channel-level lastBuildDate (if any)
    let last_build_date = feed_items
        .first()
        .map(|fi| fi.pub_date_str.clone())
        .unwrap_or_else(|| Utc::now().to_rfc2822());

    // Build RSS items with tagged titles and normalized pubDate
    let rss_items: Vec<Item> = feed_items
        .into_iter()
        .map(|fi| {
            let tagged_title = format!("[{}] {}", fi.source.tag(), fi.title);
            ItemBuilder::default()
                .title(Some(tagged_title))
                .link(Some(fi.link))
                .pub_date(Some(fi.pub_date_str))
                .build()
        })
        .collect();

    // Build RSS channel
    let channel = ChannelBuilder::default()
        .title("NF Links o'shunte88")
        .link(BASE_URL)
        .description("We Scene It - We Links It")
        .last_build_date(Some(last_build_date))
        .items(rss_items)
        .build();

    // Write RSS to file
    let mut fileo = File::create(OUTPUT_FILE)?;
    fileo.write_all(channel.to_string().as_bytes())?;

    let file = File::open(OUTPUT_FILE)?;
    let reader = BufReader::new(file);
    let channel = Channel::read_from(reader)?;

    let re_se = season_episode_regex();

    // Load shows-of-interest
    let interest = load_interest_list(INTEREST_FILE)?;

    // lite persistent KV store - yes - a flatfile - sued me
    let mut kv = KvStore::open(KV_PATH)?;

    // Process list: key -> ProcessEntry
    let mut process_map: HashMap<String, ProcessEntry> = HashMap::new();

    // load re-run list
    let mut arr = Aria2cRerun::init("aria_rerun.list".to_string()).unwrap();
    arr.load_list()?;

    let mut work_done = false;
    for cmd in arr.commands {

        // decompose the commmand to put it back on the queue
        let chunks: Vec<&str> = cmd.split(' ').collect();
        work_done = true;
  
        let link = chunks[chunks.len()-1];
        let folder_name = chunks[2];
        let sanitized_name = chunks[4].to_string();
        let ext = if sanitized_name.to_string().ends_with(".mkv"){".mkv"}else{".mp4"};
        let show_name = sanitized_name.to_string().replace(ext,"").replace(".", " ");
  
        let rerun = true;
        let core = extract_title_core(show_name.as_str());
        let sanitized_name = initcap_string(core.clone().replace(' ',".").as_str());
        let key = sanitize_show(&core, &re_se);
        let show_name_norm = extract_show_from_key(&key, &re_se);

        info!("{key} -> moved to [re]process...");
        process_map.insert(
            key.clone(),
            ProcessEntry {
                key: key.clone().to_string(),
                rerun,
                title: show_name,
                show_name: show_name_norm.to_string(),
                folder: folder_name.to_string(),
                sanitized_name: sanitized_name.to_string(),
                extention: ext.to_string(),
                link: link.to_string(),
                file_id: String::new(),
                nf_view: String::new(),
                nf_down: link.to_string(),
            },
        );

    }

    info!("Interested in {} shows.",interest.len());
    info!("Evaluating links...");

    for item in channel.items() {
        let raw_title = match item.title() {
            Some(t) if !t.trim().is_empty() => t.trim().to_string(),
            _ => continue,
        };

        let link = item.link().unwrap_or("").trim().to_string();
        if link.is_empty() {
            continue;
        }

        let core = extract_title_core(&raw_title);
        let key = sanitize_show(&core, &re_se);
        let show_name_norm = extract_show_from_key(&key, &re_se);
        let folder_name = format!(
            "{}/{}", 
            BASE_FOLDER, 
            initcap_string(show_name_norm.clone().as_str())
        );
        let sanitized_name = initcap_string(core.clone().replace(' ',".").as_str());
        
        // info!("[test] {key}");
        if !interest.contains(&show_name_norm) {
            continue;
        }

        // Check seen KV
        if let Some(_ts) = kv.get(&key) {
            continue;
        }

        // are we already on the stack?
        if process_map.contains_key(&key) {
            continue;
        }

        info!("{key} -> moved to process...");
        let rerun = false;
        // we can process further
        process_map.insert(
            key.clone(),
            ProcessEntry {
                key,
                rerun,
                title: raw_title,
                show_name: show_name_norm,
                folder: folder_name,
                sanitized_name: sanitized_name,  // will need file type!
                extention: String::new(),
                link,
                file_id: String::new(),
                nf_view: String::new(),
                nf_down: String::new(),
            },
        );
    }

    match fs::remove_file(OUTPUT_FILE) {
            Ok(_) => {},
            Err(_e) => {},
    }

    if process_map.is_empty() {
        warn!("Nothing to process, we're done...");
        return Ok(());
    }

    let selector = Selector::parse("pre.links").expect("valid <pre class=\"links\"> selector");
    // Fetch and process all HTML pages in parallel with bounded concurrency
    let streamnf = stream::iter(process_map.keys().into_iter().map(|entry| {

        // get the link for the entry
        let p = process_map.get(entry).unwrap();
        let url = p.link.clone();
        let rerun = p.rerun;
        let client = client.clone();
        let selector = selector.clone();

        async move {
            match process_page_with_retries(
                &client, 
                &selector, 
                &url, 
                MAX_RETRIES, true, 
                entry.clone().as_str(),
                rerun).await 
            {
                Ok(links) => {
                    links
                }
                Err(_e) => {
                    Vec::new()
                }
            }
        }
    }))
    .buffer_unordered(MAX_CONCURRENCY);

    // assemble the NF links we digested
    let mut pm = process_map.clone();
    tokio::pin!(streamnf);
    while let Some(links) = streamnf.next().await {
        for (key, href) in links {
            if pm.contains_key(key.as_str()) {
                let p = pm.get_mut(key.as_str()).unwrap();
                let p = pm.get_mut(key.as_str()).unwrap();
                if p.rerun {
                    work_done = true;
                    continue;
                }
                let mut temp: Vec<&str> = href.split('.').collect();
                let ext = temp[temp.len()-1];
                temp = href.split('/').collect();
                let file_id = temp[4];
                p.nf_view = href.clone();
                p.extention = format!(".{}", ext.to_string());
                p.file_id = file_id.to_string();
                if !p.file_id.is_empty() {
                    p.nf_down = sdx.get_download(p).await?;
                    if !p.nf_down.is_empty() {
                        work_done = true;
                    }
                }
            }
        }
    }

    if work_done {

        // pre-flight: ensure aria2c exists
        // this is just noise so parking the call
        //ensure_aria2c("aria2c").await?;

        let streamnf = stream::iter(process_map.keys().into_iter().map(|entry| {

            let p = pm.get(entry.as_str()).unwrap();
            let mut arr = Aria2cRerun::init("aria_rerun.list".to_string()).unwrap();

            async move {
                match aria2c_download(p, &mut arr).await {
                    Ok(good) => {
                        if good.good {
                            good.key.clone()
                        } else {
                            String::new()
                        }
                    }
                    Err(_e) => {
                        String::new()
                    }
                }
            }
        }))
        .buffer_unordered(MAX_CONCURRENCY);
   
        let now: DateTime<Utc> = Utc::now();
        let ts = now.format("%Y-%m-%dT%H:%M:%S%z").to_string();
        tokio::pin!(streamnf);
        while let Some(ret) = streamnf.next().await {
            if !ret.is_empty() {
                let p = pm.get(ret.as_str()).unwrap();
                if !p.rerun {
                    let _ = kv.insert(ret.clone().as_str(), ts.clone().as_str());
                    info!("{} closing out...", ret.clone());
                }
            }
        }

    } else {
        warn!("work was not performed, maybe try again");
    }

    Ok(())

}

async fn aria2c_download(pe: &ProcessEntry, arr: &mut Aria2cRerun) -> BoxResult<Aria2cResult> {

    let mut ret = Aria2cResult::init(pe.key.clone()).unwrap();
    // Try to detect filename before handing to aria2c
    let aria2c_path = "aria2c";
    let filename = format!("{}{}", pe.sanitized_name, pe.extention);
    let rerun = pe.rerun;

    fs::create_dir_all(pe.folder.clone())?;

    // Build command: aria2c --dir <dir> --out <filename> [args...] <url>
    let mut args: Vec<String> = vec![
        "--dir".into(),
        pe.folder.clone().into(),
        "--out".into(),
        filename.clone(),
        "--quiet".into(),
        "--max-connection-per-server=16".into(),
        "--max-concurrent-downloads=16".into(),
        "--split=20".into(),
        "--continue=true".into(),
        "--auto-file-renaming=true".into(),
        "--summary-interval=0".into(),
        "--allow-overwrite=true".into(),
    ];
    args.push(pe.nf_down.clone().into());

    // these we just need to fire and forget
    let command = format!("{} {}", aria2c_path, args.join(" "));
    info!("[aria2c] {}", command.clone());
    let status = Command::new(aria2c_path).args(&args).status().await?;
    info!("[aria2c] {} {}", status, status.success());

    if !status.success() {
        error!("aria2c failed -> {status}");
        if !rerun {
            arr.write_rerun(command.clone())?;
        }
        ret.good = true; // added to rerun (so rerun is consumed and not picked up from the scrape), and we close out
    }else{
        ret.good = true; // close out
    }

    Ok(ret)

}

fn initcap_string(show: &str) -> String {

    let s = show.to_ascii_uppercase();
    // Season/episode regex — matches S01E05, S1E5, S001E05, etc.
    let season_ep = Regex::new(r"(?i)^s\d{1,3}e\d{1,3}$").unwrap();

    let mut out: Vec<String> = Vec::new();

    for tok in s.split('.') {

        if tok.is_empty() {
            continue;
        }

        // Reserved word or season+episode we keep uppercase
        if SPECIAL_CASES.contains(&tok) ||
            season_ep.is_match(&tok) {
            out.push(tok.to_string());
            continue;
        }
        let mut chars = tok.chars();
        let formatted = match chars.next() {
            Some(first) => {
                let first_cap = first.to_uppercase().collect::<String>();
                let rest = chars.as_str().to_ascii_lowercase();
                format!("{}{}", first_cap, rest)
            }
            None => String::new(),
        };

        out.push(formatted);
    }

    out.join(".")

}


/// Build the list of page URLs, matching site pattern:
/// page 1  -> BASE_URL
/// page N>1 -> BASE_URL/b/N
fn build_urls(base_url: &str, pages: i32) -> Vec<String> {
    info!("Synthesizing RS: {pages} pages for link scraping");
    let mut urls = Vec::new();
    for page_num in 1..=pages {
        let page_url = format!("{}/b/{}", base_url, page_num);
        urls.push(if page_num == 1 {
            base_url.to_string()
        } else {
            page_url
        });
    }
    urls
}

/// Retry wrapper around `process_page`
async fn process_page_with_retries(
    client: &Client,
    selector: &Selector,
    url: &str,
    max_retries: u32,
    use_sse: bool,
    key: &str,
    rerun: bool,
) -> BoxResult<Vec<(String, String)>> {

    if rerun {
        let res: Vec<(String, String)> = Vec::new();
        return Ok(res);
    }

    let mut attempt: u32 = 0;
    loop {
        attempt += 1;
        match process_page(client, selector, url, use_sse, key).await {
            Ok(res) => {
                return Ok(res);
            }
            Err(e) => {
                if attempt >= max_retries {
                    return Err(format!(
                        "request or response body error after {} attempts: {}",
                        attempt, e
                    )
                    .into());
                } else {
                    // simple linear backoff: 500ms, 1000ms, 1500ms, ...
                    let delay_ms = 500 * attempt as u64;
                    sleep(Duration::from_millis(delay_ms)).await;
                }
            }
        }
    }

}

/// Retry wrapper around RSS fetch/parse.
async fn process_rss_with_retries(
    client: &Client,
    url: &str,
    source: Source,
    max_retries: u32,
) -> BoxResult<Vec<FeedItem>> {
    let mut attempt: u32 = 0;

    loop {
        attempt += 1;
        match process_rss(client, url, source).await {
            Ok(res) => {
                return Ok(res);
            }
            Err(e) => {
                if attempt >= max_retries {
                    return Err(
                        format!("RSS error after {} attempts for {}: {}", attempt, url, e).into(),
                    );
                } else {
                    let delay_ms = 500 * attempt as u64;
                    sleep(Duration::from_millis(delay_ms)).await;
                }
            }
        }
    }

}

/// Fetch and parse RSS, then return matching FeedItem list (with pubDate preserved).
async fn process_rss(client: &Client, url: &str, source: Source) -> BoxResult<Vec<FeedItem>> {

    let resp = client.get(url).send().await?;
    let status = resp.status();
    if !status.is_success() {
        return Err(format!("Non-success status {} for RSS {}", status, url).into());
    }

    let bytes = resp.bytes().await?;
    let cursor = Cursor::new(bytes);
    let channel = Channel::read_from(cursor)?;

    let mut results = Vec::new();

    for item in channel.items() {
        let title = match item.title() {
            Some(t) if !t.trim().is_empty() => t.trim().to_string(),
            _ => continue,
        };

        let href = match item.link() {
            Some(l) if !l.trim().is_empty() => l.trim().to_string(),
            _ => continue,
        };

        if !link_matches(&title, &href) {
            continue;
        }

        // Use RSS pubDate if present, else fallback to now
        let (pub_dt, pub_dt_str) = if let Some(pd) = item.pub_date() {
            match DateTime::parse_from_rfc2822(pd) {
                Ok(dt) => (dt, dt.to_rfc2822()),
                Err(_) => {
                    let now_utc = Utc::now();
                    let now_fixed: DateTime<FixedOffset> = now_utc.into();
                    (now_fixed, now_fixed.to_rfc2822())
                }
            }
        } else {
            let now_utc = Utc::now();
            let now_fixed: DateTime<FixedOffset> = now_utc.into();
            (now_fixed, now_fixed.to_rfc2822())
        };

        results.push(FeedItem {
            title,
            link: href,
            pub_date: pub_dt,
            pub_date_str: pub_dt_str,
            source,
        });
    }

    Ok(results)

}

/// Fetch a page, parse HTML, and return matching (title, href) pairs.
async fn process_page(
    client: &Client,
    selector: &Selector,
    url: &str,
    use_sse: bool,
    key: &str,
) -> BoxResult<Vec<(String, String)>> {

    let base_url = Url::parse(url)?;

    let resp = client.get(base_url.clone()).send().await?;
    let status = resp.status();
    if !status.is_success() {
        return Err(format!("Non-success status {} for {}", status, url).into());
    }

    let body = resp.text().await?;
    let doc = Html::parse_document(&body);
    let mut results = Vec::new();

    if use_sse {

        let target_upper = NF_LINK.to_ascii_uppercase();

        for el in doc.select(selector) {

            let raw_text = el.text().collect::<String>();
            if raw_text.trim().is_empty() {
                continue;
            }

            let cleaned = raw_text;
            let upper = cleaned.to_ascii_uppercase();
            if !upper.contains(&target_upper) {
                continue;
            }

            // last check - is it playable
            let mut good = false;
            if FILETYPES
                .iter()
                .any(|b| cleaned.to_ascii_lowercase().ends_with(b))
            {
                good = true;
            }

            // For these, we just use the URL as both title & href
            results.push((key.to_string(), cleaned.to_string()));

        }

    } else {

        // -------- Anchor mode: <a href=...> + link_matches
        for el in doc.select(selector) {
            // selector = "a"
            let text = el.text().collect::<String>().trim().to_string();
            let href_raw = match el.value().attr("href") {
                Some(h) => h.trim(),
                None => continue,
            };

            if !link_matches(&text, href_raw) {
                continue;
            }

            let href = match base_url.join(href_raw) {
                Ok(u) => u.to_string(),
                Err(_) => {
                    if href_raw.starts_with("http://") || href_raw.starts_with("https://") {
                        href_raw.to_string()
                    } else {
                        continue;
                    }
                }
            };

            let title = if text.is_empty() {
                href.clone()
            } else {
                text.clone()
            };
            results.push((title, href));
        }
    }

    Ok(results)

}

/// Matching rules:
/// - Text contains "NF" (case-insensitive)
/// - href contains "1080" and (x265|h265|HEVC|AV1)
/// - OR href contains "2160" and (x265|h265|HEVC|AV1)
fn link_matches(text: &str, href: &str) -> bool {
    let text_upper = text.to_ascii_uppercase();
    if !text_upper.contains("NF") {
        return false;
    }

    let href_upper = href.to_ascii_uppercase();
    let mut good_link =
        href_upper.contains(VIDEO_RESOLUTION_1080)
            && (href_upper.contains("X265")
                || href_upper.contains("H265")
                || href_upper.contains("HEVC")
                || href_upper.contains("AV1"));
    // skip these
    if !good_link {
        good_link = href_upper.contains(VIDEO_RESOLUTION_2160)
            && (href_upper.contains("X265")
                || href_upper.contains("H265")
                || href_upper.contains("HEVC")
                || href_upper.contains("AV1"));
    }
    if !good_link {
        good_link = href_upper.contains(VIDEO_RESOLUTION_720)
            && (href_upper.contains("X265")
                || href_upper.contains("H265")
                || href_upper.contains("HEVC")
                || href_upper.contains("AV1"));
    }

    good_link
}

/// Season/episode regex: (.*?)(S\d{2,3}E\d{2})
fn season_episode_regex() -> Regex {
    Regex::new(r"(?i)(.*?)(S\d{2,3}E\d{2})").expect("valid regex")
}

fn initcap(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first_char) => {
            first_char.to_uppercase().collect::<String>() + &chars.as_str().to_lowercase()
        }
    }
}

/// Extract the portion of the title used to build the key:
fn extract_title_core(raw_title: &str) -> String {

    let up = raw_title.to_ascii_uppercase();
    // Find earliest occurrence of any resolution token
    let resolutions = [VIDEO_RESOLUTION_1080, VIDEO_RESOLUTION_2160, VIDEO_RESOLUTION_720];
    let mut split_idx: Option<usize> = None;

    for res in &resolutions {
        if let Some(idx) = up.find(res) {
            split_idx = match split_idx {
                Some(cur) if idx >= cur => Some(cur),
                _ => Some(idx),
            };
        }
    }

    // Cut at the first resolution if found, otherwise use whole string
    let prefix = if let Some(idx) = split_idx {
        &up[..idx]
    } else {
        &up[..]
    };

    // Strip and remove leading bracket tags: "[GROUP] SHOW.S01E01" -> "SHOW.S01E01"
    let trimmed = prefix.trim();
    let after_bracket = trimmed.rsplit(']').next().unwrap_or(trimmed).trim();

    after_bracket.to_string()

}

fn sanitize_show(data: &str, re: &Regex) -> String {
    let test = data
        .trim()
        .replace(' ', ".")
        .to_ascii_uppercase();

    if let Some(caps) = re.captures(&test) {
        if let (Some(g1), Some(g2)) = (caps.get(1), caps.get(2)) {
            let mut out = String::with_capacity(g1.as_str().len() + g2.as_str().len());
            out.push_str(g1.as_str());
            out.push_str(g2.as_str());
            return out;
        }
    }

    test
}

async fn get_chunked(pe: &ProcessEntry) -> BoxResult<Aria2cResult> {

    let key = pe.key.clone();
    info!("{}", key.clone());
    let mut ret = Aria2cResult::init(key.clone()).unwrap();
    let url = pe.nf_down.clone();
    let output_path = format!("{}/Ck_{}{}", pe.folder, pe.sanitized_name, pe.extention);
    let rerun = pe.rerun;

    fs::create_dir_all(pe.folder.clone())?;
    let client = Client::new();

    // Get file size and check for range support
    // implement retries for this
    let response = client.head(url.clone()).send().await?;
    let content_length = response
        .headers()
        .get(CONTENT_LENGTH)
        .and_then(|l| l.to_str().ok())
        .and_then(|l| l.parse::<u64>().ok())
        .ok_or("Failed to get {CONTENT_LENGTH}")?;

    let mut file = File::create(output_path.clone())?;
    if !response.headers().contains_key("accept-ranges") {
        warn!("Warning: Server does not support range requests. Downloading sequentially.");
        // Fallback to sequential download if range requests are not supported
        let mut response = client.get(url.clone()).send().await?.error_for_status()?;
        while let Some(chunk) = response.chunk().await? {
            file.write_all(&chunk)?;
        }
        return Ok(ret);
    }

    // 2. Range supported, pre-allocate space
    file.set_len(content_length)?;

    // Determine chunk ranges
    let mut chunk_ranges: Vec<Range<u64>> = Vec::new();
    let mut start = 0;
    while start < content_length {
        let end = (start + CHUNK_SIZE - 1).min(content_length - 1);
        chunk_ranges.push(start..end + 1);
        start += CHUNK_SIZE;
    }

    info!("<<< {output_path} {content_length}bytes {}chunks", chunk_ranges.len());
    //let mut done = 0;
    // Download chunks in parallel
    let mut tasks = Vec::new();
    for (i, range) in chunk_ranges.into_iter().enumerate() {
        let client = client.clone(); // Clone client for each task
        let output_path = output_path.to_string();
        let url = url.clone();
        let task = tokio::spawn(
            async move {

                let mut file = File::options().write(true).open(&output_path)?;
                let range_header = format!("bytes={}-{}", range.start, range.end - 1);
                // implement retries for this
                let response = client.get(url.clone())
                    .header(RANGE, range_header)
                    .send()
                    .await?
                    .error_for_status()?;

                file.seek(std::io::SeekFrom::Start(range.start))?;
                let mut bytes = response.bytes().await?;
                file.write_all(&bytes)?;
                Ok::<(), Box<dyn std::error::Error + Send + Sync>>(())

            }
        );

        tasks.push(task);

    }

    // Wait for all tasks to complete
    join_all(tasks).await;

    info!(">>> {output_path}");

    ret.good = true;
    Ok(ret)

}

fn getenv(key: &str, defo: &str) -> String {
    match env::var(key) {
        Ok(val) => val,
        Err(_e) => defo.to_string().clone()
    }
}


/*

use std::fs::{self, File};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

type BoxResult<T> = Result<T, Box<dyn std::error::Error + Send + Sync>>;

/// Ensure parent directory exists (mkdir -p)
fn ensure_parent_dir(path: &Path) -> io::Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)?;
    }
    Ok(())
}

/// Write an aria2 input file and return its path
fn write_aria2_input_file(downloads: &[(String, PathBuf)]) -> BoxResult<PathBuf> {
    // simple temp name: ./aria2_batch_<epoch>.txt
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)?
        .as_secs();

    let list_path = PathBuf::from(format!("aria2_batch_{now}.txt"));
    let mut f = File::create(&list_path)?;

    for (url, dest) in downloads {
        if url.trim().is_empty() {
            warm!("Empty URL, skipping");
            continue;
        }

        // Ensure destination directory exists
        ensure_parent_dir(dest)?;

        let file_name = dest
            .file_name()
            .unwrap_or_default()
            .to_string_lossy()
            .to_string();
        let dir = dest
            .parent()
            .unwrap_or_else(|| Path::new("."))
            .to_string_lossy()
            .to_string();

        writeln!(f, "{}", url)?;
        writeln!(f, "  dir={}", dir)?;
        writeln!(f, "  out={}", file_name)?;
        writeln!(f)?; // blank line between entries
    }

    f.flush()?;
    Ok(list_path)
}

/// Run aria2c once to download all entries from the list file
fn run_aria2_batch(list_path: &Path) -> BoxResult<()> {
    let status = Command::new("aria2c")
        // Use the input file
        .arg("--input-file")
        .arg(list_path)

        // Robustness / resume
        .arg("--continue=true")               // resume partial
        .arg("--max-tries=5")                 // aria2 internal retries
        .arg("--retry-wait=10")               // seconds between retries
        .arg("--auto-file-renaming=false")    // don't rename on conflicts
        .arg("--allow-overwrite=true")        // overwrite if re-running

        // Parallelism / performance – tune as desired
        .arg("--max-concurrent-downloads=4")
        .arg("--split=8")                     // connections per download
        .arg("--min-split-size=5M")

        // Logging / progress
        .arg("--summary-interval=60")         // fewer log updates
        .status()?;

    if !status.success() {
        return Err(format!("aria2c exited with status: {:?}", status.code()).into());
    }

    Ok(())
}

/// Public helper: given (url, dest_path) pairs, download them all via a single aria2c call
pub fn download_with_aria2_batch(downloads: &[(String, PathBuf)]) -> BoxResult<()> {
    if downloads.is_empty() {
        println!("[info] No downloads provided, skipping aria2c call.");
        return Ok(());
    }

    let list_path = write_aria2_input_file(downloads)?;
    println!(
        "[info] Written aria2 batch file: {}",
        list_path.to_string_lossy()
    );

    match run_aria2_batch(&list_path) {
        Ok(()) => {
            println!("[info] aria2c batch completed successfully.");
            Ok(())
        }
        Err(e) => {
            eprintln!("[error] aria2c batch failed: {}", e);
            Err(e)
        }
    }
}


*/


/*
use std::process::Command;
use std::path::PathBuf;
use std::fs;
use std::io::Write;
use chrono::Utc;

// Your existing KV append format: "key|timestamp\n"
fn append_seen(key: &str, db_path: &str) -> std::io::Result<()> {
    let mut f = fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open(db_path)?;
    let ts = Utc::now().to_rfc3339();
    writeln!(f, "{}|{}", key, ts)?;
    Ok(())
}

fn run_aria2_batch(list_path: &str) -> std::io::Result<bool> {
    let status = Command::new("aria2c")
        .arg("--input-file").arg(list_path)
        .arg("--continue=true")
        .arg("--max-tries=5")
        .arg("--retry-wait=10")
        .arg("--auto-file-renaming=false")
        .arg("--allow-overwrite=true")
        .arg("--max-concurrent-downloads=4")
        .arg("--split=8")
        .arg("--min-split-size=5M")
        .status()?;

    Ok(status.success())
}

pub fn download_and_mark_seen(
    jobs: &[(String, PathBuf, String)], // (url, dest, key)
    db_path: &str,
) -> BoxResult<()> {
    // 1. write aria2 input file from (url, dest)
    let aria_jobs: Vec<(String, PathBuf)> = jobs
        .iter()
        .map(|(u, d, _k)| (u.clone(), d.clone()))
        .collect();

    let list_path = write_aria2_input_file(&aria_jobs)?; // your existing helper

    // 2. run aria2c
    let ok = run_aria2_batch(list_path.to_str().unwrap())?;
    if !ok {
        warn!("aria2c returned non-success exit code; will still check files");
    }

    // 3. for each job, if dest exists and non-zero, mark as seen
    for (_, dest, key) in jobs {
        match fs::metadata(dest) {
            Ok(meta) if meta.is_file() && meta.len() > 0 => {
                println!("[ok  ] Completed {}, marking seen: {}", dest.display(), key);
                append_seen(key, db_path)?;
            }
            _ => {
                warn!("Destination folder not present or empty, not marking seen: {} ({})",
                          dest.display(), key);
            }
        }
    }

    Ok(())
}

*/


/*

use std::fs;
use std::path::{Path, PathBuf};

/// Here we assume autoallocate is true so checking filesize
/// is redundant - we monitor the sidecar file instead
/// Given the final target file path, build the aria2 sidecar path:
/// "/path/to/file.mkv" -> "/path/to/file.mkv.aria2"
fn aria2_sidecar_path(dest: &Path) -> PathBuf {
    let mut s = dest.as_os_str().to_owned();
    s.push(".aria2");
    PathBuf::from(s)
}

/// True if aria2 appears to have completed this download:
/// - main file exists AND
/// - sidecar (*.aria2) does NOT exist
fn is_aria2_complete(dest: &Path) -> bool {
    let sidecar = aria2_sidecar_path(dest);
    dest.is_file() && !sidecar.exists()
}

fn partition_jobs_by_completion(jobs: &[Job]) -> (Vec<Job>, Vec<Job>) {
    let mut completed = Vec::new();
    let mut incomplete = Vec::new();

    for (url, dest, key) in jobs {
        if is_aria2_complete(dest) {
            completed.push((url.clone(), dest.clone(), key.clone()));
        } else {
            incomplete.push((url.clone(), dest.clone(), key.clone()));
        }
    }

    (completed, incomplete)
}

fn main() -> BoxResult<()> {

    let jobs: Vec<Job> = vec![
        (
            "https://nitroflare.com/view/...".to_string(),
            PathBuf::from("/data2/videos/Our.Cartoon.President/Our.Cartoon.President.US.S01E08.mkv"),
            "OUR.CARTOON.PRESIDENT.US.S01E08".to_string(),
        ),
        // more jobs...
    ];

    let db_path = ".cache/seen_shows.db";

    let mut remaining = jobs;
    let mut round = 1;

    loop {
        println!("[info] Round {} – {} jobs", round, remaining.len());
        if remaining.is_empty() {
            break;
        }

        remaining = run_and_update_seen(&remaining, db_path)?;
        if remaining.is_empty() {
            println!("[info] All downloads completed.");
            break;
        }

        round += 1;
        // optional: sleep/backoff before next attempt
    }

    Ok(())
}


*/
