#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
Global Jobs Web Scraper (Google CSE + JobPosting extractor)
— strict location matching, faster concurrency, international-aware, and closed/expired job skipping (v2.7)

What this version improves
- **Strict location**: city/state/country checks with aliases; toggle via `STRICT_LOCATION`.
- **Closed/expired skip**: detects 404/410, past `validThrough`, and common phrases ("no longer accepting applications").
- **Faster**: connection pooling + ThreadPoolExecutor + shorter timeouts + smart retries.
- **Better domain control**: cap by *registrable* domain (e.g., `nl.linkedin.com` & `ca.linkedin.com` → `linkedin.com`) enforced pre- and post-fetch.
- **Spam blacklist**: drops common junk redirectors.
- **No-results UX**: prints a helpful message if nothing matched.

Install:
  pip install requests beautifulsoup4 pandas python-dateutil

Env (required):
  export GOOGLE_API_KEY="your_key"
  export GOOGLE_CSE_ID="your_cse_id"
"""

import os
import re
import time
import json
import html
import random
from typing import Tuple, Optional, List, Dict, Any
from datetime import datetime, timezone, date
from urllib.parse import urlparse, parse_qs

import requests
from bs4 import BeautifulSoup
import pandas as pd
from dateutil.parser import parse as dtparse
from concurrent.futures import ThreadPoolExecutor, as_completed

# ---------------- Config ----------------
GOOGLE_API_KEY = os.getenv("GOOGLE_API_KEY")
GOOGLE_CSE_ID  = os.getenv("GOOGLE_CSE_ID")

DEFAULT_CITIES = [
    "Mumbai", "Delhi", "Bengaluru", "Hyderabad",
    "Chennai", "Kolkata", "Pune", "Ahmedabad", "Gurugram", "Noida"
]

HEADERS = {
    "User-Agent": "Mozilla/5.0 (compatible; GlobalJobsScraper/2.7; +https://example.local)",
    "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
    "Accept-Language": "en-US,en;q=0.9"
}

REQUEST_TIMEOUT = 14
RETRY_COUNT = 2
BACKOFF_BASE = 1.5
MIN_RESULTS_DEFAULT = 20
CSV_DEFAULT = "jobs_global.csv"
PER_DOMAIN_CAP = 3   # hard cap per registrable domain across the entire run
MAX_WORKERS = 14     # concurrent page fetches
STRICT_LOCATION = True  # require city/state/country match; set False to loosen
MIN_RELEVANCE_SCORE = 2 # title/description token hits required

# Optional: curated job boards
INDIA_JOB_BOARDS = [
    "naukri.com", "foundit.in", "iimjobs.com", "hirist.com",
    "timesjobs.com", "shine.com", "cutshort.io", "instahyre.com",
    "indeed.co.in", "indeed.com", "angel.co", "wellfound.com"
]
GLOBAL_JOB_BOARDS = [
    "indeed.com", "indeed.co.uk", "indeed.ca", "indeed.de", "indeed.fr", "indeed.nl",
    "linkedin.com", "glassdoor.com", "glassdoor.co.in", "monster.com", "ziprecruiter.com",
    "wellfound.com", "angel.co", "stepstone.de", "reed.co.uk",
]

# Known spammy/redirector domains to ignore outright
BLACKLIST_DOMAINS = {
    "unjoblink.org", "eworker.co", "jobeka.in", "jobleads.com"
}

# City aliases for normalization
CITY_ALIASES = {
    "bengaluru": "bangalore", "new delhi": "delhi", "gurugram": "gurgaon",
    "nyc": "new york", "sf": "san francisco", "sfo": "san francisco", "la": "los angeles",
    "blr": "bangalore", "mum": "mumbai", "ams": "amsterdam"
}

# State/Province dictionaries (US/CA/AU; extendable)
US_STATE_ABBR = {
    'AL':'alabama','AK':'alaska','AZ':'arizona','AR':'arkansas','CA':'california','CO':'colorado','CT':'connecticut','DE':'delaware','DC':'district of columbia','FL':'florida','GA':'georgia','HI':'hawaii','ID':'idaho','IL':'illinois','IN':'indiana','IA':'iowa','KS':'kansas','KY':'kentucky','LA':'louisiana','ME':'maine','MD':'maryland','MA':'massachusetts','MI':'michigan','MN':'minnesota','MS':'mississippi','MO':'missouri','MT':'montana','NE':'nebraska','NV':'nevada','NH':'new hampshire','NJ':'new jersey','NM':'new mexico','NY':'new york','NC':'north carolina','ND':'north dakota','OH':'ohio','OK':'oklahoma','OR':'oregon','PA':'pennsylvania','RI':'rhode island','SC':'south carolina','SD':'south dakota','TN':'tennessee','TX':'texas','UT':'utah','VT':'vermont','VA':'virginia','WA':'washington','WV':'west virginia','WI':'wisconsin','WY':'wyoming'
}
CA_PROVINCES = {
    'AB':'alberta','BC':'british columbia','MB':'manitoba','NB':'new brunswick','NL':'newfoundland and labrador','NS':'nova scotia','NT':'northwest territories','NU':'nunavut','ON':'ontario','PE':'prince edward island','QC':'quebec','SK':'saskatchewan','YT':'yukon'
}
AU_STATES = {
    'NSW':'new south wales','VIC':'victoria','QLD':'queensland','WA':'western australia','SA':'south australia','TAS':'tasmania','ACT':'australian capital territory','NT':'northern territory'
}

# Country synonyms/ISO2 mapping (extendable)
COUNTRY_MAP = {
    "in": "india", "india": "india",
    "us": "united states", "usa": "united states", "united states": "united states", "america": "united states",
    "uk": "united kingdom", "gb": "united kingdom", "britain": "united kingdom",
    "nl": "netherlands", "netherlands": "netherlands", "holland": "netherlands",
    "de": "germany", "germany": "germany",
    "fr": "france", "france": "france",
    "au": "australia", "aus": "australia", "australia": "australia",
    "sg": "singapore", "singapore": "singapore",
    "ca": "canada", "canada": "canada",
}

# Suggestions list (defined early so it always exists when printed)
INDUSTRY_SUGGESTIONS = [
    "Tech", "Trading", "BPO", "Consulting", "FinTech", "EdTech", "E-commerce", "Healthcare", "Telecom"
]

# ---------------- dictionaries: experience & filters ----------------
EXPERIENCE_LEVELS = {
    "1": ("Entry / Fresher (0-1 yrs)", ["fresher", "entry level", "graduate", "0-1 year", "0-2 years", "trainee", "junior"]),
    "2": ("Junior (1-3 yrs)",          ["junior", "1-3 years", "1-2 years", "associate"]),
    "3": ("Mid (3-6 yrs)",             ["mid level", "3-6 years", "3+ years", "4+ years"]),
    "4": ("Senior / Lead (6+ yrs)",    ["senior", "lead", "principal", "staff", "6+ years", "7+ years", "8+ years", "architect"]),
}

JOB_TYPES = {
    "1": ("Full-time",   ["full-time", "permanent", "regular"]),
    "2": ("Contract",    ["contract", "contractual", "temp", "temporary"]),
    "3": ("Part-time",   ["part-time"]),
    "4": ("Internship",  ["internship", "intern", "summer intern"]),
    "5": ("Remote",      ["remote", "work from home", "wfh", "hybrid"]),
}

CLOSED_PATTERNS = re.compile(
    r"(no longer accepting applications|no longer available|position (has been )?closed|job (posting )?closed|this job is closed|job expired|no longer active|has expired|has been filled|application window closed|this listing has ended)",
    re.I
)

JOB_TITLE_KEYWORDS = re.compile(
    r"\b(hiring|engineer|developer|manager|analyst|architect|lead|designer|consultant|specialist|administrator|scientist|sre|devops|python|data|trader|support|security|qa|ios|android|frontend|backend|fullstack)\b",
    re.I
)

RELEVANCE_TOKENS = [
    r"responsibilit", r"requirement", r"apply", r"experience", r"salary", r"benefit", r"qualification", r"about the role", r"what you will do"
]

# ---------------- Logging helpers ----------------
class Logger:
    def __init__(self, verbose: bool):
        self.verbose = verbose
    def info(self, msg: str):
        print(msg, flush=True)
    def debug(self, msg: str):
        if self.verbose:
            print(msg, flush=True)
    def warn(self, msg: str):
        print(f"[WARN] {msg}", flush=True)

# ---------------- Small utils ----------------

def _as_list(val):
    if val is None:
        return []
    if isinstance(val, list):
        return val
    return [val]


def clean_text(x, max_len=8000):
    if not x:
        return ""
    if isinstance(x, dict):
        x = x.get("text") or x.get("description") or json.dumps(x, ensure_ascii=False)
    x = html.unescape(BeautifulSoup(str(x), "html.parser").get_text(" ", strip=True))
    x = re.sub(r"\s+", " ", x).strip()
    return x[:max_len]


def first(x, *keys, default=""):
    if not isinstance(x, dict):
        return default
    for k in keys:
        v = x.get(k)
        if v:
            return v
    return default


def normalize_token(s: str) -> str:
    s = (s or "").strip().lower()
    s = re.sub(r"[^a-z0-9+ ]+", " ", s)
    s = re.sub(r"\s+", " ", s)
    return s


def normalize_city(s: str) -> str:
    s = normalize_token(s)
    s = CITY_ALIASES.get(s, s)
    return s


def normalize_country(s: str) -> str:
    s = normalize_token(s)
    return COUNTRY_MAP.get(s, s)


def registrable_domain(url_or_netloc: str) -> str:
    """Collapse subdomains to a registrable domain for counting caps.
    Heuristic handling for multi-part TLDs like .co.in / .co.uk.
    """
    netloc = url_or_netloc
    if "//" in netloc:
        try:
            netloc = urlparse(netloc).netloc
        except Exception:
            pass
    netloc = netloc.split(":")[0].lower()
    if netloc.startswith("www."):
        netloc = netloc[4:]
    parts = netloc.split(".")
    if len(parts) <= 2:
        return netloc
    # Handle common 2nd-level ccTLDs
    last2 = ".".join(parts[-2:])
    last3 = ".".join(parts[-3:])
    if last2 in {"co.uk","ac.uk","gov.uk","co.in","com.au","com.sg","co.nz","com.br"}:
        return last3
    if parts[-1] in {"in","uk","au","sg","nl","de","fr","ca","us"} and parts[-2] in {"co","com","gov","ac"}:
        return last3
    return last2


def unique_rows(rows, key=("title","company","apply_url")):
    seen = set()
    out = []
    for r in rows:
        k = tuple((r.get(x) or "").strip().lower() for x in key)
        if k not in seen and any(r.values()):
            seen.add(k)
            out.append(r)
    return out


def domain_of(url: str) -> str:
    try:
        return urlparse(url).netloc.lower()
    except Exception:
        return ""


def is_probably_html(url: str) -> bool:
    path = urlparse(url).path.lower()
    if any(path.endswith(ext) for ext in (".pdf", ".doc", ".docx", ".ppt", ".pptx", ".xls", ".xlsx")):
        return False
    return True


def clean_redirector(url: str) -> str:
    try:
        u = urlparse(url)
        if "linkedin.com" in u.netloc and "/redir/" in u.path:
            qs = parse_qs(u.query)
            if "url" in qs and qs["url"]:
                return qs["url"][0]
        if "google.com" in u.netloc and u.path.startswith("/url"):
            qs = parse_qs(u.query)
            if "q" in qs and qs["q"]:
                return qs["q"][0]
        return url
    except Exception:
        return url

# ---------------- HTTP helpers ----------------
class HTTPSession:
    def __init__(self, logger: Logger):
        self.logger = logger
        self.s = requests.Session()
        self.s.headers.update(HEADERS)
        # connection pool for speed
        adapter = requests.adapters.HTTPAdapter(pool_connections=64, pool_maxsize=64, max_retries=0)
        self.s.mount('http://', adapter)
        self.s.mount('https://', adapter)

    def get(self, url: str, timeout=REQUEST_TIMEOUT) -> Optional[requests.Response]:
        last_exc = None
        for attempt in range(1, RETRY_COUNT + 2):
            try:
                r = self.s.get(url, timeout=timeout, allow_redirects=True)
                return r
            except requests.RequestException as e:
                last_exc = e
                jitter = random.uniform(0.0, 0.6)
                backoff = (BACKOFF_BASE ** attempt) + jitter
                self.logger.debug(f"HTTP retry {attempt}/{RETRY_COUNT+1} for {url} due to {e!r}; sleep {backoff:.2f}s")
                time.sleep(backoff)
        self.logger.debug(f"Failed GET after retries: {url} — {last_exc!r}")
        return None

# ---------------- Google search ----------------

def google_cse_search(query, num=10, start=1, days=None, gl_country: Optional[str]=None, logger: Optional[Logger]=None):
    if not GOOGLE_API_KEY or not GOOGLE_CSE_ID:
        raise RuntimeError("Missing GOOGLE_API_KEY or GOOGLE_CSE_ID environment variables.")

    params = {
        "key": GOOGLE_API_KEY,
        "cx": GOOGLE_CSE_ID,
        "q": query,
        "num": min(10, max(1, num)),
        "start": max(1, start),
        "safe": "off",
        "hl": "en",
    }
    if days and days > 0:
        params["dateRestrict"] = f"d{int(days)}"
    if gl_country:
        params["gl"] = gl_country

    url = "https://www.googleapis.com/customsearch/v1"
    session = requests.Session()
    try:
        r = session.get(url, params=params, timeout=REQUEST_TIMEOUT)
        r.raise_for_status()
    except requests.HTTPError:
        try:
            err_json = r.json()
            if logger:
                logger.warn(f"Google CSE error for '{query}': {r.status_code}")
                logger.warn(f"ERROR JSON: {err_json}")
        except Exception:
            if logger:
                logger.warn(f"ERROR TEXT: {r.text[:500]}")
        raise
    return r.json()

# ---------------- Extraction ----------------

def extract_jobposting_from_jsonld(soup: BeautifulSoup) -> Optional[dict]:
    scripts = soup.find_all("script", type=lambda t: t and "ld+json" in t.lower())
    for sc in scripts:
        raw = sc.string or sc.text or ""
        if not raw.strip():
            continue
        try:
            data = json.loads(raw)
        except Exception:
            continue
        for node in _as_list(data):
            if isinstance(node, dict):
                types = _as_list(node.get("@type"))
                if any(str(t).lower() == "jobposting" for t in types):
                    return node
    return None


def normalize_jobposting(node: dict, fallback_url=None, city_hint="") -> dict:
    job = {}
    job["source_url"] = fallback_url or ""
    job["title"] = first(node, "title", "name", default="")
    job["company"] = ""
    hiring_org = node.get("hiringOrganization")
    if isinstance(hiring_org, dict):
        job["company"] = first(hiring_org, "name", default="")
    elif isinstance(hiring_org, str):
        job["company"] = hiring_org

    # Location
    loc = node.get("jobLocation") or node.get("applicantLocationRequirements")
    location_txt = ""
    city_norm = ""
    country_norm = ""
    region_norm = ""
    if loc:
        for loc_item in _as_list(loc):
            if isinstance(loc_item, dict):
                address = loc_item.get("address")
                if isinstance(address, dict):
                    locality = clean_text(address.get("addressLocality") or "")
                    region   = clean_text(address.get("addressRegion") or "")
                    country  = clean_text(address.get("addressCountry") or "")
                    pieces = [locality, region, country]
                    s = ", ".join([p for p in pieces if p])
                    if s:
                        location_txt = s
                        city_norm = normalize_city(locality)
                        country_norm = normalize_country(country)
                        region_norm = normalize_token(region)
                        break
                else:
                    s = clean_text(address or loc_item.get("name") or "")
                    if s:
                        location_txt = s
                        break
    if not location_txt:
        location_txt = clean_text(node.get("jobLocationType") or "")
    job["location"] = location_txt or (city_hint or "")
    job["city"] = city_hint or ""

    # Dates
    def safe_date(s):
        if not s:
            return ""
        try:
            return dtparse(str(s)).date().isoformat()
        except Exception:
            return str(s)

    job["date_posted"]   = safe_date(first(node, "datePosted", default="").strip())
    job["valid_through"] = safe_date(first(node, "validThrough", default="").strip())

    # Employment type
    et = node.get("employmentType")
    job["employment_type"] = ", ".join(str(x) for x in et) if isinstance(et, list) else (str(et) if et else "")

    # Salary
    salary = ""
    bs = node.get("baseSalary")
    if isinstance(bs, dict):
        val = bs.get("value")
        if isinstance(val, dict):
            salary = f"{val.get('currency', '')} {val.get('minValue', '')}-{val.get('maxValue', '')} {val.get('unitText', '')}".strip()
        else:
            salary = clean_text(str(bs))
    elif isinstance(bs, (list, str)):
        salary = clean_text(str(bs))
    job["salary"] = salary

    # Description
    job["description"] = clean_text(first(node, "description", "responsibilities", default=""))

    # Apply URL
    apply_url = first(node, "applicationUrl", "url", "applyUrl", default="")
    if isinstance(apply_url, dict):
        apply_url = first(apply_url, "url", default="")
    job["apply_url"] = apply_url or (fallback_url or "")

    # Job ID
    job_id = first(node, "identifier", default="")
    if isinstance(job_id, dict):
        job_id = first(job_id, "value", "name", default="")
    job["job_id"] = job_id

    # Remote?
    job["remote"] = "remote" if re.search(r"\b(remote|work from home|wfh|hybrid)\b", (job["location"] + " " + job["description"]).lower()) else ""

    # normalized hints
    job["normalized_city"] = city_norm
    job["normalized_country"] = country_norm
    job["normalized_region"] = region_norm

    return job


def heuristic_extract(soup: BeautifulSoup, url: str, city_hint: str) -> dict:
    title = soup.find("h1") or soup.find("h2")
    title_txt = title.get_text(" ", strip=True)[:200] if title else ""

    company = ""
    for prop in ["og:site_name", "application-name", "twitter:site", "twitter:creator"]:
        tag = soup.find("meta", attrs={"property": prop}) or soup.find("meta", attrs={"name": prop})
        if tag and tag.get("content"):
            company = tag["content"]
            break

    if not company:
        ttag = soup.find("title")
        if ttag and "-" in ttag.text:
            maybe = ttag.text.split("-")[-1].strip()
            if len(maybe) <= 80:
                company = maybe

    # Try to find location chips/breadcrumbs
    location_txt = ""
    selectors = [
        {"name": "meta", "attrs": {"name": "job_location"}},
        {"name": "meta", "attrs": {"property": "og:locale"}},
        {"name": "span", "class_": re.compile(r"location|job-location|posted-in", re.I)},
        {"name": "li", "class_": re.compile(r"location", re.I)},
        {"name": "p", "class_": re.compile(r"location", re.I)},
    ]
    for sel in selectors:
        try:
            el = soup.find(sel.get("name"), attrs=sel.get("attrs")) if sel.get("attrs") else soup.find(sel.get("name"), class_=sel.get("class_"))
            if el:
                val = el.get("content") if el.has_attr("content") else el.get_text(" ", strip=True)
                if val and len(val) <= 120:
                    location_txt = val
                    break
        except Exception:
            pass

    desc_tag = soup.find("meta", attrs={"name": "description"}) or soup.find("meta", attrs={"property": "og:description"})
    description = desc_tag.get("content")[:8000] if desc_tag and desc_tag.get("content") else ""

    return {
        "source_url": url,
        "title": title_txt,
        "company": company,
        "location": location_txt or (city_hint or ""),
        "city": city_hint or "",
        "date_posted": "",
        "valid_through": "",
        "employment_type": "",
        "salary": "",
        "description": description,
        "apply_url": url,
        "job_id": "",
        "remote": "remote" if re.search(r"\b(remote|work from home|wfh|hybrid)\b", (description + " " + title_txt).lower()) else "",
        "normalized_city": normalize_city(location_txt.split(',')[0] if location_txt else city_hint),
        "normalized_country": "",
        "normalized_region": "",
    }

# ---------------- Closed/expired detection ----------------

def is_closed_or_expired(soup: BeautifulSoup, status_code: int, valid_through: str) -> (bool, str):
    if status_code in (404, 410):
        return True, f"http-{status_code}"
    try:
        if valid_through:
            d = dtparse(valid_through).date()
            if d < date.today():
                return True, "validThrough-past"
    except Exception:
        pass
    txt = clean_text(soup.get_text(" ", strip=True)).lower()
    m = re.search(
        r"(no longer accepting applications|no longer available|position (has been )?closed|job (posting )?closed|this job is closed|job expired|no longer active|has expired|has been filled|application window closed|this listing has ended)",
        txt,
        re.I,
    )
    if m:
        return True, m.group(1)[:80]
    if soup.find(string=re.compile(r"apply now", re.I)) and soup.find(string=re.compile(r"closed|expired|disabled|ended", re.I)):
        return True, "apply-closed"
    return False, ""

# ---------------- Experience detection ----------------
EXPERIENCE_HINTS = [
    (r"\b(0[\-–]1|0 to 1|0-2|0 to 2|fresher|entry level|graduate|trainee)\b", "Entry / Fresher"),
    (r"\b(1[\-–]3|1 to 3|junior|associate)\b", "Junior"),
    (r"\b(3[\-–]6|3 to 6|mid|intermediate)\b", "Mid"),
    (r"\b(6\+|7\+|8\+|senior|lead|principal|staff|architect)\b", "Senior / Lead"),
]

def detect_experience_from_text(text: str) -> str:
    t = (text or "").lower()
    for pattern, label in EXPERIENCE_HINTS:
        if re.search(pattern, t):
            return label
    return ""

# ---------------- Query builder ----------------

def build_query(role: str, city: str, industries: List[str], jobtype_tokens: List[str], exp_tokens: List[str], prefer_job_boards: bool, custom_domains: List[str], country_hint: Optional[str]) -> str:
    bits = []
    if role:
        bits.append(f'"{role}"')
    for ind in industries:
        bits.append(ind)
    if jobtype_tokens:
        bits.append("(" + " OR ".join(jobtype_tokens) + ")")
    if exp_tokens:
        bits.append("(" + " OR ".join(exp_tokens) + ")")
    bits.append("jobs")
    if city:
        bits.append(f'"{city}"')
    if country_hint:
        bits.append(f'"{country_hint}"')

    base = " ".join(bits)

    domains = []
    if custom_domains:
        domains = custom_domains
    elif prefer_job_boards:
        domains = list({*INDIA_JOB_BOARDS, *GLOBAL_JOB_BOARDS})

    domain_q = (" (" + " OR ".join(f"site:{d}" for d in domains) + ")") if domains else ""
    return base + domain_q

# ---------------- Location matching ----------------

def extract_country_guess(text: str) -> str:
    t = normalize_token(text)
    for key, full in COUNTRY_MAP.items():
        if re.search(rf"\b{re.escape(key)}\b", t) or re.search(rf"\b{re.escape(full)}\b", t):
            return full
    return ""


def region_norm_match(s: str) -> str:
    s = normalize_token(s)
    if s in US_STATE_ABBR:
        return US_STATE_ABBR[s]
    for abbr, full in US_STATE_ABBR.items():
        if s == full:
            return full
    if s in CA_PROVINCES:
        return CA_PROVINCES[s]
    for abbr, full in CA_PROVINCES.items():
        if s == full:
            return full
    if s in AU_STATES:
        return AU_STATES[s]
    for abbr, full in AU_STATES.items():
        if s == full:
            return full
    return ""


def matches_desired_location(row: Dict[str, Any], desired_cities: List[str], desired_country: Optional[str], allow_remote: bool) -> Tuple[bool, str]:
    if allow_remote and row.get("remote"):
        return True, "remote-allowed"

    wanted_cities = [normalize_city(c) for c in desired_cities if c]
    wanted_country = normalize_country(desired_country) if desired_country else ""

    hay = " ".join([
        row.get("location", ""), row.get("city", ""), row.get("description", ""), row.get("title", "")
    ])
    hay_norm = normalize_token(hay)

    jc = row.get("normalized_city") or ""
    jcountry = row.get("normalized_country") or extract_country_guess(hay_norm)
    jregion = region_norm_match(row.get("normalized_region", "")) or region_norm_match(hay_norm)

    for c in wanted_cities:
        if c and re.search(rf"\b{re.escape(c)}\b", hay_norm):
            if re.search(r"\b(hiring|engineer|developer|manager|analyst|architect|lead|designer|consultant|specialist|administrator|scientist|sre|devops|python|data|trader|support)\b", hay_norm):
                if wanted_country and jcountry and jcountry != wanted_country:
                    continue
                return True, f"city:{c}"
    if jc and jc in wanted_cities:
        if not wanted_country or (jcountry == wanted_country or not jcountry):
            return True, f"jsonld-city:{jc}"
    if jregion:
        return True, f"region:{jregion}"
    if wanted_country:
        if jcountry == wanted_country or re.search(rf"\b{re.escape(wanted_country)}\b", hay_norm):
            return True, f"country:{wanted_country}"
    return (not STRICT_LOCATION), ("fallback" if not STRICT_LOCATION else "no-match")

# ---------------- Relevance scoring ----------------

def relevance_score(title: str, description: str) -> int:
    score = 0
    if re.search(JOB_TITLE_KEYWORDS, title or ""):
        score += 2
    if re.search(JOB_TITLE_KEYWORDS, description or ""):
        score += 1
    text = (title or "") + " " + (description or "")
    for tok in RELEVANCE_TOKENS:
        if re.search(tok, text, re.I):
            score += 1
    return score

# ---------------- Interactive input ----------------

def ask_list(prompt: str, default_list: List[str]) -> List[str]:
    s = input(prompt).strip()
    if not s:
        return default_list
    parts = [p.strip() for p in s.split(",")]
    return [p for p in parts if p]


def select_experience_level() -> (str, List[str]):
    print("\nSelect experience level:")
    for k, (label, _) in EXPERIENCE_LEVELS.items():
        print(f"  {k}. {label}")
    choice = input("Choice [1-4, Enter to skip]: ").strip()
    if choice in EXPERIENCE_LEVELS:
        label, tokens = EXPERIENCE_LEVELS[choice]
        return label, tokens
    return "", []


def select_job_types() -> (List[str], List[str]):
    print("\nSelect job types (choose multiple: e.g., 1,5). Options:")
    for k, (label, _) in JOB_TYPES.items():
        print(f"  {k}. {label}")
    choice = input("Choice(s) [comma-separated, Enter to skip]: ").strip()
    if not choice:
        return [], []
    idx = {c.strip() for c in choice.split(",")}
    labels, tokens = [], []
    for k in idx:
        if k in JOB_TYPES:
            lab, toks = JOB_TYPES[k]
            labels.append(lab)
            tokens.extend(toks)
    return labels, tokens

# ---------------- Worker to fetch & parse a single URL ----------------

def fetch_and_parse(url: str, city: str, logger: Logger, http: HTTPSession) -> Optional[dict]:
    try:
        if not is_probably_html(url):
            return None
        r = http.get(url)
        if not r or r.status_code >= 400:
            return None
        final_url = str(r.url)
        netloc = registrable_domain(final_url)
        if netloc in BLACKLIST_DOMAINS:
            return None
        text = r.text
        soup = BeautifulSoup(text, "html.parser")
        node = extract_jobposting_from_jsonld(soup)
        if node:
            row = normalize_jobposting(node, fallback_url=final_url, city_hint=city)
        else:
            row = heuristic_extract(soup, final_url, city)
        closed, reason = is_closed_or_expired(soup, r.status_code, row.get("valid_through", ""))
        if closed:
            row["__closed__"] = True
            row["closed_reason"] = reason
            return row
        if not row.get("title") and not row.get("description"):
            return None
        if relevance_score(row.get("title",""), row.get("description","")) < MIN_RELEVANCE_SCORE:
            return None
        row["experience_level_detected"] = detect_experience_from_text((row.get("title","") + " " + row.get("description","")))
        return row
    except Exception as e:
        logger.debug(f"fetch_and_parse failed for {url}: {e!r}")
        return None

# ---------------- Main ----------------

def main():
    print("=== Global Jobs Scraper v2.7 ===")
    print("Tip: separate multiple entries with commas.")

    roles = ask_list("Enter job roles (e.g., DevOps Engineer, SRE, Data Engineer): ", [])
    while not roles:
        roles = ask_list("Please enter at least one job role: ", [])

    cities = ask_list(f"Enter cities (press Enter for defaults: {', '.join(DEFAULT_CITIES)}): ", DEFAULT_CITIES)

    print(f"\nPopular industries: {', '.join(INDUSTRY_SUGGESTIONS)}")
    industries = ask_list("Enter industries (e.g., Tech, Trading, BPO) or press Enter to skip: ", [])

    jobtype_labels, jobtype_tokens = select_job_types()
    exp_label, exp_tokens = select_experience_level()

    country_inp = input("\nCountry (e.g., India, US, Netherlands) or ISO2 (IN/US/NL) [Enter to skip]: ").strip()
    country_norm = normalize_country(country_inp) if country_inp else ""

    prefer_boards = input("Prefer job boards for more generic links? (y/N): ").strip().lower() == "y"
    domains = ask_list("Optional: additionally restrict to domains (comma-separated) or press Enter: ", [])

    allow_remote = input("Include remote roles that mention 'remote/WFH/hybrid'? (Y/n): ").strip().lower() != "n"

    csv_path = input(f"\nCSV output path [default: {CSV_DEFAULT}]: ").strip() or CSV_DEFAULT
    try:
        min_results_target = int(input(f"Minimum results to collect [default {MIN_RESULTS_DEFAULT}]: ").strip() or MIN_RESULTS_DEFAULT)
    except ValueError:
        min_results_target = MIN_RESULTS_DEFAULT

    verbose = input("Verbose logs? (y/N): ").strip().lower() == "y"
    logger = Logger(verbose=verbose)

    if not GOOGLE_API_KEY or not GOOGLE_CSE_ID:
        logger.warn("Missing GOOGLE_API_KEY or GOOGLE_CSE_ID. Export them and re-run.")
        return

    banner = f"Starting job scrape • {datetime.now(timezone.utc).strftime('%Y-%m-%d %H:%M:%SZ')} UTC"
    logger.info("=" * len(banner))
    logger.info(banner)
    logger.info("=" * len(banner))
    logger.info(f"Roles     : {', '.join(roles)}")
    logger.info(f"Cities    : {', '.join(cities)}")
    logger.info(f"Country   : {(country_norm or '(none)')} ")
    logger.info(f"Industries: {'(none)' if not industries else ', '.join(industries)}")
    logger.info(f"Job types : {'(none)' if not jobtype_labels else ', '.join(jobtype_labels)}")
    logger.info(f"Experience: {'(none)' if not exp_label else exp_label}")
    logger.info(f"Prefer boards: {'Yes' if prefer_boards else 'No'}  • Allow remote: {'Yes' if allow_remote else 'No'}  • Strict location: {'On' if STRICT_LOCATION else 'Off'}")
    if domains:
        logger.info(f"Extra domains: {', '.join(domains)}")
    logger.info(f"Target    : at least {min_results_target} results")
    logger.info(f"Output    : {csv_path}\n")

    total_results_seen = 0
    total_pages_parsed = 0
    total_jsonld_hits = 0
    total_heuristic_hits = 0
    total_closed_skipped = 0

    all_rows: List[dict] = []
    domain_counts: Dict[str, int] = {}

    freshness_steps = [7, 30, 90, 180, 365]   # days
    per_city_steps = [30, 60, 90]             # results per city target

    round_no = 0
    http = HTTPSession(logger)

    # map country to gl (ISO2) if possible
    gl_country = None
    for iso2, fullname in COUNTRY_MAP.items():
        if len(iso2) == 2 and country_norm and fullname == country_norm:
            gl_country = iso2
            break

    for days in freshness_steps:
        for per_city in per_city_steps:
            round_no += 1
            logger.info(f"=== Round {round_no}: freshness last d{days}, per-city target {per_city} ===")

            for city in cities:
                city = city.strip()
                remaining = per_city
                start = 1
                page_index = 0
                city_rows: List[dict] = []

                while remaining > 0:
                    batch = min(10, remaining)
                    page_index += 1
                    got_items = []

                    # Aggregate results across roles for this page window
                    for kw in roles:
                        query = build_query(
                            role=kw.strip(),
                            city=city,
                            industries=industries,
                            jobtype_tokens=jobtype_tokens,
                            exp_tokens=exp_tokens,
                            prefer_job_boards=prefer_boards,
                            custom_domains=domains,
                            country_hint=country_norm,
                        )
                        if verbose:
                            logger.debug(f"→ Query: [{city}] [{kw}] (d{days})\n    {query}")
                        try:
                            data = google_cse_search(query, num=batch, start=start, days=days, gl_country=gl_country, logger=logger)
                        except Exception as e:
                            logger.warn(f"Google CSE failure: {e}")
                            continue
                        items = data.get("items", [])
                        for it in items:
                            url = it.get("link")
                            if not url:
                                continue
                            url = clean_redirector(url)
                            if not is_probably_html(url):
                                continue
                            dom_netloc = registrable_domain(url)
                            if dom_netloc in BLACKLIST_DOMAINS:
                                continue
                            existing = domain_counts.get(dom_netloc, 0)
                            # prefetch cap: skip if domain already at cap
                            if existing >= PER_DOMAIN_CAP:
                                continue
                            got_items.append({"link": url, "dom": dom_netloc})

                    got = len(got_items)
                    total_results_seen += got
                    logger.info(f"  • Page {page_index}: aggregated {got} result links across roles (start={start})")
                    if not got_items:
                        break

                    # Concurrent fetch
                    futures = {}
                    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as ex:
                        for rec in got_items:
                            futures[ex.submit(fetch_and_parse, rec["link"], city, logger, http)] = rec

                        for fut in as_completed(futures):
                            rec = futures[fut]
                            row = fut.result()
                            dom_netloc = rec["dom"]
                            if not row:
                                continue
                            if row.get("__closed__"):
                                total_closed_skipped += 1
                                continue
                            # post-filter domain cap
                            if domain_counts.get(dom_netloc, 0) >= PER_DOMAIN_CAP:
                                continue
                            total_pages_parsed += 1
                            node_used = "JSON-LD" if row.get("date_posted") else "Heuristic"
                            if node_used == "JSON-LD":
                                total_jsonld_hits += 1
                            else:
                                total_heuristic_hits += 1
                            row["__dom__"] = dom_netloc
                            city_rows.append(row)

                    # Post-filter by location and finalize cap
                    filtered = []
                    for r in city_rows:
                        ok, reason = matches_desired_location(r, [city], country_norm, allow_remote=allow_remote)
                        if not ok:
                            continue
                        dom_netloc = r.get("__dom__") or registrable_domain(r.get("source_url",""))
                        if domain_counts.get(dom_netloc, 0) >= PER_DOMAIN_CAP:
                            continue
                        r["location_match_reason"] = reason
                        domain_counts[dom_netloc] = domain_counts.get(dom_netloc, 0) + 1
                        filtered.append(r)

                    all_rows.extend(filtered)

                    # Check target after each page
                    if len(unique_rows(all_rows)) >= min_results_target:
                        break

                    start += got  # paginate
                    remaining -= got

                logger.info(f"  • Finished [{city}] — cumulative kept rows: {len(all_rows)}\n")
                if len(unique_rows(all_rows)) >= min_results_target:
                    break
            if len(unique_rows(all_rows)) >= min_results_target:
                break

    # Dedup + sort by date_posted (newest first)
    before_dedup = len(all_rows)
    all_rows = unique_rows(all_rows, key=("title","company","apply_url"))
    deduped = len(all_rows)

    def sort_key(r):
        dp = r.get("date_posted") or ""
        try:
            return dtparse(dp).date()
        except Exception:
            return date(1970,1,1)

    all_rows.sort(key=sort_key, reverse=True)

    if deduped == 0:
        print("\n⚠️ No relevant openings found for your filters. Try one or more of these:\n  • Widen the freshness window or add nearby cities\n  • Turn off strict location (set STRICT_LOCATION=False at top)\n  • Enable remote roles when prompted\n  • Add company career domains or large job boards\nSaving an empty CSV for traceability…")

    columns = [
        "source_url", "title", "company", "location", "city", "date_posted",
        "valid_through", "employment_type", "salary", "description",
        "apply_url", "job_id", "remote",
        "experience_level_detected",
        "normalized_city", "normalized_country", "normalized_region",
        "location_match_reason", "closed_reason"
    ]
    df = pd.DataFrame(all_rows)
    for c in columns:
        if c not in df.columns:
            df[c] = ""
    df = df[columns]
    df.to_csv(csv_path, index=False, encoding="utf-8")

    # Final summary
    print("\nSUMMARY")
    print("-------")
    print(f"Results returned from Google : {total_results_seen}")
    print(f"Pages fetched & parsed       : {total_pages_parsed}")
    print(f"JSON-LD extractions          : {total_jsonld_hits}")
    print(f"Heuristic extractions        : {total_heuristic_hits}")
    print(f"Closed/expired skipped       : {total_closed_skipped}")
    print(f"Rows before dedupe           : {before_dedup}")
    print(f"Rows after dedupe            : {deduped}")
    print(f"Per-domain counts (capped {PER_DOMAIN_CAP}) : {domain_counts}")
    print(f"CSV saved to                 : {csv_path}")

if __name__ == "__main__":
    main()
