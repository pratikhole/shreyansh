"""
Website Monitor
Level-2 website change monitoring system.

Target:
    https://www.excelr.com/

Designed to run locally or inside GitHub Actions.

No authentication bypass.
No CAPTCHA/WAF bypass.
No stealth crawling.
Respects robots.txt.
"""

from __future__ import annotations

import asyncio
import difflib
import gzip
import hashlib
import json
import logging
import os
import re
import sqlite3
import sys
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from typing import Any
from urllib.parse import (
    parse_qsl,
    urlencode,
    urljoin,
    urlparse,
    urlunparse,
)

import httpx
from bs4 import BeautifulSoup


# ============================================================
# CONFIGURATION
# ============================================================

BASE_URL = os.getenv(
    "BASE_URL",
    "https://www.excelr.com/",
).rstrip("/") + "/"

SITEMAP_URL = os.getenv(
    "SITEMAP_URL",
    "https://www.excelr.com/sitemap.xml",
)

USER_AGENT = os.getenv(
    "USER_AGENT",
    "WebsiteAudit/1.0",
)

DATABASE = os.getenv(
    "DATABASE",
    "monitor.db",
)

SNAPSHOT_DIR = os.getenv(
    "SNAPSHOT_DIR",
    "snapshots",
)

MAX_CONCURRENCY = int(
    os.getenv("MAX_CONCURRENCY", "8")
)

REQUEST_TIMEOUT = float(
    os.getenv("REQUEST_TIMEOUT", "30")
)

REQUEST_INTERVAL = float(
    os.getenv("REQUEST_INTERVAL_SECONDS", "0.15")
)

MAX_RETRIES = int(
    os.getenv("MAX_RETRIES", "3")
)

# Minimum successful pages required after baseline exists.
MIN_SUCCESS_ABSOLUTE = 100

# Do not replace a baseline if the new crawl suddenly
# drops below this percentage of the previous successful crawl.
MIN_SUCCESS_RATIO = 0.60

# Maximum number of internal-link-discovered URLs.
MAX_DISCOVERED_URLS = int(
    os.getenv("MAX_DISCOVERED_URLS", "20000")
)

# Maximum content characters stored/diffed per page.
MAX_CONTENT_CHARS = int(
    os.getenv("MAX_CONTENT_CHARS", "300000")
)

TRACKING_PARAMS = {
    "utm_source",
    "utm_medium",
    "utm_campaign",
    "utm_term",
    "utm_content",
    "gclid",
    "fbclid",
    "msclkid",
    "dclid",
    "mc_cid",
    "mc_eid",
    "_ga",
}

IGNORED_CONTENT_CLASSES = {
    "cookie",
    "cookies",
    "cookie-banner",
    "cookie-consent",
    "consent",
    "popup",
    "modal",
    "advertisement",
    "ads",
    "social-share",
}

RETRY_STATUS_CODES = {
    408,
    425,
    429,
    500,
    502,
    503,
    504,
}

# HTTP errors that should be recorded as failures rather
# than causing a page to disappear from the baseline.
FAILURE_STATUS_CODES = {
    403,
    404,
    408,
    425,
    429,
    500,
    501,
    502,
    503,
    504,
}


# ============================================================
# LOGGING
# ============================================================

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s %(levelname)s %(message)s",
)

logger = logging.getLogger("excelr-monitor")


# ============================================================
# DATA MODELS
# ============================================================

@dataclass
class PageSnapshot:
    url: str
    status: int | None
    final_url: str
    content_type: str

    title: str
    meta_description: str
    canonical: str
    h1: list[str]
    robots: str

    content: str

    images: list[dict[str, str]]
    internal_links: list[str]

    schema: list[Any]

    response_time_ms: int

    content_hash: str
    metadata_hash: str


@dataclass
class FailedPage:
    url: str
    status: int | None
    error_type: str
    message: str
    retries: int
    timestamp: str


# ============================================================
# GENERAL HELPERS
# ============================================================

def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def sha256_text(value: str) -> str:
    return hashlib.sha256(
        value.encode("utf-8", errors="ignore")
    ).hexdigest()


def clean_text(value: str | None) -> str:
    if not value:
        return ""

    value = value.replace("\xa0", " ")

    # Normalize whitespace but preserve actual words.
    value = re.sub(r"[ \t]+", " ", value)
    value = re.sub(r"\n[ \t]+", "\n", value)
    value = re.sub(r"\n{3,}", "\n\n", value)

    return value.strip()


def canonical_json(value: Any) -> str:
    """
    Serialize JSON deterministically so formatting/key-order
    differences don't create false schema changes.
    """
    return json.dumps(
        value,
        ensure_ascii=False,
        sort_keys=True,
        separators=(",", ":"),
    )


def is_same_domain(url: str) -> bool:
    base = urlparse(BASE_URL)
    target = urlparse(url)

    return (
        target.scheme in {"http", "https"}
        and target.netloc.lower() == base.netloc.lower()
    )


def normalize_url(url: str, base_url: str = BASE_URL) -> str | None:
    """
    Normalize URL without destroying meaningful query parameters.
    """

    try:
        absolute = urljoin(base_url, url)
        parsed = urlparse(absolute)

        if parsed.scheme not in {"http", "https"}:
            return None

        if not is_same_domain(absolute):
            return None

        # Remove fragments.
        fragment = ""

        # Remove obvious tracking parameters.
        query_items = []

        for key, value in parse_qsl(
            parsed.query,
            keep_blank_values=True,
        ):
            if key.lower() in TRACKING_PARAMS:
                continue

            query_items.append((key, value))

        query_items.sort()

        query = urlencode(
            query_items,
            doseq=True,
        )

        path = parsed.path or "/"

        # Normalize repeated slashes.
        path = re.sub(r"/{2,}", "/", path)

        # Normalize trailing slash.
        if path != "/":
            path = path.rstrip("/") + "/"

        normalized = urlunparse(
            (
                parsed.scheme.lower(),
                parsed.netloc.lower(),
                path,
                "",
                query,
                fragment,
            )
        )

        return normalized

    except Exception:
        return None


def looks_like_html_url(url: str) -> bool:
    parsed = urlparse(url)
    path = parsed.path.lower()

    ignored_extensions = (
        ".pdf",
        ".jpg",
        ".jpeg",
        ".png",
        ".gif",
        ".webp",
        ".svg",
        ".ico",
        ".css",
        ".js",
        ".zip",
        ".rar",
        ".7z",
        ".mp4",
        ".webm",
        ".mov",
        ".avi",
        ".mp3",
        ".wav",
        ".doc",
        ".docx",
        ".xls",
        ".xlsx",
        ".ppt",
        ".pptx",
    )

    return not path.endswith(ignored_extensions)


def looks_like_bad_link(value: str) -> bool:
    lowered = value.lower().strip()

    return lowered.startswith(
        (
            "mailto:",
            "tel:",
            "javascript:",
            "data:",
        )
    )


# ============================================================
# ROBOTS.TXT
# ============================================================

class RobotsChecker:
    """
    Lightweight robots.txt implementation.

    It intentionally does not attempt to bypass robots rules.
    """

    def __init__(self, robots_text: str):
        self.rules: list[tuple[str, str]] = []
        self.parse(robots_text)

    def parse(self, text: str) -> None:
        current_agents: list[str] = []

        for raw_line in text.splitlines():
            line = raw_line.split("#", 1)[0].strip()

            if not line:
                continue

            if ":" not in line:
                continue

            key, value = line.split(":", 1)

            key = key.strip().lower()
            value = value.strip()

            if key == "user-agent":
                current_agents = [
                    value.lower()
                ]
                continue

            if key == "disallow" and current_agents:
                for agent in current_agents:
                    if agent in {"*", "websiteaudit", "websiteaudit/1.0"}:
                        self.rules.append(
                            ("disallow", value)
                        )

    def allowed(self, url: str) -> bool:
        path = urlparse(url).path or "/"

        for _, rule in self.rules:
            if not rule:
                continue

            if path.startswith(rule):
                return False

        return True


# ============================================================
# DATABASE
# ============================================================

class Database:
    def __init__(self, path: str):
        self.path = path

        self.conn = sqlite3.connect(
            self.path,
            timeout=60,
        )

        self.conn.row_factory = sqlite3.Row

        self.conn.execute(
            "PRAGMA journal_mode=WAL"
        )

        self.conn.execute(
            "PRAGMA synchronous=NORMAL"
        )

        self.conn.execute(
            "PRAGMA foreign_keys=ON"
        )

        self.create_tables()

    def create_tables(self) -> None:
        self.conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS runs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                started_at TEXT NOT NULL,
                finished_at TEXT,
                discovered INTEGER DEFAULT 0,
                successful INTEGER DEFAULT 0,
                new_pages INTEGER DEFAULT 0,
                changed_pages INTEGER DEFAULT 0,
                removed_pages INTEGER DEFAULT 0,
                failed_pages INTEGER DEFAULT 0,
                duration_seconds REAL,
                status TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS pages (
                url TEXT PRIMARY KEY,
                snapshot_path TEXT NOT NULL,
                content_hash TEXT NOT NULL,
                metadata_hash TEXT NOT NULL,
                last_success_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS changes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                run_id INTEGER NOT NULL,
                url TEXT NOT NULL,
                priority TEXT NOT NULL,
                changed_fields TEXT NOT NULL,
                created_at TEXT NOT NULL,

                FOREIGN KEY(run_id)
                    REFERENCES runs(id)
                    ON DELETE CASCADE
            );

            CREATE TABLE IF NOT EXISTS failures (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                run_id INTEGER NOT NULL,
                url TEXT NOT NULL,
                status INTEGER,
                error_type TEXT NOT NULL,
                message TEXT,
                retries INTEGER DEFAULT 0,
                created_at TEXT NOT NULL,

                FOREIGN KEY(run_id)
                    REFERENCES runs(id)
                    ON DELETE CASCADE
            );

            CREATE INDEX IF NOT EXISTS idx_changes_run
                ON changes(run_id);

            CREATE INDEX IF NOT EXISTS idx_failures_run
                ON failures(run_id);
            """
        )

        self.conn.commit()

    def has_baseline(self) -> bool:
        row = self.conn.execute(
            "SELECT COUNT(*) AS c FROM pages"
        ).fetchone()

        return bool(row["c"])

    def baseline_count(self) -> int:
        row = self.conn.execute(
            "SELECT COUNT(*) AS c FROM pages"
        ).fetchone()

        return int(row["c"])

    def get_baseline_urls(self) -> set[str]:
        rows = self.conn.execute(
            "SELECT url FROM pages"
        ).fetchall()

        return {
            row["url"]
            for row in rows
        }

    def get_baseline(self, url: str) -> dict[str, Any] | None:
        row = self.conn.execute(
            "SELECT * FROM pages WHERE url = ?",
            (url,),
        ).fetchone()

        if not row:
            return None

        snapshot_path = row["snapshot_path"]

        if not os.path.exists(snapshot_path):
            return None

        try:
            with gzip.open(
                snapshot_path,
                "rt",
                encoding="utf-8",
            ) as f:
                return json.load(f)

        except Exception as exc:
            logger.warning(
                "Could not read baseline for %s: %s",
                url,
                exc,
            )
            return None

    def start_run(self) -> int:
        cursor = self.conn.execute(
            """
            INSERT INTO runs (
                started_at,
                status
            )
            VALUES (?, ?)
            """,
            (
                utc_now(),
                "RUNNING",
            ),
        )

        self.conn.commit()

        return int(cursor.lastrowid)

    def finish_run(
        self,
        run_id: int,
        discovered: int,
        successful: int,
        new_pages: int,
        changed_pages: int,
        removed_pages: int,
        failed_pages: int,
        duration: float,
        status: str,
    ) -> None:

        self.conn.execute(
            """
            UPDATE runs
            SET
                finished_at = ?,
                discovered = ?,
                successful = ?,
                new_pages = ?,
                changed_pages = ?,
                removed_pages = ?,
                failed_pages = ?,
                duration_seconds = ?,
                status = ?
            WHERE id = ?
            """,
            (
                utc_now(),
                discovered,
                successful,
                new_pages,
                changed_pages,
                removed_pages,
                failed_pages,
                duration,
                status,
                run_id,
            ),
        )

        self.conn.commit()

    def save_change(
        self,
        run_id: int,
        url: str,
        priority: str,
        changed_fields: dict[str, Any],
    ) -> None:

        self.conn.execute(
            """
            INSERT INTO changes (
                run_id,
                url,
                priority,
                changed_fields,
                created_at
            )
            VALUES (?, ?, ?, ?, ?)
            """,
            (
                run_id,
                url,
                priority,
                json.dumps(
                    changed_fields,
                    ensure_ascii=False,
                ),
                utc_now(),
            ),
        )

        self.conn.commit()

    def save_failure(
        self,
        run_id: int,
        failure: FailedPage,
    ) -> None:

        self.conn.execute(
            """
            INSERT INTO failures (
                run_id,
                url,
                status,
                error_type,
                message,
                retries,
                created_at
            )
            VALUES (?, ?, ?, ?, ?, ?, ?)
            """,
            (
                run_id,
                failure.url,
                failure.status,
                failure.error_type,
                failure.message,
                failure.retries,
                failure.timestamp,
            ),
        )

        self.conn.commit()

    def replace_baseline(
        self,
        snapshots: dict[str, PageSnapshot],
    ) -> None:

        os.makedirs(
            SNAPSHOT_DIR,
            exist_ok=True,
        )

        # Write new snapshots first.
        new_rows = []

        for url, snapshot in snapshots.items():

            filename = (
                sha256_text(url)
                + ".json.gz"
            )

            path = os.path.join(
                SNAPSHOT_DIR,
                filename,
            )

            temp_path = path + ".tmp"

            with gzip.open(
                temp_path,
                "wt",
                encoding="utf-8",
            ) as f:
                json.dump(
                    asdict(snapshot),
                    f,
                    ensure_ascii=False,
                    separators=(",", ":"),
                )

            os.replace(
                temp_path,
                path,
            )

            new_rows.append(
                (
                    url,
                    path,
                    snapshot.content_hash,
                    snapshot.metadata_hash,
                    utc_now(),
                )
            )

        # Atomic database transaction.
        with self.conn:
            self.conn.execute(
                "DELETE FROM pages"
            )

            self.conn.executemany(
                """
                INSERT INTO pages (
                    url,
                    snapshot_path,
                    content_hash,
                    metadata_hash,
                    last_success_at
                )
                VALUES (?, ?, ?, ?, ?)
                """,
                new_rows,
            )

    def recent_runs(self, limit: int = 20):
        return self.conn.execute(
            """
            SELECT *
            FROM runs
            ORDER BY id DESC
            LIMIT ?
            """,
            (limit,),
        ).fetchall()

    def close(self):
        self.conn.close()


# ============================================================
# SITEMAP
# ============================================================

async def fetch_text(
    client: httpx.AsyncClient,
    url: str,
) -> tuple[int | None, str, str]:

    try:
        response = await client.get(
            url,
            follow_redirects=True,
        )

        return (
            response.status_code,
            response.text,
            str(response.url),
        )

    except Exception as exc:
        logger.error(
            "Failed fetching %s: %s",
            url,
            exc,
        )

        return (
            None,
            "",
            url,
        )


def parse_sitemap(
    xml: str,
) -> tuple[list[str], list[str]]:

    soup = BeautifulSoup(
        xml,
        "xml",
    )

    sitemap_urls = []

    for loc in soup.find_all("sitemap"):
        node = loc.find("loc")

        if node and node.text:
            sitemap_urls.append(
                node.text.strip()
            )

    page_urls = []

    for url_node in soup.find_all("url"):
        node = url_node.find("loc")

        if node and node.text:
            page_urls.append(
                node.text.strip()
            )

    return sitemap_urls, page_urls


async def discover_sitemap_urls(
    client: httpx.AsyncClient,
) -> tuple[set[str], bool]:

    queue = [SITEMAP_URL]
    visited = set()
    urls: set[str] = set()

    sitemap_ok = False

    while queue:

        sitemap = queue.pop(0)

        if sitemap in visited:
            continue

        visited.add(sitemap)

        status, text, _ = await fetch_text(
            client,
            sitemap,
        )

        if status != 200 or not text:
            logger.warning(
                "[SITEMAP] Failed: %s (%s)",
                sitemap,
                status,
            )
            continue

        sitemap_ok = True

        child_sitemaps, page_urls = parse_sitemap(
            text
        )

        for child in child_sitemaps:
            if child not in visited:
                queue.append(child)

        for page in page_urls:

            normalized = normalize_url(page)

            if (
                normalized
                and looks_like_html_url(normalized)
            ):
                urls.add(normalized)

        if len(urls) >= MAX_DISCOVERED_URLS:
            break

    logger.info(
        "[SITEMAP] %d HTML URLs found",
        len(urls),
    )

    return urls, sitemap_ok


# ============================================================
# HTML EXTRACTION
# ============================================================

def remove_noise(soup: BeautifulSoup) -> None:

    for tag in soup(
        [
            "script",
            "style",
            "noscript",
            "template",
            "svg",
            "iframe",
        ]
    ):
        tag.decompose()

    for tag in soup.find_all(
        [
            "header",
            "footer",
            "nav",
        ]
    ):
        # Header/footer/nav can contain useful links,
        # therefore we do not delete them globally here.
        pass

    for tag in soup.find_all(True):

        classes = " ".join(
            tag.get("class", [])
        ).lower()

        tag_id = str(
            tag.get("id", "")
        ).lower()

        combined = (
            classes
            + " "
            + tag_id
        )

        if any(
            token in combined
            for token in IGNORED_CONTENT_CLASSES
        ):
            tag.decompose()


def extract_title(
    soup: BeautifulSoup,
) -> str:

    title = soup.find("title")

    return clean_text(
        title.get_text(" ", strip=True)
        if title
        else ""
    )


def extract_meta_description(
    soup: BeautifulSoup,
) -> str:

    tag = soup.find(
        "meta",
        attrs={
            "name": re.compile(
                r"^description$",
                re.I,
            )
        },
    )

    if not tag:
        return ""

    return clean_text(
        tag.get("content", "")
    )


def extract_canonical(
    soup: BeautifulSoup,
    page_url: str,
) -> str:

    tag = soup.find(
        "link",
        attrs={
            "rel": lambda value:
                value
                and "canonical" in value
        },
    )

    if not tag:
        return ""

    href = tag.get("href")

    if not href:
        return ""

    return (
        normalize_url(
            urljoin(
                page_url,
                href,
            )
        )
        or ""
    )


def extract_h1(
    soup: BeautifulSoup,
) -> list[str]:

    return [
        clean_text(
            tag.get_text(
                " ",
                strip=True,
            )
        )
        for tag in soup.find_all("h1")
        if clean_text(
            tag.get_text(
                " ",
                strip=True,
            )
        )
    ]


def extract_robots(
    soup: BeautifulSoup,
) -> str:

    tag = soup.find(
        "meta",
        attrs={
            "name": re.compile(
                r"^robots$",
                re.I,
            )
        },
    )

    if not tag:
        return ""

    return clean_text(
        tag.get("content", "")
    ).lower()


def extract_content(
    soup: BeautifulSoup,
) -> str:

    # Prefer main/article when available.
    container = (
        soup.find("main")
        or soup.find("article")
        or soup.body
        or soup
    )

    text = container.get_text(
        "\n",
        strip=True,
    )

    text = clean_text(text)

    return text[:MAX_CONTENT_CHARS]


def extract_images(
    soup: BeautifulSoup,
    page_url: str,
) -> list[dict[str, str]]:

    images = []

    seen = set()

    for img in soup.find_all("img"):

        src = (
            img.get("src")
            or img.get("data-src")
            or img.get("data-lazy-src")
            or ""
        )

        if not src:
            continue

        absolute = urljoin(
            page_url,
            src,
        )

        parsed = urlparse(absolute)

        parsed = parsed._replace(
            fragment=""
        )

        normalized = urlunparse(parsed)

        if normalized in seen:
            continue

        seen.add(normalized)

        images.append(
            {
                "url": normalized,
                "alt": clean_text(
                    img.get("alt", "")
                ),
            }
        )

    images.sort(
        key=lambda item: (
            item["url"],
            item["alt"],
        )
    )

    return images


def extract_internal_links(
    soup: BeautifulSoup,
    page_url: str,
) -> list[str]:

    links = set()

    for anchor in soup.find_all("a"):

        href = anchor.get("href")

        if not href:
            continue

        if looks_like_bad_link(href):
            continue

        normalized = normalize_url(
            urljoin(
                page_url,
                href,
            )
        )

        if not normalized:
            continue

        if not looks_like_html_url(normalized):
            continue

        links.add(normalized)

    return sorted(links)


def extract_schema(
    soup: BeautifulSoup,
) -> list[Any]:

    result = []

    for script in soup.find_all(
        "script",
        attrs={
            "type": re.compile(
                r"application/ld\+json",
                re.I,
            )
        },
    ):

        raw = script.string or script.get_text()

        raw = raw.strip()

        if not raw:
            continue

        try:
            data = json.loads(raw)

            result.append(data)

        except Exception:
            # Malformed JSON-LD is retained as raw text
            # so that a real schema break can be detected.
            result.append(
                {
                    "_invalid_jsonld": clean_text(
                        raw
                    )
                }
            )

    # Normalize through deterministic serialization.
    result = json.loads(
        canonical_json(result)
    )

    return result


def build_snapshot(
    html: str,
    status: int,
    final_url: str,
    content_type: str,
    response_time_ms: int,
) -> PageSnapshot:

    soup = BeautifulSoup(
        html,
        "html.parser",
    )

    # Make a separate soup for content so that
    # extraction mutations don't affect metadata.
    content_soup = BeautifulSoup(
        html,
        "html.parser",
    )

    remove_noise(content_soup)

    title = extract_title(soup)
    meta_description = extract_meta_description(soup)
    canonical = extract_canonical(
        soup,
        final_url,
    )
    h1 = extract_h1(soup)
    robots = extract_robots(soup)

    content = extract_content(
        content_soup
    )

    images = extract_images(
        soup,
        final_url,
    )

    internal_links = extract_internal_links(
        soup,
        final_url,
    )

    schema = extract_schema(
        soup
    )

    metadata = {
        "title": title,
        "meta_description": meta_description,
        "canonical": canonical,
        "h1": h1,
        "robots": robots,
        "images": images,
        "internal_links": internal_links,
        "schema": schema,
        "status": status,
        "final_url": normalize_url(
            final_url
        ) or final_url,
    }

    metadata_string = canonical_json(
        metadata
    )

    return PageSnapshot(
        url=normalize_url(final_url) or final_url,
        status=status,
        final_url=final_url,
        content_type=content_type,
        title=title,
        meta_description=meta_description,
        canonical=canonical,
        h1=h1,
        robots=robots,
        content=content,
        images=images,
        internal_links=internal_links,
        schema=schema,
        response_time_ms=response_time_ms,
        content_hash=sha256_text(content),
        metadata_hash=sha256_text(
            metadata_string
        ),
    )


# ============================================================
# PAGE CRAWLING
# ============================================================

async def crawl_page(
    client: httpx.AsyncClient,
    semaphore: asyncio.Semaphore,
    robots: RobotsChecker,
    url: str,
) -> tuple[PageSnapshot | None, FailedPage | None]:

    if not robots.allowed(url):

        failure = FailedPage(
            url=url,
            status=None,
            error_type="robots_disallowed",
            message="URL disallowed by robots.txt",
            retries=0,
            timestamp=utc_now(),
        )

        return None, failure

    async with semaphore:

        retries = 0

        while retries <= MAX_RETRIES:

            try:

                if REQUEST_INTERVAL > 0:
                    await asyncio.sleep(
                        REQUEST_INTERVAL
                    )

                started = time.perf_counter()

                response = await client.get(
                    url,
                    follow_redirects=True,
                )

                elapsed = int(
                    (
                        time.perf_counter()
                        - started
                    )
                    * 1000
                )

                status = response.status_code

                content_type = (
                    response.headers.get(
                        "content-type",
                        "",
                    )
                    .lower()
                )

                # Temporary errors → retry.
                if status in RETRY_STATUS_CODES:

                    if retries < MAX_RETRIES:

                        wait = min(
                            2 ** retries,
                            10,
                        )

                        logger.warning(
                            "[RETRY] %s status=%s wait=%ss",
                            url,
                            status,
                            wait,
                        )

                        await asyncio.sleep(
                            wait
                        )

                        retries += 1

                        continue

                # Non-success response.
                if status < 200 or status >= 300:

                    failure = FailedPage(
                        url=url,
                        status=status,
                        error_type=(
                            f"http_{status}"
                        ),
                        message=(
                            f"HTTP status {status}"
                        ),
                        retries=retries,
                        timestamp=utc_now(),
                    )

                    return None, failure

                # Only parse HTML.
                if (
                    "text/html" not in content_type
                    and "application/xhtml+xml"
                    not in content_type
                ):

                    failure = FailedPage(
                        url=url,
                        status=status,
                        error_type="non_html",
                        message=(
                            f"Content-Type: "
                            f"{content_type}"
                        ),
                        retries=retries,
                        timestamp=utc_now(),
                    )

                    return None, failure

                snapshot = build_snapshot(
                    response.text,
                    status,
                    str(response.url),
                    content_type,
                    elapsed,
                )

                return snapshot, None

            except (
                httpx.TimeoutException,
                httpx.ConnectError,
                httpx.NetworkError,
                httpx.RemoteProtocolError,
            ) as exc:

                if retries < MAX_RETRIES:

                    wait = min(
                        2 ** retries,
                        10,
                    )

                    logger.warning(
                        "[RETRY] %s error=%s wait=%ss",
                        url,
                        type(exc).__name__,
                        wait,
                    )

                    await asyncio.sleep(
                        wait
                    )

                    retries += 1

                    continue

                failure = FailedPage(
                    url=url,
                    status=None,
                    error_type=type(
                        exc
                    ).__name__,
                    message=str(exc),
                    retries=retries,
                    timestamp=utc_now(),
                )

                return None, failure

            except Exception as exc:

                failure = FailedPage(
                    url=url,
                    status=None,
                    error_type=type(
                        exc
                    ).__name__,
                    message=str(exc),
                    retries=retries,
                    timestamp=utc_now(),
                )

                return None, failure

    return None, None


# ============================================================
# DIFF ENGINE
# ============================================================

def sequence_diff(
    old: list[str],
    new: list[str],
) -> dict[str, list[str]]:

    old_set = set(old)
    new_set = set(new)

    return {
        "added": sorted(
            new_set - old_set
        ),
        "removed": sorted(
            old_set - new_set
        ),
    }


def text_diff(
    old: str,
    new: str,
) -> dict[str, list[str]]:

    old_lines = old.splitlines()
    new_lines = new.splitlines()

    matcher = difflib.SequenceMatcher(
        None,
        old_lines,
        new_lines,
    )

    added = []
    removed = []

    for tag, i1, i2, j1, j2 in matcher.get_opcodes():

        if tag in {"replace", "delete"}:

            removed.extend(
                old_lines[i1:i2]
            )

        if tag in {"replace", "insert"}:

            added.extend(
                new_lines[j1:j2]
            )

    return {
        "added": added,
        "removed": removed,
    }


def image_diff(
    old: list[dict[str, str]],
    new: list[dict[str, str]],
) -> dict[str, Any]:

    old_by_url = {
        item["url"]: item
        for item in old
    }

    new_by_url = {
        item["url"]: item
        for item in new
    }

    added = sorted(
        set(new_by_url)
        - set(old_by_url)
    )

    removed = sorted(
        set(old_by_url)
        - set(new_by_url)
    )

    alt_changed = []

    for url in sorted(
        set(old_by_url)
        & set(new_by_url)
    ):

        old_alt = old_by_url[url].get(
            "alt",
            "",
        )

        new_alt = new_by_url[url].get(
            "alt",
            "",
        )

        if old_alt != new_alt:

            alt_changed.append(
                {
                    "url": url,
                    "old": old_alt,
                    "new": new_alt,
                }
            )

    return {
        "added": added,
        "removed": removed,
        "alt_changed": alt_changed,
    }


def schema_diff(
    old: list[Any],
    new: list[Any],
) -> dict[str, Any]:

    old_normalized = json.loads(
        canonical_json(old)
    )

    new_normalized = json.loads(
        canonical_json(new)
    )

    if old_normalized == new_normalized:
        return {
            "changed": False
        }

    return {
        "changed": True,
        "old": old_normalized,
        "new": new_normalized,
    }


def compare_snapshots(
    old: dict[str, Any],
    new: PageSnapshot,
) -> dict[str, Any]:

    changes: dict[str, Any] = {}

    scalar_fields = [
        "title",
        "meta_description",
        "canonical",
        "robots",
        "final_url",
        "status",
    ]

    for field in scalar_fields:

        old_value = old.get(
            field,
            "",
        )

        new_value = getattr(
            new,
            field,
        )

        if old_value != new_value:

            changes[field] = {
                "old": old_value,
                "new": new_value,
            }

    old_h1 = old.get(
        "h1",
        [],
    )

    if old_h1 != new.h1:

        changes["h1"] = {
            "old": old_h1,
            "new": new.h1,
        }

    old_content = old.get(
        "content",
        "",
    )

    if old_content != new.content:

        diff = text_diff(
            old_content,
            new.content,
        )

        if diff["added"] or diff["removed"]:

            changes["content"] = diff

    old_images = old.get(
        "images",
        [],
    )

    image_changes = image_diff(
        old_images,
        new.images,
    )

    if (
        image_changes["added"]
        or image_changes["removed"]
        or image_changes["alt_changed"]
    ):
        changes["images"] = image_changes

    old_links = old.get(
        "internal_links",
        [],
    )

    link_changes = sequence_diff(
        old_links,
        new.internal_links,
    )

    if (
        link_changes["added"]
        or link_changes["removed"]
    ):
        changes["internal_links"] = link_changes

    old_schema = old.get(
        "schema",
        [],
    )

    schema_changes = schema_diff(
        old_schema,
        new.schema,
    )

    if schema_changes["changed"]:
        changes["schema"] = schema_changes

    return changes


# ============================================================
# PRIORITY
# ============================================================

HIGH_FIELDS = {
    "title",
    "meta_description",
    "canonical",
    "h1",
    "robots",
    "content",
    "schema",
    "status",
    "final_url",
    "page_removed",
    "new_page",
}

MEDIUM_FIELDS = {
    "images",
    "internal_links",
}


def calculate_priority(
    changes: dict[str, Any],
) -> str:

    fields = set(
        changes.keys()
    )

    if fields & HIGH_FIELDS:
        return "HIGH"

    if fields & MEDIUM_FIELDS:
        return "MEDIUM"

    return "LOW"


# ============================================================
# BASELINE VALIDATION
# ============================================================

def validate_crawl(
    previous_count: int,
    discovered_count: int,
    successful_count: int,
    sitemap_ok: bool,
    failures: int,
) -> tuple[bool, str]:

    if successful_count == 0:
        return (
            False,
            "No successful HTML pages",
        )

    if previous_count == 0:
        # First baseline.
        if successful_count < MIN_SUCCESS_ABSOLUTE:
            return (
                False,
                (
                    "First crawl has too few "
                    "successful pages"
                ),
            )

        return True, "First valid baseline"

    ratio = (
        successful_count
        / previous_count
    )

    if successful_count < MIN_SUCCESS_ABSOLUTE:
        return (
            False,
            "Successful page count too low",
        )

    if ratio < MIN_SUCCESS_RATIO:
        return (
            False,
            (
                f"Successful count collapsed: "
                f"{successful_count}/"
                f"{previous_count} "
                f"({ratio:.1%})"
            ),
        )

    if discovered_count < MIN_SUCCESS_ABSOLUTE:
        return (
            False,
            "Discovery result suspiciously small",
        )

    # A sitemap failure alone should not necessarily
    # invalidate a crawl if internal-link discovery
    # produced a healthy result. Therefore we don't
    # automatically invalidate solely on sitemap failure.

    return True, "Crawl passed sanity checks"


# ============================================================
# INTERNAL-LINK DISCOVERY
# ============================================================

def discover_links_from_snapshots(
    snapshots: dict[str, PageSnapshot],
) -> set[str]:

    discovered = set()

    for snapshot in snapshots.values():

        for link in snapshot.internal_links:

            normalized = normalize_url(
                link
            )

            if (
                normalized
                and looks_like_html_url(
                    normalized
                )
            ):
                discovered.add(
                    normalized
                )

    return discovered


# ============================================================
# MAIN CRAWL
# ============================================================

async def run_monitor() -> int:

    started = time.perf_counter()

    db = Database(DATABASE)

    run_id = db.start_run()

    previous_count = db.baseline_count()

    logger.info(
        "[BASELINE] %d pages",
        previous_count,
    )

    headers = {
        "User-Agent": USER_AGENT,
        "Accept": (
            "text/html,application/xhtml+xml,"
            "application/xml;q=0.9,*/*;q=0.8"
        ),
        "Accept-Language": "en-US,en;q=0.8",
        "Connection": "keep-alive",
    }

    limits = httpx.Limits(
        max_connections=MAX_CONCURRENCY * 2,
        max_keepalive_connections=MAX_CONCURRENCY,
    )

    timeout = httpx.Timeout(
        REQUEST_TIMEOUT,
        connect=15,
    )

    async with httpx.AsyncClient(
        headers=headers,
        timeout=timeout,
        limits=limits,
    ) as client:

        # ----------------------------------------------------
        # robots.txt
        # ----------------------------------------------------

        robots_url = urljoin(
            BASE_URL,
            "/robots.txt",
        )

        robots_status, robots_text, _ = (
            await fetch_text(
                client,
                robots_url,
            )
        )

        if robots_status == 200:

            robots = RobotsChecker(
                robots_text
            )

            logger.info(
                "[ROBOTS] Loaded robots.txt"
            )

        else:

            logger.warning(
                "[ROBOTS] Could not load robots.txt "
                "(status=%s)",
                robots_status,
            )

            # Fail closed if robots cannot be retrieved.
            robots = RobotsChecker(
                "User-agent: *\nDisallow: /"
            )

        # ----------------------------------------------------
        # Sitemap
        # ----------------------------------------------------

        sitemap_urls, sitemap_ok = (
            await discover_sitemap_urls(
                client
            )
        )

        urls = set(sitemap_urls)

        # Always include homepage.
        homepage = normalize_url(
            BASE_URL
        )

        if homepage:
            urls.add(homepage)

        logger.info(
            "[START] %d candidate pages",
            len(urls),
        )

        # ----------------------------------------------------
        # Crawl sitemap URLs
        # ----------------------------------------------------

        semaphore = asyncio.Semaphore(
            MAX_CONCURRENCY
        )

        snapshots: dict[
            str,
            PageSnapshot,
        ] = {}

        failures: list[
            FailedPage
        ] = []

        url_list = sorted(urls)

        total = len(url_list)

        completed = 0

        async def crawl_and_record(
            url: str,
        ):

            nonlocal completed

            snapshot, failure = await crawl_page(
                client,
                semaphore,
                robots,
                url,
            )

            completed += 1

            if completed % 100 == 0:
                logger.info(
                    "[PROGRESS] %d/%d",
                    completed,
                    total,
                )

            if snapshot:
                normalized = normalize_url(
                    snapshot.url
                )

                if normalized:
                    snapshots[
                        normalized
                    ] = snapshot

            if failure:
                failures.append(
                    failure
                )

        await asyncio.gather(
            *[
                crawl_and_record(url)
                for url in url_list
            ]
        )

        logger.info(
            "[PAGES] %d successful",
            len(snapshots),
        )

        logger.info(
            "[FAILED] %d",
            len(failures),
        )

        # ----------------------------------------------------
        # Internal link discovery
        # ----------------------------------------------------

        internal_urls = (
            discover_links_from_snapshots(
                snapshots
            )
        )

        new_candidates = (
            internal_urls
            - set(snapshots.keys())
        )

        # Avoid uncontrolled URL explosion.
        if len(new_candidates) > MAX_DISCOVERED_URLS:
            new_candidates = set(
                sorted(new_candidates)[
                    :MAX_DISCOVERED_URLS
                ]
            )

        if new_candidates:

            logger.info(
                "[LINK DISCOVERY] %d additional URLs",
                len(new_candidates),
            )

            additional_urls = sorted(
                new_candidates
            )

            total_additional = len(
                additional_urls
            )

            additional_completed = 0

            async def crawl_additional(
                url: str,
            ):

                nonlocal additional_completed

                snapshot, failure = await crawl_page(
                    client,
                    semaphore,
                    robots,
                    url,
                )

                additional_completed += 1

                if (
                    additional_completed % 100
                    == 0
                ):
                    logger.info(
                        "[LINK PROGRESS] %d/%d",
                        additional_completed,
                        total_additional,
                    )

                if snapshot:

                    normalized = normalize_url(
                        snapshot.url
                    )

                    if normalized:
                        snapshots[
                            normalized
                        ] = snapshot

                if failure:
                    failures.append(
                        failure
                    )

            await asyncio.gather(
                *[
                    crawl_additional(url)
                    for url in additional_urls
                ]
            )

    # ========================================================
    # VALIDATION
    # ========================================================

    successful_count = len(
        snapshots
    )

    valid, validation_reason = validate_crawl(
        previous_count=previous_count,
        discovered_count=len(urls)
        + len(new_candidates),
        successful_count=successful_count,
        sitemap_ok=sitemap_ok,
        failures=len(failures),
    )

    logger.info(
        "[VALIDATION] %s — %s",
        "VALID" if valid else "INVALID",
        validation_reason,
    )

    # ========================================================
    # FAILED / INVALID RUN
    # ========================================================

    for failure in failures:
        db.save_failure(
            run_id,
            failure,
        )

    if not valid:

        duration = (
            time.perf_counter()
            - started
        )

        db.finish_run(
            run_id=run_id,
            discovered=len(urls),
            successful=successful_count,
            new_pages=0,
            changed_pages=0,
            removed_pages=0,
            failed_pages=len(failures),
            duration=duration,
            status="INVALID",
        )

        logger.error(
            "[BASELINE] PROTECTED — "
            "previous baseline was not replaced"
        )

        db.close()

        return 2

    # ========================================================
    # FIRST BASELINE
    # ========================================================

    if not db.has_baseline():

        db.replace_baseline(
            snapshots
        )

        duration = (
            time.perf_counter()
            - started
        )

        db.finish_run(
            run_id=run_id,
            discovered=len(urls),
            successful=successful_count,
            new_pages=0,
            changed_pages=0,
            removed_pages=0,
            failed_pages=len(failures),
            duration=duration,
            status="SUCCESS",
        )

        logger.info(
            "[BASELINE] Created with %d pages",
            successful_count,
        )

        logger.info(
            "[COMPLETE] Duration: %.2fs",
            duration,
        )

        db.close()

        return 0

    # ========================================================
    # COMPARE AGAINST VALID BASELINE
    # ========================================================

    baseline_urls = (
        db.get_baseline_urls()
    )

    current_urls = set(
        snapshots.keys()
    )

    new_urls = (
        current_urls
        - baseline_urls
    )

    # IMPORTANT:
    # Failed pages are not included in current_urls,
    # therefore they are NOT automatically considered removed.
    #
    # We only consider a page removed if:
    #   1. It existed in baseline
    #   2. It was NOT successfully crawled now
    #   3. It was NOT among failed URLs
    #
    failed_urls = {
        failure.url
        for failure in failures
    }

    removed_urls = (
        baseline_urls
        - current_urls
        - failed_urls
    )

    changed_pages = 0
    changes_total = 0

    # --------------------------------------------------------
    # Page changes
    # --------------------------------------------------------

    for url in sorted(
        current_urls & baseline_urls
    ):

        old = db.get_baseline(
            url
        )

        if not old:
            continue

        new_snapshot = snapshots[
            url
        ]

        changes = compare_snapshots(
            old,
            new_snapshot,
        )

        if not changes:
            continue

        changed_pages += 1

        priority = calculate_priority(
            changes
        )

        db.save_change(
            run_id=run_id,
            url=url,
            priority=priority,
            changed_fields=changes,
        )

        changes_total += len(
            changes
        )

        logger.info(
            "[CHANGED] %s [%s] fields=%s",
            url,
            priority,
            ", ".join(changes.keys()),
        )

    # --------------------------------------------------------
    # New pages
    # --------------------------------------------------------

    for url in sorted(
        new_urls
    ):

        changes = {
            "new_page": True
        }

        db.save_change(
            run_id=run_id,
            url=url,
            priority="HIGH",
            changed_fields=changes,
        )

        logger.info(
            "[NEW] %s",
            url,
        )

    # --------------------------------------------------------
    # Removed pages
    # --------------------------------------------------------

    for url in sorted(
        removed_urls
    ):

        changes = {
            "page_removed": True
        }

        db.save_change(
            run_id=run_id,
            url=url,
            priority="HIGH",
            changed_fields=changes,
        )

        logger.info(
            "[REMOVED] %s",
            url,
        )

    # ========================================================
    # REPLACE BASELINE
    # ========================================================

    #
    # IMPORTANT:
    #
    # A successful page becomes part of the new baseline.
    #
    # A failed page is preserved from the old baseline.
    #
    # This prevents temporary failures from deleting data.
    #

    merged_snapshots = dict(
        snapshots
    )

    for failed_url in failed_urls:

        old = db.get_baseline(
            failed_url
        )

        if old and failed_url not in merged_snapshots:

            try:

                merged_snapshots[
                    failed_url
                ] = PageSnapshot(
                    **{
                        key: old[key]
                        for key in PageSnapshot.__dataclass_fields__
                        if key in old
                    }
                )

            except Exception:

                logger.warning(
                    "[BASELINE] Could not preserve "
                    "failed page: %s",
                    failed_url,
                )

    db.replace_baseline(
        merged_snapshots
    )

    duration = (
        time.perf_counter()
        - started
    )

    db.finish_run(
        run_id=run_id,
        discovered=(
            len(urls)
            + len(new_candidates)
        ),
        successful=successful_count,
        new_pages=len(new_urls),
        changed_pages=changed_pages,
        removed_pages=len(removed_urls),
        failed_pages=len(failures),
        duration=duration,
        status="SUCCESS",
    )

    logger.info(
        "[NEW] %d pages",
        len(new_urls),
    )

    logger.info(
        "[CHANGED] %d pages",
        changed_pages,
    )

    logger.info(
        "[REMOVED] %d pages",
        len(removed_urls),
    )

    logger.info(
        "[FAILED] %d pages",
        len(failures),
    )

    logger.info(
        "[PAGES] %d valid pages",
        successful_count,
    )

    logger.info(
        "[COMPLETE] Duration: %.2fs",
        duration,
    )

    db.close()

    return 0


# ============================================================
# ENTRY POINT
# ============================================================

def main():

    try:
        exit_code = asyncio.run(
            run_monitor()
        )

        sys.exit(exit_code)

    except KeyboardInterrupt:

        logger.warning(
            "Monitor interrupted by user."
        )

        sys.exit(130)

    except Exception as exc:

        logger.exception(
            "Fatal monitor error: %s",
            exc,
        )

        sys.exit(1)


if __name__ == "__main__":
    main()
