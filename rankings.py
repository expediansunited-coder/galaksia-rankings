# ==========================================
# 11-a-side Ranking Image Generator
# PFS + PIBFAL
# ==========================================

import os
import re
import time
import io
import json
import sys
import unicodedata
import requests

import pandas as pd

from PIL import Image, ImageDraw, ImageFont, ImageFilter

from google.oauth2.service_account import Credentials
from googleapiclient.discovery import build
from googleapiclient.http import MediaIoBaseDownload

from selenium import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.by import By
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.chrome import ChromeDriverManager


# ============================================================
# CONFIG
# ============================================================
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))

CREDENTIALS_FILE = os.path.join(SCRIPT_DIR, "credentials.json")

LOGOS_FOLDER_ID = "19NNyf1trl1LoA7Tth7PFMbRAv65oXeeR"
BACKGROUNDS_FOLDER_ID = "1QPBNq9ip3d9DwwKK88I5Ff5OVmdqcqYW"

BACKGROUND_TEMPLATE_PATTERN = os.path.join(SCRIPT_DIR, "background {count}.png")
OUTPUT_DIR = os.path.join(SCRIPT_DIR, "output", "rankings")

META_CONFIG_FILE = os.path.join(SCRIPT_DIR, "meta_config.json")

GITHUB_REPO_RAW_BASE = (
    "https://raw.githubusercontent.com/"
    "expediansunited-coder/galaksia-rankings/main/"
)

MANIFEST_FILE = os.path.join(OUTPUT_DIR, "ranking_groups_11aside.json")

RANKING_CONFIGS = [
    {
        "team": "11A",
        "source": "fotbalpraha",
        "url": "https://www.fotbalpraha.cz/souteze/tabulka/752-9-liga-a5b-3-trida-skupina-b-muzu?id_season=2026",
        "league_logo_label": "PFS",
        "galaksia_display": "Galaksia Praha 23",
    },
    {
        "team": "11B",
        "source": "fotbalpraha",
        "url": "https://www.fotbalpraha.cz/souteze/tabulka/753-9-liga-a5c-3-trida-skupina-c-muzu?id_season=2026",
        "league_logo_label": "PFS",
        "galaksia_display": "Galaksia Praha 23 B",
    },
    {
        "team": "11C",
        "source": "pibfal",
        "url": "https://pibfal.com/",
        "league_label": "1.",
        "league_logo_label": "PIBFAL",
        "galaksia_display": "Galaksia Praha 23 C",
    },
]

POST_ORDER = ["11A", "11B", "11C"]

STORY_W = 1080
STORY_H = 1920
GRAPH = "https://graph.facebook.com/v20.0"

TEXT_WHITE = (255, 255, 255)
TEXT_BLACK = (0, 0, 0)
TEXT_LIGA_GREY = (210, 210, 210)
GALAKSIA_GREEN = (55, 190, 75)

BASE_W = 768
BASE_H = 960

TABLE_X_CENTERS = {
    "position": 42,
    "team": 210,
    "matches": 395,
    "wins": 467,
    "draws": 533,
    "losses": 594,
    "diff": 658,
    "points": 722,
}

FIRST_ROW_Y = 398
ROW_H = 38
MAX_ROWS = 12

TEAM_CELL_MAX_W = 285
NUM_CELL_MAX_W = 58

LEAGUE_LABEL_POS = (190, 158)

LEAGUE_LOGO_CENTER = (305, 58)
LEAGUE_LOGO_MAX_SIZE = 95

SEASON_POS = (230, 326)


# ============================================================
# SELENIUM CONFIG
# ============================================================
chrome_options = Options()

USER_AGENT = (
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
    "AppleWebKit/537.36 (KHTML, like Gecko) "
    "Chrome/121.0.0.0 Safari/537.36"
)

chrome_options.add_argument(f"user-agent={USER_AGENT}")
chrome_options.add_argument("--headless=new")
chrome_options.add_argument("--no-sandbox")
chrome_options.add_argument("--disable-dev-shm-usage")
chrome_options.add_argument("--disable-blink-features=AutomationControlled")


# ============================================================
# GENERIC HELPERS
# ============================================================
def clean_text(text):
    if not text:
        return ""
    cleaned = str(text).replace("\xa0", " ").replace("\n", " ").replace("\r", "")
    return re.sub(r"\s+", " ", cleaned).strip()


def scale_xy(x, y, w, h):
    return int(x * w / BASE_W), int(y * h / BASE_H)


def scale_len(v, current, base):
    return int(v * current / base)


def score_diff(score):
    if not score:
        return ""

    m = re.search(r"(-?\d+)\s*[:\-]\s*(-?\d+)", str(score))
    if not m:
        return ""

    try:
        gf = int(m.group(1))
        ga = int(m.group(2))
        diff = gf - ga
        return str(diff)
    except Exception:
        return ""


def get_11aside_season_label():
    now = time.localtime()
    year = now.tm_year
    month = now.tm_mon

    if month >= 7:
        return f"{year}/{year + 1}"
    return f"{year - 1}/{year}"


def load_font(size, bold=True):
    candidates = [
        "Etna.ttf",
        "_etna.ttf",
        "DejaVuSansCondensed-Bold.ttf" if bold else "DejaVuSansCondensed.ttf",
        "DejaVuSans-Bold.ttf" if bold else "DejaVuSans.ttf",
    ]

    for path in candidates:
        try:
            return ImageFont.truetype(path, size)
        except Exception:
            continue

    return ImageFont.load_default()


def fit_font(draw, text, max_width, start_size, min_size=8):
    text = str(text)

    for size in range(start_size, min_size - 1, -1):
        font = load_font(size, bold=True)
        bbox = draw.textbbox((0, 0), text, font=font)
        width = bbox[2] - bbox[0]

        if width <= max_width:
            return font

    return load_font(min_size, bold=True)


def fit_font_inside_canvas(
    draw,
    text,
    start_size,
    xy,
    anchor,
    canvas_w,
    canvas_h,
    min_size=20,
    bold=True,
    stroke_width=0,
    margin=4,
):
    text = str(text)

    for size in range(start_size, min_size - 1, -2):
        font = load_font(size, bold=bold)

        bbox = draw.textbbox(
            xy,
            text,
            font=font,
            anchor=anchor,
            stroke_width=stroke_width,
        )

        if (
            bbox[0] >= margin
            and bbox[1] >= margin
            and bbox[2] <= canvas_w - margin
            and bbox[3] <= canvas_h - margin
        ):
            return font

    return load_font(min_size, bold=bold)


def _norm_drive_name(s):
    if not s:
        return ""
    s = unicodedata.normalize("NFKD", str(s))
    s = "".join(c for c in s if not unicodedata.combining(c))
    return re.sub(r"[^a-z0-9]+", "", s.lower())


def draw_centered_text(draw, xy, text, font, fill, stroke_width=0, stroke_fill=(0, 0, 0)):
    text = str(text)

    bbox = draw.textbbox((0, 0), text, font=font, stroke_width=stroke_width)
    text_w = bbox[2] - bbox[0]
    text_h = bbox[3] - bbox[1]

    x = xy[0] - text_w / 2 - bbox[0]
    y = xy[1] - text_h / 2 - bbox[1]

    draw.text(
        (x, y),
        text,
        font=font,
        fill=fill,
        stroke_width=stroke_width,
        stroke_fill=stroke_fill,
    )


def clean_fotbalpraha_team_name(name):
    s = clean_text(name)

    # Remove quotes around team suffixes: "B" -> B
    s = re.sub(r'["“”„]\s*([A-Za-z])\s*["“”„]', r" \1", s)

    # Remove Czech legal suffixes, including variants like z.s., z. s., a.s., a. s.
    s = re.sub(
        r"\s*,?\s*(z\.?\s*s\.?|a\.?\s*s\.?)\.?(?=\s|$)",
        "",
        s,
        flags=re.I,
    )

    s = re.sub(r"\s+", " ", s).strip()
    s = re.sub(r"\s+,", ",", s).strip()
    return s


def is_galaksia_team_name(name):
    n = _norm_drive_name(name)
    return "galaksia" in n or "gp23" in n


def galaksia_has_played(df):
    if df.empty:
        return False

    for _, row in df.iterrows():
        team_name = str(row.get("Team", ""))
        if not is_galaksia_team_name(team_name):
            continue

        mp = row.get("Matches Played", 0)

        try:
            return int(mp) > 0
        except Exception:
            try:
                return float(str(mp).replace(",", ".")) > 0
            except Exception:
                return False

    return False


# ============================================================
# DRIVE HELPERS
# ============================================================
def get_drive_service():
    scope = ["https://www.googleapis.com/auth/drive.readonly"]
    creds = Credentials.from_service_account_file(CREDENTIALS_FILE, scopes=scope)
    return build("drive", "v3", credentials=creds)


def download_file_bytes(drive, file_id):
    request = drive.files().get_media(fileId=file_id)
    buf = io.BytesIO()
    downloader = MediaIoBaseDownload(buf, request)
    done = False

    while not done:
        status, done = downloader.next_chunk()

    return buf.getvalue()


def list_folder_files(drive, folder_id):
    out, page = [], None

    while True:
        resp = drive.files().list(
            q=f"'{folder_id}' in parents and trashed = false",
            fields="nextPageToken, files(id,name,mimeType)",
            pageToken=page,
        ).execute()

        out.extend(resp.get("files", []))
        page = resp.get("nextPageToken")

        if not page:
            break

    return out


def sync_backgrounds_from_drive(drive):
    files = list_folder_files(drive, BACKGROUNDS_FOLDER_ID)

    for f in files:
        name = f["name"]
        stem, ext = os.path.splitext(name)

        if not re.match(r"^background\s+\d+$", stem.strip(), re.I):
            continue

        if ext.lower() not in (".png", ".jpg", ".jpeg", ".webp"):
            continue

        local_path = os.path.join(SCRIPT_DIR, stem.strip().lower() + ".png")

        raw = download_file_bytes(drive, f["id"])
        img = Image.open(io.BytesIO(raw)).convert("RGBA")
        img.save(local_path, "PNG")

        print(f"  Synced background: {name} -> {local_path}")


def find_league_logo_file(logo_files, logo_label):
    target = _norm_drive_name(logo_label)

    for f in logo_files:
        stem = os.path.splitext(f["name"])[0]
        stem_norm = _norm_drive_name(stem)

        if stem_norm == target:
            return f

    for f in logo_files:
        stem = os.path.splitext(f["name"])[0]
        stem_norm = _norm_drive_name(stem)

        if target in stem_norm:
            return f

    return None


def remove_edge_background(img, tol=40):
    """
    Removes only background connected to image edges.
    Interior white/bright parts inside the logo remain untouched.
    """
    img = img.convert("RGBA")
    w, h = img.size
    px = img.load()

    corners = [px[0, 0], px[w - 1, 0], px[0, h - 1], px[w - 1, h - 1]]
    bg_r = sum(c[0] for c in corners) // 4
    bg_g = sum(c[1] for c in corners) // 4
    bg_b = sum(c[2] for c in corners) // 4

    mask = bytearray(w * h)

    for y in range(h):
        for x in range(w):
            idx = y * w + x
            c = px[x, y]

            if c[3] == 0:
                mask[idx] = 0
                continue

            dist = abs(c[0] - bg_r) + abs(c[1] - bg_g) + abs(c[2] - bg_b)
            mask[idx] = 0 if dist < tol else 1

    from collections import deque

    dq = deque()
    visited = bytearray(w * h)

    for x in range(w):
        for y in (0, h - 1):
            idx = y * w + x
            if mask[idx] == 0 and not visited[idx]:
                dq.append((x, y))
                visited[idx] = 1

    for y in range(h):
        for x in (0, w - 1):
            idx = y * w + x
            if mask[idx] == 0 and not visited[idx]:
                dq.append((x, y))
                visited[idx] = 1

    outside = bytearray(w * h)

    while dq:
        x, y = dq.popleft()
        idx = y * w + x
        outside[idx] = 1

        for dx, dy in ((1, 0), (-1, 0), (0, 1), (0, -1)):
            nx, ny = x + dx, y + dy

            if 0 <= nx < w and 0 <= ny < h:
                nidx = ny * w + nx

                if not visited[nidx] and mask[nidx] == 0:
                    visited[nidx] = 1
                    dq.append((nx, ny))

    new_alpha = bytearray(w * h)

    for y in range(h):
        for x in range(w):
            idx = y * w + x
            c = px[x, y]

            if c[3] == 0:
                new_alpha[idx] = 0
                continue

            if outside[idx]:
                new_alpha[idx] = 0
            else:
                new_alpha[idx] = c[3]

    alpha_img = Image.frombytes("L", (w, h), bytes(new_alpha))
    img.putalpha(alpha_img)

    cb = img.getbbox()
    return img.crop(cb) if cb else img


def load_league_logo(drive, logo_files, league_label):
    logo_file = find_league_logo_file(logo_files, league_label)

    if not logo_file:
        print(f"  Warning: no league logo found for '{league_label}'")
        return None

    try:
        raw = download_file_bytes(drive, logo_file["id"])
        logo = Image.open(io.BytesIO(raw)).convert("RGBA")

        # 11-a-side league logos need edge-only background removal.
        logo = remove_edge_background(logo, tol=60)

        return logo
    except Exception as e:
        print(f"  Warning: could not load league logo '{logo_file['name']}': {e}")
        return None


def paste_logo_centered(base, logo, center_xy, max_size):
    if logo is None:
        return

    logo = logo.copy()
    logo.thumbnail((max_size, max_size), Image.LANCZOS)

    x = int(center_xy[0] - logo.width / 2)
    y = int(center_xy[1] - logo.height / 2)

    base.alpha_composite(logo, (x, y))


# ============================================================
# SCRAPERS
# ============================================================
def extract_fotbalpraha_league_label(driver):
    try:
        h1 = driver.find_element(By.CSS_SELECTOR, "h1")
        title = clean_text(h1.get_attribute("textContent"))

        m_liga = re.search(r"(\d+)\s*\.\s*LIGA", title, re.I)
        m_group = re.search(r"SKUPINA\s+([A-ZÁ-Ž])", title, re.I)

        if m_liga:
            league_num = m_liga.group(1)
            if m_group:
                return f"{league_num}.{m_group.group(1).upper()}"
            return f"{league_num}."

    except Exception:
        pass

    return ""


def scrape_fotbalpraha_ranking_table(driver, cfg):
    ranking_rows = []
    league_label = ""

    url = cfg["url"]

    try:
        print(f"[{time.strftime('%H:%M:%S')}] Scraping Fotbal Praha ranking: {url}")

        driver.get(url)

        wait = WebDriverWait(driver, 60)
        wait.until(EC.presence_of_element_located((By.CSS_SELECTOR, "table tbody tr")))
        time.sleep(1)

        league_label = extract_fotbalpraha_league_label(driver)

        table = driver.find_element(By.CSS_SELECTOR, "table")
        rows = table.find_elements(By.CSS_SELECTOR, "tbody tr")

        for row in rows:
            tds = row.find_elements(By.TAG_NAME, "td")

            if len(tds) < 8:
                continue

            position = clean_text(tds[0].get_attribute("textContent")).rstrip(".")

            team = ""

            try:
                long_span = tds[1].find_element(By.CSS_SELECTOR, "span.long")
                team = clean_text(long_span.get_attribute("textContent"))
            except Exception:
                team = clean_text(tds[1].get_attribute("textContent"))

            team = clean_fotbalpraha_team_name(team)

            if is_galaksia_team_name(team):
                team = cfg["galaksia_display"]

            matches_played = clean_text(tds[2].get_attribute("textContent"))
            wins = clean_text(tds[3].get_attribute("textContent"))
            draws = clean_text(tds[4].get_attribute("textContent"))
            losses = clean_text(tds[5].get_attribute("textContent"))
            score = clean_text(tds[6].get_attribute("textContent"))
            points = clean_text(tds[7].get_attribute("textContent"))

            if len(tds) > 10:
                diff = clean_text(tds[10].get_attribute("textContent"))
            else:
                diff = score_diff(score)

            ranking_rows.append({
                "Position": int(position) if position.isdigit() else position,
                "Team": team,
                "Matches Played": int(matches_played) if matches_played.isdigit() else matches_played,
                "Wins": int(wins) if wins.isdigit() else wins,
                "Draws": int(draws) if draws.isdigit() else draws,
                "Losses": int(losses) if losses.isdigit() else losses,
                "Score": score,
                "Diff": diff,
                "Points": int(points) if points.isdigit() else points,
            })

    except Exception as e:
        print(f"  Warning: Could not extract Fotbal Praha ranking from {url} ({e})")

    return pd.DataFrame(ranking_rows), league_label


def scrape_pibfal_ranking_table(driver, cfg):
    ranking_rows = []

    url = cfg["url"]

    try:
        print(f"[{time.strftime('%H:%M:%S')}] Scraping PIBFAL ranking: {url}")

        driver.get(url)

        wait = WebDriverWait(driver, 60)
        wait.until(EC.presence_of_element_located((By.CSS_SELECTOR, "table.sp-league-table tbody tr")))
        time.sleep(2)

        table = driver.find_element(By.CSS_SELECTOR, "table.sp-league-table")
        rows = table.find_elements(By.CSS_SELECTOR, "tbody tr")

        for row in rows:
            try:
                position = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-rank").get_attribute("textContent"))
                team_cell = row.find_element(By.CSS_SELECTOR, "td.data-name")

                try:
                    team = clean_text(team_cell.find_element(By.TAG_NAME, "a").get_attribute("textContent"))
                except Exception:
                    team = clean_text(team_cell.get_attribute("textContent"))

                matches_played = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-p").get_attribute("textContent"))
                wins = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-w").get_attribute("textContent"))
                draws = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-d").get_attribute("textContent"))
                losses = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-l").get_attribute("textContent"))
                gf = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-f").get_attribute("textContent"))
                ga = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-a").get_attribute("textContent"))
                diff = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-gd").get_attribute("textContent"))
                points = clean_text(row.find_element(By.CSS_SELECTOR, "td.data-pts").get_attribute("textContent"))

                score = f"{gf}:{ga}"

                ranking_rows.append({
                    "Position": int(position) if position.isdigit() else position,
                    "Team": team,
                    "Matches Played": int(matches_played) if matches_played.isdigit() else matches_played,
                    "Wins": int(wins) if wins.isdigit() else wins,
                    "Draws": int(draws) if draws.isdigit() else draws,
                    "Losses": int(losses) if losses.isdigit() else losses,
                    "Score": score,
                    "Diff": diff,
                    "Points": int(points) if points.isdigit() else points,
                })

            except Exception:
                continue

    except Exception as e:
        print(f"  Warning: Could not extract PIBFAL ranking from {url} ({e})")

    return pd.DataFrame(ranking_rows)


# ============================================================
# IMAGE GENERATION
# ============================================================
def draw_ranking_image(df, cfg, league_logo=None):
    team_count = min(len(df), MAX_ROWS)
    background_path = BACKGROUND_TEMPLATE_PATTERN.format(count=team_count)

    if not os.path.exists(background_path):
        raise RuntimeError(f"Background template not found: {background_path}")

    img = Image.open(background_path).convert("RGBA")
    W, H = img.size
    draw = ImageDraw.Draw(img)

    # ---------------- League logo ----------------
    logo_x, logo_y = scale_xy(LEAGUE_LOGO_CENTER[0], LEAGUE_LOGO_CENTER[1], W, H)
    logo_max = scale_len(LEAGUE_LOGO_MAX_SIZE, W, BASE_W)
    paste_logo_centered(img, league_logo, (logo_x, logo_y), logo_max)

    # ---------------- League label beside LIGA ----------------
    league_size = scale_len(130, H, BASE_H)
    league_x, league_y = scale_xy(LEAGUE_LABEL_POS[0], LEAGUE_LABEL_POS[1], W, H)
    league_stroke = max(1, scale_len(2, H, BASE_H))

    league_label = cfg.get("league_label", "")

    league_font = fit_font_inside_canvas(
        draw=draw,
        text=league_label,
        start_size=league_size,
        xy=(league_x, league_y),
        anchor="rm",
        canvas_w=W,
        canvas_h=H,
        min_size=20,
        bold=True,
        stroke_width=league_stroke,
        margin=4,
    )

    draw.text(
        (league_x, league_y),
        league_label,
        font=league_font,
        fill=TEXT_LIGA_GREY,
        anchor="rm",
        stroke_width=league_stroke,
        stroke_fill=(0, 0, 0),
    )

    # ---------------- Season label in green ribbon ----------------
    season_label = get_11aside_season_label()
    season_font = load_font(scale_len(36, H, BASE_H), bold=True)
    season_x, season_y = scale_xy(SEASON_POS[0], SEASON_POS[1], W, H)

    draw.text(
        (season_x, season_y),
        season_label,
        font=season_font,
        fill=TEXT_BLACK,
        anchor="mm",
    )

    # ---------------- Table rows ----------------
    num_start_size = scale_len(24, H, BASE_H)
    team_start_size = scale_len(22, H, BASE_H)

    for i in range(team_count):
        if i >= len(df):
            break

        row = df.iloc[i]

        y = scale_len(FIRST_ROW_Y + i * ROW_H, H, BASE_H)

        team_name = row.get("Team", "")
        is_galaksia = is_galaksia_team_name(team_name)
        row_color = GALAKSIA_GREEN if is_galaksia else TEXT_WHITE

        values = {
            "position": row.get("Position", ""),
            "team": team_name,
            "matches": row.get("Matches Played", ""),
            "wins": row.get("Wins", ""),
            "draws": row.get("Draws", ""),
            "losses": row.get("Losses", ""),
            "diff": row.get("Diff", ""),
            "points": row.get("Points", ""),
        }

        for key, value in values.items():
            # Template already contains ranking numbers 1-12.
            # Do not draw Position again.
            if key == "position":
                continue

            x = scale_len(TABLE_X_CENTERS[key], W, BASE_W)

            if key == "team":
                max_w = scale_len(TEAM_CELL_MAX_W, W, BASE_W)
                font = fit_font(draw, value, max_w, team_start_size, min_size=9)
            else:
                max_w = scale_len(NUM_CELL_MAX_W, W, BASE_W)
                font = fit_font(draw, value, max_w, num_start_size, min_size=8)

            draw_centered_text(
                draw,
                (x, y),
                value,
                font,
                row_color,
                stroke_width=max(1, scale_len(1, H, BASE_H)),
                stroke_fill=(0, 0, 0),
            )

    return img.convert("RGB")


def make_story_version(feed_img_path):
    feed = Image.open(feed_img_path).convert("RGB")

    bg = feed.copy()
    scale = max(STORY_W / bg.width, STORY_H / bg.height)
    bg = bg.resize((int(bg.width * scale), int(bg.height * scale)), Image.LANCZOS)

    left = (bg.width - STORY_W) // 2
    top = (bg.height - STORY_H) // 2

    bg = bg.crop((left, top, left + STORY_W, top + STORY_H))
    bg = bg.filter(ImageFilter.GaussianBlur(40))

    fg = feed.copy()
    fscale = min(STORY_W / fg.width, STORY_H / fg.height) * 0.92
    fg = fg.resize((int(fg.width * fscale), int(fg.height * fscale)), Image.LANCZOS)

    bg.paste(fg, ((STORY_W - fg.width) // 2, (STORY_H - fg.height) // 2))

    out = feed_img_path.replace(".png", "_story.png")
    bg.save(out, "PNG", quality=95)

    return out


# ============================================================
# META / POSTING
# ============================================================
def github_raw_url(local_path):
    rel = os.path.relpath(local_path, SCRIPT_DIR).replace("\\", "/")
    return GITHUB_REPO_RAW_BASE + rel


def load_meta_config():
    with open(META_CONFIG_FILE, "r", encoding="utf-8") as f:
        return json.load(f)


def _get_page_token(page_id, user_token):
    r = requests.get(
        "%s/me/accounts" % GRAPH,
        params={"access_token": user_token, "limit": 200},
    )
    r.raise_for_status()

    for p in r.json().get("data", []):
        if str(p.get("id")) == str(page_id):
            return p["access_token"]

    raise RuntimeError("Page %s not found in me/accounts" % page_id)


def _fb_page_photo(page_id, token, image_url, caption, published=True):
    r = requests.post(
        "%s/%s/photos" % (GRAPH, page_id),
        data={
            "url": image_url,
            "caption": caption,
            "published": "true" if published else "false",
            "access_token": token,
        },
    )
    r.raise_for_status()
    return r.json()


def _fb_story(page_id, token, photo_id):
    r = requests.post(
        "%s/%s/photo_stories" % (GRAPH, page_id),
        data={"photo_id": photo_id, "access_token": token},
    )
    r.raise_for_status()
    return r.json()


def _ig_publish(ig_id, token, image_url, is_story=True):
    data = {
        "image_url": image_url,
        "access_token": token,
        "media_type": "STORIES",
    }

    c = requests.post("%s/%s/media" % (GRAPH, ig_id), data=data)
    c.raise_for_status()

    creation_id = c.json()["id"]

    for _ in range(10):
        st = requests.get(
            "%s/%s" % (GRAPH, creation_id),
            params={"fields": "status_code", "access_token": token},
        )

        code = st.json().get("status_code")

        if code == "FINISHED":
            break

        if code == "ERROR":
            raise RuntimeError("IG container error: %s" % st.text)

        time.sleep(3)

    p = requests.post(
        "%s/%s/media_publish" % (GRAPH, ig_id),
        data={"creation_id": creation_id, "access_token": token},
    )

    p.raise_for_status()
    return p.json()


def post_story_to_meta(story_url, caption=""):
    cfg = load_meta_config()
    page_id = cfg["page_id"]
    ig_id = cfg["ig_user_id"]
    user_token = cfg["page_access_token"]

    if not story_url:
        raise RuntimeError("no story url; cannot post.")

    try:
        token = _get_page_token(page_id, user_token)
    except Exception as e:
        print("    [meta] could not derive Page token: %s" % e)
        token = user_token

    fb_ok = False
    ig_ok = False

    try:
        photo = _fb_page_photo(page_id, token, story_url, caption, published=False)
        _fb_story(page_id, token, photo["id"])
        print("    [meta] FB story OK")
        fb_ok = True
    except Exception as e:
        print("    [meta] FB story FAILED: %s" % e)

    try:
        _ig_publish(ig_id, user_token, story_url, is_story=True)
        print("    [meta] IG story OK")
        ig_ok = True
    except Exception as e:
        print("    [meta] IG story FAILED: %s" % e)

    return fb_ok, ig_ok


def _fb_upload_unpublished_photo(page_id, token, image_url):
    r = requests.post(
        "%s/%s/photos" % (GRAPH, page_id),
        data={
            "url": image_url,
            "published": "false",
            "access_token": token,
        },
    )
    r.raise_for_status()
    return r.json()["id"]


def _fb_carousel_post(page_id, token, image_urls, caption=""):
    media_ids = [
        _fb_upload_unpublished_photo(page_id, token, url)
        for url in image_urls
    ]

    attached_media = [{"media_fbid": mid} for mid in media_ids]

    r = requests.post(
        "%s/%s/feed" % (GRAPH, page_id),
        data={
            "message": caption,
            "attached_media": json.dumps(attached_media),
            "access_token": token,
        },
    )

    r.raise_for_status()
    return r.json()


def _ig_carousel_child(ig_id, token, image_url):
    r = requests.post(
        "%s/%s/media" % (GRAPH, ig_id),
        data={
            "image_url": image_url,
            "is_carousel_item": "true",
            "access_token": token,
        },
    )

    r.raise_for_status()
    return r.json()["id"]


def _ig_carousel_post(ig_id, token, image_urls, caption=""):
    child_ids = [_ig_carousel_child(ig_id, token, url) for url in image_urls]

    c = requests.post(
        "%s/%s/media" % (GRAPH, ig_id),
        data={
            "media_type": "CAROUSEL",
            "children": ",".join(child_ids),
            "caption": caption,
            "access_token": token,
        },
    )

    c.raise_for_status()
    creation_id = c.json()["id"]

    for _ in range(10):
        st = requests.get(
            "%s/%s" % (GRAPH, creation_id),
            params={"fields": "status_code", "access_token": token},
        )

        code = st.json().get("status_code")

        if code == "FINISHED":
            break

        if code == "ERROR":
            raise RuntimeError("IG carousel container error: %s" % st.text)

        time.sleep(3)

    p = requests.post(
        "%s/%s/media_publish" % (GRAPH, ig_id),
        data={"creation_id": creation_id, "access_token": token},
    )

    p.raise_for_status()
    return p.json()


def post_carousel_to_meta(image_urls, caption=""):
    cfg = load_meta_config()
    page_id = cfg["page_id"]
    ig_id = cfg["ig_user_id"]
    user_token = cfg["page_access_token"]

    if not image_urls:
        raise RuntimeError("no image urls; cannot post carousel.")

    try:
        token = _get_page_token(page_id, user_token)
    except Exception as e:
        print("    [meta] could not derive Page token: %s" % e)
        token = user_token

    fb_ok = False
    ig_ok = False

    try:
        _fb_carousel_post(page_id, token, image_urls, caption)
        print("    [meta] FB carousel OK")
        fb_ok = True
    except Exception as e:
        print("    [meta] FB carousel FAILED: %s" % e)

    try:
        _ig_carousel_post(ig_id, user_token, image_urls, caption)
        print("    [meta] IG carousel OK")
        ig_ok = True
    except Exception as e:
        print("    [meta] IG carousel FAILED: %s" % e)

    return fb_ok, ig_ok


# ============================================================
# MAIN
# ============================================================
def run_ranking_image_generator():
    os.makedirs(OUTPUT_DIR, exist_ok=True)

    drive = get_drive_service()
    logo_files = list_folder_files(drive, LOGOS_FOLDER_ID)

    sync_backgrounds_from_drive(drive)

    print(f"[{time.strftime('%H:%M:%S')}] Initializing Chrome...")

    driver = webdriver.Chrome(
        service=Service(ChromeDriverManager().install()),
        options=chrome_options,
    )

    try:
        generated = []

        for cfg in RANKING_CONFIGS:
            print("\n" + "=" * 50)
            print(f"[{time.strftime('%H:%M:%S')}] Processing {cfg['team']} ranking")

            if cfg["source"] == "fotbalpraha":
                df, league_label = scrape_fotbalpraha_ranking_table(driver, cfg)
                cfg["league_label"] = league_label
            elif cfg["source"] == "pibfal":
                df = scrape_pibfal_ranking_table(driver, cfg)
            else:
                print(f"  Warning: unknown source {cfg['source']} for {cfg['team']}")
                continue

            if df.empty:
                print(f"  Warning: No ranking data found for {cfg['team']}")
                continue

            # If Galaksia team has no matches yet, skip this ranking.
            if not galaksia_has_played(df):
                print(f"  Galaksia has no matches played yet for {cfg['team']} - skipping ranking.")
                continue

            league_logo = load_league_logo(drive, logo_files, cfg["league_logo_label"])

            img = draw_ranking_image(df, cfg, league_logo=league_logo)

            out_name = f"{cfg['team']}_ranking.png".replace(" ", "_")
            out_path = os.path.join(OUTPUT_DIR, out_name)

            img.save(out_path, "PNG", quality=95)

            story_path = make_story_version(out_path)

            generated.append({
                "team": cfg["team"],
                "path": out_path,
                "story_path": story_path,
            })

            print(f"  ✓ Saved: {out_path}")
            print(f"  ✓ Saved story: {story_path}")

        by_team = {g["team"]: g for g in generated}
        ordered = [by_team[t] for t in POST_ORDER if t in by_team]

        with open(MANIFEST_FILE, "w", encoding="utf-8") as f:
            json.dump(ordered, f, ensure_ascii=False, indent=2)

        print("\n" + "=" * 50)
        print(f"[{time.strftime('%H:%M:%S')}] Generation complete. {len(ordered)} ranking image(s) ready.")

        for g in ordered:
            print(f"  - {g['team']}: {g['path']}")

    finally:
        driver.quit()
        print(f"[{time.strftime('%H:%M:%S')}] Session closed.")


def post_rankings_from_manifest():
    if not os.path.exists(MANIFEST_FILE):
        raise RuntimeError(f"Manifest not found: {MANIFEST_FILE}. Run --generate-only first.")

    with open(MANIFEST_FILE, "r", encoding="utf-8") as f:
        items = json.load(f)

    by_team = {item["team"]: item for item in items}
    ordered = [by_team[t] for t in POST_ORDER if t in by_team]

    if not ordered:
        print("No ranking images found in manifest.")
        return

    for item in ordered:
        if not os.path.exists(item["path"]):
            raise RuntimeError(f"Missing ranking image: {item['path']}")

        if not os.path.exists(item["story_path"]):
            raise RuntimeError(f"Missing ranking story image: {item['story_path']}")

    print("Posting rankings in order:")

    for item in ordered:
        print(f"  - {item['team']}")

    carousel_urls = [github_raw_url(item["path"]) for item in ordered]

    caption = "League Standings"

    carousel_fb_ok, carousel_ig_ok = post_carousel_to_meta(carousel_urls, caption=caption)

    story_results = []

    for item in ordered:
        print(f"--- Posting story {item['team']} ---")
        story_url = github_raw_url(item["story_path"])
        fb_ok, ig_ok = post_story_to_meta(story_url)
        story_results.append((fb_ok, ig_ok))

    all_fb_ok = carousel_fb_ok and all(r[0] for r in story_results)
    all_ig_ok = carousel_ig_ok and all(r[1] for r in story_results)
    fully_sent = all_fb_ok and all_ig_ok

    if fully_sent:
        print("Rankings posted successfully to FB and IG.")
    else:
        print(f"Rankings NOT fully posted (FB ok={all_fb_ok}, IG ok={all_ig_ok}).")

    # Cleanup local files after posting attempt.
    for item in ordered:
        for p in (item.get("path"), item.get("story_path")):
            if p and os.path.exists(p):
                try:
                    os.remove(p)
                except Exception as e:
                    print(f"  [cleanup] could not remove {p}: {e}")

    if os.path.exists(MANIFEST_FILE):
        try:
            os.remove(MANIFEST_FILE)
        except Exception as e:
            print(f"  [cleanup] could not remove manifest {MANIFEST_FILE}: {e}")

    print("Posting complete.")


GENERATE_ONLY = "--generate-only" in sys.argv
POST_ONLY = "--post-only" in sys.argv

if not GENERATE_ONLY and not POST_ONLY:
    print("ERROR: pass either --generate-only or --post-only.")
    sys.exit(1)

if __name__ == "__main__":
    if GENERATE_ONLY:
        run_ranking_image_generator()
    elif POST_ONLY:
        post_rankings_from_manifest()
