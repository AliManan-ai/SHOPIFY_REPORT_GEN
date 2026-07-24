#!/usr/bin/env python3

"""
================================================================================
Shopify Products Export → Collection-Wise Inventory PDF Report Generator (FastAPI)
================================================================================

v4.7 — BluesMind API Fix

Fixes from v4.6:
  1. Fixed broken DEFAULT_API_BASE_URL (was double-encoded markdown link).
  2. Fixed default model: uses gpt-5-mini (the only model on BluesMind).
  3. Added robust fallback: if AI classification fails (403, etc.), uses heuristic.
  4. 403 Permission Denied errors are NOT retried — immediate fallback.
  5. response_format tried first, falls back to plain call if unsupported.
  6. All HTML entity encoding fixed (&amp; &gt; &lt; → & > <).
"""

import os, sys, csv, json, re, uuid, shutil, hashlib, tempfile, time, html

from datetime import datetime, timedelta
from collections import defaultdict, Counter
from typing import Optional, Dict, Any, List, Set, Tuple
from xml.sax.saxutils import escape as xml_escape
from difflib import SequenceMatcher

try:
    from fastapi import FastAPI, File, UploadFile, Form, HTTPException, BackgroundTasks, Query
    from fastapi.responses import HTMLResponse, FileResponse, JSONResponse
    from fastapi.middleware.cors import CORSMiddleware
    import uvicorn
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import mm, cm, inch
    from reportlab.lib.enums import TA_LEFT, TA_CENTER, TA_RIGHT
    from reportlab.platypus import (
        SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer,
        PageBreak, KeepTogether, Flowable
    )
    from openai import OpenAI
except ImportError as e:
    print(f"Missing packages: {e}")
    print("Run: pip install fastapi uvicorn python-multipart reportlab openai")
    sys.exit(1)

# --- CONFIG ---
DEFAULT_API_KEY = os.environ.get(
    "SHOPIFY_REPORT_API_KEY",
    "sk-8DLeSnmkFU4lOjPQtwwDTwYlKdLw3ikVHmt9hFzIgCsCIttE",
)
DEFAULT_API_BASE_URL = os.environ.get(
    "SHOPIFY_REPORT_API_BASE_URL",
    "https://api.bluesminds.com/v1",
)
DEFAULT_MODEL = os.environ.get("SHOPIFY_REPORT_MODEL", "gpt-5-mini")

APP_DIR = os.path.dirname(os.path.abspath(__file__))

# --- CROSS-PLATFORM DIRECTORY RESOLUTION ---

def is_writable_dir(path: str) -> bool:
    try:
        os.makedirs(path, exist_ok=True)
        probe = os.path.join(path, f".wtest_{uuid.uuid4().hex}")
        with open(probe, "w") as fh:
            fh.write("ok")
        os.remove(probe)
        return True
    except Exception:
        return False

def resolve_dir(env_var: str, subfolder: str, allow_temp_fallback: bool = True) -> str:
    override = os.environ.get(env_var)
    candidates = []
    if override:
        candidates.append(override)
    candidates.append(os.path.join(APP_DIR, subfolder))
    candidates.append(os.path.join(os.path.expanduser("~"), ".shopify_inventory_report", subfolder))
    if allow_temp_fallback:
        candidates.append(os.path.join(tempfile.gettempdir(), "shopify_inventory_report", subfolder))
    for path in candidates:
        if is_writable_dir(path):
            return path
    raise RuntimeError(
        f"No writable directory found for {env_var} (subfolder='{subfolder}'). "
        f"Tried: {candidates}. Set {env_var} to a directory this process can write to."
    )

CACHE_DIR = resolve_dir("SHOPIFY_REPORT_CACHE_DIR", ".collection_cache")
PERMANENT_DIR = resolve_dir("SHOPIFY_REPORT_PERMANENT_DIR", ".permanent_collections", allow_temp_fallback=False)
temp_jobs_override = os.environ.get("SHOPIFY_REPORT_TEMP_DIR")
TEMP_JOBS_DIR = temp_jobs_override or os.path.join(tempfile.gettempdir(), "shopify_inventory_jobs")
if not is_writable_dir(TEMP_JOBS_DIR):
    raise RuntimeError(f"Temp jobs directory is not writable: {TEMP_JOBS_DIR}.")

print("=" * 60)
print("  Storage locations in use:")
print(f"     Cache:     {CACHE_DIR}")
print(f"     Permanent: {PERMANENT_DIR}")
print(f"     Temp jobs: {TEMP_JOBS_DIR}")
print("=" * 60)

JOBS: Dict[str, Dict[str, Any]] = {}
TEMP_FILE_TTL_MINUTES = 30
CACHE_SCHEMA_VERSION = "v9"

# --- UNIVERSAL VENDOR DETECTION ENGINE ---

NOISE_VENDORS = {
    'express shipping', 'express shipping ⚡', 'express_shipping', 'express-shipping',
    'free shipping', 'shopify', 'my store', 'mystore', 'default vendor', 'default',
    'admin', 'unknown', 'null', 'none', 'n/a', 'na', '-', '1', 'test', 'sample',
    'demo', 'b', 'acme', 'generic', 'vendor', 'shop', 'store', 'my-store', 'brand',
    'company', 'shopify store'
}

DOMAIN_TLD_PATTERN = re.compile(
    r'(\.com\.pk|\.co\.uk|\.com|\.pk|\.co|\.store|\.official|\.shop|\.net|\.org|\.io)\b', re.I
)
OFFICIAL_SUFFIX_PATTERN = re.compile(
    r'\s+(official(\s+store)?|online(\s+store)?|pvt\s+ltd|pvt|ltd|pk|pakistan|store)$', re.I
)
TAG_VENDOR_PREFIX = re.compile(r'^(vendor|brand)\s*[:=]\s*(.+)$', re.I)
PARENT_BRAND_TAG_PATTERN = re.compile(
    r'^([A-Z0-9a-z\s]+?)\s+(unstitched|pret|exclusive|luxury\s*pret|collection|official)$', re.I
)

def clean_vendor_display(raw: str) -> str:
    if not raw:
        return ''
    s = raw.strip()
    if s.lower() in NOISE_VENDORS:
        return ''
    s = DOMAIN_TLD_PATTERN.sub('', s)
    s = OFFICIAL_SUFFIX_PATTERN.sub('', s)
    s = s.strip(' ._-\t\r\n')
    if len(s) <= 1 or s.lower() in NOISE_VENDORS:
        return ''
    return s

def normalize_vendor_key(clean_str: str) -> str:
    return re.sub(r'[^a-z0-9]', '', clean_str.lower())

def format_brand_name(name: str) -> str:
    if not name:
        return 'Shopify Store'
    name = name.strip()
    if name.isupper() and len(name) > 3:
        return name.title()
    if name.islower():
        return name.title()
    return name

def detect_brand(by_handle: Dict[str, Dict[str, Any]], brand_override: Optional[str] = None) -> str:
    if brand_override and brand_override.strip():
        return brand_override.strip()
    active_handle_vendors = []
    all_handle_vendors = []
    for h, p in by_handle.items():
        v_raw = (p.get('vendor') or '').strip()
        status = (p.get('status') or '').strip().lower()
        published = (p.get('published') or '').strip().lower()
        is_active_pub = (status == 'active' and published == 'true')
        if v_raw:
            cleaned = clean_vendor_display(v_raw)
            if cleaned:
                if is_active_pub:
                    active_handle_vendors.append(cleaned)
                all_handle_vendors.append(cleaned)

    target_list = active_handle_vendors if active_handle_vendors else all_handle_vendors
    if target_list:
        key_counts = Counter()
        key_display_variants = defaultdict(Counter)
        for v in target_list:
            k = normalize_vendor_key(v)
            if k:
                key_counts[k] += 1
                key_display_variants[k][v] += 1
        if key_counts:
            sorted_keys = key_counts.most_common()
            merged_counts = Counter(key_counts)
            for i in range(len(sorted_keys)):
                k1, count1 = sorted_keys[i]
                if merged_counts[k1] == 0:
                    continue
                for j in range(i + 1, len(sorted_keys)):
                    k2, count2 = sorted_keys[j]
                    if merged_counts[k2] == 0:
                        continue
                    ratio = SequenceMatcher(None, k1, k2).ratio()
                    if ratio >= 0.85:
                        merged_counts[k1] += merged_counts[k2]
                        merged_counts[k2] = 0
            best_key = merged_counts.most_common(1)[0][0]
            variants = key_display_variants[best_key]
            best_display = max(
                variants.keys(),
                key=lambda var: (' ' in var, variants[var], not var.islower(), len(var))
            )
            return format_brand_name(best_display)

    vendor_tag_counts = Counter()
    parent_tag_counts = Counter()
    for h, p in by_handle.items():
        status = (p.get('status') or '').strip().lower()
        published = (p.get('published') or '').strip().lower()
        if status != 'active' or published != 'true':
            continue
        tags_raw = p.get('tags_raw') or ''
        if not tags_raw:
            continue
        tags = [t.strip() for t in tags_raw.split(',') if t.strip()]
        for t in tags:
            m_prefix = TAG_VENDOR_PREFIX.match(t)
            if m_prefix:
                v_val = m_prefix.group(2).strip()
                if v_val and v_val.lower() not in NOISE_VENDORS:
                    vendor_tag_counts[v_val] += 1
                continue
            m_parent = PARENT_BRAND_TAG_PATTERN.match(t)
            if m_parent:
                b_name = m_parent.group(1).strip()
                if len(b_name) >= 3 and b_name.lower() not in ('casual', 'formal', 'fancy', 'daily', 'summer', 'winter', 'festive'):
                    parent_tag_counts[b_name] += 1

    if vendor_tag_counts:
        return format_brand_name(vendor_tag_counts.most_common(1)[0][0])
    if parent_tag_counts:
        return format_brand_name(parent_tag_counts.most_common(1)[0][0])
    return 'Shopify Store'

# --- BRAND SKU & HANDLE PREFIX MAPPING TABLE ---

BRAND_PREFIX_COLLECTION_MAP = {
    'SP': 'Shades of Summer', 'DD': 'Daily Delights', 'AM': 'Amaya',
    'NR': 'Raha', 'MK': 'Mukeshkari', 'TW': 'Tiny Twinkles',
    'BL': 'Ballerina', 'NP': 'Casual Pret', 'FE': 'Fancy Formal',
    'FP': 'Formal Pret', 'NE': 'Nureh Exclusive', 'NEL': 'Chiffon Luxe',
    'NSG': 'Gardenia', 'NS': 'Maya', 'NW': 'Shades of Winter',
    'NL': 'Nureh Lawn', 'NU2': 'Unstitched',
}

# --- UNIVERSAL TAG FILTER ENGINE ---

SIZE_PATTERN = re.compile(
    r'^(xs|s|m|l|xl|xxl|xxxl|2xl|3xl|4xl|5xl|6xl|7xl|8xl|9xl|10xl|'
    r'extra\s*small|small|medium|large|extra\s*large|'
    r'one\s*size|free\s*size|free\s*sz|'
    r'custom\s*(stitch|stitching)|unstitched|stitched|'
    r'\d+\s*(month|mo|m|yr|year|y)s?|'
    r'newborn|infant|toddler|kids|'
    r'super\s*(small|free))$', re.I
)
FABRIC_PATTERN = re.compile(
    r'^(lawn|chiffon|organza|net|silk|velvet|khaddar|cambric|linen|cotton|'
    r'jacquard|swiss\s*lawn|dorya|dorea|doria|viscose|crepe|raw\s*silk|rawsilk|'
    r'massori|chikankari|schiffli|wool|woolen|taffeta|georgette|satin|lace|'
    r'embroidered|printed|dyed|woven|knit|digital\s*print|screen\s*print|'
    r'banarsi|jamawar|karandi|boski|pashmina|tissue|leather\s*peach|'
    r'marina\s*twil|charmeuse\s*silk|zari\s*jacquard)$', re.I
)
SUBBRAND_PATTERN = re.compile(
    r'^(express\s*shipping|free\s*shipping|express[_-]?shipping|'
    r'(pk|us|uk|uae)\s+(active\s*)?products|'
    r'no\s*sync|do\s*not\s*sync|exclude\s*from\s*sync)$', re.I
)
PRODUCT_CODE_PATTERN = re.compile(
    r'^[a-z0-9]{1,6}[-_]\s?\d{1,5}'
    r'([\s\-_]+(shirt|trouser|trousers|frock|dupatta|shawl|kurta|kameez))?'
    r'([-_](sizechart|chart|sizechat))?\s*$', re.I
)
BARE_CODE_PATTERN = re.compile(r'^[a-z0-9]{1,6}[-_]\d{1,5}$', re.I)
STRICT_GLUED_SKU_PATTERN = re.compile(r'^[a-z]{1,3}\d{3,5}$', re.I)

DATE_PATTERNS = [
    re.compile(r'^\d{1,2}[-/]\d{1,2}[-/]\d{2,4}$'),
    re.compile(r'^\d{1,2}[-\s](jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)\w*[-\s]\d{2,4}$', re.I),
    re.compile(r'^\d{1,2}\s+(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)\w*\s+\d{2,4}$', re.I),
    re.compile(r'^\d{1,2}[a-z]+\d{2,4}[-_]file$', re.I),
    re.compile(r'^\d{1,2}(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)\d{0,2}$', re.I),
    re.compile(
        r'^\d{1,2}[-/\s](jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*'
        r'[-/\s]?\d{2,4}(\s*\([^)]*\))?([-_][a-z]{1,6})?$', re.I
    ),
    re.compile(r'^\d{1,2}\s+(january|february|march|april|may|june|july|august|september|october|november|december)\s+\d{2,4}$', re.I),
]
PRICE_PATTERNS = [
    re.compile(r'^\d+[\s\-–]+\d+(\s*(pkr|rs|usd|£|\$))?$', re.I),
    re.compile(r'^\d{3,5}\s*(rs|pkr|usd|£|\$)$', re.I),
    re.compile(r'^\d{3,6}$'),
]
SALE_PATTERNS = [
    re.compile(r'^\d+%?\s*(off|sale|discount)', re.I),
    re.compile(r'^flat\s*\d+', re.I),
    re.compile(r'^(rev|r)-?\d*%?\s*(off|sale|discount|hs)?$', re.I),
    re.compile(r'^discount\s*\d*', re.I),
    re.compile(r'^sale\s*(collection|items|202\d)?', re.I),
    re.compile(r'^(remove|exclude)\s*u\s*sale', re.I),
    re.compile(r'^special\s*offer', re.I),
    re.compile(r'^clearance', re.I),
    re.compile(r'^\d+%\s*(hs|off)?$', re.I),
    re.compile(r'^pret\s*remove\s*sale$', re.I),
    re.compile(r'^unstitched\s*\d+%\s*hs$', re.I),
    re.compile(r'^formal\s*pret\s*hs$', re.I),
]
OPERATIONAL_PATTERNS = [
    re.compile(r'^(hide|show)[-_]', re.I),
    re.compile(r'^(newin|new[-_]?in|new\s*arrivals?)$', re.I),
    re.compile(r'^(restock(ed)?|re[-_]?stock(\s*\d+)?)$', re.I),
    re.compile(r'^(new\s*restocked)$', re.I),
    re.compile(r'^(testing|just\s*check|missing\s*comp)$', re.I),
    re.compile(r'^(with|without)\s+(lining|dupatta)$', re.I),
    re.compile(r'^(sizechart|size[-_]?chart|matter[-_]?sizechart)', re.I),
    re.compile(r'^[a-z]{1,5}[-_]sizechart', re.I),
    re.compile(r'^(drop[-_]?\d+)$', re.I),
    re.compile(r'.*restock\s*alert.*\d{4}.*', re.I),
    re.compile(r'^(summer|winter|spring|fall|autumn)$', re.I),
    re.compile(r'^rev-?\d+%', re.I),
    re.compile(r'^\d+%?\s*(off|sale|hs)', re.I),
    re.compile(r'^[a-z]{1,2}[-_]?[a-z]$', re.I),
    re.compile(r'^ppd[-_]?[a-z0-9]+$', re.I),
    re.compile(r'^nada[-_]?hidden$', re.I),
    re.compile(r'^newh$', re.I),
    re.compile(r'^bh\d*$', re.I),
    re.compile(r'^inc\d+$', re.I),
    re.compile(r'^(n[-_]?p|n[-_]?h)$', re.I),
    re.compile(r'^(esgcc|rtsgcc)[-_\s].+$', re.I),
    re.compile(r'^today\s*\d+$', re.I),
    re.compile(r'^(summer|winter|spring|fall|autumn|summerr)$', re.I),
    re.compile(r'^pink$', re.I),
    re.compile(r'^shawls$', re.I),
    re.compile(r'^h$', re.I),
    re.compile(r'^ymq[_-]?size$', re.I),
    re.compile(r'^(stitched|unstitched)[_-]?note$', re.I),
    re.compile(r'^hide\s*cod\s*variants?$', re.I),
    re.compile(r'^hidecodvariants$', re.I),
    re.compile(r'^c[-_]?grade$', re.I),
    re.compile(r'^open[-_]?cart$', re.I),
    re.compile(r'^xs[_-]?xl$', re.I),
    re.compile(r'^pre[-_]?order$', re.I),
    re.compile(r'^products?[_-]?from[_-]?sheet$', re.I),
    re.compile(r'^(bridal[_-]?disclaimer|lining[_-]?option|lining[-_]?note|custom[_-]?flow)$', re.I),
    re.compile(r'^self$', re.I),
    re.compile(r'^slate$', re.I),
    re.compile(r'^lehnga[_-]?maxi$', re.I),
    re.compile(r'.*sizechart.*', re.I),
    re.compile(r'.*c\s*category\s*products?$', re.I),
    re.compile(r'^\d{1,2}[-/]\d{1,2}[-/]\d{2,4}.*sale.*$', re.I),
    re.compile(r'^\d{1,2}(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)[a-z]*\d{2,4}$', re.I),
    re.compile(r'^\d{1,2}[-_]?\d{1,2}[-_]?\d{2,4}[-_]?sale.*$', re.I),
]
GARMENT_TYPE_PATTERN = re.compile(
    r'^(shirt|trouser|trousers|dupatta|frock|kurta|kameez|shalwar|salwar|'
    r'sharara|gharara|lehnga|lehenga|peshwas|angrakha|kaftan|peplum|'
    r'pret|formal|daily\s*wear|unstitched\s*daily\s*wear|'
    r'bridal|wedding|formals|luxury\s*pret|casual|fancy|'
    r'daily\s*wear|stitched|unstitched|'
    r'three\s*piece|two\s*piece|2\s*piece|3\s*piece|'
    r'dresses?|suit|suits)$', re.I
)
AUDIENCE_MARKETING_PATTERN = re.compile(
    r'^(women|womens?|womenswear|ladies|men|mens|girls?|boys?|kids?|kidswear|'
    r'baby|unisex|adult|'
    r'bestseller|best\s*seller|best\s*selling|featured|trending|popular|'
    r'new|new\s*in|new\s*arrival[s]?|newin|newarival|arrivals?|'
    r'summers?|winters?|springs?|autumns?|falls?|'
    r'luxury|premium|sale|clearance|dot\s*sale|red\s*dot|reddot|'
    r'rtw|ready\s*to\s*wear|unstitch|unstitched|'
    r'em[_-]?hidecod|hidecod|hide\s*cod|'
    r'b1g1|buy\s*1\s*get\s*1|flash\s*deal|flashdeal|last\s*pair|lastpair|'
    r'reduced|add\d+|logoall|logo)$', re.I
)
COLOR_ATTR_PATTERN = re.compile(
    r'^(color[_-].+|colour[_-].+|'
    r'black|brown|blue|green|grey|gray|maroon|beige|red|white|orange|'
    r'camel|coffee|mustard|olive|purple|yellow|apricot|mix|mixed)$', re.I
)
PROMO_CHANNEL_PATTERN = re.compile(
    r'^(rd[_-].+|add\d+|b1g1|flashdeal|lastpair|reduced|'
    r'newarival|newarrival|mkd|mz)$', re.I
)

PRODUCT_TYPE_COLLECTION_MAP = {
    'formal shoes': 'Loafers & Lace Up', 'premium formal': 'Loafers & Lace Up',
    'formal boots': 'Formal Boots', 'casual shoes': 'Casuals & Slip-Ons',
    'slip ons': 'Casuals & Slip-Ons', 'slip on': 'Casuals & Slip-Ons',
    'slipper': 'Slippers', 'slippers': 'Slippers', 'leather slipper': 'Slippers',
    'sandal': 'Sandals', 'sandals': 'Sandals', 'leather sandal': 'Sandals',
    'active collection': 'Active Collection', 'sports': 'Active Collection',
    'sports shoes': 'Active Collection', 'premium sneakers': 'Premium Sneakers',
    'kids': 'Kids', 'kids sandals': 'Kids Sandals', 'kids slippers': 'Kids Slippers',
    'fragrance': 'Fragrance', 'perfume': 'Perfume', 'perfumes': 'Perfume',
    'perfume mist': 'Perfume Mist', 'perfum mist': 'Perfume Mist',
    'eau de toilette': 'Eau de Toilette', 'room spray': 'Room Spray',
    'roomspray': 'Room Spray', 'accessories': 'Accessories',
    'leather acc': 'Leather Accessories', 'leather accessories': 'Leather Accessories',
    'leather_acc': 'Leather Accessories', 'shoe care': 'Shoe Care',
    'shoe care acc': 'Shoe Care', 'socks': 'Socks', 'belt': 'Belts', 'belts': 'Belts',
    'wallet': 'Note Wallets', 'notewallet': 'Note Wallets', 'note wallet': 'Note Wallets',
    'cardwallet': 'Card Holders', 'cardholder': 'Card Holders',
    'card holder': 'Card Holders', 'key chain': 'Key Chains',
    'bracelets': 'Bracelets', 'bracelet': 'Bracelets',
    'vest & trunks': 'Vests & Trunks', 'vests & trunks': 'Vests & Trunks',
    'lifestyle': 'Lifestyle', 'wearable acc': 'Wearable Accessories',
}

SPECIFIC_ACCESSORY_TAGS = {
    'socks': 'Socks', 'belt': 'Belts', 'belts': 'Belts',
    'wallet': 'Note Wallets', 'notewallet': 'Note Wallets',
    'cardwallet': 'Card Holders', 'cardholder': 'Card Holders',
    'key chain': 'Key Chains', 'bracelets': 'Bracelets', 'bracelet': 'Bracelets',
    'perfume': 'Perfume', 'perfumes': 'Perfume', 'perfum mist': 'Perfume Mist',
    'perfume mist': 'Perfume Mist', 'eau de toilette': 'Eau de Toilette',
    'roomspray': 'Room Spray', 'room spray': 'Room Spray',
    'shoe care': 'Shoe Care', 'shoe care acc': 'Shoe Care',
    'leather acc': 'Leather Accessories', 'leather_acc': 'Leather Accessories',
    'leather accessories': 'Leather Accessories', 'kids sandals': 'Kids Sandals',
    'kids slippers': 'Kids Slippers', 'premium sneakers': 'Premium Sneakers',
    'slip ons': 'Casuals & Slip-Ons', 'sports': 'Active Collection',
    'formalboots': 'Formal Boots', 'vest & trunks': 'Vests & Trunks',
    'lifestyle': 'Lifestyle', 'leather moccasin': 'Loafers & Lace Up',
    'leather slipper': 'Slippers', 'leather sandal': 'Sandals',
    'sandal': 'Sandals', 'slipper': 'Slippers',
}

PARENT_BUCKET_PATTERN = re.compile(
    r'^('
    r'(nureh|afrozeh|ziva)\s+(unstitched|pret|exclusive|luxury\s*pret|collection)|'
    r'(nureh|afrozeh|ziva)\s+collection|'
    r'afrozeh|nureh|ziva|'
    r'casual\s*pret|formal\s*pret|fancy\s*formal|fancy\s*formals|'
    r'exclusive|pret|unstitched|luxury\s*pret|'
    r'wedding\s*formals?|'
    r'chiffon\s*luxe|'
    r'festive(\s*(edit|collection|wear|formals?))?|'
    r'new\s*in(\s*\d{2,4})?|new\s*arrivals?(\s*\d{2,4})?|newarrivals?\d{0,4}|'
    r'peshwas?\s*&\s*lehngas?|lehngas?\s*&\s*peshwas?|'
    r'mini\s*me\s*kids?'
    r')$', re.I
)
OCCASION_CATEGORY_PATTERN = re.compile(
    r'^('
    r'festive(\s*(edit|collection|wear|formals?))?|'
    r'eid(\s*edit)?|'
    r'wedding(\s*formals?)?|'
    r'luxury\s*(pret|lawn|formals?)|'
    r'basic\s*pret$|'
    r'cords?\s*pret$|'
    r'new\s*in(\s*\d{2,4})?|new\s*arrivals?(\s*\d{2,4})?|newarrivals?\d{0,4}'
    r')$', re.I
)
BATCH_INTERNAL_PATTERN = re.compile(
    r'^(bx\s*\d+|cart[-_]?button[-_]?hider|collection\s*products?|[a-z0-9]+-sc$)$', re.I
)

def strip_tag_wrappers(tag: str) -> str:
    t = tag.strip()
    t = t.strip('*').strip('*').strip()
    return t

def is_noise_tag(tag: str) -> Tuple[bool, str]:
    raw = tag.strip()
    if not raw:
        return True, 'empty'
    core = strip_tag_wrappers(raw)
    t = core.lower()
    if not t:
        return True, 'empty'
    if SIZE_PATTERN.match(t): return True, 'size'
    if FABRIC_PATTERN.match(t): return True, 'fabric'
    if SUBBRAND_PATTERN.match(t): return True, 'subbrand'
    if PRODUCT_CODE_PATTERN.match(t): return True, 'product_code'
    if BARE_CODE_PATTERN.match(t): return True, 'bare_code'
    if STRICT_GLUED_SKU_PATTERN.match(t): return True, 'glued_sku'
    if GARMENT_TYPE_PATTERN.match(t): return True, 'garment_type'
    if AUDIENCE_MARKETING_PATTERN.match(t): return True, 'audience_marketing'
    if COLOR_ATTR_PATTERN.match(t): return True, 'color'
    if PROMO_CHANNEL_PATTERN.match(t): return True, 'promo_channel'
    if BATCH_INTERNAL_PATTERN.match(t) or BATCH_INTERNAL_PATTERN.match(core): return True, 'batch_internal'
    for pat in DATE_PATTERNS:
        if pat.match(t): return True, 'date'
    for pat in PRICE_PATTERNS:
        if pat.match(t): return True, 'price'
    for pat in SALE_PATTERNS:
        if pat.match(t): return True, 'sale'
    for pat in OPERATIONAL_PATTERNS:
        if pat.match(t) or pat.match(core): return True, 'operational'
    if len(t) <= 2: return True, 'too_short'
    return False, ''

def parse_tags(tags_raw: str) -> List[str]:
    if not tags_raw:
        return []
    return [t.strip() for t in tags_raw.split(',') if t.strip()]

def extract_candidate_tags(tags: List[str], ignore: Optional[Set[str]] = None) -> List[str]:
    ignore = ignore or set()
    out = []
    seen = set()
    for t in tags:
        cleaned = strip_tag_wrappers(t).strip()
        if not cleaned: continue
        key = cleaned.lower()
        if key in ignore or t.strip().lower() in ignore: continue
        if is_noise_tag(cleaned)[0]: continue
        if key in seen: continue
        seen.add(key)
        out.append(cleaned)
    return out

def is_named_year_collection(tag: str) -> bool:
    clean = strip_tag_wrappers(tag).strip()
    if not clean: return False
    if re.match(r'^(basic|cords?|everyday|casual|formal|fancy)\s*pret\s*[\'\u2019]?\s*\d{2,4}$', clean, re.I):
        return True
    if re.match(r'^basicpret\s*\d{2,4}$', clean, re.I):
        return True
    return False

def is_parent_bucket(tag: str) -> bool:
    clean = strip_tag_wrappers(tag).strip()
    if is_named_year_collection(clean): return False
    return bool(PARENT_BUCKET_PATTERN.match(clean) or OCCASION_CATEGORY_PATTERN.match(clean))

def is_recoverable_occasion_tag(tag: str) -> bool:
    clean = strip_tag_wrappers(tag).strip()
    if is_named_year_collection(clean): return True
    return bool(OCCASION_CATEGORY_PATTERN.match(clean) or PARENT_BUCKET_PATTERN.match(clean))

def map_product_type_to_collection(product_type: str) -> Optional[str]:
    if not product_type: return None
    key = product_type.strip().lower()
    if key in PRODUCT_TYPE_COLLECTION_MAP: return PRODUCT_TYPE_COLLECTION_MAP[key]
    key2 = re.sub(r'[^a-z0-9\s&]+', '', key).strip()
    if key2 in PRODUCT_TYPE_COLLECTION_MAP: return PRODUCT_TYPE_COLLECTION_MAP[key2]
    return None

def map_specific_tag_to_collection(tag: str) -> Optional[str]:
    if not tag: return None
    key = strip_tag_wrappers(tag).strip().lower()
    return SPECIFIC_ACCESSORY_TAGS.get(key)

# --- UNIVERSAL COLLECTION DETECTION ENGINE ---

ACRONYMS = {'RTW', 'K&G', 'K&B', 'B&K', 'PPD', 'AIS', 'USA', 'UK', 'UAE', 'PKR'}

class CollectionDetector:
    def __init__(self, api_key=None, api_base_url=None, model=None):
        self.api_key = api_key or DEFAULT_API_KEY
        self.api_base_url = api_base_url or DEFAULT_API_BASE_URL
        self.model = model or DEFAULT_MODEL
        self.client = None
        self.init_error = None
        self._init_client()
        self.cache = self._load_cache()
        self.stats = {
            'cache_hits': 0, 'cache_misses': 0, 'ai_calls': 0, 'ai_tokens': 0,
            'ai_client_ready': self.client is not None,
            'init_error': self.init_error,
            'last_ai_error': None,
        }

    def _init_client(self):
        import traceback
        try:
            self.client = OpenAI(api_key=self.api_key, base_url=self.api_base_url)
            self.init_error = None
        except Exception as e:
            print("=" * 60)
            print("OpenAI client init FAILED - AI mode will be unavailable")
            print(f"   api_key set: {bool(self.api_key)}  base_url: {self.api_base_url}")
            print(f"   Error: {e}")
            traceback.print_exc()
            print("=" * 60)
            self.client = None
            self.init_error = str(e)

    @staticmethod
    def _brand_slug(brand_name: str) -> str:
        s = re.sub(r'[^a-z0-9]+', '-', (brand_name or '').strip().lower()).strip('-')
        return s or 'default-brand'

    def _cache_path(self, key: str) -> str:
        h = hashlib.md5(key.encode()).hexdigest()
        return os.path.join(CACHE_DIR, f"{h}.json")

    def _load_cache(self) -> Dict[str, str]:
        cache = {}
        if os.path.isdir(CACHE_DIR):
            for f in os.listdir(CACHE_DIR):
                if f.endswith('.json'):
                    try:
                        with open(os.path.join(CACHE_DIR, f), 'r') as fh:
                            d = json.load(fh)
                            val = d['value']
                            if val and val != 'NOT_COLLECTION':
                                val = self._normalize_name(val)
                            cache[d['key']] = val
                    except Exception:
                        pass
        return cache

    def _save_cache(self, key: str, value: str):
        norm_val = value if value == 'NOT_COLLECTION' else self._normalize_name(value)
        self.cache[key] = norm_val
        try:
            with open(self._cache_path(key), 'w') as f:
                json.dump(
                    {'key': key, 'value': norm_val, 'ts': datetime.now().isoformat()},
                    f,
                )
        except Exception:
            pass

    def _permanent_path(self, brand_slug: str) -> str:
        return os.path.join(PERMANENT_DIR, f"{brand_slug}.json")

    def _load_permanent(self, brand_slug: str) -> Dict[str, Any]:
        path = self._permanent_path(brand_slug)
        if os.path.exists(path):
            try:
                with open(path, 'r') as fh:
                    data = json.load(fh)
                    for k, item in data.items():
                        if item.get('value') and item['value'] != 'NOT_COLLECTION':
                            item['value'] = self._normalize_name(item['value'])
                    return data
            except Exception:
                return {}
        return {}

    def _save_permanent(self, brand_slug: str, tag_lower: str, value: str):
        norm_val = value if value == 'NOT_COLLECTION' else self._normalize_name(value)
        try:
            data = self._load_permanent(brand_slug)
            data[tag_lower] = {'value': norm_val, 'ts': datetime.now().isoformat()}
            tmp_path = self._permanent_path(brand_slug) + ".tmp"
            with open(tmp_path, 'w') as f:
                json.dump(data, f)
            os.replace(tmp_path, self._permanent_path(brand_slug))
        except Exception:
            pass

    def detect(
        self,
        products: Dict[str, Any],
        brand_name: str,
        use_ai: bool = True,
        custom_ignore_tags: Optional[Set[str]] = None,
    ) -> Tuple[Dict[str, str], Dict, List[Dict]]:
        custom_ignore = {t.strip().lower() for t in (custom_ignore_tags or set()) if t.strip()}
        brand_slug = self._brand_slug(brand_name)
        permanent = self._load_permanent(brand_slug)
        product_candidates: Dict[str, List[str]] = {}
        tag_to_products = defaultdict(set)
        tag_sample_text: Dict[str, str] = {}
        known_synthetic: Dict[str, str] = {}
        candidate_priority: Dict[str, int] = {}

        for handle, p in products.items():
            tags = parse_tags(p['tags_raw'])
            candidates = extract_candidate_tags(tags, custom_ignore)
            ordered: List[str] = []
            for t in tags:
                mapped = map_specific_tag_to_collection(t)
                if mapped:
                    key = f"__spec__:{mapped.lower()}"
                    if key not in ordered:
                        ordered.append(key)
                        known_synthetic[key] = mapped
                        tag_sample_text[key] = mapped
                        candidate_priority[key] = 0
            ptype = (p.get('type') or '').strip()
            type_coll = map_product_type_to_collection(ptype)
            if type_coll:
                key = f"__type__:{type_coll.lower()}"
                if key not in ordered:
                    ordered.append(key)
                    known_synthetic[key] = type_coll
                    tag_sample_text[key] = type_coll
                    candidate_priority[key] = 1
            for c in candidates:
                cl = c.lower()
                if cl.startswith('__'): continue
                if map_specific_tag_to_collection(c): continue
                if c not in ordered and cl not in [x.lower() for x in ordered]:
                    ordered.append(c)
                    candidate_priority[cl] = 2
                    tag_sample_text.setdefault(cl, c)
            product_candidates[handle] = ordered
            for c in ordered:
                cl = c.lower()
                tag_to_products[cl].add(handle)
                if cl not in tag_sample_text:
                    tag_sample_text[cl] = known_synthetic.get(cl, c)

        tag_resolution: Dict[str, Optional[str]] = {}
        uncached: Dict[str, Dict[str, Any]] = {}

        for tag_lower, handles in tag_to_products.items():
            if tag_lower in known_synthetic:
                tag_resolution[tag_lower] = known_synthetic[tag_lower]
                continue
            if tag_lower in permanent:
                self.stats['cache_hits'] += 1
                cached_val = permanent[tag_lower]['value']
                tag_resolution[tag_lower] = None if cached_val == 'NOT_COLLECTION' else self._normalize_name(cached_val)
                continue
            cache_key = f"{CACHE_SCHEMA_VERSION}::{brand_slug}::tag::{tag_lower}"
            if cache_key in self.cache:
                self.stats['cache_hits'] += 1
                cached_val = self.cache[cache_key]
                tag_resolution[tag_lower] = None if cached_val == 'NOT_COLLECTION' else self._normalize_name(cached_val)
                self._save_permanent(brand_slug, tag_lower, cached_val)
                permanent[tag_lower] = {'value': cached_val}
            else:
                self.stats['cache_misses'] += 1
                uncached[tag_lower] = {
                    'tag': tag_sample_text.get(tag_lower, tag_lower),
                    'products': handles,
                    'freq': len(handles),
                }

        if uncached:
            if use_ai and self.client:
                positive, negative = self._ai_classify_all(uncached, product_candidates, brand_name, products)
            else:
                positive = self._fallback_classify(uncached)
                negative = set(uncached.keys()) - set(positive.keys())

            for tag_lower in list(negative):
                sample = uncached.get(tag_lower, {}).get('tag') or tag_sample_text.get(tag_lower, tag_lower)
                if is_recoverable_occasion_tag(sample):
                    recovered = self._normalize_name(sample)
                    positive[tag_lower] = recovered
                    negative.discard(tag_lower)
                elif map_specific_tag_to_collection(sample):
                    positive[tag_lower] = map_specific_tag_to_collection(sample)
                    negative.discard(tag_lower)

            for tag_lower, name in positive.items():
                norm_name = self._normalize_name(name)
                cache_key = f"{CACHE_SCHEMA_VERSION}::{brand_slug}::tag::{tag_lower}"
                self._save_cache(cache_key, norm_name)
                self._save_permanent(brand_slug, tag_lower, norm_name)
                tag_resolution[tag_lower] = norm_name
            for tag_lower in negative:
                cache_key = f"{CACHE_SCHEMA_VERSION}::{brand_slug}::tag::{tag_lower}"
                self._save_cache(cache_key, 'NOT_COLLECTION')
                self._save_permanent(brand_slug, tag_lower, 'NOT_COLLECTION')
                tag_resolution[tag_lower] = None

        collection_tag_freq: Dict[str, int] = {}
        for tag_lower, name in tag_resolution.items():
            if name:
                collection_tag_freq[tag_lower] = len(tag_to_products.get(tag_lower, []))

        collection_map: Dict[str, str] = {}
        for handle, candidates in product_candidates.items():
            matches: List[Tuple[int, int, str, str, bool]] = []
            seen_names = set()
            for c in candidates:
                cl = c.lower()
                name = tag_resolution.get(cl)
                if not name: name = known_synthetic.get(cl)
                if not name: continue
                if name.lower() in seen_names: continue
                seen_names.add(name.lower())
                freq = collection_tag_freq.get(cl, len(tag_to_products.get(cl, [])) or 9999)
                parent = is_parent_bucket(c) or is_parent_bucket(name)
                if name.lower() in ('accessories', 'fragrance') and not cl.startswith('__spec__'):
                    parent = True
                pri = candidate_priority.get(cl, 2)
                if cl.startswith('__spec__'): pri = 0
                elif cl.startswith('__type__'): pri = 1
                matches.append((pri, freq, cl, name, parent))

            if matches:
                matches.sort(key=lambda m: (m[0], 1 if m[4] else 0, m[1], -len(m[3].split()), -len(m[3]), m[3].lower()))
                collection_map[handle] = matches[0][3]
                continue

            type_coll = map_product_type_to_collection(products[handle].get('type', ''))
            if type_coll:
                collection_map[handle] = type_coll
                continue
            pref = handle.split('-')[0].upper()
            if pref in BRAND_PREFIX_COLLECTION_MAP:
                collection_map[handle] = BRAND_PREFIX_COLLECTION_MAP[pref]
                continue
            p_obj = products[handle]
            title_lower = p_obj.get('title', '').lower()
            tags_raw = p_obj.get('tags_raw', '').lower()
            found_line = None
            for kw_line in [
                'Daily Delights', 'Gardenia', 'Raha', 'Maya', 'Shades of Summer',
                'Everyday Pret', 'Casual Pret', 'Formal Pret', 'Chiffon Luxe',
                'Printed Swiss Lawn', 'Jhoomro', 'Elanora', 'Amaya', 'Feya',
                'Inam', 'Rania', 'Ballerina', 'Mukeshkari', 'Tiny Twinkles',
                'Royal Palace', 'The Silk', 'Trend Setters'
            ]:
                if kw_line.lower() in title_lower or kw_line.lower() in tags_raw:
                    found_line = kw_line
                    break
            if found_line:
                collection_map[handle] = found_line
                continue
            if 'unstitched' in tags_raw or 'lawn' in tags_raw:
                collection_map[handle] = 'Unstitched'
            elif 'pret' in tags_raw:
                collection_map[handle] = 'Pret'
            elif 'exclusive' in tags_raw:
                collection_map[handle] = 'Exclusive'
            else:
                collection_map[handle] = 'Other / Unmapped'

        debug_table = []
        for tag_lower, name in tag_resolution.items():
            sample = tag_sample_text.get(tag_lower, tag_lower)
            is_parent = bool(name) and (is_parent_bucket(sample) or is_parent_bucket(name))
            if name and is_parent: category = 'parent_bucket'
            elif name: category = 'collection'
            else: category = 'noise'
            debug_table.append({
                'tag': sample, 'category': category, 'mapped_to': name,
                'frequency': len(tag_to_products.get(tag_lower, [])), 'is_parent': is_parent,
            })
        debug_table.sort(key=lambda x: x['frequency'], reverse=True)
        return collection_map, self.stats, debug_table

    def _ai_classify_all(
        self, uncached: Dict, product_candidates: Dict, brand_name: str, products: Dict,
        batch_size: int = 40,
    ) -> Tuple[Dict[str, str], Set[str]]:
        sorted_items = sorted(uncached.items(), key=lambda kv: kv[1]['freq'], reverse=True)
        positive: Dict[str, str] = {}
        negative: Set[str] = set()
        num_batches = (len(sorted_items) + batch_size - 1) // batch_size
        for i in range(0, len(sorted_items), batch_size):
            batch = dict(sorted_items[i:i + batch_size])
            pos, neg = self._ai_classify_batch(batch, product_candidates, brand_name, products)
            positive.update(pos)
            negative.update(neg)
            for tag_lower in batch:
                if tag_lower not in pos and tag_lower not in neg:
                    negative.add(tag_lower)
            if num_batches > 1 and (i + batch_size) < len(sorted_items):
                time.sleep(1.5)
        return positive, negative

    def _call_with_retry(self, base_kwargs: dict, max_retries: int = 5):
        import random
        last_err = None
        for attempt in range(1, max_retries + 1):
            try:
                # Try with response_format first (works with gpt-5-mini on BluesMind)
                try:
                    return self.client.chat.completions.create(
                        response_format={"type": "json_object"}, **base_kwargs
                    )
                except Exception as rf_err:
                    rf_str = str(rf_err).lower()
                    # If response_format itself caused the error, retry without it
                    if 'response_format' in rf_str or 'unsupported' in rf_str or 'invalid' in rf_str:
                        return self.client.chat.completions.create(**base_kwargs)
                    # Otherwise, re-raise to be handled by outer retry logic
                    raise
            except Exception as e:
                err_str = str(e).lower()
                last_err = e
                # 403 Permission Denied: model not accessible — do NOT retry
                if '403' in err_str or 'permission' in err_str or 'no access to model' in err_str:
                    raise
                # Rate-limit / connection / timeout errors: retry with backoff
                if any(kw in err_str for kw in ('rate', 'limit', 'connection', 'timeout', '429', '503', '502')):
                    if attempt == max_retries:
                        break
                    wait = min(8 + (attempt - 1) * 10, 60) + random.uniform(0, 3)
                    print(
                        f"AI call rate-limited/unavailable (attempt {attempt}/{max_retries}), "
                        f"retrying in {wait:.1f}s: {e}"
                    )
                    time.sleep(wait)
                else:
                    # Other errors — raise immediately
                    raise
        raise last_err

    def _ai_classify_batch(
        self, batch: Dict, product_candidates: Dict, brand_name: str, products: Dict,
    ) -> Tuple[Dict[str, str], Set[str]]:
        self.stats['ai_calls'] += 1
        sorted_candidates = sorted(batch.values(), key=lambda x: x['freq'], reverse=True)
        candidate_list = [{'tag': c['tag'], 'in_products': c['freq']} for c in sorted_candidates]
        batch_tags_lower = set(batch.keys())

        sample_products = []
        for handle, candidates in product_candidates.items():
            if len(sample_products) >= 10:
                break
            if any(c.lower() in batch_tags_lower for c in candidates):
                sample_products.append({
                    'title': products[handle]['title'][:60],
                    'tags': candidates[:15],
                })

        # KEY FIX: Shorter prompt, JSON instruction in system message (not response_format)
        prompt = f"""You are looking at product TAGS exported from a Shopify store called "{brand_name}".
For each candidate tag below, decide if it names a CLOTHING COLLECTION / PRODUCT LINE / CATEGORY BUCKET,
or if it is noise (operational/size/fabric/color/sizechart/etc).

A tag IS a collection: named product lines ("Gardenia","Raha","Maya","Shades Of Summer"),
style categories ("Everyday Pret","Formal Pret","Casual Pret"), seasonal edits ("Festive Edition"),
or codenames ("mini26","Pret26","barfi","muse"). Short codenames with digits ARE collections.

A tag is NOT a collection: sizes, fabrics, colors, sale/discount tags, dates, product codes,
operational tags. Answer NOT_COLLECTION for those.

IMPORTANT: NEVER output "Sale / Clearance" as a collection name.

Return ONLY a JSON object mapping each candidate tag (exact text) to its properly capitalized
collection name, or "NOT_COLLECTION". No markdown fences, no explanation.

CANDIDATE TAGS:
{json.dumps(candidate_list, indent=1, ensure_ascii=False)}

SAMPLE PRODUCTS:
{json.dumps(sample_products, indent=1, ensure_ascii=False)}"""

        base_kwargs = dict(
            model=self.model,
            messages=[
                {
                    "role": "system",
                    "content": (
                        "You are a precise data classifier for an e-commerce inventory report. "
                        "You MUST respond with valid JSON only. No markdown, no code fences, no explanation. "
                        "Just the raw JSON object."
                    ),
                },
                {"role": "user", "content": prompt},
            ],
            temperature=0.0,
            max_tokens=4000,
        )

        try:
            response = self._call_with_retry(base_kwargs)
            result_text = (response.choices[0].message.content or '').strip()
            self.stats['ai_tokens'] += (response.usage.total_tokens if response.usage else 0)

            # Strip markdown code fences if present
            if result_text.startswith('```'):
                result_text = re.sub(r'^```(?:json)?\s*', '', result_text)
                result_text = re.sub(r'\s*```$', '', result_text)

            json_match = re.search(r'\{.*\}', result_text, re.DOTALL)
            result = json.loads(json_match.group(0) if json_match else result_text)

            positive: Dict[str, str] = {}
            negative: Set[str] = set()
            for tag_text, verdict in result.items():
                tag_lower = tag_text.lower().strip()
                if tag_lower not in batch:
                    continue
                if verdict and str(verdict).strip().upper() != 'NOT_COLLECTION':
                    positive[tag_lower] = self._normalize_name(str(verdict).strip())
                else:
                    negative.add(tag_lower)
            return positive, negative

        except Exception as e:
            import traceback
            print("=" * 60)
            print(f"AI classification failed for a batch - using fallback heuristic")
            print(f"   model={self.model} base_url={self.api_base_url}")
            print(f"   Error: {repr(e)}")
            traceback.print_exc()
            print("=" * 60)
            self.stats['last_ai_error'] = str(e)
            fb = self._fallback_classify(batch)
            neg = set(batch.keys()) - set(fb.keys())
            return fb, neg

    def _fallback_classify(self, uncached: Dict[str, Dict]) -> Dict[str, str]:
        results = {}
        codename = re.compile(r'^[A-Za-z][A-Za-z]{2,}[vV]?\d{0,4}$')
        named_edit = re.compile(r".+['\u2019]?\s*\d{2,4}$|.+\s+(pret|lawn|edit|formals?|bridals?)\b", re.I)

        for tag_lower, info in uncached.items():
            freq = info['freq']
            tag = strip_tag_wrappers(info['tag'])
            if is_noise_tag(tag)[0]: continue
            mapped = map_specific_tag_to_collection(tag)
            if mapped:
                results[tag_lower] = mapped
                continue
            if re.match(r'^[A-Za-z0-9&]+[_\-][A-Za-z0-9&\-_/]+$', tag) and freq >= 1:
                results[tag_lower] = self._normalize_name(tag)
                continue
            if is_recoverable_occasion_tag(tag) and freq >= 1:
                results[tag_lower] = self._normalize_name(tag)
                continue
            if named_edit.match(tag) and freq >= 2 and len(tag) >= 6:
                results[tag_lower] = self._normalize_name(tag)
                continue
            if codename.match(tag) and freq >= 3:
                results[tag_lower] = self._normalize_name(tag)
                continue
            if freq < 2: continue
            words = re.split(r"[\s_'']+", tag)
            words = [w for w in words if w]
            is_multi_word = len(words) >= 2
            has_caps = any(w[0].isupper() for w in words if w)
            is_all_lower = tag == tag.lower()
            if is_multi_word and (has_caps or freq >= 3):
                results[tag_lower] = self._normalize_name(tag)
            elif freq >= 5:
                results[tag_lower] = self._normalize_name(tag)
            elif has_caps and freq >= 3:
                results[tag_lower] = self._normalize_name(tag)
            elif not is_all_lower and len(words) == 1 and freq >= 4:
                results[tag_lower] = self._normalize_name(tag)
            elif is_all_lower and len(words) == 1 and 3 <= len(tag) <= 20 and freq >= 4:
                results[tag_lower] = self._normalize_name(tag)
        return results

    @staticmethod
    def _normalize_name(name: str) -> str:
        if not name: return 'Other / Unmapped'
        name = strip_tag_wrappers(name).strip()
        m = re.fullmatch(r'([A-Za-z]+?)([vV])?(\d{1,4})', name)
        if m and len(m.group(1)) >= 3:
            base = m.group(1)
            if base.upper() in ACRONYMS or (base.isupper() and len(base) <= 2):
                base_fmt = base.upper()
            elif base.islower() or base.isupper():
                base_fmt = base.capitalize()
            else:
                base_fmt = base[0].upper() + base[1:]
            v = m.group(2)
            digits = m.group(3)
            if v:
                return f"{base_fmt}V{digits}" if v.lower() == 'v' else f"{base_fmt}{v}{digits}"
            return f"{base_fmt}{digits}"

        name = re.sub(r"(['\u2019])\s*(\d{2,4})\b", r" '\2", name)
        if ' ' in name or not any(c in name for c in ('-', '&', '_')):
            name = re.sub(r'([a-z])([A-Z])', r'\1 \2', name)
        name = re.sub(r"\s+", " ", name).strip()
        words = name.split()
        result = []
        for i, w in enumerate(words):
            if re.fullmatch(r"'?\d{2,4}", w):
                result.append(w)
                continue
            if w.upper() in ACRONYMS:
                result.append(w.upper())
                continue
            upper_cnt = sum(1 for c in w if c.isupper())
            if upper_cnt >= 2 and not any(c in w for c in ('-', '_')) and not w.isupper():
                result.append(w)
                continue
            if any(c in w for c in ('&', '-', '/', '_')):
                sub_tokens = re.split(r'([&\-/_]+)', w)
                formatted_subs = []
                for sub in sub_tokens:
                    if re.match(r'^[&\-/_]+$', sub):
                        formatted_subs.append(sub)
                    elif sub.upper() in ACRONYMS or (len(sub) <= 2 and sub.isalpha()):
                        formatted_subs.append(sub.upper())
                    elif sub.islower() or sub.isupper():
                        formatted_subs.append(sub.capitalize())
                    else:
                        formatted_subs.append(sub)
                result.append(''.join(formatted_subs))
                continue
            if i > 0 and w.lower() in ('of', 'the', 'and', 'in', 'with', 'for', 'a', 'an'):
                result.append(w.lower())
            else:
                if w.islower() or w.isupper():
                    result.append(w.capitalize())
                else:
                    result.append(w)
        return ' '.join(result) if result else name


# --- CSV LOADER ---

def parse_int(val) -> int:
    try: return int(float(val or 0))
    except (TypeError, ValueError): return 0

def parse_float(val) -> float:
    try: return float(val or 0)
    except (TypeError, ValueError): return 0.0

def load_products(csv_path: str, brand_override: Optional[str] = None):
    by_handle: Dict[str, Dict[str, Any]] = {}
    with open(csv_path, 'r', encoding='utf-8', errors='replace') as f:
        for r in csv.DictReader(f):
            handle = (r.get('Handle') or '').strip()
            if not handle or handle == 'demo-product': continue
            if handle not in by_handle:
                by_handle[handle] = {
                    'title': '', 'type': '', 'tags_raw': '', 'status': '', 'published': '',
                    'vendor': '', 'total_qty': 0, 'total_value': 0.0, 'variant_rows': 0,
                }
            p = by_handle[handle]
            title = (r.get('Title') or '').strip()
            if title and not p['title']: p['title'] = title
            ptype = (r.get('Type') or '').strip()
            if ptype and not p['type']: p['type'] = ptype
            tags = (r.get('Tags') or '').strip()
            if tags and not p['tags_raw']: p['tags_raw'] = tags
            status = (r.get('Status') or '').strip()
            if status and not p['status']: p['status'] = status
            published = (r.get('Published') or '').strip()
            if published and not p['published']: p['published'] = published
            vendor = (r.get('Vendor') or '').strip()
            if vendor and not p['vendor']: p['vendor'] = vendor
            qty = parse_int(r.get('Variant Inventory Qty'))
            price = parse_float(r.get('Variant Price'))
            p['total_qty'] += qty
            p['total_value'] += qty * price
            p['variant_rows'] += 1

    products_with_stock: Dict[str, Dict[str, Any]] = {}
    active_published = 0
    with_stock_count = 0
    out_of_stock_count = 0
    total_units = 0
    total_value = 0.0
    for handle, p in by_handle.items():
        if p['status'].strip().lower() != 'active': continue
        if p['published'].strip().lower() != 'true': continue
        active_published += 1
        qty = p['total_qty']
        val = p['total_value']
        if qty > 0:
            with_stock_count += 1
            total_units += qty
            total_value += val
            products_with_stock[handle] = {
                'title': p['title'] or handle, 'type': p['type'], 'tags_raw': p['tags_raw'],
                'total_qty': qty, 'total_value': val, 'variant_rows': p['variant_rows'],
            }
        else:
            out_of_stock_count += 1

    detected_vendor = detect_brand(by_handle, brand_override)
    inventory_stats = {
        'active_published': active_published, 'products_with_stock': with_stock_count,
        'out_of_stock': out_of_stock_count, 'available_units': total_units,
        'inventory_value': total_value,
    }
    return products_with_stock, detected_vendor, inventory_stats


# --- AGGREGATION ---

def aggregate_by_collection(products, collection_map):
    colls = defaultdict(lambda: {
        'products': set(), 'products_with_stock': set(), 'products_out_of_stock': set(),
        'total_units': 0, 'total_value': 0.0, 'product_details': [],
    })
    for h, p in products.items():
        c = collection_map.get(h, 'Other / Unmapped')
        colls[c]['products'].add(h)
        colls[c]['products_with_stock'].add(h)
        colls[c]['total_units'] += p['total_qty']
        colls[c]['total_value'] += p['total_value']
        colls[c]['product_details'].append({
            'title': p['title'], 'type': p['type'], 'units': p['total_qty'],
            'value': p['total_value'], 'out_of_stock': False,
        })
    for c in colls:
        colls[c]['product_details'].sort(key=lambda x: (-x['value'], x['title'].lower()))
    return sorted(colls.items(), key=lambda x: x[1]['total_value'], reverse=True)


# --- FORMATTERS ---

def fmt_pkr(v):
    if v >= 1e7: return f"Rs {v/1e7:.2f} Cr"
    if v >= 1e5: return f"Rs {v/1e5:.1f}L"
    return f"Rs {v:,.0f}"

def fmt_pkr_short(v):
    if v >= 1e7: return f"Rs {v/1e7:.2f} Cr"
    if v >= 1e5: return f"Rs {v/1e5:.1f}L"
    return f"Rs {v:,.0f}"

def fmt_units(n):
    return f"{n:,}"

def _pdf_text(text) -> str:
    """Escape dynamic strings before interpolating into ReportLab Paragraphs."""
    if text is None: return ''
    raw = html.unescape(str(text))
    return xml_escape(raw)


# --- PDF GENERATION ---

class HRFlowable(Flowable):
    def __init__(self, width, thickness=0.5, color=colors.HexColor('#CCCCCC')):
        Flowable.__init__(self)
        self.width = width
        self.thickness = thickness
        self.color = color
        self.height = thickness + 4
    def draw(self):
        self.canv.setStrokeColor(self.color)
        self.canv.setLineWidth(self.thickness)
        self.canv.line(0, 2, self.width, 2)

def build_pdf(products, collection_map, brand_name, output_path, inventory_stats=None):
    collections = aggregate_by_collection(products, collection_map)
    stats = inventory_stats or {}
    active_published = int(stats.get('active_published', len(products)))
    with_stock = int(stats.get('products_with_stock', len(products)))
    out_of_stock = int(stats.get('out_of_stock', max(0, active_published - with_stock)))
    total_units = int(stats.get('available_units', sum(p['total_qty'] for p in products.values())))
    total_value = float(stats.get('inventory_value', sum(p['total_value'] for p in products.values())))

    doc = SimpleDocTemplate(
        output_path, pagesize=A4,
        rightMargin=15*mm, leftMargin=15*mm, topMargin=14*mm, bottomMargin=14*mm,
    )
    styles = getSampleStyleSheet()
    for name, kwargs in [
        ('Title2', dict(parent=styles['Title'], fontSize=18, leading=22, spaceAfter=1*mm,
                        textColor=colors.HexColor('#111827'), alignment=TA_LEFT)),
        ('BrandLine', dict(parent=styles['Normal'], fontSize=12, leading=15, spaceAfter=1*mm,
                           textColor=colors.HexColor('#1a6ecc'), fontName='Helvetica-Bold')),
        ('Subtitle', dict(parent=styles['Normal'], fontSize=9, leading=12, spaceAfter=3*mm,
                          textColor=colors.HexColor('#6B7280'))),
        ('ScopeNote', dict(parent=styles['Normal'], fontSize=8, leading=11, spaceAfter=4*mm,
                           textColor=colors.HexColor('#4B5563'))),
        ('MetricLabel', dict(parent=styles['Normal'], fontSize=7.5, leading=9,
                             textColor=colors.HexColor('#6B7280'))),
        ('MetricHint', dict(parent=styles['Normal'], fontSize=6.5, leading=8,
                            textColor=colors.HexColor('#9CA3AF'))),
        ('MetricValue', dict(parent=styles['Normal'], fontSize=15, leading=18,
                             textColor=colors.HexColor('#111827'), fontName='Helvetica-Bold')),
        ('MetricValueBlue', dict(parent=styles['Normal'], fontSize=15, leading=18,
                                 textColor=colors.HexColor('#1a6ecc'), fontName='Helvetica-Bold')),
        ('MetricValueRed', dict(parent=styles['Normal'], fontSize=15, leading=18,
                                textColor=colors.HexColor('#B91C1C'), fontName='Helvetica-Bold')),
        ('MetricValueGreen', dict(parent=styles['Normal'], fontSize=15, leading=18,
                                  textColor=colors.HexColor('#047857'), fontName='Helvetica-Bold')),
        ('SectionHeader', dict(parent=styles['Heading2'], fontSize=12, leading=15,
                               spaceBefore=4*mm, spaceAfter=3*mm, textColor=colors.HexColor('#111827'))),
        ('CollectionHeader', dict(parent=styles['Heading3'], fontSize=11, leading=14,
                                  spaceBefore=5*mm, spaceAfter=2*mm, textColor=colors.HexColor('#1a6ecc'))),
        ('TableCell', dict(parent=styles['Normal'], fontSize=8, leading=11)),
        ('TableCellBold', dict(parent=styles['Normal'], fontSize=8, leading=11, fontName='Helvetica-Bold')),
        ('TableHeader', dict(parent=styles['Normal'], fontSize=8, leading=11,
                             fontName='Helvetica-Bold', textColor=colors.white)),
        ('Footnote', dict(parent=styles['Normal'], fontSize=7, leading=9,
                          textColor=colors.HexColor('#9CA3AF'))),
        ('TotalRow', dict(parent=styles['Normal'], fontSize=8, leading=11, fontName='Helvetica-Bold')),
    ]:
        styles.add(ParagraphStyle(name, **kwargs))

    story = []
    pw = A4[0] - 30*mm

    story.append(Paragraph("INVENTORY REPORT", styles['Title2']))
    story.append(Paragraph(f"{_pdf_text(brand_name)} &mdash; Active product inventory", styles['BrandLine']))
    story.append(Paragraph(
        "Collection-wise stock and retail value for all active and published products with positive inventory",
        styles['Subtitle'],
    ))
    story.append(Paragraph(
        f"<b>Active + Published only</b> &nbsp;&middot;&nbsp; <b>Positive inventory only</b> "
        f"&nbsp;&middot;&nbsp; <b>All locations combined</b> &nbsp;&middot;&nbsp; "
        f"Generated {datetime.now().strftime('%d %b %Y, %I:%M %p')}",
        styles['ScopeNote'],
    ))

    def kpi_cell(label, hint, value, value_style):
        return [
            Paragraph(label, styles['MetricLabel']),
            Paragraph(str(value), value_style),
            Paragraph(hint, styles['MetricHint']),
        ]

    kpi_data = [[
        kpi_cell("Active + published", "Total products", f"{active_published:,}", styles['MetricValue']),
        kpi_cell("Products with stock", "Positive inventory", f"{with_stock:,}", styles['MetricValueBlue']),
        kpi_cell("Out of stock", "Zero inventory", f"{out_of_stock:,}", styles['MetricValueRed']),
        kpi_cell("Available units", "All locations", fmt_units(total_units), styles['MetricValue']),
        kpi_cell("Inventory value", "At retail price", fmt_pkr(total_value), styles['MetricValueGreen']),
    ]]
    flat_row = []
    for cell in kpi_data[0]:
        inner = Table([[c] for c in cell], colWidths=[pw/5 - 4])
        inner.setStyle(TableStyle([
            ('VALIGN', (0, 0), (-1, -1), 'TOP'),
            ('LEFTPADDING', (0, 0), (-1, -1), 4), ('RIGHTPADDING', (0, 0), (-1, -1), 4),
            ('TOPPADDING', (0, 0), (-1, -1), 1), ('BOTTOMPADDING', (0, 0), (-1, -1), 1),
        ]))
        flat_row.append(inner)
    kpi = Table([flat_row], colWidths=[pw/5]*5)
    kpi.setStyle(TableStyle([
        ('BACKGROUND', (0, 0), (-1, -1), colors.HexColor('#F8FAFC')),
        ('BOX', (0, 0), (-1, -1), 0.6, colors.HexColor('#E5E7EB')),
        ('INNERGRID', (0, 0), (-1, -1), 0.4, colors.HexColor('#E5E7EB')),
        ('VALIGN', (0, 0), (-1, -1), 'TOP'),
        ('TOPPADDING', (0, 0), (-1, -1), 6), ('BOTTOMPADDING', (0, 0), (-1, -1), 6),
        ('LEFTPADDING', (0, 0), (-1, -1), 2), ('RIGHTPADDING', (0, 0), (-1, -1), 2),
    ]))
    story.append(kpi)
    story.append(Spacer(1, 5*mm))

    story.append(Paragraph("COLLECTION WISE OVERVIEW", styles['SectionHeader']))
    sd = [[Paragraph(h, styles['TableHeader']) for h in ["Collection", "Products", "Available Units", "Retail Value"]]]
    sum_products = sum_units = 0
    sum_value = 0.0
    for cn, cd in collections:
        n_prod = len(cd['products'])
        sum_products += n_prod
        sum_units += cd['total_units']
        sum_value += cd['total_value']
        sd.append([
            Paragraph(_pdf_text(cn), styles['TableCellBold']),
            Paragraph(str(n_prod), styles['TableCell']),
            Paragraph(fmt_units(cd['total_units']), styles['TableCell']),
            Paragraph(fmt_pkr_short(cd['total_value']), styles['TableCell']),
        ])
    sd.append([
        Paragraph("Total", styles['TotalRow']), Paragraph(str(sum_products), styles['TotalRow']),
        Paragraph(fmt_units(sum_units), styles['TotalRow']), Paragraph(fmt_pkr_short(sum_value), styles['TotalRow']),
    ])
    cw = [pw*0.40, pw*0.15, pw*0.20, pw*0.25]
    st = Table(sd, colWidths=cw, repeatRows=1)
    last = len(sd) - 1
    st.setStyle(TableStyle([
        ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#1a6ecc')),
        ('TEXTCOLOR', (0, 0), (-1, 0), colors.white),
        ('BACKGROUND', (0, last), (-1, last), colors.HexColor('#EEF2FF')),
        ('FONTSIZE', (0, 0), (-1, -1), 8),
        ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
        ('TOPPADDING', (0, 0), (-1, -1), 3), ('BOTTOMPADDING', (0, 0), (-1, -1), 3),
        ('LEFTPADDING', (0, 0), (-1, -1), 4), ('RIGHTPADDING', (0, 0), (-1, -1), 4),
        ('LINEBELOW', (0, 0), (-1, -1), 0.3, colors.HexColor('#E0E0E0')),
        ('ROWBACKGROUNDS', (0, 1), (-1, last - 1), [colors.white, colors.HexColor('#F8FAFD')]),
        ('ALIGN', (1, 0), (-1, -1), 'CENTER'),
        ('BOX', (0, 0), (-1, -1), 0.5, colors.HexColor('#D1D5DB')),
    ]))
    story.append(st)
    story.append(Paragraph(
        "Method: Product = unique Handle. Units = SUM(Variant Inventory Qty) all locations. "
        "Value = SUM(Qty x Price) per variant row at retail. "
        "Filter: Status=active, Published=true. Collection tables: units > 0 only.",
        styles['Footnote'],
    ))
    story.append(PageBreak())

    story.append(Paragraph("TOP PRODUCTS PER COLLECTION &mdash; BY RETAIL VALUE", styles['SectionHeader']))
    story.append(Paragraph(
        "Each row is one product (unique Handle). Units/value summed across size variants. Positive inventory only.",
        ParagraphStyle('DN', parent=styles['Normal'], fontSize=8, textColor=colors.HexColor('#6B7280')),
    ))
    story.append(Spacer(1, 2*mm))

    for cn, cd in collections:
        story.append(Paragraph(
            f"{_pdf_text(cn)} &nbsp;&nbsp; {fmt_pkr_short(cd['total_value'])} &middot; {fmt_units(cd['total_units'])} units",
            styles['CollectionHeader'],
        ))
        if not cd['product_details']:
            story.append(Paragraph("No products in this collection.", styles['TableCell']))
            story.append(Spacer(1, 2*mm))
            continue
        dd = [[Paragraph(h, styles['TableHeader']) for h in ["Product", "Units", "Retail Value"]]]
        for pi in cd['product_details']:
            dd.append([
                Paragraph(_pdf_text(pi['title']), styles['TableCellBold']),
                Paragraph(fmt_units(pi['units']), styles['TableCell']),
                Paragraph(fmt_pkr_short(pi['value']), styles['TableCell']),
            ])
        dt = Table(dd, colWidths=[pw*0.55, pw*0.18, pw*0.27], repeatRows=1)
        dt.setStyle(TableStyle([
            ('BACKGROUND', (0, 0), (-1, 0), colors.HexColor('#374151')),
            ('TEXTCOLOR', (0, 0), (-1, 0), colors.white),
            ('FONTSIZE', (0, 0), (-1, -1), 8),
            ('VALIGN', (0, 0), (-1, -1), 'MIDDLE'),
            ('TOPPADDING', (0, 0), (-1, -1), 3), ('BOTTOMPADDING', (0, 0), (-1, -1), 3),
            ('LEFTPADDING', (0, 0), (-1, -1), 4), ('RIGHTPADDING', (0, 0), (-1, -1), 4),
            ('LINEBELOW', (0, 0), (-1, -1), 0.3, colors.HexColor('#E0E0E0')),
            ('ROWBACKGROUNDS', (0, 1), (-1, -1), [colors.white, colors.HexColor('#F8FAFD')]),
            ('ALIGN', (1, 0), (-1, -1), 'CENTER'),
        ]))
        story.append(dt)
        story.append(Spacer(1, 3*mm))

    story.append(Spacer(1, 6*mm))
    story.append(Paragraph(
        f"{_pdf_text(brand_name)} Inventory Report &nbsp;&middot;&nbsp; Active + Published &middot; "
        f"Positive Inventory &middot; All Locations",
        styles['Footnote'],
    ))
    doc.build(story)
    return output_path


# --- CLEANUP ---

def cleanup_old_jobs(max_age=TEMP_FILE_TTL_MINUTES):
    now = datetime.now()
    cutoff = now - timedelta(minutes=max_age)
    for jid in [j for j, i in JOBS.items() if i.get("created_at") and i["created_at"] < cutoff]:
        jd = JOBS[jid].get("job_dir")
        if jd and os.path.exists(jd):
            shutil.rmtree(jd, ignore_errors=True)
        JOBS.pop(jid, None)
    if os.path.exists(TEMP_JOBS_DIR):
        for e in os.listdir(TEMP_JOBS_DIR):
            ep = os.path.join(TEMP_JOBS_DIR, e)
            if os.path.isdir(ep):
                try:
                    if datetime.fromtimestamp(os.path.getmtime(ep)) < cutoff:
                        shutil.rmtree(ep, ignore_errors=True)
                except Exception:
                    pass

def get_server_storage_stats():
    cf = cs = 0
    if os.path.exists(CACHE_DIR):
        for f in os.listdir(CACHE_DIR):
            if f.endswith('.json'):
                cf += 1
                cs += os.path.getsize(os.path.join(CACHE_DIR, f))
    tj = ts = 0
    if os.path.exists(TEMP_JOBS_DIR):
        for r, d, fs in os.walk(TEMP_JOBS_DIR):
            for f in fs:
                try: ts += os.path.getsize(os.path.join(r, f))
                except Exception: pass
        tj = len(os.listdir(TEMP_JOBS_DIR))
    return {
        "cache_files": cf, "cache_size_kb": round(cs/1024, 2),
        "temp_jobs_count": tj, "temp_size_mb": round(ts/(1024*1024), 2),
        "active_memory_jobs": len(JOBS),
    }


# --- FASTAPI APP ---

app = FastAPI(title="Shopify Inventory Report Generator Pro v4.7", version="4.7.0")
app.add_middleware(
    CORSMiddleware, allow_origins=["*"], allow_credentials=True,
    allow_methods=["*"], allow_headers=["*"],
)

@app.get("/", response_class=HTMLResponse)
async def serve_frontend():
    return HTMLResponse(content=get_html())

def get_html():
    return r"""<!DOCTYPE html>
<html lang="en" class="bg-slate-50 text-slate-800">
<head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>Shopify Inventory Pro v4.7 — BluesMind API Fix</title>
<script src="https://cdn.tailwindcss.com"></script>
<script src="https://unpkg.com/lucide@latest"></script></head>
<body class="min-h-screen flex flex-col font-sans">
<header class="bg-white border-b border-slate-200 sticky top-0 z-40 shadow-sm">
<div class="max-w-6xl mx-auto px-4 sm:px-6 py-4 flex items-center justify-between">
<div class="flex items-center space-x-3">
<div class="w-10 h-10 rounded-xl bg-gradient-to-tr from-blue-600 to-indigo-500 flex items-center justify-center text-white shadow-md"><i data-lucide="file-bar-chart-2" class="w-6 h-6"></i></div>
<div><h1 class="text-lg font-bold text-slate-900">Shopify Inventory Pro <span class="text-xs font-normal text-emerald-600 bg-emerald-50 px-1.5 py-0.5 rounded">v4.7</span></h1>
<p class="text-xs text-slate-500">BluesMind API Fix &bull; No more crashes</p></div></div>
<div class="flex items-center space-x-3">
<button onclick="refreshStats()" class="inline-flex items-center space-x-1.5 px-3 py-1.5 rounded-lg border border-slate-200 bg-slate-50 hover:bg-slate-100 text-xs font-medium text-slate-600"><i data-lucide="database" class="w-3.5 h-3.5"></i><span id="cache-status">Cache: ...</span></button>
<button onclick="resetLearning()" class="inline-flex items-center space-x-1 px-3 py-1.5 rounded-lg bg-amber-50 text-amber-700 hover:bg-amber-100 text-xs font-medium border border-amber-200"><i data-lucide="refresh-ccw" class="w-3.5 h-3.5"></i><span>Reset Learning</span></button>
<button onclick="cleanServer()" class="inline-flex items-center space-x-1 px-3 py-1.5 rounded-lg bg-rose-50 text-rose-600 hover:bg-rose-100 text-xs font-medium border border-rose-200"><i data-lucide="trash-2" class="w-3.5 h-3.5"></i><span>Free Space</span></button>
</div></div></header>
<main class="flex-1 max-w-6xl w-full mx-auto px-4 sm:px-6 py-8 grid grid-cols-1 lg:grid-cols-12 gap-8 items-start">
<div class="lg:col-span-5 space-y-6">
<div class="bg-white rounded-2xl border border-slate-200 shadow-sm p-6">
<h2 class="text-base font-semibold text-slate-900 flex items-center space-x-2 mb-4"><i data-lucide="upload-cloud" class="w-5 h-5 text-blue-600"></i><span>1. Upload Shopify CSV</span></h2>
<div id="dropzone" class="border-2 border-dashed border-slate-300 rounded-xl p-6 text-center cursor-pointer hover:border-blue-500 flex flex-col items-center justify-center min-h-[160px]" onclick="document.getElementById('csv-file-input').click()">
<input type="file" id="csv-file-input" accept=".csv" class="hidden" onchange="handleFile(this.files)">
<div id="upload-prompt" class="space-y-2"><div class="w-12 h-12 rounded-full bg-blue-50 text-blue-600 flex items-center justify-center mx-auto"><i data-lucide="file-spreadsheet" class="w-6 h-6"></i></div>
<p class="text-sm font-medium text-slate-700">Drop CSV here or click to browse</p>
<p class="text-xs text-slate-400">Works with Minnie Minors and any Shopify store export</p></div>
<div id="file-info" class="hidden w-full"><div class="p-3 bg-blue-50 border border-blue-200 rounded-lg flex items-center justify-between">
<div class="flex items-center space-x-3 overflow-hidden"><i data-lucide="check-circle-2" class="w-5 h-5 text-blue-600"></i>
<div class="overflow-hidden"><p id="file-name" class="text-sm font-medium truncate"></p><p id="file-size" class="text-xs text-slate-500"></p></div></div>
<button onclick="clearFile(event)" class="text-slate-400 hover:text-slate-600 p-1"><i data-lucide="x" class="w-4 h-4"></i></button></div></div></div></div>
<div class="bg-white rounded-2xl border border-slate-200 shadow-sm p-6 space-y-5">
<h2 class="text-base font-semibold flex items-center space-x-2"><i data-lucide="sliders" class="w-5 h-5 text-blue-600"></i><span>2. Settings</span></h2>
<div>
<label class="block text-xs font-semibold uppercase tracking-wider text-slate-500 mb-2">Detection Mode</label>
<div class="space-y-2">
<label class="flex items-start p-3 rounded-xl border border-blue-500 bg-blue-50/40 cursor-pointer">
<input type="radio" name="mode" value="ai" checked class="mt-0.5">
<div class="ml-3 text-xs"><span class="font-bold text-blue-700">AI-Powered (Recommended)</span>
<span class="bg-emerald-100 text-emerald-800 text-[10px] px-1.5 py-0.2 rounded ml-1">v4.7</span>
<p class="text-slate-600 mt-0.5">Smart brand SKU/prefix resolution with BluesMind AI.</p></div></label>
<label class="flex items-start p-3 rounded-xl border border-slate-200 cursor-pointer hover:bg-slate-50">
<input type="radio" name="mode" value="fast" class="mt-0.5">
<div class="ml-3 text-xs"><span class="font-bold text-emerald-700">Fast Pattern Mode</span>
<span class="bg-slate-100 text-slate-700 text-[10px] px-1.5 py-0.2 rounded ml-1">$0.00</span>
<p class="text-slate-600 mt-0.5">Zero API cost. Pattern heuristics + brand prefix mapping.</p></div></label>
</div></div>
<div><label class="block text-xs font-semibold uppercase tracking-wider text-slate-500 mb-1.5">Brand Name (optional)</label>
<input type="text" id="brand-name" placeholder="Auto-detected from active products & vendor" class="w-full px-3.5 py-2 border border-slate-300 rounded-lg text-sm focus:ring-2 focus:ring-blue-500 outline-none"></div>
<div><label class="block text-xs font-semibold uppercase tracking-wider text-slate-500 mb-1.5">Tags To Always Ignore (optional)</label>
<textarea id="ignore-tags" rows="2" placeholder="Comma-separated, e.g. Staff Pick, VIP Only" class="w-full px-3.5 py-2 border border-slate-300 rounded-lg text-xs focus:ring-2 focus:ring-blue-500 outline-none"></textarea>
<p class="text-[11px] text-slate-400 mt-1">Per-brand only. Operational noise is already filtered.</p></div>
<details class="group border border-slate-200 rounded-xl">
<summary class="px-4 py-2.5 text-xs font-medium text-slate-600 cursor-pointer flex items-center justify-between"><span>Custom API Settings</span><i data-lucide="chevron-down" class="w-4 h-4 text-slate-400 group-open:rotate-180 transition"></i></summary>
<div class="px-4 pb-4 pt-2 border-t border-slate-100 space-y-3 text-xs">
<div><label class="block text-slate-500 mb-1">API Key</label><input type="password" id="api-key" placeholder="Default built-in key" class="w-full px-3 py-1.5 border border-slate-300 rounded"></div>
<div><label class="block text-slate-500 mb-1">API Base URL</label><input type="text" id="api-base" placeholder="https://api.bluesminds.com/v1" class="w-full px-3 py-1.5 border border-slate-300 rounded"></div>
<div><label class="block text-slate-500 mb-1">Model</label><input type="text" id="api-model" placeholder="gpt-5-mini" class="w-full px-3 py-1.5 border border-slate-300 rounded"></div>
</div></details>
<button id="generate-btn" onclick="startGen()" disabled class="w-full py-3 rounded-xl font-semibold text-sm text-white bg-slate-300 cursor-not-allowed flex items-center justify-center space-x-2">
<i data-lucide="zap" class="w-4 h-4"></i><span>Generate Report</span></button></div></div>
<div class="lg:col-span-7 space-y-6">
<div id="welcome" class="bg-white rounded-2xl border border-slate-200 shadow-sm p-8 text-center min-h-[450px] flex flex-col items-center justify-center">
<div class="w-16 h-16 rounded-2xl bg-slate-100 text-slate-400 flex items-center justify-center mb-4"><i data-lucide="file-text" class="w-8 h-8"></i></div>
<h3 class="text-base font-bold">Upload a CSV to get started</h3>
<p class="text-sm text-slate-500 mt-1 max-w-sm">v4.7 fixes the BluesMind API crash. Correct model + robust fallback.</p>
<div class="mt-6 grid grid-cols-2 gap-3 text-left max-w-md w-full">
<div class="p-3 rounded-xl bg-emerald-50 border border-emerald-200/80">
<p class="text-emerald-700 font-semibold text-xs mb-1">API Crash Fixed</p>
<p class="text-slate-500 text-[11px]">Correct model (gpt-5-mini) + 403 errors handled gracefully.</p></div>
<div class="p-3 rounded-xl bg-blue-50 border border-blue-200/80">
<p class="text-blue-700 font-semibold text-xs mb-1">Brand Prefix Engine</p>
<p class="text-slate-500 text-[11px]">SP-, DD-, NR-, AM-, MK-, TW- prefix fallback mapping.</p></div>
<div class="p-3 rounded-xl bg-purple-50 border border-purple-200/80">
<p class="text-purple-700 font-semibold text-xs mb-1">Robust Fallback</p>
<p class="text-slate-500 text-[11px]">If AI fails, heuristic classification still works.</p></div>
<div class="p-3 rounded-xl bg-amber-50 border border-amber-200/80">
<p class="text-amber-700 font-semibold text-xs mb-1">Auditable</p>
<p class="text-slate-500 text-[11px]">Detailed tag classification table included.</p></div>
</div></div>
<div id="loading" class="hidden bg-white rounded-2xl border border-slate-200 shadow-sm p-8 text-center min-h-[450px] flex flex-col items-center justify-center">
<div class="relative w-20 h-20 mb-6"><div class="absolute inset-0 border-4 border-blue-200 rounded-full"></div>
<div class="absolute inset-0 border-4 border-blue-600 rounded-full border-t-transparent animate-spin"></div></div>
<h3 id="load-title" class="text-lg font-bold">Analyzing...</h3>
<p id="load-desc" class="text-sm text-slate-500 mb-4">Processing CSV and detecting collections &amp; vendor...</p>
<div class="w-full max-w-sm bg-slate-50 rounded-xl p-4 text-left text-xs space-y-2 border">
<div id="s1" class="flex items-center space-x-2 text-slate-400"><span class="w-4 h-4 rounded-full border border-slate-300 flex items-center justify-center text-[10px]">1</span><span>Extracting tags &amp; detecting brand name...</span></div>
<div id="s2" class="flex items-center space-x-2 text-slate-400"><span class="w-4 h-4 rounded-full border border-slate-300 flex items-center justify-center text-[10px]">2</span><span>AI classifying + specificity ranking...</span></div>
<div id="s3" class="flex items-center space-x-2 text-slate-400"><span class="w-4 h-4 rounded-full border border-slate-300 flex items-center justify-center text-[10px]">3</span><span>Generating PDF report...</span></div>
</div></div>
<div id="results" class="hidden space-y-6">
<div class="bg-gradient-to-r from-blue-600 to-indigo-700 rounded-2xl p-6 text-white shadow-lg flex flex-col sm:flex-row items-center justify-between gap-4">
<div><span class="px-2.5 py-0.5 rounded-full bg-white/20 text-[10px] font-bold uppercase">Report Ready</span>
<h3 id="res-title" class="text-xl font-extrabold mt-1"></h3>
<p id="res-subtitle" class="text-blue-100 text-xs mt-0.5"></p></div>
<div class="flex space-x-3"><a id="dl-link" href="#" class="inline-flex items-center space-x-2 bg-white text-blue-700 px-5 py-3 rounded-xl font-bold text-sm"><i data-lucide="download" class="w-4 h-4"></i><span>Download PDF</span></a>
<button onclick="delJob()" class="p-3 bg-white/10 hover:bg-white/20 rounded-xl"><i data-lucide="trash-2" class="w-4 h-4"></i></button></div></div>
<div class="grid grid-cols-2 sm:grid-cols-5 gap-3">
<div class="bg-white p-3 rounded-xl border"><p class="text-slate-400 text-[10px] font-semibold uppercase">Active + Published</p><p id="st-p" class="text-xl font-extrabold mt-1">0</p><p class="text-[10px] text-slate-400">Total products</p></div>
<div class="bg-white p-3 rounded-xl border"><p class="text-slate-400 text-[10px] font-semibold uppercase">With Stock</p><p id="st-s" class="text-xl font-extrabold text-blue-600 mt-1">0</p><p class="text-[10px] text-slate-400">Positive inventory</p></div>
<div class="bg-white p-3 rounded-xl border"><p class="text-slate-400 text-[10px] font-semibold uppercase">Out of Stock</p><p id="st-oos" class="text-xl font-extrabold text-rose-600 mt-1">0</p><p class="text-[10px] text-slate-400">Zero inventory</p></div>
<div class="bg-white p-3 rounded-xl border"><p class="text-slate-400 text-[10px] font-semibold uppercase">Available Units</p><p id="st-u" class="text-xl font-extrabold mt-1">0</p><p class="text-[10px] text-slate-400">All locations</p></div>
<div class="bg-white p-3 rounded-xl border"><p class="text-slate-400 text-[10px] font-semibold uppercase">Inventory Value</p><p id="st-v" class="text-lg font-extrabold text-emerald-600 mt-1">0</p><p class="text-[10px] text-slate-400">At retail price</p></div>
</div>
<div id="ai-stats" class="hidden bg-white rounded-xl border p-4">
<h4 class="font-bold text-sm mb-2 flex items-center space-x-2"><i data-lucide="cpu" class="w-4 h-4 text-blue-600"></i><span>AI Processing Details</span></h4>
<div class="grid grid-cols-4 gap-3 text-center text-xs">
<div class="p-2 bg-blue-50 rounded-lg"><p class="font-bold text-blue-700 text-lg" id="ai-cached">0</p><p class="text-slate-500">Cache Hits</p></div>
<div class="p-2 bg-amber-50 rounded-lg"><p class="font-bold text-amber-700 text-lg" id="ai-missed">0</p><p class="text-slate-500">Cache Misses</p></div>
<div class="p-2 bg-purple-50 rounded-lg"><p class="font-bold text-purple-700 text-lg" id="ai-calls">0</p><p class="text-slate-500">AI API Calls</p></div>
<div class="p-2 bg-emerald-50 rounded-lg"><p class="font-bold text-emerald-700 text-lg" id="ai-tokens">0</p><p class="text-slate-500">Tokens Used</p></div>
</div></div>
<div class="bg-white rounded-2xl border overflow-hidden">
<div class="p-4 bg-slate-50 border-b flex items-center justify-between"><h4 class="font-bold text-sm flex items-center space-x-2"><i data-lucide="layers" class="w-4 h-4 text-blue-600"></i><span>Collections</span></h4>
<span id="st-c" class="text-xs bg-slate-200 px-2.5 py-0.5 rounded-full font-semibold">0</span></div>
<div class="overflow-x-auto max-h-[400px]"><table class="w-full text-left border-collapse">
<thead><tr class="bg-slate-100/70 text-[11px] font-bold text-slate-600 uppercase sticky top-0">
<th class="py-2.5 px-4">Collection</th><th class="py-2.5 px-3 text-center">Products</th><th class="py-2.5 px-3 text-right">Units</th><th class="py-2.5 px-4 text-right">Retail Value</th></tr></thead>
<tbody id="col-tbody" class="divide-y divide-slate-100 text-xs"></tbody></table></div></div>
<div id="tag-debug-wrap" class="hidden bg-white rounded-2xl border overflow-hidden">
<div class="p-4 bg-slate-50 border-b"><h4 class="font-bold text-sm flex items-center space-x-2"><i data-lucide="search-check" class="w-4 h-4 text-blue-600"></i><span>Tag Classification Audit</span></h4>
<p class="text-[11px] text-slate-500 mt-0.5">COLLECTION = named line &bull; PARENT = category bucket &bull; NOISE = ignored</p></div>
<div class="overflow-x-auto max-h-[320px]"><table class="w-full text-left border-collapse text-xs">
<thead><tr class="bg-slate-100/70 text-[11px] font-bold text-slate-600 uppercase sticky top-0">
<th class="py-2 px-3">Tag</th><th class="py-2 px-3">Verdict</th><th class="py-2 px-3">Mapped Collection</th><th class="py-2 px-3 text-right">Products</th></tr></thead>
<tbody id="tag-debug-tbody" class="divide-y divide-slate-100"></tbody></table></div></div>
</div>
</main>
<footer class="bg-white border-t py-4 text-center text-xs text-slate-400">Shopify Inventory Pro v4.7 — BluesMind API Crash Fix</footer>
<script>
lucide.createIcons();let selFile=null,jobId=null;
const dz=document.getElementById('dropzone');
['dragenter','dragover','dragleave','drop'].forEach(e=>dz.addEventListener(e,ev=>{ev.preventDefault();ev.stopPropagation()},false));
['dragenter','dragover'].forEach(e=>dz.addEventListener(e,()=>dz.classList.add('dropzone-active'),false));
['dragleave','drop'].forEach(e=>dz.addEventListener(e,()=>dz.classList.remove('dropzone-active'),false));
dz.addEventListener('drop',e=>handleFile(e.dataTransfer.files),false);
function esc(s){const d=document.createElement('div');d.textContent=s==null?'':String(s);return d.innerHTML}
function handleFile(files){if(!files||!files.length)return;const f=files[0];
if(!f.name.toLowerCase().endsWith('.csv')){alert('Select .csv file');return}
selFile=f;document.getElementById('file-name').textContent=f.name;
document.getElementById('file-size').textContent=(f.size/1024).toFixed(1)+' KB';
document.getElementById('upload-prompt').classList.add('hidden');
document.getElementById('file-info').classList.remove('hidden');
const b=document.getElementById('generate-btn');b.disabled=false;
b.className="w-full py-3 rounded-xl font-semibold text-sm text-white bg-blue-600 hover:bg-blue-700 cursor-pointer flex items-center justify-center space-x-2";lucide.createIcons()}
function clearFile(e){e.stopPropagation();selFile=null;
document.getElementById('csv-file-input').value='';
document.getElementById('upload-prompt').classList.remove('hidden');
document.getElementById('file-info').classList.add('hidden');
const b=document.getElementById('generate-btn');b.disabled=true;
b.className="w-full py-3 rounded-xl font-semibold text-sm text-white bg-slate-300 cursor-not-allowed flex items-center justify-center space-x-2"}
function setStep(id,s){const el=document.getElementById(id);if(!el)return;
if(s==='active'){el.className="flex items-center space-x-2 text-blue-600 font-semibold";
el.querySelector('span').className="w-4 h-4 rounded-full bg-blue-600 text-white flex items-center justify-center text-[10px]"}
else if(s==='done'){el.className="flex items-center space-x-2 text-emerald-600 font-semibold";
el.querySelector('span').className="w-4 h-4 rounded-full bg-emerald-600 text-white flex items-center justify-center text-[10px]"}
else{el.className="flex items-center space-x-2 text-slate-400";
el.querySelector('span').className="w-4 h-4 rounded-full border border-slate-300 flex items-center justify-center text-[10px]"}}
async function startGen(){if(!selFile)return;
document.getElementById('welcome').classList.add('hidden');
document.getElementById('results').classList.add('hidden');
document.getElementById('loading').classList.remove('hidden');
setStep('s1','active');setStep('s2','pending');setStep('s3','pending');
const fd=new FormData();fd.append('csv_file',selFile);
const m=document.querySelector('input[name="mode"]:checked').value;
fd.append('use_ai',m==='ai'?'true':'false');
const br=document.getElementById('brand-name').value.trim();if(br)fd.append('brand',br);
const ig=document.getElementById('ignore-tags').value.trim();if(ig)fd.append('ignore_tags',ig);
const ak=document.getElementById('api-key').value.trim();if(ak)fd.append('api_key',ak);
const ab=document.getElementById('api-base').value.trim();if(ab)fd.append('api_base_url',ab);
const am=document.getElementById('api-model').value.trim();if(am)fd.append('api_model',am);
try{const r=await fetch('/api/generate',{method:'POST',body:fd});
const d=await r.json();if(!r.ok)throw new Error(d.detail||'Failed');
jobId=d.job_id;renderResults(d);refreshStats()}
catch(e){alert('Error: '+e.message);document.getElementById('loading').classList.add('hidden');
document.getElementById('welcome').classList.remove('hidden')}}
function renderResults(d){document.getElementById('loading').classList.add('hidden');
document.getElementById('results').classList.remove('hidden');
document.getElementById('res-title').textContent=(d.brand||'Store')+' Inventory Report';
document.getElementById('st-p').textContent=(d.active_published!=null?d.active_published:d.total_products).toLocaleString();
document.getElementById('st-s').textContent=d.products_with_stock.toLocaleString();
document.getElementById('st-oos').textContent=(d.products_out_of_stock!=null?d.products_out_of_stock:0).toLocaleString();
document.getElementById('st-u').textContent=d.total_units.toLocaleString();
document.getElementById('st-v').textContent=d.formatted_value;
document.getElementById('st-c').textContent=d.collections.length+' Collections';
document.getElementById('dl-link').href='/api/download/'+d.job_id;
document.getElementById('res-subtitle').textContent=
  (d.active_published!=null?d.active_published:d.total_products)+' active+published &middot; '+
  d.products_with_stock+' with stock &middot; '+(d.products_out_of_stock!=null?d.products_out_of_stock:0)+' out of stock &middot; '+
  d.collections.length+' collections';
if(d.ai_stats){document.getElementById('ai-stats').classList.remove('hidden');
document.getElementById('ai-cached').textContent=d.ai_stats.cache_hits;
document.getElementById('ai-missed').textContent=d.ai_stats.cache_misses;
document.getElementById('ai-calls').textContent=d.ai_stats.ai_calls;
document.getElementById('ai-tokens').textContent=d.ai_stats.ai_tokens.toLocaleString()}
const tb=document.getElementById('col-tbody');tb.innerHTML='';
d.collections.forEach((c,i)=>{const tr=document.createElement('tr');tr.className=i%2===0?'bg-white':'bg-slate-50/60';
tr.innerHTML='<td class="py-2.5 px-4 font-bold text-slate-800">'+esc(c.name)+'</td><td class="py-2.5 px-3 text-center">'+c.products_count+'</td><td class="py-2.5 px-3 text-right font-mono">'+c.units.toLocaleString()+'</td><td class="py-2.5 px-4 text-right font-bold font-mono">'+c.formatted_value+'</td>';
tb.appendChild(tr)});
if(d.tag_classification_sample&&d.tag_classification_sample.length){document.getElementById('tag-debug-wrap').classList.remove('hidden');
const tb2=document.getElementById('tag-debug-tbody');tb2.innerHTML='';
d.tag_classification_sample.forEach(t=>{const tr=document.createElement('tr');
let badge;
if(t.category==='collection') badge='<span class="px-1.5 py-0.5 rounded bg-emerald-100 text-emerald-700 text-[10px] font-bold">COLLECTION</span>';
else if(t.category==='parent_bucket') badge='<span class="px-1.5 py-0.5 rounded bg-amber-100 text-amber-700 text-[10px] font-bold">PARENT</span>';
else badge='<span class="px-1.5 py-0.5 rounded bg-slate-100 text-slate-500 text-[10px] font-bold">NOISE</span>';
tr.innerHTML='<td class="py-1.5 px-3">'+esc(t.tag)+'</td><td class="py-1.5 px-3">'+badge+'</td><td class="py-1.5 px-3">'+esc(t.mapped_to||'—')+'</td><td class="py-1.5 px-3 text-right font-mono">'+t.frequency+'</td>';
tb2.appendChild(tr)})}
lucide.createIcons()}
async function refreshStats(){try{const r=await fetch('/api/storage-stats');const s=await r.json();
document.getElementById('cache-status').textContent='Cache: '+s.cache_files+' tags ('+s.cache_size_kb+' KB) &bull; '+s.temp_jobs_count+' jobs'}catch(e){}}
async function cleanServer(){if(!confirm('Delete all temp report files?'))return;
try{await fetch('/api/cleanup?force_all=true',{method:'POST'});refreshStats()}catch(e){}}
async function resetLearning(){if(!confirm('Clear all cached collection classifications for every brand?'))return;
try{await fetch('/api/cleanup?force_all=true&clear_classification_cache=true',{method:'POST'});refreshStats();alert('Collection learning cache cleared.')}catch(e){}}
async function delJob(){if(!jobId||!confirm('Delete report?'))return;
try{await fetch('/api/jobs/'+jobId,{method:'DELETE'});
document.getElementById('results').classList.add('hidden');
document.getElementById('welcome').classList.remove('hidden');refreshStats()}catch(e){}}
refreshStats();</script></body></html>"""


@app.post("/api/generate")
async def generate_inventory_report(
    background_tasks: BackgroundTasks,
    csv_file: UploadFile = File(...),
    use_ai: bool = Form(True),
    brand: Optional[str] = Form(None),
    api_key: Optional[str] = Form(None),
    api_base_url: Optional[str] = Form(None),
    api_model: Optional[str] = Form(None),
    ignore_tags: Optional[str] = Form(None),
):
    background_tasks.add_task(cleanup_old_jobs)
    job_id = str(uuid.uuid4())[:12]
    job_dir = os.path.join(TEMP_JOBS_DIR, f"job_{job_id}")
    os.makedirs(job_dir, exist_ok=True)
    csv_path = os.path.join(job_dir, "products_export.csv")
    pdf_path = os.path.join(job_dir, f"report_{job_id}.pdf")

    try:
        with open(csv_path, "wb") as buf:
            shutil.copyfileobj(csv_file.file, buf)

        products, auto_brand, inv_stats = load_products(csv_path, brand)
        use_brand = brand or auto_brand

        if inv_stats.get('active_published', 0) == 0:
            raise HTTPException(400, "No active & published products found.")
        if not products:
            raise HTTPException(
                400,
                "Active & published products found, but none have positive inventory (units > 0).",
            )

        ignore_set = set()
        if ignore_tags:
            ignore_set = {t.strip() for t in ignore_tags.split(',') if t.strip()}

        t0 = time.time()
        detector = CollectionDetector(api_key=api_key, api_base_url=api_base_url, model=api_model)
        collection_map, ai_stats, debug_table = detector.detect(
            products, use_brand, use_ai=use_ai, custom_ignore_tags=ignore_set
        )
        detect_time = time.time() - t0

        build_pdf(products, collection_map, use_brand, pdf_path, inventory_stats=inv_stats)
        collections_data = aggregate_by_collection(products, collection_map)

        tp_stock = inv_stats['products_with_stock']
        tp_all = inv_stats['active_published']
        tp_oos = inv_stats['out_of_stock']
        tu = inv_stats['available_units']
        tv = inv_stats['inventory_value']

        cs = [{
            "name": n, "products_count": len(d['products']), "stock_count": len(d['products']),
            "stock_out_count": 0, "units": d['total_units'], "value": d['total_value'],
            "formatted_value": fmt_pkr_short(d['total_value']),
        } for n, d in collections_data]

        JOBS[job_id] = {
            "job_id": job_id, "created_at": datetime.now(), "job_dir": job_dir,
            "pdf_path": pdf_path, "brand": use_brand,
        }

        return JSONResponse({
            "status": "success", "job_id": job_id, "brand": use_brand,
            "active_published": tp_all, "total_products": tp_all,
            "products_with_stock": tp_stock, "products_out_of_stock": tp_oos,
            "total_units": tu, "total_value": tv, "formatted_value": fmt_pkr(tv),
            "collections": cs,
            "ai_stats": {**ai_stats, "detect_time_sec": round(detect_time, 3)},
            "detect_time_sec": round(detect_time, 3),
            "tag_classification_sample": debug_table[:80],
            "method": {
                "product_key": "Handle",
                "units": "SUM(Variant Inventory Qty) per Handle — all locations combined",
                "value": "SUM(Variant Inventory Qty x Variant Price) per variant row at retail",
                "filter": "Status=active AND Published=true",
                "collection_tables": "Positive inventory only (units > 0)",
            },
        })
    except Exception as e:
        shutil.rmtree(job_dir, ignore_errors=True)
        if isinstance(e, HTTPException):
            raise e
        raise HTTPException(500, str(e))


@app.get("/api/download/{job_id}")
async def download_report(job_id: str):
    job = JOBS.get(job_id)
    if not job or not os.path.exists(job["pdf_path"]):
        raise HTTPException(404, "Report not found or expired.")
    safe = re.sub(r'[^a-zA-Z0-9_-]', '_', job["brand"])
    return FileResponse(job["pdf_path"], filename=f"{safe}_Inventory_Report.pdf", media_type="application/pdf")

@app.delete("/api/jobs/{job_id}")
async def delete_job_endpoint(job_id: str):
    job = JOBS.pop(job_id, None)
    if job and os.path.exists(job["job_dir"]):
        shutil.rmtree(job["job_dir"], ignore_errors=True)
        return {"status": "deleted"}
    jd = os.path.join(TEMP_JOBS_DIR, f"job_{job_id}")
    if os.path.exists(jd):
        shutil.rmtree(jd, ignore_errors=True)
        return {"status": "deleted"}
    return JSONResponse(status_code=404, content={"detail": "Not found"})

@app.get("/api/storage-stats")
async def storage_stats():
    return get_server_storage_stats()

@app.post("/api/cleanup")
async def force_cleanup(
    force_all: bool = Query(False),
    clear_classification_cache: bool = Query(False),
):
    if force_all:
        n = len(JOBS)
        JOBS.clear()
        if os.path.exists(TEMP_JOBS_DIR):
            for e in os.listdir(TEMP_JOBS_DIR):
                ep = os.path.join(TEMP_JOBS_DIR, e)
                if os.path.isdir(ep):
                    shutil.rmtree(ep, ignore_errors=True)
        msg = f"{n} jobs wiped."
        if clear_classification_cache and os.path.exists(CACHE_DIR):
            cn = 0
            for f in os.listdir(CACHE_DIR):
                if f.endswith('.json'):
                    try:
                        os.remove(os.path.join(CACHE_DIR, f))
                        cn += 1
                    except Exception:
                        pass
            msg += f" {cn} cached tag classifications cleared."
        return {"status": "success", "message": msg}
    cleanup_old_jobs()
    return {"status": "success", "message": "Expired jobs cleaned."}


if __name__ == "__main__":
    host = os.environ.get("SHOPIFY_REPORT_HOST", "0.0.0.0")
    port = int(os.environ.get("SHOPIFY_REPORT_PORT", "8000"))
    print("=" * 60)
    print("  Shopify Inventory Report Pro v4.7")
    print("     BluesMind API Crash Fix • Heuristic Fallback • Entity Safe")
    print("=" * 60)
    print(f"  Cache: {CACHE_DIR}")
    print(f"  http://{host}:{port}")
    print("=" * 60)
    uvicorn.run(app, host=host, port=port)
