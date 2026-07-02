"""

What this script does:
1. Takes a Shopify product export CSV.
2. Groups rows by product Handle because one product can have many variant rows.
3. Keeps only Status = active and Published = true products.
4. Counts stock from Variant Inventory Qty.
5. Keeps only products where total product inventory is greater than 0.
6. Calculates exact retail inventory value using variant-level formula:
      SUM(Variant Inventory Qty * Variant Price)
7. Detects collection from exact Tags.
8. Creates a complete PDF report plus optional CSV outputs.

Install first:
    pip install pandas reportlab

Run:
    python boosterex_inventory_web_app.py "products_export_1 (25).csv"

Run with custom output name:
    python boosterex_inventory_web_app.py "products_export_1 (25).csv" --output "Inventory_Report.pdf"

If you want only top 5 products per collection in the PDF:
    python boosterex_inventory_web_app.py "products_export_1 (25).csv" --products-per-collection 5
"""

from __future__ import annotations

import argparse
import mimetypes
import os
import re
import unicodedata
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Dict, Iterable, List, Optional

import pandas as pd

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_LEFT, TA_RIGHT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import inch
from reportlab.platypus import (
    BaseDocTemplate,
    Frame,
    Image as RLImage,
    PageBreak,
    PageTemplate,
    Paragraph,
    Spacer,
    Table,
    TableStyle,
)


# =========================
# SETTINGS YOU CAN CHANGE
# =========================
BRAND_NAME = ""
REPORT_TITLE = "Inventory Report"
REPORT_SUBTITLE = "Active + Published products with positive inventory - CSV verified"

# Set to None for complete product detail.
# Set to 5 if you want only top 5 products per collection like the sample report.
DEFAULT_PRODUCTS_PER_COLLECTION = None

# The previous/wrong report numbers. These are shown only as comparison on page 1.
# If you do not want comparison, set PREVIOUS_REPORT_METRICS = None
PREVIOUS_REPORT_METRICS = None

REQUIRED_COLUMNS = [
    "Handle",
    "Title",
    "Tags",
    "Published",
    "Status",
    "Variant Inventory Qty",
    "Variant Price",
]

TYPE_COLUMN_CANDIDATES = [
    "Type",
    "Product Type",
    "Product type",
]

COLLECTION_COLUMN_CANDIDATES = [
    "Collection",
    "Collections",
    "Collection Name",
    "Collection Names",
    "Custom Collection",
    "Custom Collections",
    "Smart Collection",
    "Smart Collections",
    "Manual Collection",
    "Manual Collections",
    "Product Collection",
    "Product Collections",
    "Shopify Collection",
    "Shopify Collections",
]

SIZE_TAGS = {
    "xxs", "xs", "s", "m", "l", "xl", "xxl", "xxxl", "2xl", "3xl", "4xl", "5xl",
    "small", "medium", "large", "extra small", "extra large",
}

NON_COLLECTION_TAGS = {
    "new", "newin", "new in", "new arrival", "new arrivals",
    "restock", "restocked", "new restocked",
    "sale", "discount", "discount sale", "special offer",
    "stitched", "unstitched", "stitch", "unstitch",
    "women", "woman", "men", "man", "girls", "boys", "kids", "ladies",
    "womenswear", "menswear",
    "cotton", "karandi", "lawn", "silk", "chiffon", "organza", "doria", "net",
    "summer", "summers", "winter", "winters",
    "no sync", "hidden", "nada-hidden", "hide", "ppd-elgbl", "ppd-ex",
    "pk active products", "active products",
}

NON_COLLECTION_PATTERNS = [
    r"_",
    r"\bymq\b",
    r"size\s*chart",
    r"sizechart",
    r"\bfabric\b",
    r"cod",
    r"\bcustom\b",
    r"\bflow\b",
    r"\bcart\b",
    r"\bdelivery\b",
    r"\boption\b",
    r"\bnote\b",
    r"\bgrade\b",
    r"\beligible\b",
    r"\bhidden\b",
    r"\bhide\b",
    r"\bsync\b",
    r"\bactive\s+products\b",
    r"\bdiscount\b",
    r"\bsale\s*\d*",
    r"\brestock",
    r"\bflat\s*\d+",
    r"\bnew\s*in\s*\d+",
    r"\bnew\s*arrivals?\s*\d*",
    r"\bnewarrivals?\s*\d*",
    r"\brev[-\s]?\d+%?",
    r"%",
    r"\b\d+%\s*off\b",
    r"\boff\b",
    r"\btoday\b",
    r"\bshirt\b",
    r"\btrouser",
    r"\bpeshwas\b",
    r"\blehnga\b",
    r"\blehenga\b",
    r"\blehngas\b",
    r"\bcholi\b",
    r"\bmaxi\b",
    r"\bsharara\b",
    r"\bpeplum\b",
    r"\bwedding\s+formal",
    r"\bwedding\s+formals",
    r"\bformals\b",
    r"\|",
    r"\bproducts?\s+from\s+sheet\b",
    r"\bcollection\s+products\b",
    r"\blow\s+selling\b",
    r"\bhigh\s+inventory\b",
    r"\bdupatta\b",
    r"\bshawl\s+only\b",
    r"\b\d+\s*-\s*\d+\s*(pkr|rs)?\b",
    r"\b(pkr|rs)\b",
    r"^\d+\s*(pkr|rs)$",
    r"^\d{1,2}[-\s_/]?(jan|feb|mar|march|apr|april|may|jun|june|jul|july|aug|august|sep|sept|september|oct|nov|dec|december)",
    r"^\d{1,2}[-\s_/]?[a-z]+[-\s_/]?\d{2,4}",
    r"^\d{1,2}(st|nd|rd|th)?\s+[a-z]+\s+\d{2,4}",
    r"^\d{1,2}[a-z]{3}\d{2,4}$",
    r"^[a-z]{2,}[-\s_/]?(jan|feb|mar|march|apr|april|may|jun|june|jul|july|aug|august|sep|sept|september|oct|nov|dec|december)[-\s_/]?\d{2,4}$",
    r"^[a-z]{1,4}\s+\d{2,4}$",
    r"^[a-z]{1,4}[-_/][a-z]{1,4}$",
]

COLLECTION_KEYWORDS = {
    "collection", "pret", "lawn", "formal", "formals", "wear", "summer", "winter",
    "eid", "edit", "prints", "printed", "exclusive", "signature", "luxury", "daily",
    "casual", "fancy", "festive", "bridal", "chiffon", "organza", "silk", "doria",
}

MIN_COLLECTION_TAG_SCORE = 25

# Logo file settings.
# Put your logo in the same folder as app.py. Best name: logo.png
# This code also supports logo.jpg, logo.jpeg, logo.webp and common folders like static/assets/images.
LOGO_FILE_NAME = "logo.png"
LOGO_CANDIDATE_NAMES = [
    "logo.png", "Logo.png", "LOGO.png", "logo.PNG",
    "logo.jpg", "Logo.jpg", "LOGO.jpg", "logo.JPG",
    "logo.jpeg", "Logo.jpeg", "LOGO.jpeg", "logo.JPEG",
    "logo.webp", "Logo.webp", "LOGO.webp", "logo.WEBP",
]
LOGO_SEARCH_SUBFOLDERS = ["", "static", "assets", "images"]


# =========================
# HELPER FUNCTIONS
# =========================

def clean_text(value) -> str:
    """Make text safe for ReportLab basic fonts."""
    if pd.isna(value):
        return ""
    text = str(value)
    text = unicodedata.normalize("NFKC", text)
    replacements = {
        "\u2013": "-",
        "\u2014": "-",
        "\u2018": "'",
        "\u2019": "'",
        "\u201c": '"',
        "\u201d": '"',
        "\u00a0": " ",
    }
    for old, new in replacements.items():
        text = text.replace(old, new)
    # Remove control characters that can break PDF rendering
    text = re.sub(r"[\x00-\x08\x0b\x0c\x0e-\x1f]", "", text)
    return text.strip()


def to_number(series: pd.Series) -> pd.Series:
    """Convert messy Shopify numeric strings to numbers."""
    return pd.to_numeric(
        series.astype(str)
        .str.replace(",", "", regex=False)
        .str.replace("Rs", "", regex=False)
        .str.replace("PKR", "", regex=False)
        .str.strip(),
        errors="coerce",
    ).fillna(0)


def first_non_empty(series: pd.Series) -> str:
    """Return first non-empty value from a product group."""
    for value in series:
        if pd.notna(value) and str(value).strip() != "":
            return clean_text(value)
    return ""


def first_existing_non_empty(group: pd.DataFrame, columns: Iterable[str], fallback: str = "") -> str:
    """Return first non-empty value from the first available column in a group."""
    for col in columns:
        if col in group.columns:
            value = first_non_empty(group[col])
            if value:
                return value
    return fallback


def detect_collection_from_columns(group: pd.DataFrame) -> str:
    """Read collection from CSV columns when the export includes them."""
    return first_existing_non_empty(group, COLLECTION_COLUMN_CANDIDATES, fallback="")


def normalise_match_text(value: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", clean_text(value).lower())


def looks_like_product_code(tag: str, handle: str, title: str) -> bool:
    tag_clean = clean_text(tag)
    tag_key = normalise_match_text(tag_clean)
    handle_key = normalise_match_text(handle)
    title_key = normalise_match_text(title)

    if tag_key and tag_key in {handle_key, title_key}:
        return True
    if handle_key and tag_key.startswith(handle_key):
        return True
    if re.fullmatch(r"[A-Z]{1,6}[-_/]?\d+[A-Z0-9-_/]*", tag_clean):
        return True
    if re.fullmatch(r"[A-Z]{2,}[-_/][A-Z0-9-_/]+", tag_clean):
        return True
    return False


def is_collection_tag_candidate(tag: str, handle: str, title: str, disallowed_exact_tags: set[str]) -> bool:
    tag_clean = clean_text(tag)
    if not tag_clean:
        return False

    lower = tag_clean.lower().strip("_- ")
    if lower in disallowed_exact_tags:
        return False
    if lower in SIZE_TAGS or lower in NON_COLLECTION_TAGS:
        return False
    if looks_like_product_code(tag_clean, handle, title):
        return False
    if re.fullmatch(r"[A-Z]{1,3}", tag_clean):
        return False
    if len(tag_clean) <= 1:
        return False
    if tag_clean.isdigit():
        return False
    if re.fullmatch(r"[_\W\d]+", tag_clean):
        return False

    for pattern in NON_COLLECTION_PATTERNS:
        if re.search(pattern, lower, flags=re.IGNORECASE):
            return False
    return True


def score_collection_tag(tag: str, tag_counts: Dict[str, int]) -> float:
    tag_clean = clean_text(tag)
    lower = tag_clean.lower()
    words = re.findall(r"[a-z0-9]+", lower)
    count = tag_counts.get(lower, 1)

    score = 0.0
    score += min(count, 80) * 0.8
    if len(words) >= 2:
        score += 35
    if len(words) >= 3:
        score += 10
    if any(word in COLLECTION_KEYWORDS for word in words):
        score += 45
    if any(keyword in lower for keyword in ["pret", "lawn", "formal", "wear", "edit"]):
        score += 20
    if re.search(r"[a-z]+v\d+$", lower):
        score += 45
    elif re.search(r"[a-z]{4,}\d{2,4}$", lower):
        score += 40
    if len(words) == 1 and count >= 8 and tag_clean[:1].isupper() and not tag_clean.isupper():
        score += 25
    if tag_clean.isupper() and len(words) <= 2:
        score -= 10
    if count <= 1:
        score -= 20
    return score


def pretty_tag_score(tag: str) -> int:
    tag_clean = clean_text(tag)
    if not tag_clean:
        return 0
    if tag_clean.isupper():
        return 1
    if tag_clean.islower():
        return 2
    if re.search(r"[A-Z]", tag_clean):
        return 4
    return 3


def build_canonical_tag_display(tag_display_counts: Dict[str, Dict[str, int]]) -> Dict[str, str]:
    canonical = {}
    for key, display_counts in tag_display_counts.items():
        selected = max(
            display_counts,
            key=lambda tag: (pretty_tag_score(tag), display_counts[tag], len(tag)),
        )
        if selected.isupper() and len(selected) > 3:
            selected = selected.title()
        canonical[key] = selected
    return canonical


def infer_collection_from_tags(
    tags: str,
    handle: str,
    title: str,
    tag_counts: Dict[str, int],
    tag_display: Dict[str, str],
    disallowed_exact_tags: set[str],
) -> str:
    """Pick one best collection-like tag for products without a collection column."""
    candidates = [
        tag for tag in product_tags_for_overview(tags)
        if is_collection_tag_candidate(tag, handle, title, disallowed_exact_tags)
    ]
    if not candidates:
        return "Other / Unmapped"
    best = max(candidates, key=lambda tag: (score_collection_tag(tag, tag_counts), tag_counts.get(tag.lower(), 0), tag))
    if score_collection_tag(best, tag_counts) < MIN_COLLECTION_TAG_SCORE:
        return "Other / Unmapped"
    return tag_display.get(best.lower(), best)


def detect_product_type(group: pd.DataFrame) -> str:
    """Detect Shopify product type universally across any brand."""
    product_type = first_existing_non_empty(group, TYPE_COLUMN_CANDIDATES, fallback="")
    
    if not product_type or product_type.lower() == "no type":
        return "No Type"
        
    # Shopify standard taxonomy often exports as "Apparel & Accessories > Clothing > Shirts"
    # We split by '>' and take the last part so the report looks clean for ANY brand.
    if ">" in product_type:
        product_type = product_type.split(">")[-1].strip()
        
    # Capitalize for a clean PDF look if the raw CSV data is lowercase
    if product_type.islower():
        return product_type.title()
        
    return product_type


def format_int(value) -> str:
    try:
        return f"{int(round(float(value))):,}"
    except Exception:
        return "0"


def format_money(value, compact: bool = True) -> str:
    """Format Pakistani rupees as Rs 13.71 Cr, Rs 75.1L, or Rs 89,760."""
    try:
        amount = float(value)
    except Exception:
        amount = 0.0

    sign = "-" if amount < 0 else ""
    amount_abs = abs(amount)

    if compact:
        if amount_abs >= 10_000_000:  # 1 crore
            return f"{sign}Rs {amount_abs / 10_000_000:.2f} Cr"
        if amount_abs >= 100_000:  # 1 lakh
            return f"{sign}Rs {amount_abs / 100_000:.1f}L"
    return f"{sign}Rs {int(round(amount_abs)):,}"


def format_money_millions(value) -> str:
    """Format money like the reference PDF: Rs. 168.33M or Rs. 780."""
    try:
        amount = float(value)
    except Exception:
        amount = 0.0

    sign = "-" if amount < 0 else ""
    amount_abs = abs(amount)
    if amount_abs >= 1_000_000:
        return f"{sign}Rs. {amount_abs / 1_000_000:.2f}M"
    return f"{sign}Rs. {int(round(amount_abs)):,}"


def format_money_metric(value) -> str:
    """Short money format for narrow metric cards."""
    try:
        amount = float(value)
    except Exception:
        amount = 0.0
    sign = "-" if amount < 0 else ""
    amount_abs = abs(amount)
    if amount_abs >= 1_000_000:
        return f"{sign}Rs.{amount_abs / 1_000_000:.0f}M"
    return format_money_millions(value).replace("Rs. ", "Rs.")


def format_money_crore(value) -> str:
    """Format money in crore for the overall summary."""
    try:
        amount = float(value)
    except Exception:
        amount = 0.0

    sign = "-" if amount < 0 else ""
    return f"{sign}Rs. {abs(amount) / 10_000_000:.2f} crore"


def format_price_range(min_price: float, max_price: float) -> str:
    if round(min_price) == round(max_price):
        return format_money(min_price, compact=False)
    return f"{format_money(min_price, compact=False)} - {format_money(max_price, compact=False)}"


def normalise_bool(value: str) -> str:
    return clean_text(value).lower()


def safe_filename_stem(path: str) -> str:
    return Path(path).stem.replace(" ", "_").replace("(", "").replace(")", "")


def app_base_dir() -> Path:
    """Return the folder where this app.py file lives."""
    return Path(__file__).resolve().parent


def find_logo_file() -> Optional[Path]:
    """Find the logo safely on Windows and Linux."""
    env_logo = os.getenv("BOOSTEREX_LOGO_FILE", "").strip()
    base_dirs = [app_base_dir(), Path.cwd()]
    candidates: List[Path] = []

    if env_logo:
        candidates.append(Path(env_logo).expanduser())

    for base in base_dirs:
        for subfolder in LOGO_SEARCH_SUBFOLDERS:
            folder = base / subfolder if subfolder else base
            for name in LOGO_CANDIDATE_NAMES:
                candidates.append(folder / name)

    seen: set[str] = set()
    for candidate in candidates:
        try:
            resolved = candidate.resolve()
        except Exception:
            continue
        key = str(resolved).lower()
        if key in seen:
            continue
        seen.add(key)
        if resolved.is_file():
            return resolved

    scanned_dirs: set[Path] = set()
    allowed_exts = {".png", ".jpg", ".jpeg", ".webp"}
    for base in base_dirs:
        for subfolder in LOGO_SEARCH_SUBFOLDERS:
            folder = base / subfolder if subfolder else base
            try:
                folder = folder.resolve()
            except Exception:
                continue
            if folder in scanned_dirs or not folder.is_dir():
                continue
            scanned_dirs.add(folder)
            try:
                for item in folder.iterdir():
                    if item.is_file() and item.stem.lower() == "logo" and item.suffix.lower() in allowed_exts:
                        return item
            except Exception:
                continue

    return None


def logo_media_type(path: Path) -> str:
    guessed, _ = mimetypes.guess_type(str(path))
    return guessed or "application/octet-stream"

def build_logo_flowable(max_width: float = 1.10 * inch, max_height: float = 0.70 * inch) -> Optional[RLImage]:
    logo_path = find_logo_file()
    if not logo_path:
        return None

    try:
        logo = RLImage(str(logo_path), width=max_width, height=max_height, kind="proportional")
        logo.hAlign = "LEFT"
        return logo
    except Exception:
        return None


@dataclass
class ReportData:
    products_all: pd.DataFrame
    active_published: pd.DataFrame
    stocked_products: pd.DataFrame
    type_overview: pd.DataFrame
    collection_overview: pd.DataFrame
    tag_overview: pd.DataFrame
    metrics: Dict[str, float]
    audit: Dict[str, float]


# =========================
# DATA PROCESSING
# =========================

def load_and_prepare(csv_path: str) -> pd.DataFrame:
    df = pd.read_csv(csv_path, dtype=str, keep_default_na=False)
    missing = [col for col in REQUIRED_COLUMNS if col not in df.columns]
    if missing:
        raise ValueError(
            "CSV is missing required columns: " + ", ".join(missing)
        )

    for col in ["Handle", "Title", "Tags", "Published", "Status"]:
        df[col] = df[col].apply(clean_text)

    df["_qty"] = to_number(df["Variant Inventory Qty"])
    df["_price"] = to_number(df["Variant Price"])
    df["_row_value"] = df["_qty"] * df["_price"]

    df = df[df["Handle"].astype(str).str.strip() != ""].copy()
    return df


def build_inventory_overview(
    products: pd.DataFrame,
    group_col: str,
    empty_label: str,
) -> pd.DataFrame:
    rows = []
    if products.empty or group_col not in products.columns:
        return pd.DataFrame(
            columns=[group_col, "Products", "With_Stock", "Available_Units", "Current_Value"]
        )

    for name, group in products.groupby(group_col, sort=False, dropna=False):
        label = clean_text(name) or empty_label
        stocked = group[group["Units"] > 0]
        rows.append(
            {
                group_col: label,
                "Products": int(group["Handle"].nunique()),
                "With_Stock": int(stocked["Handle"].nunique()),
                "Available_Units": float(stocked["Units"].sum()),
                "Current_Value": float(stocked["Exact Retail Value"].sum()),
            }
        )

    if not rows:
        return pd.DataFrame(
            columns=[group_col, "Products", "With_Stock", "Available_Units", "Current_Value"]
        )

    return (
        pd.DataFrame(rows)
        .sort_values(["Current_Value", "Products"], ascending=[False, False])
        .reset_index(drop=True)
    )


def product_tags_for_overview(tags: str) -> List[str]:
    tag_list = []
    seen = set()
    for raw_tag in str(tags or "").split(","):
        tag = clean_text(raw_tag)
        if not tag:
            continue
        key = tag.lower()
        if key in seen:
            continue
        seen.add(key)
        tag_list.append(tag)
    return tag_list


def build_tag_overview(products: pd.DataFrame) -> pd.DataFrame:
    columns = ["Tag", "Products", "With_Stock", "Available_Units", "Current_Value"]
    if products.empty or "Tags" not in products.columns:
        return pd.DataFrame(columns=columns)

    tag_rows = []
    for _, product in products.iterrows():
        tags = product_tags_for_overview(product.get("Tags", ""))
        if not tags:
            tags = ["No Tag"]
        for tag in tags:
            tag_rows.append(
                {
                    "Tag": tag,
                    "Handle": product["Handle"],
                    "Units": product["Units"],
                    "Exact Retail Value": product["Exact Retail Value"],
                }
            )

    if not tag_rows:
        return pd.DataFrame(columns=columns)

    expanded = pd.DataFrame(tag_rows)
    rows = []
    for tag, group in expanded.groupby("Tag", sort=False, dropna=False):
        stocked = group[group["Units"] > 0]
        rows.append(
            {
                "Tag": clean_text(tag) or "No Tag",
                "Products": int(group["Handle"].nunique()),
                "With_Stock": int(stocked["Handle"].nunique()),
                "Available_Units": float(stocked["Units"].sum()),
                "Current_Value": float(stocked["Exact Retail Value"].sum()),
            }
        )

    return (
        pd.DataFrame(rows)
        .sort_values(["Current_Value", "Products"], ascending=[False, False])
        .reset_index(drop=True)
    )


def build_report_data(csv_path: str) -> ReportData:
    df = load_and_prepare(csv_path)

    product_rows = []
    for handle, group in df.groupby("Handle", sort=False):
        title = first_non_empty(group["Title"])
        tags = first_non_empty(group["Tags"])
        vendor = first_non_empty(group["Vendor"]) if "Vendor" in group.columns else ""
        published = first_non_empty(group["Published"])
        status = first_non_empty(group["Status"])
        product_type = detect_product_type(group)

        qty_total = float(group["_qty"].sum())
        value_exact = float(group["_row_value"].sum())

        positive_price_rows = group[group["_price"] > 0]
        if not positive_price_rows.empty:
            min_price = float(positive_price_rows["_price"].min())
            max_price = float(positive_price_rows["_price"].max())
            first_price = float(positive_price_rows["_price"].iloc[0])
        else:
            min_price = max_price = first_price = 0.0

        product_rows.append(
            {
                "Handle": clean_text(handle),
                "Title": title,
                "Tags": tags,
                "Vendor": vendor,
                "Type": product_type,
                "Collection": detect_collection_from_columns(group),
                "Status": status,
                "Published": published,
                "Variant Rows": int(len(group)),
                "Units": qty_total,
                "Positive Variant Units": float(group.loc[group["_qty"] > 0, "_qty"].sum()),
                "Negative Variant Units": float(group.loc[group["_qty"] < 0, "_qty"].sum()),
                "Min Price": min_price,
                "Max Price": max_price,
                "First Price": first_price,
                "Price Display": format_price_range(min_price, max_price),
                "Exact Retail Value": value_exact,
                "Simple Retail Value": qty_total * first_price,
                "Different Variant Prices": bool(round(min_price, 2) != round(max_price, 2)),
            }
        )

    products = pd.DataFrame(product_rows)

    active_published = products[
        (products["Status"].apply(normalise_bool) == "active")
        & (products["Published"].apply(normalise_bool) == "true")
    ].copy()

    disallowed_exact_tags: set[str] = set()
    for value in active_published.get("Vendor", pd.Series(dtype=str)):
        value = clean_text(value).lower()
        if value:
            disallowed_exact_tags.add(value)
    for value in active_published.get("Type", pd.Series(dtype=str)):
        value = clean_text(value).lower()
        if value and value != "no type":
            disallowed_exact_tags.add(value)

    tag_counts: Dict[str, int] = {}
    tag_display_counts: Dict[str, Dict[str, int]] = {}
    for tags in active_published["Tags"]:
        for tag in product_tags_for_overview(tags):
            key = tag.lower()
            tag_counts[key] = tag_counts.get(key, 0) + 1
            if key not in tag_display_counts:
                tag_display_counts[key] = {}
            tag_display_counts[key][tag] = tag_display_counts[key].get(tag, 0) + 1

    tag_display = build_canonical_tag_display(tag_display_counts)

    active_published["Collection"] = active_published.apply(
        lambda row: row["Collection"] if clean_text(row["Collection"]) else infer_collection_from_tags(
            row["Tags"],
            row["Handle"],
            row["Title"],
            tag_counts,
            tag_display,
            disallowed_exact_tags,
        ),
        axis=1,
    )

    stocked = active_published[active_published["Units"] > 0].copy()

    type_overview = build_inventory_overview(active_published, "Type", "No Type")
    collection_overview = build_inventory_overview(active_published, "Collection", "Other")
    tag_overview = build_tag_overview(active_published)

    metrics = {
        "Active + Published": int(active_published["Handle"].nunique()),
        "Products with stock": int(stocked["Handle"].nunique()),
        "Out of stock": int(active_published["Handle"].nunique() - stocked["Handle"].nunique()),
        "Available units": float(stocked["Units"].sum()),
        "Inventory value": float(stocked["Exact Retail Value"].sum()),
        "Simple inventory value": float(stocked["Simple Retail Value"].sum()),
    }

    audit = {
        "total_csv_rows": int(len(df)),
        "total_handles": int(products["Handle"].nunique()),
        "active_published_handles": metrics["Active + Published"],
        "stocked_handles": metrics["Products with stock"],
        "out_of_stock_handles": metrics["Out of stock"],
        "negative_inventory_variant_rows": int((df["_qty"] < 0).sum()),
        "negative_inventory_units_total": float(df.loc[df["_qty"] < 0, "_qty"].sum()),
        "products_with_different_variant_prices": int(stocked["Different Variant Prices"].sum()),
    }

    return ReportData(
        products_all=products,
        active_published=active_published,
        stocked_products=stocked,
        type_overview=type_overview,
        collection_overview=collection_overview,
        tag_overview=tag_overview,
        metrics=metrics,
        audit=audit,
    )


# =========================
# PDF STYLES
# =========================

def make_styles():
    styles = getSampleStyleSheet()
    styles.add(
        ParagraphStyle(
            name="ReportTitle",
            parent=styles["Title"],
            fontName="Helvetica-Bold",
            fontSize=24,
            leading=29,
            textColor=colors.HexColor("#123D22"),
            spaceAfter=8,
        )
    )
    styles.add(
        ParagraphStyle(
            name="Subtitle",
            parent=styles["BodyText"],
            fontName="Helvetica",
            fontSize=10.5,
            leading=15,
            textColor=colors.HexColor("#557A5F"),
            spaceAfter=10,
        )
    )
    styles.add(
        ParagraphStyle(
            name="SectionTitle",
            parent=styles["Heading2"],
            fontName="Helvetica-Bold",
            fontSize=13,
            leading=17,
            textColor=colors.HexColor("#123D22"),
            spaceBefore=12,
            spaceAfter=7,
        )
    )
    styles.add(
        ParagraphStyle(
            name="Small",
            parent=styles["BodyText"],
            fontName="Helvetica",
            fontSize=8,
            leading=10,
            textColor=colors.HexColor("#557A5F"),
        )
    )
    styles.add(
        ParagraphStyle(
            name="Tiny",
            parent=styles["BodyText"],
            fontName="Helvetica",
            fontSize=7,
            leading=8.5,
            textColor=colors.HexColor("#1F3A29"),
        )
    )
    styles.add(
        ParagraphStyle(
            name="TinyBold",
            parent=styles["BodyText"],
            fontName="Helvetica-Bold",
            fontSize=7,
            leading=8.5,
            textColor=colors.HexColor("#123D22"),
        )
    )
    styles.add(
        ParagraphStyle(
            name="MetricLabel",
            parent=styles["BodyText"],
            fontName="Helvetica",
            fontSize=7.5,
            leading=9,
            textColor=colors.HexColor("#557A5F"),
            alignment=TA_LEFT,
        )
    )
    styles.add(
        ParagraphStyle(
            name="MetricValue",
            parent=styles["BodyText"],
            fontName="Helvetica-Bold",
            fontSize=16,
            leading=18,
            textColor=colors.HexColor("#123D22"),
            alignment=TA_LEFT,
        )
    )
    return styles


def p(text: str, style: ParagraphStyle) -> Paragraph:
    return Paragraph(clean_text(text), style)


def table_style(header_bg="#EAF7EE", grid="#CFEAD7") -> TableStyle:
    return TableStyle(
        [
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor(header_bg)),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.HexColor("#557A5F")),
            ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
            ("FONTSIZE", (0, 0), (-1, 0), 7.5),
            ("BOTTOMPADDING", (0, 0), (-1, 0), 7),
            ("TOPPADDING", (0, 0), (-1, 0), 7),
            ("FONTNAME", (0, 1), (-1, -1), "Helvetica"),
            ("FONTSIZE", (0, 1), (-1, -1), 7.3),
            ("TEXTCOLOR", (0, 1), (-1, -1), colors.HexColor("#123D22")),
            ("BOTTOMPADDING", (0, 1), (-1, -1), 5),
            ("TOPPADDING", (0, 1), (-1, -1), 5),
            ("LINEBELOW", (0, 0), (-1, -1), 0.4, colors.HexColor(grid)),
            ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ]
    )


def add_number_alignment(style: TableStyle, numeric_cols: Iterable[int]) -> TableStyle:
    for col in numeric_cols:
        style.add("ALIGN", (col, 1), (col, -1), "RIGHT")
        style.add("ALIGN", (col, 0), (col, 0), "RIGHT")
    return style


# =========================
# PDF REPORT BUILDING
# =========================

def header_footer(canvas, doc):
    canvas.saveState()
    width, height = A4
    canvas.setFont("Helvetica", 7)
    canvas.setFillColor(colors.HexColor("#557A5F"))
    canvas.drawString(doc.leftMargin, 0.35 * inch, "Inventory Report")
    canvas.drawRightString(width - doc.rightMargin, 0.35 * inch, f"Page {doc.page}")
    canvas.restoreState()


def build_metric_cards(report: ReportData, styles) -> Table:
    metrics = report.metrics
    cards = [
        ("Active + published", format_int(metrics["Active + Published"]), "Total products"),
        ("Products with stock", format_int(metrics["Products with stock"]), "Positive inventory"),
        ("Out of stock", format_int(metrics["Out of stock"]), "Zero or negative total"),
        ("Available units", format_int(metrics["Available units"]), "All variants combined"),
        ("Inventory value", format_money_metric(metrics["Inventory value"]), "Variant-level retail"),
    ]

    row = []
    for label, value, sub in cards:
        cell = [
            p(label, styles["MetricLabel"]),
            p(value, styles["MetricValue"]),
            p(sub, styles["MetricLabel"]),
        ]
        row.append(cell)

    tbl = Table([row], colWidths=[1.38 * inch] * 5)
    tbl.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (-1, -1), colors.HexColor("#F6FCF8")),
                ("BOX", (0, 0), (-1, -1), 0.5, colors.HexColor("#CFEAD7")),
                ("INNERGRID", (0, 0), (-1, -1), 0.5, colors.HexColor("#DDF2E4")),
                ("VALIGN", (0, 0), (-1, -1), "TOP"),
                ("TOPPADDING", (0, 0), (-1, -1), 9),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 9),
                ("LEFTPADDING", (0, 0), (-1, -1), 8),
                ("RIGHTPADDING", (0, 0), (-1, -1), 8),
            ]
        )
    )
    return tbl


def build_pill_row(styles) -> Table:
    pills = [
        p("Active + Published only", styles["TinyBold"]),
        p("Positive inventory only", styles["TinyBold"]),
        p("All variant rows combined", styles["TinyBold"]),
        p("Exact CSV calculation", styles["TinyBold"]),
    ]
    tbl = Table([pills], colWidths=[1.72 * inch] * 4)
    tbl.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (-1, -1), colors.HexColor("#EAF7EE")),
                ("ALIGN", (0, 0), (-1, -1), "CENTER"),
                ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                ("TOPPADDING", (0, 0), (-1, -1), 7),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 7),
                ("BOX", (0, 0), (-1, -1), 0.3, colors.HexColor("#CFEAD7")),
            ]
        )
    )
    return tbl


def build_comparison_table(report: ReportData, styles) -> Optional[Table]:
    if not PREVIOUS_REPORT_METRICS:
        return None

    current = report.metrics
    rows = [["Metric", "Previous Report", "Correct CSV", "Difference"]]

    ordered = [
        "Active + Published",
        "Products with stock",
        "Out of stock",
        "Available units",
        "Inventory value",
    ]

    for key in ordered:
        prev = PREVIOUS_REPORT_METRICS.get(key, 0)
        curr = current.get(key, 0)
        diff = curr - prev
        if "value" in key.lower():
            rows.append([key, format_money(prev), format_money(curr), format_money(diff)])
        else:
            rows.append([key, format_int(prev), format_int(curr), format_int(diff)])

    tbl = Table(rows, colWidths=[2.0 * inch, 1.55 * inch, 1.55 * inch, 1.55 * inch])
    style = table_style()
    style = add_number_alignment(style, [1, 2, 3])
    tbl.setStyle(style)
    return tbl


def build_rules_table(styles) -> Table:
    rows = [
        ["Step", "Rule used in this inventory report"],
        ["Product key", "One product = one unique Handle. Rows are variants/sizes."],
        ["Product filter", "Keep only Status = active and Published = true."],
        ["Stock filter", "After grouping by Handle, keep only products where total Units > 0."],
        ["Available units", "Sum Variant Inventory Qty across all variant rows for included products."],
        ["Retail value", "Exact formula: SUM(Variant Inventory Qty * Variant Price)."],
        ["Collection", "Read from collection columns if the CSV includes them; otherwise shown as Other / Unmapped."],
    ]
    tbl = Table(rows, colWidths=[1.55 * inch, 5.15 * inch])
    tbl.setStyle(table_style())
    return tbl


def build_overall_summary_table(report: ReportData, styles) -> Table:
    metrics = report.metrics
    rows = [
        ["Metric", "Value"],
        ["Active + Published Products", format_int(metrics["Active + Published"])],
        ["Products With Stock", format_int(metrics["Products with stock"])],
        ["Out of Stock Products", format_int(metrics["Out of stock"])],
        ["Available Units", f"{format_int(metrics['Available units'])} pcs"],
        ["Current Inventory Value", format_money_millions(metrics["Inventory value"])],
        ["Current Value in Crore", format_money_crore(metrics["Inventory value"])],
    ]
    tbl = Table(rows, colWidths=[3.6 * inch, 2.4 * inch])
    style = table_style()
    style = add_number_alignment(style, [1])
    tbl.setStyle(style)
    return tbl


def build_type_table(report: ReportData, styles) -> Table:
    rows = [["Type", "Products", "With Stock", "Available Units", "Current Value"]]
    for _, row in report.type_overview.iterrows():
        rows.append(
            [
                p(row["Type"], styles["Tiny"]),
                format_int(row["Products"]),
                format_int(row["With_Stock"]),
                format_int(row["Available_Units"]),
                format_money_millions(row["Current_Value"]),
            ]
        )
    rows.append(
        [
            p("Total", styles["TinyBold"]),
            format_int(report.metrics["Active + Published"]),
            format_int(report.metrics["Products with stock"]),
            format_int(report.metrics["Available units"]),
            format_money_millions(report.metrics["Inventory value"]),
        ]
    )

    tbl = Table(rows, colWidths=[2.75 * inch, 0.8 * inch, 0.9 * inch, 1.25 * inch, 1.35 * inch], repeatRows=1)
    style = table_style()
    style = add_number_alignment(style, [1, 2, 3, 4])
    last_row = len(rows) - 1
    style.add("FONTNAME", (0, last_row), (-1, last_row), "Helvetica-Bold")
    style.add("BACKGROUND", (0, last_row), (-1, last_row), colors.HexColor("#EAF7EE"))
    tbl.setStyle(style)
    return tbl


def build_collection_table(report: ReportData, styles) -> Table:
    rows = [["Collection", "Products", "With Stock", "Available Units", "Current Value"]]
    for _, row in report.collection_overview.iterrows():
        rows.append(
            [
                p(row["Collection"], styles["Tiny"]),
                format_int(row["Products"]),
                format_int(row["With_Stock"]),
                format_int(row["Available_Units"]),
                format_money_millions(row["Current_Value"]),
            ]
        )
    rows.append(
        [
            p("Total", styles["TinyBold"]),
            format_int(report.metrics["Active + Published"]),
            format_int(report.metrics["Products with stock"]),
            format_int(report.metrics["Available units"]),
            format_money_millions(report.metrics["Inventory value"]),
        ]
    )

    tbl = Table(rows, colWidths=[2.75 * inch, 0.8 * inch, 0.9 * inch, 1.25 * inch, 1.35 * inch], repeatRows=1)
    style = table_style()
    style = add_number_alignment(style, [1, 2, 3, 4])
    last_row = len(rows) - 1
    style.add("FONTNAME", (0, last_row), (-1, last_row), "Helvetica-Bold")
    style.add("BACKGROUND", (0, last_row), (-1, last_row), colors.HexColor("#EAF7EE"))
    tbl.setStyle(style)
    return tbl


def build_tag_collection_table(report: ReportData, styles) -> Table:
    rows = [["Tag", "Products", "With Stock", "Available Units", "Current Value"]]
    for _, row in report.tag_overview.iterrows():
        rows.append(
            [
                p(row["Tag"], styles["Tiny"]),
                format_int(row["Products"]),
                format_int(row["With_Stock"]),
                format_int(row["Available_Units"]),
                format_money_millions(row["Current_Value"]),
            ]
        )
    rows.append(
        [
            p("Unique Total", styles["TinyBold"]),
            format_int(report.metrics["Active + Published"]),
            format_int(report.metrics["Products with stock"]),
            format_int(report.metrics["Available units"]),
            format_money_millions(report.metrics["Inventory value"]),
        ]
    )

    tbl = Table(rows, colWidths=[2.75 * inch, 0.8 * inch, 0.9 * inch, 1.25 * inch, 1.35 * inch], repeatRows=1)
    style = table_style()
    style = add_number_alignment(style, [1, 2, 3, 4])
    last_row = len(rows) - 1
    style.add("FONTNAME", (0, last_row), (-1, last_row), "Helvetica-Bold")
    style.add("BACKGROUND", (0, last_row), (-1, last_row), colors.HexColor("#EAF7EE"))
    tbl.setStyle(style)
    return tbl


def build_audit_table(report: ReportData, csv_path: str, styles) -> Table:
    audit = report.audit
    rows = [
        ["Audit Check", "Result"],
        ["Source CSV", os.path.basename(csv_path)],
        ["CSV rows read", format_int(audit["total_csv_rows"])],
        ["Unique product handles in CSV", format_int(audit["total_handles"])],
        ["Active + published products", format_int(audit["active_published_handles"])],
        ["Products with positive total stock", format_int(audit["stocked_handles"])],
        ["Out-of-stock active + published products", format_int(audit["out_of_stock_handles"])],
        ["Negative inventory variant rows", format_int(audit["negative_inventory_variant_rows"])],
        ["Total negative inventory units", format_int(audit["negative_inventory_units_total"])],
        ["Stocked products with different variant prices", format_int(audit["products_with_different_variant_prices"])],
        ["Report generated at", datetime.now().strftime("%Y-%m-%d %H:%M")],
    ]
    tbl = Table(rows, colWidths=[2.8 * inch, 3.9 * inch])
    tbl.setStyle(table_style())
    return tbl


def product_rows_for_pdf(products: pd.DataFrame, styles) -> List[List]:
    rows = [["Product", "Units", "Price / Range", "Exact Value", "Simple Value"]]
    for _, row in products.iterrows():
        rows.append(
            [
                p(row["Title"], styles["Tiny"]),
                format_int(row["Units"]),
                row["Price Display"],
                format_money(row["Exact Retail Value"]),
                format_money(row["Simple Retail Value"]),
            ]
        )
    return rows


def build_products_table(products: pd.DataFrame, styles) -> Table:
    rows = product_rows_for_pdf(products, styles)
    tbl = Table(
        rows,
        colWidths=[2.8 * inch, 0.75 * inch, 1.35 * inch, 1.05 * inch, 1.05 * inch],
        repeatRows=1,
    )
    style = table_style()
    style = add_number_alignment(style, [1, 2, 3, 4])
    tbl.setStyle(style)
    return tbl


def make_pdf(
    csv_path: str,
    output_pdf: str,
    products_per_collection: Optional[int] = DEFAULT_PRODUCTS_PER_COLLECTION,
    make_csv_outputs: bool = True,
) -> ReportData:
    report = build_report_data(csv_path)
    styles = make_styles()

    output_pdf = str(output_pdf)
    output_dir = Path(output_pdf).resolve().parent
    output_dir.mkdir(parents=True, exist_ok=True)

    doc = BaseDocTemplate(
        output_pdf,
        pagesize=A4,
        leftMargin=0.48 * inch,
        rightMargin=0.48 * inch,
        topMargin=0.48 * inch,
        bottomMargin=0.55 * inch,
        title=REPORT_TITLE,
        author="Generated by Python",
    )

    frame = Frame(
        doc.leftMargin,
        doc.bottomMargin,
        doc.width,
        doc.height,
        id="normal",
    )
    doc.addPageTemplates([PageTemplate(id="main", frames=[frame], onPage=header_footer)])

    story = []

    # Page 1: summary
    logo = build_logo_flowable()
    if logo is not None:
        story.append(logo)
        story.append(Spacer(1, 8))

    story.append(p("INVENTORY REPORT", styles["ReportTitle"]))
    story.append(p(REPORT_SUBTITLE, styles["Subtitle"]))
    story.append(build_pill_row(styles))
    story.append(Spacer(1, 13))
    story.append(build_metric_cards(report, styles))

    comparison = build_comparison_table(report, styles)
    if comparison is not None:
        story.append(Spacer(1, 12))
        story.append(p("Previous Report vs Correct CSV", styles["SectionTitle"]))
        story.append(comparison)

    story.append(Spacer(1, 8))
    story.append(p("Overall Summary", styles["SectionTitle"]))
    story.append(build_overall_summary_table(report, styles))

    story.append(Spacer(1, 8))
    story.append(p("Type-wise Inventory", styles["SectionTitle"]))
    story.append(build_type_table(report, styles))

    story.append(PageBreak())
    story.append(p("Collection-wise Inventory", styles["SectionTitle"]))
    story.append(build_collection_table(report, styles))

    # ==========================================
    # SESSION 1: TYPE-WISE PRODUCT DETAIL
    # ==========================================
    story.append(PageBreak())
    if products_per_collection is None:
        type_heading = "Product Detail Session 1: Grouped by Product Type"
    else:
        type_heading = f"Top {products_per_collection} Products by Type - By Exact Retail Value"

    story.append(p(type_heading, styles["ReportTitle"]))
    story.append(p("Extracted explicitly from the Shopify 'Type' or 'Product Type' columns.", styles["Small"]))
    story.append(Spacer(1, 8))

    type_order = report.type_overview[report.type_overview["With_Stock"] > 0]["Type"].tolist()
    for idx, p_type in enumerate(type_order):
        products = report.stocked_products[report.stocked_products["Type"] == p_type].copy()
        products = products.sort_values("Exact Retail Value", ascending=False)
        if products_per_collection is not None:
            products = products.head(products_per_collection)

        type_row = report.type_overview[report.type_overview["Type"] == p_type].iloc[0]
        heading_text = (
            f"Type: {p_type} - {format_money(type_row['Current_Value'])} - "
            f"{format_int(type_row['Available_Units'])} units - "
            f"{format_int(type_row['With_Stock'])} stocked products"
        )
        story.append(p(heading_text, styles["SectionTitle"]))
        story.append(build_products_table(products, styles))
        story.append(Spacer(1, 10))

    # ==========================================
    # SESSION 2: TAG-WISE COLLECTION DETAIL
    # ==========================================
    story.append(PageBreak())
    if products_per_collection is None:
        coll_heading = "Product Detail Session 2: Grouped by Tag-Based Collection"
    else:
        coll_heading = f"Top {products_per_collection} Products by Tag Collection - By Exact Retail Value"

    story.append(p(coll_heading, styles["ReportTitle"]))
    story.append(p("Extracted by smart-scanning and filtering the Shopify 'Tags' column.", styles["Small"]))
    story.append(Spacer(1, 8))

    collection_order = report.collection_overview[report.collection_overview["With_Stock"] > 0]["Collection"].tolist()
    for idx, collection in enumerate(collection_order):
        products = report.stocked_products[report.stocked_products["Collection"] == collection].copy()
        products = products.sort_values("Exact Retail Value", ascending=False)
        if products_per_collection is not None:
            products = products.head(products_per_collection)

        coll_row = report.collection_overview[report.collection_overview["Collection"] == collection].iloc[0]
        heading_text = (
            f"Collection: {collection} - {format_money(coll_row['Current_Value'])} - "
            f"{format_int(coll_row['Available_Units'])} units - "
            f"{format_int(coll_row['With_Stock'])} stocked products"
        )
        story.append(p(heading_text, styles["SectionTitle"]))
        story.append(build_products_table(products, styles))
        story.append(Spacer(1, 10))

    story.append(PageBreak())

    # Audit page
    story.append(p("CSV Audit Notes", styles["SectionTitle"]))
    story.append(build_audit_table(report, csv_path, styles))
    story.append(Spacer(1, 10))
    story.append(
        p(
            "Important: This report uses the CSV only. If Shopify admin stock changes after the export, the PDF will not update until a fresh CSV is exported and this script is run again.",
            styles["Small"],
        )
    )
    story.append(Spacer(1, 8))
    story.append(
        p(
            "Exact retail value is more accurate than using one product price because some products can have different prices across variants/sizes.",
            styles["Small"],
        )
    )

    doc.build(story)

    if make_csv_outputs:
        base = Path(output_pdf).with_suffix("")
        product_csv = str(base) + "_Product_Detail.csv"
        collection_csv = str(base) + "_Collection_Overview.csv"
        tag_csv = str(base) + "_Tag_Collection_Overview.csv"

        product_export = report.stocked_products.copy()
        product_export = product_export.sort_values(["Collection", "Exact Retail Value"], ascending=[True, False])
        product_export.to_csv(product_csv, index=False)

        report.collection_overview.to_csv(collection_csv, index=False)
        report.tag_overview.to_csv(tag_csv, index=False)

        print(f"Product detail CSV saved: {product_csv}")
        print(f"Collection overview CSV saved: {collection_csv}")
        print(f"Tag collection overview CSV saved: {tag_csv}")

    return report

# =========================
# FASTAPI WEB FRONTEND
# =========================

import asyncio
import uuid
from urllib.parse import quote

try:
    import uvicorn
    from fastapi import FastAPI, File, HTTPException, UploadFile
    from fastapi.responses import FileResponse, HTMLResponse, JSONResponse
    from starlette.background import BackgroundTask
except ImportError as exc:
    raise SystemExit(
        "Missing web packages. Install them first:\n"
        "pip install fastapi uvicorn python-multipart pandas reportlab"
    ) from exc


APP_TITLE = "BOOSTEREX Inventory Report Generator"
WEB_STORAGE_DIR = Path(__file__).resolve().parent / "_boosterex_inventory_temp"
UPLOAD_DIR = WEB_STORAGE_DIR / "uploads"
REPORT_DIR = WEB_STORAGE_DIR / "reports"
MAX_UPLOAD_MB = 100
MAX_UPLOAD_BYTES = MAX_UPLOAD_MB * 1024 * 1024

app = FastAPI(title=APP_TITLE)


@app.get("/logo.png")
async def serve_logo_png():
    return await serve_logo_asset()


@app.get("/assets/logo")
async def serve_logo_asset():
    logo_path = find_logo_file()
    if not logo_path:
        raise HTTPException(
            status_code=404,
            detail=(
                "Logo file not found. Put logo.png in the same folder as app.py, "
                "or put logo.png/logo.jpg inside static, assets, or images folder."
            ),
        )
    return FileResponse(str(logo_path), media_type=logo_media_type(logo_path))


@app.get("/debug/logo")
async def debug_logo():
    logo_path = find_logo_file()
    return JSONResponse(
        {
            "found": bool(logo_path),
            "path": str(logo_path) if logo_path else None,
            "app_folder": str(app_base_dir()),
            "current_working_folder": str(Path.cwd()),
            "accepted_names": LOGO_CANDIDATE_NAMES,
            "accepted_folders": ["same folder as app.py", "static", "assets", "images"],
        }
    )

INDEX_HTML = """
<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>BOOSTEREX Inventory Report Generator</title>
  <style>
    :root {
      --bg: #F4FBF6;
      --card: rgba(255, 255, 255, 0.96);
      --text: #123D22;
      --muted: #557A5F;
      --line: #CFEAD7;
      --accent: #2E7D32;
      --accent-2: #8FD19E;
      --success: #2E7D32;
      --danger: #aa2424;
      --shadow: 0 24px 70px rgba(46, 125, 50, 0.13);
      --radius: 28px;
    }

    * { box-sizing: border-box; }

    body {
      margin: 0;
      min-height: 100vh;
      font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
      background:
        radial-gradient(circle at 12% 5%, rgba(143, 209, 158, 0.34), transparent 30%),
        radial-gradient(circle at 88% 8%, rgba(46, 125, 50, 0.12), transparent 28%),
        linear-gradient(135deg, #FFFFFF 0%, var(--bg) 52%, #EAF7EE 100%);
      color: var(--text);
      padding: 34px 18px;
    }

    .shell {
      width: min(1120px, 100%);
      margin: 0 auto;
    }

    .hero {
      display: grid;
      grid-template-columns: 1.12fr 0.88fr;
      gap: 22px;
      align-items: stretch;
    }

    .panel {
      background: var(--card);
      border: 1px solid rgba(255,255,255,0.65);
      box-shadow: var(--shadow);
      border-radius: var(--radius);
      backdrop-filter: blur(16px);
      overflow: hidden;
    }

    .intro {
      padding: 42px;
      position: relative;
      min-height: 520px;
      display: flex;
      flex-direction: column;
      justify-content: space-between;
    }

    .brand-row {
      display: flex;
      align-items: center;
      justify-content: space-between;
      gap: 14px;
      margin-bottom: 44px;
    }

    .logo {
      display: inline-flex;
      align-items: center;
      justify-content: center;
      width: 56px;
      height: 56px;
      min-width: 56px;
      border-radius: 18px;
      background: var(--accent);
      color: white;
      font-size: 22px;
      font-weight: 900;
      line-height: 1;
      letter-spacing: 0.08em;
      overflow: hidden;
    }

    .logo img {
      width: 100%;
      height: 100%;
      object-fit: contain;
      display: block;
      background: white;
      padding: 5px;
    }

    .tag {
      border: 1px solid var(--line);
      border-radius: 999px;
      padding: 9px 14px;
      color: var(--muted);
      background: rgba(255,255,255,0.58);
      font-size: 13px;
      font-weight: 650;
    }

    h1 {
      margin: 0;
      font-size: clamp(36px, 5.4vw, 64px);
      line-height: 0.94;
      letter-spacing: -0.055em;
    }

    .lead {
      margin: 22px 0 0;
      max-width: 650px;
      color: var(--muted);
      font-size: 17px;
      line-height: 1.65;
    }

    .steps {
      display: grid;
      grid-template-columns: repeat(3, 1fr);
      gap: 10px;
      margin-top: 34px;
    }

    .step {
      border: 1px solid var(--line);
      background: rgba(255,255,255,0.58);
      border-radius: 18px;
      padding: 14px;
      min-height: 92px;
    }

    .step b {
      display: block;
      font-size: 13px;
      margin-bottom: 8px;
    }

    .step span {
      color: var(--muted);
      font-size: 12px;
      line-height: 1.45;
    }

    .upload-panel {
      padding: 28px;
    }

    .upload-title {
      margin: 0 0 8px;
      font-size: 25px;
      letter-spacing: -0.03em;
    }

    .upload-sub {
      margin: 0 0 22px;
      color: var(--muted);
      line-height: 1.5;
      font-size: 14px;
    }

    .dropzone {
      border: 2px dashed #B7E4C7;
      border-radius: 24px;
      min-height: 214px;
      background: rgba(255,255,255,0.55);
      display: flex;
      align-items: center;
      justify-content: center;
      text-align: center;
      padding: 24px;
      cursor: pointer;
      transition: 180ms ease;
    }

    .dropzone:hover,
    .dropzone.dragover {
      transform: translateY(-2px);
      border-color: var(--accent-2);
      background: rgba(255,255,255,0.88);
    }

    .drop-icon {
      width: 62px;
      height: 62px;
      border-radius: 22px;
      margin: 0 auto 16px;
      display: grid;
      place-items: center;
      background: var(--accent);
      color: white;
      font-size: 28px;
    }

    .drop-main {
      font-size: 16px;
      font-weight: 800;
      margin: 0 0 6px;
    }

    .drop-small {
      color: var(--muted);
      font-size: 13px;
      margin: 0;
    }

    input[type="file"] { display: none; }

    .file-card {
      margin-top: 14px;
      border: 1px solid var(--line);
      border-radius: 18px;
      padding: 14px 16px;
      display: none;
      align-items: center;
      justify-content: space-between;
      gap: 12px;
      background: rgba(255,255,255,0.68);
    }

    .file-name {
      font-weight: 800;
      font-size: 14px;
      word-break: break-word;
    }

    .file-size {
      color: var(--muted);
      font-size: 12px;
      margin-top: 4px;
    }

    .btn-row {
      display: grid;
      grid-template-columns: 1fr;
      gap: 10px;
      margin-top: 18px;
    }

    button, .download-btn {
      border: 0;
      border-radius: 17px;
      padding: 15px 18px;
      background: var(--accent);
      color: white;
      font-weight: 900;
      cursor: pointer;
      font-size: 15px;
      text-decoration: none;
      text-align: center;
      display: inline-flex;
      justify-content: center;
      align-items: center;
      gap: 10px;
      transition: 160ms ease;
    }

    button:hover, .download-btn:hover { transform: translateY(-1px); }
    button:disabled { opacity: 0.55; cursor: not-allowed; transform: none; }

    .ghost {
      background: transparent;
      color: var(--accent);
      border: 1px solid var(--line);
    }

    .status {
      margin-top: 16px;
      padding: 14px 16px;
      border-radius: 18px;
      display: none;
      line-height: 1.5;
      font-size: 14px;
      border: 1px solid var(--line);
      background: rgba(255,255,255,0.7);
    }

    .status.success { display: block; color: var(--success); border-color: rgba(23,109,58,0.25); }
    .status.error { display: block; color: var(--danger); border-color: rgba(170,36,36,0.25); }
    .status.info { display: block; color: var(--accent); }

    .loader {
      display: none;
      height: 8px;
      border-radius: 999px;
      background: #DDF2E4;
      overflow: hidden;
      margin-top: 16px;
    }

    .loader div {
      width: 44%;
      height: 100%;
      background: var(--accent);
      border-radius: inherit;
      animation: slide 1.1s infinite ease-in-out;
    }

    @keyframes slide {
      0% { transform: translateX(-110%); }
      100% { transform: translateX(260%); }
    }

    .result {
      display: none;
      margin-top: 18px;
      border-radius: 22px;
      padding: 18px;
      border: 1px solid rgba(23,109,58,0.18);
      background: rgba(234, 247, 238, 0.88);
    }

    .result h3 {
      margin: 0 0 12px;
      font-size: 18px;
    }

    .metrics {
      display: grid;
      grid-template-columns: repeat(2, 1fr);
      gap: 10px;
      margin-bottom: 14px;
    }

    .metric {
      border-radius: 16px;
      background: rgba(255,255,255,0.78);
      border: 1px solid rgba(23,109,58,0.11);
      padding: 12px;
    }

    .metric span {
      display: block;
      color: var(--muted);
      font-size: 11px;
      font-weight: 800;
      text-transform: uppercase;
      letter-spacing: 0.04em;
      margin-bottom: 6px;
    }

    .metric b {
      font-size: 18px;
      letter-spacing: -0.02em;
    }

    .note {
      margin-top: 14px;
      color: var(--muted);
      font-size: 12px;
      line-height: 1.5;
    }

    .footer-note {
      margin-top: 16px;
      color: var(--muted);
      text-align: center;
      font-size: 12px;
    }

    @media (max-width: 920px) {
      body { padding: 16px; }
      .hero { grid-template-columns: 1fr; }
      .intro { min-height: auto; padding: 28px; }
      .steps { grid-template-columns: 1fr; }
      .metrics { grid-template-columns: 1fr; }
    }
  </style>
</head>
<body>
  <main class="shell">
    <section class="hero">
      <div class="panel intro">
        <div>
          <div class="brand-row">
            <div class="logo"><img src="/assets/logo?v=3" alt="BOOSTEREX logo" onerror="this.parentElement.innerHTML='B';"></div>
            <div class="tag">CSV verified PDF report</div>
          </div>
          <h1>BOOSTEREX inventory report generator.</h1>
          <p class="lead">
            Upload your Shopify products CSV and BOOSTEREX will generate a clean inventory PDF report using your backend logic: active + published products, positive inventory, exact variant-level value, and collection-wise detail.
          </p>
          <div class="steps">
            <div class="step"><b>1. Upload CSV</b><span>Choose the Shopify products export file.</span></div>
            <div class="step"><b>2. Generate PDF</b><span>The backend calculates stock and retail value.</span></div>
            <div class="step"><b>3. Download</b><span>PDF is removed after download or page refresh.</span></div>
          </div>
        </div>
      </div>

      <div class="panel upload-panel">
        <h2 class="upload-title">Generate report</h2>
        <p class="upload-sub">Only .csv files are accepted. No side CSV files are created.</p>

        <form id="uploadForm">
          <label class="dropzone" id="dropzone" for="csvFile">
            <div>
              <div class="drop-icon">↑</div>
              <p class="drop-main">Drop CSV here or click to browse</p>
              <p class="drop-small">Maximum file size: 100 MB</p>
            </div>
          </label>
          <input id="csvFile" name="csv_file" type="file" accept=".csv,text/csv" />

          <div class="file-card" id="fileCard">
            <div>
              <div class="file-name" id="fileName"></div>
              <div class="file-size" id="fileSize"></div>
            </div>
            <button type="button" class="ghost" id="clearBtn">Clear</button>
          </div>

          <div class="btn-row">
            <button id="generateBtn" type="submit">Generate PDF Report</button>
          </div>
        </form>

        <div class="loader" id="loader"><div></div></div>
        <div class="status" id="statusBox"></div>

        <div class="result" id="resultBox">
          <h3>PDF is ready ✅</h3>
          <div class="metrics" id="metricsBox"></div>
          <a class="download-btn" id="downloadBtn" href="#" download>Download PDF</a>
          <p class="note">After you download, the PDF is deleted from the server. If you refresh this page, temporary PDFs are also cleaned automatically.</p>
        </div>
      </div>
    </section>
    <p class="footer-note">Local app: files stay on your own machine while this server is running.</p>
  </main>

  <script>
    const fileInput = document.getElementById('csvFile');
    const dropzone = document.getElementById('dropzone');
    const fileCard = document.getElementById('fileCard');
    const fileName = document.getElementById('fileName');
    const fileSize = document.getElementById('fileSize');
    const clearBtn = document.getElementById('clearBtn');
    const form = document.getElementById('uploadForm');
    const generateBtn = document.getElementById('generateBtn');
    const loader = document.getElementById('loader');
    const statusBox = document.getElementById('statusBox');
    const resultBox = document.getElementById('resultBox');
    const downloadBtn = document.getElementById('downloadBtn');
    const metricsBox = document.getElementById('metricsBox');

    let currentDownloadUrl = null;

    function readableSize(bytes) {
      if (!bytes) return '0 KB';
      const units = ['B', 'KB', 'MB', 'GB'];
      let size = bytes;
      let index = 0;
      while (size >= 1024 && index < units.length - 1) {
        size /= 1024;
        index++;
      }
      return `${size.toFixed(index === 0 ? 0 : 1)} ${units[index]}`;
    }

    function setStatus(type, message) {
      statusBox.className = `status ${type}`;
      statusBox.textContent = message;
    }

    function resetStatus() {
      statusBox.className = 'status';
      statusBox.textContent = '';
    }

    function setFile(file) {
      if (!file) return;
      fileName.textContent = file.name;
      fileSize.textContent = readableSize(file.size);
      fileCard.style.display = 'flex';
      resultBox.style.display = 'none';
      resetStatus();
    }

    fileInput.addEventListener('change', () => setFile(fileInput.files[0]));

    clearBtn.addEventListener('click', () => {
      fileInput.value = '';
      fileCard.style.display = 'none';
      resultBox.style.display = 'none';
      resetStatus();
    });

    ['dragenter', 'dragover'].forEach(eventName => {
      dropzone.addEventListener(eventName, event => {
        event.preventDefault();
        dropzone.classList.add('dragover');
      });
    });

    ['dragleave', 'drop'].forEach(eventName => {
      dropzone.addEventListener(eventName, event => {
        event.preventDefault();
        dropzone.classList.remove('dragover');
      });
    });

    dropzone.addEventListener('drop', event => {
      const file = event.dataTransfer.files[0];
      if (!file) return;
      const transfer = new DataTransfer();
      transfer.items.add(file);
      fileInput.files = transfer.files;
      setFile(file);
    });

    function renderMetrics(metrics) {
      const items = [
        ['Active + Published', metrics.active_published],
        ['Products with Stock', metrics.products_with_stock],
        ['Out of Stock', metrics.out_of_stock],
        ['Available Units', metrics.available_units],
        ['Inventory Value', metrics.inventory_value],
        ['Simple Value', metrics.simple_inventory_value]
      ];
      metricsBox.innerHTML = items.map(([label, value]) => `
        <div class="metric"><span>${label}</span><b>${value}</b></div>
      `).join('');
    }

    form.addEventListener('submit', async event => {
      event.preventDefault();
      const file = fileInput.files[0];
      if (!file) {
        setStatus('error', 'Please choose a CSV file first.');
        return;
      }
      if (!file.name.toLowerCase().endsWith('.csv')) {
        setStatus('error', 'Only CSV files are allowed.');
        return;
      }

      const formData = new FormData();
      formData.append('csv_file', file);

      generateBtn.disabled = true;
      loader.style.display = 'block';
      resultBox.style.display = 'none';
      setStatus('info', 'Generating your inventory PDF report...');

      try {
        const response = await fetch('/generate', { method: 'POST', body: formData });
        const data = await response.json();
        if (!response.ok || !data.success) {
          throw new Error(data.detail || data.error || 'PDF generation failed.');
        }

        currentDownloadUrl = data.download_url;
        downloadBtn.href = data.download_url;
        downloadBtn.setAttribute('download', data.filename);
        renderMetrics(data.metrics);
        resultBox.style.display = 'block';
        setStatus('success', 'Report generated successfully. Click Download PDF.');
      } catch (error) {
        setStatus('error', error.message || 'Something went wrong.');
      } finally {
        generateBtn.disabled = false;
        loader.style.display = 'none';
      }
    });

    downloadBtn.addEventListener('click', () => {
      setTimeout(() => {
        setStatus('info', 'Download started. The server copy will be removed automatically.');
      }, 600);
    });

    window.addEventListener('beforeunload', () => {
      if (currentDownloadUrl && navigator.sendBeacon) {
        navigator.sendBeacon('/cleanup');
      }
    });
  </script>
</body>
</html>
"""


def ensure_web_dirs() -> None:
    UPLOAD_DIR.mkdir(parents=True, exist_ok=True)
    REPORT_DIR.mkdir(parents=True, exist_ok=True)


def web_safe_stem(filename: str) -> str:
    stem = safe_filename_stem(filename or "products_export")
    stem = re.sub(r"[^A-Za-z0-9_-]+", "_", stem).strip("_")
    return (stem[:80] or "products_export")


def delete_file(path: Path) -> None:
    try:
        Path(path).unlink(missing_ok=True)
    except Exception:
        pass


def cleanup_generated_reports() -> int:
    ensure_web_dirs()
    deleted = 0
    for folder in (UPLOAD_DIR, REPORT_DIR):
        for item in folder.iterdir():
            if item.is_file() and item.suffix.lower() in {".csv", ".pdf"}:
                try:
                    item.unlink()
                    deleted += 1
                except Exception:
                    pass
    return deleted


def cleanup_old_generated_files(max_age_minutes: int = 60) -> int:
    ensure_web_dirs()
    deleted = 0
    now_ts = datetime.now().timestamp()
    max_age_seconds = max_age_minutes * 60
    for folder in (UPLOAD_DIR, REPORT_DIR):
        for item in folder.iterdir():
            if not item.is_file():
                continue
            if item.suffix.lower() not in {".csv", ".pdf"}:
                continue
            try:
                if now_ts - item.stat().st_mtime > max_age_seconds:
                    item.unlink()
                    deleted += 1
            except Exception:
                pass
    return deleted


def safe_download_path(file_name: str) -> Path:
    if not re.fullmatch(r"[A-Za-z0-9_.-]+\.pdf", file_name or ""):
        raise HTTPException(status_code=400, detail="Invalid file name.")
    path = (REPORT_DIR / file_name).resolve()
    report_root = REPORT_DIR.resolve()
    if report_root not in path.parents and path != report_root:
        raise HTTPException(status_code=400, detail="Invalid file path.")
    return path


@app.get("/", response_class=HTMLResponse)
async def index():
    cleanup_generated_reports()
    return HTMLResponse(INDEX_HTML)


@app.post("/cleanup")
async def cleanup():
    deleted = cleanup_generated_reports()
    return JSONResponse({"success": True, "deleted": deleted})


@app.post("/generate")
async def generate_report(csv_file: UploadFile = File(...)):
    ensure_web_dirs()
    cleanup_old_generated_files()

    original_name = csv_file.filename or "products_export.csv"
    if not original_name.lower().endswith(".csv"):
        raise HTTPException(status_code=400, detail="Please upload a .csv file only.")

    raw = await csv_file.read()
    if not raw:
        raise HTTPException(status_code=400, detail="Uploaded CSV is empty.")
    if len(raw) > MAX_UPLOAD_BYTES:
        raise HTTPException(status_code=413, detail=f"CSV is too large. Maximum size is {MAX_UPLOAD_MB} MB.")

    unique = uuid.uuid4().hex[:10]
    stem = web_safe_stem(original_name)
    upload_path = UPLOAD_DIR / f"{unique}_{stem}.csv"
    pdf_filename = f"{stem}_{datetime.now().strftime('%Y%m%d_%H%M%S')}_{unique}_Inventory_Report.pdf"
    pdf_path = REPORT_DIR / pdf_filename

    try:
        upload_path.write_bytes(raw)

        report = await asyncio.to_thread(
            make_pdf,
            csv_path=str(upload_path),
            output_pdf=str(pdf_path),
            products_per_collection=DEFAULT_PRODUCTS_PER_COLLECTION,
            make_csv_outputs=False,
        )

        metrics = report.metrics
        return JSONResponse(
            {
                "success": True,
                "filename": pdf_filename,
                "download_url": f"/download/{quote(pdf_filename, safe='')}",
                "metrics": {
                    "active_published": format_int(metrics["Active + Published"]),
                    "products_with_stock": format_int(metrics["Products with stock"]),
                    "out_of_stock": format_int(metrics["Out of stock"]),
                    "available_units": format_int(metrics["Available units"]),
                    "inventory_value": format_money(metrics["Inventory value"]),
                    "simple_inventory_value": format_money(metrics["Simple inventory value"]),
                },
            }
        )
    except ValueError as exc:
        delete_file(pdf_path)
        raise HTTPException(status_code=400, detail=str(exc)) from exc
    except Exception as exc:
        delete_file(pdf_path)
        raise HTTPException(status_code=500, detail=f"PDF generation failed: {exc}") from exc
    finally:
        delete_file(upload_path)
        try:
            await csv_file.close()
        except Exception:
            pass


@app.get("/download/{file_name}")
async def download_report(file_name: str):
    ensure_web_dirs()
    path = safe_download_path(file_name)
    if not path.exists():
        raise HTTPException(status_code=404, detail="PDF not found. Please generate the report again.")

    return FileResponse(
        path=str(path),
        media_type="application/pdf",
        filename=file_name,
        background=BackgroundTask(delete_file, path),
    )


if __name__ == "__main__":
    ensure_web_dirs()
    print("\nBOOSTEREX Inventory Report Generator")
    logo_path = find_logo_file()
    print("Open this local link in your browser:")
    print("http://127.0.0.1:8000")
    print("Logo found:", str(logo_path) if logo_path else "NO - put logo.png beside app.py")
    print("Logo debug:", "http://127.0.0.1:8000/debug/logo")
    print("On Amazon Linux/EC2, run with host 0.0.0.0 and open your public IP/security-group port.\n")

    host = os.getenv("HOST", "0.0.0.0")
    port = int(os.getenv("PORT", "8000"))
    uvicorn.run(app, host=host, port=port)
