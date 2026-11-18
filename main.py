#!/usr/bin/env python3
"""Lexora LegalTech: rule-based screening of multilingual contracts.

Usage:
    python lexora.py                      interactive menu
    python lexora.py contract.pdf         analyze one or more files
    python lexora.py a.docx --save        analyze and store in the database
"""

import argparse
import codecs
import contextlib
import difflib
import getpass
import hashlib
import hmac
import json
import os
import re
import secrets
import sqlite3
import tempfile
import unicodedata
from collections import Counter
from datetime import datetime, timedelta
from html import escape
from pathlib import Path
from typing import Optional

APP_DIR = Path(__file__).resolve().parent
DB_FILE = APP_DIR / "lexora.db"
REPORT_DIR = APP_DIR / "reports"
CLAUSES_FILE = APP_DIR / "clauses.json"
VERSION = "39.0"

MAX_FILE_BYTES = 10 * 1024 * 1024
SUPPORTED_SUFFIXES = {".txt", ".md", ".csv", ".pdf", ".docx"}
PBKDF2_ITERATIONS = 200_000
SESSION_TTL = timedelta(hours=8)
MAX_LOGIN_ATTEMPTS = 5
LOGIN_WINDOW = timedelta(minutes=15)
USERNAME_RE = re.compile(r"[A-Za-z0-9_.\-]{3,64}")

DISCLAIMER = (
    "این گزارش غربالگری ماشینی است و نظر حقوقی یا "
    "تأیید اعتبار قانونی قرارداد محسوب نمی‌شود."
)


# =====================================================
# 1. TEXT NORMALIZATION
# =====================================================

_CHAR_TABLE = str.maketrans({
    "ي": "ی", "ك": "ک", "ة": "ه", "ۀ": "ه", "ؤ": "و",
    "إ": "ا", "أ": "ا", "\u200c": " ", "\u200f": "", "\u200e": "",
    "\u200b": "", "\ufeff": "", "\u00a0": " ",
})
_DIGIT_TABLE = str.maketrans(
    "۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩",
    "01234567890123456789",
)


def normalize_text(text):
    """Lowercase, unify Persian/Arabic letters and digits, collapse spaces."""
    text = unicodedata.normalize("NFKC", str(text or "")).lower()
    text = text.translate(_CHAR_TABLE).translate(_DIGIT_TABLE)
    return re.sub(r"\s+", " ", text).strip()


def detect_language(text):
    counts = {
        "Persian": len(re.findall(f"[{PERSIAN_LETTER}]", text)),
        "Chinese": len(re.findall(r"[\u4e00-\u9fff]", text)),
        "English": len(re.findall(r"[a-zA-Z]", text)),
    }
    if max(counts.values()) == 0:
        return "Unknown"
    return max(counts, key=counts.get)


# =====================================================
# 2. TERM PATTERNS
# Latin terms use word boundaries and accept plural forms.
# Persian terms use boundaries and common suffixes.
# Chinese terms match as substrings, since Chinese has no spaces.
# =====================================================

PERSIAN_LETTER = "\u0600-\u06FF"
PERSIAN_SUFFIXES = r"(?:های|ها|ای|ی|ان|ات|ه)?"
FUZZY_THRESHOLD = 0.88
CJK_RE = re.compile(r"[\u4e00-\u9fff]")
NUMBERED_HEADING_RE = re.compile(
    r"^\s*(?:ماده|بند|فصل|article|clause|section|第\s*[\d一二三四五六七八九十百]+\s*条)\b",
    re.IGNORECASE,
)


def build_pattern(term):
    text = normalize_text(term)
    escaped = re.escape(text)

    if re.fullmatch(r"[a-z0-9 /\-]+", text):
        return re.compile(
            r"(?<![a-z0-9])" + escaped + r"(?:s|es|ed|ing|ion|ions)?(?![a-z0-9])"
        )

    if re.search(f"[{PERSIAN_LETTER}]", text):
        return re.compile(
            f"(?<![{PERSIAN_LETTER}])" + escaped + PERSIAN_SUFFIXES
            + f"(?![{PERSIAN_LETTER}])"
        )

    return re.compile(escaped)


def strict_pattern(term):
    text = normalize_text(term)
    return re.compile(r"(?<![a-z0-9])" + re.escape(text) + r"(?![a-z0-9])")


def compile_terms(terms):
    return [(term, build_pattern(term)) for term in terms]


def matched_terms(normalized_line, compiled):
    return [term for term, pattern in compiled if pattern.search(normalized_line)]


def fuzzy_match(normalized_line, normalized_term):
    """Typo-tolerant match for Latin and Persian phrases of several characters."""
    if len(normalized_term) < 6 or CJK_RE.search(normalized_term):
        return False

    term_words = normalized_term.split()
    size = len(term_words)
    words = re.findall(r"[^\s.,;:()\[\]\"'«»]+", normalized_line)

    for start in range(len(words) - size + 1):
        window = " ".join(words[start:start + size])
        ratio = difflib.SequenceMatcher(None, window, normalized_term).ratio()
        if ratio >= FUZZY_THRESHOLD:
            return True
    return False


# =====================================================
# 3. KNOWLEDGE BASE
# =====================================================

CLAUSE_TERMS = {
    "Dispute Resolution": [
        "dispute resolution", "dispute settlement", "arbitration",
        "arbitrator", "arbitral tribunal", "mediation", "jurisdiction",
        "amicable settlement", "alternative dispute resolution",
        "expert determination",
        "حل اختلاف", "حل و فصل اختلاف", "حل و فصل دعاوی",
        "رسیدگی به اختلافات", "داوری", "داور", "مرجع حل اختلاف",
        "مذاکره برای حل اختلاف", "سازش", "میانجیگری",
        "争议解决", "争端解决", "仲裁", "仲裁庭", "仲裁机构",
        "争议仲裁", "调解", "纠纷解决",
        "爭議解決", "爭端解決", "調解", "糾紛解決",
    ],
    "Force Majeure": [
        "force majeure", "act of god", "unforeseeable circumstances",
        "events beyond control", "pandemic", "epidemic",
        "natural disaster", "government restrictions",
        "فورس ماژور", "قوه قاهره", "حوادث غیرمترقبه",
        "شرایط خارج از کنترل", "همه‌گیری", "بلایای طبیعی",
        "محدودیت‌های دولتی",
        "不可抗力", "不可预见事件", "不可控制的事件",
        "不可抗力事件", "不可預見事件", "自然灾害", "政府限制",
    ],
    "Payment": [
        "payment", "payment terms", "payment schedule", "invoice",
        "invoicing", "payable", "purchase price", "consideration",
        "late payment", "installment", "bank transfer",
        "پرداخت", "شرایط پرداخت", "نحوه پرداخت", "مبلغ قرارداد",
        "ثمن معامله", "صورتحساب", "فاکتور", "بهای قرارداد",
        "تأخیر در پرداخت", "پرداخت اقساطی", "اعتبار اسنادی",
        "付款", "支付", "付款条件", "付款期限", "发票", "价款",
        "付款方式", "分期付款", "信用证",
        "付款條件", "付款期限",
    ],
    "Termination": [
        "termination", "terminate", "cancellation", "early termination",
        "termination for cause", "breach of contract",
        "material breach", "event of default", "notice period",
        "termination notice",
        "فسخ", "انفساخ", "خاتمه قرارداد", "پایان قرارداد",
        "نقض قرارداد", "نقض اساسی قرارداد", "تخلف قراردادی",
        "ابطال قرارداد", "اخطار فسخ",
        "终止", "解除合同", "合同解除", "违约", "合同终止",
        "取消合同", "解除通知",
        "終止", "違約",
    ],
    "Governing Law": [
        "governing law", "applicable law", "applicable legislation",
        "choice of law", "conflict of laws", "governed by",
        "قانون حاکم", "قوانین حاکم", "قانون قابل اعمال",
        "قانون قابل اجرا", "تابع قوانین", "تعارض قوانین",
        "适用法律", "准据法", "适用的法律", "法律适用",
        "準據法", "適用法律",
    ],
    "Delivery": [
        "delivery", "delivery date", "delivery terms",
        "delivery location", "place of delivery", "delivery deadline",
        "shipment", "shipping", "incoterms", "bill of lading",
        "goods shall be delivered",
        "تحویل", "تحویل کالا", "زمان تحویل", "تاریخ تحویل",
        "محل تحویل", "شرایط تحویل", "ارسال کالا", "حمل کالا",
        "تسلیم کالا", "تحویل در مقصد", "بارنامه",
        "شرایط حمل بین‌المللی",
        "交货", "交付", "发货", "交货日期", "交付日期",
        "交货地点", "交付地点", "货物交付", "提单", "国际贸易术语",
        "交貨", "交貨地點",
    ],
    "Liability": [
        "liability", "liable", "indemnity", "indemnification",
        "compensation", "damages", "limitation of liability",
        "liquidated damages", "consequential loss", "indirect damages",
        "مسئولیت", "مسئولیت مدنی", "مسئولیت قراردادی",
        "جبران خسارت", "خسارت", "غرامت", "وجه التزام",
        "خسارت غیرمستقیم",
        "赔偿", "赔偿责任", "损害赔偿", "责任限制", "违约赔偿",
        "间接损失",
        "賠償", "損害賠償", "責任限制",
    ],
    "Confidentiality": [
        "confidentiality", "confidential information", "non-disclosure",
        "nondisclosure", "non disclosure agreement", "trade secret",
        "proprietary information", "data protection",
        "personal information",
        "محرمانگی", "اطلاعات محرمانه", "حفظ اسرار", "عدم افشا",
        "تعهد محرمانگی", "اسرار تجاری", "حفاظت از داده",
        "اطلاعات شخصی",
        "保密", "保密义务", "保密信息", "保密协议", "商业秘密",
        "数据保护", "个人信息",
        "保密條款", "商業秘密",
    ],
}

CRITICAL_CLAUSES = {
    "Payment", "Termination", "Governing Law",
    "Dispute Resolution", "Liability",
}

AMBIGUOUS_TERMS = [
    "as soon as possible", "reasonable time", "reasonable efforts",
    "best efforts", "from time to time", "promptly", "if necessary",
    "در اسرع وقت", "در اولین فرصت", "در زمان مناسب", "به نحو مقتضی",
    "در صورت لزوم", "تلاش متعارف",
    "尽快", "适当时间", "合理时间", "必要时", "尽可能",
    "儘快", "合理時間",
]

INCOMPLETE_TERMS = [
    "to be determined", "to be agreed", "to be decided",
    "as mutually agreed", "details will follow",
    "در آینده تعیین می‌شود", "تعیین خواهد شد",
    "بعداً توافق می‌شود", "متعاقباً اعلام می‌شود",
    "پس از توافق طرفین",
    "待定", "另行协商", "以后确定", "由双方另行约定", "待双方确认",
]

# (level, weight per hit, terms)
RISK_RULES = [
    ("High", 30, [
        "unlimited liability", "uncapped liability", "waive all claims",
        "مسئولیت نامحدود", "بدون حق اعتراض",
        "无上限责任", "无限责任", "放弃一切索赔",
        "無上限責任", "放棄一切索賠",
    ]),
    ("Medium", 12, [
        "without prior notice", "at any time", "sole discretion",
        "unilaterally", "بدون اطلاع قبلی", "به تشخیص انحصاری",
        "یک طرفه", "随时修改", "单方面", "隨時修改",
    ]),
    ("Review", 5, [
        "reasonable time", "as soon as possible", "best efforts",
        "reasonable efforts", "در اسرع وقت", "در زمان مناسب", "尽快",
    ]),
]

OBLIGATION_TERMS = [
    "متعهد است", "موظف است", "مکلف است", "باید",
    "shall", "must", "is required to", "undertakes to",
    "应当", "必须", "有义务",
]

CONSISTENCY_PAIRS = [
    (["غیرقابل فسخ", "irrevocable"], ["حق فسخ", "may terminate", "حق خاتمه"]),
    (["محرمانه", "confidential"], ["افشای عمومی", "public disclosure"]),
    (["انحصاری", "exclusive"], ["غیرانحصاری", "non-exclusive"]),
]

INTERNATIONAL_TERMS = [
    "EXW", "FCA", "CPT", "CIP", "DAP", "DPU", "DDP", "FAS", "FOB",
    "CFR", "CIF", "LC", "L/C", "SWIFT", "CNY", "RMB", "USD", "EUR",
    "IRR", "GBP",
]


def compile_groups(groups):
    return {name: compile_terms(terms) for name, terms in groups.items()}


def load_clause_terms():
    terms = {name: list(values) for name, values in CLAUSE_TERMS.items()}

    if CLAUSES_FILE.exists():
        custom = json.loads(CLAUSES_FILE.read_text(encoding="utf-8"))
        for name, values in custom.items():
            bucket = terms.setdefault(name, [])
            bucket.extend(v for v in values if v not in bucket)

    return terms


CLAUSE_PATTERNS = compile_groups(load_clause_terms())
AMBIGUOUS_PATTERNS = compile_terms(AMBIGUOUS_TERMS)
INCOMPLETE_PATTERNS = compile_terms(INCOMPLETE_TERMS)
RISK_PATTERNS = [
    (level, weight, compile_terms(terms)) for level, weight, terms in RISK_RULES
]
OBLIGATION_PATTERNS = compile_terms(OBLIGATION_TERMS)
CONSISTENCY_PATTERNS = [
    (compile_terms(first), compile_terms(second))
    for first, second in CONSISTENCY_PAIRS
]
INTERNATIONAL_PATTERNS = [(term, strict_pattern(term)) for term in INTERNATIONAL_TERMS]


# =====================================================
# 4. DOCUMENT READER
# =====================================================

def decode_text(raw):
    if raw.startswith((codecs.BOM_UTF16_LE, codecs.BOM_UTF16_BE)):
        return raw.decode("utf-16")
    if raw.startswith(codecs.BOM_UTF8):
        return raw.decode("utf-8-sig")
    try:
        return raw.decode("utf-8")
    except UnicodeDecodeError:
        pass

    candidates = []
    for encoding in ("gb18030", "cp1256"):
        try:
            candidates.append(raw.decode(encoding))
        except UnicodeDecodeError:
            continue

    if not candidates:
        return raw.decode("utf-8", errors="replace")

    return max(
        candidates,
        key=lambda text: len(re.findall(r"[\u4e00-\u9fff\u0600-\u06FF]", text)),
    )


def read_document(file_path):
    path = Path(file_path)

    if not path.exists():
        raise FileNotFoundError(f"File not found: {path}")
    if path.stat().st_size > MAX_FILE_BYTES:
        raise ValueError("File exceeds 10 MB")

    suffix = path.suffix.lower()

    if suffix in {".txt", ".md", ".csv"}:
        return decode_text(path.read_bytes())

    if suffix == ".pdf":
        try:
            import fitz
        except ImportError as exc:
            raise RuntimeError("برای PDF: pip install pymupdf") from exc

        with fitz.open(str(path)) as document:
            return "\n".join(page.get_text() for page in document)

    if suffix == ".docx":
        try:
            from docx import Document
        except ImportError as exc:
            raise RuntimeError("برای DOCX: pip install python-docx") from exc

        document = Document(str(path))
        parts = [paragraph.text for paragraph in document.paragraphs]

        for table in document.tables:
            for row in table.rows:
                cells = []
                for cell in row.cells:
                    value = cell.text.strip()
                    if value and (not cells or cells[-1] != value):
                        cells.append(value)
                if cells:
                    parts.append(" | ".join(cells))

        return "\n".join(parts)

    raise ValueError("Supported files: TXT, MD, CSV, PDF, DOCX")


def extract_text_from_bytes(data, suffix):
    fd, temp_path = tempfile.mkstemp(suffix=suffix)
    try:
        with os.fdopen(fd, "wb") as handle:
            handle.write(data)
        return read_document(temp_path)
    finally:
        os.remove(temp_path)


# =====================================================
# 5. ANALYSIS ENGINE
# =====================================================

def find_clause_hits(lines, compiled):
    matches = []
    distinct = set()

    for number, line in enumerate(lines, start=1):
        normalized = normalize_text(line)
        if not normalized:
            continue

        hit_term, kind = None, None

        for term, pattern in compiled:
            if pattern.search(normalized):
                hit_term, kind = term, "exact"
                break

        if hit_term is None:
            for term, _ in compiled:
                if fuzzy_match(normalized, normalize_text(term)):
                    hit_term, kind = term, "fuzzy"
                    break

        if hit_term is not None:
            matches.append({
                "line": number,
                "keyword": hit_term,
                "match": kind,
                "text": line.strip(),
            })
            distinct.add(hit_term)

    return matches, distinct


def find_heading_hits(lines, compiled):
    hits = []

    for number, line in enumerate(lines, start=1):
        normalized = normalize_text(line)
        if not normalized or len(normalized) > 120:
            continue
        if not NUMBERED_HEADING_RE.search(normalized):
            continue

        for term in matched_terms(normalized, compiled):
            hits.append({
                "line": number,
                "keyword": term,
                "match": "heading",
                "text": line.strip(),
            })
            break

    return hits


def clause_confidence(matches, distinct, heading_hits):
    if not matches and not heading_hits:
        return 0
    score = 30 + 10 * len(distinct)
    if heading_hits:
        score += 25
    fuzzy_only = all(m["match"] == "fuzzy" for m in matches) and not heading_hits
    if fuzzy_only:
        score -= 15
    return max(10, min(95, score))


def find_term_hits(lines, compiled):
    hits = []

    for number, line in enumerate(lines, start=1):
        normalized = normalize_text(line)
        if not normalized:
            continue

        for term in matched_terms(normalized, compiled):
            hits.append({
                "line": number,
                "term": term,
                "text": line.strip(),
            })

    return hits


def find_duplicate_lines(lines):
    seen = {}
    duplicates = []

    for index, line in enumerate(lines, start=1):
        normalized = normalize_text(line)
        if len(normalized) < 8:
            continue

        if normalized in seen:
            duplicates.append({
                "first_line": seen[normalized],
                "duplicate_line": index,
                "text": line.strip(),
            })
        else:
            seen[normalized] = index

    return duplicates


def find_obligations(lines):
    obligations = []

    for number, line in enumerate(lines, start=1):
        normalized = normalize_text(line)
        if normalized and matched_terms(normalized, OBLIGATION_PATTERNS):
            obligations.append({
                "line": number,
                "description": line.strip(),
                "status": "Review Required",
            })

    return obligations


def find_risk_flags(lines):
    flags = []

    for number, line in enumerate(lines, start=1):
        normalized = normalize_text(line)
        if not normalized:
            continue

        for level, weight, compiled in RISK_PATTERNS:
            for term in matched_terms(normalized, compiled):
                flags.append({
                    "level": level,
                    "weight": weight,
                    "line": number,
                    "term": term,
                    "text": line.strip(),
                    "requires_human_review": True,
                })

    return flags


def find_international_terms(text):
    normalized = normalize_text(text)
    return sorted({
        term for term, pattern in INTERNATIONAL_PATTERNS
        if pattern.search(normalized)
    })


def find_consistency_warnings(text):
    normalized = normalize_text(text)
    warnings = []

    for first_group, second_group in CONSISTENCY_PATTERNS:
        if matched_terms(normalized, first_group) and matched_terms(normalized, second_group):
            warnings.append({
                "type": "possible_inconsistency",
                "message": "دو عبارت نیازمند بررسی تطبیق با یکدیگر هستند.",
                "human_review_required": True,
            })

    return warnings


def extract_information(text):
    ascii_text = text.translate(_DIGIT_TABLE)

    dates = re.findall(
        r"\b(?:\d{4}[-/]\d{1,2}[-/]\d{1,2}"
        r"|\d{1,2}[-/]\d{1,2}[-/]\d{2,4})\b",
        ascii_text,
    )
    emails = re.findall(
        r"\b[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}\b",
        ascii_text,
    )
    amounts = re.findall(
        r"(?:[$€£¥]\s?\d[\d,.]*"
        r"|\d[\d,.]*\s?(?:USD|EUR|GBP|IRR|RMB|CNY|دلار|یورو|ریال|تومان))",
        ascii_text,
        flags=re.IGNORECASE,
    )

    return {
        "dates": sorted(set(dates)),
        "emails": sorted(set(emails)),
        "amounts": sorted(set(amounts)),
    }


def risk_level(score):
    if score >= 50:
        return "High"
    if score >= 20:
        return "Medium"
    return "Low"


def analyze_contract(text):
    lines = text.splitlines()

    clause_results = {}
    for name, compiled in CLAUSE_PATTERNS.items():
        matches, distinct = find_clause_hits(lines, compiled)
        heading_hits = find_heading_hits(lines, compiled)
        found = bool(matches or heading_hits)

        clause_results[name] = {
            "found": found,
            "confidence": clause_confidence(matches, distinct, heading_hits),
            "distinct_terms": sorted(distinct),
            "matches": heading_hits + matches,
        }

    missing = [name for name, data in clause_results.items() if not data["found"]]
    total = len(clause_results)
    coverage = round((total - len(missing)) / total * 100) if total else 0

    risk_flags = find_risk_flags(lines)
    for name in missing:
        if name in CRITICAL_CLAUSES:
            risk_flags.append({
                "level": "High",
                "weight": 15,
                "line": None,
                "term": name,
                "text": f"Critical clause not detected: {name}",
                "requires_human_review": True,
            })

    risk_score = min(100, sum(flag["weight"] for flag in risk_flags))

    return {
        "version": VERSION,
        "analysis_engine": "Lexora Rules Engine",
        "analysis_date": datetime.now().isoformat(timespec="seconds"),
        "language": detect_language(text),
        "coverage_score": coverage,
        "clauses_found": total - len(missing),
        "clauses_total": total,
        "clause_results": clause_results,
        "missing_clauses": missing,
        "duplicate_lines": find_duplicate_lines(lines),
        "ambiguous_terms": find_term_hits(lines, AMBIGUOUS_PATTERNS),
        "incomplete_terms": find_term_hits(lines, INCOMPLETE_PATTERNS),
        "advanced_obligations": find_obligations(lines),
        "risk_flags": risk_flags,
        "risk_score": risk_score,
        "risk_level": risk_level(risk_score),
        "international_terms": find_international_terms(text),
        "consistency_warnings": find_consistency_warnings(text),
        "extracted_information": extract_information(text),
        "disclaimer": DISCLAIMER,
    }


def analyze_file(path):
    content = read_document(path)
    result = analyze_contract(content)
    result["file_name"] = Path(path).name
    return content, result


def compare_clauses(old_result, new_result):
    changes = []
    for name in CLAUSE_PATTERNS:
        before = old_result["clause_results"].get(name, {}).get("found", False)
        after = new_result["clause_results"].get(name, {}).get("found", False)
        if before != after:
            changes.append(
                f"{name}: {'FOUND' if before else 'MISSING'} -> "
                f"{'FOUND' if after else 'MISSING'}"
            )
    return changes


def review_text(text):
    result = analyze_contract(text)
    recommendations = []

    for clause in result["missing_clauses"]:
        recommendations.append({
            "type": "missing_clause",
            "clause": clause,
            "message": "این موضوع در متن شناسایی نشد؛ وجود یا نبود آن را بررسی کنید.",
        })

    for risk in result["risk_flags"]:
        recommendations.append({
            "type": "risk_review",
            "level": risk["level"],
            "line": risk["line"],
            "message": f"عبارت «{risk['term']}» نیازمند بررسی انسانی است.",
        })

    return result, recommendations


# =====================================================
# 6. DATABASE
# =====================================================

DB_SCHEMA = """
CREATE TABLE IF NOT EXISTS users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    username TEXT UNIQUE NOT NULL,
    salt TEXT NOT NULL,
    password_hash TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS sessions (
    token_hash TEXT PRIMARY KEY,
    user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
    created_at TEXT NOT NULL,
    expires_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS login_attempts (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    username TEXT NOT NULL,
    attempted_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS contracts (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    file_name TEXT NOT NULL,
    content TEXT NOT NULL,
    analysis_json TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS obligations (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    contract_id INTEGER NOT NULL REFERENCES contracts(id) ON DELETE CASCADE,
    description TEXT NOT NULL,
    due_date TEXT,
    status TEXT DEFAULT 'Pending',
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS checklist_rules (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    name TEXT NOT NULL,
    keyword TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS audit_log (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    action TEXT NOT NULL,
    details TEXT,
    user_id INTEGER,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS contract_notes (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    contract_id INTEGER NOT NULL REFERENCES contracts(id) ON DELETE CASCADE,
    note TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS contract_archive (
    contract_id INTEGER PRIMARY KEY REFERENCES contracts(id) ON DELETE CASCADE,
    archived_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS contract_tags (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    contract_id INTEGER NOT NULL REFERENCES contracts(id) ON DELETE CASCADE,
    tag TEXT NOT NULL,
    UNIQUE (contract_id, tag)
);

CREATE TABLE IF NOT EXISTS legal_glossary (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    source_term TEXT NOT NULL,
    target_term TEXT NOT NULL,
    source_language TEXT DEFAULT 'en',
    target_language TEXT DEFAULT 'fa'
);
"""


@contextlib.contextmanager
def db():
    connection = sqlite3.connect(DB_FILE)
    connection.row_factory = sqlite3.Row
    connection.execute("PRAGMA foreign_keys = ON")
    try:
        yield connection
        connection.commit()
    except Exception:
        connection.rollback()
        raise
    finally:
        connection.close()


def initialize_database():
    with db() as conn:
        conn.executescript(DB_SCHEMA)


def now_iso():
    return datetime.now().isoformat(timespec="seconds")


def like_pattern(query):
    escaped = query.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")
    return f"%{escaped}%"


def audit_log(action, details="", user_id=None):
    with db() as conn:
        conn.execute(
            "INSERT INTO audit_log(action, details, user_id, created_at) "
            "VALUES(?,?,?,?)",
            (action, str(details)[:1000], user_id, now_iso()),
        )


# =====================================================
# 7. ACCOUNTS AND SESSIONS
# =====================================================

DUMMY_SALT = secrets.token_hex(16)


def hash_password(password, salt):
    return hashlib.pbkdf2_hmac(
        "sha256",
        password.encode("utf-8"),
        bytes.fromhex(salt),
        PBKDF2_ITERATIONS,
    ).hex()


def register_user(username, password):
    if not USERNAME_RE.fullmatch(username):
        raise ValueError(
            "نام کاربری باید ۳ تا ۶۴ نویسه و شامل حروف لاتین، عدد، نقطه، "
            "خط تیره یا زیرخط باشد."
        )
    if not 8 <= len(password) <= 128:
        raise ValueError("گذرواژه باید بین ۸ تا ۱۲۸ نویسه باشد.")

    salt = secrets.token_hex(16)
    password_hash = hash_password(password, salt)

    try:
        with db() as conn:
            conn.execute(
                "INSERT INTO users(username, salt, password_hash, created_at) "
                "VALUES(?,?,?,?)",
                (username, salt, password_hash, now_iso()),
            )
    except sqlite3.IntegrityError as exc:
        raise ValueError("ثبت‌نام انجام نشد.") from exc


def authenticate_user(username, password):
    with db() as conn:
        row = conn.execute(
            "SELECT id, salt, password_hash FROM users WHERE username = ?",
            (username,),
        ).fetchone()

    if row is None:
        hash_password(password, DUMMY_SALT)
        return None

    candidate = hash_password(password, row["salt"])
    if hmac.compare_digest(candidate, row["password_hash"]):
        return row["id"]
    return None


def count_recent_failures(username):
    cutoff = (datetime.now() - LOGIN_WINDOW).isoformat(timespec="seconds")
    with db() as conn:
        row = conn.execute(
            "SELECT COUNT(*) AS n FROM login_attempts "
            "WHERE username = ? AND attempted_at >= ?",
            (username, cutoff),
        ).fetchone()
    return row["n"]


def record_failure(username):
    with db() as conn:
        conn.execute(
            "INSERT INTO login_attempts(username, attempted_at) VALUES(?,?)",
            (username, now_iso()),
        )


def clear_failures(username):
    with db() as conn:
        conn.execute("DELETE FROM login_attempts WHERE username = ?", (username,))


def _hash_token(token):
    return hashlib.sha256(token.encode("utf-8")).hexdigest()


def create_session(user_id):
    token = secrets.token_urlsafe(32)
    created = datetime.now()
    expires = created + SESSION_TTL

    with db() as conn:
        conn.execute(
            "INSERT INTO sessions(token_hash, user_id, created_at, expires_at) "
            "VALUES(?,?,?,?)",
            (
                _hash_token(token),
                user_id,
                created.isoformat(timespec="seconds"),
                expires.isoformat(timespec="seconds"),
            ),
        )
    return token


def get_user_by_token(token):
    with db() as conn:
        row = conn.execute(
            """
            SELECT users.id, users.username, sessions.expires_at
            FROM sessions
            JOIN users ON users.id = sessions.user_id
            WHERE sessions.token_hash = ?
            """,
            (_hash_token(token),),
        ).fetchone()

    if row is None:
        return None
    if datetime.fromisoformat(row["expires_at"]) < datetime.now():
        return None
    return {"id": row["id"], "username": row["username"], "token": token}


def delete_session(token):
    with db() as conn:
        conn.execute(
            "DELETE FROM sessions WHERE token_hash = ?",
            (_hash_token(token),),
        )


def login_user(username, password):
    """Return a session token on success, None on wrong credentials."""
    if count_recent_failures(username) >= MAX_LOGIN_ATTEMPTS:
        raise PermissionError("تعداد تلاش‌های ناموفق زیاد است. بعداً دوباره امتحان کنید.")

    user_id = authenticate_user(username, password)
    if user_id is None:
        record_failure(username)
        return None

    clear_failures(username)
    token = create_session(user_id)
    audit_log("login", username, user_id)
    return token


# =====================================================
# 8. CONTRACTS, OBLIGATIONS, CHECKLIST, GLOSSARY
# =====================================================

def save_contract(filename, content, result, user_id=None):
    with db() as conn:
        cursor = conn.execute(
            "INSERT INTO contracts(file_name, content, analysis_json, created_at) "
            "VALUES(?,?,?,?)",
            (filename, content, json.dumps(result, ensure_ascii=False), now_iso()),
        )
        contract_id = cursor.lastrowid

    audit_log("contract_saved", f"{contract_id}:{filename}", user_id)
    return contract_id


def get_contract(contract_id):
    with db() as conn:
        return conn.execute(
            "SELECT * FROM contracts WHERE id = ?", (contract_id,)
        ).fetchone()


def list_contracts(include_archived=False):
    with db() as conn:
        rows = conn.execute(
            """
            SELECT id, file_name, created_at FROM contracts
            WHERE ? = 1 OR id NOT IN (SELECT contract_id FROM contract_archive)
            ORDER BY id DESC
            """,
            (1 if include_archived else 0,),
        ).fetchall()
    return [dict(row) for row in rows]


def search_contracts(query):
    with db() as conn:
        rows = conn.execute(
            """
            SELECT id, file_name, created_at FROM contracts
            WHERE file_name LIKE ? ESCAPE '\\'
            ORDER BY id DESC
            """,
            (like_pattern(query),),
        ).fetchall()
    return [dict(row) for row in rows]


def _require_contract(conn, contract_id):
    exists = conn.execute(
        "SELECT id FROM contracts WHERE id = ?", (contract_id,)
    ).fetchone()
    if not exists:
        raise LookupError("قرارداد پیدا نشد.")


def archive_contract(contract_id, user_id=None):
    with db() as conn:
        _require_contract(conn, contract_id)
        conn.execute(
            "INSERT OR REPLACE INTO contract_archive(contract_id, archived_at) "
            "VALUES(?,?)",
            (contract_id, now_iso()),
        )
    audit_log("contract_archived", contract_id, user_id)


def restore_contract(contract_id, user_id=None):
    with db() as conn:
        conn.execute(
            "DELETE FROM contract_archive WHERE contract_id = ?", (contract_id,)
        )
    audit_log("contract_restored", contract_id, user_id)


def add_contract_note(contract_id, note, user_id=None):
    with db() as conn:
        _require_contract(conn, contract_id)
        conn.execute(
            "INSERT INTO contract_notes(contract_id, note, created_at) VALUES(?,?,?)",
            (contract_id, note, now_iso()),
        )
    audit_log("note_added", contract_id, user_id)


def list_contract_notes(contract_id):
    with db() as conn:
        rows = conn.execute(
            "SELECT * FROM contract_notes WHERE contract_id = ? ORDER BY id DESC",
            (contract_id,),
        ).fetchall()
    return [dict(row) for row in rows]


def add_contract_tag(contract_id, tag, user_id=None):
    with db() as conn:
        _require_contract(conn, contract_id)
        conn.execute(
            "INSERT OR IGNORE INTO contract_tags(contract_id, tag) VALUES(?,?)",
            (contract_id, tag),
        )
    audit_log("tag_added", f"{contract_id}:{tag}", user_id)


def get_contract_tags(contract_id):
    with db() as conn:
        rows = conn.execute(
            "SELECT tag FROM contract_tags WHERE contract_id = ? ORDER BY tag",
            (contract_id,),
        ).fetchall()
    return [row["tag"] for row in rows]


def add_obligation(contract_id, description, due_date=None, user_id=None):
    with db() as conn:
        _require_contract(conn, contract_id)
        conn.execute(
            "INSERT INTO obligations(contract_id, description, due_date, created_at) "
            "VALUES(?,?,?,?)",
            (contract_id, description, due_date, now_iso()),
        )
    audit_log("obligation_added", contract_id, user_id)


def list_obligations(contract_id):
    with db() as conn:
        rows = conn.execute(
            "SELECT * FROM obligations WHERE contract_id = ? ORDER BY id DESC",
            (contract_id,),
        ).fetchall()
    return [dict(row) for row in rows]


def add_rule(name, keyword, user_id=None):
    with db() as conn:
        conn.execute(
            "INSERT INTO checklist_rules(name, keyword, created_at) VALUES(?,?,?)",
            (name, keyword, now_iso()),
        )
    audit_log("rule_added", name, user_id)


def list_rules():
    with db() as conn:
        rows = conn.execute(
            "SELECT id, name, keyword FROM checklist_rules ORDER BY id"
        ).fetchall()
    return [dict(row) for row in rows]


def run_checklist(text):
    rules = list_rules()
    normalized = normalize_text(text)
    results = []

    for rule in rules:
        found = build_pattern(rule["keyword"]).search(normalized) is not None
        results.append({
            "name": rule["name"],
            "keyword": rule["keyword"],
            "status": "Found" if found else "Missing",
        })

    return results


def add_glossary_term(source_term, target_term,
                      source_language="en", target_language="fa", user_id=None):
    with db() as conn:
        conn.execute(
            "INSERT INTO legal_glossary"
            "(source_term, target_term, source_language, target_language) "
            "VALUES(?,?,?,?)",
            (source_term, target_term, source_language, target_language),
        )
    audit_log("glossary_added", source_term, user_id)


def lookup_glossary(term):
    with db() as conn:
        rows = conn.execute(
            "SELECT * FROM legal_glossary WHERE source_term LIKE ? ESCAPE '\\'",
            (like_pattern(term),),
        ).fetchall()
    return [dict(row) for row in rows]


def contract_analytics():
    with db() as conn:
        rows = conn.execute("SELECT analysis_json FROM contracts").fetchall()

    scores = []
    levels = Counter()
    languages = Counter()
    missing_counts = Counter()

    for row in rows:
        try:
            data = json.loads(row["analysis_json"])
        except (TypeError, json.JSONDecodeError):
            continue

        scores.append(data.get("coverage_score", 0))
        levels[data.get("risk_level", "Unknown")] += 1
        languages[data.get("language", "Unknown")] += 1
        for clause in data.get("missing_clauses", []):
            missing_counts[clause] += 1

    return {
        "total_contracts": len(rows),
        "average_coverage": round(sum(scores) / len(scores), 2) if scores else 0,
        "risk_levels": dict(levels),
        "languages": dict(languages),
        "most_missing_clauses": dict(missing_counts.most_common(10)),
    }


# =====================================================
# 9. REPORTS
# =====================================================

def generate_markdown(result):
    lines = [
        "# LEXORA LEGALTECH",
        "",
        f"Version: {result.get('version', VERSION)}",
        f"File: {result.get('file_name', '-')}",
        f"Language: {result['language']}",
        f"Coverage: {result['coverage_score']}/100",
        f"Risk: {result.get('risk_level', '-')} ({result.get('risk_score', 0)}/100)",
        f"Date: {result['analysis_date']}",
        "",
        "## Clause Analysis",
        "",
    ]

    for name, data in result["clause_results"].items():
        status = "FOUND" if data["found"] else "MISSING"
        lines.append(f"### {name} — {status}")
        if data["found"]:
            lines.append(f"- Confidence: {data.get('confidence', 0)}%")
            for match in data["matches"]:
                lines.append(
                    f"- Line {match['line']} | Keyword: {match['keyword']} "
                    f"({match.get('match', 'exact')}) | {match['text']}"
                )
        else:
            lines.append("- No matching keyword found")
        lines.append("")

    def section(title, items, render):
        lines.extend([f"## {title}", ""])
        if items:
            lines.extend(render(item) for item in items)
        else:
            lines.append("- None")
        lines.append("")

    section("Missing Clauses", result["missing_clauses"], lambda name: f"- {name}")
    section(
        "Risk Flags", result.get("risk_flags", []),
        lambda item: f"- [{item['level']}] Line {item['line'] or '-'}: "
                     f"{item['term']} | {item['text']}",
    )
    section(
        "Duplicate Lines", result["duplicate_lines"],
        lambda item: f"- Line {item['duplicate_line']} duplicates line {item['first_line']}",
    )
    section(
        "Ambiguous Terms", result["ambiguous_terms"],
        lambda item: f"- Line {item['line']}: {item['term']}",
    )
    section(
        "Incomplete Terms", result["incomplete_terms"],
        lambda item: f"- Line {item['line']}: {item['term']}",
    )
    section(
        "Obligations for Review", result.get("advanced_obligations", []),
        lambda item: f"- Line {item['line']}: {item['description']}",
    )
    section(
        "International Terms", result.get("international_terms", []),
        lambda term: f"- {term}",
    )
    section(
        "Consistency Warnings", result.get("consistency_warnings", []),
        lambda item: f"- {item['message']}",
    )

    lines.extend([
        "## Extracted Information",
        "",
        "```json",
        json.dumps(result["extracted_information"], ensure_ascii=False, indent=2),
        "```",
        "",
        "> Coverage measures keyword-based clause detection. "
        "It does not certify legal completeness or correctness.",
        "",
        DISCLAIMER,
        "",
    ])

    return "\n".join(lines)


def save_reports(result, markdown_path, json_path):
    Path(markdown_path).write_text(generate_markdown(result), encoding="utf-8")
    Path(json_path).write_text(
        json.dumps(result, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def export_pdf(result, output_path):
    try:
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
        from reportlab.pdfbase import pdfmetrics
        from reportlab.pdfbase.cidfonts import UnicodeCIDFont
        from reportlab.pdfbase.ttfonts import TTFont
        from reportlab.platypus import Paragraph, SimpleDocTemplate, Spacer
    except ImportError as exc:
        raise RuntimeError("برای خروجی PDF: pip install reportlab") from exc

    font_path = os.environ.get("LEXORA_FONT", "")
    if font_path and Path(font_path).exists():
        pdfmetrics.registerFont(TTFont("LexoraFont", font_path))
        font_name = "LexoraFont"
    else:
        pdfmetrics.registerFont(UnicodeCIDFont("STSong-Light"))
        font_name = "STSong-Light"

    base = getSampleStyleSheet()
    title = ParagraphStyle("LexTitle", parent=base["Title"], fontName=font_name)
    heading = ParagraphStyle("LexHeading", parent=base["Heading3"], fontName=font_name)
    body = ParagraphStyle(
        "LexBody", parent=base["BodyText"], fontName=font_name,
        fontSize=10, leading=14,
    )

    story = [
        Paragraph("Lexora LegalTech Report", title),
        Spacer(1, 10),
        Paragraph(escape(f"File: {result.get('file_name', '-')}"), body),
        Paragraph(escape(f"Language: {result['language']}"), body),
        Paragraph(f"Coverage: {result['coverage_score']}/100", body),
        Paragraph(
            escape(f"Risk: {result.get('risk_level', '-')} "
                   f"({result.get('risk_score', 0)}/100)"),
            body,
        ),
        Spacer(1, 10),
        Paragraph("Clauses", heading),
    ]

    for name, data in result["clause_results"].items():
        status = "FOUND" if data["found"] else "MISSING"
        story.append(Paragraph(escape(f"{name}: {status}"), body))

    story.extend([Spacer(1, 10), Paragraph("Risk Flags", heading)])
    flags = result.get("risk_flags", [])[:25]
    if flags:
        for flag in flags:
            story.append(Paragraph(
                escape(f"[{flag['level']}] line {flag['line'] or '-'}: "
                       f"{flag['term']}"),
                body,
            ))
    else:
        story.append(Paragraph("None", body))

    story.extend([
        Spacer(1, 12),
        Paragraph(escape(DISCLAIMER), body),
    ])

    SimpleDocTemplate(str(output_path), pagesize=A4).build(story)
    return str(output_path)


def export_all(result, folder, stem):
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)

    md_path = folder / f"{stem}.md"
    json_path = folder / f"{stem}.json"
    save_reports(result, md_path, json_path)
    created = [str(md_path), str(json_path)]

    try:
        pdf_path = folder / f"{stem}.pdf"
        export_pdf(result, pdf_path)
        created.append(str(pdf_path))
    except RuntimeError as error:
        print("PDF پساخته نشد:", error)

    return created


def compare_documents(old_file, new_file):
    old_text = read_document(old_file)
    new_text = read_document(new_file)

    return "\n".join(difflib.unified_diff(
        old_text.splitlines(),
        new_text.splitlines(),
        fromfile=str(old_file),
        tofile=str(new_file),
        lineterm="",
    ))


def print_summary(result):
    print("\n" + "=" * 60)
    print(f"LEXORA LEGALTECH {VERSION}")
    print("=" * 60)
    print("File:      ", result.get("file_name", "-"))
    print("Language:  ", result["language"])
    print("Coverage:  ", f"{result['coverage_score']}/100")
    print("Clauses:   ", f"{result['clauses_found']}/{result['clauses_total']}")
    print("Risk:      ", f"{result['risk_level']} ({result['risk_score']}/100)")

    print("\nCLAUSES")
    for name, data in result["clause_results"].items():
        status = "FOUND" if data["found"] else "MISSING"
        confidence = f" ({data['confidence']}%)" if data["found"] else ""
        print(f"  {name}: {status}{confidence}")
        for match in data["matches"][:5]:
            print(f"      line {match['line']}: {match['keyword']} "
                  f"[{match.get('match', 'exact')}]")

    print("\nMissing:            ", ", ".join(result["missing_clauses"]) or "None")
    print("Risk flags:         ", len(result["risk_flags"]))
    print("Duplicate lines:    ", len(result["duplicate_lines"]))
    print("Ambiguous terms:    ", len(result["ambiguous_terms"]))
    print("Incomplete terms:   ", len(result["incomplete_terms"]))
    print("Obligations to review:", len(result["advanced_obligations"]))
    print()


# =====================================================
# 10. COMMAND LINE AND INTERACTIVE MENU
# =====================================================

def build_arg_parser():
    parser = argparse.ArgumentParser(
        description=f"Lexora LegalTech {VERSION}: run without arguments for the menu."
    )
    parser.add_argument("files", nargs="*", help="contract files to analyze")
    parser.add_argument("--save", action="store_true", help="store results in the database")
    parser.add_argument("--report", default="lexora_report.md")
    parser.add_argument("--json", default="lexora_report.json")
    parser.add_argument("--pdf", help="write a PDF report to this path")
    parser.add_argument("--compare", nargs=2, metavar=("OLD", "NEW"))
    parser.add_argument("--list-contracts", action="store_true")
    parser.add_argument("--checklist", type=int, metavar="CONTRACT_ID")
    parser.add_argument("--add-rule", nargs=2, metavar=("NAME", "KEYWORD"))
    parser.add_argument("--add-obligation", nargs=2, metavar=("CONTRACT_ID", "DESCRIPTION"))
    parser.add_argument("--due-date")
    parser.add_argument("--list-obligations", type=int, metavar="CONTRACT_ID")
    parser.add_argument("--analytics", action="store_true")
    return parser


def process_cli_file(filename, args, multiple):
    try:
        content, result = analyze_file(filename)
        print_summary(result)

        if args.save:
            contract_id = save_contract(Path(filename).name, content, result)
            print("Saved. Contract ID:", contract_id)

        if multiple:
            base = Path(filename)
            md_path = str(base.with_suffix(".report.md"))
            json_path = str(base.with_suffix(".report.json"))
            pdf_path = str(base.with_suffix(".pdf"))
        else:
            md_path, json_path, pdf_path = args.report, args.json, args.pdf

        save_reports(result, md_path, json_path)
        print("Reports created:", md_path, json_path)

        if args.pdf or multiple:
            try:
                print("PDF created:", export_pdf(result, pdf_path))
            except RuntimeError as error:
                print("PDF not created:", error)

    except Exception as error:
        print(f"Error processing {filename}: {error}")


def run_cli(args):
    if args.list_contracts:
        for row in list_contracts():
            print(f"ID: {row['id']} | {row['file_name']} | {row['created_at']}")
        return

    if args.checklist is not None:
        row = get_contract(args.checklist)
        if not row:
            print("قرارداد پیدا نشد.")
            return
        for item in run_checklist(row["content"]):
            print(item)
        return

    if args.add_rule:
        add_rule(args.add_rule[0], args.add_rule[1])
        print("Checklist rule added.")
        return

    if args.add_obligation:
        try:
            add_obligation(int(args.add_obligation[0]), args.add_obligation[1], args.due_date)
            print("Obligation added.")
        except (ValueError, LookupError) as error:
            print(error)
        return

    if args.list_obligations is not None:
        for row in list_obligations(args.list_obligations):
            print(row)
        return

    if args.analytics:
        print(json.dumps(contract_analytics(), ensure_ascii=False, indent=2))
        return

    if args.compare:
        try:
            print(compare_documents(*args.compare))
        except (OSError, ValueError, RuntimeError) as error:
            print("Comparison error:", error)
        return

    multiple = len(args.files) > 1
    for filename in args.files:
        process_cli_file(filename, args, multiple)


def ask(text):
    try:
        return input(text).strip()
    except EOFError:
        raise SystemExit(0)


def read_path(text):
    raw = ask(text).strip('"').strip("'")
    if not raw:
        return None
    path = Path(raw).expanduser()
    if not path.exists():
        print("فایل پیدا نشد.")
        return None
    return path


def ask_contract_id():
    value = ask("شناسه قرارداد: ")
    if not value.isdigit():
        print("شناسه نامعتبر است.")
        return None
    return int(value)


def load_result(contract_id):
    row = get_contract(contract_id)
    if row is None:
        print("قرارداد پیدا نشد.")
        return None, None
    result = json.loads(row["analysis_json"])
    result.setdefault("file_name", row["file_name"])
    return row, result


def interactive_login():
    while True:
        choice = ask("1) ورود   2) ثبت‌نام   0) خروج\nانتخاب: ")

        if choice == "0":
            return None

        if choice == "2":
            username = ask("نام کاربری: ")
            password = getpass.getpass("گذرواژه (حداقل ۸ نویسه): ")
            confirm = getpass.getpass("تکرار گذرواژه: ")
            if password != confirm:
                print("گذرواژه‌ها یکسان نیستند.")
                continue
            try:
                register_user(username, password)
                print("حساب ساخته شد. لطفاً وارد شوید.")
            except ValueError as error:
                print(error)
            continue

        if choice == "1":
            username = ask("نام کاربری: ")
            password = getpass.getpass("گذرواژه: ")
            try:
                token = login_user(username, password)
            except PermissionError as error:
                print(error)
                continue
            if token is None:
                print("نام کاربری یا گذرواژه نادرست است.")
                continue
            return get_user_by_token(token)

        print("گزینهٔ نامعتبر است.")


def menu_analyze(user):
    path = read_path("مسیر فایل: ")
    if path is None:
        return
    try:
        content, result = analyze_file(path)
    except Exception as error:
        print("خطا:", error)
        return

    print_summary(result)
    if ask("ذخیرهٔ قرارداد در پایگاه داده؟ (Enter = بله، n = خیر): ").lower() in {"", "y", "yes"}:
        contract_id = save_contract(path.name, content, result, user["id"])
        print("ذخیره شد. شناسه:", contract_id)


def menu_list(user):
    for row in list_contracts(include_archived=True):
        print(f"ID: {row['id']} | {row['file_name']} | {row['created_at']}")


def menu_search(user):
    query = ask("نام فایل برای جستجو: ")
    for row in search_contracts(query):
        print(f"ID: {row['id']} | {row['file_name']} | {row['created_at']}")


def menu_show(user):
    contract_id = ask_contract_id()
    if contract_id is None:
        return
    _, result = load_result(contract_id)
    if result is None:
        return

    print_summary(result)
    for name, data in result["clause_results"].items():
        if data["found"]:
            print(f"{name}: {', '.join(data['distinct_terms'][:5])}")
    if result.get("risk_flags"):
        print("\nTOP RISK FLAGS")
        for flag in result["risk_flags"][:10]:
            print(f"  [{flag['level']}] line {flag['line'] or '-'}: {flag['text'][:120]}")


def menu_notes_tags(user):
    contract_id = ask_contract_id()
    if contract_id is None:
        return
    print("1) افزودن یادداشت   2) افزودن برچسب   3) نمایش یادداشت‌ها و برچسب‌ها")
    choice = ask("انتخاب: ")
    try:
        if choice == "1":
            add_contract_note(contract_id, ask("متن یادداشت: "), user["id"])
            print("یادداشت ذخیره شد.")
        elif choice == "2":
            add_contract_tag(contract_id, ask("برچسب: "), user["id"])
            print("برچسب ذخیره شد.")
        elif choice == "3":
            for note in list_contract_notes(contract_id):
                print(f"- [{note['created_at']}] {note['note']}")
            print("برچسب‌ها:", ", ".join(get_contract_tags(contract_id)) or "-")
    except LookupError as error:
        print(error)


def menu_archive(user):
    contract_id = ask_contract_id()
    if contract_id is None:
        return
    choice = ask("1) بایگانی   2) بازیابی: ")
    try:
        if choice == "1":
            archive_contract(contract_id, user["id"])
            print("بایگانی شد.")
        elif choice == "2":
            restore_contract(contract_id, user["id"])
            print("بازیابی شد.")
    except LookupError as error:
        print(error)


def menu_obligations(user):
    contract_id = ask_contract_id()
    if contract_id is None:
        return
    choice = ask("1) افزودن تعهد   2) فهرست تعهدات: ")
    try:
        if choice == "1":
            description = ask("شرح تعهد: ")
            due_date = ask("تاریخ سررسید (اختیاری): ") or None
            add_obligation(contract_id, description, due_date, user["id"])
            print("تعهد ثبت شد.")
        elif choice == "2":
            for row in list_obligations(contract_id):
                print(f"- {row['description']} | due: {row['due_date'] or '-'} | {row['status']}")
    except LookupError as error:
        print(error)


def menu_rules(user):
    choice = ask("1) افزودن قاعده   2) فهرست قواعد: ")
    if choice == "1":
        name = ask("نام قاعده: ")
        keyword = ask("کلیدواژه: ")
        if name and keyword:
            add_rule(name, keyword, user["id"])
            print("قاعده ثبت شد.")
    elif choice == "2":
        for rule in list_rules():
            print(f"{rule['id']}. {rule['name']} -> {rule['keyword']}")


def menu_checklist(user):
    contract_id = ask_contract_id()
    if contract_id is None:
        return
    row = get_contract(contract_id)
    if row is None:
        print("قرارداد پیدا نشد.")
        return
    for item in run_checklist(row["content"]):
        print(f"[{item['status']}] {item['name']} ({item['keyword']})")


def menu_glossary(user):
    choice = ask("1) افزودن واژه   2) جستجوی واژه: ")
    if choice == "1":
        source = ask("واژهٔ مبدأ: ")
        target = ask("ترجمه: ")
        source_lang = ask("زبان مبدأ (مثلاً en): ") or "en"
        target_lang = ask("زبان مقصد (مثلاً fa): ") or "fa"
        if source and target:
            add_glossary_term(source, target, source_lang, target_lang, user["id"])
            print("واژه ثبت شد.")
    elif choice == "2":
        for item in lookup_glossary(ask("واژه: ")):
            print(f"{item['source_term']} -> {item['target_term']}")


def menu_compare(user):
    old_path = read_path("مسیر نسخهٔ قدیمی: ")
    new_path = read_path("مسیر نسخهٔ جدید: ")
    if old_path is None or new_path is None:
        return
    try:
        old_result = analyze_contract(read_document(old_path))
        new_result = analyze_contract(read_document(new_path))
        diff = compare_documents(old_path, new_path)
    except Exception as error:
        print("خطا:", error)
        return

    changes = compare_clauses(old_result, new_result)
    print("\nتغییر وضعیت بندها:")
    print("\n".join(f"  {item}" for item in changes) or "  بدون تغییر")
    print(f"\nریسک: {old_result['risk_level']} -> {new_result['risk_level']}")
    print("\nتفاوت متن:")
    print(diff or "بدون تفاوت متنی")


def menu_analytics(user):
    print(json.dumps(contract_analytics(), ensure_ascii=False, indent=2))


def menu_review_text(user):
    print("متن را وارد کنید و برای پایان، خطی فقط با «.» بنویسید:")
    lines = []
    while True:
        line = ask("")
        if line == ".":
            break
        lines.append(line)

    text = "\n".join(lines)
    if not text.strip():
        print("متنی وارد نشده است.")
        return

    result, recommendations = review_text(text)
    print(f"\nزبان: {result['language']} | پوشش: {result['coverage_score']}/100 | "
          f"ریسک: {result['risk_level']}")
    for item in recommendations:
        print(f"- {item['message']}")
    print(DISCLAIMER)


def menu_export(user):
    contract_id = ask_contract_id()
    if contract_id is None:
        return
    _, result = load_result(contract_id)
    if result is None:
        return
    created = export_all(result, REPORT_DIR, f"contract_{contract_id}")
    print("فایل‌های ساخته‌شده:")
    for path in created:
        print(" ", path)


def run_menu():
    user = interactive_login()
    if user is None:
        return

    actions = {
        "1": menu_analyze,
        "2": menu_list,
        "3": menu_search,
        "4": menu_show,
        "5": menu_notes_tags,
        "6": menu_archive,
        "7": menu_obligations,
        "8": menu_rules,
        "9": menu_checklist,
        "10": menu_glossary,
        "11": menu_compare,
        "12": menu_analytics,
        "13": menu_review_text,
        "14": menu_export,
    }

    menu_text = """
1.  تحلیل و ذخیرهٔ فایل جدید
2.  فهرست قراردادها
3.  جستجوی قرارداد
4.  نمایش نتیجهٔ تحلیل
5.  یادداشت و برچسب
6.  بایگانی یا بازیابی
7.  تعهدات
8.  قواعد چک‌لیست
9.  اجرای چک‌لیست
10. واژه‌نامهٔ حقوقی
11. مقایسهٔ دو نسخه
12. آمار کلی
13. بررسی متن وارد شده
14. خروجی گزارش (Markdown / JSON / PDF)
0.  خروج
"""

    try:
        while True:
            if get_user_by_token(user["token"]) is None:
                print("نشست منقضی شده است. دوباره وارد شوید.")
                break

            print(menu_text)
            choice = ask("انتخاب: ")

            if choice == "0":
                break

            action = actions.get(choice)
            if action is None:
                print("گزینهٔ نامعتبر است.")
                continue

            try:
                action(user)
            except Exception as error:
                print("خطا:", error)
    finally:
        delete_session(user["token"])
        audit_log("logout", user["username"], user["id"])
        print("خروج انجام شد.")


def main():
    initialize_database()
    parser = build_arg_parser()
    args = parser.parse_args()

    has_cli_action = any([
        args.files, args.compare, args.list_contracts, args.checklist is not None,
        args.add_rule, args.add_obligation, args.list_obligations is not None,
        args.analytics,
    ])

    if has_cli_action:
        run_cli(args)
    else:
        run_menu()


if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nخروج.")