#!/usr/bin/env python3
"""
Cross-reference MIT OCW books against the ~1000 missing theorems from
the Lean community's 1000+ theorems project.

Reads:
  - mathlib_coverage/mathlib/docs/1000.yaml   (theorem formalization status)
  - mit_books/*/short_assessment.md
  - mit_books/*/all_statements.md
  - mit_books/*/detailed_assessment.md

Outputs a markdown report to stdout (and optionally to 1000_theorems_analysis.md).
"""

import re
import sys
import unicodedata
from collections import defaultdict
from pathlib import Path

import yaml

# ── Constants ────────────────────────────────────────────────────────────────

YAML_PATH = Path("../mathlib_coverage/mathlib/docs/1000.yaml")
BOOKS_DIR = Path("../mit_books")
OUTPUT_FILE = Path("1000_theorems_analysis.md")


# ── Step 1: Parse missing theorems from YAML ────────────────────────────────

def load_missing_theorems(yaml_path: Path) -> list[dict]:
    """Return list of dicts with keys 'id', 'title' for theorems without decl/decls."""
    with open(yaml_path) as f:
        data = yaml.safe_load(f)

    missing = []
    for qid, entry in data.items():
        if "decl" not in entry and "decls" not in entry:
            missing.append({"id": qid, "title": entry.get("title", "")})
    return missing


def load_all_theorems(yaml_path: Path) -> list[dict]:
    """Return all theorems with their formalization status."""
    with open(yaml_path) as f:
        data = yaml.safe_load(f)

    theorems = []
    for qid, entry in data.items():
        formalized = "decl" in entry or "decls" in entry
        theorems.append({
            "id": qid,
            "title": entry.get("title", ""),
            "formalized": formalized,
        })
    return theorems


# ── Step 2: Parse book assessments ───────────────────────────────────────────

def parse_short_assessment(filepath: Path) -> list[dict]:
    """
    Parse a short_assessment.md file, handling four formats:
      A: **Status**: included / non-included / not included
      B: 1. ... - included / - non-included  (inline dash)
      C: | ... | included | / | ... | non-included |  (table)
      D: Statement header line, then 'included' or 'non-included' on next non-blank line
      E: Assessment: included / non-included
      F: — included / — non-included  (em-dash)
    Returns list of dicts with 'name', 'status', 'number'.
    """
    text = filepath.read_text(encoding="utf-8", errors="replace")
    lines = text.split("\n")
    results = []
    statement_num = 0

    # Detect format by scanning first 30 non-empty lines
    sample = "\n".join(lines[:80])

    if re.search(r"\*\*Status\*\*\s*:", sample):
        # Format A: **Status**: included
        current_name = ""
        for line in lines:
            header = re.match(r"^##\s+Statement\s+(\d+)\s*:\s*(.*)", line)
            if header:
                statement_num = int(header.group(1))
                current_name = header.group(2).strip()
                continue
            status_match = re.match(r"\*\*Status\*\*\s*:\s*(.*)", line)
            if status_match and current_name:
                raw = status_match.group(1).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": current_name, "status": status, "number": statement_num})
                current_name = ""

    elif re.search(r"^\|.*\|.*\|", sample, re.MULTILINE):
        # Format C: table rows  | # | Statement | Assessment/Status |
        # Handle multiple status formats:
        #   | 1 | Statement | included |
        #   | 1 | Statement | **Included** |
        #   | 1 | Statement | Yes |
        #   | 1 | Line | Type | Name | Yes |
        #   | Def 1 | Statement | **Included** |
        for line in lines:
            # Match: | number-or-id | ... | status |
            m = re.match(
                r"^\|\s*(?:(?:Def|Thm|Cor|Lem|Prop|Rmk|Ex)\s+)?(\d+)\s*\|\s*(.*?)\s*\|\s*\*?\*?(included|non-included|not included|yes|no|n/a|partial|partially included)\*?\*?\s*\|",
                line, re.IGNORECASE
            )
            if m:
                statement_num = int(m.group(1))
                name = m.group(2).strip()
                # Remove intermediate table columns
                parts = [p.strip() for p in name.split("|")]
                name = parts[-1] if parts else name
                raw = m.group(3).strip().lower().strip("*")
                status = "included" if raw in ("included", "yes") else "non-included"
                results.append({"name": name, "status": status, "number": statement_num})

    elif re.search(r"^\d+\.\s+.*\s+-\s+(included|non-included)", sample, re.MULTILINE):
        # Format B: numbered list with inline dash
        for line in lines:
            m = re.match(r"^\d+\.\s+(.*?)\s+-\s+(included|non-included|not included)", line, re.IGNORECASE)
            if m:
                statement_num += 1
                name = m.group(1).strip()
                raw = m.group(2).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": name, "status": status, "number": statement_num})

    elif re.search(r"^\d+\.\s+.*\s+—\s+(included|non-included)", sample, re.MULTILINE):
        # Format F: numbered list with em-dash
        for line in lines:
            m = re.match(r"^\d+\.\s+(.*?)\s+—\s+(included|non-included|not included)", line, re.IGNORECASE)
            if m:
                statement_num += 1
                name = m.group(1).strip()
                raw = m.group(2).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": name, "status": status, "number": statement_num})

    elif re.search(r"Assessment\s*:\s*(included|non-included)", sample, re.IGNORECASE):
        # Format E: Assessment: included
        current_name = ""
        for line in lines:
            header = re.match(r"^##\s+Statement\s+(\d+)\s*:\s*(.*)", line)
            if header:
                statement_num = int(header.group(1))
                current_name = header.group(2).strip()
                continue
            ass_match = re.match(r"Assessment\s*:\s*(.*)", line, re.IGNORECASE)
            if ass_match and current_name:
                raw = ass_match.group(1).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": current_name, "status": status, "number": statement_num})
                current_name = ""

    elif re.search(r"\*\*Statement\s+\d+\s*[—–-].*:\*\*\s*(included|non-included|not included)", sample, re.IGNORECASE):
        # Format G: **Statement N — Name:** included/non-included (bold inline, algebraic_geometry_i style)
        for line in lines:
            m = re.match(
                r"\*\*Statement\s+(\d+)\s*[—–-]\s*(.*?):\*\*\s*(included|non-included|not included)",
                line, re.IGNORECASE
            )
            if m:
                statement_num = int(m.group(1))
                name = m.group(2).strip()
                raw = m.group(3).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": name, "status": status, "number": statement_num})

    elif re.search(r"^-\s+.*:\s*(included|non-included|not included)\s*$", sample, re.MULTILINE | re.IGNORECASE):
        # Format H: bullet list with colon-separated status (representations_of_lie_groups style)
        # e.g. "- Proposition 1.6 (continuity of Banach representations): non-included"
        for line in lines:
            m = re.match(
                r"^-\s+(.*?):\s*(included|non-included|not included|partially included)\s*$",
                line.strip(), re.IGNORECASE
            )
            if m:
                statement_num += 1
                name = m.group(1).strip()
                raw = m.group(2).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": name, "status": status, "number": statement_num})

    else:
        # Format D: header line followed by status on next non-blank line
        # Also handles:
        #   "## Statement N (Name) — included"  (heading with em-dash)
        #   "**Statement N — Name:** included"   (bold inline)
        #   "1. **Theorem 7 (Miller)** [line 96]: non-included"
        #   "Statement N (Name):\n included"
        #   "Theorem 1.2 [Baker's Theorem]:\nincluded"
        i = 0
        while i < len(lines):
            line = lines[i].strip()

            # Check heading with em-dash: "## Statement N (Name) — included"
            m_heading_dash = re.match(
                r"^##\s+Statement\s+(\d+)\s*(?:\(.*?\))?\s*[—–-]\s*(included|non-included|not included)\s*$",
                line, re.IGNORECASE
            )
            if not m_heading_dash:
                # Also try: ## Statement N (Name) — included
                m_heading_dash = re.match(
                    r"^##\s+Statement\s+(\d+)\s+\(([^)]*)\)\s*[—–-]\s*(included|non-included|not included)\s*$",
                    line, re.IGNORECASE
                )
                if m_heading_dash:
                    statement_num = int(m_heading_dash.group(1))
                    name = m_heading_dash.group(2).strip()
                    raw = m_heading_dash.group(3).strip().lower()
                    status = "included" if raw == "included" else "non-included"
                    results.append({"name": name, "status": status, "number": statement_num})
                    i += 1
                    continue
            else:
                statement_num = int(m_heading_dash.group(1))
                name = f"Statement {statement_num}"
                raw = m_heading_dash.group(2).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": name, "status": status, "number": statement_num})
                i += 1
                continue

            # Check bold inline: "**Statement N — Name:** included"
            m_bold = re.match(
                r"\*\*Statement\s+(\d+)\s*[—–-]\s*(.*?):\*\*\s*(included|non-included|not included)",
                line, re.IGNORECASE
            )
            if m_bold:
                statement_num = int(m_bold.group(1))
                name = m_bold.group(2).strip()
                raw = m_bold.group(3).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": name, "status": status, "number": statement_num})
                i += 1
                continue

            # Check for numbered bold format: "1. **Theorem 7 (Miller)** [line 96]: non-included"
            m_numbered = re.match(
                r"^(\d+)\.\s+\*\*(.*?)\*\*.*?:\s*(included|non-included|not included)\s*$",
                line, re.IGNORECASE
            )
            if m_numbered:
                statement_num = int(m_numbered.group(1))
                name = m_numbered.group(2).strip()
                raw = m_numbered.group(3).strip().lower()
                status = "included" if raw == "included" else "non-included"
                results.append({"name": name, "status": status, "number": statement_num})
                i += 1
                continue

            # Check if this is a statement/theorem header line
            header_m = re.match(
                r"^(?:(?:Statement|Theorem|Lemma|Proposition|Corollary|Definition|Remark|Claim|Conjecture|Axiom|Exercise|Example|Scholium|Fact|Problem|Question|Rule|Observation|Property|Note|Result)\b.*)",
                line, re.IGNORECASE
            )
            if header_m:
                name = re.sub(r":$", "", line).strip()
                # look for status on next non-blank line
                j = i + 1
                while j < len(lines) and lines[j].strip() == "":
                    j += 1
                if j < len(lines):
                    status_line = lines[j].strip().lower()
                    if status_line in ("included", "non-included", "not included",
                                       "non included", "not-included"):
                        statement_num += 1
                        status = "included" if status_line == "included" else "non-included"
                        results.append({"name": name, "status": status, "number": statement_num})
                        i = j + 1
                        continue
            i += 1

    return results


def parse_all_books(books_dir: Path) -> dict:
    """
    Parse all book directories.
    Returns dict: book_name -> {
        'statements': [...],   # from short_assessment
        'total': int,
        'included': int,
        'non_included': int,
        'all_statements_text': str,
        'detailed_text': str,
        'short_text': str,
    }
    """
    books = {}
    for entry in sorted(books_dir.iterdir()):
        if not entry.is_dir():
            continue
        book_name = entry.name
        short_path = entry / "short_assessment.md"
        all_path = entry / "all_statements.md"
        detailed_path = entry / "detailed_assessment.md"

        if not short_path.exists():
            continue

        statements = parse_short_assessment(short_path)
        total = len(statements)
        included = sum(1 for s in statements if s["status"] == "included")
        non_included = total - included

        all_text = all_path.read_text(encoding="utf-8", errors="replace") if all_path.exists() else ""
        detailed_text = detailed_path.read_text(encoding="utf-8", errors="replace") if detailed_path.exists() else ""
        short_text = short_path.read_text(encoding="utf-8", errors="replace")

        books[book_name] = {
            "statements": statements,
            "total": total,
            "included": included,
            "non_included": non_included,
            "all_statements_text": all_text,
            "detailed_text": detailed_text,
            "short_text": short_text,
        }
    return books


# ── Step 3: Cross-reference via keyword matching ────────────────────────────

# Common words to ignore when extracting keywords from theorem names
STOPWORDS = {
    "theorem", "lemma", "conjecture", "inequality", "formula", "principle",
    "law", "property", "rule", "problem", "equation", "the", "of", "for",
    "and", "in", "on", "a", "an", "is", "by", "to", "with", "from", "that",
    "about", "over", "s", "first", "second", "third", "last", "number",
    "existence", "uniqueness", "theory", "analysis",
    "generalization", "generalized", "fundamental", "general",
    "complex", "real", "linear", "set", "space", "group", "ring",
    "field", "function", "functions", "point", "points", "line",
    "dimension", "ii", "iii", "iv", "finite", "infinite", "positive",
    "negative", "zero", "one", "two", "three", "four", "algebra",
    "algebraic", "differential", "topological", "geometric",
    "analytic", "continuous", "smooth",
}

# Words that are too common to use as sole keywords (will match everything)
TOO_GENERIC_ALONE = {
    "prime", "factor", "fixed", "closed", "open", "inverse", "dual",
    "normal", "simple", "free", "base", "change", "extension",
    "covering", "mapping", "structure", "classification", "max", "min",
    "odd", "even", "bounded", "compact", "complete", "dense", "convergence",
    "monotone", "absolute", "addition", "multiplication", "quotient",
    "subspace", "curve", "surface", "graph", "spectral", "critical",
    "initial", "final", "value", "mean", "power", "rank", "constant",
    "residue", "gradient", "preimage", "range", "rotation",
    "reflection", "projection",
    # Common English words that are also mathematician names
    "ore", "lie", "cap", "may", "rice", "cox", "young", "bell",
    "stone", "moore", "hall", "ford", "hardy", "mann", "low",
    "wall", "fan", "cole", "love", "long", "hand", "cross",
}


def _strip_accents(s: str) -> str:
    """Remove diacritics/accents from a string: Szemerédi -> Szemeredi."""
    return "".join(
        c for c in unicodedata.normalize("NFD", s)
        if unicodedata.category(c) != "Mn"
    )


def extract_search_terms(title: str) -> dict:
    """
    Extract search terms from a theorem title.
    Returns dict with:
      - 'exact_names': exact name phrases to search (highest priority)
      - 'proper_names': proper name keywords (e.g., Gauss, Ramsey)
      - 'keywords': all non-stop keywords
    """
    clean = _strip_accents(title)
    # Remove parenthetical qualifiers like "(differential geometry)"
    clean_no_parens = re.sub(r'\s*\(.*?\)\s*', ' ', clean).strip()

    # Build exact name phrases (the most precise search)
    exact_names = set()
    # Full title (without parens)
    exact_names.add(clean_no_parens.lower().strip())
    # Also without possessive
    no_poss_title = re.sub(r"['']s\b", "", clean_no_parens)
    no_poss_title = re.sub(r'\s+', ' ', no_poss_title).strip()
    if no_poss_title.lower() != clean_no_parens.lower():
        exact_names.add(no_poss_title.lower())
    # Title without "theorem", "conjecture" etc.
    for base in [clean_no_parens, no_poss_title]:
        reduced = base
        for suffix in ["theorem", "conjecture", "lemma", "formula", "inequality",
                       "principle", "law", "problem"]:
            reduced = re.sub(r'\b' + suffix + r'\b', '', reduced, flags=re.IGNORECASE)
        reduced = re.sub(r'\s+', ' ', reduced).strip().strip(" -–—'',.")
        if len(reduced) >= 4 and reduced.lower() not in exact_names:
            exact_names.add(reduced.lower())
    # Sort by length descending (prefer longer, more specific matches first)
    exact_names = sorted(exact_names, key=len, reverse=True)

    # Remove possessives for name extraction
    no_poss = re.sub(r"['']s\b", "", clean)
    tokens = re.split(r"[^a-zA-Z]+", no_poss)

    # Extract proper names: tokens that start with uppercase and aren't stopwords
    proper_names = []
    for t in tokens:
        t_lower = t.lower()
        if (len(t_lower) >= 3 and t_lower not in STOPWORDS
                and t_lower not in TOO_GENERIC_ALONE
                and t[0].isupper()):
            proper_names.append(t_lower)

    # All non-stop keywords
    keywords = []
    for t in tokens:
        t_lower = t.lower().strip()
        if len(t_lower) >= 3 and t_lower not in STOPWORDS:
            keywords.append(t_lower)

    return {
        "exact_names": exact_names,
        "proper_names": proper_names,
        "keywords": keywords,
    }


def _word_boundary_search(keyword: str, text: str) -> bool:
    """Check if keyword appears as a whole word in text (case-insensitive, accent-stripped)."""
    text = _strip_accents(text)
    return bool(re.search(r'\b' + re.escape(keyword) + r'\b', text, re.IGNORECASE))


def _word_boundary_line_search(keyword: str, line: str) -> bool:
    """Check if keyword appears as a whole word in a single line (accent-stripped)."""
    line = _strip_accents(line)
    return bool(re.search(r'\b' + re.escape(keyword) + r'\b', line, re.IGNORECASE))


def search_book_for_theorem(search_terms: dict, book_data: dict) -> list[dict]:
    """
    Search a book's texts for mentions of a theorem.
    Priority:
      1. Exact name match (full title or reduced name as substring)
      2. Proper name match — only if ALL proper names co-occur on same line
         AND there are ≥2 proper names or the single name is distinctive
    Returns list of matches with context.
    """
    exact_names = search_terms["exact_names"]
    proper_names = search_terms["proper_names"]

    if not exact_names and not proper_names:
        return []

    matches = []
    found_exact = False

    for source_name, text_key in [
        ("all_statements", "all_statements_text"),
        ("detailed", "detailed_text"),
        ("short", "short_text"),
    ]:
        text = book_data[text_key]
        if not text:
            continue

        text_stripped = _strip_accents(text)
        lines_stripped = text_stripped.split("\n")
        lines_original = text.split("\n")

        # Strategy 1: exact name phrase search
        for name in exact_names:
            # Use word-boundary matching to avoid substring false positives
            # Build pattern with word boundaries on each side
            pat = re.compile(r'\b' + re.escape(name) + r'\b', re.IGNORECASE)
            for i, (line_s, line_o) in enumerate(zip(lines_stripped, lines_original)):
                if pat.search(line_s):
                    found_exact = True
                    matches.append({
                        "source": source_name,
                        "line_num": i + 1,
                        "line": line_o.strip()[:200],
                        "matched_keywords": [name],
                        "match_quality": "exact",
                    })

    # Strategy 2: proper name fallback (only if no exact matches found)
    if not found_exact and proper_names and len(proper_names) >= 2:
        for source_name, text_key in [
            ("all_statements", "all_statements_text"),
            ("detailed", "detailed_text"),
            ("short", "short_text"),
        ]:
            text = book_data[text_key]
            if not text:
                continue

            text_stripped = _strip_accents(text)
            lines_stripped = text_stripped.split("\n")
            lines_original = text.split("\n")

            kw_patterns = {kw: re.compile(r'\b' + re.escape(kw) + r'\b', re.IGNORECASE)
                           for kw in proper_names}

            for i, (line_s, line_o) in enumerate(zip(lines_stripped, lines_original)):
                matching = [kw for kw, pat in kw_patterns.items() if pat.search(line_s)]
                if len(matching) >= len(proper_names):
                    matches.append({
                        "source": source_name,
                        "line_num": i + 1,
                        "line": line_o.strip()[:200],
                        "matched_keywords": matching,
                        "match_quality": "proper_name",
                    })

    return matches


def find_statement_status_for_match(match_line: str, book_data: dict) -> str | None:
    """Try to determine if a matched line corresponds to an included or non-included statement."""
    line_lower = match_line.lower().strip()
    for stmt in book_data["statements"]:
        # Check if the statement name appears in the matched line
        if stmt["name"].lower() in line_lower or line_lower in stmt["name"].lower():
            return stmt["status"]
    return None


def cross_reference(missing: list[dict], books: dict) -> list[dict]:
    """
    For each missing theorem, search all books for matches.
    Returns list of dicts with 'theorem', 'matches' (list of book matches).
    """
    results = []
    for theorem in missing:
        search_terms = extract_search_terms(theorem["title"])
        if not search_terms["exact_names"] and not search_terms["proper_names"]:
            continue

        theorem_matches = []
        for book_name, book_data in books.items():
            book_matches = search_book_for_theorem(search_terms, book_data)
            if book_matches:
                # Determine statement status from best match
                status = None
                best_line = ""
                best_quality = ""
                for m in book_matches:
                    s = find_statement_status_for_match(m["line"], book_data)
                    if s:
                        status = s
                        best_line = m["line"]
                        best_quality = m.get("match_quality", "")
                        break
                    if not best_line:
                        best_line = m["line"]
                        best_quality = m.get("match_quality", "")

                theorem_matches.append({
                    "book": book_name,
                    "status": status,
                    "best_line": best_line,
                    "match_count": len(book_matches),
                    "match_quality": best_quality,
                })

        if theorem_matches:
            results.append({
                "id": theorem["id"],
                "title": theorem["title"],
                "search_terms": search_terms,
                "matches": theorem_matches,
            })

    return results

    return results


# ── Step 4: Generate report ─────────────────────────────────────────────────

def extract_key_topics(book_data: dict, max_topics: int = 5) -> str:
    """Extract a few key topic words from a book's statement names."""
    names = [s["name"] for s in book_data["statements"]]
    # Count named theorems
    named = []
    for name in names:
        # Extract named theorem parts like "(Gauss-Bonnet theorem)"
        paren = re.findall(r"\(([^)]+)\)", name)
        for p in paren:
            named.append(p)
        # Also grab bracket names like "[Baker's Theorem]"
        bracket = re.findall(r"\[([^\]]+)\]", name)
        for b in bracket:
            named.append(b)
    if named:
        return "; ".join(named[:max_topics])
    # Fallback: use first few statement names
    short_names = [n[:50] for n in names[:max_topics]]
    return "; ".join(short_names)


def generate_report(
    missing: list[dict],
    all_theorems: list[dict],
    books: dict,
    cross_ref: list[dict],
) -> str:
    out = []
    out.append("# Cross-Reference: MIT Books vs 1000+ Missing Theorems\n")
    out.append(f"**Total theorems in 1000.yaml**: {len(all_theorems)}")
    formalized = sum(1 for t in all_theorems if t["formalized"])
    out.append(f"**Formalized (has decl/decls)**: {formalized}")
    out.append(f"**Missing (no decl/decls)**: {len(missing)}")
    out.append(f"**Books analyzed**: {len(books)}")
    out.append(f"**Missing theorems found in books**: {len(cross_ref)}")
    out.append("")

    # ── Section A: Book Rankings ──
    out.append("## Section A — Book Rankings (sorted by non-included count)\n")
    out.append("| # | Book | Total | Included | Non-included | % Coverage | Key Topics |")
    out.append("|---|------|-------|----------|--------------|------------|------------|")

    sorted_books = sorted(books.items(), key=lambda x: x[1]["non_included"], reverse=True)
    for rank, (name, data) in enumerate(sorted_books, 1):
        pct = f"{data['included'] / data['total'] * 100:.0f}%" if data["total"] > 0 else "N/A"
        topics = extract_key_topics(data, max_topics=3)
        # Truncate topics to fit
        if len(topics) > 80:
            topics = topics[:77] + "..."
        out.append(
            f"| {rank} | {name} | {data['total']} | {data['included']} | "
            f"{data['non_included']} | {pct} | {topics} |"
        )
    out.append("")

    # ── Section B: Missing 1000 Theorems Found in Books ──
    out.append("## Section B — Missing 1000 Theorems Found in Books\n")
    out.append("| # | Missing Theorem | Wikidata | Book(s) | Status | Best Match |")
    out.append("|---|----------------|----------|---------|--------|------------|")

    # Sort by number of book matches (most matches first)
    sorted_xref = sorted(cross_ref, key=lambda x: len(x["matches"]), reverse=True)
    for i, entry in enumerate(sorted_xref, 1):
        books_str = ", ".join(m["book"] for m in entry["matches"][:3])
        if len(entry["matches"]) > 3:
            books_str += f" (+{len(entry['matches']) - 3} more)"

        # Pick best status
        statuses = [m["status"] for m in entry["matches"] if m["status"]]
        status_str = statuses[0] if statuses else "unknown"

        best_line = entry["matches"][0]["best_line"][:80]
        # Escape pipes in the line
        best_line = best_line.replace("|", "\\|")

        out.append(
            f"| {i} | {entry['title']} | {entry['id']} | {books_str} | "
            f"{status_str} | {best_line} |"
        )
    out.append("")

    # ── Section C: Top Recommended Books ──
    out.append("## Section C — Top Recommended Books\n")
    out.append("Books ranked by how many **missing 1000-list theorems** they cover:\n")

    # Count per book how many missing theorems are matched
    book_missing_count = defaultdict(list)
    for entry in cross_ref:
        for m in entry["matches"]:
            book_missing_count[m["book"]].append(entry["title"])

    sorted_recs = sorted(book_missing_count.items(), key=lambda x: len(x[1]), reverse=True)
    out.append("| # | Book | Missing Theorems Covered | Non-included Stmts | Example Theorems |")
    out.append("|---|------|------------------------|-------------------|------------------|")
    for rank, (book_name, theorem_list) in enumerate(sorted_recs[:25], 1):
        non_incl = books[book_name]["non_included"] if book_name in books else "?"
        examples = "; ".join(theorem_list[:3])
        if len(examples) > 80:
            examples = examples[:77] + "..."
        out.append(
            f"| {rank} | {book_name} | {len(theorem_list)} | {non_incl} | {examples} |"
        )
    out.append("")

    # ── Summary statistics ──
    out.append("## Summary\n")
    total_non_included = sum(b["non_included"] for b in books.values())
    total_included = sum(b["included"] for b in books.values())
    total_stmts = sum(b["total"] for b in books.values())
    out.append(f"- **Total statements across all books**: {total_stmts}")
    out.append(f"- **Total included (in Mathlib)**: {total_included}")
    out.append(f"- **Total non-included**: {total_non_included}")
    out.append(f"- **Overall coverage**: {total_included / total_stmts * 100:.1f}%" if total_stmts else "")
    out.append(f"- **Missing 1000-list theorems found in at least one book**: {len(cross_ref)} / {len(missing)}")
    out.append("")

    return "\n".join(out)


# ── Main ─────────────────────────────────────────────────────────────────────

def main():
    # Step 1: Load theorems
    if not YAML_PATH.exists():
        print(f"Error: {YAML_PATH} not found. Make sure the mathlib submodule is initialized.", file=sys.stderr)
        sys.exit(1)

    print("Loading theorems from YAML...", file=sys.stderr)
    missing = load_missing_theorems(YAML_PATH)
    all_theorems = load_all_theorems(YAML_PATH)
    print(f"  Total: {len(all_theorems)}, Formalized: {len(all_theorems) - len(missing)}, Missing: {len(missing)}", file=sys.stderr)

    # Step 2: Parse books
    if not BOOKS_DIR.exists():
        print(f"Error: {BOOKS_DIR} not found.", file=sys.stderr)
        sys.exit(1)

    print("Parsing book assessments...", file=sys.stderr)
    books = parse_all_books(BOOKS_DIR)
    print(f"  Parsed {len(books)} books", file=sys.stderr)
    for name, data in sorted(books.items(), key=lambda x: x[1]["non_included"], reverse=True)[:5]:
        print(f"    {name}: {data['total']} total, {data['included']} included, {data['non_included']} non-included", file=sys.stderr)

    # Step 3: Cross-reference
    print("Cross-referencing missing theorems against books...", file=sys.stderr)
    cross_ref = cross_reference(missing, books)
    print(f"  Found {len(cross_ref)} missing theorems in at least one book", file=sys.stderr)

    # Step 4: Generate report
    print("Generating report...", file=sys.stderr)
    report = generate_report(missing, all_theorems, books, cross_ref)

    # Write to file
    OUTPUT_FILE.write_text(report, encoding="utf-8")
    print(f"Report written to {OUTPUT_FILE}", file=sys.stderr)

    # Also print to stdout
    print(report)


if __name__ == "__main__":
    main()
