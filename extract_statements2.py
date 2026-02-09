#!/usr/bin/env python3
"""Extract all theorem-like statements from the buildings book PDF, more carefully."""

import pdfplumber
import re

pdf = pdfplumber.open('/Users/vivc/code/Lean/statement_selection/buildings/book.pdf')

full_text = ""
page_texts = {}
for i, page in enumerate(pdf.pages):
    text = page.extract_text()
    if text:
        page_texts[i+1] = text
        full_text += f"\n=== PAGE {i+1} ===\n{text}\n"

pdf.close()

# We'll search page by page, looking for statement beginnings
# Statements typically start at the beginning of a line or after a paragraph break
# Pattern: "Theorem:", "Lemma:", "Proposition:", "Corollary:", possibly with numbering
# But NOT in table of contents (pages 1-6) or index/bibliography

statements = []
for page_num in range(7, 346):  # Skip TOC and bibliography/index
    if page_num not in page_texts:
        continue
    text = page_texts[page_num]

    # Find statement headers - these are typically standalone or start a paragraph
    # Look for patterns like:
    # "Theorem:" "Lemma:" "Proposition:" "Corollary:"
    # "Theorem 3.1:" "Lemma 3.2.1:" etc.
    # "Theorem: [Foo's theorem]" etc.
    patterns = [
        r'(?:^|\n)\s*(Theorem\s*[\d.]*\s*(?:\[.*?\])?\s*:)',
        r'(?:^|\n)\s*(Lemma\s*[\d.]*\s*(?:\[.*?\])?\s*:)',
        r'(?:^|\n)\s*(Proposition\s*[\d.]*\s*(?:\[.*?\])?\s*:)',
        r'(?:^|\n)\s*(Corollary\s*[\d.]*\s*(?:\[.*?\])?\s*:)',
    ]

    for pat in patterns:
        for m in re.finditer(pat, text):
            # Get statement text (up to the proof or next statement or end of reasonable length)
            start = m.start()
            # Get text after the match, up to "Proof:" or next statement header or 1000 chars
            rest = text[m.end():]
            end_patterns = [r'\nProof', r'\n\s*Theorem', r'\n\s*Lemma', r'\n\s*Proposition', r'\n\s*Corollary', r'\n\s*Remark', r'♣']
            end_pos = len(rest)
            for ep in end_patterns:
                em = re.search(ep, rest)
                if em and em.start() < end_pos:
                    end_pos = em.start()

            stmt_text = m.group(1).strip() + " " + rest[:end_pos].strip()
            # Clean up
            stmt_text = ' '.join(stmt_text.split())

            statements.append({
                'page': page_num,
                'header': m.group(1).strip(),
                'text': stmt_text[:500]  # Cap at 500 chars
            })

print(f"Found {len(statements)} statements\n")
for i, s in enumerate(statements):
    print(f"{i+1}. [Page {s['page']}] {s['header']}")
    print(f"   {s['text'][:300]}")
    print()
