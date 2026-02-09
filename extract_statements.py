#!/usr/bin/env python3
"""Extract all theorem-like statements from the buildings book PDF."""

import pdfplumber
import re

pdf = pdfplumber.open('/Users/vivc/code/Lean/statement_selection/buildings/book.pdf')

full_text = ""
for i, page in enumerate(pdf.pages):
    text = page.extract_text()
    if text:
        full_text += f"\n=== PAGE {i+1} ===\n{text}\n"

pdf.close()

# Save full text for reference
with open('/Users/vivc/code/Lean/statement_selection/buildings/full_text.txt', 'w') as f:
    f.write(full_text)

# Find all statement-like patterns
# Looking for: Theorem, Lemma, Proposition, Corollary (with optional numbering and names)
pattern = r'(Theorem|Lemma|Proposition|Corollary|Remark)\s*[\d.]*\s*[^:]*:'
matches = []
for m in re.finditer(pattern, full_text):
    # Get some context
    start = max(0, m.start() - 50)
    end = min(len(full_text), m.end() + 200)
    context = full_text[start:end]
    # Find which page this is on
    page_matches = list(re.finditer(r'=== PAGE (\d+) ===', full_text[:m.start()]))
    page = int(page_matches[-1].group(1)) if page_matches else 0
    matches.append((page, m.group(0), context))

print(f"Total pages: {len(pdf.pages)}")
print(f"Found {len(matches)} potential statements\n")
for page, match, context in matches:
    print(f"Page {page}: {match.strip()}")
    print(f"  Context: {context.strip()[:200]}")
    print()
