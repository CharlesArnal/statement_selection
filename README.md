# Statement Selection

Extract mathematical statements from textbooks and assess their coverage in [mathlib](https://github.com/leanprover-community/mathlib4).

## Preprocessing

The `mit_ocw/` directory contains scripts for downloading, unzipping, and organizing MIT OpenCourseWare materials. See [`mit_ocw/README.md`](mit_ocw/README.md) for details.

## Workflow

1. **`instructions.md`** — detailed instructions for extracting statements and checking mathlib.
2. **`initial_prompt.md`** — template prompt with a `{TEXTBOOK_LIST}` placeholder.
3. **`split_prompt.py X`** — splits the prompt into X batch files (`initial_prompt_batch_{1..X}.md`), each covering a subset of the textbooks. Each batch can be fed to a separate Claude Code instance to parallelize the work.

## Key directories

| Directory | Description |
|-----------|-------------|
| `mit_books/` | 69 MIT OCW textbooks (TeX/PDF sources) |
| `mathlib/` | Lean 4 mathlib submodule (v4.27.0) |
| `mit_ocw/` | Preprocessing pipeline |

## Other utilities

- **`extract_pdf.py`** — convert PDF files to markdown.
- **`search_arxiv.py`** — harvest CC-BY-4.0 math textbooks from ArXiv.
