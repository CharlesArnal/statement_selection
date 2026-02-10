# Statement Selection

Extract mathematical statements from textbooks and assess their coverage in [mathlib](https://github.com/leanprover-community/mathlib4).

## Pipeline

| Stage | Directory | Description |
|-------|-----------|-------------|
| 1 | `download_mit_ocw/` | Download, unzip, organize MIT OCW course materials |
| 2 | `ocr/` | Convert PDFs to LLM-friendly markdown |
| 3 | `mathlib_coverage/` | Template prompts for batch mathlib assessment |
| 4 | `arxiv/` | Harvest CC-BY-4.0 math textbooks from ArXiv |

## Key resources

| Path | Description |
|------|-------------|
| `instructions.md` | Detailed instructions for statement extraction |
| `selected_books_and_statements.md` | 5 selected books and 52 statements for annotation |
| `mit_books/` | 69 MIT OCW textbooks (TeX/PDF/markdown) |
| `mathlib_coverage/books_to_skip.md` | Tiered ranking of all 69 books by mathlib coverage |
| `mit_books/undergrad_todo_candidate_analysis.md` | Books ranked against mathlib undergrad TODO |
| `mathlib_coverage/mathlib/` | Lean 4 mathlib submodule |
