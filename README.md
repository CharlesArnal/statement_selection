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
| `mit_books/` | 69 MIT OCW textbooks (TeX/PDF/markdown) |
| `mathlib/` | Lean 4 mathlib submodule |
