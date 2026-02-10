- Run Claude to see what is alreday in mathlib for all the books.

- Redo the full pipeline for the books that were flagged as "Bad candidate"


- Add algebraic stack content

- Run Claude on all the MIT books content.

- Run Claude on Garrett's building, the AlgebraicStack and spectral methods for data science
    - Try to write some utilities for pdf extraction.
 
- [Vivien] Finish the pipeline to extract all the MIT OCW content.
    - See `mit_ocw/README.md`.
    - Is the following up-to-date: http://leanprover-community.github.io/undergrad_todo.html. If so, we could use it to grade the quality of textbooks.

- Write utilities to find arxiv sources that are under CC-by-4 licenses
    - First version in search_arxiv.py

#### Preselection improvement

Some books were rejected by my LLM pipeline as too sparse to be good for autoformalization, when this is sometimes debatable.

#### OCR improvement

- The building books shows that OCR often write z ∈ Y and not $z \in Y$, which is fine in markdown, but we may use the latter option.
- Some books have unicode symbols.


Missing OCR:
- `advanced_partial_differential_equations_with_applications`: 29 PDFs present but no `.md` output. Needs GPU/marker-pdf to OCR.