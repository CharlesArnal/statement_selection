- Run Claude to see what is alreday in mathlib for all the books.
- From these, choose a set of 50 statements to send to the annotators.

#### OCR pipeline on all the books
- Add all the textbook we had from the list.
    - Add algebraic stack content.
    - Add OpenLogicProject.
- Run the pipeline for all of them.

#### Find a good sources for the 1000 theorems, and the missing undergrad math from mathlib
- Is the following up-to-date: http://leanprover-community.github.io/undergrad_todo.html. If so, we could use it to grade the quality of textbooks.

#### Extract Textbook from Arxiv
- Run the search arxiv.

#### OCR improvement

- The building books shows that OCR often write z ∈ Y and not $z \in Y$, which is fine in markdown, but we may use the latter option.
- Some books have unicode symbols.

Missing OCR:
- `advanced_partial_differential_equations_with_applications`: 29 PDFs present but no `.md` output. Needs GPU/marker-pdf to OCR.