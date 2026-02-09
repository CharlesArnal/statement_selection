- Add algebraic stack content

- Run Claude on Garrett's building, the AlgebraicStack and spectral methods for data science
    - Try to write some utilities for pdf extraction.

- Remove pdf from github?
 
- [Vivien] Finish the pipeline to extract all the MIT OCW content.
    - See `mit_ocw/README.md`.
    - Is the following up-to-date: http://leanprover-community.github.io/undergrad_todo.html. If so, we could use it to grade the quality of textbooks.

- Write utilities to find arxiv sources that are under CC-by-4 licenses
    - First version in search_arxiv.py

- Write utilities to OCR the pdf we have
    - By default Claude try to use poppler or various pdf utils libraries in python, would be nice to ask it to write a script and to inspect if this is sufficient for what we want to do (run claude again to see how feasible the formalization task is). We may want to use Mathpix, or other OCR tools specialized for math.
