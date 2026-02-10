- Add algebraic stack content

- Run Claude on Garrett's building, the AlgebraicStack and spectral methods for data science
    - Try to write some utilities for pdf extraction.

- Remove pdf from github?
 
- [Vivien] Finish the pipeline to extract all the MIT OCW content.
    - See `mit_ocw/README.md`.
    - Is the following up-to-date: http://leanprover-community.github.io/undergrad_todo.html. If so, we could use it to grade the quality of textbooks.

- Write utilities to find arxiv sources that are under CC-by-4 licenses
    - First version in search_arxiv.py

#### OCR improvement

- For the autoformalization pipeline, we may want to add an LLM back-end to pdf-marker in `extract_pdf.py`. We may need to wrap the llama API service in `marker/services/openai.py` in order to use our Llama API key.