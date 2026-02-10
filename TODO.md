- Run the OCR on a cluster.

Ask Claude to inspect the work.
Were there error, if so were do they come from.
How can we fix them.


```md
I have run an OCR pipeline. I have extracted ressources online in `ocr_mit/unzipped`.
I have then tried to copy the best pdf sources into `mit_books`/
I have then OCR these books.
However, I have noticed some mistakes in my pipeline.
Let's take for example Algebra 1 (`mit_books/algebra_i_student_notes`), the OCR is poor quality. Moreover the book.pdf stops early. I can map it back to the `ocr_mit/unzipped/RES.18-011-fall-2021` (thanks to the `3_list_of_first_candidates.md`). I see that I did not took the full book, which should have been `mit18_701f21_full_lec_new.pdf`.
Can you review all my OCR books in `mit_books` and check for mistakes. If you find some, can you go back to the root of the problem. Can you then fix these mistakes?
```

When we have the full tex sources.
Prefer the tex sources over the OCR path.

```md
I have run an OCR pipeline. I have extracted ressources online in `ocr_mit/unzipped`.
I have then tried to copy the best pdf sources into `mit_books`/
I have then OCR these books.
However for some books I have some tex files that should have authority over my OCR pipeline.
Let's take for example Algebra 1 (`mit_books/algebra_i_student_notes`), I can map it back to the `ocr_mit/unzipped/RES.18-011-fall-2021` (thanks to the `3_list_of_first_candidates.md`).
I see that the tex files exists there.
Can you review all my OCR books in `mit_books` and check for the ones where I actually have the tex files. Can you list those? And update the content in `mit_books` to put the tex files there instead?
```

- Run Claude to see what is alreday in mathlib.


- Add algebraic stack content

- Run Claude on all the MIT books content.

- Run Claude on Garrett's building, the AlgebraicStack and spectral methods for data science
    - Try to write some utilities for pdf extraction.
 
- [Vivien] Finish the pipeline to extract all the MIT OCW content.
    - See `mit_ocw/README.md`.
    - Is the following up-to-date: http://leanprover-community.github.io/undergrad_todo.html. If so, we could use it to grade the quality of textbooks.

- Write utilities to find arxiv sources that are under CC-by-4 licenses
    - First version in search_arxiv.py

#### OCR improvement

- [BEING DONE] For the autoformalization pipeline, we may want to add an LLM back-end to pdf-marker in `extract_pdf.py`. We may need to wrap the llama API service in `marker/services/openai.py` in order to use our Llama API key.
- The building books shows that OCR often write z ∈ Y and not $z \in Y$, which is fine in markdown, but we may use the latter option.

#### List of Mistake

**Algebra 1:**
Wrong full pdf was taken.
We have tex sources.
