- Run Claude to see what is alreday in mathlib for all the books.
- From these, choose a set of 50 statements to send to the annotators.

#### OCR pipeline on all the books
- Add all the textbook we had from the list.
 - Add algebraic stack content.
 - Add OpenLogicProject.
- Run the pipeline for all of them.

#### Find a good sources for the 1000 theorems, and the missing undergrad math from mathlib
- Is the following up-to-date: http://leanprover-community.github.io/undergrad_todo.html. If so, we could use it to grade the quality of textbooks.
- **Done**: Ranked all MIT books against the undergrad TODO. See `mit_books/undergrad_todo_candidate_analysis.md` for the full tiered analysis and coverage matrix. Top 8 books identified.

#### Extract Textbook from Arxiv
- Run the search arxiv.

#### OCR improvement

- The building books shows that OCR often write z ∈ Y and not $z \in Y$, which is fine in markdown, but we may use the latter option.
- Some books have unicode symbols.

Missing OCR:
- `advanced_partial_differential_equations_with_applications`: 29 PDFs present but no `.md` output. Needs GPU/marker-pdf to OCR.


---

I want to extract 4 or 5 books to send to annotators for an autoformalization project. The goal would be that the annotators write the formal statements of some hard theorems that are not in mathlib, and for which reading the associated books should provide the informal context, which translated into formal context would yield the proof of the theorem. I have an assessment of the mathlib coverage of books for all the mit_books. Can you review all of them, and suggest some books that would provide some good coverage of math (like proba, stats, algebra, pde, ...). 
 
I have extracted assessment for all the books in mit_books. I want to know which one I should not bother formalizing as most of the content is already in mathlib. Can you do this for me? 

I have extracted assessment for all the books in mit_books. I want to know which books would be good candidates to fill in the missing undergrad math from mathlib: http://leanprover-community.github.io/undergrad_todo.html.

I have extracted assessment for all the books in mit_books. I want to know which books would be good candidates to fill in the missing 1000 theorems from mathlib: https://leanprover-community.github.io/1000.html

---

Put mathlib in the mathlib coverage stuffs.