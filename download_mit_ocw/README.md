
# MIT OpenCourseWare

This folder contains utilities to process content provided by the MIT on their OCW platform.

## Reproducing the Course Data

To download and organize the MIT OCW course PDFs from scratch, follow these steps.

### 1. Download the ZIP files

```bash
python download_mit_ocw/download_mit.py
```

This reads the course URLs from `download_mit_ocw/2_list_of_urls.md` and downloads each course's ZIP archive into `download_mit_ocw/zip_files/`.

### 2. Unzip the files

```bash
python download_mit_ocw/unzip_files.py
```

This extracts each ZIP into `download_mit_ocw/unzipped/<course-id>/`.

### 3. Organize courses into folders

```bash
python download_mit_ocw/organize_courses.py
```

This processes the 69 courses tagged as Good/Borderline/To-check in `download_mit_ocw/3_list_of_first_candidates.md` and creates a folder for each at the project root:

- **Single-PDF courses** (30): `<course_name>/book.pdf`
- **Multi-PDF courses** (39): `<course_name>/book/part1.pdf`, `part2.pdf`, ...

The script handles stripping OCW hash prefixes from filenames, deduplication, and sorting.

### 4. Extract PDF content

Convert the organized PDFs to LLM-friendly markdown using `ocr/extract_pdf.py`.

**Dependencies:**

```bash
pip install marker-pdf python-dotenv pypdfium2
```

**Basic usage** — single file or entire directory:

```bash
# Single PDF
python ocr/extract_pdf.py mit_books/advanced_algorithms/part4.pdf --verbose

# All PDFs in a directory (discovers book.pdf and part*.pdf)
python ocr/extract_pdf.py mit_books/advanced_algorithms/ --verbose
```

**LLM-assisted conversion** — uses an Llama API endpoint for higher quality:

```bash
python ocr/extract_pdf.py mit_books/advanced_algorithms/part4.pdf --verbose --llm-service openai
```

The script points at `https://api.llama.com/compat/v1/` by default. Set your LLAMA_API_KEY key in a `.env` file at the project root (it will be loaded automatically via `python-dotenv`.)

**Batch OCR on a Slurm cluster** — process all 69 courses as a job array via `ocr/run_ocr.slurm`. Run from the project root with your conda environment active:

```bash
cd /path/to/statement_selection
conda activate <your-env>
sbatch ocr/run_ocr.slurm          # all 69 courses
```

## Extraction Background

Here is how I extracted the course data.

### Retrieve List of Courses

This was ctrl+A on the course explorer on OpenCourseWare.
It was used to create `1_list_of_courses.md`.

### Retrieve URLs and Download Content

Claude initially prompted with
```md
For each book in the 1_list_of_courses.md, e.g. for Graduate Topology Seminar: Kan Seminar, can you provide the associated url, for both the main course page, e.g. https://ocw.mit.edu/courses/18-915-graduate-topology-seminar-kan-seminar-fall-2014/, as well as the download url for the zip materials associated to the courses, e.g., https://ocw.mit.edu/courses/18-915-graduate-topology-seminar-kan-seminar-fall-2014/18.915-fall-2014.zip. Do it for all the book in the list, you may create a markdown file 2_list_of_urls, with a rubric homepage and a rubric download link.
```

Claude initially prompted with
```md
Can you create a script to download the zip the files from the `2_list_of_urls.md`? Can you also create a script to unzip these files?
```

### Filter Courses based on Autoformalization Potential

Claude initially prompted with
```md
I have a directory `download_mit_ocw/unzipped` containing folders for MIT OpenCourseWare courses.
Each course folder is typically named `<class_number>-<semester_date>` and includes a `static_resources` subfolder containing course materials.
My goal is to identify courses with the most suitable content for autoformalization in Lean4.
Here are my criteria to filter out poor candidates:
1. Content Quality: Filter out content that are not well-structured (e.g., slides only, too informal, not clear way to extract the main content of the course).
2. Formalization Potential: Exclude courses that are already well-represented in `mathlib` due to being too basic.

Output a list of all MIT courses in the directory, annotated with their candidate status and a short rationale for rejections. E.g.,

18.417 | Graduate
Introduction to Computational Molecular Biology
Source: 18.417-fall-2004
Status: ❌ Not a Candidate
Reason: Not clear textbook, cluttered lectures, without strong formalization potential

18.757 | Graduate
Representations of Lie Groups
Source: 18.755-sprint-2024
Status: ✅ Good Candidate
Reason: Clear and well structured textbook `mit18-755-s24_lec_full.pdf` covering important subject missing in mathlib.
```
It was used to create `3_list_of_first_candidates.md`

### Extract, Organize PDFs, and OCR

Claude initially prompted with
```md
For all the course tagged in the list `download_mit_ocw/3_list_of_first_candidates.md` as either `Good candidate`, `Borderline candidate` or `To check`, can you create a dedicated folder with the course name (used the title, e.g. `representations_of_lie_groups` not the numbering version, e.g. `18.755-sprint-2024`)? Within this folder, create a subfolder `content`. Then, put all and only the ressources that will be autoformalized that you will find in `download_mit_ocw/unzipped/<course id>/static_resources` in this `content` subfolder. Ideally the resources should be a simple pdf, which you can rename `book.pdf`. Eventually it could be several pdf, which you should then order and named `partX.pdf` where X = 1, 2, ....
```
It was used to create the `organize_courses.py` script.

Claude initially prompted with
```md
I have a list of books that I want to study throughoutly with an LLM. They are Math textbooks in pdf format. I need some scripts in order to extract the content in a format that is LLM friendly.
```
It created `ocr/extract_pdf.py`, and then `ocr/run_ocr.slurm`.

### Cleaning

Claude initially prompted with
```md
I have run an OCR pipeline. I have extracted ressources online in `ocr_mit/unzipped`.
I have then tried to copy the best pdf sources into `mit_books`/
I have then OCR these books.
Can you review all my OCR books in `mit_books` and check for mistakes. If you find some, can you go back to the root of the problem. Can you then fix these mistakes?
```

**Skip OCR thanks to tex sources:**

Claude initially prompted with
```md
I have run an OCR pipeline. I have extracted ressources online in `ocr_mit/unzipped`.
I have then tried to copy the best pdf sources into `mit_books`/
I have then OCR these books.
However for some books I have some tex files that should have authority over my OCR pipeline.
Let's take for example Algebra 1 (`mit_books/algebra_i_student_notes`), I can map it back to the `ocr_mit/unzipped/RES.18-011-fall-2021` (thanks to the `3_list_of_first_candidates.md`).
I see that the tex files exists there.
Can you review all my OCR books in `mit_books` and check for the ones where I actually have the tex files. Can you list those? And update the content in `mit_books` to put the tex files there instead?
```

#### Check Mathlib coverage
This is done with `mathlib_coverage/split_prompt.py`, `instructions.md` and `mathlib_coverage/template_mathlib_prompt.md`.


Check additional statistics:
```md
I want to extract 4 or 5 books to send to annotators for an autoformalization project from the mit_books. The goal would be that the annotators write the formal statements of some hard theorems that are not in mathlib, and for which reading the associated books should provide the informal context, which translated into formal context would yield the proof of the theorem. I have an assessment of the mathlib coverage of books for all the mit_books. Can you review all of them, and suggest some books that would provide some good coverage of math (like proba, stats, algebra, pde, ...).
```

```md
I have extracted assessments for all the books in mit_books. I want to know which one I should not bother formalizing as most of the content is already in mathlib. Can you do this for me?
```

```md
I have extracted assessments for all the books in mit_books. I want to know which books would be good candidates to fill in the missing undergrad math from mathlib: http://leanprover-community.github.io/undergrad_todo.html.
```
**Result**: See `mit_books/undergrad_todo_candidate_analysis.md` for the full tiered ranking and coverage matrix.

```md
I have extracted assessments for all the books in mit_books. I want to know which books would be good candidates to fill in the missing 1000 theorems from mathlib: https://leanprover-community.github.io/1000.html
```
