
# MIT OpenCourseWare

This folder contains utilities to process content provided by the MIT on their OCW platform.

## Reproducing the Course Data

To download and organize the MIT OCW course PDFs from scratch, follow these steps.

### 1. Download the ZIP files

```bash
python mit_ocw/download_zips.py
```

This reads the course URLs from `mit_ocw/2_list_of_urls.md` and downloads each course's ZIP archive into `mit_ocw/zip_files/`.

### 2. Unzip the files

```bash
python mit_ocw/unzip_files.py
```

This extracts each ZIP into `mit_ocw/unzipped/<course-id>/`.

### 3. Organize courses into folders

```bash
python mit_ocw/organize_courses.py
```

This processes the 69 courses tagged as Good/Borderline/To-check in `mit_ocw/3_list_of_first_candidates.md` and creates a folder for each at the project root:

- **Single-PDF courses** (30): `<course_name>/book.pdf`
- **Multi-PDF courses** (39): `<course_name>/book/part1.pdf`, `part2.pdf`, ...

The script handles stripping OCW hash prefixes from filenames, deduplication, and sorting.

### 4. Extract PDF content

Convert the organized PDFs to LLM-friendly markdown using `extract_pdf.py`.

**Dependencies:**

```bash
pip install marker-pdf python-dotenv pypdfium2
```

**Basic usage** — single file or entire directory:

```bash
# Single PDF
python extract_pdf.py mit_books/advanced_algorithms/part4.pdf --verbose

# All PDFs in a directory (discovers book.pdf and part*.pdf)
python extract_pdf.py mit_books/advanced_algorithms/ --verbose
```

**LLM-assisted conversion** — uses an Llama API endpoint for higher quality:

```bash
python extract_pdf.py mit_books/advanced_algorithms/part4.pdf --verbose --llm-service openai
```

The script points at `https://api.llama.com/compat/v1/` by default. Set your LLAMA_API_KEY key in a `.env` file at the project root (it will be loaded automatically via `python-dotenv`.)

**Batch OCR on a Slurm cluster** — process all 69 courses as a job array:

```bash
# Edit run_ocr.slurm to set your partition, GPU spec, conda env, and project path, then:
sbatch run_ocr.slurm
```

## Extraction Background

Here is how I extracted the course data.

### Retrieve List of Courses

This was ctrl+A on the course explorer on OpenCourseWare.
It was used to create `list_of_mit_courses.md`.

### Retrieve URLs and Download Content

Claude prompted with
```md
For each book in the list_of_mit_courses.md, e.g. for Graduate Topology Seminar: Kan Seminar, can you provide the associated url, for both the main course page, e.g. https://ocw.mit.edu/courses/18-915-graduate-topology-seminar-kan-seminar-fall-2014/, as well as the download url for the zip materials associated to the courses, e.g., https://ocw.mit.edu/courses/18-915-graduate-topology-seminar-kan-seminar-fall-2014/18.915-fall-2014.zip. Do it for all the book in the list, you may create a markdown file list_of_mit_courses_with_links, with a rubric homepage and a rubric download link.
Do it by creating a script called `find_ocw_urls.py`.
```

Claude prompted with
```md
Can you create a script to download the zip the files from the `list_of_mit_courses_with_links.md`? Can you also create a script to unzip these files? Call these scripts `download_zips.py` and `unzip_files.py`.
```

### Filter Courses based on Autoformalization Potential

Claude prompted with
```md
I have a directory `mit_ocw/unzipped` containing folders for MIT OpenCourseWare courses.
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
It was used to create `list_of_first_candidates.md`

### Extract and Organize PDFs

Claude prompted with
```md
For all the course tagged in the list `mit_ocw/3_list_of_first_candidates.md` as either `Good candidate`, `Borderline candidate` or `To check`, can you create a dedicated folder with the course name (used the title, e.g. `representations_of_lie_groups` not the numbering version, e.g. `18.755-sprint-2024`)? Within this folder, create a subfolder `content`. Then, put all and only the ressources that will be autoformalized that you will find in `mit_ocw/unzipped/<course id>/static_resources` in this `content` subfolder. Ideally the resources should be a simple pdf, which you can rename `book.pdf`. Eventually it could be several pdf, which you should then order and named `partX.pdf` where X = 1, 2, ....
```
It was used to create the `organize_courses.py` script.

Claude prompted with
```md
I have a list of books that I want to study throughoutly with an LLM. They are Math textbooks in pdf format. I need some scripts in order to extract the content in a format that is LLM friendly
```
It created `extract_pdf.py`.
Best is to run this of GPU to extract the pdf faster.

#### TODO: Run Charles' pipeline on each borderline and better candidate
Once we have this list, let's extract everything in a cleaner format, the one we agreed before, and let's run the instruction.md on each of them.
