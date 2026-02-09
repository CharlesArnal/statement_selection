
# MIT OpenCourseWare

This folder contains utilities to process content provided by the MIT on their OCW platform.

## Preprocessing Steps 

#### Retrieve List of Courses

This was ctrl+A on the course explorer on OpenCourseWare.
It was used to create `list_of_mit_courses.md`

#### Retrive Urls and Download Content

Claude prompted with
```
For each book in the list_of_mit_courses.md, e.g. for Graduate Topology Seminar: Kan Seminar, can you provide the associated url, for both the main course page, e.g. https://ocw.mit.edu/courses/18-915-graduate-topology-seminar-kan-seminar-fall-2014/, as well as the download url for the zip materials associated to the courses, e.g., https://ocw.mit.edu/courses/18-915-graduate-topology-seminar-kan-seminar-fall-2014/18.915-fall-2014.zip. Do it for all the book in the list, you may create a markdown file list_of_mit_courses_with_links, with a rubric homepage and a rubric download link.
Do it by creating a script called `find_ocw_urls.py`.
```

Claude prompted with
```
Can you create a script to download the zip the files from the `list_of_mit_courses_with_links.md`? Can you also create a script to unzip these files? Call these scripts `download_zips.py` and `unzip_files.py`.
```

#### Filter Courses based on Autoformalization Potential

Claude prompted with
```
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

#### TODO: Extract main pdf files, order them, and put them in a special location

Claude prompted with
```
For all the course tagged in the list `mit_ocw/3_list_of_first_candidates.md` as either `Good candidate`, `Borderline candidate` or `To check`, can you create a dedicated folder with the course name (used the title, e.g. `representations_of_lie_groups` not the numbering version, e.g. `18.755-sprint-2024`)?
Within this folder, create a subfolder `content`.
Then, put all and only the ressources that will be autoformalized that you will find in `mit_ocw/unzipped/<course id>/static_resources` in this `content` subfolder. Ideally the resources should be a simple pdf, which you can rename `book.pdf`. Eventually it could be several pdf, which you should then order and named `partX.pdf` where X = 1, 2, ....
```

#### TODO: Run Charles' pipeline on each borderline and better candidate
Once we have this list, let's extract everything in a cleaner format, the one we agreed before, and let's run the instruction.md on each of them.
