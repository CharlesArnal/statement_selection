
# Preprocessing steps 

#### Retrieve list of courses

This was ctrl+A on the course explorer on OpenCourseWare.
It was used to create `list_of_mit_courses.md`

#### Retrive urls 

Claude prompted with
```
For each book in the list_of_mit_courses.md, e.g. for Graduate Topology Seminar: Kan Seminar, can you provide the associated url, for both the main course page, e.g. https://ocw.mit.edu/courses/18-915-graduate-topology-seminar-kan-seminar-fall-2014/, as well as the download url for the zip materials associated to the courses, e.g., https://ocw.mit.edu/courses/18-915-graduate-topology-seminar-kan-seminar-fall-2014/18.915-fall-2014.zip. Do it for all the book in the list, you may create a markdown file list_of_mit_courses_with_links, with a rubric homepage and a rubric download link.
Do it by creating a script called `find_ocw_urls.py`.
```

Claude prompted with
```
Can you create a script to download the zip the files from the `list_of_mit_courses_with_links.md`? Can you also create a script to unzip these files? Call these scripts `download_zips.py` and `unzip_files.py`.
```

#### Retreive the main source for each courses

TODO: Describe the structure of the MIT downloaded folder, and give claude instructions in order to filter for good and less good candidates to filter book candidates.

Use the currently existing instructions to get the final files with the statements of interest.

Unzip what we have download, look into static_ressources.
There, there are usually much more files than what we need, there may be duplicate between chapters and the full book, there may be tex source.
We want to extrat a single source, best is a single tex (if there are many we many contenate them ourselves), or a single pdf (if they are split by chapter, we may need to concatenate them).

# Check if good source
Check if it is a good candidate for autoformalization, is the content good enough? Is the content already in mathlib?
Make it a skills for Claude to work on this.