#!/usr/bin/env python3
"""Organize MIT OCW courses into dedicated folders with autoformalization-relevant PDFs."""

import re
import shutil
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
UNZIPPED = PROJECT_ROOT / "mit_ocw" / "unzipped"

# ── Course configurations ──────────────────────────────────────────────────────
# strategy: "full" → copy single PDF as book.pdf
#           "parts" → copy multiple PDFs as part1.pdf, part2.pdf, ...
#
# For "full": target is a substring to match in the stripped filename.
# For "parts": pattern is a regex to match lecture files (after hash stripping).
# sort_key: function name or "custom" for hardcoded ordering.

COURSES = [
    # ── "full" strategy (32 courses, incl. 5 switched from parts) ──────────

    # 1
    {"folder": "algebra_ii_student_notes", "source": "RES.18-012-spring-2022",
     "strategy": "full", "target": "full_lec.pdf"},
    # 2
    {"folder": "real_analysis_18100a", "source": "18-100a-fall-2020",
     "strategy": "full", "target": "lec_full.pdf"},
    # 3
    {"folder": "real_analysis_18100b", "source": "18.100B-spring-2025",
     "strategy": "full", "target": "lec_full.pdf"},
    # 4 - match "lectures.pdf" but NOT "lecture1.pdf" etc.
    {"folder": "analysis_ii", "source": "18.101-fall-2005",
     "strategy": "full", "target": "lectures.pdf"},
    # 5
    {"folder": "introduction_to_functional_analysis", "source": "18.102-spring-2021",
     "strategy": "full", "target": "full_lec.pdf"},
    # 6
    {"folder": "projection_theory", "source": "18.156-spring-2025",
     "strategy": "full", "target": "lec_full.pdf"},
    # 7
    {"folder": "noncommutative_algebra", "source": "18.706-spring-2023",
     "strategy": "full", "target": "full_lec.pdf"},
    # 8 - match "MIT18_735F09_lec.pdf" (exact, not ch*)
    {"folder": "double_affine_hecke_algebras", "source": "18.735-fall-2009",
     "strategy": "full", "target": "MIT18_735F09_lec.pdf"},
    # 9
    {"folder": "lie_groups_and_lie_algebras_i", "source": "18.745-fall-2020",
     "strategy": "full", "target": "lec_full.pdf"},
    # 10
    {"folder": "lie_groups_and_lie_algebras_ii", "source": "18.755-spring-2024",
     "strategy": "full", "target": "lec_full.pdf"},
    # 11
    {"folder": "representations_of_lie_groups", "source": "18.757-fall-2023",
     "strategy": "full", "target": "lec_full.pdf"},
    # 12
    {"folder": "tensor_categories", "source": "18.769-spring-2009",
     "strategy": "full", "target": "notes.pdf"},
    # 13
    {"folder": "number_theory_i", "source": "18.785-fall-2021",
     "strategy": "full", "target": "full_lec.pdf"},
    # 14 - match "notes.pdf" not ch*
    {"folder": "algebraic_topology_ii", "source": "18.906-spring-2020",
     "strategy": "full", "target": "notes.pdf"},
    # 15 - match "main.pdf" not "main1.pdf"
    {"folder": "seminar_in_geometry", "source": "18.994-fall-2004",
     "strategy": "full", "target": "main.pdf"},
    # 16
    {"folder": "graph_theory_and_additive_combinatorics", "source": "18.225-fall-2023",
     "strategy": "full", "target": "lec_full.pdf"},
    # 17
    {"folder": "probabilistic_methods_in_combinatorics", "source": "18.226-fall-2022",
     "strategy": "full", "target": "lec_full.pdf"},
    # 18
    {"folder": "geometry_and_quantum_field_theory", "source": "18.238-Spring-2023",
     "strategy": "full", "target": "lec_full.pdf"},
    # 19
    {"folder": "topics_in_fourier_analysis", "source": "res.18-015-spring-2024",
     "strategy": "full", "target": "full_lec.pdf"},
    # 20
    {"folder": "applied_category_theory", "source": "18.s097-january-iap-2019",
     "strategy": "full", "target": "textbook.pdf"},
    # 21 - match "full_lec.pdf" not "full_lec_new"
    {"folder": "algebra_i_student_notes", "source": "RES.18-011-fall-2021",
     "strategy": "full", "target": "full_lec.pdf"},
    # 22
    {"folder": "differential_analysis", "source": "18.155-fall-2004",
     "strategy": "full", "target": "lecture_notes.pdf"},
    # 23
    {"folder": "mathematics_for_computer_science", "source": "6.042j-spring-2015",
     "strategy": "full", "target": "textbook.pdf"},
    # 24
    {"folder": "category_theory_for_scientists", "source": "18.s996-spring-2013",
     "strategy": "full", "target": "textbook.pdf"},
    # 25
    {"folder": "mathematics_of_machine_learning", "source": "18.657-fall-2015",
     "strategy": "full", "target": "LecNote.pdf"},
    # 26
    {"folder": "high_dimensional_statistics", "source": "18.s997-spring-2015",
     "strategy": "full", "target": "CourseNotes.pdf"},
    # 27
    {"folder": "matrix_calculus_for_machine_learning", "source": "18.s096-iap-2023",
     "strategy": "full", "target": "lec_full.pdf"},
    # 28 - switched from parts: has 18117notes.pdf
    {"folder": "topics_in_several_complex_variables", "source": "18.117-spring-2005",
     "strategy": "full", "target": "18117notes.pdf"},
    # 29 - switched from parts: has notes.pdf
    {"folder": "number_theory_ii_class_field_theory", "source": "18.786-spring-2016",
     "strategy": "full", "target": "notes.pdf"},
    # 30 - switched from parts: has notes.pdf
    {"folder": "algebraic_geometry_i", "source": "18.725-fall-2015",
     "strategy": "full", "target": "notes.pdf"},
    # 31 - switched from parts: has lecture_notes.pdf (111 pages)
    {"folder": "algebraic_topology_i", "source": "18.905-fall-2016",
     "strategy": "full", "target": "lecture_notes.pdf"},
    # 32 - switched from parts: has 18_969_geometry.pdf (55 pages)
    {"folder": "dirac_geometry", "source": "18.969-fall-2006",
     "strategy": "full", "target": "18_969_geometry.pdf"},

    # ── "parts" strategy (37 courses) ──────────────────────────────────────

    # 1
    {"folder": "rational_points_on_elliptic_curves", "source": "18.704-fall-2004",
     "strategy": "parts", "pattern": r"lecture(\d+)\.pdf$"},
    # 2 - custom order
    {"folder": "fourier_analysis", "source": "18.103-fall-2013",
     "strategy": "parts", "pattern": "custom",
     "custom_order": [
         "intro", "fseries1", "fseries2", "fseries3",
         "fourierint1", "fourierint2", "orthonormal",
         "lptheory", "booleanrings", "brownian"
     ]},
    # 3
    {"folder": "complex_variables_with_applications", "source": "18.04-spring-2018",
     "strategy": "parts", "pattern": r"topic(\d+)\.pdf$"},
    # 4
    {"folder": "functions_of_a_complex_variable", "source": "18.112-fall-2008",
     "strategy": "parts", "pattern": r"lecture(\d+(?:_\d+)?)\.pdf$"},
    # 5
    {"folder": "introduction_to_partial_differential_equations", "source": "18.152-fall-2011",
     "strategy": "parts", "pattern": r"lec_(\d+(?:_\d+)?)\.pdf$"},
    # 6 - deduplicate: keep numbered lec##.pdf, skip descriptive variants
    {"folder": "advanced_partial_differential_equations_with_applications", "source": "18.306-fall-2009",
     "strategy": "parts", "pattern": r"_lec(\d+)\.pdf$"},
    # 7
    {"folder": "theory_of_probability", "source": "18.175-spring-2014",
     "strategy": "parts", "pattern": r"Lecture(\d+)\.pdf$"},
    # 8 - files: lec01_intro.pdf, lec02_categories.pdf, etc.
    {"folder": "algebraic_geometry_ii", "source": "18.726-spring-2009",
     "strategy": "parts", "pattern": r"lec(\d+)_\w+\.pdf$"},
    # 9
    {"folder": "introduction_to_arithmetic_geometry", "source": "18.782-fall-2013",
     "strategy": "parts", "pattern": r"_lec(\d+)\.pdf$"},
    # 10
    {"folder": "elliptic_curves", "source": "18.783-spring-2021",
     "strategy": "parts", "pattern": r"notes(\d+)\.pdf$"},
    # 11
    {"folder": "the_sullivan_conjecture", "source": "18.917-fall-2007",
     "strategy": "parts", "pattern": r"lecture(\d+(?:_\d+)?)\.pdf$"},
    # 12
    {"folder": "geometry_of_manifolds_i", "source": "18.965-fall-2004",
     "strategy": "parts", "pattern": r"lecture(\d+(?:_\d+)?)\.pdf$"},
    # 13
    {"folder": "geometry_of_manifolds_ii", "source": "18.966-spring-2007",
     "strategy": "parts", "pattern": r"lect(\d+)\.pdf$"},
    # 14 - no hash prefixes
    {"folder": "analysis_of_boolean_functions", "source": "18-218-spring-2021",
     "strategy": "parts", "pattern": r"lec(\d+(?:-\d+)?)\.pdf$"},
    # 15 - stripped names are just lec01.pdf, lec02.pdf... (no course prefix after hash strip)
    {"folder": "combinatorial_theory", "source": "18.315-spring-2005",
     "strategy": "parts", "pattern": r"^lec(\d+)\.pdf$"},
    # 16
    {"folder": "the_polynomial_method", "source": "18.s997-fall-2012",
     "strategy": "parts", "pattern": r"_lec(\d+)\.pdf$"},
    # 17
    {"folder": "real_analysis_18100c", "source": "18.100c-fall-2012",
     "strategy": "parts", "pattern": r"l(\d+)sum\.pdf$"},
    # 18
    {"folder": "measure_and_integration", "source": "18.125-fall-2003",
     "strategy": "parts", "pattern": r"18125_lec(\d+)\.pdf$"},
    # 19
    {"folder": "advanced_calculus_for_engineers", "source": "18.075-fall-2004",
     "strategy": "parts", "pattern": r"lecture(\d+)\.pdf$"},
    # 20
    {"folder": "linear_partial_differential_equations", "source": "18.303-fall-2014",
     "strategy": "parts", "pattern": r"_Lecture(\d+)\.pdf$"},
    # 21
    {"folder": "topics_in_algebraic_number_theory", "source": "18.786-spring-2010",
     "strategy": "parts", "pattern": r"_lec(\d+)\.pdf$"},
    # 22 - custom order
    {"folder": "intersection_theory_on_moduli_spaces", "source": "18.727-spring-2006",
     "strategy": "parts", "pattern": "custom",
     "custom_order": [
         "week1", "picard", "const", "homology",
         "kontsevich", "generaltype", "formularium"
     ]},
    # 23 - no hash prefix, skip quizzes q1-q40
    {"folder": "geometry_and_topology_in_the_plane", "source": "18.900-spring-2023",
     "strategy": "parts", "pattern": r"^mit18_900s23_lec(\d+)\.pdf$"},
    # 24
    {"folder": "mirror_symmetry", "source": "18.969-spring-2009",
     "strategy": "parts", "pattern": r"_lec(\d+)\.pdf$"},
    # 25 - custom order
    {"folder": "topics_in_algebraic_combinatorics", "source": "18.318-spring-2006",
     "strategy": "parts", "pattern": "custom",
     "custom_order": ["notes2", "sperner", "boolean", "hadamard", "young"]},
    # 26 - skip video transcript PDFs (YouTube ID filenames)
    {"folder": "theory_of_computation", "source": "18.404j-fall-2020",
     "strategy": "parts", "pattern": r"_lec(\d+)\.pdf$"},
    # 27 - no hash prefix, combined lecture ranges
    {"folder": "probabilistically_checkable_proofs", "source": "18.408-fall-2022",
     "strategy": "parts", "pattern": r"lec(\d+(?:-\d+)?)\.pdf$"},
    # 28
    {"folder": "topics_in_combinatorial_optimization", "source": "18.997-spring-2004",
     "strategy": "parts", "pattern": r"co_lec(\d+)\.pdf$"},
    # 29
    {"folder": "automata_computability_and_complexity", "source": "6.045j-spring-2011",
     "strategy": "parts", "pattern": r"_lec(\d+)\.pdf$"},
    # 30 - has both writtenlec and lec patterns; use writtenlec (written lecture notes)
    {"folder": "design_and_analysis_of_algorithms", "source": "6.046j-spring-2015",
     "strategy": "parts", "pattern": r"writtenlec(\d+)\.pdf$"},
    # 31 - mixed naming: lec_1 to lec_10, lec11_12, lec13_14, lec15_16
    {"folder": "simplicity_theory", "source": "18.996a-spring-2004",
     "strategy": "parts", "pattern": r"lec[_]?(\d+(?:_\d+)?)\.pdf$"},
    # 32 - custom order
    {"folder": "nonparametrics_and_robustness", "source": "18.465-spring-2005",
     "strategy": "parts", "pattern": "custom",
     "custom_order": [
         "bretagn_massart", "delta_asympt", "location_scatter",
         "breakdown", "m_estimates", "outliers", "spatialmedian",
         "brkdn_location", "quantiles", "obenchain", "run_mwwtest"
     ]},
    # 33
    {"folder": "statistical_learning_theory", "source": "18.465-spring-2007",
     "strategy": "parts", "pattern": r"lecture(\d+)\.pdf$"},
    # 34
    {"folder": "an_algorithmists_toolkit", "source": "18.409-fall-2009",
     "strategy": "parts", "pattern": r"scribe(\d+)\.pdf$"},
    # 35 - stripped names: l123.pdf, l4.pdf, l78.pdf, l1617.pdf etc.
    {"folder": "combinatorial_optimization", "source": "18.433-fall-2003",
     "strategy": "parts", "pattern": r"^l(\d+)\.pdf$"},
    # 36 - stripped names: lec1.pdf, lec5.pdf etc. Skip lecture18.pdf, lect* variants
    {"folder": "advanced_algorithms", "source": "6.854j-fall-2008",
     "strategy": "parts", "pattern": r"^lec(\d+)\.pdf$"},
    # 37
    {"folder": "introduction_to_numerical_methods", "source": "18.335j-spring-2019",
     "strategy": "parts", "pattern": r"_lec(\d+)\.pdf$"},
]


def strip_hash(filename: str) -> str:
    """Strip 32-char hex hash prefix if present."""
    if re.match(r'^[0-9a-f]{32}_', filename):
        return filename[33:]
    return filename


def list_pdfs(src_dir: Path) -> list[tuple[str, Path]]:
    """Return list of (stripped_name, full_path) for all PDFs in src_dir."""
    results = []
    if not src_dir.exists():
        return results
    for f in src_dir.iterdir():
        if f.suffix.lower() == '.pdf':
            stripped = strip_hash(f.name)
            results.append((stripped, f))
    return results


def extract_first_number(s: str) -> int:
    """Extract the first number from a string for sorting."""
    m = re.search(r'\d+', s)
    return int(m.group()) if m else 0


def find_full_match(pdfs: list[tuple[str, Path]], target: str) -> Path | None:
    """Find a PDF whose stripped name ends with the target substring.

    For targets like "main.pdf", we need exact match (not "main1.pdf").
    For targets like "full_lec.pdf", we must avoid "full_lec_new.pdf".
    For "lectures.pdf", we must avoid "lecture1.pdf" etc.
    For "notes.pdf", we must avoid "notes1.pdf", "ch1_notes.pdf" etc.
    """
    exact_matches = []
    substring_matches = []
    for stripped, path in pdfs:
        if stripped == target:
            exact_matches.append(path)
        elif stripped.endswith(target):
            # Verify the char before target is underscore or start of string
            prefix = stripped[:-len(target)]
            if prefix == '' or prefix.endswith('_'):
                substring_matches.append(path)
    if exact_matches:
        return exact_matches[0]
    if substring_matches:
        return substring_matches[0]
    # Fallback: any file containing the target
    for stripped, path in pdfs:
        if target in stripped:
            return path
    return None


def filter_and_sort_parts(pdfs: list[tuple[str, Path]], pattern: str) -> list[Path]:
    """Filter PDFs matching pattern, deduplicate by stripped name, sort by number.

    The pattern is searched anywhere in the stripped filename (not anchored),
    so it can match files with course-code prefixes like MIT18_175S14_Lecture1.pdf.
    """
    seen = {}
    for stripped, path in pdfs:
        m = re.search(pattern, stripped)
        if m:
            # Deduplicate: keep first occurrence per stripped name
            if stripped not in seen:
                seen[stripped] = (m.group(1), path)
    # Sort by first number in the captured group
    items = list(seen.values())
    items.sort(key=lambda x: extract_first_number(x[0]))
    return [path for _, path in items]


def filter_custom_order(pdfs: list[tuple[str, Path]], custom_order: list[str]) -> list[Path]:
    """Match PDFs by custom order list (substring match on stripped name)."""
    result = []
    for name in custom_order:
        for stripped, path in pdfs:
            if name in stripped.lower() and path not in result:
                result.append(path)
                break
    return result


def process_course(course: dict) -> dict:
    """Process a single course, returning summary info."""
    folder = course["folder"]
    source = course["source"]
    strategy = course["strategy"]

    src_dir = UNZIPPED / source / "static_resources"
    course_dir = PROJECT_ROOT / "mit_books" / folder

    pdfs = list_pdfs(src_dir)

    if not pdfs:
        return {"folder": folder, "strategy": strategy, "count": 0, "error": "no PDFs found"}

    if strategy == "full":
        target = course["target"]
        match = find_full_match(pdfs, target)
        if match is None:
            return {"folder": folder, "strategy": strategy, "count": 0,
                    "error": f"no match for '{target}'"}
        course_dir.mkdir(parents=True, exist_ok=True)
        shutil.copy2(match, course_dir / "book.pdf")
        return {"folder": folder, "strategy": strategy, "count": 1}

    else:  # parts
        pattern = course["pattern"]
        if pattern == "custom":
            ordered = filter_custom_order(pdfs, course["custom_order"])
        else:
            ordered = filter_and_sort_parts(pdfs, pattern)

        if not ordered:
            return {"folder": folder, "strategy": strategy, "count": 0,
                    "error": f"no files matched pattern '{pattern}'"}

        # books/<folder>/partN.pdf
        course_dir.mkdir(parents=True, exist_ok=True)
        for i, path in enumerate(ordered, 1):
            shutil.copy2(path, course_dir / f"part{i}.pdf")

        return {"folder": folder, "strategy": strategy, "count": len(ordered)}


def main():
    print(f"Processing {len(COURSES)} courses...\n")
    errors = []
    total_files = 0

    for course in COURSES:
        result = process_course(course)
        status = f"  [{result['strategy']:5s}] {result['folder']:<55s} → {result['count']} file(s)"
        if "error" in result:
            status += f"  ⚠ {result['error']}"
            errors.append(result)
        print(status)
        total_files += result["count"]

    print(f"\nDone: {len(COURSES)} courses, {total_files} files copied.")
    if errors:
        print(f"\n⚠ {len(errors)} course(s) had issues:")
        for e in errors:
            print(f"  - {e['folder']}: {e['error']}")


if __name__ == "__main__":
    main()
