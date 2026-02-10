#!/usr/bin/env python3
"""
Fetch MIT OCW sitemap and match courses from list_of_mit_courses.md
to generate list_of_mit_courses_with_links.md with homepage and ZIP URLs.
"""

import re
import urllib.request
import xml.etree.ElementTree as ET
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from difflib import SequenceMatcher
from html.parser import HTMLParser
from pathlib import Path


def fetch_sitemap():
    """Fetch the OCW sitemap index and extract course slugs from sub-sitemap URLs.

    The sitemap index contains entries like:
    https://ocw.mit.edu/courses/18-06-linear-algebra-spring-2010/sitemap.xml
    We extract the course slug directly from these URLs (no need to fetch each sub-sitemap).
    """
    url = "https://ocw.mit.edu/sitemap.xml"
    print(f"Fetching sitemap from {url}...")
    req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
    with urllib.request.urlopen(req, timeout=60) as resp:
        data = resp.read()

    root = ET.fromstring(data)
    ns = {"sm": "http://www.sitemaps.org/schemas/sitemap/0.9"}

    course_urls = []

    # The sitemap index has <sitemap><loc>...</loc></sitemap> entries
    # Each course sub-sitemap URL looks like:
    # https://ocw.mit.edu/courses/{slug}/sitemap.xml
    for loc in root.findall("sm:sitemap/sm:loc", ns):
        sub_url = loc.text.strip()
        # Extract the course page URL from the sub-sitemap URL
        m = re.match(r"^(https://ocw\.mit\.edu/courses/[^/]+)/sitemap\.xml$", sub_url)
        if m:
            course_urls.append(m.group(1) + "/")

    # If no sitemap entries found, try direct URL entries
    if not course_urls:
        for url_elem in root.findall("sm:url/sm:loc", ns):
            u = url_elem.text.strip()
            if "/courses/" in u:
                course_urls.append(u)

    print(f"Found {len(course_urls)} course URLs in sitemap")
    return course_urls


def build_course_lookup(course_urls):
    """
    Build a lookup from course number to list of (slug, full_url) pairs.

    OCW URL pattern: https://ocw.mit.edu/courses/{slug}/...
    where slug typically starts with the department number, e.g.:
    18-06-linear-algebra-spring-2010
    18-06sc-linear-algebra-fall-2011
    res-18-001-calculus-online-textbook-spring-2005
    """
    # We want only top-level course pages (the slug, not sub-pages)
    slug_pattern = re.compile(r"^https://ocw\.mit\.edu/courses/([^/]+)/?$")

    slugs = set()
    for url in course_urls:
        m = slug_pattern.match(url)
        if m:
            slugs.add(m.group(1))

    print(f"Found {len(slugs)} unique course slugs")

    # Build lookup: course_number -> [(slug, semester, year)]
    # Slug format: {dept}-{num}[-{suffix}]-{name}-{semester}-{year}
    # e.g., 18-06-linear-algebra-spring-2010
    # e.g., res-18-001-calculus-online-textbook-spring-2005

    lookup = defaultdict(list)

    for slug in sorted(slugs):
        # Try to extract course number from slug
        # Pattern 1: res-18-001-...
        # Pattern 2: 18-06-...
        # Pattern 3: 18-06sc-...
        # Pattern 4: 18-4041j-6-840j-...

        # Extract semester and year from end of slug
        semester_match = re.search(r"-(spring|fall|summer|january-iap|iap)-((?:19|20)\d{2})$", slug)
        semester = semester_match.group(1) if semester_match else None
        year = int(semester_match.group(2)) if semester_match else None

        # Extract course number(s) from the beginning
        # Handle RES courses
        res_match = re.match(r"^(res-\d+-\d+[a-z]*)", slug)
        if res_match:
            raw_num = res_match.group(1)  # e.g., res-18-001
            # Convert to dotted form: RES.18-001
            parts = raw_num.split("-")
            course_num = f"RES.{parts[1]}-{parts[2]}"
            course_num = course_num.upper()
            lookup[course_num].append((slug, semester, year))
            continue

        # Handle regular courses: e.g., 18-06-..., 18-06sc-..., 18-4041j-6-840j-...
        # Try to extract one or more course numbers
        # The slug starts with dept-num[-suffix] possibly followed by more dept-num pairs

        # First, try to get the leading course number
        # Course sub-numbers can be digits optionally followed by letters (e.g., 06, 06sc, s096, a34, 404j)
        num_match = re.match(r"^(\d+)-([a-z]?\d+[a-z]*)(?:-(\d+)-([a-z]?\d+[a-z]*))?", slug)
        if num_match:
            dept1 = num_match.group(1)
            num1 = num_match.group(2)
            course_num = f"{dept1}.{num1}".upper()
            lookup[course_num].append((slug, semester, year))

            # If there's a cross-listed number
            if num_match.group(3) and num_match.group(4):
                dept2 = num_match.group(3)
                num2 = num_match.group(4)
                course_num2 = f"{dept2}.{num2}".upper()
                lookup[course_num2].append((slug, semester, year))

    print(f"Built lookup with {len(lookup)} unique course numbers")
    return lookup


def parse_course_list(filepath):
    """
    Parse list_of_mit_courses.md to extract unique (course_number, course_name) pairs.

    Format (every 5 lines, including blank separator):
    18.437J | Graduate
    Distributed Algorithms
    Prof. Nancy Lynch
    EngineeringComputer ScienceAlgorithms and Data Structures+ 1 more
    <blank line>
    """
    with open(filepath) as f:
        lines = [l.rstrip() for l in f.readlines()]

    courses = []
    seen = set()

    i = 0
    while i < len(lines):
        # Skip blank lines
        if not lines[i].strip():
            i += 1
            continue

        # Line 1: course number | level
        header = lines[i].strip()
        # Line 2: course name
        if i + 1 < len(lines):
            name = lines[i + 1].strip()
        else:
            break

        # Extract course number(s) from header
        # Examples: "18.437J | Graduate", "18.650 (formerly 18.443) | Undergraduate"
        # "18.4041J,6.840J | Undergraduate, Graduate", "RES.18-006 | Undergraduate"

        # Get the part before the pipe
        parts = header.split("|")
        num_part = parts[0].strip()

        # Remove "(formerly ...)" notation
        num_part = re.sub(r"\s*\(formerly\s+[\d.]+\)\s*", "", num_part)

        # Split by comma for cross-listed
        nums = [n.strip() for n in num_part.split(",")]

        # Use the first number as the primary
        primary_num = nums[0].upper()

        key = (primary_num, name)
        if key not in seen:
            seen.add(key)
            courses.append((primary_num, name, nums))

        # Advance past this course block (4 lines + blank)
        i += 4
        # Skip any trailing blank lines
        while i < len(lines) and not lines[i].strip():
            i += 1

    print(f"Parsed {len(courses)} unique courses from input file")
    return courses


def normalize_for_matching(text):
    """Normalize text for fuzzy matching: lowercase, remove punctuation, collapse spaces."""
    text = text.lower()
    text = re.sub(r"[^a-z0-9\s]", " ", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def slug_to_title(slug, course_num_raw):
    """Extract the title portion from a slug by removing course number prefix and semester suffix."""
    # Remove semester-year suffix
    title = re.sub(r"-(spring|fall|summer|january-iap|iap)-(19|20)\d{2}$", "", slug)

    # Remove course number prefix
    # For RES courses: res-18-001-...
    res_match = re.match(r"^res-\d+-\d+[a-z]*-", title)
    if res_match:
        title = title[res_match.end():]
    else:
        # For cross-listed: 18-4041j-6-840j-...
        cross_match = re.match(r"^\d+-\d+[a-z]*-\d+-\d+[a-z]*-", title)
        if cross_match:
            title = title[cross_match.end():]
        else:
            # For regular: 18-06-..., 18-06sc-..., 18-s096-..., 18-a34-...
            reg_match = re.match(r"^\d+-[a-z]?\d+[a-z]*-", title)
            if reg_match:
                title = title[reg_match.end():]

    # Replace hyphens with spaces for comparison
    title = title.replace("-", " ")
    return title


def find_best_match(course_num, course_name, lookup):
    """Find the best matching OCW slug for a given course number and name."""
    # Normalize course number for lookup
    # Input format: "18.06", "18.06SC", "RES.18-006", "18.4041J"
    # Lookup keys: "18.06", "18.06SC", "RES.18-006", "18.4041J"

    candidates = lookup.get(course_num, [])

    if not candidates:
        # Try without trailing letter (J suffix for cross-listed)
        stripped = re.sub(r"[A-Z]$", "", course_num)
        if stripped != course_num:
            candidates = lookup.get(stripped, [])

        # Try with J suffix
        if not candidates:
            candidates = lookup.get(course_num + "J", [])

    # For J courses like 18.437J, try looking for just 18.437
    if not candidates and course_num.endswith("J"):
        base = course_num[:-1]
        candidates = lookup.get(base, [])

    # For 18.4041J type (cross-listed), the slug might be under 6.840J or similar
    # Try all variations
    if not candidates:
        # Try case-insensitive match across all lookup keys
        lower_num = course_num.lower()
        for key, vals in lookup.items():
            if key.lower() == lower_num:
                candidates = vals
                break

    # For S-prefix courses like 18.S096, 18.S190, 18.S191, 18.S996, 18.S997
    # OCW slugs use formats like: 18-s096, 18-s190, etc.
    # These should already match if the slug parsing is correct.
    # Let's also try without the S prefix or with lowercase
    if not candidates and ".S" in course_num:
        # Try lowercase version
        lower = course_num.replace(".S", ".s")
        candidates = lookup.get(lower, [])
        if not candidates:
            candidates = lookup.get(lower.upper(), [])

    # For 4-digit numbers like 18.1001, 18.1002
    # These are newer courses, might be listed as 18-1001 in slug

    # Known cross-listed courses: try alternate department numbers
    # Many 18.xxxJ math courses are also listed as 6.xxxJ CS courses
    cross_listed_alternates = {
        "18.062J": ["6.042J"],
        "18.410J": ["6.046J"],
        "18.416J": ["6.856J"],
        "18.415J": ["6.854J"],
        "18.400J": ["6.045J"],
        "18.437J": ["6.852J"],
        "18.352J": ["12.009J"],
        "18.4041J": ["18.404J", "6.840J"],
        "18.435J": ["2.111J"],
        "18.337J": ["6.338J"],
        "18.338J": ["6.339J"],
        "18.385J": ["2.036J"],
        "18.335J": ["6.337J"],
        "18.353J": ["12.006J", "2.050J"],
        "5.95J": ["6.982J"],
        "3.021J": ["1.021J"],
        "2.034J": ["12.207J"],
        # Newer 4-digit numbers mapped to older letter-suffix equivalents
        "18.1001": ["18.100A"],
        "18.1002": ["18.100B", "18.100C"],
    }
    if not candidates and course_num in cross_listed_alternates:
        for alt in cross_listed_alternates[course_num]:
            candidates = lookup.get(alt, [])
            if not candidates:
                # Try without J suffix
                candidates = lookup.get(alt.rstrip("J"), [])
            if candidates:
                break

    if not candidates:
        return None, None

    if len(candidates) == 1:
        slug, semester, year = candidates[0]
        return slug, semester

    # Multiple candidates - find best match by title similarity
    norm_name = normalize_for_matching(course_name)

    best_slug = None
    best_score = -1
    best_year = -1
    best_semester = None

    for slug, semester, year in candidates:
        slug_title = slug_to_title(slug, course_num)
        norm_slug_title = normalize_for_matching(slug_title)

        score = SequenceMatcher(None, norm_name, norm_slug_title).ratio()

        # If scores are very close, prefer the latest year
        yr = year if year else 0

        if score > best_score + 0.05 or (abs(score - best_score) <= 0.05 and yr > best_year):
            best_score = score
            best_slug = slug
            best_year = yr
            best_semester = semester

    return best_slug, best_semester


class ZipLinkParser(HTMLParser):
    """Parse an OCW download page to find the .zip download href."""

    def __init__(self):
        super().__init__()
        self.zip_href = None

    def handle_starttag(self, tag, attrs):
        if tag == "a" and self.zip_href is None:
            attrs_dict = dict(attrs)
            href = attrs_dict.get("href", "")
            if href.endswith(".zip"):
                self.zip_href = href


def fetch_zip_url_from_download_page(slug):
    """Fetch the download page for a course and extract the .zip URL.

    Returns (slug, zip_url) or (slug, None) on failure.
    """
    download_page_url = f"https://ocw.mit.edu/courses/{slug}/download/"
    try:
        req = urllib.request.Request(
            download_page_url, headers={"User-Agent": "Mozilla/5.0"}
        )
        with urllib.request.urlopen(req, timeout=30) as resp:
            html = resp.read().decode("utf-8", errors="replace")

        parser = ZipLinkParser()
        parser.feed(html)

        if parser.zip_href:
            # The href may be relative (e.g., /courses/slug/file.zip) or absolute
            href = parser.zip_href
            if href.startswith("/"):
                return slug, f"https://ocw.mit.edu{href}"
            elif href.startswith("http"):
                return slug, href
            else:
                return slug, f"https://ocw.mit.edu/courses/{slug}/{href}"
        return slug, None
    except Exception as e:
        print(f"  Warning: Failed to fetch download page for {slug}: {e}")
        return slug, None


def fetch_all_zip_urls(slugs, max_workers=10):
    """Fetch ZIP download URLs for all slugs in parallel.

    Returns a dict mapping slug -> zip_url (or None).
    """
    print(f"\nFetching download pages for {len(slugs)} courses (max {max_workers} workers)...")
    zip_urls = {}

    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {
            executor.submit(fetch_zip_url_from_download_page, slug): slug
            for slug in slugs
        }
        done_count = 0
        for future in as_completed(futures):
            slug, zip_url = future.result()
            zip_urls[slug] = zip_url
            done_count += 1
            if done_count % 20 == 0 or done_count == len(slugs):
                print(f"  Progress: {done_count}/{len(slugs)}")

    found = sum(1 for v in zip_urls.values() if v is not None)
    print(f"  Found ZIP URLs for {found}/{len(slugs)} courses")
    return zip_urls


def verify_zip_urls(zip_urls_to_verify, max_workers=10):
    """Verify ZIP URLs by making HEAD requests. Reports failures."""
    print(f"\nVerifying {len(zip_urls_to_verify)} ZIP URLs...")

    def check_url(item):
        course_label, url = item
        try:
            req = urllib.request.Request(
                url, method="HEAD", headers={"User-Agent": "Mozilla/5.0"}
            )
            with urllib.request.urlopen(req, timeout=15) as resp:
                return course_label, url, resp.status
        except urllib.error.HTTPError as e:
            return course_label, url, e.code
        except Exception as e:
            return course_label, url, str(e)

    failures = []
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = [executor.submit(check_url, item) for item in zip_urls_to_verify]
        done_count = 0
        for future in as_completed(futures):
            course_label, url, status = future.result()
            done_count += 1
            if status != 200:
                failures.append((course_label, url, status))
            if done_count % 20 == 0 or done_count == len(zip_urls_to_verify):
                print(f"  Verified: {done_count}/{len(zip_urls_to_verify)}")

    if failures:
        print(f"\n  {len(failures)} ZIP URLs returned non-200 status:")
        for label, url, status in sorted(failures):
            print(f"    {label}: {status} — {url}")
    else:
        print(f"  All {len(zip_urls_to_verify)} ZIP URLs verified OK (200)")

    return failures


def main():
    DIR = Path(__file__).parent
    input_file = DIR / "1_list_of_courses.md"
    output_file = DIR / "2_list_of_urls.md"

    # Step 1: Fetch sitemap
    course_urls = fetch_sitemap()

    # Step 2: Build lookup
    lookup = build_course_lookup(course_urls)

    # Step 3: Parse course list
    courses = parse_course_list(input_file)

    # Step 4: Match courses to slugs
    matched_courses = []  # (course_num, course_name, slug)
    unmatched = []

    for course_num, course_name, all_nums in courses:
        slug, _ = find_best_match(course_num, course_name, lookup)

        # If primary didn't match, try other cross-listed numbers
        if slug is None and len(all_nums) > 1:
            for alt_num in all_nums[1:]:
                slug, _ = find_best_match(alt_num.upper(), course_name, lookup)
                if slug:
                    break

        if slug:
            matched_courses.append((course_num, course_name, slug))
        else:
            unmatched.append((course_num, course_name))

    print(f"\nMatched {len(matched_courses)}/{len(courses)} courses to OCW slugs")

    # Step 5: Fetch ZIP URLs in parallel for all matched courses
    unique_slugs = list({slug for _, _, slug in matched_courses})
    zip_url_map = fetch_all_zip_urls(unique_slugs)

    # Step 6: Generate output
    output_lines = []
    output_lines.append("# MIT OCW Course Links\n")
    zip_urls_to_verify = []

    for course_num, course_name, slug in matched_courses:
        homepage = f"https://ocw.mit.edu/courses/{slug}/"
        zip_url = zip_url_map.get(slug)

        output_lines.append(f"## {course_num} — {course_name}")
        output_lines.append(f"- **Homepage**: {homepage}")
        if zip_url:
            output_lines.append(f"- **Download**: {zip_url}")
            zip_urls_to_verify.append((f"{course_num} — {course_name}", zip_url))
        output_lines.append("")

    for course_num, course_name in unmatched:
        output_lines.append(f"## {course_num} — {course_name}")
        output_lines.append("- **Homepage**: *Not found on OCW*")
        output_lines.append("")

    # Write output
    with open(output_file, "w") as f:
        f.write("\n".join(output_lines))

    print(f"\nResults: {len(matched_courses)}/{len(courses)} courses matched")
    if unmatched:
        print(f"\nUnmatched courses ({len(unmatched)}):")
        for num, name in unmatched:
            print(f"  {num} — {name}")

    print(f"\nOutput written to {output_file}")

    # Step 7: Verify ZIP URLs
    if zip_urls_to_verify:
        verify_zip_urls(zip_urls_to_verify)


if __name__ == "__main__":
    main()
