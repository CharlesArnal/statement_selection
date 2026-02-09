#!/usr/bin/env python3
"""Download all ZIP files listed in list_of_mit_courses_with_links.md."""

import os
import re
import urllib.request
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

MARKDOWN_FILE = Path(__file__).parent / "list_of_mit_courses_with_links.md"
OUTPUT_DIR = Path(__file__).parent / "zip_files"


def parse_download_urls(md_path: Path) -> list[str]:
    text = md_path.read_text()
    return re.findall(r"\*\*Download\*\*:\s*(https?://\S+)", text)


def download_one(url: str, output_dir: Path) -> tuple[str, str]:
    """Download a single URL. Returns (filename, status)."""
    filename = url.rsplit("/", 1)[-1]
    dest = output_dir / filename
    if dest.exists() and dest.stat().st_size > 0:
        return filename, "skipped"
    try:
        urllib.request.urlretrieve(url, dest)
        return filename, "ok"
    except Exception as e:
        # Clean up partial downloads
        if dest.exists():
            dest.unlink()
        return filename, f"FAILED: {e}"


def main():
    urls = parse_download_urls(MARKDOWN_FILE)
    print(f"Found {len(urls)} download URLs")

    OUTPUT_DIR.mkdir(exist_ok=True)

    successes = 0
    skipped = 0
    failures = []

    with ThreadPoolExecutor(max_workers=5) as pool:
        futures = {pool.submit(download_one, url, OUTPUT_DIR): url for url in urls}
        for i, future in enumerate(as_completed(futures), 1):
            filename, status = future.result()
            if status == "ok":
                successes += 1
                print(f"[{i}/{len(urls)}] Downloaded {filename}")
            elif status == "skipped":
                skipped += 1
                print(f"[{i}/{len(urls)}] Skipped {filename} (already exists)")
            else:
                failures.append((filename, status))
                print(f"[{i}/{len(urls)}] {filename} — {status}")

    print(f"\nDone: {successes} downloaded, {skipped} skipped, {len(failures)} failed")
    if failures:
        print("Failures:")
        for name, err in failures:
            print(f"  {name}: {err}")


if __name__ == "__main__":
    main()
