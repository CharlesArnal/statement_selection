#!/usr/bin/env python3
"""Extract all ZIP files from zip_files/ into unzipped/."""

import zipfile
from pathlib import Path

ZIP_DIR = Path(__file__).parent / "zip_files"
OUTPUT_DIR = Path(__file__).parent / "unzipped"


def main():
    zips = sorted(ZIP_DIR.glob("*.zip"))
    print(f"Found {len(zips)} ZIP files")

    OUTPUT_DIR.mkdir(exist_ok=True)

    extracted = 0
    skipped = 0
    failures = []

    for i, zp in enumerate(zips, 1):
        dest = OUTPUT_DIR / zp.stem
        if dest.exists():
            skipped += 1
            print(f"[{i}/{len(zips)}] Skipped {zp.name} (already extracted)")
            continue
        try:
            with zipfile.ZipFile(zp) as zf:
                zf.extractall(dest)
            extracted += 1
            print(f"[{i}/{len(zips)}] Extracted {zp.name}")
        except Exception as e:
            failures.append((zp.name, str(e)))
            print(f"[{i}/{len(zips)}] FAILED {zp.name}: {e}")

    print(f"\nDone: {extracted} extracted, {skipped} skipped, {len(failures)} failed")
    if failures:
        print("Failures:")
        for name, err in failures:
            print(f"  {name}: {err}")


if __name__ == "__main__":
    main()
