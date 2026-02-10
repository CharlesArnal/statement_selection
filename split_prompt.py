#!/usr/bin/env python3
import argparse
import os

def main():
    parser = argparse.ArgumentParser(description="Split initial_prompt.md into X batch files.")
    parser.add_argument("X", type=int, help="Number of batches to create")
    args = parser.parse_args()

    base_dir = os.path.dirname(os.path.abspath(__file__))
    template = open(os.path.join(base_dir, "initial_prompt.md")).read()

    mit_books_dir = os.path.join(base_dir, "mit_books")
    dirs = sorted(
        d for d in os.listdir(mit_books_dir)
        if os.path.isdir(os.path.join(mit_books_dir, d))
    )

    X = args.X
    n = len(dirs)
    chunks = []
    start = 0
    for i in range(X):
        size = n // X + (1 if i < n % X else 0)
        chunks.append(dirs[start : start + size])
        start += size

    for i, chunk in enumerate(chunks, 1):
        textbook_list = "\n".join(f"- mit_books/{d}" for d in chunk) + "\n"
        content = template.replace("{TEXTBOOK_LIST}", textbook_list)
        path = os.path.join(base_dir, f"initial_prompt_batch_{i}.md")
        with open(path, "w") as f:
            f.write(content)
        print(f"Wrote {path} ({len(chunk)} textbooks)")

if __name__ == "__main__":
    main()
