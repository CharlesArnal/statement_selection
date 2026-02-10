#!/usr/bin/env python3
"""Convert math PDF textbooks to LLM-friendly markdown with LaTeX math notation.

Uses marker-pdf for ML-based PDF → markdown conversion, with post-processing
to clean up the output. Supports single files, directories with book.pdf or
part*.pdf naming conventions, and optional merging of multi-part books.

Dependencies: pip install marker-pdf
"""

import argparse
import gc
import os
import re
from pathlib import Path

import pypdfium2 as pdfium
from dotenv import load_dotenv
from marker.config.parser import ConfigParser
from marker.converters.pdf import PdfConverter
from marker.models import create_model_dict
from marker.output import text_from_rendered

load_dotenv()  # loads .env from cwd (or parent dirs)


LLM_SERVICES = {
    "gemini": "marker.services.gemini.GoogleGeminiService",
    "claude": "marker.services.claude.ClaudeService",
    "openai": "marker.services.openai.OpenAIService",
    "azure": "marker.services.azure_openai.AzureOpenAIService",
    "ollama": "marker.services.ollama.OllamaService",
}


def discover_pdfs(path: Path, force: bool) -> list[Path]:
    """Find PDFs to process.

    Single file: return that file.
    Directory: find book.pdf and part*.pdf in each subdirectory.
    Skip PDFs that already have a .md sibling unless --force.
    """
    if path.is_file():
        if not path.suffix.lower() == ".pdf":
            print(f"Error: {path} is not a PDF file")
            return []
        md_path = path.with_suffix(".md")
        if md_path.exists() and not force:
            print(f"Skipping {path} (already has .md output, use --force to re-extract)")
            return []
        return [path]

    if not path.is_dir():
        print(f"Error: {path} does not exist")
        return []

    pdfs = []
    # Walk subdirectories looking for book.pdf and part*.pdf
    for subdir in sorted(path.rglob("*")):
        if not subdir.is_dir():
            continue
        _collect_from_dir(subdir, force, pdfs)
    # Also check the given directory itself
    _collect_from_dir(path, force, pdfs)
    return pdfs


def _collect_from_dir(directory: Path, force: bool, out: list[Path]):
    """Collect book.pdf and part*.pdf from a single directory."""
    book = directory / "book.pdf"
    if book.exists():
        md_path = book.with_suffix(".md")
        if md_path.exists() and not force:
            return
        out.append(book)
        return  # If there's a book.pdf, don't also pick up parts

    parts = sorted(directory.glob("part*.pdf"), key=_part_sort_key)
    if parts:
        for p in parts:
            md_path = p.with_suffix(".md")
            if md_path.exists() and not force:
                continue
            out.append(p)


def _part_sort_key(path: Path) -> int:
    """Extract numeric suffix from part filenames for sorting."""
    m = re.search(r"part(\d+)", path.stem)
    return int(m.group(1)) if m else 0


def postprocess(text: str) -> str:
    """Light cleanup of marker output.

    - Remove isolated page numbers (lines that are just a number).
    - Collapse runs of 3+ blank lines to 2.
    """
    lines = text.split("\n")
    cleaned = []
    for line in lines:
        stripped = line.strip()
        # Remove lines that are just a page number
        if re.fullmatch(r"\d{1,4}", stripped):
            continue
        cleaned.append(line)
    text = "\n".join(cleaned)
    # Collapse excessive blank lines
    text = re.sub(r"\n{4,}", "\n\n\n", text)
    return text


def merge_parts(directory: Path, verbose: bool):
    """Merge part1.md, part2.md, ... into book.md."""
    parts = sorted(directory.glob("part*.md"), key=_part_sort_key)
    if len(parts) < 2:
        return
    merged = []
    for p in parts:
        content = p.read_text(encoding="utf-8")
        merged.append(content.strip())
    book_md = directory / "book.md"
    book_md.write_text("\n\n---\n\n".join(merged) + "\n", encoding="utf-8")
    if verbose:
        print(f"  Merged {len(parts)} parts → {book_md}")


def load_models():
    """Load marker-pdf ML models once."""
    print("Loading marker-pdf models...")
    model_dict = create_model_dict()
    print("Models loaded.")
    return model_dict


def build_converter(model_dict, *, force_ocr: bool = False, use_llm: bool = False,
                    page_range: str | None = None, llm_service: str | None = None,
                    openai_config: dict | None = None):
    """Build a PdfConverter with the given options."""
    config = {
        "output_format": "markdown",
        "disable_image_extraction": True,
    }
    if force_ocr:
        config["force_ocr"] = True
    if use_llm:
        config["use_llm"] = True
    if llm_service:
        config["llm_service"] = llm_service
    if page_range is not None:
        config["page_range"] = page_range
    if openai_config:
        config.update(openai_config)

    config_parser = ConfigParser(config)

    converter = PdfConverter(
        config=config_parser.generate_config_dict(),
        artifact_dict=model_dict,
        processor_list=config_parser.get_processors(),
        renderer=config_parser.get_renderer(),
        llm_service=config_parser.get_llm_service() if use_llm else None,
    )
    return converter


def _get_page_count(pdf_path: Path) -> int:
    """Get the number of pages in a PDF using pypdfium2."""
    pdf = pdfium.PdfDocument(str(pdf_path))
    count = len(pdf)
    pdf.close()
    return count


def convert_one(model_dict, pdf_path: Path, verbose: bool, *,
                force_ocr: bool = False, use_llm: bool = False,
                chunk_size: int = 50, llm_service: str | None = None,
                openai_config: dict | None = None) -> bool:
    """Convert a single PDF to markdown. Returns True on success.

    For large PDFs, processes in chunks of `chunk_size` pages to avoid OOM.
    Set chunk_size=0 to disable chunking.
    """
    if verbose:
        print(f"  Converting {pdf_path} ...")

    try:
        page_count = _get_page_count(pdf_path)
    except Exception as e:
        print(f"  ERROR reading {pdf_path}: {e}")
        return False

    if verbose:
        print(f"  {page_count} pages")

    # Decide whether to chunk
    if chunk_size > 0 and page_count > chunk_size:
        # Chunked conversion
        chunks = []
        for start in range(0, page_count, chunk_size):
            end = min(start + chunk_size, page_count)
            # ConfigParser expects a string like "0-49" (0-indexed, inclusive end)
            page_range = f"{start}-{end - 1}"
            chunk_label = f"pages {start + 1}-{end}/{page_count}"

            if verbose:
                print(f"  Chunk: {chunk_label}")

            try:
                converter = build_converter(
                    model_dict, force_ocr=force_ocr, use_llm=use_llm,
                    page_range=page_range, llm_service=llm_service,
                    openai_config=openai_config,
                )
                rendered = converter(str(pdf_path))
                text, _, _ = text_from_rendered(rendered)
                chunks.append(text)
            except Exception as e:
                print(f"  ERROR converting {pdf_path} ({chunk_label}): {e}")
                return False
            finally:
                gc.collect()

        text = "\n\n".join(chunks)
    else:
        # Single-pass conversion
        try:
            converter = build_converter(
                model_dict, force_ocr=force_ocr, use_llm=use_llm,
                llm_service=llm_service, openai_config=openai_config,
            )
            rendered = converter(str(pdf_path))
            text, _, _ = text_from_rendered(rendered)
        except Exception as e:
            print(f"  ERROR converting {pdf_path}: {e}")
            return False

    text = postprocess(text)

    if len(text.strip()) < 100:
        print(f"  WARNING: output for {pdf_path} is suspiciously short ({len(text.strip())} chars)")

    md_path = pdf_path.with_suffix(".md")
    md_path.write_text(text, encoding="utf-8")

    if verbose:
        print(f"  Wrote {md_path} ({len(text)} chars)")
    return True


def main():
    parser = argparse.ArgumentParser(
        description="Convert math PDF textbooks to markdown with LaTeX math notation."
    )
    parser.add_argument("path", type=Path, help="Path to a PDF file or directory")
    parser.add_argument("--force", "-f", action="store_true",
                        help="Re-extract PDFs that already have .md output")
    parser.add_argument("--merge-parts", action="store_true",
                        help="Merge part1.md, part2.md, ... into book.md per directory")
    parser.add_argument("--force-ocr", action="store_true",
                        help="Force OCR on all pages (better inline math → LaTeX)")
    parser.add_argument("--use-llm", action="store_true",
                        help="Use LLM-assisted conversion (highest quality, needs API key)")
    parser.add_argument("--llm-service", type=str, default=None,
                        choices=["openai", "gemini", "claude", "azure", "ollama"],
                        help="LLM provider to use with --use-llm (default: None)")
    parser.add_argument("--openai-api-key", type=str, default=None,
                        help="API key for the OpenAI-compatible endpoint (default: LLAMA_API_KEY from .env)")
    parser.add_argument("--openai-model", type=str, default="claude-4-6-opus-genai",
                        help="Model name for the OpenAI-compatible endpoint")
    parser.add_argument("--dry-run", action="store_true",
                        help="List PDFs that would be processed without converting")
    parser.add_argument("--verbose", "-v", action="store_true",
                        help="Detailed progress output")
    parser.add_argument("--chunk-size", type=int, default=50,
                        help="Max pages per conversion pass to limit memory (default 50, 0=no chunking)")

    args = parser.parse_args()

    # --llm-service implies --use-llm
    if args.llm_service:
        args.use_llm = True

    # Resolve LLM service name to full import path
    llm_service = LLM_SERVICES.get(args.llm_service) if args.llm_service else None

    # Build OpenAI-compatible endpoint config from CLI flags / .env
    openai_config = {}
    openai_config["openai_base_url"] = "https://api.llama.com/compat/v1/"
    openai_config["openai_api_key"] = args.openai_api_key or os.environ.get("LLAMA_API_KEY")
    openai_config["openai_model"] = args.openai_model

    # Stage 1: PDF Discovery
    pdfs = discover_pdfs(args.path, args.force)
    if not pdfs:
        print("No PDFs to process.")
        return

    print(f"Found {len(pdfs)} PDF(s) to process")

    if args.dry_run:
        for p in pdfs:
            print(f"  {p}")
        return

    # Stage 2: Model Loading
    model_dict = load_models()

    # Stage 3: Conversion + Post-processing
    successes = 0
    failures = []

    for i, pdf in enumerate(pdfs, 1):
        print(f"[{i}/{len(pdfs)}] {pdf}")
        if convert_one(model_dict, pdf, args.verbose,
                       force_ocr=args.force_ocr, use_llm=args.use_llm,
                       chunk_size=args.chunk_size, llm_service=llm_service,
                       openai_config=openai_config or None):
            successes += 1
        else:
            failures.append(pdf)

    print(f"\nDone: {successes} converted, {len(failures)} failed")
    if failures:
        print("Failures:")
        for f in failures:
            print(f"  {f}")

    # Stage 4: Optional merge
    if args.merge_parts:
        # Collect unique directories that contain part*.md
        dirs_seen = set()
        for pdf in pdfs:
            d = pdf.parent
            if d not in dirs_seen:
                dirs_seen.add(d)
                merge_parts(d, args.verbose)


if __name__ == "__main__":
    main()
