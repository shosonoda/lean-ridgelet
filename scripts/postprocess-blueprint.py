#!/usr/bin/env python3

"""Add Lean definition bodies and small presentation fixes to Blueprint HTML."""

from __future__ import annotations

import argparse
import html
import re
from pathlib import Path


CHAPTERS = (
    ("overview", "L2 implementation map before result reordering"),
    ("foundations", "Fourier conventions and Hilbert spaces"),
    ("fourier-dilation", "Unitary coordinates and their Fourier construction"),
    ("operators", "Synthesis, ridgelets, and reconstruction"),
    ("general-solution", "Null space and the general solution"),
    ("activations", "Standard activation functions"),
    ("further-results", "Further results from the source manuscript"),
)

DECL_PATTERN = re.compile(
    r'(?P<prefix><div class="declaration decl [^"]*" '
    r'data-decl="(?P<decl>[^"]+)" data-kind="(?P<kind>def|abbrev)">.*?)'
    r'(?P<body><div class="bp_external_decl_body">)',
    re.DOTALL,
)
SOURCE_PATTERN = re.compile(
    r'href="[^"]*/(?P<path>LeanRidgelet/[^"#?]+)#L(?P<start>\d+)'
    r'(?:-L(?P<end>\d+))?"'
)

STYLE = """
<style id="lean-ridgelet-blueprint-style">
.bp_external_decl_implementation {
  margin: 0.75rem 0;
}
.bp_external_decl_implementation > summary {
  cursor: pointer;
  font-weight: 600;
}
.bp_external_decl_implementation pre {
  margin-top: 0.5rem;
  max-height: 32rem;
  overflow: auto;
  white-space: pre-wrap;
}
</style>
"""

OVERVIEW_STYLE = """
<style id="lean-ridgelet-overview-style">
/* Verso uses one counter for all theorem-like kinds. The authored first sentence carries the
   manuscript's independent Proposition/Theorem/Lemma numbering, so suppress that shared count. */
.bp_wrapper > .bp_heading .bp_label,
.bp_code_block > summary .bp_label {
  display: none;
}
</style>
"""


def source_implementation(repo_root: Path, source_match: re.Match[str]) -> str | None:
    source_path = repo_root / source_match.group("path")
    if not source_path.is_file():
        return None
    start = int(source_match.group("start"))
    end = int(source_match.group("end") or start)
    lines = source_path.read_text(encoding="utf-8").splitlines(keepends=True)
    source = "".join(lines[start - 1 : end]).rstrip()
    assign = source.find(":=")
    if assign < 0:
        return None
    return source[assign:]


def inject_implementations(document: str, repo_root: Path) -> tuple[str, int]:
    if "bp_external_decl_implementation" in document:
        return document, document.count('class="bp_external_decl_implementation"')

    inserted = 0

    def replace(match: re.Match[str]) -> str:
        nonlocal inserted
        source_match = SOURCE_PATTERN.search(match.group("prefix"))
        if source_match is None:
            return match.group(0)
        implementation = source_implementation(repo_root, source_match)
        if implementation is None:
            return match.group(0)
        inserted += 1
        implementation_html = html.escape(implementation, quote=False)
        panel = (
            '<details class="bp_external_decl_implementation" open="open">'
            "<summary>Implementation after <code>:=</code></summary>"
            f'<pre class="bp_external_decl_impl hl lean block">{implementation_html}</pre>'
            "</details>"
        )
        return match.group("prefix") + panel + match.group("body")

    return DECL_PATTERN.sub(replace, document), inserted


def process_chapter(repo_root: Path, output_root: Path, slug: str) -> int:
    index = output_root / "html-multi" / slug / "index.html"
    if not index.is_file():
        raise FileNotFoundError(index)
    document = index.read_text(encoding="utf-8")
    document, implementation_count = inject_implementations(document, repo_root)
    if "lean-ridgelet-blueprint-style" not in document:
        document = document.replace("</head>", STYLE + "</head>", 1)
    if slug == "overview" and "lean-ridgelet-overview-style" not in document:
        document = document.replace("</head>", OVERVIEW_STYLE + "</head>", 1)
    index.write_text(document, encoding="utf-8")
    return implementation_count


def verify_navigation(output_root: Path) -> None:
    html_root = output_root / "html-multi"
    pages = [html_root / "index.html"] + [
        html_root / slug / "index.html" for slug, _ in CHAPTERS
    ]
    for page_number, index in enumerate(pages):
        document = index.read_text(encoding="utf-8")
        if document.count('class="split-toc book"') != 1:
            raise RuntimeError(f"expected exactly one standard Verso table of contents in {index}")
        for slug, title in CHAPTERS:
            if f'href="{slug}/' not in document or title not in document:
                raise RuntimeError(f"missing standard chapter link for {slug} in {index}")
            if not (html_root / slug / "index.html").is_file():
                raise RuntimeError(f"missing standard chapter page for {slug}")
        if page_number > 0 and 'rel="prev"' not in document:
            raise RuntimeError(f"missing standard previous-page navigation in {index}")
        if page_number + 1 < len(pages) and 'rel="next"' not in document:
            raise RuntimeError(f"missing standard next-page navigation in {index}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "output_root",
        nargs="?",
        default="_out/blueprint",
        type=Path,
        help="Blueprint output root (default: _out/blueprint)",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    output_root = args.output_root
    if not output_root.is_absolute():
        output_root = repo_root / output_root

    total = 0
    for slug, _ in CHAPTERS:
        count = process_chapter(repo_root, output_root, slug)
        total += count
        print(f"postprocessed {slug}: {count} Lean definition implementation(s)")
    if total == 0:
        raise RuntimeError("no Lean definition implementations were inserted")
    verify_navigation(output_root)
    print("verified standard Verso navigation across all seven chapters")


if __name__ == "__main__":
    main()
