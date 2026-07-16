#!/usr/bin/env python3

"""Add project-specific navigation and Lean definition bodies to Blueprint HTML."""

from __future__ import annotations

import argparse
import html
import re
from pathlib import Path


CHAPTERS = (
    ("foundations", "Fourier conventions and Hilbert spaces"),
    ("fourier-dilation", "Fourier--dilation coordinates"),
    ("operators", "Synthesis, ridgelets, and reconstruction"),
    ("general-solution", "Null space and the general solution"),
    ("activations", "Standard activation functions"),
    ("further-results", "Further results from the source manuscript"),
)

TOC_PATTERN = re.compile(
    r'(<div class="split-toc book">\s*<div class="title">\s*'
    r'<span class="no-toggle"></span><span class="">Table of Contents</span></div>)'
    r'(\s*</div>)'
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


def chapter_toc(current: str) -> str:
    rows = [
        '<tr class="unnumbered"><td class="num"></td>'
        '<td><a href="../../../html-multi/index.html">Blueprint home</a></td></tr>'
    ]
    for slug, title in CHAPTERS:
        current_class = "current " if slug == current else ""
        rows.append(
            f'<tr class="{current_class}unnumbered"><td class="num"></td>'
            f'<td><a href="../../{slug}/html-multi/index.html">'
            f"{html.escape(title)}</a></td></tr>"
        )
    return '<table class="lean-ridgelet-chapter-toc">' + "".join(rows) + "</table>"


def inject_toc(document: str, current: str) -> str:
    if "lean-ridgelet-chapter-toc" in document:
        return document
    replacement = lambda match: match.group(1) + chapter_toc(current) + match.group(2)
    document, count = TOC_PATTERN.subn(replacement, document, count=1)
    if count != 1:
        raise RuntimeError(f"could not locate the empty Table of Contents for {current}")
    return document


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
    index = output_root / "chapters" / slug / "html-multi" / "index.html"
    if not index.is_file():
        raise FileNotFoundError(index)
    document = index.read_text(encoding="utf-8")
    document = inject_toc(document, slug)
    document, implementation_count = inject_implementations(document, repo_root)
    if "lean-ridgelet-blueprint-style" not in document:
        document = document.replace("</head>", STYLE + "</head>", 1)
    index.write_text(document, encoding="utf-8")
    return implementation_count


def verify_navigation(output_root: Path) -> None:
    hrefs = ["../../../html-multi/index.html"] + [
        f"../../{slug}/html-multi/index.html" for slug, _ in CHAPTERS
    ]
    for slug, _ in CHAPTERS:
        index = output_root / "chapters" / slug / "html-multi" / "index.html"
        document = index.read_text(encoding="utf-8")
        if document.count('class="lean-ridgelet-chapter-toc"') != 1:
            raise RuntimeError(f"expected exactly one chapter table of contents in {index}")
        for href in hrefs:
            if f'href="{href}"' not in document:
                raise RuntimeError(f"missing navigation link {href} in {index}")
            if not (index.parent / href).resolve().is_file():
                raise RuntimeError(f"navigation target does not exist: {index.parent / href}")


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
    print("verified Blueprint navigation across all six chapters")


if __name__ == "__main__":
    main()
