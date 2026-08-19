#!/usr/bin/env python3

"""Add Lean definition bodies and small presentation fixes to Blueprint HTML."""

from __future__ import annotations

import argparse
import html
import re
from pathlib import Path


L2_PAGES = (
    ("l2", "L2 theory"),
    ("l2/overview", "L2 theory: arXiv:2106.04770v2 implementation map"),
    ("l2/foundations", "Fourier conventions and Hilbert spaces"),
    ("l2/fourier-dilation", "Unitary coordinates and their Fourier construction"),
    ("l2/operators", "Synthesis, ridgelets, and reconstruction"),
    ("l2/general-solution", "Null space and the general solution"),
    ("l2/activations", "Standard activation functions"),
    ("l2/further-results", "Further results from the source manuscript"),
)

L1_PAGES = (
    ("l1", "L1 theory"),
    ("l1/overview-l1", "L1 theory: arXiv:1505.03654v2 implementation map"),
    ("l1/l1-theory", "L1 theory: formalization details"),
)

FS_PAGES = (
    ("fs", "Fourier slice method"),
    ("fs/overview-fs", "Fourier slice method: arXiv:2402.15984 implementation map"),
    ("fs/fs-theory", "Fourier slice method: formalization details"),
)

HA_PAGES = (
    ("ha", "Harmonic-analysis method"),
    ("ha/overview-ha", "Harmonic-analysis method: arXiv:2405.13682 implementation map"),
    ("ha/ha-representations", "Harmonic-analysis method: representations and intertwiners"),
    ("ha/ha-affine", "Harmonic-analysis method: the affine Mackey model"),
    ("ha/ha-architectures", "Harmonic-analysis method: reconstruction and architectures"),
    ("ha/ha-quadratic", "Harmonic-analysis method: the quadratic-form network"),
)

TO_MATHLIB_PAGES = (
    ("to-mathlib", "Mathlib upstream candidates"),
    ("to-mathlib/measure-lp", "Mathlib candidates: Lp and measure transport"),
    ("to-mathlib/radon-fourier", "Mathlib candidates: Radon and Fourier transforms"),
    ("to-mathlib/integral-fourier-tools", "Mathlib candidates: integral and Fourier tools"),
    ("to-mathlib/schwartz-convolution", "Mathlib candidates: Schwartz space and convolution"),
    ("to-mathlib/finite-euclidean", "Mathlib candidates: finite Fourier and Euclidean geometry"),
    ("to-mathlib/representations", "Mathlib candidates: unitary representations and groups"),
    ("to-mathlib/invariant-geometry", "Mathlib candidates: invariant geometry and integration"),
    ("to-mathlib/symmetric-spaces",
     "Mathlib candidates: symmetric spaces and the Helgason--Fourier transform"),
)

# No subtree is development-only at present: the harmonic-analysis pages joined the published ones
# on 2026-08-19, as the Fourier-slice pages did on 2026-08-11. The two tuples stay separate so that
# the next unstable subtree can be added to the development one alone.
PUBLIC_PAGES = L2_PAGES + L1_PAGES + FS_PAGES + HA_PAGES + TO_MATHLIB_PAGES
DEVELOPMENT_PAGES = L2_PAGES + L1_PAGES + FS_PAGES + HA_PAGES + TO_MATHLIB_PAGES

# Chapters that `{blueprint_graph}` and `{blueprint_summary}` generate from the node registry.
# They carry no hand-written Lean panels, so they are verified but not rewritten.
GENERATED_CHAPTERS = (
    ("Dependency-Graph", "Dependency Graph"),
    ("Blueprint-Summary", "Blueprint Summary"),
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

OVERVIEW_LABEL_PATTERN = re.compile(
    r'(?P<open><span class="bp_label[^"]*">)(?:\d+\.)+(?P<number>\d+)(?P<close></span>)'
)
OVERVIEW_REFERENCE_PATTERN = re.compile(
    r'\b(?P<kind>Definition|Theorem|Proposition|Lemma|Corollary) '
    r'(?:\d+\.)+(?P<number>\d+)\b'
)
OVERVIEW_STATEMENT_LABEL_PATTERN = re.compile(
    r'<div class="bp_heading bp_kind_'
    r'(?:definition|theorem|proposition|lemma|corollary)_heading[^"]*".*?'
    r'<span class="bp_label[^"]*">(?P<number>\d+)</span>',
    re.DOTALL,
)
OLD_OVERVIEW_STYLE_PATTERN = re.compile(
    r'\s*<style id="lean-ridgelet-overview-style">.*?</style>', re.DOTALL
)


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


def normalize_overview_numbering(document: str) -> str:
    """Match the manuscript's global 1--26 theorem counter.

    Verso prefixes statement labels with their nested Blueprint section number. The manuscript
    uses the same shared ordering without that hierarchy prefix.
    """
    document = OLD_OVERVIEW_STYLE_PATTERN.sub("", document)
    document = OVERVIEW_LABEL_PATTERN.sub(
        lambda match: match.group("open") + match.group("number") + match.group("close"), document
    )
    document = OVERVIEW_REFERENCE_PATTERN.sub(
        lambda match: match.group("kind") + " " + match.group("number"), document
    )
    labels = OVERVIEW_STATEMENT_LABEL_PATTERN.findall(document)
    expected = [str(number) for number in range(1, 27)]
    if labels != expected:
        raise RuntimeError(f"unexpected Overview statement numbering: {labels}")
    return document


def process_chapter(repo_root: Path, output_root: Path, slug: str) -> int:
    index = output_root / "html-multi" / slug / "index.html"
    if not index.is_file():
        raise FileNotFoundError(index)
    document = index.read_text(encoding="utf-8")
    document, implementation_count = inject_implementations(document, repo_root)
    if "lean-ridgelet-blueprint-style" not in document:
        document = document.replace("</head>", STYLE + "</head>", 1)
    if slug == "l2/overview":
        document = normalize_overview_numbering(document)
    index.write_text(document, encoding="utf-8")
    return implementation_count


def verify_navigation(output_root: Path, pages_to_check: tuple[tuple[str, str], ...]) -> None:
    html_root = output_root / "html-multi"
    all_entries = pages_to_check + GENERATED_CHAPTERS
    groups: dict[str, tuple[tuple[str, str], ...]] = {}
    for slug, _ in pages_to_check:
        group = slug.split("/", 1)[0]
        groups[group] = tuple(entry for entry in pages_to_check if entry[0].split("/", 1)[0] == group)
    top_entries = tuple(entry for entry in pages_to_check if "/" not in entry[0]) + GENERATED_CHAPTERS
    page_entries: tuple[tuple[str | None, str], ...] = ((None, ""),) + tuple(
        (slug, title) for slug, title in all_entries
    )
    for slug, _ in all_entries:
        if not (html_root / slug / "index.html").is_file():
            raise RuntimeError(f"missing standard Blueprint page for {slug}")
    for page_number, (page_slug, _) in enumerate(page_entries):
        index = html_root / "index.html" if page_slug is None else html_root / page_slug / "index.html"
        document = index.read_text(encoding="utf-8")
        if document.count('class="split-toc book"') != 1:
            raise RuntimeError(f"expected exactly one standard Verso table of contents in {index}")
        required_entries = top_entries
        if page_slug is not None:
            group = page_slug.split("/", 1)[0]
            if group in groups:
                required_entries += groups[group][1:]
        for slug, title in required_entries:
            if f'href="{slug}/' not in document or title not in document:
                raise RuntimeError(f"missing standard Blueprint page link for {slug} in {index}")
        if page_number > 0 and 'rel="prev"' not in document:
            raise RuntimeError(f"missing standard previous-page navigation in {index}")
        if page_number + 1 < len(page_entries) and 'rel="next"' not in document:
            raise RuntimeError(f"missing standard next-page navigation in {index}")


def verify_generated_chapters(output_root: Path) -> None:
    html_root = output_root / "html-multi"
    markers = {
        "Dependency-Graph": ("bp_graph_legend", "bp-graph-data"),
        "Blueprint-Summary": ("bp_summary_grid",),
    }
    for slug, title in GENERATED_CHAPTERS:
        index = html_root / slug / "index.html"
        if not index.is_file():
            raise RuntimeError(f"missing generated chapter page for {slug}")
        document = index.read_text(encoding="utf-8")
        for marker in markers[slug]:
            if marker not in document:
                raise RuntimeError(f"generated chapter {slug} is missing {marker}")
        root = (html_root / "index.html").read_text(encoding="utf-8")
        if f'href="{slug}/' not in root or title not in root:
            raise RuntimeError(f"missing generated chapter link for {slug} in the root page")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "output_root",
        nargs="?",
        default="_out/blueprint",
        type=Path,
        help="Blueprint output root (default: _out/blueprint)",
    )
    parser.add_argument(
        "--published-only",
        dest="published_only",
        action="store_true",
        help="process and verify only the published chapters",
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    output_root = args.output_root
    if not output_root.is_absolute():
        output_root = repo_root / output_root

    pages = PUBLIC_PAGES if args.published_only else DEVELOPMENT_PAGES

    total = 0
    for slug, _ in pages:
        count = process_chapter(repo_root, output_root, slug)
        total += count
        print(f"postprocessed {slug}: {count} Lean definition implementation(s)")
    if total == 0:
        raise RuntimeError("no Lean definition implementations were inserted")
    verify_navigation(output_root, pages)
    print(f"verified standard Verso navigation across all {len(pages)} theory pages")
    verify_generated_chapters(output_root)
    print(f"verified {len(GENERATED_CHAPTERS)} generated chapters")


if __name__ == "__main__":
    main()
