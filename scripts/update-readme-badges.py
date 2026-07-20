#!/usr/bin/env python3

"""Synchronize README badges with the version pinned by lean-toolchain."""

from __future__ import annotations

import argparse
from pathlib import Path


START = "<!-- BEGIN GENERATED BADGES -->"
END = "<!-- END GENERATED BADGES -->"
REPOSITORY = "shosonoda/lean-ridgelet"
ARXIV_ID = "2106.04770v2"


def lean_version(repo_root: Path) -> str:
    toolchain = (repo_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    marker = ":v"
    if marker not in toolchain:
        raise ValueError(f"unsupported lean-toolchain value: {toolchain!r}")
    version = toolchain.rsplit(marker, 1)[1]
    if not version:
        raise ValueError("lean-toolchain does not contain a version")
    return version


def badge_block(version: str) -> str:
    audit_url = f"https://github.com/{REPOSITORY}/actions/workflows/audit.yml"
    audit_badge = (
        f"https://img.shields.io/github/actions/workflow/status/{REPOSITORY}/audit.yml"
        "?branch=main&amp;label=assumption%20audit&amp;style=flat-square"
    )
    return (
        f'{START}\n<p align="center"><a href="{audit_url}"><img alt="Assumption audit" '
        f'src="{audit_badge}"></a> <a href="https://lean-lang.org/"><img '
        f'alt="Lean {version}" src="https://img.shields.io/badge/Lean-{version}-0f4c81.svg?'
        f'style=flat-square"></a> <a href="https://arxiv.org/abs/{ARXIV_ID}"><img '
        f'alt="arXiv {ARXIV_ID}" src="https://img.shields.io/badge/arXiv-{ARXIV_ID}-b31b1b.svg?'
        'style=flat-square"></a> <a href="LICENSE"><img alt="Apache 2.0" '
        'src="https://img.shields.io/badge/license-Apache--2.0-blue.svg?style=flat-square">'
        f"</a></p>\n{END}"
    )


def updated_readme(path: Path, block: str) -> str:
    document = path.read_text(encoding="utf-8")
    if document.count(START) != 1 or document.count(END) != 1:
        raise ValueError(f"expected exactly one generated badge block in {path}")
    prefix, remainder = document.split(START, 1)
    _, suffix = remainder.split(END, 1)
    return prefix + block + suffix


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--check", action="store_true", help="fail instead of writing when a README is stale"
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parent.parent
    block = badge_block(lean_version(repo_root))
    readmes = [repo_root / "README.md", repo_root / "public" / "README.md"]
    readmes = [path for path in readmes if path.is_file()]

    stale = []
    for path in readmes:
        expected = updated_readme(path, block)
        if expected == path.read_text(encoding="utf-8"):
            continue
        stale.append(path)
        if not args.check:
            path.write_text(expected, encoding="utf-8")

    if args.check and stale:
        names = ", ".join(str(path.relative_to(repo_root)) for path in stale)
        print(f"README badge block is stale: {names}")
        print("run: python3 scripts/update-readme-badges.py")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
