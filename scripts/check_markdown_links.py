#!/usr/bin/env python3
"""Check repository-local links in active Markdown documentation."""

from __future__ import annotations

import re
from pathlib import Path
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parents[1]
LINK = re.compile(r"\[[^]]*\]\(([^)]+)\)")
# `.opencode` holds local agent tooling (including a vendored `node_modules`
# whose READMEs point at web resources), not project documentation.
EXCLUDED_PARTS = {".git", ".lake", ".opencode", "node_modules"}


def main() -> None:
    broken: list[str] = []
    for document in sorted(ROOT.rglob("*.md")):
        relative = document.relative_to(ROOT)
        if EXCLUDED_PARTS.intersection(relative.parts):
            continue
        if relative.parts[:2] == ("research", "archive"):
            continue
        for raw_target in LINK.findall(document.read_text(encoding="utf-8", errors="replace")):
            target = raw_target.strip().strip("<>")
            if target.startswith(("http://", "https://", "mailto:", "#")):
                continue
            target = unquote(target.split("#", 1)[0])
            if target and not (document.parent / target).resolve().exists():
                broken.append(f"{relative.as_posix()} -> {target}")

    if broken:
        print("Broken local Markdown links:")
        print("\n".join(f"  {item}" for item in broken))
        raise SystemExit(1)
    print("No broken local Markdown links in active documentation.")


if __name__ == "__main__":
    main()
