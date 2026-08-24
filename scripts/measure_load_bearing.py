#!/usr/bin/env python3
"""Measure load-bearing depth across Scaffold/Mathlib modules.

For each module (file) under Scaffold/Mathlib, "height" is the number of
distinct OTHER Mathlib files whose body references at least one of that
module's declared names (theorem/lemma/def/axiom) — a proxy for how many
other proofs would break if the module's content were wrong. "QA depth"
is the same count restricted to Scaffold/QA files: a module can have QA
without having any real theorem consumer, which is exactly the gap this
script is meant to surface.

Usage: python3 scripts/measure_load_bearing.py [--top N]
"""

import argparse
import os
import re
from collections import defaultdict

ROOT = "Scaffold"
DECL_RE = re.compile(
    r"^\s*(?:private\s+|protected\s+|noncomputable\s+)*"
    r"(?:theorem|lemma|def|axiom)\s+([A-Za-z_][A-Za-z0-9_']*)"
)
TOKEN_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")

BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)
LINE_COMMENT_RE = re.compile(r"--.*")


def strip_comments(text):
    text = BLOCK_COMMENT_RE.sub(" ", text)
    text = LINE_COMMENT_RE.sub(" ", text)
    return text


def iter_lean_files(root):
    for dirpath, _, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith(".lean"):
                yield os.path.join(dirpath, fn)


def is_mathlib(path):
    return path.startswith(os.path.join(ROOT, "Mathlib"))


def is_qa(path):
    return path.startswith(os.path.join(ROOT, "QA"))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--top", type=int, default=12)
    args = ap.parse_args()

    files = list(iter_lean_files(ROOT))
    file_tokens = {}
    file_decls = defaultdict(list)

    for f in files:
        with open(f, encoding="utf-8", errors="ignore") as fh:
            raw = fh.read()
        text = strip_comments(raw)
        file_tokens[f] = set(TOKEN_RE.findall(text))
        for line in text.splitlines():
            m = DECL_RE.match(line)
            if m:
                file_decls[f].append(m.group(1))

    mathlib_files = [f for f in files if is_mathlib(f)]

    module_rows = []
    for f in mathlib_files:
        names = file_decls[f]
        if not names:
            continue
        mathlib_consumers = set()
        qa_consumers = set()
        for g, toks in file_tokens.items():
            if g == f:
                continue
            if any(name in toks for name in names):
                if is_mathlib(g):
                    mathlib_consumers.add(g)
                elif is_qa(g):
                    qa_consumers.add(g)
        module_rows.append({
            "file": f,
            "declarations": len(names),
            "mathlib_consumers": len(mathlib_consumers),
            "qa_consumers": len(qa_consumers),
            "consumer_files": sorted(mathlib_consumers),
        })

    module_rows.sort(key=lambda r: (r["mathlib_consumers"], r["file"]))

    print(f"{len(mathlib_files)} Mathlib files, {len(module_rows)} with declarations\n")

    print("=== VALLEYS (lowest structural fan-out first) ===")
    print(f"{'file':<65} {'decls':>6} {'mathlib_consumers':>18} {'qa_consumers':>13}")
    for r in module_rows[: args.top]:
        print(f"{r['file']:<65} {r['declarations']:>6} {r['mathlib_consumers']:>18} {r['qa_consumers']:>13}")

    print()
    print("=== MOUNTAINS (highest structural fan-out first) ===")
    print(f"{'file':<65} {'decls':>6} {'mathlib_consumers':>18} {'qa_consumers':>13}")
    for r in sorted(module_rows, key=lambda r: -r["mathlib_consumers"])[: args.top]:
        print(f"{r['file']:<65} {r['declarations']:>6} {r['mathlib_consumers']:>18} {r['qa_consumers']:>13}")

    print()
    print("=== Zero-structural-consumer modules with QA (proved but never reused) ===")
    zero = [r for r in module_rows if r["mathlib_consumers"] == 0]
    for r in zero:
        print(f"  {r['file']}  (decls={r['declarations']}, qa_files={r['qa_consumers']})")


if __name__ == "__main__":
    main()
