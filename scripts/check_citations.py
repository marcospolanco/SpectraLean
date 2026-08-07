#!/usr/bin/env python3
"""Check that axioms have proper citations."""

import os
import re
import sys
from pathlib import Path

AXIOM_PATTERN = r'^axiom\s+(\w+)'
DOC_PATTERN = r'/-[-\s]*Source:'
SOURCE_KEYWORDS = ['Source:', 'author', 'Author', 'title', 'Title', 'Theorem', 'Lemma', 'Definition']

def check_file(filepath):
    """Check a single Lean file for proper axiom citations."""
    with open(filepath, 'r') as f:
        content = f.read()

    # Find all axioms
    axioms = re.finditer(AXIOM_PATTERN, content, re.MULTILINE)
    issues = []

    for match in axioms:
        axiom_name = match.group(1)
        axiom_start = match.start()

        # Look backwards for doc comment
        doc_start = content.rfind('/--', 0, axiom_start)
        if doc_start == -1:
            issues.append(f"{filepath}:{axiom_name}: Missing doc comment")
            continue

        doc_content = content[doc_start:axiom_start]

        # Check for Source: keyword
        if not re.search(DOC_PATTERN, doc_content):
            issues.append(f"{filepath}:{axiom_name}: Missing 'Source:' in doc comment")

    return issues

def main():
    """Check all Lean files in Scaffold/Mathlib/."""
    scaffold_dir = Path('Scaffold/Mathlib')
    if not scaffold_dir.exists():
        print(f"Error: {scaffold_dir} not found")
        sys.exit(1)

    all_issues = []
    for lean_file in scaffold_dir.rglob('*.lean'):
        issues = check_file(lean_file)
        all_issues.extend(issues)

    if all_issues:
        print("Citation issues found:")
        for issue in all_issues:
            print(f"  {issue}")
        sys.exit(1)
    else:
        print("All axioms have proper citations!")
        sys.exit(0)

if __name__ == '__main__':
    main()
