#!/usr/bin/env python3
"""Check that axioms have proper citations."""

import os
import re
import sys
from pathlib import Path

AXIOM_PATTERN = r'^axiom\s+(\w+)'
SOURCE_PATTERN = r'Source:'

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

        # Look backwards for the nearest doc comment. Both `/-- ... -/`
        # and plain `/- ... -/` blocks carry documentation in this
        # repository, so take whichever is closest to the axiom.
        doc_starts = [pos for pos in
                      (content.rfind('/--', 0, axiom_start),
                       content.rfind('/-', 0, axiom_start))
                      if pos != -1]
        if not doc_starts:
            issues.append(f"{filepath}:{axiom_name}: Missing doc comment")
            continue
        doc_start = max(doc_starts)

        doc_content = content[doc_start:axiom_start]

        # A citation is a `Source:` marker anywhere in the doc comment
        # preceding the axiom (not only at the very start of the block,
        # which is what an earlier, stricter pattern required).
        if not re.search(SOURCE_PATTERN, doc_content):
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
