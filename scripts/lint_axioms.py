#!/usr/bin/env python3
"""Lint axiom declarations for consistency."""

import os
import re
import sys
from pathlib import Path

def check_axiom_in_public_api():
    """Check that no axioms are in the wrong location."""
    issues = []

    # Check for axioms in Trusted (should use theorem := by sorry)
    trusted_dir = Path('Scaffold/Trusted')
    if trusted_dir.exists():
        for lean_file in trusted_dir.rglob('*.lean'):
            with open(lean_file, 'r') as f:
                content = f.read()
            if re.search(r'^axiom\s+', content, re.MULTILINE):
                issues.append(f"{lean_file}: Found 'axiom' in Trusted directory (use 'theorem := by sorry')")

    return issues

def check_index_coverage():
    """Check that axioms are documented in index files."""
    issues = []

    # Extract all axiom names from Lean files
    axiom_names = set()
    for lean_file in Path('Scaffold/Mathlib').rglob('*.lean'):
        with open(lean_file, 'r') as f:
            content = f.read()
        for match in re.finditer(r'^axiom\s+(\w+)', content, re.MULTILINE):
            axiom_names.add(match.group(1))

    # Check if mentioned in index files (warning only)
    for axiom_name in axiom_names:
        found = False
        for index_file in Path('index').rglob('*.md'):
            with open(index_file, 'r') as f:
                if axiom_name in f.read():
                    found = True
                    break
        if not found:
            issues.append(f"Warning: Axiom '{axiom_name}' not found in index files")

    return issues

def main():
    """Run all lint checks."""
    issues = []

    # Check for axioms in wrong location
    issues.extend(check_axiom_in_public_api())

    # Check index coverage (warnings)
    issues.extend(check_index_coverage())

    if issues:
        for issue in issues:
            print(issue)
        if any('Warning' not in i for i in issues):
            sys.exit(1)
    else:
        print("No lint issues found!")

if __name__ == '__main__':
    main()
