# Axiom Policy

This document defines the policy for adding and managing axioms in Scaffold.

## Principles

1. **Axioms are explicit**: All trusted assumptions are declared as `axiom`, never hidden in `sorry`
2. **Axioms are minimal**: Each axiom should be as small and focused as possible
3. **Axioms are cited**: Every axiom must include a precise citation to a primary source
4. **Axioms are replaceable**: All axioms are designed to be replaced by mathlib theorems

## Axiom Requirements

Every axiom in `Scaffold/Mathlib/**` must:

### 1. Include Documentation

```lean
/--
Brief description of the mathematical statement.

Source:
- Author, Title, Edition (if applicable)
  Chapter/Section, Theorem Number, Page (if possible)

Intended meaning:
Explanation of how this Lean statement maps to the mathematical result.
-/
```

### 2. Use Mathlib Types

- Prefer existing mathlib definitions (MeasureTheory, ProbabilityTheory, etc.)
- Avoid reinventing foundational types unless absolutely necessary
- Match mathlib naming conventions

### 3. Be Minimal and Composable

- Prefer many small axioms to one large axiom
- Each axiom should capture a single mathematical concept
- Make dependencies explicit and minimal

### 4. Update Indices

Every axiom PR must update:
- `index/sources/<source>.md` - map theorems to Lean identifiers
- `index/map/<area>.md` - group axioms by topic

## Allowed Locations

### `Scaffold/Mathlib/**` (Public API)
- **Allowed**: `axiom` declarations with proper citations
- **Forbidden**: `sorry`, `admit`, `by sorry`

### `Scaffold/Trusted/**` (Quarantine)
- **Allowed**: `theorem := by sorry` for experimental work
- **Never allowed in public API**

## Review Checklist

Maintainers verify for each axiom:

- [ ] Statement is faithful to the cited source
- [ ] Hypotheses are explicit and minimal
- [ ] Citation is precise (author, title, location)
- [ ] Name follows mathlib conventions (lower_snake_case)
- [ ] Types are from mathlib when possible
- [ ] No `sorry` in `Scaffold/Mathlib/**`
- [ ] Index files are updated

## Removal Process

When mathlib provides an equivalent theorem:

1. Replace `axiom` with import and re-export
2. Keep the same identifier if possible
3. Mark as deprecated in CHANGELOG
4. Update index to note mathlib availability

## Emergency Removal

If an axiom is found to be incorrect:
1. Immediately deprecate in a patch release
2. Add warning in documentation
3. Track replacement in issues
