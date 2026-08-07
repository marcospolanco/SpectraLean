# Internal Utilities

This directory contains internal utilities and style definitions for Scaffold.

## Purpose

This module is for:

- Shared `simp` sets and tactics
- Internal notation and conventions
- Helper theorems and lemmas
- Development and testing utilities

## Policy

**NOT part of the public API**

Content in this directory:
- May change without notice
- Is not subject to deprecation policy
- Should not be imported by downstream users

## Modules

### `Style.lean` (planned)

Shared simp sets and notation:

- Common simp sets for probability calculations
- Notation for measure-theoretic expressions
- Tactic extensions for concentration inequalities

## When to Add Here

Add utilities here when:

1. They are used by multiple internal modules
2. They are not part of the public API contract
3. They may change frequently as the library evolves

## When NOT to Add Here

Do NOT add here:

- Public API definitions (use `Scaffold/Mathlib/**`)
- Axioms or theorems (use `Scaffold/Mathlib/**`)
- Content that downstream users need (use `Scaffold/Mathlib/**`)

## See Also

- [Core Definitions](../Mathlib/Core/README.md) for public shared definitions
- [Contributing Guidelines](../../../../governance/CONTRIBUTING.md)
