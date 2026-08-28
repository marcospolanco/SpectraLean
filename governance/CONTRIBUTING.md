# Contributing to Scaffold

Thank you for your interest in contributing to Scaffold!

## Types of Contributions

We welcome several types of contributions:

## Center-Out Scope Policy

Spectral graph theory is the repository's organizing center. New work must
identify the concrete, broadly reusable SGT theorem, definition, dependency,
or experiment it unlocks. Adjacent topics are in scope when they form the
shortest credible path to that objective.

Before implementation, compare the proposal with existing load-bearing work:

- build and import failures;
- placeholder definitions or statement shapes;
- missing citations and index coverage;
- reusable SGT definitions and bridge theorems;
- validated applications.

Prefer the change that unlocks the most reusable SGT progress, improves assurance, and has the lowest justified complexity. If outer-layer work exposes a defect closer to the SGT center, repair that inner dependency first.

### 1. Axiom Addition

Adding new textbook results as axioms with proper citations.

**Requirements:**
- Lean axiom with full documentation and citation
- Update `index/sources/<source>.md`
- Update `index/map/<area>.md`
- Follow naming conventions
- QA coverage or a review note explaining why thin QA is not applicable

**QA Requirement:**
For every new axiom file, normally provide at least one QA lemma in `Scaffold/QA/` that:
- Uses the axiom in a nontrivial way
- Has a real Lean proof (not `sorry`)
- Proves a well-known consequence that domain experts expect
- Exercises a relevant part of the axiom's interface
- Is small enough to diagnose when the interface changes

**QA Documentation Required:**
Every axiom should include a `QA:` comment documenting which QA lemmas exercise it or why thin QA is not applicable. See the [architecture and QA contract](../docs/2_ARCHITECTURE.md) for the current policy.

QA checks usability and selected consequences relative to axioms; it does not prove those axioms.

### 2. Index Improvement

Enhancing the mapping between sources and axioms.

**Examples:**
- Adding more detailed bibliographic information
- Improving cross-references
- Adding new source documents

### 3. API Cleanup

Refactoring without breaking changes.

**Examples:**
- Improving documentation
- Reorganizing internal structure
- Adding convenience theorems (proved, not axioms)

### 4. Migration PR

Replacing an axiom with a mathlib re-export.

**Process:**
- Verify mathlib theorem is equivalent
- Replace axiom with import
- Update deprecation notices

## Submission Process

1. **Check existing issues** - Someone may already be working on it
2. **Fork the repository** - Create a branch for your work
3. **Make your changes** - Follow the guidelines below
4. **Submit a PR** - Include the checklist below

## Pull Request Checklist

### For Axiom Addition

- [ ] Lean file with `axiom` declarations
- [ ] Doc comments with citations for each axiom
- [ ] `index/sources/<source>.md` updated
- [ ] `index/map/<area>.md` updated
- [ ] Changed modules compile directly; `lake build` alone may not reach every module
- [ ] No `sorry` in `Scaffold/Mathlib/**`
- [ ] `python3 scripts/lint_axioms.py` passes, including the degenerate-corner guard check — a flagged new axiom gets its allowlist entry (recording why the corner is accepted) at admission time
- [ ] Names follow mathlib conventions
- [ ] QA coverage or a documented not-applicable rationale
- [ ] QA lemma compiles and uses the new axiom
- [ ] **Each axiom has `QA:` documentation** referencing QA lemmas
- [ ] Referenced QA lemmas exist and are appropriately scoped

### For QA Lemmas

- [ ] Real Lean proof (no `sorry` or `admit`)
- [ ] Exercises the relevant definition or axiom interface
- [ ] Proves a well-known consequence
- [ ] File named appropriately: `<Domain>_<Topic>_QA.lean`

### For Other Changes

- [ ] Changed modules compile directly; record unrelated baseline build failures
- [ ] Documentation updated if needed
- [ ] Follows existing patterns and conventions
- [ ] New scope includes its SGT dependency and leverage rationale

## Code Style

- Follow mathlib naming conventions (lower_snake_case)
- Use mathlib types and definitions when possible
- Keep axioms minimal and focused
- Add doc comments for all public declarations
- Follow the [canonical architecture](../docs/2_ARCHITECTURE.md) for quality and QA requirements

## Three-Layer Architecture

This project uses a three-layer architecture:

1. **Public Axiom APIs** (`Scaffold/Mathlib/`) - Textbook-anchored definitions and explicit axioms
2. **QA Lemmas** (`Scaffold/QA/`) - Simple sanity checks with real proofs
3. **Derived Work** (`Scaffold/Derived/`, planned, or downstream) - Novel mathematics built on 1 and 2

When contributing, identify which layer you're working in and follow the standards for that layer.

## Review Process

Maintainers will review your PR and may request:
- Clarification of citations
- Adjustments to naming
- Additional documentation
- Splitting large PRs into smaller pieces

For a theorem with several hypotheses, reviewers should also ask whether
each one is actually necessary, not just used by the proof as written —
see [Adversarial Review](ADVERSARIAL_REVIEW.md) for the full methodology
and a real example this check found.

## License

By contributing, you agree that your contributions will be licensed under the Apache 2.0 License.

## Questions?

Feel free to open an issue with the `question` label.
