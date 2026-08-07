# Contributing to Scaffold

Thank you for your interest in contributing to Scaffold!

## Types of Contributions

We welcome several types of contributions:

### 1. Axiom Addition

Adding new textbook results as axioms with proper citations.

**Requirements:**
- Lean axiom with full documentation and citation
- Update `index/sources/<source>.md`
- Update `index/map/<area>.md`
- Follow naming conventions
- **At least one QA lemma** (see QA Policy below)

**QA Requirement:**
For every new axiom file, you must provide at least one QA lemma in `Scaffold/QA/` that:
- Uses the axiom in a nontrivial way
- Has a real Lean proof (not `sorry`)
- Proves a well-known consequence that domain experts expect
- Would fail if the axiom was mis-stated
- Is trivially derivable (1-5 lines from the axiom)

**QA Documentation Required:**
Every axiom must include a `QA:` comment documenting which QA lemmas exercise it. See `governance/QA_POLICY.md` for the format and examples.

See `governance/QA_POLICY.md` for full details.

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
- [ ] Code compiles with `lake build`
- [ ] No `sorry` in `Scaffold/Mathlib/**`
- [ ] Names follow mathlib conventions
- [ ] **At least one QA lemma** with real proof in `Scaffold/QA/`
- [ ] QA lemma compiles and uses the new axiom
- [ ] **Each axiom has `QA:` documentation** referencing QA lemmas
- [ ] Referenced QA lemmas exist and are trivially derivable

### For QA Lemmas

- [ ] Real Lean proof (no `sorry` or `admit`)
- [ ] Uses the axiom it's QA-ing in a nontrivial way
- [ ] Proves a well-known consequence
- [ ] File named appropriately: `<Domain>_<Topic>_QA.lean`

### For Other Changes

- [ ] Code compiles with `lake build`
- [ ] Documentation updated if needed
- [ ] Follows existing patterns and conventions

## Code Style

- Follow mathlib naming conventions (lower_snake_case)
- Use mathlib types and definitions when possible
- Keep axioms minimal and focused
- Add doc comments for all public declarations
- Follow `governance/QUALITY_CRITERIA.md` for quality standards
- Follow `governance/QA_POLICY.md` for QA requirements

## Three-Layer Architecture

This project uses a three-layer architecture:

1. **Trusted Axioms** (`Scaffold/Trusted/`) - Textbook results with no proofs
2. **QA Lemmas** (`Scaffold/QA/`) - Simple sanity checks with real proofs
3. **Derived Work** (`Scaffold/Derived/`) - Novel mathematics built on 1 and 2

When contributing, identify which layer you're working in and follow the standards for that layer.

## Review Process

Maintainers will review your PR and may request:
- Clarification of citations
- Adjustments to naming
- Additional documentation
- Splitting large PRs into smaller pieces

## License

By contributing, you agree that your contributions will be licensed under the Apache 2.0 License.

## Questions?

Feel free to open an issue with the `question` label.
