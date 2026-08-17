# Formal Architecture and Axiom Engineering

**Status:** Canonical technical and policy specification  
**Last reviewed:** August 17, 2026

## 1. Scope and assurance

Scaffold is a mathlib-compatible Lean library that exposes selected published results as explicit axioms. The architecture makes the trust boundary visible and supports later replacement by proved upstream theorems.

Scaffold guarantees only what the artifacts establish:

- Lean compilation checks types and proofs relative to imported declarations and axioms.
- A proof that depends on an axiom is conditional on that axiom.
- QA lemmas test interface usability and selected consequences; they do not prove the axioms or certify citation fidelity.
- Citations are provenance for human review, not machine-checked evidence.

## 2. Implemented repository layers

### Layer 1: public axiom APIs

Location: `Scaffold/Mathlib/**`

This subtree mirrors Mathlib topics where practical. It contains real definitions and explicit axioms for results not yet proved locally. Public declarations should be narrow enough to replace independently.

### Layer 2: QA proofs

Location: `Scaffold/QA/**`

QA files contain fully elaborated proofs of small properties, special cases, or cross-interface consequences. They must contain no `sorry` or `admit`. A QA lemma is useful when failure would reveal an API-shape, assumption, or composability problem.

### Layer 3: derived research

`Scaffold/Derived/**` is reserved but not currently implemented. Novel work may also live in a downstream repository. Derived claims must distinguish proved Lean theorems from axiom-backed results.

`Scaffold/Trusted/` currently contains explanatory material; it is not the public axiom location.

## 3. Public API contract

The public API consists of declarations reachable through `Scaffold.Mathlib.*` imports. Changes should follow these rules:

- prefer Mathlib types, predicates, and naming conventions;
- use focused modules and minimal imports;
- state all mathematical preconditions explicitly;
- preserve names and statement shapes within a compatible release line;
- avoid umbrella imports for narrow downstream use;
- document edge cases and fallback behavior for partial operations.

The matrix-first spectral graph representation uses `Matrix V V ℝ` because it composes directly with finite-dimensional linear algebra, perturbation bounds, and event updates. This does not eliminate the need for adapters to Mathlib graph structures.

## 4. Definition standards

Core mathematical objects must be real definitions, not constants chosen merely to make a file elaborate. In particular:

- do not define a spectrum, norm, quotient, or projector as an unconditional `0` placeholder;
- do not use `True` as the type of an intended mathematical result;
- guard division by zero and state invertibility or positivity requirements;
- preserve symmetry, diagonal, and sign invariants by construction when feasible;
- document deliberately noncomputable definitions and their mathematical meaning.

Legacy declarations that violate these rules are migration debt and must be reported in the QA pillar. The policy is a target enforced on new changes, not a claim that all current source already complies.

## 5. Axiom admission policy

An axiom is admissible only when all of the following hold:

1. It unlocks a concrete downstream use case.
2. Its conclusion is meaningful and composable.
3. Its assumptions include dimensions, symmetry, positivity, independence, measurability, boundedness, or spectral gaps as applicable.
4. Its documentation cites an authoritative source precisely enough to locate the result.
5. The documentation explains any difference between the source statement and the Lean statement.
6. The axiom has a small blast radius and does not bundle unrelated facts.
7. Relevant source and topic indices are updated.
8. At least one QA obligation is identified, or the review explains why no useful thin QA exists.

Use `axiom` for an intentional trust boundary. Do not disguise that boundary with `theorem := by sorry` in public modules.

## 6. QA contract

A QA proof must:

- compile with no `sorry` or `admit`;
- exercise a real definition or public axiom;
- check a mathematically meaningful property;
- remain small enough to diagnose interface failures;
- avoid claiming that a trivial consequence validates the source theorem.

Proof length is a heuristic, not a correctness criterion. A longer elementary proof may belong in QA when Lean requires bookkeeping; a one-line tautology does not become valuable because it is short.

Useful categories include structural invariants, nonnegativity, zero-update cases, dimensional compatibility, edge-case behavior, and cross-axiom coherence.

## 7. Quality review

Reviewers assess five dimensions:

| Dimension | Questions |
| --- | --- |
| Definitions | Are core objects real, guarded, and mathematically recognizable? |
| Statement shape | Are assumptions explicit and conclusions usable? |
| API design | Is naming consistent, scope narrow, and organization coherent? |
| Mathlib compatibility | Are standard types and predicates reused where practical? |
| Documentation | Are limitations, citations, and modeling choices clear? |

Event-driven modules additionally review whether updates preserve required invariants and whether perturbation bounds refer to the same representation and norm as the update model.

## 8. Citation and index policy

Every public axiom should include author, title, theorem or section locator, and edition/page where relevant. Files under `index/sources/` map references to Lean identifiers; files under `index/map/` map subject areas to declarations. Large quotations or copyrighted source text do not belong in the repository.

The citation checker is a hygiene tool. Human mathematical review remains necessary.

## 9. Upstream replacement lifecycle

When Mathlib or another accepted dependency provides a proved replacement:

1. Compare assumptions, conclusion, conventions, and namespace—not just the theorem name.
2. Add an adapter theorem if the shapes differ but are equivalent.
3. Run the affected QA and downstream checks against the replacement.
4. Deprecate the Scaffold declaration with a migration note.
5. Retain compatibility for the documented deprecation window unless the declaration is unsound or unsafe.
6. Remove the axiom and update citation/topic indices in the next permitted release.

An emergency removal is appropriate for a materially false statement, an inconsistent assumption set, or a declaration that creates unacceptable trust exposure. Release notes must identify the impact.

## 10. Toolchain and verification

The repository pins Lean and Mathlib in `lean-toolchain` and `lakefile.lean`. The default build, direct module checks, QA placeholder scan, axiom lint, citation check, and Markdown link check measure different properties and must be reported separately.

The generated [QA scoreboard](5_QA_SCOREBOARD.md) is the authority for current counts and recorded check results.

## 11. Contribution workflow

A change to the public axiom layer should include:

- the SGT obligation or consumer it unlocks and why it outranks nearer load-bearing work;
- the declaration and documentation;
- citation and topic-index updates;
- QA coverage or a stated reason it is not applicable;
- a successful check of the changed module and its consumers;
- a compatibility note when changing an existing declaration.

Community process is defined by `governance/CONTRIBUTING.md`, `MAINTAINERS.md`, and `RELEASES.md`.

## 12. Known architectural debt

- The probability concentration subtree (`Scaffold.Mathlib.Probability.Concentration.*`) does not elaborate (malformed syntax, invalid binder annotations, undefined interfaces) and is excluded from the umbrella; its QA file is uncertified.
- Spectral-projector idempotence and eigenbasis orthonormality behind `spectralProjector` are consumed through the admitted perturbation interfaces rather than proved locally.
- The planned derived layer is not present.
- Citation mappings for the uncertified concentration subtree are incomplete (for example, `matrix_azuma_hoeffding` lacks a `Source:` marker); page-level locators for Horn–Johnson and Chung chapter-level citations are pending review.
- There is no executable target; the former `scaffold` executable referenced a missing `Main.lean` and was removed from the default build until a real driver exists.

These are tracked as facts, not hidden by the target architecture.

## Source provenance

This document consolidates the archived [full project specification](../research/archive/governance/PROJECT_SPEC.md) and former policies for [design](../research/archive/governance/SCAFFOLD_DESIGN.md), [axioms](../research/archive/governance/AXIOM_POLICY.md), [QA](../research/archive/governance/QA_POLICY.md), [deprecation](../research/archive/governance/DEPRECATION_POLICY.md), and [quality](../research/archive/governance/QUALITY_CRITERIA.md).
