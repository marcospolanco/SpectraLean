# Strategy

**Status:** Canonical project strategy  
**Last reviewed:** August 17, 2026

## Mission

Scaffold is a Lean library for making selected, modern applied-mathematics results usable before their foundational proofs are available in Mathlib. It exposes those results as explicit, cited axioms with mathlib-compatible types and tests their interfaces with small, fully proved QA lemmas.

The project optimizes for transparent assumptions and replaceable APIs. It does not claim that an axiom has been formally proved, that a citation has been independently verified merely because it is present, or that a QA lemma establishes the truth of its dependencies.

## Who it serves

- Applied researchers who want Lean to check new deductions while treating established literature as an explicit trust boundary.
- Lean developers who need stable interfaces for concentration, perturbation, and spectral graph theory.
- Formalizers looking for a structured backlog of useful results that may later be proved upstream.
- Research collaborators evaluating SGT questions and executable research
  pipelines.

## Ecosystem pacing

The internal shorthand “rabbit” describes a pacing choice, not competition with Mathlib. Mathlib prioritizes proved, reusable foundations and community review. Scaffold can move faster in a narrow applied domain because it admits cited statements at an explicit axiom boundary. The tradeoff is reduced assurance: downstream proofs are conditional on those axioms.

Scaffold should therefore stay subordinate and interoperable:

1. Reuse Mathlib definitions and naming where practical.
2. Admit only the smallest statements needed for current applications.
3. Record citations and modeling differences.
4. Replace Scaffold declarations when suitable proved upstream results appear.

## Why spectral graph theory is a useful focus

The intended applications cross several formal domains: finite graph combinatorics, matrices and operator norms, probability and concentration, and perturbation theory. A usable result often depends on all four. That intersection makes API alignment as important as theorem availability.

Spectral persistence is already developed elsewhere and is retained here only
as an existing compatibility/example package. It is not Scaffold's research
goal or the criterion for choosing new work. Scaffold's agenda is to grow a
broad, reusable neighborhood around SGT, so future research can start from
well-specified graph, spectral, probabilistic, and operator-theoretic APIs.

## Center-out prioritization

Spectral graph theory is the organizing center for ongoing work. The repository expands outward only along dependencies that unlock a concrete SGT theorem, research experiment, or downstream application.

The working rings are:

1. **SGT center:** graph and Laplacian definitions, quadratic and Rayleigh forms, spectra, variational characterizations, Cheeger theory, and buildable QA.
2. **Mathematical bridges:** perturbation theory, matrix concentration, probability, and update identities needed by a center obligation.
3. **Reusable SGT extensions:** general interfaces and tools with more than
   one plausible SGT consumer.
4. **Research applications:** domain observables and experiments that name
   their needed SGT interfaces.

Work may proceed outward only when the inward dependency path is explicit.
When adjacent or application work reveals an ambiguous definition, missing
assumption, placeholder, or broken interface, the priority moves inward to
the nearest load-bearing defect.

### Leverage test

Compare proposed work using these questions:

- How many concrete SGT proof obligations or consumers does it unlock?
- Does it repair a load-bearing definition or reduce the axiom/admission surface?
- Will the interface be reused across multiple SGT results?
- Does it improve alignment with Mathlib and make upstream replacement easier?
- Can progress be verified through a focused proof, build, citation review, or experiment?
- Is the expected gain worth its implementation and maintenance cost?

Build health, meaningful statement shapes, real definitions, and source fidelity outrank new breadth. Adjacency to SGT is not sufficient by itself; the dependency and leverage case must be documented in the issue or pull request.

## Conjecture pathfinding

The project uses a disciplined search loop for turning an application goal into formal targets under incomplete information:

1. **State the observable.** Define the quantity the application can actually measure.
2. **State the desired guarantee.** Express the operational success condition as a typed mathematical relation.
3. **Build the dependency graph.** Identify definitions, textbook results, bridge lemmas, and genuinely novel claims.
4. **Classify every edge.** Mark it as proved upstream, axiom-backed, locally proved, experimentally supported, or conjectural.
5. **Choose the smallest frontier cut.** Admit or investigate only the missing statements that unlock the next testable result.
6. **Run falsification checks.** Exercise edge cases, dimensions, zero denominators, symmetry assumptions, and small examples.
7. **Promote carefully.** Move a claim from hypothesis to theorem only when its proof and dependencies justify that status.

This process treats conjecture generation as constrained search. It is a prioritization method, not an automated proof of novelty or correctness.

## Success measures

Scaffold is succeeding when:

- downstream work can import narrow APIs without importing unrelated assumptions;
- every public axiom has precise provenance and an explicit trust cost;
- QA exercises meaningful consequences without `sorry` or `admit`;
- current build and coverage status can be reproduced;
- upstream replacements reduce, rather than expand, the axiom surface;
- research hypotheses are connected to measurable experiments and formal proof obligations.

## Source provenance

This document distills the archived [project assessment](../research/archive/gem-scaffold-assessment.md) and [pathfinding transcript](../research/archive/pathfinding.md). Those files preserve historical reasoning; this document controls current strategy.
