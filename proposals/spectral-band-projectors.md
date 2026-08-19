# Proposal: Spectral Band Projectors

**Status:** Proposed; priority **High**. Assistant's assessment of project
direction, requested 2026-08-19, promoted from `sgt-gaps.md` item 5.
Authorizes no Lean changes, axiom admissions, or external publication.

Companion to `sgt-gaps.md` and `Scaffold/Mathlib/GraphTheory/Spectral.lean`'s
already-delivered `spectralProjector`, of which this proposal is a direct
generalization. No backlog gate applies.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard functional-analysis sources.
Do not copy this proposal verbatim.

Assessed from `Spectral.lean:271` (`spectralProjector M hM c`, the
below-threshold projector already delivered and load-bearing for
`initialProjector`) and
`.lake/packages/mathlib/Mathlib/Analysis/InnerProductSpace/Projection.lean`
(the Hilbert projection theorem, confirmed present 2026-08-19).

## External consumer

Bandpass filtering in graph signal processing; frequency-selective
analysis (e.g., functional-connectivity work studying a specific band of
a network's spectrum rather than the whole thing).

## Recommendation

Define the two-sided band projector for an interval `[a, b]` of the
spectrum and prove: idempotence, self-adjointness, orthogonality of
disjoint bands, and completeness when a family of bands **partitions**
the spectrum. Add the Hilbert-projection-theorem specialization: the band
projector's output is the closest point in its range to the input.

## Why this is cheaper than the original assessment rated it

`spectralProjector M hM c` (`Spectral.lean:271`) **already is** the
below-threshold half of this construction: it projects onto every
eigenvector with `eigvalOf ≤ c`. A two-sided band is the *difference* of
two existing `spectralProjector` calls:

```
bandProjector M hM a b := spectralProjector M hM b - spectralProjector M hM a
```

restricted conceptually to eigenvalues in `(a, b]`. This is not a
from-scratch construction — it is composition of an object already
delivered and QA'd, which is why this is rated cheaper than the original
outside assessment's "medium," and a clean instance of this repository's
own "reuse what's proved" discipline actually paying off.

## Design note — parameterize by interval, not index

Do not hard-code the construction to the low end (a "top-`k`" or
"bottom-`k`" projector). Parameterize the band by a spectral interval
`(a, b]`, with the below-threshold case falling out as `bandProjector M
hM (-∞) c` conceptually (or as `spectralProjector` directly, kept as the
named special case rather than re-derived). A construction that only
expresses low bands states strictly less and closes off the general
result. Bands that **partition** the spectrum (a finite, ordered sequence
of thresholds covering the full range) avoid the specific failure mode
where a gapped definition silently ignores every mode strictly between
two thresholds — the completeness theorem should be stated over a
partition, not assumed pairwise.

## Build order

### Step 1: The two-sided band projector and its basic properties

Define `bandProjector M hM a b := spectralProjector M hM b -
spectralProjector M hM a` (for `a ≤ b`). Prove idempotence and
self-adjointness — both should transfer cheaply from
`spectralProjector_symmetric` and the existing idempotence argument for
`spectralProjector` itself (survey whether that idempotence lemma already
exists before reproving it).

### Step 2: Orthogonality of disjoint bands

For `a ≤ b ≤ c ≤ d`, prove `bandProjector M hM a b` and `bandProjector M
hM c d` project onto orthogonal subspaces (they share no eigenvector,
since the eigenbasis is orthonormal and the two eigenvalue ranges are
disjoint).

### Step 3: Completeness under a partition

For a finite ordered sequence of thresholds `t₀ < t₁ < ... < tₙ` covering
the full spectrum's range, prove the sum of the resulting band projectors
equals the identity — the completeness statement the design note above
requires be stated over a partition, not pairwise.

### Step 4: The Hilbert-projection-theorem specialization

Prove `bandProjector M hM a b x` is the closest point in its range to
`x`, by instantiating Mathlib's Hilbert projection theorem
(`Analysis/InnerProductSpace/Projection.lean`) at the band's eigenspace,
survey the exact lemma signature first.

## QA plan

- Positive witness: a small fixture with a known multi-eigenvalue
  spectrum (reuse an existing pinned-spectrum fixture from
  `CourantFischer_QA.lean` or `Variational_QA.lean`), the band projector
  computed at a concrete interval and checked against a hand-computed
  eigenvector sum.
- Partition witness: the completeness identity instantiated on the same
  fixture with a concrete partition, the sum checked to equal the
  identity matrix from independent computation.
- Negative witness: a band interval that excludes a mode strictly between
  its endpoints on a fixture with a tight eigenvalue gap, confirming the
  excluded mode is genuinely absent from the projector's range — guards
  the "silently ignores a mode" failure mode the design note names.

## Operating instructions for an autonomous run

- One step per run.
- **No new axioms.** Every step composes `spectralProjector` (already
  proved) with either elementary linear algebra or Mathlib's Hilbert
  projection theorem. If Step 4's instantiation needs machinery not on
  the shelf, stop and record the exact obstruction.
- Survey `spectralProjector`'s existing lemma set precisely before Step 1
  — reuse rather than reprove idempotence/symmetry if already available
  in a directly usable shape.

## Open next step

Unblocked now — begin with Step 1.
