# Proposal: Approximate Spectral Projection with Error Bounds

**Status:** Proposed; priority **Medium**, contingent on Step 0 — do not
begin Step 1 before Step 0's scoping decision is recorded. Assistant's
assessment of project direction, requested 2026-08-19, promoted from
`sgt-gaps.md` item 7. Authorizes no Lean changes, axiom admissions, or
external publication.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard numerical-linear-algebra sources
(Saad; Trefethen & Bau). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean`
(`spectralProjector`, the exact eigendecomposition machinery this
proposal's subject approximates), `icebox/lyapunov-stability-
formalization-gap.md` (the closest precedent in this repository for
"a genuinely different kind of math than what's already here"), and a
search of the pinned Mathlib for Lanczos/Chebyshev/Nyström machinery
(none found).

## External consumer

Large-scale spectral clustering, where Lanczos, Chebyshev/polynomial
filters, and Nyström approximation are literally how the exact
eigendecomposition this repository builds on gets replaced at scale in
practice; GNN pooling layers using the same approximations (Saad,
*Numerical Methods for Large Eigenvalue Problems*; Trefethen & Bau for
the polynomial-filter view — **citations unverified**, confirm before
committed use).

## Why this needed a correction from the original triage, not exclusion

`sgt-gaps.md`'s first pass toward this item recommended iceboxing it
rather than writing a proposal, on the grounds that it is fundamentally
about *iterative numerical algorithms and their convergence rates* — a
different kind of formalization than everything else delivered so far
(closed-form identities over finite-dimensional linear algebra). That
diagnosis stands, but exclusion was the wrong response to it: every other
item promoted from `sgt-gaps.md` earned its priority by being scoped, not
by being easy, and this item deserves the same treatment — a mandatory
Step 0 that either finds a tractable finite slice or records precisely
why there isn't one, the same pattern `decidable-spectral-certificates.md`
and this session's other Step-0-gated proposals already use. Recommending
icebox was treating uncertainty as disqualifying; the honest move is to
scope the uncertainty instead.

## The candidate shapes, precisely

Each method needs an error bound relating approximation quality to
iteration count or sample size:

- **Lanczos**: after `k` iterations on a symmetric matrix, the Ritz
  values approximate the extremal eigenvalues with an error bound in
  terms of the spectral gap and `k`.
- **Chebyshev / polynomial filters**: a degree-`d` polynomial
  approximation to a spectral indicator function (e.g., a band
  projector), with an error bound in `d` and the target function's
  smoothness at the polynomial's approximation region.
- **Nyström**: a low-rank approximation to a PSD matrix from a sampled
  subset of rows/columns, with an error bound in sample size.

## Calibration — why "finite-iteration" is the load-bearing scoping choice

The original assessment's own honesty is the key signal: "nothing else
in this list depends on this item." Combined with the different-kind-of-
math diagnosis above, the right target is not general asymptotic
convergence theory (which would need real-analysis machinery on
sequences and limits closer to `icebox/lyapunov-stability-
formalization-gap.md`'s caution about calculus-on-a-parameter than to
anything this repository has built) but a **fixed, finite iteration
count** statement: for a specific `k` (or `d`, or sample size), state and
prove a concrete numerical bound, not a limiting statement as `k → ∞`.
This stays inside Scaffold's existing finite-dimensional idiom — Step 0
below is where this distinction gets tested for real, not assumed.

## Build order

### Step 0: Scope and survey (mandatory; may find nothing tractable)

For each of the three candidate shapes, in order of apparent cost
(Lanczos first, being the most classical and most likely to have a clean
finite-`k` statement; Nyström second; Chebyshev/polynomial filters
third, since it composes with the not-yet-delivered
`spectral-band-projectors.md`):

1. Write down the exact finite-`k` (or finite-sample) statement in full
   mathematical precision — not the asymptotic textbook version.
2. Identify every piece of machinery the proof needs (matrix powers,
   polynomial evaluation on a symmetric matrix via the eigenbasis,
   concentration bounds for Nyström specifically) and check each against
   what Scaffold and Mathlib already provide.
3. Record a real cost estimate per shape. If all three come back
   intractable at reasonable cost, **stop here and icebox this
   proposal** rather than forcing a Step 1 — this is the honest outcome
   the original triage anticipated, reached by scoping rather than
   skipping straight to it.
4. If at least one shape is tractable, proceed with only that shape;
   drop the others from this proposal's scope rather than attempting all
   three.

### Step 1 (only for whichever shape Step 0 finds tractable)

State and prove the finite-`k` error bound, using whichever route Step 0
identifies. Likely needs its own sub-decomposition across multiple runs
— treat as at least as hard as the electrical program's harder steps
were scoped to be, per this repository's own calibration precedent.

## QA plan

- Positive witness: a small fixture with a known spectrum, the
  approximation computed at a small concrete `k`/`d`/sample size and
  compared numerically against the exact `spectralProjector` (or `evals`)
  output, with the error bound checked to hold.
- Tightness witness, if feasible: a fixture where the bound is close to
  attained, distinguishing a real bound from a vacuously loose one.

## Operating instructions for an autonomous run

- Step 0 is mandatory and may legitimately terminate this proposal
  without any Lean code landing — that is a valid, recorded outcome, not
  a failure.
- **No new axioms.** If Step 0 finds a shape tractable but Step 1 later
  hits missing machinery, stop and record the precise obstruction rather
  than admitting anything.
- Do not attempt more than one of the three candidate shapes in the same
  run, and do not attempt Step 1 on a shape Step 0 did not explicitly
  clear.

## Open next step

Step 0's Lanczos survey — unblocked now, the recommended first shape to
scope given its relative classical maturity.
