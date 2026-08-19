# Proposal: Tikhonov Regularization in the Laplacian Eigenbasis

**Status:** Proposed; priority **High**. Assistant's assessment of project
direction, requested 2026-08-19, promoted from `sgt-gaps.md` item 4.
Authorizes no Lean changes, axiom admissions, or external publication.

Companion to `sgt-gaps.md` and `finite-relative-entropy.md` (comparable
cost profile — a direct corollary of already-proved eigenbasis machinery,
no new infrastructure). No backlog gate applies.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard graph-signal-processing sources
(Shuman et al.). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean`
(`eigvecOf_complete`, `quadForm`, the eigenbasis expansion machinery
already used by `prove-lambda2-variational.md` and the electrical
program), confirming the closed-form minimizer below is a direct
corollary with no missing Mathlib pieces.

## External consumer

Graph signal processing's standard smoothing operator — semi-supervised
label propagation, graph signal denoising, and any application wanting a
smooth-but-not-projected reconstruction. One of the most cited operators
in the graph signal processing literature (Shuman, Narang, Frossard,
Ortega & Vandergheynst, "The Emerging Field of Signal Processing on
Graphs," IEEE Signal Processing Magazine 30(3), 2013 — **citation
unverified**, confirm before use in a committed docstring).

## Recommendation

For `y : V → ℝ` and `π : ℝ` (`0 < π`), define the minimizer of
`‖x − y‖² + (1/π) · xᵀLx` over `x : V → ℝ` and prove its eigencoefficients
are

```
c_k(x*) = π / (λ_k + π) · c_k(y)
```

— a low-pass shrinkage filter: every mode attenuated by a factor strictly
in `(0,1)`, decreasing in `λ_k`, none exactly zeroed. State explicitly,
alongside the theorem, that this is **not** a projection (unlike
`spectralProjector`) — the two are easily conflated, and the distinction
(every mode survives, attenuated, vs. some modes are zeroed exactly) is
the entire point of the operator.

## Why this is cheap

The minimizer's existence and uniqueness are a direct strict-convexity
argument (the objective is a strictly convex quadratic in `x`, since `L`
is PSD and the `‖x-y‖²` term is strictly convex on its own). The
closed-form eigencoefficient identity falls out of expanding both terms
in the eigenbasis via `eigvecOf_complete` and minimizing termwise — each
mode decouples because `L`'s eigenbasis simultaneously diagonalizes both
quadratic terms. No new Mathlib machinery needed anywhere in this proof;
it is algebra over the already-proved eigenbasis expansion, the same
technique `Foster.lean` and `prove-lambda2-variational.md` already used.

## Build order

### Step 1: The minimizer and its existence/uniqueness

Define `tikhonovMinimizer (A : WAdj) (hA : A.IsSymm) (hnonneg : ...) (π :
ℝ) (hπ : 0 < π) (y : V → ℝ) : V → ℝ` (via `Classical.choice` over the
strict-convexity argument, or directly via the eigenbasis formula below —
decide which is cheaper before writing the statement, per this
repository's standing rule). Prove it is the unique minimizer of
`‖x − y‖² + (1/π) · quadForm (laplacian A) x`.

### Step 2: The closed-form eigencoefficient identity

Prove `⟪eigvecOf (laplacian A) hA k, tikhonovMinimizer A hA hnonneg π hπ
y⟫ = π / (evals hA k + π) * ⟪eigvecOf (laplacian A) hA k, y⟫` for every
`k`, by expanding both quadratic terms in the eigenbasis and minimizing
per-coefficient (each mode's minimization is a one-variable quadratic,
solved by `deriv = 0`).

### Step 3: The shrinkage-factor properties

Prove the attenuation factor `π / (λ_k + π)` is strictly in `(0,1)` for
every `λ_k ≥ 0` (from `π > 0` and `λ_k ≥ 0`), strictly decreasing in
`λ_k`, and never exactly `0` or `1` — the facts that make this a
shrinkage filter rather than a projection or the identity. State the
not-a-projection distinction explicitly as a corollary or docstring note.

## QA plan

- Positive witness: a small fixture (`K₂` or the 3-vertex path), `y`
  concrete, `tikhonovMinimizer` computed both from the definition and via
  the closed-form eigencoefficient identity, cross-checked to agree.
- Shrinkage witness: the attenuation factor computed numerically at two
  different `λ_k` values on the same fixture, confirming the ordering
  (larger `λ_k` ⇒ smaller factor).
- Negative/distinguishing witness: compare `tikhonovMinimizer` against
  `spectralProjector`'s output on the same fixture and `y`, showing they
  disagree — concrete evidence the two are not the same operator, guarding
  the "not a projection" claim rather than leaving it asserted.

## Operating instructions for an autonomous run

- One step per run; all three are small enough that a single run may
  cover more than one if the first lands cleanly.
- **No new axioms.** This proposal's entire cost case is that nothing
  here needs machinery beyond the already-proved eigenbasis expansion —
  if a step turns out to need something genuinely absent, stop and record
  the obstruction rather than admitting anything.
- Survey Mathlib's convexity/minimization API before Step 1 in case a
  ready-made strict-convex-minimizer-exists lemma is cheaper than the
  direct eigenbasis construction.

## Open next step

Unblocked now — begin with Step 1.
