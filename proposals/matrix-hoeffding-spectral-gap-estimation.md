# Proposal: Concentration of a Sampled Laplacian's Quadratic Form — a Real Consumer for Matrix Hoeffding

**Status:** Proposed; **priority:** Medium. This document authorizes no
Lean changes, axiom admissions, commits, or external publication on its
own — Step 0 (the survey below) must land before Step 1 begins.

## The obligation this discharges

`matrix_hoeffding`
(`Scaffold/Mathlib/Probability/Concentration/Matrix/Hoeffding.lean`) is
one of the seven admitted axioms with **zero theorem consumers** —
referenced only by its own file and the thin zero-sequence QA check. Its
docstring already names an intended use ("the matrix concentration
statement consumed by Scaffold's event-stream frontier: bounded
per-event Laplacian perturbations with independent events") that has
never actually been discharged — a recorded intent, not a proof
obligation anyone has picked up. This proposal is that pickup: a small,
self-contained consumer distinct from and simpler than
[spectral-sparsification-via-leverage-scores.md](spectral-sparsification-via-leverage-scores.md)'s
`matrix_bernstein` route (Hoeffding needs no variance statistic, only a
semidefinite bound `X i ω² ⪯ A i²` per term — mechanically simpler to
instantiate, a good first exercise of the matrix-concentration axiom
family before the harder Bernstein-based sparsification argument).

## Assessed from

`Scaffold/Mathlib/Probability/Concentration/Matrix/Hoeffding.lean`
(the exact semidefinite-order hypothesis `Matrix.PosSemidef (A i * A i -
X i ω * X i ω)`, no centering required), `Scaffold/Mathlib/GraphTheory/
VariationalTransfer.lean` (`normalizedLaplacian_psd`,
`rayleigh_normalizedLaplacian_degreeSqrt` — itself a second
zero-real-consumer module, referenced only by its own file: this
proposal incidentally loads two under-exercised modules with one
theorem), and the event-stream frontier's own docstring pointer (name
only verified, content not yet read in detail — Step 0's first task).

## The statement (draft shape — subject to Step 0 correction)

Given `n` independent bounded per-event Laplacian perturbations
`X i : Ω → Matrix V V ℝ` (Hermitian, each satisfying the semidefinite
bound `X i ω * X i ω ⪯ A i * A i` for a fixed deterministic bound matrix
`A i`, e.g. a single-edge-weight perturbation bounded by its own
conductance), the target theorem composes `matrix_hoeffding` with the
normalized-Laplacian quadratic form to get a *scalar* concentration
statement usable by the rest of the graph-theoretic shelf without
carrying matrix-norm machinery downstream:

```
P {|quadForm (∑ i, X i ω) x| ≥ t * ‖x‖²} ≤
    2 * card V * exp (-t² / (2 ‖∑ i, A i ^ 2‖))
```

for a fixed test vector `x` (e.g. the Fiedler vector, or `onesVec`),
via `Matrix.L2OpNorm`'s operator-norm bound on the quadratic form
(`|quadForm M x| ≤ ‖M‖ * ‖x‖²`, a standard Cauchy–Schwarz-style
inequality — Step 0 must confirm this exact lemma or its equivalent is
in the pin under the `L2OpNorm` API before stating the corollary this
way).

**Step 0 must check:** (1) whether `‖M‖ * ‖x‖² ≥ |quadForm M x|` is
already in the pin for `Matrix.L2OpNorm`, or needs a short proof from
the operator norm's definition; (2) what the "event-stream frontier"
docstring pointer actually refers to — if there is already a partially-built
consumer elsewhere in the shelf (an event-driven Laplacian-update module
under `GraphTheory/Dynamics` per the discrete-affine proposal's naming
note), this proposal should compose with it rather than duplicate it;
(3) whether a fixed, non-random test vector `x` is a sufficient first
statement, deferring the sup-over-`x` / operator-norm-of-the-whole-sum
form (a strictly stronger and harder statement, likely its own follow-on).

## QA obligations (draft — refine after Step 0)

1. A small fixture (K₂ or a path on 3 vertices) with a hand-computable
   bound matrix `A i` and a concrete `x` (e.g. `onesVec` or the Fiedler
   vector on the fixture), the resulting scalar bound evaluated in
   closed form.
2. The `n = 0` degenerate case (empty sum, vacuous bound), consistent
   with the axiom's own zero-sequence QA pattern.
3. A boundary witness where the semidefinite hypothesis fails for one
   term — the hypothesis-free form refuted in proved form on the same
   fixture, per this session's established fence discipline.

## Acceptance bar

- Step 0 delivers a written verdict — including an explicit check of
  whether this duplicates unstarted event-stream-frontier work — before
  any shelf Lean is written.
- If Step 1 proceeds: zero new axioms; `matrix_hoeffding` appears
  honestly in `#print axioms` on the new public theorem;
  `VariationalTransfer.lean`'s existing PSD/Rayleigh lemmas are reused,
  not re-derived.
- `docs/7_SGT_RADAR.md` axis 7 (Algorithms/Randomness) is the natural
  re-score target.

## Companion

[Spectral Sparsification via Leverage-Score Sampling](spectral-sparsification-via-leverage-scores.md)
(the harder, Bernstein-based sibling consumer), `docs/6_SGT_BACKLOG.md`,
`docs/7_SGT_RADAR.md` axis 7.
