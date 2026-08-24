# Proposal: Concentration of the Empirical Stationary Distribution — a Real Consumer for Scalar Hoeffding

**Status:** Proposed; **priority:** Medium-High. This document authorizes
no Lean changes, axiom admissions, commits, or external publication on
its own — Step 0 (the survey below) must land before Step 1 begins.

## The obligation this discharges

`hoeffding_inequality` and `hoeffding_empirical`
(`Scaffold/Mathlib/Probability/Concentration/Scalar/Hoeffding.lean`) are
two of the seven admitted axioms with **zero theorem consumers** —
referenced only by their own file and a QA file that instantiates each
at the degenerate zero sequence (`hoeffding_inequality_zero_QA`, the
empty-event vacuous case). No proof in this repository has ever
exercised `hoeffding_empirical`'s exact centering/boundedness clause
structure against a real random variable, so a misstated clause
(wrong denominator, wrong bound direction) would currently break
nothing. This proposal gives it a graph-theoretic consumer: concentration
of the *empirical* stationary distribution estimated by simulating a
random walk, around the *true* `stationaryVec` this repository already
has closed-form (`Scaffold/Mathlib/GraphTheory/Mixing.lean:106`).

## Assessed from

`Scaffold/Mathlib/GraphTheory/Mixing.lean` (`stationaryVec`,
`stationaryVec_pos`, `sum_stationaryVec`, `walk_isStationary`,
`walkDistribution`, `chiSquareDistance_le_of_connected` — the mixing-time
program, delivered and COMPLETE per `mixing-time-bound.md`, already
gives the *exact* deterministic decay of `walkDistribution t` toward
`stationaryVec`), `Scaffold/Mathlib/GraphTheory/RandomWalk.lean`
(`transitionMatrix`, `randomWalkLaplacian`), and
`Hoeffding.lean`'s `hoeffding_empirical` (the `[0,1]`-bounded empirical-mean
tail bound, stated exactly at `2 exp(-2 n t²)` — the natural per-vertex
indicator-visit-frequency form).

## The statement (draft shape — subject to Step 0 correction)

This is deliberately **not** a new probabilistic-graph-theory
construction — no new random-walk sample-path measure space is built
from scratch here if the shelf already has one; Step 0's first job is to
check whether one exists or must be added (see below). Given `n`
independent simulated random-walk states (e.g. `n` independent walks of
fixed length `t` started from a fixed distribution, or `n` samples from
the stationary chain if a mixing/coupling argument is already
available), and the empirical visit-frequency estimator at vertex `i`,

```
p̂_i(n) = (1/n) * ∑ (k < n), indicator (walk_k = i)
```

the target theorem is the two-sided concentration bound around the true
value:

```
P {|p̂_i(n) - trueValue_i| ≥ t} ≤ 2 * exp (-2 * n * t²)
```

where `trueValue_i` is either `stationaryVec A i` (if the walks are
started from stationarity or run long enough that the mixing bound's
decay is folded in as an additional deterministic bias term) or
`walkDistribution A t₀ x i` at a fixed finite time `t₀` (the cleaner,
weaker statement — no mixing argument needed, `hoeffding_empirical`
applies directly to i.i.d. draws of a fixed-time distribution). **Step 0
should pick the fixed-time form first** — it composes `hoeffding_empirical`
with nothing but `walkDistribution`'s own definition (already a genuine
probability distribution by `sum_walkDistribution`), with no new
measure-theoretic random-walk infrastructure required. The
stationarity-limit form is a natural but strictly harder follow-on
(needs `chiSquareDistance_le_of_connected`'s decay rate folded in as a
bias term via a triangle inequality) and should be recorded as a
deferred Step 2, not attempted in the same run.

**Step 0 must check:** whether an i.i.d.-sampling measure space over
`n` independent copies of a `Fin t → V`-valued random walk already
exists anywhere in the shelf (it likely does not — `RandomWalk.lean` is
purely the deterministic transition-matrix machinery); if it does not,
whether building the minimal one (a product measure of `n` copies of a
walk-path distribution, each mapped to its final-state indicator) is
in scope for a single Step-1 run or is itself a separate prerequisite
proposal. This is the actual cost driver, not the Hoeffding application,
which is mechanical once the measure space exists.

## QA obligations (draft — refine after Step 0)

1. A small fixture (K₂ or a 3-cycle) where `walkDistribution A t₀ x`
   is closed-form (already true for these fixtures per `Mixing_QA.lean`
   precedent), so the concentration bound's target value is pinned
   independently of the theorem.
2. The `n = 0` / degenerate boundary consistent with `hoeffding_empirical`'s
   own documented junk-value behavior at `n = 0`.
3. If the sampling measure space is newly built: a raw two-sample
   instantiation (`n = 2`) checked by hand against the formula, the same
   route-independence discipline used throughout this session's other
   deliveries.

## Acceptance bar

- Step 0 delivers a written verdict on the measure-space cost before any
  shelf Lean is written; "not tractable at reasonable cost in one step"
  (i.e., the sampling infrastructure itself is the real project) is a
  valid recorded outcome that iceboxes or re-scopes this proposal.
- If Step 1 proceeds: zero new axioms; `hoeffding_empirical` appears
  honestly in `#print axioms` on the new public theorem.
- `docs/7_SGT_RADAR.md` axis 7 (Algorithms/Randomness) is the natural
  re-score target.

## Companion

[A Spectral Mixing-Time Bound (delivered)](mixing-time-bound.md),
`docs/6_SGT_BACKLOG.md`, `docs/7_SGT_RADAR.md` axis 7.
