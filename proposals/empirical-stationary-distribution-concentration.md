# Proposal: Concentration of the Empirical Stationary Distribution — a Real Consumer for Scalar Hoeffding

**Status:** COMPLETE — Steps 0+1 delivered 2026-08-27 (run
`20260827T234233Z-run-1`, the Step-0 survey verdict and the Step-1
fixed-time delivery below); Step 2 (the stationarity-limit form)
delivered 2026-08-31 (run `20260831T103057Z-run-1`, the follow-on
delivery record below, the consumer gate discharged by naming the
oversmoothing ceiling's empirical counterpart). This document
authorizes no Lean changes, axiom admissions, commits, or external
publication on its own beyond what its delivery record states.

## Step 0 verdict (2026-08-27, recorded before any shelf Lean)

**Tractable; the minimal sampling space is one module.** Surveyed
from repository evidence: no i.i.d. sampling measure space over
V-valued draws exists anywhere in the shelf — the only concrete
probability space is `Probability.BernoulliProduct`'s product
Bernoulli on `ι → Bool`, and the pinned Mathlib supplies no
coordinate-independence lemma on product measures (BernoulliProduct's
own scope note records both facts). The minimal object the fixed-time
form needs is that module's construction with the two-atom Bernoulli
factor replaced by an arbitrary normalized `q : V → ℝ`: the ∑-∏
arithmetic core (`Finset.sum_prod_piFinset`, the factorized
one-/two-coordinate marginals) generalizes verbatim. One genuine
interface difference: `ι → Bool` inherits its σ-algebra from Bool's
global discrete instance, while a general `V` must carry
`[MeasurableSpace V] [MeasurableSingletonClass V]` as instance
hypotheses — both discharge automatically on the graph fixtures'
`Fin n` vertex types. One graph-side gap: only `sum_walkDistribution`
existed; `walkDistribution_nonneg` (entrywise, by induction through
`walkDistribution_succ` at nonnegative weights) had to be added
beside it. The clause set of `hoeffding_empirical` needs exactly
three things at this space — `measurable_indicator_coord`,
`indepFun_indicator_coord`, and `integral_indicator` (`∫ 1_{ω e = i}
∂μ = q i`, the constant the axiom's internal centering collapses to)
— none needing a mixing argument, confirming the proposal's own
Step-0 guidance that the fixed-time form is the right first target.

## Step 1 delivery record (2026-08-27)

Delivered in three pieces, spike first (`wip/esd0_spike.lean`,
iterated to zero errors/warnings before any shelf Lean):

1. `Scaffold/Mathlib/Probability/IIDProduct.lean` — the V-valued
   i.i.d. product sampling space (`iidMass`/`iidPMF` at a normalized
   `q`, the one-/two-coordinate marginals `sum_coord_mul`/
   `sum_coord2_mul`, cylinder measures `toMeasure_cyl`, pairwise
   `indepFun_coord` of the projections, and the three
   `hoeffding_empirical` clause shapes: `measurable_indicator_coord`,
   `integral_indicator`, `indepFun_indicator_coord`) — pure hard
   crust, consumer-neutral (the module's docstring cross-lists this
   proposal's Step-0 verdict).
2. `walkTransitionMatrix_nonneg` + `walkDistribution_nonneg` in
   `GraphTheory/Mixing.lean` — the walk law certified entrywise
   nonnegative at every time; beside the delivered
   `sum_walkDistribution` this makes `walkDistribution A t₀ x` a
   legal factor distribution. Pure hard crust.
3. `Scaffold/Derived/EmpiricalStationary.lean` —
   **`hoeffding_empirical_iid`** (the generic composition: on the
   i.i.d. product space at any normalized `q`, the empirical visit
   frequency of `i` concentrates around `q i` at `2 exp(−2nt²)`;
   `n ≠ 0` load-bearing — the statement's clean centering is the
   collapse of `(1/n)∑∫`, which holds exactly when the average is
   genuine) and **`empiricalWalkDistribution_tail`** (the graph
   instance at `q = walkDistribution A t₀ x`; hypotheses: nonnegative
   weights and positive degrees — no symmetry, no connectivity, no
   mixing). Both conditional on `hoeffding_empirical` alone; every
   hypothesis clause proved hard crust. `#print axioms` via
   `wip/esd_axcheck.lean`: exactly `propext, Classical.choice,
   Quot.sound, hoeffding_empirical` on both, the standard three on
   all 14 sampling-module declarations and both Mixing lemmas.

QA +29 (2666 → 2695): `Scaffold/QA/Probability/IIDProduct_QA.lean`
(16 — the `Fin 2` fixture at `q = ![2/3, 1/3]`: four atom masses raw,
total mass by two routes, the indicator marginal raw vs the theorem,
the centering integral, the cylinder measures, the numeric
independence split `2/3 · 2/3 = 4/9` against the raw atom, and the
non-normalized-`q` fence `∑ iidMass ![2,0] = 4 ≠ 1`) and
`Scaffold/QA/Derived/EmpiricalStationary_QA.lean` (13 — the three
named obligations: the path-fixture closed form reused from
`Mixing_QA` with the theorem instance and the event honestly
characterized empty at `t = 1`; the `n = 0` boundary with the event
identified as `univ`, the bound evaluated to `2`, and the `n ≠ 0`
centering fence `0 ≠ 2/3`; and the raw two-sample measure `1/9` with
the numeric comparison `1/9 ≤ 2 exp(−1)` proved from
`Real.add_one_le_exp` at `−1/2`). The three tail-instantiating QA
theorems carry the axiom honestly (`wip/esd_qa_axcheck.lean`); the
raw computations are axiom-free by construction.

Verification: spike green before any shelf Lean; `lake env lean` zero
errors/zero warnings on all five touched/new files; explicit `lake
build` targets ✔ (2006/2006, 2192/2192, 2210/2210); full `lake build`
✔ followed by `check_build_completeness.py` — 123/123 fresh, 0
stale, 0 missing, exit 0 (one documented remediation: the new Derived
QA module sits outside the umbrella's import closure, built by
explicit target); `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (2695/10/0).

Technique findings for future runs: `ENNReal.ofReal_sum_of_nonneg`'s
direction (`←` to merge a factor sum); the elaboration trap behind
`∑ ω, iidMass q ω = 1` on a *function-space* index at a section-
variable codomain (annotate the binder: `∑ ω : ι → V, …` — the bare
form leaves `Fintype ?m` stuck); `omit`-of-used-section-variables is
*semantic* (`iidPMF`'s `Finset.univ` pulls `DecidableEq V` into its
signature, so downstream omits fail while the linter still flags the
variable — the resolution is a local
`set_option linter.unusedSectionVars false`); `Fin 2`-value
enumeration via `(by omega : (ω i).val = 0 ∨ …) + Fin.ext` (the
`fin_cases`-on-term route hits the recorded `(fun i => i) ⟨k, ⋯⟩`
wrapper); `Pi.single` and term-level `if`s reference `DecidableEq V`
(those omits fail too); the `← add_assoc` shape of a 4-atom
`sum_insert` chain (left-associated; the m-chain must match);
`abs_of_nonpos` for negative deviations; and the Nat-cast spelling
(`↑2` vs `(2 : ℝ)`) in `rw`-exponent normalizations — state the
equation with `((2 : ℕ) : ℝ)` or `norm_num` misfires.

## Deferred Step 2 (priced, not attempted)

The stationarity-limit form — concentration around `stationaryVec`
with `chiSquareDistance_le_of_connected`'s decay folded in as a bias
term via a triangle inequality — needs the mixing program's rate
statement composed with the fixed-time theorem delivered above; a
named consumer for the bias-term shape should price it first.


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


## Step 2 delivery record (2026-08-31, run `20260831T103057Z-run-1`)

Delivered per the Deferred section's own pricing gate — "a named
consumer for the bias-term shape should price it first" — with the
consumer named: **the oversmoothing ceiling's empirical counterpart**
(`proposals/message-passing-depth-mixing-bound.md`, delivered
2026-08-31 hours earlier). That ceiling bounds the *true* walk law's
entrywise distance to stationarity past a computable depth; Step 2 is
the statement an agent that can only *sample* the walk needs — past
the same depth certificate, `n` i.i.d. simulated trajectories estimate
the stationary value to `ε` with failure probability `2 exp (−n ε²/2)`.
The depth certificate of the mixing axis thereby becomes a sampling
guarantee, and the two most recent mixing-axis deliveries compose.
Zero new axioms (count stays 5); every declaration is pure hard crust
(`hoeffding_empirical` was retired 2026-08-30, so the whole chain —
sampler, tail engine, entrywise extraction, bias fold — is
axiom-free).

### The Lean

`Scaffold/Derived/EmpiricalStationary.lean`'s new `StationaryLimit`
section, two theorems:

- `empiricalWalkDistribution_stationary_tail` — the bias-term form:
  on a connected graph with a certified mixing rate `r` (exactly the
  oversmoothing ceiling's own hypothesis set), at any threshold
  strictly above the entrywise bias
  `r ^ t₀ √(π i ((π x)⁻¹ − 1))`,
  `P{|p̂_i(n) − π i| ≥ t} ≤ 2 exp(−2 n (t − bias)²)`. The one-line
  mathematical content is the triangle-route event inclusion
  `{|p̂ − π| ≥ t} ⊆ {|p̂ − ν_{t₀}| ≥ t − bias}` (with
  `|ν_{t₀} − π| ≤ bias` the proved
  `walkDistribution_sub_stationaryVec_abs_le`), closed by measure
  monotonicity into the delivered fixed-time tail — the proposal's
  own sketched "triangle inequality with the decay folded in as a
  bias term", stated at the direct-subset form rather than the
  two-event union split (strictly cleaner: one application, no union
  bound, the exponent paying only for the residual).
- `empiricalWalkDistribution_stationary_tail_of_depth` — the capstone:
  past the ceiling's own threshold computed at `ε / 2`, the bias is at
  most `ε / 2` (by the shelf's `pow_mul_le_of_log_threshold`), and the
  exponent arithmetic collapses `-2 n (ε − ε/2)²` to `-n ε² / 2`.

An honesty repair rode along: the module docstring and both Step-1
theorem docstrings still described the pair as **conditional on the
admitted axiom `hoeffding_empirical`** — stale since the 2026-08-30
retirement (the retirement's records already verified
`empiricalWalkDistribution_tail` hard crust; the index map already
said so) — now corrected, with the fact re-verified rather than
assumed (`#print axioms` in `wip/empstat2_axcheck.lean`).

### The QA (`EmpiricalStationary_QA.lean`'s Step-2 section, +7, 3306 → 3313)

On the triangle at the honest certificate `r = 1/2`, reusing the
oversmoothing QA's own pins:

1. the raw deviation `|ν₂ 0 0 − π 0| = 1/6` (walk law + stationary
   value, both raw) beside the bias `(1/2)² · √(2/3)` with the
   domination `1/6 ≤ (1/4)√(2/3)` *proved* — the fold-in is honest
   slack, witnessed, not asserted;
2. the bias-form interface instance at `t₀ = 2`, `n = 2`,
   `t = 1/2` (the exponent left closed-form in the bias);
3. the depth-form capstone instance at `ε = 1/4` (so the threshold
   hypothesis is *exactly* the delivered `tri_ceiling_threshold_three_QA`
   at `ε/2 = 1/8`), closing at the clean `2 exp(−1/16)`;
4. non-vacuity: the both-samples-at-`0` cylinder (mass
   `(ν₃ 0 0)² = 1/16` through `toMeasure_cyl_inter`) sits inside the
   measured event — the capstone bounds a real event;
5. the **fence**: the bias-free naive form — concluding around `π` at
   the empirical exponent with no bias term, i.e. treating the `t₀`-step
   law as already stationary — is *refuted* at `t₀ = 0`: the sampler
   law is `δ₀`, every outcome gives `p̂ = 1` and deviation `2/3`, so
   `{|p̂ − 1/3| ≥ 2/3}` is the whole space at measure `1`, against
   `2 exp(−16/9) < 1` (from `Real.add_one_le_exp (16/9)`, monotone
   inversion). The bias term — equivalently, the depth — is
   load-bearing;
6. the `t₀ = 0` corner of the delivered form itself: admitted with the
   honest large bias `√(2/3)` (not excluded by the strict guard), the
   event genuinely empty at `t = 1` — the form degrades gracefully as
   the bias grows, exactly the behavior the fence demands.

### Degenerate-corner analysis (the standing Step-0 discipline)

- `n = 0` is excluded by `hn` exactly as in Step 1 (its boundary
  behavior is fenced in the Step-1 QA; the strict guard is the same
  clause).
- `t₀ = 0`: analyzed and *pinned* rather than excluded — the form
  holds with the honest `O(1)` bias (QA item 6), and the naive
  no-bias reading is refuted (QA item 5). No hypothesis of the
  statement is satisfiable-vacuous here: connectivity and the rate
  certificate are the ceiling's own, unchanged.
- `t ≤ bias`: the strict guard `hbias` keeps the exponent meaningful;
  at `t ≤ bias` the bound statement is still true (the exponent is
  then nonpositive and `2 exp(·) ≥ 2 > 1 ≥` any PMF-derived measure)
  but shape-degenerate — the guard is for statement honesty, not
  truth, and the QA's fence pins why the guarded quantity is the
  meaningful one.

### Technique findings

1. `Real.add_one_le_exp` in the pinned Mathlib takes the *value*
   explicitly and carries no hypothesis
   (`Real.add_one_le_exp (x : ℝ) : x + 1 ≤ exp x`), while
   `Real.add_one_lt_exp (hx : x ≠ 0) : x + 1 < exp x` — a `by
   norm_num` passed where the value is expected leaves a `⊢ ℝ` goal,
   the bare-numeral elaboration trap in its most confusing costume.
2. `inv_le_inv_of_le` is deprecated to `inv_anti₀` in this pin.
3. `Real.sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y)` takes *both*
   hypotheses; the single-argument application misfires into a
   metavariable type error.
4. The stale-olen import-boundary recurrence bit once more at the
   Derived→QA boundary (rebuild the shelf target before elaborating
   the QA file) — consistent with the drift-pipeline run's finding.
5. `toMeasure_cyl_inter`'s rewritten goal keeps the cylinder family
   `A i` un-beta-reduced: a downstream `rw` against a beta-spelled
   pattern fails while `Finset.prod_const` (which abstracts under the
   binder) fires first; the robust order is prod-const → card →
   `Finset.sum_eq_single` applied *to the goal's own sum* (instance-
   preserving — a standalone `have` of the factor equation elaborates
   a different `Decidable` instance and will not rewrite).
6. `push_cast at h` (not `norm_num at h`) is the cast-normalizer
   that leaves measures and sets untouched — `norm_num` unfolds the
   measure into indicator sums and mangles `√(2/3)` into `√2/√3`.

### Verification

`lake env lean` zero errors/zero warnings on both touched modules;
explicit `lake build` targets ✔ on
`Scaffold.Derived.EmpiricalStationary` and
`Scaffold.QA.Derived.EmpiricalStationary_QA`; `#print axioms` via
`wip/empstat2_axcheck.lean` (11 audited: both new theorems, all seven
QA declarations, both de-staled Step-1 theorems) — every one exactly
`propext, Classical.choice, Quot.sound`; full `lake build` ✔
(2407/2408) immediately followed by `check_build_completeness.py` —
131 source files, 131 fresh artifacts, 0 stale, 0 missing, exit 0
(after the documented artifact-removal mtime remediation);
`lint_axioms` (5, both PF findings allowlisted-confirmed);
`check_refutation_independence` (10 tagged, clean);
`check_public_reachability` (62 modules); `check_citations`,
`check_markdown_links` pass; scoreboard regenerated at **3313/5/0**;
`check_scaffold_map_freshness` exit 0 after the 3306 → 3313 stats
sync in both map files and SVG regeneration. Records updated: this
document, `proposals/README.md` (the Medium-High row retired to the
Delivered table), README (3313), the radar QA axis (synced, 4.0 held
per protocol), `index/map/probability_concentration.md` (the two new
rows and the stale axiom-backed lead repaired), the scoreboard
verification row, both map data tables + regenerated SVG, the QA
module's purpose header, the execution plan, and the activity log.
Nothing committed; the previous runs' uncommitted deliveries
preserved.
