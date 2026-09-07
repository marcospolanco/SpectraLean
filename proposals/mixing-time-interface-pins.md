# Proposal: The Mixing-Time Interface Layer's Positive Pins

**Status:** COMPLETE (delivered in the opening run, run
`20260907T020912Z-run-1`, session `ses_f8684723effefqlJShDqrQZ0l1`;
delivery record below)

## Why this, why now

The compiler-derived consumption census's terminal handoff named the
mixing-time interface layer its top remaining target after Tikhonov.
A fresh census run at this run's opening (`wip/census_20260907.txt`,
81 → 70 inert — reproducing the Tikhonov delivery's closure claim
mechanically) re-confirmed the ranking: **ten designed-but-unconsumed
interface theorems** across `DirectedMixing` (4) and `Oversmoothing`
(6) — the `t_mix` object family's field-standard interfaces
(`_spec`, `_anti`, `_le_of_rate`, `_le_of_escalation`,
`_le_of_connected`, `_le_of_depth`, the entrywise max-rate ceiling).

**SGT leverage:** the `t_mix` object family is the walk/diffusion
axis's field-standard interface (LPW ch. 20's objects). The prior QA
pinned the objects and *evaluated the interfaces' displays* beside
them — attainment pins that re-derive both sides separately without
ever applying the interface theorem — so none of the interfaces'
proof-term content was exercised by QA. This delivery puts real
weight on all ten: each pin derives a concrete threshold, bound, or
lower-bound THROUGH the interface, at fixtures whose exact values are
already independently pinned (so a wrong-shaped interface makes the
pin's numeric claim fail or its proof break).

One aspirational-consumption docstring claim was verified and is now
made true: `lazyWalkMixingTimeFrom_le_of_connected`'s docstring cites
`path_lazy_center_ceiling_attained_QA` as its QA, but that pin
evaluates the display and the object separately (the Tikhonov
header-claim pattern, second instance).

## Step 0: the census (exact, compiler-derived)

The ten never-consumed theorems (the fresh census's inert list,
confirmed by the post-delivery re-run below):

- **DirectedMixing:** `pageRankMixingTimeFrom_le_of_rate`,
  `pageRankMixingTimeFrom_anti`, `pageRankMixingTime_le_of_rate`,
  `pageRankMixingTime_le_of_escalation`.
- **Oversmoothing:** `walkMixingTime_spec`,
  `walkMixingTime_le_of_escalation`, `lazyWalkMixingTimeFrom_anti`,
  `lazyWalkMixingTimeFrom_le_of_connected`,
  `lazyWalkDistribution_tvDistance_le_of_depth`,
  `walkDistribution_sub_stationaryVec_abs_le_max_rate`.

## Step 1: the pins (18 QA theorems, two modules)

**At `DirectedMixing_QA.lean`'s `A2` fixture** (periodic 2-cycle,
α = 1/2; TV closed forms `TV(t) = (1/2)^{t+1}`, objects pinned in both
directions at `1/8` and `1/32`):

1. **`mtip_From_rate_le_QA`** — the per-start rate ceiling's display
   evaluates to `⌈log 4/log 2⌉ = 2` THROUGH
   `pageRankMixingTimeFrom_le_of_rate`, re-deriving `PR_tmix_eighth_QA`'s
   ≤ half by the rate route (that pin used the witness certificate;
   `PR_tmix_ceiling_attained_QA` had evaluated both sides separately).
2. **`mtip_From_anti_lb_QA`** — `2 ≤ t_mix(1/16)` THROUGH
   `pageRankMixingTimeFrom_anti` (from the pinned `t_mix(1/8) = 2`):
   a lower bound delivered by antitonicity, a genuinely different
   mechanism than the attainment route.
3. **`mtip_From_sixteenth_QA`** — the completion
   `t_mix(1/16) = 3` (≤ by witness; ≥ by attainment), with (2) beside
   it.
4. **`mtip_unif_rate_le_QA`** — the uniform rate ceiling:
   `t_mix^unif(1/8) ≤ 2` THROUGH `pageRankMixingTime_le_of_rate`
   (`d̄(0) = 1/2` evaluates the display to the pinned exact value).
5. **`mtip_unif_escalation_le_QA`** — the ⌈log⌉ display escalation
   THROUGH `pageRankMixingTime_le_of_escalation` at the delivered
   certified evaluation (`t₀ = 2`, `d̄(2) = 1/8`, `d(2) = 1/4`): the
   display reads `(⌈log 4/log 4⌉ + 1)·2 = 4` — the pinned exact
   object value (the delivered `PRU_escalation_attained_QA` had
   consumed only the `_mul_` sibling).

**At `Mixing_QA.lean`'s `triAdj`/`pathAdj` fixtures:**

6. **`mtip_walk_spec_QA`** — the uniform certificate at EVERY depth
   (`∀ s ≥ 2, ∀ x, TV(s, x) ≤ 1/6`) derived THROUGH
   `walkMixingTime_spec` from the pinned `walkMixingTime triAdj (1/6)
   = 2`.
7. **`mtip_walk_escalation_le_QA`** — the display escalation THROUGH
   `walkMixingTime_le_of_escalation` at the certified evaluation
   (`t₀ = 1`, `d̄(1) = 1/3`, `d(1) = 1/2`): the display reads
   `(⌈log 2/log 2⌉ + 1)·1 = 2` — the pinned exact `t_mix(1/6) = 2`.
8. **`mtip_lazy_anti_lb_QA` / `mtip_lazy_sixteenth_QA`** — the lazy
   antitonicity lower bound `2 ≤ t_mix_lazy(1/16)` THROUGH
   `lazyWalkMixingTimeFrom_anti` (from the pinned corner-start
   `t_mix_lazy(1/8) = 2`) and the completion `= 3`.
9. **`mtip_lazy_ceiling_le_QA`** — the intrinsic-rate ceiling's ≤
   direction consumed for the first time (the docstring's claim made
   true): `t_mix_lazy(corner, 1/8) ≤ 3` THROUGH
   `lazyWalkMixingTimeFrom_le_of_connected`, with the display
   `⌈log(4√3)/log 2⌉ = 3` evaluated by the rational route
   (`1 < √3 < 2` from `1 < 3 < 4` through log monotonicity) — the
   honest `3` against the pinned exact `2`, exactly the slack the
   docstring describes; the two threshold-evaluation companions
   (`mtip_path_thr_lt_QA`/`_le_QA`) are the shared arithmetic.
10. **`mtip_lazy_depth_le_QA`** — the depth-form TV ceiling THROUGH
    `lazyWalkDistribution_tvDistance_le_of_depth` at the corner start
    and depth `3` (the threshold fires; exact TV `(1/2)⁴ = 1/16` —
    honest slack).
11. **`mtip_walk_abs_rate_QA`** — the entrywise max-rate ceiling
    THROUGH `walkDistribution_sub_stationaryVec_abs_le_max_rate` at
    the triangle: the bound evaluates to `(1/2)·√(2/3)` against the
    pinned true deviation `1/6` (the numeric reading
    `mtip_walk_abs_rate_value_QA` beside it), with the fresh
    top-eigenvalue companion `mtip_tri_top_eval_QA`
    (`evals ⟨2⟩ = 3/2` — every eigenvalue `0` or `3/2`, sorted, and
    `λ₂ = 3/2` forces the top up).

## QA obligation

The pins are the QA. No shelf change; zero axiom contact (all-proved
shelf, theorem instantiations, no `-- @refutes` tags apply).

## Delivery record (2026-09-07)

DELIVERED at the full designed scope in the opening run: 18 QA
theorems (DirectedMixing_QA 186 → 192, Mixing_QA 763 → 775; QA 6561 →
6579), QA-only, zero axiom contact (`#print axioms` via
`wip/mtifaces_axcheck.lean` on all 18 — every one exactly
`propext, Classical.choice, Quot.sound`; the 24-tag independence
check unchanged and clean).

**Consumption closure, verified by the tool**: the census re-run
(`wip/census_20260907_post.txt`) shows 11 theorems leaving the inert
set — the 10 targeted interfaces PLUS
`lazyWalkDistribution_tvDistance_le_of_connected`, reached
transitively through the ceiling theorem's own proof chain (an honest
bonus, recorded as such). Census: value-consumed 1287 → 1298, never
touched 70 → 59 (the pre-run had already absorbed the Tikhonov
delivery's 11).

Verification: spike-first (`wip/mtifaces_spike.lean` — green after
~8 fix rounds; the recorded traps: the named-argument/positional
hypothesis order of the escalation interfaces, `lt_div_iff₀` vs
`div_le_iff₀` side-dispatch (div on which side of the relation),
`Nat.ceil_le.mp` needing a fully concrete ℕ bound (the `by omega`
meta-variable trap — ascribe the intermediate), `mul_lt_mul_of_pos_
left` vs `_right` operand order, and `sq_le_sq'` being the WRONG
direction for numeric sqrt comparisons — `sq_lt_sq'` with
`-b ≤ a` is the route); both landed modules elaborate with zero
errors (Mixing_QA's three pre-existing `ring_nf` suggestions verified
pre-existing — the identical spike code was silent); explicit `lake
build` of both modules ✔; **full `lake build` +
`check_build_completeness.py` — 135 source files, 135 fresh
artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4
axioms unchanged); `check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new `mtip_*`
names collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (6579) with the verification row; map freshness exit 0
after the stats sync in both map data tables + SVG regeneration.

Remaining risk: none owed — QA-only, no axiom disposition changed, no
public statement changed. QA proves consequences relative to the
substrate; it does not prove the substrate (no axiom touched). Honest
scope: the pins are at three fixtures (A2 two-cycle, triangle, path)
and one lazy corner start; the escalation/rate displays are EXACT at
the two-cycle and triangle but honest-slack at the path (the
intrinsic-rate ceiling's `3` vs `2`).
