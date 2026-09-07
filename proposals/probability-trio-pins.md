# Proposal: The Probability Trio's Positive Pins

**Status:** COMPLETE (delivered 2026-09-07, run `20260907T135907Z-run-1`,
session `ses_f840b32f9ffeQquR0Tn6QqpJwb`; delivery record below).

The prior terminal handoff's named next batch ("the probability trio …
is the natural next batch — one shared-fixture run on the Bernoulli/iid
machinery"), executed exactly so: the census's three remaining
never-touched probability singles (inert 14, per
`wip/census_20260907_post13.txt`), first-consumed on ONE shared
fixture — the pins method's twelfth application and its first
scalar-concentration instantiation.

## Why these three, on one fixture

- **`hoeffding_iid` / `bernstein_iid`** (Scalar.Hoeffding/Bernstein) —
  the iid forms of the now-axiom-free scalar concentration stack:
  proved theorems since the 2026-08-30 retirements, never instantiated.
  Both need the same clause set (measurability, `iIndepFun`, bound,
  centering), so one family discharges both.
- **`indepFun_indicator_coord`** (IIDProduct) — the pairwise
  indicator-independence clause shape; its mutual twin
  (`iIndepFun_indicator_coord`) is consumed by the empirical layer, the
  pairwise form kept "for the refutation records" and never applied.

The fixture is the fair coin `prFair = ![1/2, 1/2]` on `Fin 2 → Fin 2`
with the ±1 family `prX k ω = if ω k = 0 then 1 else -1`: centered at
exactly the fair coin (the mean decomposition
`∫ prX = ∫ 1_{=0} − ∫ 1_{=1} = q 0 − q 1 = 0`, two `integral_indicator`
applications — no `integral_one` needed), bounded by `a = 1`, variance
`σ² = 1`, mutually independent through the shelf's
`iIndepFun_coord_apply` at the identity coordinate selection,
measurable through `measurable_coord` composition — the whole iid
supplier layer exercised in one configuration.

## The pins (15 QA theorems + 2 fixtures, QA 6727 → 6742)

- `pri_indepFun_indicator_pin` — the pairwise theorem consumed; **the
  two-route joint-mass join**: route A derives `μ{ω 0 = 0 ∧ ω 1 = 1}
  = 1/4` from the consumed `IndepFun` through the inter-preimage
  factorization and cylinder masses; route B computes the same `1/4`
  from `toMeasure_cyl_inter` alone (no independence) — two routes, one
  value.
- `pri_event_mass_raw` — the tail event `{ω | |∑ prX| ≥ 2}` is exactly
  the same-value pairs (the set-level decomposition), of raw mass
  `1/2`: the non-vacuity witness for both twin bounds.
- `pri_hoeffding_iid_pin` / `pri_bernstein_iid_pin` — both twins
  instantiated at `t = 2`, stated at the theorems' verbatim bound
  shapes, with `norm_num` display collapses to `2 exp(−1)` and
  `2 exp(−3/4)`.
- `pri_bound_contrast` — **the honest extremal-variance contrast**: at
  this Rademacher fixture (`σ² = a² = 1`) the variance term cannot
  help, and the Hoeffding bound is the strictly smaller one
  (`2 exp(−1) < 2 exp(−3/4)`, pure monotonicity, no numeric bound on
  `e`). The first draft's opposite direction was FALSE (`−3/4 < −1`
  fails — the elaborator caught it); the Bernstein-sharper direction
  needs an asymmetric family with `σ² < a²` on a biased coin — priced
  as a future fixture family, not owed.

## Delivery record (2026-09-07)

**Delivered at the full designed scope** — all three singles consumed,
15 QA theorems (+ the `prFair`/`prX` fixture definitions) in
`IIDProduct_QA.lean`'s new `SinglesPins` section, zero axiom contact
(`#print axioms` via `wip/prpins_axcheck.lean` on all 15 theorems —
every one exactly `propext, Classical.choice, Quot.sound`; the twins
are proved theorems, nothing admitted is touched).

**Verification.** Spike-first (`wip/prpins_spike.lean` — green after
ten fix rounds; traps recorded: **the `Decidable`-instance trichotomy**
on `if v ∈ S` sums — the goal's, a helper's, and the singleton-spelled
instances all differ syntactically, so `rw`/`simp only [helper]` on
set-membership ifs is fragile — cured by instance-agnostic
normalization (`Finset.sum_ite_eq'`, `Set.mem_singleton_iff`,
`mul_ite`) that erases the spelling before matching;
`ENNReal.ofReal_mul`'s hypothesis pinning the implicit `p`, so a
provided `0 ≤ 1/2` mismatches a goal spelled `2⁻¹` — provide the
goal's spelling; `Disjoint` for sets unfolding through `≤` with
membership-function conclusions; `fin_cases` on an application
`(ω k)` failing to parse where `omega` closes the Fin-2 dichotomy;
`Set.mem_inter_iff.1 hz` projection failing on metavars — state the
And-conclusion directly. The elaborator also caught the author's
backwards contrast inequality, recorded above). The landed module
elaborates with literally zero output (errors/warnings/infos).
Explicit build ✔. Full `lake build` + `check_build_completeness.py` —
135/135 fresh, 0 stale, 0 missing, exit 0. `lint_axioms` exit 0 (4
axioms unchanged). `check_refutation_independence` (24-tag clean).
`check_public_reachability` (63 modules). `check_citations`.
`check_markdown_links`. `check_qa_name_uniqueness` (the new
`prFair`/`prX`/`pri_*` names collision-free). `check_backlog_freshness`
clean. Scoreboard regenerated (1376 / 6742 / 4 / 0) with the
verification row. Map freshness exit 0 after the 6742 sync in both map
data tables + SVG regeneration (49 stations, no status change — none
owed). **Consumption closure verified by the tool**: the census re-run
(`wip/census_20260907_post14.txt`, diffed against `post13`) shows
exactly the 3 targeted theorems leaving the inert set — 1360 → 1363
value-consumed, 14 → 11 never-touched, no bonus, no collateral.

**Remaining risk:** none owed — QA-only, no axiom disposition changed,
no public statement changed. Honest scope: one fixture family (the
fair coin, `n = 2`, `t = 2`); the joint-mass join at one pair of level
sets; the event mass at one threshold; the twins' bounds at their
verbatim shapes. The Bernstein-sharper direction is priced, not owed.
