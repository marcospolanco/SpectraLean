# The i.i.d.-Product Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run
`20260905T211403Z-run-1`, session
`ses_f8c962534ffeFk8IsV5RX3OWXM`; see the delivery record).

## Scope

The prior terminal handoff's named natural next target — "the audit
method's natural next target by this run's survey numbers:
**`IIDProduct`** (2 transitive non-QA consumers, its QA carrying one
free-form fence `junk_normalization_fence_QA` never reconciled)" —
confirmed by this run's own import walk: `Probability.IIDProduct`
feeds `GraphTheory.Mixing` and the `Derived/EmpiricalStationary`
capstone (plus the umbrella). The shelf is
`Scaffold/Mathlib/Probability/IIDProduct.lean` (476 lines, 2 defs +
17 public theorems): the `V`-valued i.i.d. product sampling space
`iidPMF` and the interfaces that discharge `hoeffding_empirical`'s
`h_meas`/`h_indep`/mean clauses at a concrete measure. Everything on
the shelf is proved — no axiom — so this is a theorem-instantiation
audit (no `-- @refutes` tags; the fences refute dropped-hypothesis
statement shapes of proved theorems, consuming nothing admitted).

**SGT leverage:** this shelf is the sampling engine of the
empirical-stationary program — the `Derived/EmpiricalStationary`
capstone's trajectories and `GraphTheory.Mixing`'s walk laws
instantiate exactly these independence and mean clauses. A wrong
product structure here — a marginal that does not factor, an
independence transfer that survives a non-injective reindexing, a
normalization hypothesis that is not load-bearing — would poison
every conditional sampling guarantee downstream while every QA
stayed green. The audit makes each clause shape falsifiable at its
source.

Its QA (`IIDProduct_QA.lean`, 284 lines) carries the positive pin
layer (four-atom mass enumeration, raw-vs-theorem routes, the
clause-shape constants, cylinder and independence numerics) and
exactly one free-form fence — `junk_normalization_fence_QA` (the
mass sum at the non-normalized `q = ![2, 0]`) — never reconciled
into the per-clause hypothesis-form discipline. Method:
`governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier, irregular Cheeger, regular Cheeger,
effective-resistance, electrical-flow, Foster, sparsification-core,
band-projector, Davis–Kahan core, normalized, variational-transfer,
resolvent, Perron–Frobenius, heat, random-walk, stationary,
irreducible-stationary, directed, spectral-core (Steps 0–4),
matrix-concentration, Bernoulli-product, scalar-concentration).

## Step-0 findings: the priced fence list

Clause census over the shelf's 17 public theorems — 12 carry
mathematical hypotheses; three are hypothesis-free (`iidMass_ne_top`,
`measurable_coord`, `measurable_indicator_coord`; nothing to drop).
Four clause shapes:

1. **`hq0 : ∀ v, 0 ≤ q v` (and `hq1 : ∑ v, q v = 1`)** on the four
   ∑-theorems whose statements do not mention `iidPMF`:
   `sum_mass_eq_one`, `sum_iidMass_eq_one`, `sum_coord_mul`,
   `sum_coord2_mul`. Fenceable at out-of-bounds factor distributions
   keeping the other clause genuine: `q = ![-1, 2]` breaks `hq0` only
   (the `ENNReal.ofReal` clamp zeroes the negative coordinate's
   mass; kept `hq1` genuine at `-1 + 2 = 1`), `q = ![2, 0]` breaks
   `hq1` only (kept `hq0` genuine). On `V = Fin 2` the first three
   theorems' kills land at the four-atom enumeration (`0 + 2 = 2 ≠ 1`
   at the mass level; `4 ≠ 1` and `4 ≠ 2` at the joint level);
   `sum_coord2_mul` needs the **outside-the-consumed-coordinates
   rule** (the Bernoulli-product audit's pricing finding, transposed
   from sample coordinates to the same role): on `ι = Fin 2` both
   quantified coordinates are consumed by the statement, so the
   dropped identity is true there by Fubini (`(2+0)² = 2·2`); a third
   coordinate on `ι = Fin 3` multiplies the left side only
   (`2³ = 8 ≠ 4 = 2·2`).
2. **`hq0`/`hq1` on the nine `iidPMF q hq0 hq1`-consuming theorems**
   (`iidPMF_apply`, `toMeasure_cyl`, `indepFun_coord`,
   `integral_indicator`, `indepFun_indicator_coord`,
   `toMeasure_cyl_inter`, `iIndepFun_coord`,
   `iIndepFun_coord_apply`, `iIndepFun_indicator_coord`):
   **signature-entangled** — `iidPMF q hq0 hq1` takes the proofs as
   arguments, so the dropped statement cannot be formed out of
   bounds; the sampling measure does not exist there (the module
   docstring says exactly this: "outside `0 ≤ q` and `∑ q = 1` the
   joint masses fail to sum to `1` and `iidPMF`'s hypotheses cannot
   be discharged — fenced in QA at `q = ![2, 0]`"). The mass-level
   fences of item 1 are that entanglement's visible boundary.
3. **`hee : e ≠ e'`** on `sum_coord2_mul`, `indepFun_coord`,
   `indepFun_indicator_coord`: fenceable at the all-genuine fixture
   `q23 = ![2/3, 1/3]` with `e = e' = 0`. For the double marginal the
   kill is **Cauchy–Schwarz strictness** at the coordinate-`0`
   indicator (`2/3 ≠ 4/9`); for the two independence statements a
   coordinate (resp. coordinate indicator) is not independent of
   itself, killed at the singleton cylinder — the indicator twin at
   the measurable set `{1}` through the preimage identification with
   the `{ω | ω 0 = 0}` cylinder.
4. **`he : Function.Injective e`** on `iIndepFun_coord_apply`:
   fenceable at the constant reindexing (both reindexed coordinates
   the same projection — perfectly correlated), killed at
   `T = univ`, `sets = {0}, {0}`: `2/3 ≠ 4/9`. Its sibling clause
   **`hF : ∀ k, Measurable (F k)` is classified truth-removable at
   the shelf's own generality** — `V` is a `Fintype` with
   `MeasurableSingletonClass`, so every subset of `V` is measurable
   and `measurable_of_finite` discharges `hF` for any `F`; the
   audit delivers the proved hF-free twin as the strengthening
   companion (the decorative-clause class, like `eigvalOf_one`'s
   `hOne` in the spectral-core audit).

**The reconciliation:** `junk_normalization_fence_QA` (2026-08-era
free-form witness computing `∑ iidMass ![2,0] = 4`) becomes the
proof engine of `sum_iidMass_eq_one`'s `hq1` fence — the file's
free-form negative-witness layer is then fully inside the per-clause
discipline, completing the pattern the Bernoulli-product audit set.

## Delivery record

Delivered at the full priced scope — **twelve hypothesis-form fences**
plus fixtures, kept-clause pins, and the strengthening twin in
`IIDProduct_QA.lean`'s new `AdversarialFences` section (a pure
~470-line insertion), QA-only, zero axiom contact (count stays 4;
`#print axioms` via `wip/iidfences_axcheck.lean` on all 21 new
nameable declarations — the 19 public theorems and 2 fixture `def`s —
every one exactly `propext, Classical.choice, Quot.sound`; the
private `ofReal`-disequality kill engine is audited transitively
through every fence that consumes it; no `-- @refutes` tags — theorem
instantiations of an all-proved shelf; the 24-tag independence check
unchanged and clean). QA 6167 → 6186 (+19 by the generator metric;
22 declarations = 19 public theorems + 2 fixture `def`s + 1 private
engine).

The fences, each a first witness for its clause:

1. **`sum_mass_eq_one`'s `hq0`** at `iidNeg = ![-1, 2]` (kept `hq1`
   genuine by the pin `iidNeg_sum`): the `ofReal` clamp zeroes the
   negative coordinate's mass, `0 + 2 = 2 ≠ 1`.
2. **`sum_mass_eq_one`'s `hq1`** at `iidTwo = ![2, 0]` (kept `hq0`
   genuine by `iidTwo_nonneg`): `2 + 0 = 2 ≠ 1`.
3. **`sum_iidMass_eq_one`'s `hq0`** at `iidNeg`: the clamped joint
   masses sum to `4 ≠ 1` — the `(1,1)` atom carries `2 · 2 = 4`,
   every atom touching the negative coordinate zeroed (the pinned
   enumeration `iidNeg_mass_sum`).
4. **`sum_iidMass_eq_one`'s `hq1`** — the **reconciliation**: the
   hypothesis-form wrapper consuming the file's delivered free-form
   `junk_normalization_fence_QA` as its proof engine (`∑ iidMass
   ![2,0] = 4` against `= 1`), closing the file's pre-discipline
   witness layer.
5. **`sum_coord_mul`'s `hq0`** at `iidNeg`, `e = 0`, `F` the constant
   `1`: left `4` against right `2` — the clamped negative coordinate
   zeroes three atoms on the left but only one summand on the right.
6. **`sum_coord_mul`'s `hq1`** at `iidTwo`, same shape: `4 ≠ 2`
   (through the defeq bridge `iidTwo_mass_sum :=
   junk_normalization_fence_QA`).
7. **`sum_coord2_mul`'s `hq0`** at `iidNeg` on **three** sample
   coordinates, `e = 0`, `e' = 1`, `F = G` the constant `1`: the full
   product total `2³ = 8` against `2 · 2 = 4`, through the ∑-∏ swap
   at `Fintype.piFinset`.
8. **`sum_coord2_mul`'s `hq1`** at `iidTwo`, the same three-coordinate
   breaker: `8 ≠ 4`.
9. **`sum_coord2_mul`'s `hee`** at the all-genuine `q23` with
   `e = e' = 0`, `F = G` the coordinate-`0` indicator: the marginal
   `2/3` against its square `4/9` — Cauchy–Schwarz strictness, so a
   single coordinate cannot play the role of two (the file's own
   `mass_00_QA`/`mass_01_QA` pins feed the left side directly).
10. **`indepFun_coord`'s `hee`** at `q23`, `e = e' = 0`: at
    `s = t = {0}`, `μ(A ∩ A) = 2/3 ≠ 4/9` through the file's
    `cylinder_QA` pin — a coordinate is not independent of itself.
11. **`indepFun_indicator_coord`'s `hee`** at `q23`, `e = e' = 0`,
    `i = j = 0`: the same kill at the indicator codomain, at the
    measurable support `{1}` through the preimage identification
    with the `{ω | ω 0 = 0}` cylinder.
12. **`iIndepFun_coord_apply`'s `he`** at the constant reindexing
    `e = fun _ => 0` with `F k = id` (kept `hF` genuine: the identity
    is measurable): both reindexed coordinates are `ω ↦ ω 0` —
    perfectly correlated — killed at `T = univ`, `sets = {0}, {0}`:
    `2/3 ≠ 4/9`.

Plus the **strengthening companion**
`iIndepFun_coord_apply_strict`: the hF-free twin of
`iIndepFun_coord_apply`, proved by discharging the dropped clause
with `measurable_of_finite` — the classification's evidence that
`hF` is decorative at the shelf's own generality (`V` a `Fintype`
with `MeasurableSingletonClass` ⟹ every subset of `V` measurable).

**Pricing findings (reusable technique):**

- **The outside-the-consumed-coordinates rule is a sample-coordinate
  rule here, not a factor rule.** The Bernoulli-product audit's rule
  ("a marginal-identity bounds fence needs a breaker coordinate
  OUTSIDE the statement's consumed coordinates") transfers verbatim
  once transposed: `sum_coord_mul` breaks on `ι = Fin 2` (one free
  coordinate beyond `e`) and `sum_coord2_mul` on `ι = Fin 3` (one
  beyond `{e, e'}`) — on smaller spaces Fubini makes the dropped
  statement true, and the fixtures' arithmetic confirms it
  (`(0+2)² = 2·2` at `iidNeg` on `Fin 2`).
- **The clamp kills asymmetrically through position.** An
  `rw [ENNReal.ofReal_eq_zero.2 (by norm_num)]` elaborates its bound
  against a metavariable and unifies with the FIRST `ofReal`
  occurrence in the goal — at an atom like `ofReal 2 * ofReal (-1)`
  it rewrote the wrong factor. The cure (recorded in the landed
  `hclamp` pin): state the clamp once as a fully explicit `have`
  before use.
- **Reconciliation wrappers consume equation-shaped witnesses by
  `rw`, not application.** `junk_normalization_fence_QA` computes a
  junk value (an equation), unlike the Bernoulli-product audit's
  refutation-shaped `bp_out_of_bounds_fence_QA` (a function to
  `False`); the wrapper's shape must match the witness's own.

**Verification:** spike first (`wip/iidfences_spike.lean` — the full
22-declaration delivery, green after three fix rounds, every error in
the recorded trap classes above); `lake env lean` on the landed
module (zero errors, zero warnings — clean on the first
post-landing elaboration); explicit `lake build
Scaffold.QA.Probability.IIDProduct_QA` ✔ (2044/2044); **full `lake
build` + `check_build_completeness.py` — 134 source files, 134 fresh
artifacts, 0 stale, 0 missing, exit 0**; the 21-declaration axiom
audit above; `lint_axioms` exit 0 (4 axioms unchanged);
`check_refutation_independence` (24-tag clean);
`check_public_reachability` clean (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new `iid*`
names collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (**6186/4/0**) with the verification row; map-freshness
exit 0 after the 6167 → 6186 stats sync in both map data tables and
SVG regeneration (49 stations, no status change — none owed: this
proposal is not a map station's cited source). Records updated: this
proposal, `proposals/README.md` (new Delivered row), README (6186),
the radar (QA row synced, held 4.5), the backlog item-2
falsification-surface ledger, the scoreboard verification row, both
map data tables + regenerated SVG, the QA file's header note, the
execution plan, and the activity log. Nothing committed; prior runs'
uncommitted deliveries preserved.

**Remaining risk:** none owed — QA-only, no axiom disposition
changed, no public statement changed. QA proves consequences relative
to the substrate; it does not prove the substrate (no axiom touched).
Honest scope: the shelf's priceable clause surface is CLOSED — the
nine `iidPMF`-consumers' `hq0`/`hq1` clauses are classified
signature-entangled with their mechanism (the sampling measure's
nonexistence out of bounds, exactly what the module's own docstring
promises the mass-level fences witness), the `hF` decorative
classification is backed by the proved strengthening twin, and the
three hypothesis-free theorems carry nothing to drop.
