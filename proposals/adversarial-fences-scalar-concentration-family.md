# The Scalar-Concentration Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run
`20260905T194443Z-run-1`, session `ses_f8d05c8e1ffetzzSvB5NA7IdOu`;
see the delivery record). **Deferrals D1 + D2 RESOLVED 2026-09-05**
(run `20260905T213117Z-run-1`, session
`ses_f8c962534ffeFk8IsV5RX3OWXM`; see the deferral-closure record) —
the family's falsification surface is now closed with no open item.
## Scope

The prior terminal handoff's named next surface — "by this run's
survey numbers the next unaudited surface is the scalar concentration
family (5 transitive non-QA consumers, all theorems since 2026-08-30,
never per-clause audited)" — confirmed by this run's own fresh
reverse-import walk: the `Probability.Concentration.Scalar` subtree
(Hoeffding 870 lines, Bernstein 800, Subgaussian 368) at **5
transitive non-QA consumers** (the umbrella plus `EdgePerturbation`
and the Derived `EdgePerturbationTail`, `EdgePerturbationDrift`,
`EmpiricalStationary` capstones — the scalar tail engine behind the
degree-concentration chain). Everything on the shelf is proved (all
four axioms of the family retired 2026-08-28/30), so this is a
theorem-instantiation audit (no `-- @refutes` tags).

**SGT leverage:** this family is the scalar engine the derived
degree-tail capstones consume. Its retirement QA (`Scalar_QA.lean`,
1474 lines) carries real fence sections — the wrong-constant fence,
the mass-guard fence, the tail-level denominator fence, the uncentered
Bernstein MGF-separation refutation — but **every fence from the
retirement era is a constant/shape/guard fence: the `h_indep` clauses
have no negative witness anywhere in the repository.** Independence
was only ever instantiated genuinely (the scRad family), never refuted
in dropped form. A wrong independence transfer — a product-integral
identity that survived correlation — would poison every conditional
tail bound downstream while all QA stayed green. Method:
`governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(twenty-five precedents, most recently Bernoulli-product).

## Step-0 findings: the priced fence list

Clause census over the family's public surface — the priceable
unfenced surface is two clause classes:

1. **`h_indep : iIndepFun … X μ` on the nine tail/MGF theorems**
   (`integral_prod_exp_of_iIndepFun`, `mgf_sum_le_of_iIndepFun`,
   `hoeffding_inequality_interval`, `hoeffding_inequality`,
   `hoeffding_iid`, `hoeffding_empirical`, `bernstein_inequality`,
   `bernstein_bounded_variance`, `bernstein_iid`): fenceable at the
   new fixture **`scCorrX i ω := if ω 0 then 1 else -1`** — the
   perfectly-correlated two-coin family (both coordinates factor
   through coordinate `0`). Every kept clause is genuine there:
   measurable (the ±1 lift composed with the coordinate projection),
   `|X| = 1`, mean `0` (`integral_delta` at the fair coin), variance
   `1` — the family is distributionally identical to scRad; only the
   joint law differs. The kills: the tail events at `t = 2` are
   degenerate (`∑ X i = 2·(±1)`, so `|∑ X i| ≥ 2` is all of `Ω` and
   the measure is `1`), against bounds `2e⁻¹ < 1` (Hoeffding family,
   from `Real.exp_one_gt_d9`'s `e > 2`) and `2e^{-3/4} < 1` (Bernstein
   family, from `e³ > (27/10)³ > 16`); the empirical form at
   `t = 1/2` with the `[0,1]`-lift `(1 + X)/2` (deviation `±1/2`
   everywhere, bound `2e⁻¹`); the product-integral identity by the
   **algebraic** `cosh 2 ≠ cosh²1` (the difference is
   `(e − e⁻¹)²/4 > 0` — pure algebra from `e·e⁻¹ = 1`, no pins); and
   the Hoeffding MGF bound by `cosh 2 > e` (from the pins
   `27/10 < e < 14/5`, the upper from `exp_half_lt_five_thirds_QA`).
2. **`ht : 0 ≤ t` on the Hoeffding and Bernstein head theorems**: at
   the delivered genuine scRad fixture with `t = -2` the tail event
   `{|∑ X i| ≥ -2}` is all of `Ω` (absolute values are nonnegative),
   so the measure is `1` against bounds `2e⁻¹ < 1` and `2e^{-3/2} < 1`
   (the latter: `e³ > 8`).

**Deferred with priced mechanisms:** `mgf_sum_le_bernstein`'s
`h_indep` (the kill is at `λ = 1/2`: `cosh 1 > e^{3/10}` through the
rational chain `e³ < (11/4)³ < (11/8)¹⁰` and `e + e⁻¹ > 2.7 + 5/14 >
11/4` — feasible but the priciest single fence in the family);
the `h_mean : ∀ i, ∫ X i = 0` centering cluster of the Hoeffding
family at a two-coin biased fixture (tail kill at `t = 2` with
`|∑ X| = 2` a.s.; MGF kill at `λ = -1` with
`(9/10)e² > e^{1/2}` — the fixture needs the independent biased
product, `iIndepFun_coord_apply` at `p = ![1/10, 9/10]`).

**Classified, not fenced:** the subgaussian centered theorem
`subgaussianNorm_le_of_bounded`'s centering is built into the
hypothesis set through the MGF constraint, and dropping the analogous
centering is **truth-removable-through-junk**: a positive-drift
variable makes the constraint set empty, so the `sInf` junk-collapses
to `0` (the retired axiom's original defect mechanism) and the
dropped statement *holds* — the fence cannot exist; the companion's
mass-guard fence (delivered) is the boundary of exactly this. The
`h_meas` measurability clauses of the MGF engines
(`measurable_finset_prod'`/`sum'`, the `hX : Measurable` of the
integrability safety lemma) are fenceable only at a non-measurable
fixture (the `⊥`-σ-algebra space the matrix audit built); priced as a
follow-up. The already-fenced retirement clauses (wrong constant, mass
guard, denominator, uncentered Bernstein MGF) are cited as adjacent
coverage, not re-fenced.

## Fixtures (one new, one delivered, all on the fair two-coin space)

- `scCorrX` — the perfectly-correlated family: both coordinates are
  the ±1 lift of coordinate `0`. The `h_indep` breaker.
- `scCorr01` (`(1 + X)/2`) — the `[0,1]`-valued lift for the empirical
  form's `h_indep` breaker.
- `scRadX` (delivered, reused) — the genuine family for the `ht`
  fences.

## Delivery record

DELIVERED at the full priced scope — QA-only, an insertion before the
closing `end` of `Scalar_QA.lean` (the new `AdversarialFences` section,
reusing the file's own private lift-measurability lemmas, the delivered
`scRadX` fixture, and the `local instance` probability structure): all
eleven hypothesis-form fences, the `scCorrX`/`scCorr01` fixture `def`s
with their genuine-clause companions (`scCorrX_measurable_QA`,
`scCorrX_abs_QA`, `scCorrX_mean_QA`, `scCorr01_measurable_QA`,
`scCorr01_mean_QA`), the `¬iIndepFun` isolation companion
(`scCorr_not_iIndepFun_QA` — the dropped clause genuinely fails, the
fixture is not degenerate), the MGF pin `scCorr_integral_exp` (the
exponential moment is `cosh z` by the four-atom enumeration), the
shared event pins (`scCorr_event_eq_univ`,
`scCorr_centered_event_eq_univ`), the variance pin `scCorr_var_sum`,
and the six exp-bound helper pins. 30 new declarations (28 public
theorems by the generator metric + 2 fixture `def`s + private helpers);
QA 6139 → 6167 (+28). Zero axiom contact (`#print axioms` via
`wip/scfences_axcheck.lean` on all 28 public declarations — every one
exactly `propext, Classical.choice, Quot.sound`; no `-- @refutes` tags
— theorem instantiations of an all-proved shelf; the 24-tag
independence check unchanged and clean).

The fences:

1. **`scFence_prod_exp_indep`** — `integral_prod_exp_of_iIndepFun`'s
   `h_indep` at `lam = 1`, `s = univ`: `cosh 2 ≠ cosh²1`, an algebraic
   kill (the difference is `(e − e⁻¹)²/4 > 0` from `e·e⁻¹ = 1`; the
   final contradiction `exp 1 = exp (-1)` discharges through
   `Real.exp_strictMono.injective`).
2. **`scFence_mgf_sum_indep`** — the Hoeffding MGF bound's `h_indep`:
   `cosh 2 > e` from the pins `27/10 < e < 14/5` (the upper from the
   file's `exp_half_lt_five_thirds_QA`, the lower from Mathlib's
   `Real.exp_one_gt_d9`), by `nlinarith`.
3-6. **`scFence_hoeffding_interval_indep`, `scFence_hoeffding_indep`,
   `scFence_hoeffding_iid_indep`, `scFence_hoeffding_empirical_indep`**
   — the four Hoeffding tail forms at `t = 2` (the empirical at the
   `[0,1]`-lift `scCorr01`, `t = 1/2`): every tail event degenerates to
   `univ` (the correlated sum is `±2` everywhere), so the measure is
   `1` against `2e⁻¹ < 1`.
7-9. **`scFence_bernstein_indep`,
   `scFence_bernstein_bounded_variance_indep`,
   `scFence_bernstein_iid_indep`** — the three Bernstein tail forms at
   `t = 2`, `a = 1`: the centered events degenerate the same way
   (mean `0`), against `2e^{-3/4} < 1` (from `e³ > (27/10)³ > 16`).
10-11. **`scFence_hoeffding_ht`, `scFence_bernstein_ht`** — the
   backward-time clauses at the genuine `scRadX` fixture, `t = -2`:
   `{|Σ| ≥ -2}` is all of `Ω` (absolute values are nonnegative),
   against `2e⁻¹ < 1` and `2e^{-3/2} < 1`.

Technique findings recorded for future audits:

1. **`rw` cannot rewrite under a binder whose variable appears in the
   pattern, but `integral_congr_ae (ae_of_all _)` bridges integrals
   for free.** Rewriting `1 * ∑ i, X i ?ω → 2 * X 0 ?ω` inside an
   integral hypothesis fails outright (capture avoidance); stating the
   function-level congruence and rewriting the whole integral through
   `integral_congr_ae` is the robust route.
2. **Match the elaborated negation placement in `show`-rewrites.**
   The instantiated `-t ^ 2 / …` bounds elaborate with the negation in
   specific, hard-to-guess positions (`-((-2)^2 / …)` vs
   `-(-2)^2 / …`); when a `show`-rewrite fails on an arithmetic-shaped
   pattern, copy the exact displayed form (the retirement QA's own
   `show -(2 : ℝ) ^ 2 / (2 * 2) = -(1 : ℝ)` is the calibrated
   precedent — this audit rediscovered it independently).
3. **`Set.eq_univ_of_forall` + `le_trans (show (-2:ℝ) ≤ 0 by norm_num)
   (abs_nonneg _)`** is the one-line route to "`{|Σ| ≥ negative t}` is
   all of `Ω`" — the `by norm_num` side goal needs its expected type
   pinned by `show`, or it elaborates against a metavariable.
4. **Statement binders of constant summands trip the unused-variable
   linter** (`∑ i : Fin 2, (1:ℝ)^2` — `i` legitimately unused); the
   per-theorem `set_option linter.unusedVariables false in` before the
   docstring is the honest suppression.

## Verification

Spike first (`wip/scfences_spike.lean` — the full delivery, iterated to
zero errors/zero warnings over ~12 fix rounds, all in the recorded
trap classes above); `lake env lean` on the landed module (zero errors;
all 10 warnings verified pre-existing at HEAD by elaborating `git show
HEAD`'s copy — same count, same classes); explicit `lake build
Scaffold.QA.Concentration.Scalar_QA` ✔; the 28-public-declaration axiom
audit above; **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 134 source files, 134 fresh artifacts,
0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4 current axioms,
unchanged); `check_refutation_independence` (24-tag clean — no tags
touched); `check_public_reachability` clean (63 repo modules);
`check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_qa_name_uniqueness` clean (the
new `scCorr*`/`scF*` names collision-free); `check_backlog_freshness`
clean; scoreboard regenerated (**6167/4/0**) with the verification row;
map-freshness exit 0 after the 6139 → 6167 stats sync in both map data
tables and SVG regeneration (49 stations, no status change — none
owed: the audit's proposal is not a map station's cited source).
Records updated: this proposal (COMPLETE + delivery record), the
scoreboard verification row, README (6167), the radar (QA row synced,
held 4.5), the backlog item-2 falsification-surface ledger, both map
data tables + regenerated SVG, `index/map/probability_concentration.md`
(coverage notes in the Hoeffding and Bernstein sections), the
execution plan, and the activity log. Nothing committed; prior runs'
uncommitted deliveries preserved.

## Deferral-closure record (D1 + D2, 2026-09-05)

Both priced deferrals closed in one delivery (run
`20260905T213117Z-run-1`, session
`ses_f8c962534ffeFk8IsV5RX3OWXM`) — `Scalar_QA.lean`'s new
`DeferralFences` section, QA-only, zero axiom contact (`#print
axioms` via `wip/scdefl_axcheck.lean` on all 21 new nameable
declarations — every one exactly `propext, Classical.choice,
Quot.sound`; no `-- @refutes` tags — theorem instantiations of an
all-proved shelf; the 24-tag independence check unchanged and
clean). QA 6167 → 6205 across the two scalar deliveries (+19 here;
19 public theorems + 2 fixture `def`s + 9 private enumeration
helpers).

**D1 — `mgf_sum_le_bernstein`'s `h_indep`** (`scFence_bernstein_mgf_indep`),
at the delivered perfectly-correlated fixture `scCorrX` with `a = 1`,
`λ = 1/2`: the MGF is `cosh 1 = (e + e⁻¹)/2` (the delivered
`scCorr_integral_exp` pin at `z = 1`, through the `λ·∑ = 1·X₀`
collapse) while the bound is `exp(3/10)` (the variance statistic
pinned `2` by the new `scCorr_sq_sum`, the exponent
`(1/4)·2/(2·(5/6)) = 3/10`). The kill was re-priced against the
original sketch's rational chain: instead of `cosh 1 > e^{3/10}`
directly, both sides are bracketed at `3/2` — `cosh 1 > 3/2` (from
`e > 27/10` and `e⁻¹ > 3/10`, the latter via `e < 14/5`:
`e·(3/10) < (14/5)(3/10) = 21/25 < 1 = e·e⁻¹`) and `exp(3/10) < 3/2`
(the cubing route `exp(3/10)³ = exp(9/10) < e < 14/5 < 27/8 =
(3/2)³`, mirroring the delivered three-quarters pin's `by_contra` +
`pow_le_pow_left₀` structure). The priciest single fence in the
family, and the last never-refuted clause of the Bernstein MGF
engine.

**D2 — the `h_mean` centering cluster of the four Hoeffding-family
theorems** (`scFence_mgf_sum_mean`, `scFence_hoeffding_interval_mean`,
`scFence_hoeffding_mean`, `scFence_hoeffding_iid_mean`), at the NEW
genuinely-independent biased product: `scBias = ![9/10, 9/10]` with
the ±1 coordinate lift `scBiasX` (each coordinate through its OWN
projection — independence GENUINE via `iIndepFun_coord`'s `.comp`,
measurability and the ±1 bounds genuine, the centering broken at
`∫ scBiasX i = 4/5`, pinned by `scBiasX_mean_QA`). This is the
family's first *independent* non-centered witness — every prior
fence broke independence, every genuine-independence instance was
centered, so no `h_mean`-only fence could exist before it. The
kills: the `t = 2` tail event is `{ω | ω 0 = ω 1}` (both coordinates
equal, the sum `±2`) at measure `81/100 + 1/100 = 41/50` (the
four-atom enumeration `scBias_event_mass`) against the bound
`2e⁻¹ < 41/50` (from `e⁻¹ < 10/27` via `e > 27/10`: the new pin
`scF_exp_inv_lt_ten_27s`, nlinarith over `e·e⁻¹ = 1`); the MGF at
`λ = 1` is `(81/100)e² + 18/100 + (1/100)e⁻²` (the pin
`scBias_integral_exp_one`) against the bound `e` — the `tt` atom
alone exceeds it, `(81/100)e² > e ⟺ (81/100)e > 1` at `e > 27/10`.

**Technique findings (reusable):**

- **Simp's numeral normalizer is asymmetric across `ofReal`.** Full
  `simp` normalizes `ofReal (1/10)` to `ofReal 10⁻¹` on the stated
  side while leaving the unfolded `bern` side's `ofReal (1 − 9/10)`
  unreduced — the intermediate `have` must be stated in the
  *unfolded* arithmetic shape, then reduced on both sides by an
  explicit `show ... from by norm_num` rewrite. The single-argument
  `ENNReal.ofReal_mul (hp : 0 ≤ p)` (q free — the pinned Mathlib's
  signature) resolves its second factor from the rewrite pattern,
  avoiding the metavar trap the i.i.d.-product audit recorded.
- **`ENNReal.toReal_le_toReal` is oriented `toReal-side ↔ ≤-side`**
  in the pinned Mathlib: extracting a real inequality from an
  `ofReal ≤ ofReal` fence hypothesis goes through `.mpr`, then the
  two `toReal_ofReal` rewrites (the private bridge
  `scF_ofReal_le_ofReal'`).
- **`nlinarith` kills need un-atomized monomials.** Rewriting
  `e·e` to `exp 2` before the kill atomizes the product the
  arithmetic route needs ((81/100)e² ≤ e against `sq_nonneg (e −
  27/10)`); the fences keep products unreduced and hand `nlinarith`
  the raw monomials.
- **A section's `open` expires at its `end`.** The landed section
  initially failed the explicit module build on
  `measurable_coord`/`iIndepFun_coord`/`bern` unknowns — invisible
  to a truncated `lake env lean | head` check (the pipe's exit code
  is `head`'s, not Lean's; the errors printed after the warnings).
  The explicit `lake build` target and an `rg error` grep on full
  output are the reliable pair; recorded as a verification
  discipline note.

**Verification:** spike first (`wip/scdefl_spike.lean` — the full
delivery, green after five fix rounds, every error in the recorded
trap classes); `lake env lean` on the landed module (zero errors
against an `rg error` grep of the full output; the file's 10
warnings all at lines ≤ 1448 — the prior run's HEAD-verified
baseline, the new section contributing zero); explicit `lake build
Scaffold.QA.Concentration.Scalar_QA` ✔ (2128/2128); **full `lake
build` + `check_build_completeness.py` — 134 source files, 134 fresh
artifacts, 0 stale, 0 missing, exit 0**; the 21-declaration axiom
audit above; `lint_axioms` exit 0 (4 axioms unchanged);
`check_refutation_independence` (24-tag clean);
`check_public_reachability` clean (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new
`scBias*`/`scFence_*_mean`/`scFence_bernstein_mgf_indep` names
collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (**6205/4/0**) with the verification row; map-freshness
exit 0 after the 6186 → 6205 stats sync in both map data tables and
SVG regeneration (49 stations, no status change — none owed). The
family's one remaining classified non-fenceable (the subgaussian
centering, truth-removable-through-junk: positive drift empties the
constraint set, `sInf ∅ = 0`) carries its mechanism above and is a
property of the *retired* axiom's defect, not an open obligation of
the proved shelf.

## Follow-up record: the measurability/integrability-guard clauses (2026-09-05)

The delivery's own follow-up pricing — "the `h_meas` measurability
clauses of the MGF engines (`measurable_finset_prod'`/`sum'`, the
`hX : Measurable` of the integrability safety lemma) are fenceable
only at a non-measurable fixture (the `⊥`-σ-algebra space the matrix
audit built)" — delivered the same day as the prior terminal handoff's
named last recorded follow-up. QA-only: 11 hypothesis-form fences plus
the shared fixture, mass, non-measurability, and pin companions in
`Scalar_QA.lean`'s new `MeasurabilityFences` section (+36 by the
generator metric, 6205 → 6241; 40 declarations = 36 theorems + 4
`def`s + the probability instance), zero axiom contact (`#print
axioms` via `wip/scmfences_axcheck.lean` on all 40 — every one
exactly `propext, Classical.choice, Quot.sound`; no `-- @refutes`
tags — theorem-instantiation fences of an all-proved shelf; the
24-tag independence check unchanged and clean).

**The fixture (a design finding in itself):** the two-point
trivial-σ-algebra space with BIASED masses `9/10 : 1/10`
(`scM2μ`, the `mcTwoBot` pattern at the bias the tail kills need —
the audit's fair-coin version cannot kill: a `9/10`-mass tail against
`2e⁻²` needs the heavy atom to dominate). Every real function on
`⊥` is measurable iff constant (`stronglyMeasurable_bot_iff`), so the
two-valued breakers `scM2X` (values `2`/`0`) and `scM2Emp`
(values `1`/`0`) are non-measurable, not ae-strongly-measurable
(`scM2_not_aeSM`, the `mcTwoBot_not_aeSM` clone at the biased
measure), and every integral of them is the junk zero
(`integral_undef`) — the exact mechanism class of Errata §7. **The
kills use only mass LOWER bounds** (`scM2μ_ge_zero`: point-membership
gives `ofReal (9/10) ≤ μ S` through `dirac_apply_of_mem`), which
sidesteps the trim-saturation trap below.

The eleven fences:

1. **`measurable_finset_prod'`'s `hf`** — at the one-element index
   the product IS the breaker: `Measurable` refuted by
   `scM2X_not_measurable` (the `Measurable.aestronglyMeasurable`
   route into the not-aeSM engine).
2. **`measurable_finset_sum'`'s `hf`** — same at the sum.
3. **`integrable_of_bounded_measurable`'s `h_meas`** — `h_bound`
   genuine (`|scM2X| ≤ 2`), `Integrable` refuted (ae-SM is a
   conjunct of integrability).
4. **`integrable_sq_sub_mean`'s `h_meas`** — the centered square at
   the junk zero mean is the two-valued `scM2X²`, not integrable.
5. **`hoeffding_inequality_interval`'s `h_meas`** — `c = 0`, `d = 2`,
   `t = 2`: the tail event contains the heavy atom (mass `9/10`)
   against `2e⁻² < 9/10` (the new pin, from `e > 27/10`).
6. **`hoeffding_empirical`'s `h_meas`** — the `[0,1]` breaker at
   `t = 1`: `9/10 > 2e⁻²`.
7. **`bernstein_inequality`'s `h_meas`** — `a = 2`, `t = 2`: the
   variance statistic `∑∫(X − ∫X)²` is ITSELF the junk zero (the
   matrix audit's headline mechanism at the scalar sibling), the
   denominator collapses to `2at/3`, the bound to `2e^{-3/2} < 9/10`
   (new pin from `e³ > 16`).
8-9. **`bernstein_bounded_variance`'s and `bernstein_iid`'s
   `h_meas`** — same kill at `v = 0` / `σ² = 0` (the `h_var` clauses
   hold through the junk zero).
10. **`markov_tail_of_mgf`'s `hint`** — the Markov engine's
    integrability guard, the exact clause class that was vacuous in
    the Errata §7 repair: at `B = 0`, `t = 0` the MGF hypothesis
    holds through the junk zero while `{0 ≤ Y}` is all of `Ω`
    (measure `1`) against the bound `ofReal 0`.
11. **`subgaussian_tail_bound`'s `h_int`** — the moment integrability
    guard: `K = 1`, `t = 2`, `9/10 > 2e⁻²`.

Kept-clause honesty: `h_indep` is genuine by single-coordinate
triviality (`scM2Fam_iIndepFun_QA` — `iIndepFun` over `Fin 1` proved
by the `Finset.eq_empty_or_nonempty` case split, both sides of the
independence equality identical); `h_bound`/`h_mean`/`h_var` hold
with `h_mean`-shaped integrals junk (recorded on the companions as
"held through the junk", the matrix audit's precedent).

**Classified truth-removable-through-junk (not fenceable):** the
MGF-conclusion `h_meas` clauses — `hoeffding_lemma_mgf`'s,
`bennett_mgf`'s, `integral_prod_exp_of_iIndepFun`'s (identity:
junk LHS `0 = ∏ 0`), `mgf_sum_le_of_iIndepFun`'s and
`mgf_sum_le_bernstein`'s (junk-zero LHS `≤` every positive bound) —
the dropped statements HOLD at every non-measurable fixture; a fence
cannot exist.

**Deferred with the priced mechanism:** `hoeffding_inequality`'s and
`hoeffding_iid`'s `h_meas`. These need TWO genuinely-independent
non-constant coordinates (at `n = 1` the ±a bound `2exp(−t²/2a²) ≥
2e^{−1/2} > 1 ≥ μ` at every fixture; a constant second coordinate
dilutes the denominator `2∑a²` below the kill threshold at `n = 2`).
The obstruction: on a trivial σ-algebra, a measure built as a Dirac
combination SATURATES — `OuterMeasure.trim` (the definitional total
function of `Measure.ofMeasurable`-built measures, per
`toMeasure_toOuterMeasure`'s `rfl`) takes every nonempty set to the
inf over its measurable supersets, which on `⊥` is `univ` alone, so
exact non-measurable-set masses are all `1` while the honest point
computation wants `9/10`-style values; point-membership lower bounds
(the only cheaply provable mass facts) prove independence just for
constant coordinates. Two priced routes: (a) the deep unfold
`δ_a s = 1` for nonempty `s` via the `inducedOuterMeasure`/`extend`
guts, making all-saturated independence provable (all-`1` masses
satisfy the equality when all pairwise level-set intersections are
nonempty — a `Fin 4` four-cell partition design); (b) a richer
non-`⊥` σ-algebra whose measurable sets separate the breaker's level
sets from the other atoms — shown impossible at four points (any
σ-algebra separating all four points makes the breaker measurable).
Both routes are multi-step measure-theory archaeology for two sibling
theorems whose shared engine (`hoeffding_inequality_interval`) is
fenced at clause 5; priced as a follow-up, not an obligation.

Technique findings recorded for future audits:

1. **`simp only`-before-unfold ordering at junk-integral membership
   goals.** The integral lemma (`scM2Fam_integral`) must fire BEFORE
   the family def unfolds (`simp [scM2Fam, ...]` beta-reduces
   `scM2Fam i` to `scM2X`, killing the family-lemma match); the
   robust shape is `simp only [Fin.sum_univ_one, <integral lemma>]`
   then the value simp.
2. **`rw` cannot rewrite under a binder where the pattern binds** —
   restated for the square-integral case: `(fun ω => (X ω − 0)²)`
   needs `simp only [sub_zero]`, not `rw [sub_zero]`.
3. **The `ofReal`-vs-literal kill chain:** state mass lemmas in
   `ofReal` form (`ofReal (9/10) ≤ μ S`), keep one bridge lemma
   (`scM2μ_ofReal_coe`), and discharge the final contradiction via
   `ENNReal.ofReal_lt_ofReal_iff_of_nonneg` — whose nonnegativity
   side goal needs `mul_pos (show (0:ℝ) < 2 by norm_num)
   (Real.exp_pos _)`, since `positivity` does not see through
   `Real.exp` of an arbitrary sign.
4. **`Finset.eq_empty_or_nonempty` + `Finset.ext` at `Subsingleton`
   index types** is the clean `Fin 1` independence route (the
   `univ_unique` rewrite fails: `iIndepFun`'s definition quantifies
   over ALL Finsets, not just `univ`).

## Deferral-closure record: the trim-saturation route (2026-09-05)

The follow-up's two deferred siblings — `hoeffding_inequality`'s and
`hoeffding_iid`'s `h_meas` — closed the same day by taking the priced
route (a): the saturation itself becomes the lemma, and the
"genuinely-independent non-measurable family" the deferral recorded as
blocked becomes constructible. QA-only: the new `SaturationFences`
section of `Scalar_QA.lean` (+29 by the generator metric,
6241 → 6270; 33 declarations = 29 theorems + 6 `def`s + the
probability instance), zero axiom contact (`#print axioms` via
`wip/scsat_axcheck.lean` on all 29 nameable declarations — every one a
subset of `propext, Classical.choice, Quot.sound`; no `-- @refutes`
tags; the 24-tag independence check unchanged and clean).

**The saturation lemma (`scM_dirac_bot_eq_one`):** on the trivial
σ-algebra, `@Measure.dirac α ⊥ a s = 1` for every nonempty `s`. The
proof route is the packaged `measure_eq_iInf` — a measure's value at
any set is the infimum over its measurable supersets — and on `⊥` the
only measurable superset of a nonempty set is `univ` (the empty-cover
case contradicts nonemptiness; the univ element attains the infimum).
The follow-up's obstruction ("`OuterMeasure.trim` saturates every
nonempty set to full measure, blocking exact-mass computation") is
therefore not a bug of the fixture space but its load-bearing
structure: saturation makes every mass EXACTLY `1`, which is precisely
what a saturated-independence argument needs.

**The saturated-independence lemma (`scM_indepFun_of_saturated`):** on
any measure where every nonempty set has measure `1`, two real
functions are independent whenever every pair of nonempty Borel
preimages intersects (both sides of each independence equality reduce
to `1 · 1` or to `0` through the empty side, by
`indepFun_iff_measure_inter_preimage_eq_mul`). The hypothesis is
discharged at the four-cell design: `X₀ = 2·1_A`, `X₁ = 2·1_B` with
`A = {0,1}`, `B = {0,2}` — the four cells carry the value pairs
`(2,2)`, `(2,0)`, `(0,2)`, `(0,0)`, so whichever values land in `S` and
`T`, some cell lies in both preimages (`scM4X_indep_hint`, a four-case
witness argument). The `Fin 2` `iIndepFun` is then assembled by the
`Finset.erase` case analysis (empty/singleton/full). **This is the
repository's first genuinely-independent non-measurable family** —
every prior fence either broke independence or was measurable.

**The fences:** at `a = 2`, `t = 4` the tail event
`{|X₀ + X₁| ≥ 4} = A ∩ B = {0}` is nonempty, hence of saturated
measure exactly `1` (`scM4μ_sat`), against both theorems' bounds
`2exp(−16/16) = 2e⁻¹ < 1` (the on-file pin `scF_two_exp_neg_lt_one` —
no new pins). Kept clauses: `h_indep` genuine (above), `h_bound`
genuine, `h_mean` through the junk zero (`scM4X_integral`,
`integral_undef` at the two-valued non-ae-SM coordinates), `ht`
genuine.

With this closure the scalar family's falsification surface is
COMPLETE: every priceable clause is fenced, the two deferral classes
are closed, and the five MGF-conclusion classifications
(truth-removable-through-junk) stand as properties of junk-satisfiable
conclusion shapes, not open obligations.

Technique findings recorded for future audits:

1. **`measure_eq_iInf` is the saturation route** — no
   `inducedOuterMeasure`/`extend` archaeology is needed: the
   measurable-superset infimum IS a theorem, and on `⊥` it collapses
   to the single `univ` candidate.
2. **Decidable cell predicates are load-bearing for elaboration**: a
   breaker defined as `if ω ∈ ({0,1} : Set (Fin 4)) then 2 else 0`
   does not elaborate (no `Decidable` instance for set membership);
   spelling the same cell as `if ω ≤ 1 then 2 else 0` does, and the
   set/membership layer rides beside it.
3. **Hypothesis-carrying `Finset.prod_insert` cannot fire inside
   `simp only`** (the membership argument is not a simp fact);
   `Finset.set_biInter_insert` has no hypothesis and fires freely —
   the Fin-2 `iIndepFun` univ case needs the pair applied separately.
4. **A saturated measure makes the not-ae-SM engine easier**: every
   point carries full mass, so the two-point distinct-values argument
   needs no mass computation at all.
