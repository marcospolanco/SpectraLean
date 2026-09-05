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
