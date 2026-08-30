# Proposal: Repair-and-Retire the Scalar Bernstein Pair (`bernstein_inequality`, `bernstein_bounded_variance`)

**Status:** DELIVERED 2026-08-30 — a repair (Errata §8) plus a
retirement: both axioms were materially false in hypothesis shape (the
*uncentered* bound `|X i ω| ≤ a` where the cited sources bound the
*centered* variables), repaired in place to the source-faithful
centered hypothesis and **proved** by a local Bennett MGF engine.
Zero new axioms; the admitted-axiom count drops 8 → 6. Run
`20260830T124650Z-run-1` recorded the Step-0 finding, the plan, and
the spiked engine (both repaired statements already elaborating in
`wip/bernspike.lean`); run `20260830T150349Z-run-1` corrected the
witness constants, landed the shelf, threaded the consumers, and wrote
this record. See [Delivery record](#delivery-record).

## Why this, now

Priority item 4 (reduce the explicit trust surface), continuing the
standing handoff's named frontier after the 2026-08-30 Hoeffding
retirement ("the Bernstein pair's own retirement route — the
Bennett/Bernstein MGF machinery would be the analogy of this
delivery"). The mandatory Step-0 adversarial check (compare the exact
hypothesis set against the cited source clause by clause, per
`docs/2_ARCHITECTURE.md` §5) upgraded the retirement into a
repair-plus-retirement.

## The Step-0 finding (Errata §8)

Both axioms hypothesized the **uncentered** bound `|X i ω| ≤ a` while
centering internally in the conclusion (`∑ (X i − ∫ X i)`). The cited
sources hypothesize *mean-zero* variables with the bound on the
centered ones:

- Vershynin, *High-Dimensional Probability*, Theorem 2.8.1 (2nd ed.):
  "Let `X₁, …, X_n` be independent mean-zero, sub-exponential random
  variables" with the sub-exponential norm bound — the bound is on the
  centered variable `X i` itself.
- Wainwright, *High-Dimensional Statistics*, Theorem 2.15: "independent
  random variables `X_i`, each with mean zero and satisfying
  `|X_i| ≤ b`" — mean-zero *and* the bound on the same (centered)
  variable.

Under the uncentered reading, a variable `X` with `|X| ≤ a` has
centered values satisfying only `|X − E X| ≤ 2a` (both endpoints
attainable), so the `2at/3` linear term understates the Bennett price
by up to a factor 2. `matrix_bernstein` is safe on this axis — its
`h_mean : ∫ X i = 0` plus `h_bound` bind the *same* (already centered)
variables, which is Tropp's own shape. The proved
`hoeffding_inequality` family is safe (range-only exponent, no linear
term).

### The numerical LD evidence (honestly not a Lean refutation)

At the biased ±1 coin `P(+1) = q = 1/10` (so `a = 1`, `E X = −4/5`,
true variance `V = 9/25`), the per-variable large-deviation rate at
deviation `y = 1/2` is

```
I(1/2) = D(1/2 + (1−2q)/2 ‖ q) = D(0.35 ‖ 0.1) = 0.22693…
```

while the claimed exponent rate at the same deviation is

```
y²/(2V + 2ay/3) = 0.25/(0.72 + 1/3) = 0.23730…
```

The claim exceeds the truth by ~1% per variable, so the stated tail
bound is violated for `n ≳ 500–1000` — beyond exact Lean witness
scale. Recorded as numerical evidence (the rates above are classical
binomial KL divergences), not as a Lean proof.

### The Lean MGF-separation witness

The *mechanism* of the violation is exactly Lean-provable at fixture
scale, and it is what landed in QA
(`Scaffold/QA/Concentration/Scalar_QA.lean`, the Bernstein retirement
section):

- The pre-repair hypothesis set holds **genuinely** at the fixture:
  `|X b| ≤ 1` uncentered (`biasedX_abs_QA`), measurability
  (discreteness of `Bool`), singleton independence, and the *true*
  variance `∫ (X − EX)² = 9/25` (`biasedX_var_QA` — the witness fails
  at the honest variance statistic, not a misstated one).
- At `λ = 5/9` (chosen so the `+`-deviation `9/5` gives exponent
  exactly `1`, riding the pinned `e > 2.7182818283`), the claimed
  per-variable MGF bound the old denominator prices —
  `E e^{λY} ≤ exp (λ²V/(2(1 − λa/3)))` — has exponent exactly `3/44`,
  and

```
E e^{λY} = (9/10) e^{−1/9} + (1/10) e
         ≥ (9/10)(17/18)² + e/10        (squaring trick: e^{−1/9} ≥ (1 − 1/18)²)
         > 44/41                        (since e > 2.7182818283 > 3991/1476·10)
         > e^{3/44}                     (reciprocal trick: e^{−3/44} > 1 − 3/44)
```

  proved as `bernstein_mgf_separation_QA`, with the fence
  `old_bernstein_mgf_uncentered_refuted_QA` refuting the claimed MGF
  bound in hypothesis form (every pre-repair hypothesis clause holds,
  the conclusion fails). The planning note's draft constant
  `(18/25)(e−2)` was an arithmetic slip, corrected during the spike:
  `(9/25)(e−2)` is the *true Bennett* exponent at `M = 1`, which the
  true MGF does **not** exceed — the honest separation is against the
  *claimed* Bernstein exponent `3/44`, as above.

## The proof (the Bennett engine)

All in `Scaffold/Mathlib/Probability/Concentration/Scalar/Bernstein.lean`,
pure hard crust (`#print axioms` on every engine lemma: exactly
`propext, Classical.choice, Quot.sound`):

1. **Bennett's ratio** `bennettQ u = (e^u − 1 − u)/u²`, with the
   integral representation `bennettQ_eq_integral`:
   `q(u) = ∫₀¹ (1 − s) e^{us} ds`, by the antiderivative
   `((1 − t)/u + 1/u²) e^{ut}` and
   `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
2. **Whole-line monotonicity** `bennettQ_le` (the integrand
   `(1−s) e^{us}` is monotone in `u` pointwise on `[0,1]`; the
   representation handles both signs of `u` uniformly — no case split).
3. **The series bound** `bennettQ_le_inv`: `q(v) ≤ 1/(2(1 − v/3))` on
   `(0, 3)`, termwise from the series representation
   `hasSum_bennettQ` (`v^j/(j+2)!` against the geometric
   `v^j/(2·3^j)`, the factorial bound `(j+2)! ≥ 2·3^j` by induction).
4. **The pointwise bound** `exp_le_add_sq_mul`: for `y ≤ a`, `λ > 0`,
   `a > 0`: `e^{λy} ≤ 1 + λy + y²·q(λa)` — by monotonicity of `q`
   applied at `λy ≤ λa` (valid for negative `y` too, again through the
   integral representation).
5. **The per-variable MGF bound** `bennett_mgf`: a measurable,
   centered, centered-bounded `Y` with `|Y| ≤ a` satisfies
   `E e^{λY} ≤ exp (λ²σ²/(2(1 − λa/3)))` for `0 < λ`, `λa < 3`, where
   `σ² = ∫ Y²` — the pointwise bound integrated
   (`integral_mono_of_nonneg` against the integrable majorant; honest
   integrability throughout via `integrable_of_bounded_measurable` and
   `integrable_sq_sub_mean`), the series bound closing the ratio
   against the claimed exponent, `1 + x ≤ e^x` finishing.
6. **The sum bound** `mgf_sum_le_bernstein`: the product factorization
   through the Hoeffding retirement's proved
   `integral_prod_exp_of_iIndepFun` (no new independence machinery).
7. **The Chernoff assembly** at `λ = t/(V + at/3)`: both tails via the
   retirement's proved `markov_tail_of_mgf`, the exponent identity
   closing at exactly `−t²/(2V + 2at/3)` (the opaque-denominator
   formulation `exponent_identity` so every division is by an atom);
   the `V = 0` corner a dedicated null-event case (each centered
   variable vanishes a.e.); the `t = 0` corner `2 ≥ 1 ≥ μ` trivial; the
   `a = 0` corner forcing `V = 0`.

`bernstein_bounded_variance` then follows by denominator monotonicity
(`h_var` relaxes the exponent) — with the previously-present `0 ≤ v`
clause dropped as dead (implied by `h_var`, unused by the proof; the
repaired statement is strictly stronger, recorded as a deliberate
API simplification in the same breaking release as the repair).

### Degenerate-corner analysis (recorded pre-statement, per §5)

- **Measure mass:** `[IsProbabilityMeasure μ]` instance hypothesis
  present in the statement (the mass-scaling hazard guarded).
- **Junk integrals:** every hypothesis-side integral is discharged
  honestly inside the proof — the centered bound plus measurability
  plus probability force `Integrable (X i)` (proved, not assumed: a
  non-integrable `X i` would make `∫ X i` a junk `0`, but then the
  centered bound becomes the uncentered bound `|X| ≤ a` and
  integrability resurrects via `integrable_of_bounded_measurable` —
  the proof's `hXint` by-contradiction step), and the second moments
  via `integrable_sq_sub_mean`. No hypothesis can be a junk zero.
- **`V = 0`:** dedicated case, the event is null.
- **`t = 0`:** the bound is `2 ≥ 1 ≥ μ(univ)`.
- **`a = 0`:** forces every centered variable to vanish, reducing to
  the `V = 0` case (proved inside, no extra hypothesis).
- **Empty `Fin n`:** the sum is `0`; the statement holds through the
  `t = 0`-style bound (no `Nonempty` guard needed — the scalar
  prefactor is the constant `2`, never collapsing at a degenerate
  dimension; the 2026-08-28 matrix-side analysis transfers).

## Consumer leverage

- `bernstein_iid` re-derived at the centered shape (still proved, not
  an axiom).
- The two Derived Bernstein-twin tails
  (`edgePerturbation_degree_tail_bernstein`, `_budget`) re-proved at
  unchanged public statements — their designs are already centered
  Bernoulli summands with proved zero means
  (`integral_degPerturbSummand_eq_zero`), so the `h_bound` clauses
  re-thread mechanically (`rw [hmean i, sub_zero]`). **Both tails and
  their QA pins are now hard crust** (`#print axioms`: standard three
  only, via `wip/bernretire_axcheck.lean`).
- The window family remains conditional on `matrix_hoeffding` alone
  and the sparsification family on `matrix_bernstein` alone (audited,
  unchanged by this delivery).
- The remaining admitted surface after this delivery: the PF pair, the
  matrix trio, and `hoeffding_lemma` — the one zero-consumer axiom;
  its natural consumer was this proof's engine, which used
  `bennett_mgf` instead, so `hoeffding_lemma`'s consumer question
  stays open.

## Delivery record

- **Run `20260830T124650Z-run-1`** (opening): the Step-0 finding and
  full plan recorded in `docs/EXECUTION_PLAN.md`; the analytic core,
  both repaired statements, and the engine spiked in
  `wip/bernspike.lean` (both statements elaborating with only cosmetic
  warnings at that run's exit); the witness section left half-finished
  (the run exited before its terminal entry — the recurring
  interrupted-run pattern).
- **Run `20260830T150349Z-run-1`** (this run; delivery): the spike
  finished to zero errors/zero warnings — the witness redesigned at
  `λ = 5/9` so the comparison rides the pinned `e` exactly, the
  previous run's draft constant corrected (see above); the shelf
  landed (`Bernstein.lean` rewritten: engine + repaired theorems +
  `bernstein_iid`, module docstring recording the repair); the four
  consumer sites re-threaded; the retirement QA (+15: the biased-coin
  fixture family, the MGF-separation witness, the refutation fence,
  the two fair-coin closed-form instances with
  `iIndepFun.of_subsingleton` supplying singleton independence); the
  axiom audit (`wip/bernretire_axcheck.lean`, 33 declarations); the
  full ladder; Errata §8; this record; the status-record stamps
  (README, radar, both index maps, coverage map, architecture §12,
  scoreboard row, both map files' stat stamps + regenerated SVG).

**Verification:** the spike iterated to zero errors/zero warnings
before any shelf edit; `lake env lean` zero errors on every touched
module with warning baselines compared against HEAD by file-pair
elaboration (`Bernstein.lean` strictly fewer warnings than HEAD — the
`bernstein_iid` section-variable note gone with the theorem route;
`Scalar_QA.lean` +2 statement-binder warnings of the recorded
zero-family class — the `∑ i : Fin 1` binders in the two instance
statements, recorded not appeased per the retirement precedent);
explicit `lake build` targets ✔ on `Bernstein`,
`Scalar_QA`, `EdgePerturbationTail`, `EdgePerturbation_QA`;
`#print axioms` via `wip/bernretire_axcheck.lean` exactly as
summarized above; **full `lake build` ✔ (2406/2407) immediately
followed by `check_build_completeness.py` — 129 source files, 129
fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` (6, both
PF findings allowlisted-confirmed), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**3160/6/0**);
map-freshness stats sync (3145 → 3160, 8 → 6) passing exit 0.

## Technique findings

- `Real.add_one_lt_exp` in the pinned Mathlib takes `(h : x ≠ 0) :
  x + 1 < exp x` — passing the goal-shaped `x + 1 ≠ 0` silently
  instantiates `x := x + 1` and produces a useless hypothesis
  (`(x+1) + 1 < exp (x+1)`); pass `x ≠ 0` and rewrite the sum
  (`rwa [show -x + 1 = 1 - x from by norm_num] at h`), the delivered
  `exp_tiny_lt_QA`'s idiom.
- `Integrable.smul_measure` needs `{c : ℝ≥0∞} (hc : c ≠ ∞)`; at
  concrete ENNReal coefficients `(by norm_num)` does not close
  `c ≠ ∞` — `ENNReal.div_lt_top (by norm_num) (by norm_num)).ne`
  does, and the named-argument form `(c := …)` is required to pin the
  implicit coefficient.
- ENNReal tenths (`(1:ℝ≥0∞)/10 + (9:ℝ≥0∞)/10 = 1`) resist `norm_num`;
  the route is `div_eq_mul_inv` twice, `← add_mul`, then
  `ENNReal.mul_inv_cancel` — the same breakthrough the shelf's
  `rademacherMeasure_univ_QA` recorded for halves.
- `rw` cannot apply a bounded-integral lemma like
  `coin_integral (f) (c) hb` with `f` inferred — higher-order pattern
  unification fails; pass `f` explicitly (as a lambda) and beta-reduce
  with `simp only`.
- `cases b` on `Bool` yields `false` **first**; bullets named by
  `with | true => … | false => …` are immune to the order trap.
- One positionless `Try this: ring_nf` info note accompanies the
  engine (`Bernstein.lean` and the spike both); the same class the
  pairwise repair and the Hoeffding QA recorded — info-level, exit 0,
  recorded here rather than chased further.

## Follow-ons priced, not owed

None named. The natural next retirement targets are the matrix trio
(`matrix_hoeffding`, `matrix_bernstein`, `matrix_azuma_hoeffding` —
each would need the matrix MGF machinery) and `hoeffding_lemma`'s
still-open consumer question.
