# Proposal: Retire `hoeffding_inequality` and `hoeffding_empirical` by Proving Hoeffding's Lemma Locally

**Status:** DELIVERED 2026-08-30 (run `20260830T030715Z-run-1` proved
the core and both retirements — axioms 10 → 8, committed at e77df27 —
but exited before its terminal entry; run `20260830T053158Z-run-1`
verified the tree independently, added the adversarial QA planned by
the first run (fences and closed-form instances), audited the Derived
consumers' axiom loads, and wrote this record). Zero new axioms; the
admitted-axiom count drops 10 → 8. See
[Delivery record](#delivery-record).

## Why this, now

Priority item 4 (reduce the explicit trust surface), selected per
priority item 0 (no High rows; the one Medium-High row consumer-gated;
all Low rows human-decision-gated). Of the ten admitted axioms after
the pairwise-independence repair, `hoeffding_inequality` and
`hoeffding_empirical` were two whose entire mathematical content
follows from a two-standard-step argument:

- the secant/convexity bound `e^{λx} ≤ ((b−x)/(b−a)) e^{λa} +
  ((x−a)/(b−a)) e^{λb}` for `x ∈ [a,b]` (`convexOn_exp`),
- integrated against a mean-zero law to land on the two-point
  combination `φ(u) = (1−p) e^{−pu} + p e^{(1−p)u}` at
  `p = −a/(b−a)`,
- the sharp two-point bound `φ(u) ≤ e^{u²/8}`, and
- the classical Chernoff assembly (independence factorization, Markov
  at `exp (λ·∑)`, λ-optimization at `λ = 4t/∑(d i − c i)²`).

Every needed pin lemma exists in the pinned Mathlib
(`IndepFun.integral_mul_of_nonneg`,
`iIndepFun.indepFun_finset_prod_of_not_mem`,
`antitone_of_deriv_nonpos`, `Real.exp_sum`, `HasDerivAt.log`), so the
retirement needed no new mathematical admission at all.

Consumer leverage: `hoeffding_inequality` was the load-bearing axiom of
the delivered degree-tail family and the window family's degree half;
`hoeffding_empirical` carried the empirical-stationary tails. Retiring
both makes every one of those consumers strictly lighter — the audit
below shows four of them become hard crust outright.

## The proof

### The analytic core (`phiComb_le_exp`)

For `p ∈ [0,1]` the two-point combination

```
φ(u) = (1−p) e^{−pu} + p e^{(1−p)u}
```

satisfies `φ(u) ≤ e^{u²/8}`. Route: the perfect-square identity

```
φ² − 4(φ''φ − φ'²) = ((1−p) e^{−pu} − p e^{(1−p)u})² ≥ 0,
```

so `(log φ)'' = (φ''φ − φ'²)/φ² ≤ 1/4` (`phiComb_square`), and `H(u) =
u²/8 − log φ(u)` has `H' = u/4 − φ'/φ` with `H(0) = 0`; two
monotone-on-half-line arguments (`monotoneOn_of_deriv_nonneg`,
`antitoneOn_of_deriv_nonpos`) give `H ≥ 0` on both sides of `0`.

### The interval engine (`hoeffding_lemma_mgf`)

A measurable, mean-zero `X ∈ [a,b]` on a probability measure
satisfies `E exp (λX) ≤ exp (λ²(b−a)²/8)`. Degenerate interval
(`a = b`): mean-zero forces `X ≡ 0` and both sides are `1`. Main case:
the secant bound pointwise (`convexOn_exp`), monotone integration (the
two affine sides are integrable through
`integrable_of_bounded_measurable`), the affine integrals evaluate to
`b` and `−a`, landing exactly on `φ(λ(b−a))` at `p = −a/(b−a)`, then
the core. The mean-zero hypothesis is honest by construction:
`integrable_of_bounded_measurable` (the 2026-08-28 audit's safety
lemma) is applied before any integral manipulation.

### The Chernoff assembly

`mgf_sum_le_of_iIndepFun` factors the sum's MGF by mutual independence
(`integral_prod_exp_of_iIndepFun`: a Finset induction whose insert-step
is `iIndepFun.indepFun_finset_prod_of_not_mem` — this is where the
pairwise-repair's `iIndepFun` clause shape is genuinely load-bearing);
`markov_tail_of_mgf` is the Markov step; `hoeffding_inequality_interval`
optimizes at `λ = 4t/W` (`W = ∑(d i − c i)² > 0`) and unions the two
tails. The `W = 0` corner is handled honestly: every interval is then
degenerate, mean-zero forces every `X i ≡ 0`, and the statement
degenerates to `1 ≤ 2` (at `t = 0`) / the empty event. The public
shapes `hoeffding_inequality` (interval `[−a i, a i]`, exponent
`−t²/(2∑a i²)`) and `hoeffding_empirical` (centered `[0,1]` averages,
exponent `−2 n t²`, the `n = 0` junk corner handled by the `2 ≥ 1`
trivial bound) are derivations, not re-statements.

## Degenerate-corner analysis (Step 0)

Checked before the statements were frozen, against the §5 hazard list:

- **Empty/degenerate cardinality**: the scalar prefactor is the
  constant `2`, never a `card V`-collapsing prefactor — no `Nonempty`
  guard needed (the matrix trio's hazard does not transfer). The `n = 0`
  corner of `hoeffding_empirical` instantiates to `P(∅-sum event) ≤ 2`
  — trivially true, handled by the explicit `2 ≥ 1` branch rather than
  junk arithmetic.
- **Unconstrained measure mass**: `[IsProbabilityMeasure μ]` is an
  instance assumption on every statement — and the QA mass-guard fence
  below proves the conclusion *fails* at the mass-`19/10` fixture with
  every other hypothesis genuinely satisfied, so the guard is
  load-bearing, not decorative.
- **Junk-valued integrals**: every `h_mean` hypothesis is paired with
  `integrable_of_bounded_measurable` before integration; the
  secant-bound sides are proved integrable in the engine.
- **Wrong constant**: the `1/8` in the engine and the `2` in the tail
  denominators are the source's exact constants; both are pinned by
  the fences below.

No Errata entry: an honestly-admitted axiom proved is the retirement
lifecycle working, not a falsity record
(`docs/9_ERRATA.md`'s own exclusion).

## Delivery record

### Run 1 (`20260830T030715Z-run-1`): the proof

`Hoeffding.lean` rewritten: the analytic core (`phiComb`,
`phiComb_le_exp`), `hoeffding_lemma_mgf`,
`integral_prod_exp_of_iIndepFun`, `mgf_sum_le_of_iIndepFun`,
`markov_tail_of_mgf`, `hoeffding_inequality_interval`, and the two
retired statements as theorems at unchanged public shapes; plus
`hoeffding_iid` (the Vershynin Corollary 2.2.3 form, proved). The
spike is preserved at `wip/hoeffding_mgf_spike.lean`. Independently
verified after the run's early exit (operator closing note): full
build, build-completeness 129/129, `#print axioms` standard-three on
all three names, axiom count 8 by direct grep.

### Run 2 (`20260830T053158Z-run-1`): this record and the QA

The adversarial QA the first run planned but did not land
(`Scalar_QA.lean`, +24 declarations), all spiked to zero
errors/warnings before shelf insertion:

1. **The wrong-constant fence at the MGF level**
   (`hoeffding_lemma_mgf_constant_fence_QA`): the fair-coin Rademacher
   fixture's *exact* MGF `(e + e⁻¹)/2` (closed form through the two
   Dirac atoms) is at least `3/2` at `λ = 1`, while the lemma's
   conclusion sharpened from constant `8` to `12` reads
   `exp (1/3) < 3/2` — so any proof regression landing on a
   denominator above `12` makes the theorem false, and the fence
   catches it. (Fixture-scale sharpness threshold: the true MGF
   exceeds `exp (4/K)` iff `K > 4/log((e+e⁻¹)/2) ≈ 9.22`; the fence
   pins `K ≤ 12` refutable with first-decimal arithmetic alone.)
2. **The mass-guard fence** (`hoeffding_lemma_mgf_mass_guard_fence_QA`):
   at the mass-`19/10` measure every *other* hypothesis holds
   genuinely — measurability (discreteness), the pointwise bound, the
   mean (`scaledRademacherMeasure_mean_QA`, on the shelf since the
   2026-08-28 audit) — and the MGF scales with the mass to `≥ 57/20`
   against the bound `exp (1/2) < 5/3`. The probability-measure
   hypothesis is load-bearing.
3. **The tail-level denominator fence**
   (`hoeffding_inequality_denominator_fence_QA`): on the fair two-coin
   BernoulliProduct space, the Rademacher lift's tail event at `t = 2`
   is the agreement event, of *exactly* `1/2` (computed through the
   design's own independence machinery — `indepFun_coord` +
   `toMeasure_cyl` — independently of the tail theorem), while the
   theorem with the factor `2` dropped from the exponent denominator
   reads `2 exp (−2) < 1/2`. The tail-level wrong-constant class, with
   the event measure pinned exactly rather than bounded.
4. **Closed-form instances**: the MGF lemma at the fair coin with the
   two-sided window `3/2 ≤ (e+e⁻¹)/2 ≤ exp (1/2) < 5/3` (the bound
   within `1/6` of the true value — non-vacuous on both ends);
   `hoeffding_inequality` at the genuinely random two-coin Rademacher
   family (its first nonconstant instantiation — the zero-family
   instances cannot exercise the `iIndepFun` clause at all), bound
   `2 exp (−1)` with the slack `1/2 < 2 exp (−1)` pinned; and
   `hoeffding_empirical` at the `[0,1]` coordinate indicators, the
   deviation event again exactly `1/2` against `2 exp (−1)`.

**Consumer audit** (`#print axioms`, `wip/hoeffding_qa_axcheck.lean`,
37 declarations): the 24 new QA declarations all exactly
`propext, Classical.choice, Quot.sound` (the fences prove `False` with
no axiom contact; the instances consume only proved theorems);
`edgePerturbation_degree_tail` and `edgePerturbation_degree_tail_all`
are now **hard crust**; `hoeffding_empirical_iid` and
`empiricalWalkDistribution_tail` are now **hard crust**; the six
window-family members are conditional on `matrix_hoeffding` alone
(previously `matrix_hoeffding` AND `hoeffding_inequality`).

**Technique findings** (the spike's caught slips): `rw` cannot rewrite
under a set-builder membership — `simp only [Set.mem_setOf_eq]` first
(the deviation-event proof's `rw [hmean ω]` failed against `ω ∈ {ω |
…}` until reordered); an `if-then-else` chain intended as a sum needs
explicit parentheses (`if ω 0 then 1 else 0 + if ω 1 …` parses the
`else` branch as the sum — the TT case proved `False` until
parenthesized); the positionless `Try this: ring_nf` note bisected to
a `ring` call closing a post-`rw` identity (replaced by `ring_nf`,
the same lesson the pairwise repair recorded).

**Baseline-warning note**: `Scalar_QA.lean`'s zero-family lemmas carry
7 pre-existing binder warnings (set-builder `ω`/`i`, one
`unusedSectionVars`) — verified byte-identical in multiset against the
HEAD baseline by file-pair elaboration; they arrived with the
retirement commit's own edits, not this delivery, and are recorded
rather than appeased (the MatrixMDS delivery's precedent).

## Residual honesty

The retired statements are now genuinely proved — no residual axiom
contact. The remaining admitted axioms touching this neighborhood:
`matrix_hoeffding` (the window family's window half), the Bernstein
pair, `hoeffding_lemma` (still the one zero-consumer axiom; its
natural consumer is `bernstein_inequality`'s own proof — upstream
work), and `matrix_azuma_hoeffding`. The fixture-scale junk-measure
obstruction recorded for the window family applies to the new
instances too: at two-coin scale the exponential never drops below the
atom masses, so the *exactness* pins and the MGF-level fence carry the
falsification content.
