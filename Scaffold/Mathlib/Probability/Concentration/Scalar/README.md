# Scalar Concentration Inequalities

Definitions and proved theorems for concentration inequalities of scalar
(real-valued) random variables, stated over an explicit probability
measure with Mathlib's `ProbabilityTheory.iIndepFun`. **The scalar
concentration subtree is axiom-free end to end** — every former axiom
was repaired where defective and then retired by local proof across
2026-08-22 through 2026-08-30.

## Modules

### `Subgaussian.lean`

The subgaussian (ψ₂) norm and its proved consequences.

**Definitions**:
- `subgaussianNorm` - Ψ₂ norm via the MGF characterization
- `subgaussianNorm_nonneg` - proved nonnegativity

**Proved** (not axioms):
- `subgaussianNorm_eq_zero_of_forall_eq_zero` - a pointwise-zero
  variable has norm exactly `0` (the `a = 0` corner)
- `subgaussianNorm_le_of_bounded` - the sharp boundedness-only collapse
  `subgaussianNorm ≤ a/√(log 2)` (no centering, no measurability, no
  numeric pins; constant attained at every `|X| ≡ a` fixture)
- `hoeffding_lemma` - bounded and centered ⇒ ≤ √6·a-subgaussian on
  probability measures (**proved 2026-08-30** by the pointwise-collapse
  route at the unchanged shape; repaired 2026-08-28 when the pre-repair
  `≤ a` shape with no measure guard was found materially false — two
  refutation witnesses in `QA/Concentration/Scalar_QA.lean`; the
  mean-zero hypothesis is unused by the proof, retained for statement
  stability — see `proposals/retire-hoeffding-lemma-pointwise-collapse.md`)
- `subgaussian_tail_bound` - P(|X| ≥ t) ≤ 2exp(-t²/(2K²)) (proved
  2026-08-22)

**Source**: Vershynin, High-Dimensional Probability, Chapter 2

### `Hoeffding.lean`

**Proved** (not axioms; the tail pair retired 2026-08-30):
- `hoeffding_lemma_mgf` - Hoeffding's lemma in λ-form,
  `E exp(λX) ≤ exp(λ²(b−a)²/8)` — the local proof that retired the pair
- `hoeffding_inequality` - sums of bounded independent variables
- `hoeffding_empirical` - empirical averages of [0,1] variables
- `hoeffding_iid` - uniform-bound specialization of `hoeffding_inequality`
- `integrable_of_bounded_measurable` - the audit's integrability safety
  lemma (measurable + bounded + probability measure ⇒ `Integrable`)

**Sources**: Vershynin Thm 2.2.2 / Cor 2.2.3; Boucheron–Lugosi–Massart Thm 2.8

### `Bernstein.lean`

**Proved** (not axioms; the pair repaired and retired 2026-08-30, Errata §8):
- `bernstein_inequality` - variance-dependent tail bound (Bennett MGF
  engine)
- `bernstein_bounded_variance` - explicit variance budget form
- `bernstein_iid` - common-variance specialization of `bernstein_inequality`
- `integrable_sq_sub_mean` - the audit's centered-square integrability
  safety lemma for both variance statistics

**Sources**: Vershynin Thm 2.8.1 / Cor 2.8.3; Wainwright Thm 2.15

See `index/map/probability_concentration.md` for the full
declaration-to-source mapping.
