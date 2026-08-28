# Scalar Concentration Inequalities

Definitions and cited axioms for concentration inequalities of scalar
(real-valued) random variables, stated over an explicit probability
measure with Mathlib's `ProbabilityTheory.IndepFun`.

## Modules

### `Subgaussian.lean`

The subgaussian (ψ₂) norm and its admitted consequences.

**Definitions**:
- `subgaussianNorm` - Ψ₂ norm via the MGF characterization
- `subgaussianNorm_nonneg` - proved nonnegativity

**Axioms**:
- `hoeffding_lemma` - bounded and centered ⇒ ≤ √6·a-subgaussian on
  probability measures (repaired 2026-08-28: the pre-repair
  `≤ a` shape with no measure guard was materially false — two
  refutation witnesses in `QA/Concentration/Scalar_QA.lean`)
- `subgaussian_tail_bound` - P(|X| ≥ t) ≤ 2exp(-t²/(2K²))

**Source**: Vershynin, High-Dimensional Probability, Chapter 2

### `Hoeffding.lean`

**Axioms**:
- `hoeffding_inequality` - sums of bounded independent variables
- `hoeffding_empirical` - empirical averages of [0,1] variables

**Proved** (not axioms):
- `hoeffding_iid` - uniform-bound specialization of `hoeffding_inequality`
- `integrable_of_bounded_measurable` - the audit's integrability safety
  lemma (measurable + bounded + probability measure ⇒ `Integrable`)

**Sources**: Vershynin Thm 2.2.2 / Cor 2.2.3; Boucheron–Lugosi–Massart Thm 2.8

### `Bernstein.lean`

**Axioms**:
- `bernstein_inequality` - variance-dependent tail bound
- `bernstein_bounded_variance` - explicit variance budget form

**Proved** (not axioms):
- `integrable_sq_sub_mean` - the audit's centered-square integrability
  safety lemma for both axioms' variance statistics
- `bernstein_iid` - common-variance specialization of `bernstein_inequality`

**Sources**: Vershynin Thm 2.8.1 / Cor 2.8.3; Wainwright Thm 2.15

See `index/map/probability_concentration.md` for the full
declaration-to-source mapping.
