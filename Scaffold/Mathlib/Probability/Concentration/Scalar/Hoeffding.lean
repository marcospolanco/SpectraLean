/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Hoeffding's inequality

Hoeffding's tail bound for sums of bounded, centered, independent real
random variables, stated over an arbitrary probability measure with
Mathlib's `ProbabilityTheory.IndepFun`.

`hoeffding_iid` is not an axiom: it is derived from `hoeffding_inequality`
by instantiating the per-variable bounds, keeping the trust boundary
minimal.
-/

open MeasureTheory ProbabilityTheory Real

namespace Scaffold.Mathlib.Probability.Concentration.Scalar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrability safety for `hoeffding_inequality`'s hypothesis clauses:
on a probability measure, a measurable uniformly bounded variable is
integrable, so the axiom's `h_mean : ∫ X i ∂μ = 0` clause is an honest
constraint — the mean integral cannot be the junk `0` that
`MeasureTheory.integral_undef` assigns to non-integrable functions.

Recorded by the integrability audit of 2026-08-28
(`proposals/audit-scalar-concentration-integrability-hazard.md`, Step
0): together with the probability-measure constraint, this rules out
both junk mechanisms that made the sibling
`subgaussian_tail_bound` axiom materially false. QA: `integrable_rademacher_QA` in
`Scaffold/QA/Concentration/Scalar_QA.lean`.
-/
theorem integrable_of_bounded_measurable {X : Ω → ℝ} {a : ℝ}
    (h_meas : Measurable X) (h_bound : ∀ ω, |X ω| ≤ a) : Integrable X μ :=
  Integrable.mono' (integrable_const |a|) h_meas.aestronglyMeasurable
    (ae_of_all μ fun ω => by
      have hX : |X ω| ≤ |a| := (h_bound ω).trans (le_abs_self a)
      simpa [Real.norm_eq_abs] using hX)

/-- Hoeffding's inequality: a sum of independent, centered variables with
`|X i ω| ≤ a i` satisfies the two-sided tail bound
`P {|∑ X i| ≥ t} ≤ 2 exp (-t² / (2 ∑ a i²))`.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Cambridge University
  Press, 2018, Theorem 2.2.2, Chapter 2, p. 24.

Statement differences: the source states the interval form
`P {∑ X i ≥ t} ≤ exp (-2t² / ∑ (b i - a i) ^ 2)` for `a i ≤ X i ≤ b i`;
we state the symmetric two-sided form obtained by taking
`a i = -a i`, `b i = a i`, which gives the denominator
`∑ (2 a i) ^ 2 / 4 = ∑ a i ^ 2` and doubles the tail probability.

QA: exercised by `hoeffding_inequality_zero_QA` in
`Scaffold/QA/Concentration/Scalar_QA.lean`, which instantiates the axiom at
the zero sequence and checks the resulting empty-event bound.
-/
axiom hoeffding_inequality {n : ℕ} {X : Fin n → Ω → ℝ} {a : Fin n → ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω| ≤ a i)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, X i ω| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ∑ i, (a i) ^ 2)))

/-- Hoeffding's inequality for identically distributed bounded variables:
with a uniform bound `|X i ω| ≤ a`, the denominator specializes to
`n a²`. This is a proved consequence of `hoeffding_inequality`, not an
axiom.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Corollary 2.2.3,
  Chapter 2, p. 25.
-/
theorem hoeffding_iid {n : ℕ} {X : Fin n → Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω| ≤ a)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, X i ω| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ((n : ℝ) * a ^ 2)))) := by
  have h := hoeffding_inequality h_meas h_indep h_bound h_mean t ht
  rwa [show ∑ i : Fin n, a ^ 2 = (n : ℝ) * a ^ 2 by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]] at h

/-- Hoeffding's inequality for empirical averages of `[0, 1]`-valued
independent variables: `P {|mean - E mean| ≥ t} ≤ 2 exp (-2 n t²)`.

Source:
- Boucheron, Lugosi, Massart, Concentration Inequalities: A Nonasymptotic
  Theory of Independence, Oxford University Press, 2013, Theorem 2.8,
  Chapter 2, p. 32.

Statement differences: none; the empirical-mean form is stated directly.
For `n = 0` both the deviation (junk `0`) and the bound are consistent with
the source, since a probability never exceeds `1 ≤ 2`.

QA: no dedicated thin QA beyond the shared zero-sequence pattern already
covered by `hoeffding_inequality_zero_QA`; the statement adds the
centering structure, whose degenerate case reduces to that pattern.
-/
axiom hoeffding_empirical {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |(1 / (n : ℝ)) * ∑ i, X i ω
        - (1 / (n : ℝ)) * ∑ i, ∫ ω', X i ω' ∂μ| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * t ^ 2))

end Scaffold.Mathlib.Probability.Concentration.Scalar
