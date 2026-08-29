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
# Bernstein's inequality

Bernstein's tail bound for sums of bounded independent real random
variables with a variance-dependent denominator, stated over an arbitrary
probability measure with Mathlib's `ProbabilityTheory.IndepFun`.

`bernstein_iid` is not an axiom: it is derived from
`bernstein_inequality` by instantiating the common variance, keeping the
trust boundary minimal.
-/

open MeasureTheory ProbabilityTheory Real

namespace Scaffold.Mathlib.Probability.Concentration.Scalar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrability safety for the variance statistics in
`bernstein_inequality` and `bernstein_bounded_variance`: on a
probability measure, a measurable uniformly bounded variable has its
centered square integrable, so the variance integrals appearing in both
axioms' conclusions (and the `h_var` clause of the budget form) are
honest — none of them can be the junk `0` of
`MeasureTheory.integral_undef`.

Recorded by the integrability audit of 2026-08-28
(`proposals/audit-scalar-concentration-integrability-hazard.md`, Step
0). QA: `integrable_sq_sub_mean_rademacher_QA` in
`Scaffold/QA/Concentration/Scalar_QA.lean`.
-/
theorem integrable_sq_sub_mean {X : Ω → ℝ} {a : ℝ}
    (h_meas : Measurable X) (h_bound : ∀ ω, |X ω| ≤ a) :
    Integrable (fun ω => (X ω - ∫ ω', X ω' ∂μ) ^ 2) μ := by
  set c : ℝ := ∫ ω', X ω' ∂μ with hc
  have hbdd : ∀ ω, |X ω - c| ≤ |a| + |c| := by
    intro ω
    have hX : |X ω| ≤ |a| := (h_bound ω).trans (le_abs_self a)
    calc |X ω - c| ≤ |X ω| + |c| := abs_sub _ _
      _ ≤ |a| + |c| := add_le_add hX le_rfl
  have hmsub : Measurable fun ω => X ω - c := h_meas.sub measurable_const
  have hm : Measurable fun ω => (X ω - c) ^ 2 := by
    have hmul : Measurable fun ω => (X ω - c) * (X ω - c) := hmsub.mul hmsub
    have heq : (fun ω => (X ω - c) ^ 2) = fun ω => (X ω - c) * (X ω - c) := by
      funext ω; rw [sq]
    rw [heq]; exact hmul
  refine Integrable.mono' (integrable_const ((|a| + |c|) ^ 2)) hm.aestronglyMeasurable ?_
  refine ae_of_all μ fun ω => ?_
  have h1 : |X ω - c| ^ 2 ≤ (|a| + |c|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hbdd ω) 2
  simpa [Real.norm_eq_abs, sq_abs] using h1

/-- Bernstein's inequality: a sum of independent variables with
`|X i ω| ≤ a` satisfies the two-sided, variance-dependent tail bound
`P {|∑ (X i - E (X i))| ≥ t} ≤ 2 exp (-t² / (2 V + 2 a t / 3))`,
where `V = ∑ i Var (X i)` is written with explicit centered integrals.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Cambridge University
  Press, 2018, Theorem 2.8.1, Chapter 2, p. 43.

Statement differences: the source states a one-sided bound for sums of
independent centered variables; we state the two-sided form for the
centered sum (doubling the right-hand side) and write the variance
statistic explicitly instead of through a `let`.

QA: exercised by `bernstein_inequality_zero_QA` in
`Scaffold/QA/Concentration/Scalar_QA.lean`, which instantiates the axiom at
the zero sequence and checks the resulting empty-event bound.
-/
axiom bernstein_inequality {n : ℕ} {X : Fin n → Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω| ≤ a)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, (X i ω - ∫ ω', X i ω' ∂μ)| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) /
        (2 * ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ + (2 * a * t) / 3)))

/-- Bernstein's inequality with an explicit variance budget `v`
dominating the total variance.

Source:
- Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint,
  Cambridge University Press, 2019, Theorem 2.15, Chapter 2, p. 52.

Statement differences: as in `bernstein_inequality`, plus the budget form
`∑ Var (X i) ≤ v`, which relaxes the denominator monotonically.

QA: no dedicated thin QA; the degenerate case reduces to the zero-sequence
pattern certified for `bernstein_inequality`.
-/
axiom bernstein_bounded_variance {n : ℕ} {X : Fin n → Ω → ℝ} {a v : ℝ}
    (ha : 0 ≤ a) (hv : 0 ≤ v)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω| ≤ a)
    (h_var : ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ ≤ v)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, (X i ω - ∫ ω', X i ω' ∂μ)| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * v + (2 * a * t) / 3)))

/-- Bernstein's inequality for identically distributed variables with
common centered second moment `σ_sq`. This is a proved consequence of
`bernstein_inequality`, not an axiom.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Corollary 2.8.3,
  Chapter 2, p. 45.

Statement differences: we state the direct instantiation
`2 exp (-t² / (2 n σ² + 2 a t / 3))` of the general bound; an equivalent
form rescales the numerator to `n t²`.
-/
theorem bernstein_iid {n : ℕ} {X : Fin n → Ω → ℝ} {a σ_sq : ℝ} (ha : 0 ≤ a)
    (hσ : 0 ≤ σ_sq)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω| ≤ a)
    (h_var : ∀ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ = σ_sq)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, (X i ω - ∫ ω', X i ω' ∂μ)| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * ((n : ℝ) * σ_sq) + (2 * a * t) / 3))) := by
  have h := bernstein_inequality ha h_meas h_indep h_bound t ht
  rwa [show ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ = (n : ℝ) * σ_sq by
    rw [Finset.sum_congr rfl (fun i _ => h_var i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]] at h

end Scaffold.Mathlib.Probability.Concentration.Scalar
