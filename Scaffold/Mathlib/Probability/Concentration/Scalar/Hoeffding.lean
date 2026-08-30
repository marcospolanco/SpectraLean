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
import Mathlib.Probability.Integration
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Hoeffding's inequality

Hoeffding's tail bound for sums of bounded, centered, independent real
random variables, stated over an arbitrary probability measure with
Mathlib's `ProbabilityTheory.IndepFun`.

`hoeffding_inequality` and `hoeffding_empirical` are **not** axioms: they
were retired from axioms to theorems (2026-08-30) by proving Hoeffding's
lemma locally in MGF interval form (`hoeffding_lemma_mgf`) and deriving
both tail statements from it by the classical Chernoff route — the
secant/convexity bound, the sharp two-point combination
`φ(u) = (1-p)e^{-pu} + pe^{(1-p)u} ≤ e^{u²/8}` (by the perfect-square
identity `4(φ''φ - φ'²) = 4p(1-p)AB ≤ φ²`), independence factorization,
and Markov's inequality at `λ = 4t/∑(d i - c i)²`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

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

/-! ## The analytic core -/

/-- The two-point exponential combination of Hoeffding's lemma. -/
noncomputable def phiComb (p u : ℝ) : ℝ :=
  (1 - p) * Real.exp (-(p * u)) + p * Real.exp ((1 - p) * u)

/-- First `u`-derivative of `phiComb p`. -/
noncomputable def phiCombDeriv (p u : ℝ) : ℝ :=
  p * (1 - p) * (Real.exp ((1 - p) * u) - Real.exp (-(p * u)))

/-- Second `u`-derivative of `phiComb p`. -/
noncomputable def phiCombDeriv2 (p u : ℝ) : ℝ :=
  p * (1 - p) * ((1 - p) * Real.exp ((1 - p) * u) + p * Real.exp (-(p * u)))

private theorem hasDerivAt_exp_const_mul (c u : ℝ) :
    HasDerivAt (fun u => Real.exp (c * u)) (c * Real.exp (c * u)) u := by
  have h := (hasDerivAt_exp (𝕂 := ℝ) (x := c * u)).comp u
    ((hasDerivAt_id u).const_mul c : HasDerivAt (fun y : ℝ => c * y) (c * 1) u)
  simpa [Function.comp_def, Real.exp_eq_exp_ℝ, mul_comm] using h

private theorem hasDerivAt_phiComb (p u : ℝ) :
    HasDerivAt (phiComb p) (phiCombDeriv p u) u := by
  have hA := hasDerivAt_exp_const_mul (1 - p) u
  have hB : HasDerivAt (fun y => Real.exp (-(p * y))) (-(p * Real.exp (-(p * u)))) u := by
    have h := hasDerivAt_exp_const_mul (-p) u
    simpa [neg_mul] using h
  have h := (hB.const_mul (1 - p)).add (hA.const_mul p)
  have h2 : HasDerivAt (phiComb p)
      ((1 - p) * (-(p * Real.exp (-(p * u)))) + p * ((1 - p) * Real.exp ((1 - p) * u))) u := by
    refine HasDerivAt.congr_of_eventuallyEq h ?_
    exact Filter.Eventually.of_forall (fun _ => rfl)
  exact h2.congr_deriv (by simp only [phiCombDeriv]; ring)

private theorem hasDerivAt_phiCombDeriv (p u : ℝ) :
    HasDerivAt (phiCombDeriv p) (phiCombDeriv2 p u) u := by
  have hA := hasDerivAt_exp_const_mul (1 - p) u
  have hB : HasDerivAt (fun y => Real.exp (-(p * y))) (-(p * Real.exp (-(p * u)))) u := by
    have h := hasDerivAt_exp_const_mul (-p) u
    simpa [neg_mul] using h
  have hsub := (hA.const_mul (p * (1 - p))).sub (hB.const_mul (p * (1 - p)))
  have h2 : HasDerivAt (phiCombDeriv p)
      (p * (1 - p) * ((1 - p) * Real.exp ((1 - p) * u))
        - p * (1 - p) * (-(p * Real.exp (-(p * u))))) u := by
    refine HasDerivAt.congr_of_eventuallyEq hsub ?_
    exact Filter.Eventually.of_forall (fun y => by simp only [phiCombDeriv]; ring)
  exact h2.congr_deriv (by simp only [phiCombDeriv2]; ring)

private theorem phiComb_pos (p u : ℝ) (hp : p ∈ Set.Icc 0 1) : 0 < phiComb p u := by
  obtain ⟨hp1, hp2⟩ := hp
  rcases eq_or_lt_of_le hp1 with rfl | hp1'
  · simp [phiComb]
  · have h2 : 0 < p * Real.exp ((1 - p) * u) := mul_pos hp1' (Real.exp_pos _)
    have h1 : 0 ≤ (1 - p) * Real.exp (-(p * u)) :=
      mul_nonneg (by linarith) (le_of_lt (Real.exp_pos _))
    simp only [phiComb]
    linarith

/-- The perfect-square identity: `4 (φ''φ - φ'²) ≤ φ²`. -/
private theorem phiComb_square (p u : ℝ) :
    4 * (phiCombDeriv2 p u * phiComb p u - phiCombDeriv p u ^ 2) ≤ phiComb p u ^ 2 := by
  have h : phiComb p u ^ 2 - 4 * (phiCombDeriv2 p u * phiComb p u - phiCombDeriv p u ^ 2)
      = ((1 - p) * Real.exp (-(p * u)) - p * Real.exp ((1 - p) * u)) ^ 2 := by
    simp only [phiComb, phiCombDeriv, phiCombDeriv2]
    ring
  have h2 := sq_nonneg ((1 - p) * Real.exp (-(p * u)) - p * Real.exp ((1 - p) * u))
  linarith

private theorem hasDerivAt_phiComb_ratio (p x : ℝ) (hp : p ∈ Set.Icc 0 1) :
    HasDerivAt (fun y => phiCombDeriv p y / phiComb p y)
      ((phiCombDeriv2 p x * phiComb p x - phiCombDeriv p x ^ 2) / phiComb p x ^ 2) x := by
  have hinv : HasDerivAt (fun y => (phiComb p y)⁻¹)
      (-(phiComb p x ^ 2)⁻¹ * phiCombDeriv p x) x :=
    (hasDerivAt_inv (ne_of_gt (phiComb_pos p x hp))).comp x (hasDerivAt_phiComb p x)
  have h := (hasDerivAt_phiCombDeriv p x).mul hinv
  refine HasDerivAt.congr_deriv (HasDerivAt.congr_of_eventuallyEq h ?_) ?_
  · exact Filter.Eventually.of_forall (fun y => div_eq_mul_inv (phiCombDeriv p y) (phiComb p y))
  · have hc : phiComb p x ≠ 0 := ne_of_gt (phiComb_pos p x hp)
    field_simp [hc]
    ring

private theorem phiComb_ratio_deriv_nonpos (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    Antitone (fun u => phiCombDeriv p u / phiComb p u - u / 4) := by
  have hdiff : ∀ x : ℝ, HasDerivAt (fun y => phiCombDeriv p y / phiComb p y - y / 4)
      ((phiCombDeriv2 p x * phiComb p x - phiCombDeriv p x ^ 2) / phiComb p x ^ 2 - 1 / 4) x :=
    fun x => ((hasDerivAt_phiComb_ratio p x hp).sub ((hasDerivAt_id x).div_const 4)).congr_deriv
      (by ring)
  refine antitone_of_deriv_nonpos (fun x => (hdiff x).differentiableAt) (fun x => ?_)
  have h1 := hdiff x
  have h2 : (phiCombDeriv2 p x * phiComb p x - phiCombDeriv p x ^ 2) / phiComb p x ^ 2 - 1 / 4
      ≤ 0 := by
    have hsq := phiComb_square p x
    have hpos : 0 < phiComb p x ^ 2 := sq_pos_of_pos (phiComb_pos p x hp)
    have key : (phiCombDeriv2 p x * phiComb p x - phiCombDeriv p x ^ 2) / phiComb p x ^ 2
        ≤ 1 / 4 := by
      rw [div_le_div_iff₀ hpos (by norm_num)]
      linarith
    linarith
  rw [h1.deriv]
  exact h2

private theorem phiComb_ratio_zero (p : ℝ) : phiCombDeriv p 0 / phiComb p 0 - 0 / 4 = 0 := by
  simp [phiComb, phiCombDeriv]

private theorem phiComb_ratio_le (p : ℝ) (hp : p ∈ Set.Icc 0 1) {u : ℝ} (hu : 0 ≤ u) :
    phiCombDeriv p u / phiComb p u ≤ u / 4 := by
  have hK := phiComb_ratio_deriv_nonpos p hp
  have h0 : (fun u => phiCombDeriv p u / phiComb p u - u / 4) 0 = 0 := by
    simpa using phiComb_ratio_zero p
  have hle : (fun u => phiCombDeriv p u / phiComb p u - u / 4) u
      ≤ (fun u => phiCombDeriv p u / phiComb p u - u / 4) 0 := hK hu
  rw [h0] at hle
  simp only [] at hle ⊢
  linarith

private theorem phiComb_ratio_ge (p : ℝ) (hp : p ∈ Set.Icc 0 1) {u : ℝ} (hu : u ≤ 0) :
    u / 4 ≤ phiCombDeriv p u / phiComb p u := by
  have hK := phiComb_ratio_deriv_nonpos p hp
  have h0 : (fun u => phiCombDeriv p u / phiComb p u - u / 4) 0 = 0 := by
    simpa using phiComb_ratio_zero p
  have hle : (fun u => phiCombDeriv p u / phiComb p u - u / 4) 0
      ≤ (fun u => phiCombDeriv p u / phiComb p u - u / 4) u := hK hu
  rw [h0] at hle
  simp only [] at hle ⊢
  linarith

/-- The sharp two-point exponential moment bound: for `p ∈ [0, 1]`,
`φ(u) = (1-p) e^{-pu} + p e^{(1-p)u} ≤ e^{u²/8}`. -/
theorem phiComb_le_exp (p : ℝ) (hp : p ∈ Set.Icc 0 1) (u : ℝ) :
    phiComb p u ≤ Real.exp (u ^ 2 / 8) := by
  have hHderiv : ∀ x : ℝ, HasDerivAt
      (fun y => y ^ 2 / 8 - Real.log (phiComb p y))
      (x / 4 - phiCombDeriv p x / phiComb p x) x := by
    intro x
    have h := ((hasDerivAt_pow 2 x).div_const 8).sub
      ((hasDerivAt_phiComb p x).log (ne_of_gt (phiComb_pos p x hp)))
    exact h.congr_deriv (by field_simp; ring)
  have hdiff : Differentiable ℝ (fun y => y ^ 2 / 8 - Real.log (phiComb p y)) :=
    fun x => (hHderiv x).differentiableAt
  -- H is increasing on [0, ∞)
  have hmono : MonotoneOn (fun y => y ^ 2 / 8 - Real.log (phiComb p y)) (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact hdiff.continuous.continuousOn
    · exact hdiff.differentiableOn
    · intro x hx
      rw [(hHderiv x).deriv]
      exact sub_nonneg.mpr (phiComb_ratio_le p hp (Set.mem_Ici.mp (interior_subset hx)))
  -- H is decreasing on (-∞, 0]
  have hanti : AntitoneOn (fun y => y ^ 2 / 8 - Real.log (phiComb p y)) (Set.Iic 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Iic 0) ?_ ?_ ?_
    · exact hdiff.continuous.continuousOn
    · exact hdiff.differentiableOn
    · intro x hx
      rw [(hHderiv x).deriv]
      exact sub_nonpos.mpr (phiComb_ratio_ge p hp (Set.mem_Iic.mp (interior_subset hx)))
  have hH0 : (fun y : ℝ => y ^ 2 / 8 - Real.log (phiComb p y)) 0 = 0 := by
    simp [phiComb]
  have hlog : Real.log (phiComb p u) ≤ u ^ 2 / 8 := by
    rcases le_or_lt 0 u with hu | hu
    · have hH := hmono (Set.mem_Ici.mpr (le_refl (0:ℝ))) (Set.mem_Ici.mpr hu) hu
      rw [hH0] at hH
      simpa using hH
    · have hH := hanti (Set.mem_Iic.mpr hu.le) (Set.mem_Iic.mpr (le_refl (0:ℝ))) hu.le
      rw [hH0] at hH
      simpa using hH
  have h1 : Real.log (phiComb p u) ≤ u ^ 2 / 8 := by linarith [hlog]
  calc phiComb p u = Real.exp (Real.log (phiComb p u)) := (Real.exp_log (phiComb_pos p u hp)).symm
    _ ≤ Real.exp (u ^ 2 / 8) := Real.exp_le_exp.mpr h1

/-! ## Hoeffding's lemma in MGF interval form -/

/-- Hoeffding's lemma, MGF interval form: a measurable, mean-zero random
variable with `X ω ∈ [a, b]` on a probability measure satisfies
`E exp(λX) ≤ exp(λ²(b-a)²/8)`. -/
theorem hoeffding_lemma_mgf {X : Ω → ℝ} {a b : ℝ}
    (hab : a ≤ b) (h_meas : Measurable X) (h_bound : ∀ ω, X ω ∈ Set.Icc a b)
    (h_mean : ∫ ω, X ω ∂μ = 0) (lam : ℝ) :
    ∫ ω, Real.exp (lam * X ω) ∂μ ≤ Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) := by
  have hXbnd : ∀ ω, |X ω| ≤ max |a| |b| := by
    intro ω
    obtain ⟨h1, h2⟩ := h_bound ω
    refine abs_le.mpr ⟨?_, ?_⟩
    · calc -(max |a| |b|) ≤ -|a| := neg_le_neg (le_max_left |a| |b|)
        _ ≤ a := by
            rcases le_or_lt 0 a with h0 | h0
            · calc -|a| ≤ 0 := neg_nonpos.mpr (abs_nonneg a)
                _ ≤ a := h0
            · rw [abs_of_neg h0] at *; linarith
        _ ≤ X ω := h1
    · calc X ω ≤ b := h2
        _ ≤ |b| := le_abs_self b
        _ ≤ max |a| |b| := le_max_right |a| |b|
  have hXint : Integrable X μ := integrable_of_bounded_measurable h_meas hXbnd
  rcases eq_or_lt_of_le hab with hab' | hab'
  · -- degenerate interval: X is constant, mean zero forces the constant 0
    subst hab'
    have hXc : ∀ ω, X ω = a := fun ω => le_antisymm (h_bound ω).2 (h_bound ω).1
    have ha : a = 0 := by
      have h1 : ∫ ω, (X ω - a) ∂μ = 0 - a := by
        rw [integral_sub hXint (integrable_const a), h_mean, integral_const]
        simp [measure_univ]
      have h2 : 0 ≤ ∫ ω, (X ω - a) ∂μ :=
        integral_nonneg (fun ω => sub_nonneg.mpr (le_of_eq (hXc ω).symm))
      have h3 : ∫ ω, (a - X ω) ∂μ = a - 0 := by
        rw [integral_sub (integrable_const a) hXint, h_mean, integral_const]
        simp [measure_univ]
      have h4 : 0 ≤ ∫ ω, (a - X ω) ∂μ :=
        integral_nonneg (fun ω => sub_nonneg.mpr (le_of_eq (hXc ω)))
      linarith
    have hint : ∫ ω, Real.exp (lam * X ω) ∂μ = 1 := by
      rw [integral_congr_ae (ae_of_all μ fun ω => by rw [hXc ω, ha, mul_zero, Real.exp_zero]),
        integral_const, measure_univ]
      simp
    rw [hint]
    have hz : lam ^ 2 * (a - a) ^ 2 / 8 = 0 := by
      rw [sub_self]
      norm_num
    rw [hz, Real.exp_zero]
  · -- the main case
    have hba : 0 < b - a := by linarith
    -- the mean forces a ≤ 0 ≤ b
    have hale : a ≤ 0 := by
      have h1 : ∫ ω, (X ω - a) ∂μ = 0 - a := by
        rw [integral_sub hXint (integrable_const a), h_mean, integral_const]
        simp [measure_univ]
      have h2 : 0 ≤ ∫ ω, (X ω - a) ∂μ := integral_nonneg (fun ω => sub_nonneg.mpr (h_bound ω).1)
      linarith
    have hbe : 0 ≤ b := by
      have h1 : ∫ ω, (b - X ω) ∂μ = b - 0 := by
        rw [integral_sub (integrable_const b) hXint, h_mean, integral_const]
        simp [measure_univ]
      have h2 : 0 ≤ ∫ ω, (b - X ω) ∂μ := integral_nonneg (fun ω => sub_nonneg.mpr (h_bound ω).2)
      linarith
    -- the secant (convexity) bound, pointwise
    have hsec : ∀ ω, Real.exp (lam * X ω) ≤ (b - X ω) / (b - a) * Real.exp (lam * a)
        + (X ω - a) / (b - a) * Real.exp (lam * b) := by
      intro ω
      obtain ⟨hx1, hx2⟩ := h_bound ω
      have ht0 : 0 ≤ (b - X ω) / (b - a) := div_nonneg (by linarith) (by linarith)
      have ht1 : (b - X ω) / (b - a) ≤ 1 := by
        rw [div_le_iff₀ (by linarith : 0 < b - a)]
        linarith
      have hconv := convexOn_exp.2 (Set.mem_univ (lam * a)) (Set.mem_univ (lam * b)) ht0
        (by linarith : 0 ≤ 1 - (b - X ω) / (b - a)) (by field_simp)
      simp only [smul_eq_mul] at hconv
      have hlhs : (b - X ω) / (b - a) * (lam * a)
          + (1 - (b - X ω) / (b - a)) * (lam * b) = lam * X ω := by
        field_simp
        ring
      have h1t : (1 - (b - X ω) / (b - a)) = (X ω - a) / (b - a) := by
        field_simp
      rw [hlhs, h1t] at hconv
      exact hconv
    -- the common-denominator form of the secant bound
    have hint2 : ∀ ω, (b - X ω) / (b - a) * Real.exp (lam * a)
        + (X ω - a) / (b - a) * Real.exp (lam * b)
        = ((b - X ω) * Real.exp (lam * a) + (X ω - a) * Real.exp (lam * b)) / (b - a) := by
      intro ω
      field_simp
    -- integrability of the two sides
    have hintexp : Integrable (fun ω => Real.exp (lam * X ω)) μ := by
      refine integrable_of_bounded_measurable
        (a := Real.exp (|lam| * max |a| |b|))
        (Real.measurable_exp.comp (h_meas.const_mul lam)) (fun ω => ?_)
      have h1 : |Real.exp (lam * X ω)| ≤ Real.exp (|lam| * max |a| |b|) := by
        rw [abs_of_nonneg (Real.exp_pos _).le]
        refine Real.exp_le_exp.mpr ?_
        calc lam * X ω ≤ |lam * X ω| := le_abs_self _
          _ = |lam| * |X ω| := abs_mul lam (X ω)
          _ ≤ |lam| * max |a| |b| := mul_le_mul_of_nonneg_left (hXbnd ω) (abs_nonneg lam)
      simpa [Real.norm_eq_abs] using h1
    have hub_meas : Measurable (fun ω => ((b - X ω) * Real.exp (lam * a)
        + (X ω - a) * Real.exp (lam * b)) / (b - a)) :=
      (((measurable_const.sub h_meas).mul measurable_const).add
        ((h_meas.sub measurable_const).mul measurable_const)).div_const _
    have hub_int : Integrable (fun ω => ((b - X ω) * Real.exp (lam * a)
        + (X ω - a) * Real.exp (lam * b)) / (b - a)) μ := by
      refine integrable_of_bounded_measurable
        (a := 2 * Real.exp (|lam| * max |a| |b|)) hub_meas (fun ω => ?_)
      obtain ⟨hy1, hy2⟩ := h_bound ω
      have hE : (0:ℝ) < Real.exp (|lam| * max |a| |b|) := Real.exp_pos _
      have h3 : |b - X ω| ≤ b - a := by
        have hb0 : 0 ≤ b - X ω := by linarith
        rw [abs_of_nonneg hb0]
        linarith
      have h4 : |X ω - a| ≤ b - a := by
        have ha0 : 0 ≤ X ω - a := by linarith
        rw [abs_of_nonneg ha0]
        linarith
      have hsplit : |(b - X ω) * Real.exp (lam * a) + (X ω - a) * Real.exp (lam * b)|
          ≤ 2 * (b - a) * Real.exp (|lam| * max |a| |b|) := by
        have hA : |Real.exp (lam * a)| ≤ Real.exp (|lam| * max |a| |b|) := by
          rw [abs_of_nonneg (Real.exp_pos _).le]
          refine Real.exp_le_exp.mpr ?_
          calc lam * a ≤ |lam * a| := le_abs_self _
            _ = |lam| * |a| := abs_mul lam a
            _ ≤ |lam| * max |a| |b| := mul_le_mul_of_nonneg_left (le_max_left _ _) (abs_nonneg _)
        have hB : |Real.exp (lam * b)| ≤ Real.exp (|lam| * max |a| |b|) := by
          rw [abs_of_nonneg (Real.exp_pos _).le]
          refine Real.exp_le_exp.mpr ?_
          calc lam * b ≤ |lam * b| := le_abs_self _
            _ = |lam| * |b| := abs_mul lam b
            _ ≤ |lam| * max |a| |b| := mul_le_mul_of_nonneg_left (le_max_right _ _) (abs_nonneg _)
        calc |(b - X ω) * Real.exp (lam * a) + (X ω - a) * Real.exp (lam * b)|
            ≤ |(b - X ω) * Real.exp (lam * a)| + |(X ω - a) * Real.exp (lam * b)| :=
              abs_add _ _
          _ = |b - X ω| * |Real.exp (lam * a)| + |X ω - a| * |Real.exp (lam * b)| := by
              rw [abs_mul, abs_mul]
          _ ≤ |b - X ω| * Real.exp (|lam| * max |a| |b|)
              + |X ω - a| * Real.exp (|lam| * max |a| |b|) :=
              add_le_add (mul_le_mul_of_nonneg_left hA (abs_nonneg _))
                (mul_le_mul_of_nonneg_left hB (abs_nonneg _))
          _ ≤ (b - a) * Real.exp (|lam| * max |a| |b|)
              + (b - a) * Real.exp (|lam| * max |a| |b|) :=
              add_le_add (mul_le_mul_of_nonneg_right h3 hE.le)
                (mul_le_mul_of_nonneg_right h4 hE.le)
          _ = 2 * (b - a) * Real.exp (|lam| * max |a| |b|) := by ring
      calc |((b - X ω) * Real.exp (lam * a) + (X ω - a) * Real.exp (lam * b)) / (b - a)|
          = |(b - X ω) * Real.exp (lam * a) + (X ω - a) * Real.exp (lam * b)| / |b - a| :=
            (abs_div _ _)
        _ = |(b - X ω) * Real.exp (lam * a) + (X ω - a) * Real.exp (lam * b)| / (b - a) := by
            rw [abs_of_pos hba]
        _ ≤ 2 * (b - a) * Real.exp (|lam| * max |a| |b|) / (b - a) :=
            (div_le_div_of_nonneg_right hsplit hba.le)
        _ = 2 * Real.exp (|lam| * max |a| |b|) := by
            field_simp
            ring
    -- the monotone step
    have hstep : ∫ ω, Real.exp (lam * X ω) ∂μ
        ≤ ∫ ω, ((b - X ω) * Real.exp (lam * a)
          + (X ω - a) * Real.exp (lam * b)) / (b - a) ∂μ :=
      integral_mono_of_nonneg (ae_of_all μ fun _ => (Real.exp_pos _).le) hub_int
        (ae_of_all μ fun ω => by refine le_trans (hsec ω) ?_; rw [hint2 ω])
    -- compute the affine integral
    have hi1 : ∫ ω, (b - X ω) ∂μ = b := by
      rw [integral_sub (integrable_const b) hXint, h_mean, integral_const]
      simp [measure_univ]
    have hi2 : ∫ ω, (X ω - a) ∂μ = -a := by
      rw [integral_sub hXint (integrable_const a), h_mean, integral_const]
      simp [measure_univ]
    have hc1 : Integrable (fun ω => (b - X ω) * Real.exp (lam * a)) μ :=
      ((integrable_const b).sub hXint).mul_const _
    have hc2 : Integrable (fun ω => (X ω - a) * Real.exp (lam * b)) μ :=
      (hXint.sub (integrable_const a)).mul_const _
    rw [integral_div, integral_add hc1 hc2, integral_mul_right, integral_mul_right,
      hi1, hi2] at hstep
    -- compare with phiComb and conclude
    have hmem : (-(a / (b - a))) ∈ Set.Icc 0 1 := by
      have ha0 : 0 ≤ -a := neg_nonneg.mpr hale
      constructor
      · rw [← neg_div (b - a) a]
        exact div_nonneg ha0 hba.le
      · rw [← neg_div (b - a) a]
        exact (div_le_one hba).mpr (by linarith)
    have hphi := phiComb_le_exp (-(a / (b - a))) hmem (lam * (b - a))
    have hcomp : (b * Real.exp (lam * a) + -a * Real.exp (lam * b)) / (b - a)
        = phiComb (-(a / (b - a))) (lam * (b - a)) := by
      have h1 : -(a / (b - a)) * (lam * (b - a)) = -(lam * a) := by
        field_simp
        ring
      have h2 : (1 - -(a / (b - a))) * (lam * (b - a)) = lam * b := by
        field_simp
        ring
      simp only [phiComb, h1, h2]
      field_simp
    calc ∫ ω, Real.exp (lam * X ω) ∂μ
        ≤ (b * Real.exp (lam * a) + -a * Real.exp (lam * b)) / (b - a) := hstep
      _ = phiComb (-(a / (b - a))) (lam * (b - a)) := hcomp
      _ ≤ Real.exp ((lam * (b - a)) ^ 2 / 8) := hphi
      _ = Real.exp (lam ^ 2 * (b - a) ^ 2 / 8) := by congr 1; ring


/-! ## The Chernoff assembly -/

/-- Measurability of finite products of measurable real functions. -/
theorem measurable_finset_prod' {ι : Type*} {s : Finset ι} {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact measurable_const
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact Measurable.mul (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Measurability of finite sums of measurable real functions. -/
theorem measurable_finset_sum' {ι : Type*} {s : Finset ι} {f : ι → Ω → ℝ}
    (hf : ∀ i ∈ s, Measurable (f i)) : Measurable (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact measurable_const
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact Measurable.add (hf i (Finset.mem_insert_self i s))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- Independence factorization of the integral of a finite product of
exponentials of independent real functions. -/
theorem integral_prod_exp_of_iIndepFun {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (lam : ℝ) (s : Finset (Fin n)) :
    ∫ ω, ∏ i ∈ s, Real.exp (lam * X i ω) ∂μ
      = ∏ i ∈ s, ∫ ω, Real.exp (lam * X i ω) ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Pi.one_apply, integral_const, measure_univ]
      simp
  | @insert i s hi ih =>
      have hexp : ∀ j, Measurable (fun ω => Real.exp (lam * X j ω)) :=
        fun j => Real.measurable_exp.comp ((h_meas j).const_mul lam)
      have hexpindep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ))
          (fun j ω => Real.exp (lam * X j ω)) μ :=
        h_indep.comp (fun _ => fun x => Real.exp (lam * x))
          (fun _ => Real.measurable_exp.comp (measurable_id.const_mul lam))
      have hind : IndepFun (∏ j ∈ s, fun ω => Real.exp (lam * X j ω))
          (fun ω => Real.exp (lam * X i ω)) μ :=
        iIndepFun.indepFun_finset_prod_of_not_mem hexpindep hexp hi
      have hfun : (∏ j ∈ s, fun ω => Real.exp (lam * X j ω))
          = (fun ω => ∏ j ∈ s, Real.exp (lam * X j ω)) :=
        funext fun ω => by simp only [Finset.prod_apply]
      have hind' : IndepFun (fun ω => ∏ j ∈ s, Real.exp (lam * X j ω))
          (fun ω => Real.exp (lam * X i ω)) μ := by
        rw [hfun] at hind
        exact hind
      have hm : Measurable (fun ω => ∏ j ∈ s, Real.exp (lam * X j ω)) := by
        rw [← hfun]
        exact measurable_finset_prod' fun j _ => hexp j
      have hsplit : ∫ ω, (∏ j ∈ s, Real.exp (lam * X j ω)) * Real.exp (lam * X i ω) ∂μ
          = (∫ ω, ∏ j ∈ s, Real.exp (lam * X j ω) ∂μ) * (∫ ω, Real.exp (lam * X i ω) ∂μ) :=
        hind'.integral_mul_of_nonneg
          (fun ω => Finset.prod_nonneg fun j _ => (Real.exp_pos _).le)
          (fun _ => (Real.exp_pos _).le)
          hm.aemeasurable (hexp i).aemeasurable
      have hEq : (fun ω => ∏ j ∈ insert i s, Real.exp (lam * X j ω))
          = (fun ω => (∏ j ∈ s, Real.exp (lam * X j ω)) * Real.exp (lam * X i ω)) := by
        funext ω
        rw [Finset.prod_insert hi, mul_comm]
      rw [hEq, hsplit, ih, Finset.prod_insert hi]
      ring

private theorem negAbs_le (a : ℝ) : -|a| ≤ a := by
  rcases le_or_lt 0 a with h | h
  · calc -|a| = -a := (abs_of_nonneg h).symm ▸ rfl
      _ ≤ 0 := neg_nonpos.mpr h
      _ ≤ a := h
  · rw [abs_of_neg h, neg_neg]

/-- The MGF of an independent bounded centered sum: under the interval
hypotheses, `E exp(λ ∑ X i) ≤ exp(λ² ∑(d i - c i)²/8)` for every `λ`. -/
theorem mgf_sum_le_of_iIndepFun {n : ℕ} {X : Fin n → Ω → ℝ} {c d : Fin n → ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, X i ω ∈ Set.Icc (c i) (d i))
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0) (lam : ℝ) :
    ∫ ω, Real.exp (lam * ∑ i, X i ω) ∂μ
      ≤ Real.exp (lam ^ 2 * (∑ i, (d i - c i) ^ 2) / 8) := by
  obtain ⟨⟨ω₀, -⟩⟩ := (nonempty_of_measure_ne_zero
    (by rw [measure_univ]; simp : (μ Set.univ) ≠ 0)).to_subtype
  have hper : ∀ i : Fin n, ∫ ω, Real.exp (lam * X i ω) ∂μ
      ≤ Real.exp (lam ^ 2 * (d i - c i) ^ 2 / 8) :=
    fun i => hoeffding_lemma_mgf ((h_bound i ω₀).1.trans (h_bound i ω₀).2) (h_meas i)
      (h_bound i) (h_mean i) lam
  have hexpsum : ∀ ω, Real.exp (lam * ∑ i, X i ω) = ∏ i, Real.exp (lam * X i ω) := by
    intro ω
    rw [← Real.exp_sum, Finset.mul_sum]
  calc ∫ ω, Real.exp (lam * ∑ i, X i ω) ∂μ
      = ∏ i, ∫ ω, Real.exp (lam * X i ω) ∂μ := by
        rw [integral_congr_ae (ae_of_all μ hexpsum)]
        exact integral_prod_exp_of_iIndepFun h_meas h_indep lam Finset.univ
    _ ≤ ∏ i, Real.exp (lam ^ 2 * (d i - c i) ^ 2 / 8) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
          (fun i _ => hper i)
    _ = Real.exp (lam ^ 2 * (∑ i, (d i - c i) ^ 2) / 8) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.sum_div, ← Finset.mul_sum]

omit [IsProbabilityMeasure μ] in
/-- Markov tail bound from an exponential-moment bound: if
`E exp(λY) ≤ B` with `λ ≥ 0`, then `μ {t ≤ Y} ≤ exp(-λt) B`. -/
theorem markov_tail_of_mgf {Y : Ω → ℝ} {B : ℝ}
    (hint : Integrable (fun ω => Real.exp (lam * Y ω)) μ)
    (hmgf : ∫ ω, Real.exp (lam * Y ω) ∂μ ≤ B) (hlam : 0 ≤ lam) (t : ℝ) :
    μ {ω | t ≤ Y ω} ≤ ENNReal.ofReal (Real.exp (-(lam * t)) * B) := by
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (f := fun ω => Real.exp (lam * Y ω)) (ae_of_all μ fun _ => (Real.exp_pos _).le) hint
    (Real.exp (lam * t))
  have hsub : {ω | t ≤ Y ω} ⊆ {ω | Real.exp (lam * t) ≤ Real.exp (lam * Y ω)} := by
    intro ω hω
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω hlam)
  have hmono : μ {ω | t ≤ Y ω} ≤ μ {ω | Real.exp (lam * t) ≤ Real.exp (lam * Y ω)} :=
    measure_mono hsub
  have hfin : μ {ω | Real.exp (lam * t) ≤ Real.exp (lam * Y ω)} < ∞ := by
    have h := hint.measure_norm_ge_lt_top (Real.exp_pos (lam * t))
    rw [show {x : Ω | Real.exp (lam * t) ≤ ‖(fun x => Real.exp (lam * Y x)) x‖}
        = {x : Ω | Real.exp (lam * t) ≤ Real.exp (lam * Y x)} from by
      ext x
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]] at h
    exact h
  rw [← ENNReal.ofReal_toReal (ne_of_lt hfin)] at hmono
  refine le_trans hmono ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : Real.exp (-(lam * t)) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpos : 0 ≤ Real.exp (-(lam * t)) := (Real.exp_pos _).le
  calc (μ {x | Real.exp (lam * t) ≤ Real.exp (lam * Y x)}).toReal
      = Real.exp (-(lam * t)) * (Real.exp (lam * t)
          * (μ {x | Real.exp (lam * t) ≤ Real.exp (lam * Y x)}).toReal) := by
        rw [← mul_assoc, h1, one_mul]
    _ ≤ Real.exp (-(lam * t)) * ∫ ω, Real.exp (lam * Y ω) ∂μ :=
        mul_le_mul_of_nonneg_left hmark hpos
    _ ≤ Real.exp (-(lam * t)) * B := mul_le_mul_of_nonneg_left hmgf hpos

/-- Hoeffding's inequality, interval form: under mutual independence, the
two-sided tail obeys `μ {|∑ X i| ≥ t} ≤ 2 exp(-2t² / ∑(d i - c i)²)`. -/
theorem hoeffding_inequality_interval {n : ℕ} {X : Fin n → Ω → ℝ} {c d : Fin n → ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, X i ω ∈ Set.Icc (c i) (d i))
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, X i ω| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / ∑ i, (d i - c i) ^ 2)) := by
  have hper : ∀ i, ∀ ω, |X i ω| ≤ |c i| ⊔ |d i| := by
    intro i ω
    obtain ⟨h1, h2⟩ := h_bound i ω
    exact abs_le.mpr ⟨le_trans (neg_le_neg le_sup_left) (le_trans (negAbs_le _) h1),
      le_trans h2 (le_trans (le_abs_self _) le_sup_right)⟩
  have hSmeas : Measurable (fun ω => ∑ i, X i ω) := by
    have h := measurable_finset_sum' (s := (Finset.univ : Finset (Fin n))) (fun i _ => h_meas i)
    rwa [show (∑ i ∈ Finset.univ, X i) = (fun ω => ∑ i, X i ω) from
      funext fun ω => by simp only [Finset.sum_apply]] at h
  have hS : ∀ ω, |∑ i, X i ω| ≤ ∑ i, (|c i| ⊔ |d i|) := by
    intro ω
    calc |∑ i, X i ω| ≤ ∑ i, |X i ω| := by
          simpa [Real.norm_eq_abs] using norm_sum_le (Finset.univ : Finset (Fin n))
            (fun i => X i ω)
      _ ≤ ∑ i, (|c i| ⊔ |d i|) := Finset.sum_le_sum fun i _ => hper i ω
  have hintexp : ∀ lam : ℝ, Integrable (fun ω => Real.exp (lam * ∑ i, X i ω)) μ := by
    intro lam
    refine integrable_of_bounded_measurable
      (a := Real.exp (|lam| * ∑ i, (|c i| ⊔ |d i|)))
      (Real.measurable_exp.comp
        ((hSmeas).const_mul lam)) (fun ω => ?_)
    have h1 : |Real.exp (lam * ∑ i, X i ω)| ≤ Real.exp (|lam| * ∑ i, (|c i| ⊔ |d i|)) := by
      rw [abs_of_nonneg (Real.exp_pos _).le]
      refine Real.exp_le_exp.mpr ?_
      calc lam * ∑ i, X i ω ≤ |lam * ∑ i, X i ω| := le_abs_self _
        _ = |lam| * |∑ i, X i ω| := abs_mul _ _
        _ ≤ |lam| * ∑ i, (|c i| ⊔ |d i|) := mul_le_mul_of_nonneg_left (hS ω) (abs_nonneg _)
    simpa [Real.norm_eq_abs] using h1
  by_cases hW : 0 < ∑ i, (d i - c i) ^ 2
  · set W := ∑ i, (d i - c i) ^ 2 with hWdef
    set lam := 4 * t / W with hlamdef
    have hlam : 0 ≤ lam := div_nonneg (mul_nonneg zero_le_four ht) hW.le
    have hmgfpos := mgf_sum_le_of_iIndepFun h_meas h_indep h_bound h_mean lam
    have hmgfneg := mgf_sum_le_of_iIndepFun h_meas h_indep h_bound h_mean (-lam)
    rw [neg_sq] at hmgfneg
    have hintneg : Integrable (fun ω => Real.exp (lam * (-∑ i, X i ω))) μ := by
      have h := hintexp (-lam)
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [mul_neg, neg_mul]
    have hmgfneg' : ∫ ω, Real.exp (lam * (-(∑ i, X i ω))) ∂μ
        ≤ Real.exp (lam ^ 2 * W / 8) := by
      have hEq : (fun ω => Real.exp (lam * (-(∑ i, X i ω))))
          = (fun ω => Real.exp (-lam * ∑ i, X i ω)) := by
        funext ω
        simp only [mul_neg, neg_mul]
      rw [hEq]
      exact hmgfneg
    have h1 := markov_tail_of_mgf (hintexp lam) hmgfpos hlam t
    have h2 := markov_tail_of_mgf hintneg hmgfneg' hlam t
    have hsub : {ω | |∑ i, X i ω| ≥ t} ⊆ {ω | t ≤ ∑ i, X i ω} ∪ {ω | t ≤ -(∑ i, X i ω)} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      rcases le_or_lt 0 (∑ i, X i ω) with h | h
      · exact Or.inl (by rwa [abs_of_nonneg h] at hω)
      · exact Or.inr (by rwa [abs_of_neg h] at hω)
    have hexpcomb : Real.exp (-(lam * t)) * Real.exp (lam ^ 2 * W / 8)
        = Real.exp (-(lam * t) + lam ^ 2 * W / 8) := (Real.exp_add _ _).symm
    have hexpo : -(lam * t) + lam ^ 2 * W / 8 = -2 * t ^ 2 / W := by
      rw [hlamdef]
      field_simp
      ring
    calc μ {ω | |∑ i, X i ω| ≥ t}
        ≤ μ {ω | t ≤ ∑ i, X i ω} + μ {ω | t ≤ -(∑ i, X i ω)} :=
          le_trans (measure_mono hsub) (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (Real.exp (-(lam * t)) * Real.exp (lam ^ 2 * W / 8))
          + ENNReal.ofReal (Real.exp (-(lam * t)) * Real.exp (lam ^ 2 * W / 8)) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / W)) := by
          have hnn : 0 ≤ Real.exp (-2 * t ^ 2 / W) := (Real.exp_pos _).le
          rw [hexpcomb, hexpo, ← ENNReal.ofReal_add hnn hnn, ← two_mul]
      _ = ENNReal.ofReal (2 * Real.exp (-2 * t ^ 2 / ∑ i, (d i - c i) ^ 2)) := by
          rw [hWdef]
  · -- W = 0: every interval is degenerate, mean zero forces X ≡ 0
    have hnn : 0 ≤ ∑ i, (d i - c i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    have hW0 : ∑ i, (d i - c i) ^ 2 = 0 := by
      rcases lt_or_eq_of_le hnn with h | h
      · exact absurd h hW
      · exact h.symm
    have hcd : ∀ i, d i = c i := by
      intro i
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg (d i - c i))).mp hW0 i (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hmem)
    obtain ⟨⟨ω₀, -⟩⟩ := (nonempty_of_measure_ne_zero
      (by rw [measure_univ]; simp : (μ Set.univ) ≠ 0)).to_subtype
    have hc0 : ∀ i, c i = 0 := by
      intro i
      have hXc : ∀ ω, X i ω = c i := fun ω =>
        le_antisymm ((h_bound i ω).2.trans (by rw [hcd i])) (h_bound i ω).1
      have hint : ∫ ω, X i ω ∂μ = c i := by
        rw [integral_congr_ae (ae_of_all μ fun ω => by rw [hXc ω]), integral_const]
        simp [measure_univ]
      rw [h_mean i] at hint
      linarith
    have hX0 : ∀ i, ∀ ω, X i ω = 0 := by
      intro i ω
      have h1 : X i ω = c i :=
        le_antisymm ((h_bound i ω).2.trans (le_of_eq (hcd i))) (h_bound i ω).1
      rw [h1, hc0 i]
    rcases ht.eq_or_lt with rfl | ht'
    · have hsum0 : ∀ ω, ∑ i, X i ω = 0 := fun ω =>
        Finset.sum_eq_zero fun i _ => hX0 i ω
      have hval : -2 * (0:ℝ) ^ 2 / ∑ i, (d i - c i) ^ 2 = 0 := by
        rw [hW0]
        norm_num
      rw [hval, Real.exp_zero]
      have hfull : {ω : Ω | |∑ i, X i ω| ≥ 0} = Set.univ := by
        ext ω
        simp
      rw [hfull, measure_univ, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by norm_num : (1:ℝ) ≤ 2 * 1)
    · have hempty : {ω | |∑ i, X i ω| ≥ t} = ∅ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, not_false_iff]
        have hsum0 : ∑ i, X i ω = 0 := Finset.sum_eq_zero fun i _ => hX0 i ω
        rw [hsum0]
        simp only [abs_zero]
        exact ⟨fun h => absurd h (not_le.mpr ht'), False.elim⟩
      rw [hempty, measure_empty]
      exact zero_le _


/-- **Retired from axiom to theorem.** Hoeffding's inequality: a sum of
independent, centered variables with `|X i ω| ≤ a i` satisfies the
two-sided tail bound `P {|∑ X i| ≥ t} ≤ 2 exp (-t² / (2 ∑ a i²))`.

Proof: the interval engine at `[-a i, a i]`, where the range `2 a i`
specializes the exponent `-2t²/∑(2a i)²` to `-t²/(2∑a i²)`. -/
theorem hoeffding_inequality {n : ℕ} {X : Fin n → Ω → ℝ} {a : Fin n → ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω| ≤ a i)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, X i ω| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * ∑ i, (a i) ^ 2))) := by
  have h := hoeffding_inequality_interval (c := fun i => -a i) (d := fun i => a i) h_meas h_indep
    (fun i ω => abs_le.mp (h_bound i ω)) h_mean t ht
  have hsum : ∑ i, (a i - (-a i)) ^ 2 = 4 * ∑ i, (a i) ^ 2 := by
    have h1 : ∑ i, (a i - (-a i)) ^ 2 = ∑ i, 4 * (a i) ^ 2 :=
      Finset.sum_congr rfl fun i _ => by ring
    rw [h1, Finset.mul_sum]
  rw [hsum] at h
  refine h.trans_eq ?_
  have hkey : ∀ V : ℝ, -2 * t ^ 2 / (4 * V) = -t ^ 2 / (2 * V) := by
    intro V
    rcases eq_or_ne V 0 with rfl | hV
    · simp
    · field_simp
      ring
  rw [hkey]


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

/-- **Retired from axiom to theorem.** Hoeffding's inequality for empirical
averages of `[0, 1]`-valued independent variables:
`P {|mean - E mean| ≥ t} ≤ 2 exp (-2 n t²)`.

Proof: the interval engine at the centered variables `X i - E X i`, whose
intervals `[-m i, 1 - m i]` have range `1` regardless of `m i`. -/
theorem hoeffding_empirical {n : ℕ} {X : Fin n → Ω → ℝ}
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |(1 / (n : ℝ)) * ∑ i, X i ω
        - (1 / (n : ℝ)) * ∑ i, ∫ ω', X i ω' ∂μ| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * t ^ 2)) := by
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · -- n = 0: junk corner; the bound is `2 exp 0 = 2 >= 1 >= any measure`
    have hz : (-2 : ℝ) * (n : ℝ) * t ^ 2 = 0 := by
      rw [h0]
      simp
    have hle : (1 : ℝ) ≤ 2 * Real.exp (-2 * (n : ℝ) * t ^ 2) := by
      rw [hz]
      norm_num
    calc μ {ω | |(1 / (n : ℝ)) * ∑ i, X i ω
          - (1 / (n : ℝ)) * ∑ i, ∫ ω', X i ω' ∂μ| ≥ t}
        ≤ (1 : ℝ≥0∞) := by
          refine le_trans (measure_mono (Set.subset_univ _)) ?_
          rw [measure_univ]
      _ ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * t ^ 2)) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal hle
  · -- n > 0: center and apply the interval engine
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast h0
    have hXint : ∀ i, Integrable (X i) μ := fun i =>
      integrable_of_bounded_measurable (h_meas i) (fun ω =>
        abs_le.mpr ⟨show (-(1:ℝ)) ≤ X i ω by linarith [(h_bound i ω).1],
          show X i ω ≤ 1 by linarith [(h_bound i ω).2]⟩)
    set m : Fin n → ℝ := fun i => ∫ ω', X i ω' ∂μ with hmdef
    have hm_mem : ∀ i, m i ∈ Set.Icc (0:ℝ) 1 := by
      intro i
      refine Set.mem_Icc.mpr ⟨integral_nonneg (fun ω' => (h_bound i ω').1), ?_⟩
      have h1 : ∫ ω', (1 - X i ω') ∂μ = 1 - m i := by
        rw [integral_sub (integrable_const 1) (hXint i), integral_const]
        simp [measure_univ]
      have h2 : 0 ≤ ∫ ω', (1 - X i ω') ∂μ :=
        integral_nonneg (fun ω' => show (0:ℝ) ≤ 1 - X i ω' by
          linarith [(h_bound i ω').2])
      linarith
    have hYmeas : ∀ i, Measurable (fun ω => X i ω - m i) :=
      fun i => (h_meas i).sub measurable_const
    have hYmean : ∀ i, ∫ ω, (X i ω - m i) ∂μ = 0 := by
      intro i
      rw [integral_sub (hXint i) (integrable_const _), hmdef, integral_const]
      simp [measure_univ]
    have hYindep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ))
        (fun i ω => X i ω - m i) μ :=
      h_indep.comp (fun j => fun x => x - m j) (fun _ => measurable_id.sub measurable_const)
    have hYbound : ∀ i ω, (X i ω - m i) ∈ Set.Icc (-(m i)) (1 - m i) := by
      intro i ω
      exact Set.mem_Icc.mpr ⟨show -(m i) ≤ X i ω - m i by
          linarith [(h_bound i ω).1, (hm_mem i).1],
        show X i ω - m i ≤ 1 - m i by linarith [(h_bound i ω).2, (hm_mem i).2]⟩
    have heng := hoeffding_inequality_interval (c := fun i => -(m i)) (d := fun i => 1 - m i)
      hYmeas hYindep hYbound hYmean ((n : ℝ) * t) (mul_nonneg hnpos.le ht)
    have hrange : ∑ i, ((1 - m i) - (-(m i))) ^ 2 = (n : ℝ) := by
      have h1 : ∀ i : Fin n, ((1 - m i) - (-(m i))) ^ 2 = 1 := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => h1 i)]
      simp
    rw [hrange] at heng
    have hsumeq : ∀ ω, ∑ i, (X i ω - m i)
        = (∑ i, X i ω) - (∑ i, ∫ ω', X i ω' ∂μ) := by
      intro ω
      simp only [Finset.sum_sub_distrib]
    have hev : {ω | |(1 / (n : ℝ)) * ∑ i, X i ω
        - (1 / (n : ℝ)) * ∑ i, ∫ ω', X i ω' ∂μ| ≥ t}
        = {ω | |∑ i, (X i ω - m i)| ≥ (n : ℝ) * t} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      have hsplit : ((1 / (n : ℝ)) * ∑ i, X i ω
          - (1 / (n : ℝ)) * ∑ i, ∫ ω', X i ω' ∂μ)
          = (∑ i, (X i ω - m i)) / (n : ℝ) := by
        rw [← mul_sub, ← hsumeq ω]
        field_simp
      rw [hsplit]
      simp only [abs_div, abs_of_pos hnpos]
      constructor
      · intro h
        have h2 := (le_div_iff₀ hnpos).mp h
        rw [mul_comm] at h2
        exact h2
      · intro h
        rw [mul_comm] at h
        exact (le_div_iff₀ hnpos).mpr h
    rw [hev]
    refine heng.trans_eq ?_
    have hkey : -2 * ((n : ℝ) * t) ^ 2 / (n : ℝ) = -2 * (n : ℝ) * t ^ 2 := by
      field_simp
      ring
    rw [hkey]
end Scaffold.Mathlib.Probability.Concentration.Scalar
