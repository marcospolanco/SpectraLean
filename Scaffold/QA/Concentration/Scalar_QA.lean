/-
  Scalar_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Probability.Concentration.Scalar.*`:
  the subgaussian norm definition, the admitted Hoeffding/Bernstein tail
  bounds, and the admitted Hoeffding lemma. Each tail-bound lemma is
  instantiated at a degenerate constant-zero family, so the hypothesis
  interface (measurability, independence of constants, centeredness) is
  exercised constructively; the event side is then evaluated exactly.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not prove
  the axioms; it checks their interfaces and degenerate cases.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein

open MeasureTheory ProbabilityTheory

namespace Scaffold.Mathlib.Probability.Concentration.Scalar.QA

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-!
## Independence of constants
-/

/-- Constants are independent of anything under a probability measure:
the σ-algebra a constant function generates is trivial. This exercises
Mathlib's `IndepFun` at the boundary the axioms consume. -/
theorem indepFun_const_left_QA (a : ℝ) (Y : Ω → ℝ) :
    IndepFun (fun _ => a) Y μ := by
  rw [IndepFun_iff_Indep, MeasurableSpace.comap_const]
  exact indep_bot_left _

/-!
## Subgaussian interface
-/

/-- The constant-zero variable has subgaussian norm exactly `0`. This is
a cross-axiom coherence check: `hoeffding_lemma` (admitted) gives
`≤ 0`, and the real definition `subgaussianNorm` gives `≥ 0`. -/
theorem subgaussian_norm_zero_QA : subgaussianNorm (fun _ => (0 : ℝ)) μ = 0 :=
  le_antisymm
    (hoeffding_lemma (le_refl 0) (fun ω => by simp) (by simp))
    (subgaussianNorm_nonneg _ _)

/-- The admitted tail bound instantiated at the constant-zero variable
with `K = 1`: the subgaussian-norm hypothesis is supplied through the
admitted `hoeffding_lemma`, exercising both axioms coherently. -/
theorem subgaussian_tail_bound_zero_QA (t : ℝ) (ht : 0 < t) :
    μ {ω : Ω | |(0 : ℝ)| ≥ t} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := by
  have hK : subgaussianNorm (fun _ => (0 : ℝ)) μ ≤ 1 :=
    le_trans (hoeffding_lemma (le_refl 0) (fun ω => by simp) (by simp))
      (by norm_num)
  have hax := subgaussian_tail_bound (by norm_num) hK t ht.le
  rwa [show (2 * (1 : ℝ) ^ 2) = 2 by simp] at hax

/-!
## Hoeffding interface
-/

/-- Hoeffding's inequality instantiated at the constant-zero family with
uniform bound `a = 1`: every hypothesis is discharged constructively and
the variance statistic specializes to `∑ 1² = n`. -/
theorem hoeffding_inequality_zero_QA {n : ℕ} (t : ℝ) (ht : 0 < t) :
    μ {ω : Ω | |∑ i : Fin n, (0 : ℝ)| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * (n : ℝ)))) := by
  have hax := hoeffding_inequality (n := n) (X := fun _ _ => (0 : ℝ)) (a := fun _ => 1)
    (fun i => measurable_const)
    (fun i j _ => indepFun_const_left_QA (Ω := Ω) (μ := μ) 0 (fun _ => (0 : ℝ)))
    (fun i ω => by simp) (fun i => by simp) t ht.le
  rwa [show ∑ i : Fin n, (1 : ℝ) ^ 2 = (n : ℝ) by simp] at hax

/-- The Hoeffding zero-family event is empty, so its measure is exactly
`0`: the degenerate case of the admitted bound is tight at zero. -/
theorem hoeffding_zero_event_QA {n : ℕ} {t : ℝ} (ht : 0 < t) :
    μ {ω : Ω | |∑ i : Fin n, (0 : ℝ)| ≥ t} = 0 := by
  have hempty : {ω : Ω | |∑ i : Fin n, (0 : ℝ)| ≥ t} = ∅ := by
    ext ω
    simp only [Finset.sum_const_zero, abs_zero]
    simp [ht.not_le]
  rw [hempty, measure_empty]

/-!
## Bernstein interface
-/

/-- Bernstein's inequality instantiated at the constant-zero family with
bound `a = 1`: the centered variance statistic specializes to `0`. -/
theorem bernstein_inequality_zero_QA {n : ℕ} (t : ℝ) (ht : 0 < t) :
    μ {ω : Ω | |∑ i : Fin n, ((0 : ℝ) - ∫ ω' : Ω, (0 : ℝ) ∂μ)| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / ((2 * 1 * t) / 3))) := by
  have hax := bernstein_inequality (n := n) (X := fun _ _ => (0 : ℝ)) (a := 1) (by norm_num)
    (fun i => measurable_const)
    (fun i j _ => indepFun_const_left_QA (Ω := Ω) (μ := μ) 0 (fun _ => (0 : ℝ)))
    (fun i ω => by simp) t ht.le
  have hsum : ∑ i : Fin n, ∫ ω : Ω,
      ((0 : ℝ) - ∫ ω' : Ω, (0 : ℝ) ∂μ) ^ 2 ∂μ = 0 := by
    simp
  rwa [hsum, mul_zero, zero_add] at hax

end Scaffold.Mathlib.Probability.Concentration.Scalar.QA
