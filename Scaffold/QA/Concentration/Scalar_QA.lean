/-
  Scalar_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Probability.Concentration.Scalar.*`:
  the subgaussian norm definition, the *proved* subgaussian tail bound
  (retired from axiom 2026-08-22 — its interfaces are now exercised as
  hard crust, including the refutation of the old axiom shape), the
  admitted Hoeffding/Bernstein tail bounds, and the admitted Hoeffding
  lemma. Each tail-bound lemma is instantiated at explicit fixtures, so
  the hypothesis interface (integrability, moment bounds, measurability,
  independence of constants, centeredness) is exercised constructively;
  the event side is then evaluated exactly.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not prove
  the remaining axioms; it checks their interfaces and degenerate cases.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory
open scoped ENNReal

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

/-- The constant-zero variable's MGF is integrable with integral exactly
`1` under any probability measure: the proved tail bound's two new
hypotheses, discharged constructively. -/
theorem subgaussian_tail_bound_zero_hypotheses_QA :
    Integrable (fun _ : Ω => Real.exp ((0 : ℝ) ^ 2 / (1 : ℝ) ^ 2)) μ
      ∧ ∫ _ : Ω, Real.exp ((0 : ℝ) ^ 2 / (1 : ℝ) ^ 2) ∂μ = 1 := by
  have hone : (fun _ : Ω => Real.exp ((0 : ℝ) ^ 2 / (1 : ℝ) ^ 2)) = fun _ => (1 : ℝ) := by
    funext _ω; simp
  refine ⟨?_, ?_⟩
  · rw [hone]; exact integrable_const _
  · rw [hone, integral_const]
    simp

/-- The proved tail bound instantiated at the constant-zero variable
with `K = 1`: both moment hypotheses are supplied constructively (see
`subgaussian_tail_bound_zero_hypotheses_QA`), and the bound reads
`μ {|0| ≥ t} ≤ 2 * exp (-(t ^ 2) / 2)`. -/
theorem subgaussian_tail_bound_zero_QA (t : ℝ) (ht : 0 < t) :
    μ {_ω : Ω | |(0 : ℝ)| ≥ t} ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := by
  obtain ⟨hint, hmom⟩ := subgaussian_tail_bound_zero_hypotheses_QA (μ := μ)
  have hK : (0 : ℝ) < 1 := by norm_num
  have hax := subgaussian_tail_bound (K := 1) hK hint
    (by rw [hmom]; norm_num) t ht.le
  rwa [show (2 * (1 : ℝ) ^ 2) = 2 by simp] at hax

/-!
### A genuine nonzero instance of the proved tail bound
-/

/-- The constant-one variable on the Dirac mass at `0` is `2`-subgaussian
in the proved theorem's sense: the MGF integrand is the constant
`exp (1 / 4)`, integrable under the (probability) Dirac measure, with
integral `exp (1 / 4) ≤ 2` via the pinned lower bound
`Real.log_two_gt_d9` on `log 2`. This is a *non-vacuous* use: the moment
hypothesis genuinely binds (`exp (1/4) > 1`), unlike the zero fixture. -/
theorem subgaussian_tail_bound_instance_hypotheses_QA :
    Integrable (fun _ : ℝ => Real.exp ((1 : ℝ) ^ 2 / (2 : ℝ) ^ 2)) (Measure.dirac (0 : ℝ))
      ∧ ∫ _ : ℝ, Real.exp ((1 : ℝ) ^ 2 / (2 : ℝ) ^ 2) ∂Measure.dirac (0 : ℝ)
        = Real.exp ((1 : ℝ) / 4) := by
  refine ⟨integrable_const _, ?_⟩
  rw [integral_dirac]
  norm_num

/-- `exp (1 / 4) ≤ 2`, the instance's moment bound: `1/4 < log 2` through
the pinned decimal lower bound `0.6931471803 < log 2`. -/
theorem subgaussian_exp_quarter_le_two_QA : Real.exp ((1 : ℝ) / 4) ≤ 2 := by
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  refine Real.exp_le_exp.2 ?_
  calc (1 : ℝ) / 4 ≤ 0.6931471803 := by norm_num
    _ ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9

/-- The proved tail bound instantiated at the constant-one variable with
`K = 2`, `t = 1`: the event is everything (measure exactly `1` under the
Dirac probability measure), so the bound `1 ≤ 2 * exp (-(1 / 8))` is
*attained with a nonzero left side* — not a vacuous or degenerate
witness. The numeric comparison holds since `1 / 8 < log 2`. -/
theorem subgaussian_tail_bound_instance_QA :
    (Measure.dirac (0 : ℝ)) {_ω : ℝ | |(1 : ℝ)| ≥ 1}
      ≤ ENNReal.ofReal (2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * (2 : ℝ) ^ 2))) := by
  obtain ⟨hint, hmom⟩ := subgaussian_tail_bound_instance_hypotheses_QA
  have hK : (0 : ℝ) < 2 := by norm_num
  exact subgaussian_tail_bound (K := 2) hK hint
    (by rw [hmom]; exact subgaussian_exp_quarter_le_two_QA) 1 (by norm_num)

/-- The instance's event side pinned raw: the Dirac probability measure
of the everything-event is exactly `1`. -/
theorem subgaussian_tail_bound_instance_event_QA :
    (Measure.dirac (0 : ℝ)) {_ω : ℝ | |(1 : ℝ)| ≥ 1} = 1 := by
  have hu : {_ω : ℝ | |(1 : ℝ)| ≥ 1} = Set.univ :=
    Set.eq_univ_of_forall fun _ => by simp
  rw [hu, measure_univ]

/-- The instance's bound side pinned raw: `1 ≤ 2 * exp (-(1 / 8))`, so
the instantiation above carries genuine content on both sides (the left
side is `1`, not `0`; the right side is strictly between `1` and `2`). -/
theorem subgaussian_tail_bound_instance_bound_QA :
    (1 : ℝ) ≤ 2 * Real.exp (-((1 : ℝ) / 8)) := by
  rw [Real.exp_neg, mul_comm (2 : ℝ) (Real.exp ((1 : ℝ) / 8))⁻¹, inv_mul_eq_div,
    one_le_div (Real.exp_pos ((1 : ℝ) / 8))]
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  refine Real.exp_le_exp.2 ?_
  calc (1 : ℝ) / 8 ≤ 0.6931471803 := by norm_num
    _ ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9

/-!
## The retired axiom shape, refuted
-/

/-- The refutation fixture: a finite measure of total mass `3` (three
copies of the Dirac mass). Its total mass exceeds `2`, so no `K > 0`
can satisfy the moment condition `∫ exp (X² / K²) ∂μ ≤ 2` — for the
constant-zero variable the integrand is the constant `1` and the
integral is exactly `3`. -/
noncomputable def refutationMeasure : Measure ℝ := (3 : ℝ≥0∞) • Measure.dirac (0 : ℝ)

theorem refutationMeasure_univ_QA : refutationMeasure Set.univ = 3 := by
  simp [refutationMeasure]

theorem refutationMeasure_integral_one_QA :
    ∫ _ : ℝ, (1 : ℝ) ∂refutationMeasure = 3 := by
  rw [integral_const, refutationMeasure_univ_QA]
  norm_num

/-- The junk mechanism, exhibited: under `refutationMeasure` the defining
set of `subgaussianNorm` (at the constant-zero variable) is *empty* —
every candidate integral is `3 > 2` — so `Real.sInf_empty` makes the
norm the junk value `0`, and the old norm-hypothesis held vacuously. -/
theorem old_subgaussian_tail_bound_norm_junk_QA :
    subgaussianNorm (fun _ => (0 : ℝ)) refutationMeasure = 0 := by
  have hS : {K : ℝ | 0 < K ∧ ∫ ω : ℝ, Real.exp ((0 : ℝ) ^ 2 / K ^ 2) ∂refutationMeasure ≤ 2}
      = ∅ := by
    refine Set.eq_empty_iff_forall_not_mem.mpr fun K hK => ?_
    obtain ⟨-, hint⟩ := hK
    have hone : (fun ω : ℝ => Real.exp ((0 : ℝ) ^ 2 / K ^ 2)) = fun _ : ℝ => (1 : ℝ) := by
      funext ω; simp
    rw [hone, refutationMeasure_integral_one_QA] at hint
    norm_num at hint
  show (sInf _) = 0
  rw [hS, Real.sInf_empty]

/-- The old axiom's hypotheses were satisfiable at the fixture:
`subgaussianNorm ≤ 1` holds — vacuously, through the junk value. -/
theorem old_subgaussian_tail_bound_hypotheses_QA :
    subgaussianNorm (fun _ => (0 : ℝ)) refutationMeasure ≤ 1 := by
  rw [old_subgaussian_tail_bound_norm_junk_QA]; norm_num

/-- The old axiom shape, refuted with its hypotheses proved satisfiable:
the retired statement — `hK : 0 ≤ K`, `h_sub : subgaussianNorm X μ ≤ K`,
conclusion `μ {|X| ≥ t} ≤ 2 * exp (-t² / (2K²))` — instantiated at the
constant-zero variable, `K = 1`, `t = 0` on `refutationMeasure` reads
`3 ≤ 2` on the nose (the event is everything; the bound evaluates to
`2 * exp 0 = 2`). This is the same falsification pattern as the Woodbury
and old-Cheeger-lower-bound repairs. -/
theorem old_subgaussian_tail_bound_refuted_QA
    (h : refutationMeasure {ω : ℝ | |(fun _ => (0 : ℝ)) ω| ≥ 0}
        ≤ ENNReal.ofReal (2 * Real.exp (-((0 : ℝ) ^ 2) / (2 * (1 : ℝ) ^ 2)))) : False := by
  have hL : refutationMeasure {ω : ℝ | |(fun _ => (0 : ℝ)) ω| ≥ 0} = 3 := by
    have hu : {ω : ℝ | |(fun _ => (0 : ℝ)) ω| ≥ 0} = Set.univ :=
      Set.eq_univ_of_forall fun _ => by simp
    rw [hu]
    exact refutationMeasure_univ_QA
  have hR : ENNReal.ofReal (2 * Real.exp (-((0 : ℝ) ^ 2) / (2 * (1 : ℝ) ^ 2))) = 2 := by
    norm_num
  rw [hL, hR] at h
  norm_num at h

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
