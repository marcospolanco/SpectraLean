/-
  Scalar_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Probability.Concentration.Scalar.*`:
  the subgaussian norm definition, the *proved* subgaussian tail bound
  (retired from axiom 2026-08-22 — its interfaces are now exercised as
  hard crust, including the refutation of the old axiom shape), the
  admitted Hoeffding/Bernstein tail bounds, and the admitted (repaired
  2026-08-28) Hoeffding lemma. Each tail-bound lemma is instantiated at
  explicit fixtures, so the hypothesis interface (integrability, moment
  bounds, measurability, independence of constants, centeredness) is
  exercised constructively; the event side is then evaluated exactly.

  The 2026-08-28 integrability audit
  (`proposals/audit-scalar-concentration-integrability-hazard.md`) added
  the refutation family for the pre-repair `hoeffding_lemma` (two
  materially false shapes, each refuted with genuinely-satisfied
  hypotheses) plus the integrability safety lemmas' first consumers.

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
`≤ √6 * 0 = 0`, and the real definition `subgaussianNorm` gives `≥ 0`. -/
theorem subgaussian_norm_zero_QA : subgaussianNorm (fun _ => (0 : ℝ)) μ = 0 :=
  le_antisymm
    (by simpa using hoeffding_lemma (le_refl 0) (fun ω => by simp) (by simp))
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
## The `hoeffding_lemma` repair (2026-08-28), refuted and re-instantiated

The integrability audit
(`proposals/audit-scalar-concentration-integrability-hazard.md`) found
the pre-repair axiom — `subgaussianNorm X μ ≤ a` with no measure
constraint — materially false in two independent ways. Both refutation
witnesses are proved here with every hypothesis of the old axiom
discharged genuinely (boundedness and a *real* mean-zero integral, not
a junk one); each then refutes the old conclusion on the nose. The
repaired axiom (probability measure + `√6 * a`) is re-instantiated at
the same fixture that kills the old constant.
-/

/-- The first refutation fixture: the fair-coin probability measure on
`Bool` (total mass exactly `1`). -/
noncomputable def rademacherMeasure : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)

theorem rademacherMeasure_univ_QA : rademacherMeasure Set.univ = 1 := by
  have h1 : (Measure.dirac true) Set.univ = 1 := measure_univ
  have h2 : (Measure.dirac false) Set.univ = 1 := measure_univ
  show ((1 / 2 : ℝ≥0∞) • (Measure.dirac true + Measure.dirac false)) Set.univ = 1
  rw [Measure.smul_apply, Measure.add_apply, h1, h2]
  norm_num
  rw [mul_comm, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]

instance : IsProbabilityMeasure rademacherMeasure :=
  ⟨rademacherMeasure_univ_QA⟩

instance : IsFiniteMeasure rademacherMeasure :=
  ⟨by rw [measure_univ]; exact ENNReal.one_lt_top⟩

/-- The Rademacher variable on `Bool`: `+1` at `true`, `-1` at `false`. -/
def rademacherX : Bool → ℝ := fun b => if b then 1 else -1

theorem rademacherX_sq_QA (b : Bool) : rademacherX b ^ 2 = 1 := by
  cases b <;> simp [rademacherX]

theorem rademacherX_abs_QA (b : Bool) : |rademacherX b| = 1 := by
  cases b <;> simp [rademacherX]

/-- Every function out of `Bool` is measurable (the σ-algebra is
discrete), supplying the `h_meas`-shaped clauses at this fixture. -/
theorem rademacherX_measurable_QA : Measurable rademacherX :=
  fun _s _ => Set.Countable.measurableSet (Set.to_countable _)

/-- The mean is genuinely zero — the bounded variable is integrable
through the audit's safety lemma `integrable_of_bounded_measurable`
(its first QA consumer), so `h_mean` is an honest constraint here, not
a junk-integral one. -/
theorem rademacherMeasure_mean_QA : ∫ b : Bool, rademacherX b ∂rademacherMeasure = 0 := by
  have hintd : ∀ b : Bool, Integrable rademacherX (Measure.dirac b) :=
    fun b => integrable_of_bounded_measurable rademacherX_measurable_QA
      (fun ω => by rw [rademacherX_abs_QA ω])
  rw [rademacherMeasure, integral_smul_measure,
    integral_add_measure (hintd true) (hintd false), integral_dirac, integral_dirac]
  simp [rademacherX]

/-- The safety lemma `integrable_of_bounded_measurable` instantiated at
the fixture (exercising the `h_meas` + `h_bound` + probability-measure
interface that the audit records as ruling out the junk-integral
mechanism for `hoeffding_inequality`). -/
theorem integrable_rademacher_QA : Integrable rademacherX rademacherMeasure :=
  integrable_of_bounded_measurable rademacherX_measurable_QA
    (fun b => by rw [rademacherX_abs_QA b])

/-- The centered-square safety lemma `integrable_sq_sub_mean` for the
Bernstein axioms, instantiated at the same fixture. -/
theorem integrable_sq_sub_mean_rademacher_QA :
    Integrable (fun ω => (rademacherX ω - ∫ ω', rademacherX ω' ∂rademacherMeasure) ^ 2)
      rademacherMeasure :=
  integrable_sq_sub_mean rademacherX_measurable_QA
    (fun b => by rw [rademacherX_abs_QA b])

theorem rademacherMeasure_integral_exp_QA (K : ℝ) :
    ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂rademacherMeasure
      = Real.exp (1 / K ^ 2) := by
  have hcongr : (fun b : Bool => Real.exp (rademacherX b ^ 2 / K ^ 2))
      = fun _ : Bool => Real.exp (1 / K ^ 2) := by
    funext b; rw [rademacherX_sq_QA b]
  rw [hcongr, integral_const, rademacherMeasure_univ_QA]
  norm_num

/-- The arithmetic core of the constant-defect refutation: for `K ≤ 6/5`
the moment condition fails, since `log 2 < 25/36 ≤ 1/K²` gives
`exp (1/K²) > 2`. -/
theorem exp_gt_two_rademacher_QA {K : ℝ} (hKpos : 0 < K) (hK : K ≤ 6 / 5) :
    2 < Real.exp (1 / K ^ 2) := by
  have hK2 : K ^ 2 ≤ (6 / 5 : ℝ) ^ 2 := sq_le_sq' (by linarith) hK
  have hinv2 : 25 / 36 ≤ 1 / K ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 36) (by positivity)]
    nlinarith [hK2]
  have h2536 : Real.log 2 < 25 / 36 :=
    lt_of_lt_of_le Real.log_two_lt_d9 (by norm_num)
  have hlt : Real.log 2 < 1 / K ^ 2 := lt_of_lt_of_le h2536 hinv2
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact Real.exp_lt_exp.2 hlt

/-- Every member of the defining set at the Rademacher fixture is at
least `6/5`, so the subgaussian norm is at least `6/5 > 1 = a`. -/
theorem rademacher_norm_ge_QA : 6 / 5 ≤ subgaussianNorm rademacherX rademacherMeasure := by
  have hlower : ∀ K : ℝ, K ∈ {K : ℝ | 0 < K
      ∧ ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂rademacherMeasure ≤ 2}
      → 6 / 5 ≤ K := by
    intro K hK
    by_contra hcon
    obtain ⟨hK1, hK2⟩ := hK
    rw [rademacherMeasure_integral_exp_QA K] at hK2
    exact absurd hK2
      (not_le.2 (exp_gt_two_rademacher_QA hK1 (le_of_lt (lt_of_not_le hcon))))
  have hmem : (2 : ℝ) ∈ {K : ℝ | 0 < K
      ∧ ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂rademacherMeasure ≤ 2} := by
    refine ⟨by norm_num, ?_⟩
    rw [rademacherMeasure_integral_exp_QA, show ((2 : ℝ) ^ 2) = 4 from by norm_num]
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_le_exp.2
      (le_trans (by norm_num : (1 : ℝ) / 4 ≤ 0.6931471803) (le_of_lt Real.log_two_gt_d9))
  simp only [subgaussianNorm]
  exact le_csInf ⟨2, hmem⟩ hlower

/-- The pre-repair axiom's **constant defect**, refuted: every hypothesis
of the old `hoeffding_lemma` (`ha`, `h_bound`, `h_mean`) holds genuinely
at the fair-coin Rademacher fixture with `a = 1`, yet the old conclusion
`subgaussianNorm ≤ 1` fails — the norm is at least `6/5`. No junk
mechanism is involved; the constant `1` is wrong even on well-behaved
probability spaces. -/
theorem old_hoeffding_lemma_refuted_constant_QA
    (h : subgaussianNorm rademacherX rademacherMeasure ≤ 1) : False :=
  absurd (le_trans rademacher_norm_ge_QA h) (by norm_num : ¬ ((6 / 5 : ℝ) ≤ 1))

/-- The second refutation fixture: the mass-`19/10` rescaling of the
fair-coin measure. Not a probability measure — exactly the point. -/
noncomputable def scaledRademacherMeasure : Measure Bool :=
  (19 / 10 : ℝ≥0∞) • rademacherMeasure

theorem scaledRademacherMeasure_univ_QA :
    scaledRademacherMeasure Set.univ = 19 / 10 := by
  show ((19 / 10 : ℝ≥0∞) • rademacherMeasure) Set.univ = 19 / 10
  rw [Measure.smul_apply, rademacherMeasure_univ_QA]
  norm_num

instance : IsFiniteMeasure scaledRademacherMeasure :=
  ⟨by rw [scaledRademacherMeasure_univ_QA]
      exact ENNReal.div_lt_top (by norm_num) (by norm_num)⟩

theorem scaledRademacherMeasure_mean_QA :
    ∫ b : Bool, rademacherX b ∂scaledRademacherMeasure = 0 := by
  have hint : Integrable rademacherX scaledRademacherMeasure :=
    Integrable.mono' (integrable_const (1 : ℝ)) rademacherX_measurable_QA.aestronglyMeasurable
      (ae_of_all _ fun b => by rw [Real.norm_eq_abs, rademacherX_abs_QA b])
  rw [scaledRademacherMeasure, integral_smul_measure, rademacherMeasure_mean_QA]
  norm_num

theorem scaledRademacherMeasure_integral_exp_QA (K : ℝ) :
    ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂scaledRademacherMeasure
      = (19 / 10 : ℝ) * Real.exp (1 / K ^ 2) := by
  have hcongr : (fun b : Bool => Real.exp (rademacherX b ^ 2 / K ^ 2))
      = fun _ : Bool => Real.exp (1 / K ^ 2) := by
    funext b; rw [rademacherX_sq_QA b]
  rw [hcongr, integral_const, scaledRademacherMeasure_univ_QA]
  norm_num

/-- The arithmetic core of the guard-defect refutation: for `K ≤ 21/5`
the moment condition fails at the scaled fixture, since
`log (20/19) ≤ 1/19 < 25/441 ≤ 1/K²` gives `exp (1/K²) > 20/19` and
hence an integral strictly above `2`. -/
theorem exp_gt_two_scaled_QA {K : ℝ} (hKpos : 0 < K) (hK : K ≤ 21 / 5) :
    2 < (19 / 10 : ℝ) * Real.exp (1 / K ^ 2) := by
  have hK2 : K ^ 2 ≤ (21 / 5 : ℝ) ^ 2 := sq_le_sq' (by linarith) hK
  have h25441 : 25 / 441 ≤ 1 / K ^ 2 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 441) (by positivity)]
    nlinarith [hK2]
  have hlog : Real.log (20 / 19 : ℝ) < 25 / 441 := by
    have h1 : Real.log (20 / 19 : ℝ) ≤ 20 / 19 - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : (1 : ℝ) / 19 < 25 / 441 := by norm_num
    rw [show (20 : ℝ) / 19 - 1 = 1 / 19 from by norm_num] at h1
    exact lt_of_le_of_lt h1 h2
  have hlt : Real.log (20 / 19 : ℝ) < 1 / K ^ 2 := lt_of_lt_of_le hlog h25441
  have hexp : (20 / 19 : ℝ) < Real.exp (1 / K ^ 2) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 20 / 19)]
    exact Real.exp_lt_exp.2 hlt
  calc (2 : ℝ) = 19 / 10 * (20 / 19) := by norm_num
    _ < 19 / 10 * Real.exp (1 / K ^ 2) := mul_lt_mul_of_pos_left hexp (by norm_num)

/-- `exp (1 / 10000) < 10000 / 9999`: `exp (-x) > 1 - x` at
`x = 1/10000` composed with `exp (x) * exp (-x) = 1` — the
nonempty-witness arithmetic for the scaled fixture's defining set. -/
theorem exp_tiny_lt_QA : Real.exp (1 / 10000 : ℝ) < 10000 / 9999 := by
  have hkey : (1 : ℝ) - 1 / 10000 < Real.exp (-(1 / 10000 : ℝ)) := by
    have h1 : -(1 / 10000 : ℝ) + 1 < Real.exp (-(1 / 10000 : ℝ)) :=
      Real.add_one_lt_exp (by norm_num : -((1 : ℝ) / 10000) ≠ 0)
    rwa [show (-((1 : ℝ) / 10000)) + 1 = 1 - 1 / 10000 from by norm_num] at h1
  have hmul : Real.exp (1 / 10000) * Real.exp (-(1 / 10000 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hexp : Real.exp (1 / 10000) * (1 - 1 / 10000) < 1 := by
    calc Real.exp (1 / 10000) * (1 - 1 / 10000)
        < Real.exp (1 / 10000) * Real.exp (-(1 / 10000 : ℝ)) :=
          mul_lt_mul_of_pos_left hkey (Real.exp_pos _)
      _ = 1 := hmul
  have hq : (0 : ℝ) < 9999 / 10000 := by norm_num
  rw [show (10000 : ℝ) / 9999 = 1 / (9999 / 10000) from by field_simp,
    lt_div_iff₀ hq, show (9999 : ℝ) / 10000 = 1 - 1 / 10000 from by norm_num]
  exact hexp

/-- The pre-repair axiom's **guard defect**, refuted: at the mass-`19/10`
measure the mean-zero hypothesis still holds genuinely (bounded
variable, finite measure, canceling atoms), but the norm exceeds
`21/5 > 4` — so *no* constant `≤ 4` can repair the old statement; the
probability-measure hypothesis of the repaired axiom is load-bearing,
not decorative. -/
theorem old_hoeffding_lemma_refuted_guard_QA
    (h : subgaussianNorm rademacherX scaledRademacherMeasure ≤ 4) : False := by
  have hlower : ∀ K : ℝ, K ∈ {K : ℝ | 0 < K
      ∧ ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂scaledRademacherMeasure ≤ 2}
      → 21 / 5 ≤ K := by
    intro K hK
    by_contra hcon
    obtain ⟨hK1, hK2⟩ := hK
    rw [scaledRademacherMeasure_integral_exp_QA K] at hK2
    exact absurd hK2
      (not_le.2 (exp_gt_two_scaled_QA hK1 (le_of_lt (lt_of_not_le hcon))))
  have hmem : (100 : ℝ) ∈ {K : ℝ | 0 < K
      ∧ ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂scaledRademacherMeasure ≤ 2} := by
    refine ⟨by norm_num, ?_⟩
    rw [scaledRademacherMeasure_integral_exp_QA,
      show ((100 : ℝ) ^ 2) = 10000 from by norm_num]
    calc (19 / 10 : ℝ) * Real.exp (1 / 10000)
        ≤ (19 / 10 : ℝ) * (10000 / 9999 : ℝ) :=
          mul_le_mul_of_nonneg_left (le_of_lt exp_tiny_lt_QA) (by norm_num)
      _ ≤ 2 := by norm_num
  have h215 : 21 / 5 ≤ subgaussianNorm rademacherX scaledRademacherMeasure := by
    simp only [subgaussianNorm]
    exact le_csInf ⟨100, hmem⟩ hlower
  exact absurd (le_trans h215 h) (by norm_num : ¬ ((21 / 5 : ℝ) ≤ 4))

/-- The repaired axiom instantiated at the very fixture that refutes the
old constant: at `a = 1` the repaired statement reads
`subgaussianNorm rademacherX rademacherMeasure ≤ √6 * 1`, consistent
with the proved lower bound `6/5 ≤ norm` (`6/5 < √6 ≈ 2.449`). This is
the axiom's honest interface — conditional on the axiom, not a proof of
it. -/
theorem hoeffding_lemma_rademacher_QA :
    subgaussianNorm rademacherX rademacherMeasure ≤ √6 * 1 :=
  hoeffding_lemma (by norm_num : (0 : ℝ) ≤ 1) (fun b => by rw [rademacherX_abs_QA b])
    rademacherMeasure_mean_QA

/-- A constant real family is mutually independent under any
probability measure — the repaired `h_indep` clause shape at the
zero-family instantiations below (a constant family generates the
trivial σ-algebra at every finite index intersection; the pre-repair
pairwise clause is its two-point consequence). -/
theorem iIndepFun_const_real_QA {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (c : ℝ) :
    iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ))
      (fun (_ : Fin n) (_ : Ω) => c) μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets hsets
  by_cases hall : ∀ i ∈ T, c ∈ sets i
  · have hpre : ∀ i ∈ T, (fun _ : Ω => c) ⁻¹' sets i = Set.univ := by
      intro i hi
      ext ω
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      exact hall i hi
    have huniv : (⋂ i ∈ T, (fun _ : Ω => c) ⁻¹' sets i) = Set.univ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_univ, Set.mem_preimage]
      exact ⟨fun _ => trivial, fun h => fun i hi => hall i hi⟩
    rw [huniv, measure_univ]
    rw [Finset.prod_eq_one fun i hi => by rw [hpre i hi, measure_univ]]
  · push_neg at hall
    obtain ⟨i₀, hi₀, hi₀A⟩ := hall
    have hempty : (⋂ i ∈ T, (fun _ : Ω => c) ⁻¹' sets i) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_empty_iff_false]
      exact ⟨fun h => hi₀A (h i₀ hi₀), fun h => h.elim⟩
    have hzero : μ ((fun _ : Ω => c) ⁻¹' sets i₀) = 0 := by
      have hpre : (fun _ : Ω => c) ⁻¹' sets i₀ = ∅ := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_empty_iff_false]
        exact ⟨hi₀A, fun h => h.elim⟩
      rw [hpre, measure_empty]
    rw [hempty, measure_empty, Finset.prod_eq_zero hi₀ hzero]

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
    (iIndepFun_const_real_QA (Ω := Ω) (μ := μ) 0)
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
    (iIndepFun_const_real_QA (Ω := Ω) (μ := μ) 0)
    (fun i ω => by simp) t ht.le
  have hsum : ∑ i : Fin n, ∫ ω : Ω,
      ((0 : ℝ) - ∫ ω' : Ω, (0 : ℝ) ∂μ) ^ 2 ∂μ = 0 := by
    simp
  rwa [hsum, mul_zero, zero_add] at hax

end Scaffold.Mathlib.Probability.Concentration.Scalar.QA
