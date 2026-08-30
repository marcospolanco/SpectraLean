/-
  Scalar_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Probability.Concentration.Scalar.*`:
  the subgaussian norm definition, the *proved* subgaussian tail bound
  (retired from axiom 2026-08-22 — its interfaces are now exercised as
  hard crust, including the refutation of the old axiom shape), the
  Hoeffding/Bernstein tail bounds (retired from axioms 2026-08-30), and
  Hoeffding's lemma in ψ₂ form (repaired 2026-08-28, retired to a proved
  theorem 2026-08-30 by the pointwise-collapse route). Each tail-bound
  lemma is instantiated at explicit fixtures, so the hypothesis interface
  (integrability, moment bounds, measurability, independence of
  constants, centeredness) is exercised constructively; the event side is
  then evaluated exactly.

  The 2026-08-28 integrability audit
  (`proposals/audit-scalar-concentration-integrability-hazard.md`) added
  the refutation family for the pre-repair `hoeffding_lemma` (two
  materially false shapes, each refuted with genuinely-satisfied
  hypotheses) plus the integrability safety lemmas' first consumers.

  The retirement QA of 2026-08-30
  (`proposals/prove-hoeffding-inequality-mgf.md`) added the fences and
  closed-form instances for the proved `hoeffding_lemma_mgf` /
  `hoeffding_inequality` / `hoeffding_empirical` (retired from axioms
  that day): the wrong-constant fence at the MGF level, the mass-guard
  fence, the tail-level denominator fence with the exact
  agreement-event measure, and the first genuinely random (nonconstant)
  instantiations of both tail theorems.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not prove
  the remaining axioms; it checks their interfaces and degenerate cases.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein
import Scaffold.Mathlib.Probability.BernoulliProduct
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
a cross-axiom coherence check: `hoeffding_lemma` (retired to a proved
theorem 2026-08-30) gives `≤ √6 * 0 = 0`, and the real definition
`subgaussianNorm` gives `≥ 0`. -/
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

/-- The retired theorem instantiated at the very fixture that refutes the
old constant: at `a = 1` the statement reads
`subgaussianNorm rademacherX rademacherMeasure ≤ √6 * 1`, consistent
with the proved lower bound `6/5 ≤ norm` (`6/5 < √6 ≈ 2.449`) and with
the exact pin below (`norm = 1/√(log 2) ≈ 1.201`). Hard crust since the
2026-08-30 retirement — this instantiation consumes a proved theorem,
not an axiom. -/
theorem hoeffding_lemma_rademacher_QA :
    subgaussianNorm rademacherX rademacherMeasure ≤ √6 * 1 :=
  hoeffding_lemma (by norm_num : (0 : ℝ) ≤ 1) (fun b => by rw [rademacherX_abs_QA b])
    rademacherMeasure_mean_QA

/-!
## The `hoeffding_lemma` retirement (2026-08-30), pinned and fenced

The retirement
(`proposals/retire-hoeffding-lemma-pointwise-collapse.md`) replaced the
admitted statement by a theorem via the pointwise-collapse route: the
defining set `{K | 0 < K ∧ ∫ exp (X²/K²) ≤ 2}` sees only the bound
`|X ω| ≤ a` and the mass, never the mean, so the sharper companion
`subgaussianNorm_le_of_bounded` (`≤ a/√(log 2)`, no centering) implies
the retired shape. The falsification content lives here: the companion's
constant is *attained* (the exact two-sided Rademacher pin), it applies
to uncentered variables, and its probability-measure instance is
load-bearing (the mass-guard fence refutes the companion itself at the
mass-`19/10` fixture — a strictly sharper refutation target than the
pre-repair axiom's, since `1/√(log 2) ≈ 1.20 < √6 ≈ 2.45`).
-/

/-- The exact pin: the Rademacher norm is exactly `1/√(log 2)`. The
upper side is the companion `subgaussianNorm_le_of_bounded`'s defining
membership (the moment condition holds with equality there); the lower
side is every defining-set member forced above it (`exp (1/K²) ≤ 2`
forces `1/K² ≤ log 2`). The companion's constant is therefore sharp —
attained, not slack — and the 2026-08-28 refutation's lower-bound class
(`6/5 ≤ norm`) is re-derived two-sided: `1.2 < 1.2011… < 1.2026`, all
three pins provably consistent. -/
theorem rademacher_norm_eq_QA :
    subgaussianNorm rademacherX rademacherMeasure = 1 / Real.sqrt (Real.log 2) := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hKpos : (0 : ℝ) < 1 / Real.sqrt (Real.log 2) := by positivity
  have hK2 : (1 / Real.sqrt (Real.log 2)) ^ 2 = 1 / Real.log 2 := by
    rw [div_pow, one_pow, Real.sq_sqrt (le_of_lt hL)]
  have hmem : (1 / Real.sqrt (Real.log 2)) ∈ {K : ℝ | 0 < K
      ∧ ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂rademacherMeasure ≤ 2} := by
    refine ⟨hKpos, ?_⟩
    rw [rademacherMeasure_integral_exp_QA, hK2, one_div_one_div]
    exact le_of_eq (Real.exp_log (by norm_num : (0 : ℝ) < 2))
  have hlower : ∀ K : ℝ, K ∈ {K : ℝ | 0 < K
      ∧ ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂rademacherMeasure ≤ 2}
      → 1 / Real.sqrt (Real.log 2) ≤ K := by
    intro K hK
    obtain ⟨hK1, hK2'⟩ := hK
    rw [rademacherMeasure_integral_exp_QA K] at hK2'
    have hle : 1 / K ^ 2 ≤ Real.log 2 := by
      refine Real.exp_le_exp.1 ?_
      calc Real.exp (1 / K ^ 2) ≤ 2 := hK2'
        _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num : (0 : ℝ) < 2)).symm
    have hs : (1 : ℝ) ≤ Real.log 2 * K ^ 2 := (div_le_iff₀ (by positivity)).1 hle
    have hsqL : (Real.sqrt (Real.log 2)) ^ 2 = Real.log 2 := Real.sq_sqrt (le_of_lt hL)
    rw [div_le_iff₀ (Real.sqrt_pos.2 hL), mul_comm]
    by_contra hcon
    push_neg at hcon
    have hnn : (0 : ℝ) ≤ Real.sqrt (Real.log 2) * K :=
      mul_nonneg (Real.sqrt_nonneg _) hK1.le
    have hsq : (Real.sqrt (Real.log 2) * K) ^ 2 < 1 ^ 2 :=
      sq_lt_sq' (by linarith : (-1 : ℝ) < Real.sqrt (Real.log 2) * K) hcon
    rw [mul_pow, hsqL, one_pow] at hsq
    linarith
  simp only [subgaussianNorm]
  exact le_antisymm (csInf_le ⟨0, fun k hk => le_of_lt hk.1⟩ hmem)
    (le_csInf ⟨1 / Real.sqrt (Real.log 2), hmem⟩ hlower)

/-- The companion at an *uncentered* variable: `X ≡ 1` has mean `1 ≠ 0`,
yet `subgaussianNorm ≤ 1/√(log 2)` — the retired statement's
centering hypothesis was never needed by the proof route at this
constant. (The retired theorem itself cannot be instantiated here: its
`h_mean` hypothesis is false at this variable, which is exactly the
point — the shelf's sharper bound covers what the admitted shape's
hypotheses pretended to constrain.) -/
theorem subgaussianNorm_le_of_bounded_uncentered_QA :
    subgaussianNorm (fun _ : Bool => (1 : ℝ)) rademacherMeasure
      ≤ 1 / Real.sqrt (Real.log 2) :=
  subgaussianNorm_le_of_bounded (by norm_num) (fun b => by simp)

/-- The companion's own mass-guard fence, refuted: at the mass-`19/10`
rescaling every defining-set member is at least `1/√(log (20/19))` (from
`(19/10) · exp (1/K²) ≤ 2`, i.e. `1/K² ≤ log (20/19)`), that bound is
*attained* (the moment condition holds with equality at it), and
`1/√(log (20/19)) > 1/√(log 2)` since `20/19 < 2` — so the conclusion
`≤ 1/√(log 2)` fails and the `[IsProbabilityMeasure μ]` instance is
load-bearing for the new theorem, not decorative. This is a strictly
sharper fence than the pre-repair axiom's (`≤ 4`): the refuted target
shrank from `√6 ≈ 2.45` to `1.20`. -/
theorem subgaussianNorm_le_of_bounded_guard_refuted_QA
    (h : subgaussianNorm rademacherX scaledRademacherMeasure
      ≤ 1 / Real.sqrt (Real.log 2)) : False := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hL' : (0 : ℝ) < Real.log (20 / 19 : ℝ) := Real.log_pos (by norm_num)
  have h2019 : Real.log (20 / 19 : ℝ) < Real.log 2 :=
    Real.log_lt_log (by norm_num : (0 : ℝ) < 20 / 19) (by norm_num : (20 / 19 : ℝ) < 2)
  have hc'pos : (0 : ℝ) < 1 / Real.sqrt (Real.log (20 / 19 : ℝ)) := by positivity
  have hlower : ∀ K : ℝ, K ∈ {K : ℝ | 0 < K
      ∧ ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂scaledRademacherMeasure ≤ 2}
      → 1 / Real.sqrt (Real.log (20 / 19 : ℝ)) ≤ K := by
    intro K hK
    obtain ⟨hK1, hK2⟩ := hK
    rw [scaledRademacherMeasure_integral_exp_QA K] at hK2
    have h1 : Real.exp (1 / K ^ 2) ≤ 20 / 19 := by
      refine le_of_mul_le_mul_left ?_ (by norm_num : (0 : ℝ) < 19 / 10)
      calc (19 / 10 : ℝ) * Real.exp (1 / K ^ 2) ≤ 2 := hK2
        _ = 19 / 10 * (20 / 19) := by norm_num
    have h2 : 1 / K ^ 2 ≤ Real.log (20 / 19 : ℝ) := by
      refine Real.exp_le_exp.1 ?_
      calc Real.exp (1 / K ^ 2) ≤ 20 / 19 := h1
        _ = Real.exp (Real.log (20 / 19 : ℝ)) :=
            (Real.exp_log (by norm_num : (0 : ℝ) < 20 / 19)).symm
    have hs : (1 : ℝ) ≤ Real.log (20 / 19 : ℝ) * K ^ 2 :=
      (div_le_iff₀ (by positivity)).1 h2
    have hsqL' : (Real.sqrt (Real.log (20 / 19 : ℝ))) ^ 2
        = Real.log (20 / 19 : ℝ) := Real.sq_sqrt (le_of_lt hL')
    rw [div_le_iff₀ (Real.sqrt_pos.2 hL'), mul_comm]
    by_contra hcon
    push_neg at hcon
    have hnn : (0 : ℝ) ≤ Real.sqrt (Real.log (20 / 19 : ℝ)) * K :=
      mul_nonneg (Real.sqrt_nonneg _) hK1.le
    have hsq : (Real.sqrt (Real.log (20 / 19 : ℝ)) * K) ^ 2 < 1 ^ 2 :=
      sq_lt_sq' (by linarith : (-1 : ℝ) < Real.sqrt (Real.log (20 / 19 : ℝ)) * K) hcon
    rw [mul_pow, hsqL', one_pow] at hsq
    linarith
  have hmem : (1 / Real.sqrt (Real.log (20 / 19 : ℝ))) ∈ {K : ℝ | 0 < K
      ∧ ∫ b : Bool, Real.exp (rademacherX b ^ 2 / K ^ 2) ∂scaledRademacherMeasure ≤ 2} := by
    refine ⟨hc'pos, ?_⟩
    rw [scaledRademacherMeasure_integral_exp_QA, div_pow, one_pow,
      Real.sq_sqrt (le_of_lt hL'), one_div_one_div,
      Real.exp_log (by norm_num : (0 : ℝ) < 20 / 19)]
    norm_num
  have hge : 1 / Real.sqrt (Real.log (20 / 19 : ℝ))
      ≤ subgaussianNorm rademacherX scaledRademacherMeasure := by
    simp only [subgaussianNorm]
    exact le_csInf ⟨1 / Real.sqrt (Real.log (20 / 19 : ℝ)), hmem⟩ hlower
  have hlt : 1 / Real.sqrt (Real.log 2)
      < 1 / Real.sqrt (Real.log (20 / 19 : ℝ)) := by
    rw [div_lt_div_iff₀ (Real.sqrt_pos.2 hL) (Real.sqrt_pos.2 hL')]
    simpa using Real.sqrt_lt_sqrt (le_of_lt hL') h2019
  exact absurd (le_trans hge h) (not_le.2 hlt)

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

/-! ## The retirement QA (2026-08-30): fences and closed-form instances -/

/-! ### The exact MGF at the fair coin, and the wrong-constant fence -/

theorem rademacherMeasure_mgf_QA (lam : ℝ) :
    ∫ b : Bool, Real.exp (lam * rademacherX b) ∂rademacherMeasure
      = (Real.exp lam + Real.exp (-lam)) / 2 := by
  have hintd : ∀ b : Bool,
      Integrable (fun ω : Bool => Real.exp (lam * rademacherX ω)) (Measure.dirac b) := by
    refine fun b => integrable_of_bounded_measurable
      (a := Real.exp |lam|)
      (Real.measurable_exp.comp (rademacherX_measurable_QA.const_mul lam)) ?_
    intro ω
    rw [abs_of_nonneg (Real.exp_pos _).le]
    refine Real.exp_le_exp.mpr ?_
    calc lam * rademacherX ω ≤ |lam * rademacherX ω| := le_abs_self _
      _ = |lam| * |rademacherX ω| := abs_mul _ _
      _ = |lam| := by rw [rademacherX_abs_QA ω, mul_one]
  rw [rademacherMeasure, integral_smul_measure,
    integral_add_measure (hintd true) (hintd false), integral_dirac, integral_dirac]
  simp only [rademacherX]
  field_simp

/-- The exp tail bound `exp (-1) ≥ 1/3`, from the pinned upper bound
`exp 1 < 2.7182818286 < 3`. -/
theorem rademacher_exp_neg_ge_third_QA : (1 : ℝ) / 3 ≤ Real.exp (-1 : ℝ) := by
  have hle : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have h := inv_le_inv₀ (a := 3) (b := Real.exp 1) (by norm_num) (Real.exp_pos 1)
  rw [Real.exp_neg, one_div]
  exact h.mpr hle

/-- The fair-coin MGF at `λ = 1` is at least `3/2`: `e ≥ 2.7182818283`
and `e⁻¹ ≥ 1/3` give `(e + e⁻¹)/2 ≥ 3.05/2 > 3/2`. -/
theorem rademacher_mgf_ge_three_halves_QA :
    (3 : ℝ) / 2 ≤ ∫ b : Bool, Real.exp (1 * rademacherX b) ∂rademacherMeasure := by
  rw [rademacherMeasure_mgf_QA]
  have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 := rademacher_exp_neg_ge_third_QA
  linarith

/-- The sharpened-exponent comparison: `exp (1/3) < 3/2`, by cubing —
`exp 1 = exp (1/3)³ < (3/2)³ = 27/8 = 3.375` against the pinned
`exp 1 < 2.7182818286`. -/
theorem exp_third_lt_three_halves_QA : Real.exp ((1 : ℝ) / 3) < 3 / 2 := by
  by_contra hcon
  have hle : 3 / 2 ≤ Real.exp ((1 : ℝ) / 3) := le_of_not_gt hcon
  have h3 : Real.exp ((1 : ℝ) / 3) ^ 3 = Real.exp 1 := by
    rw [pow_three, ← Real.exp_add, ← Real.exp_add]
    norm_num
  have hcube : (3 / 2 : ℝ) ^ 3 ≤ Real.exp ((1 : ℝ) / 3) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hle 3
  have h278 : (3 / 2 : ℝ) ^ 3 = 27 / 8 := by norm_num
  have hp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hlt : (2.7182818286 : ℝ) < 27 / 8 := by norm_num
  rw [← h3] at hp
  linarith [hp, hcube, h278, hlt]

/-- **The wrong-constant fence at the MGF level.** The fair-coin
Rademacher fixture — every hypothesis of `hoeffding_lemma_mgf` genuinely
satisfied at the interval `[-1, 1]`, `λ = 1` — has exact MGF
`(e + e⁻¹)/2 ≥ 3/2`, while the lemma's conclusion sharpened from the
constant `8` to `12` would read `exp (1² · 2² / 12) = exp (1/3) < 3/2`.
So the proved constant `8` cannot be weakened past `12` at this
fixture: any future proof regression that lands on a larger denominator
makes the theorem false, and this fence is engineered to catch it
(the same falsification class as the `√6 · a` repair of the admitted
`hoeffding_lemma`). -/
theorem hoeffding_lemma_mgf_constant_fence_QA
    (h : ∫ b : Bool, Real.exp (1 * rademacherX b) ∂rademacherMeasure
      ≤ Real.exp (1 ^ 2 * (1 - (-(1 : ℝ))) ^ 2 / 12)) : False := by
  have hR : (1 : ℝ) ^ 2 * (1 - (-(1 : ℝ))) ^ 2 / 12 = 1 / 3 := by norm_num
  rw [hR] at h
  exact absurd (le_trans rademacher_mgf_ge_three_halves_QA h)
    (not_le.2 exp_third_lt_three_halves_QA)

/-! ### The mass-guard fence -/

/-- The MGF at the mass-`19/10` rescaling: the fair-coin MGF scaled by
the measure's mass. -/
theorem scaledRademacherMeasure_mgf_QA (lam : ℝ) :
    ∫ b : Bool, Real.exp (lam * rademacherX b) ∂scaledRademacherMeasure
      = (19 / 10) * ((Real.exp lam + Real.exp (-lam)) / 2) := by
  rw [scaledRademacherMeasure, integral_smul_measure, rademacherMeasure_mgf_QA]
  norm_num

/-- The headroom comparison for the guard fence: `exp (1/2) < 5/3`, by
squaring — `exp 1 = exp (1/2)² < (5/3)² = 25/9 = 2.77…` against the
pinned `exp 1 < 2.7182818286`. -/
theorem exp_half_lt_five_thirds_QA : Real.exp ((1 : ℝ) / 2) < 5 / 3 := by
  by_contra hcon
  have hle : 5 / 3 ≤ Real.exp ((1 : ℝ) / 2) := le_of_not_gt hcon
  have h2 : Real.exp ((1 : ℝ) / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]
    norm_num
  have hsq : (5 / 3 : ℝ) ^ 2 ≤ Real.exp ((1 : ℝ) / 2) ^ 2 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5 / 3) hle 2
  have h259 : (5 / 3 : ℝ) ^ 2 = 25 / 9 := by norm_num
  have hp : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hlt : (2.7182818286 : ℝ) < 25 / 9 := by norm_num
  rw [← h2] at hp
  linarith [hp, hsq, h259, hlt]

/-- **The mass-guard fence.** At the mass-`19/10` rescaling of the fair
coin — not a probability measure — every *other* hypothesis of
`hoeffding_lemma_mgf` holds genuinely at the interval `[-1, 1]`, `λ = 1`
(measurability is discreteness; the bound is pointwise; the mean is the
proved `scaledRademacherMeasure_mean_QA`), yet the conclusion fails:
the MGF scales with the mass to `(19/10) · (e + e⁻¹)/2 ≥ 57/20 = 2.85`
against the bound `exp (1/2) < 5/3 < 2.85`. The probability-measure
hypothesis of the proved lemma is load-bearing, not decorative. -/
theorem hoeffding_lemma_mgf_mass_guard_fence_QA
    (h : ∫ b : Bool, Real.exp (1 * rademacherX b) ∂scaledRademacherMeasure
      ≤ Real.exp (1 ^ 2 * (1 - (-(1 : ℝ))) ^ 2 / 8)) : False := by
  have hR : (1 : ℝ) ^ 2 * (1 - (-(1 : ℝ))) ^ 2 / 8 = 1 / 2 := by norm_num
  rw [hR, scaledRademacherMeasure_mgf_QA] at h
  have hL : (57 : ℝ) / 20 ≤ 19 / 10 * ((Real.exp 1 + Real.exp (-1 : ℝ)) / 2) := by
    have h1 : (2.7182818283 : ℝ) ≤ Real.exp 1 := le_of_lt Real.exp_one_gt_d9
    have h2 := rademacher_exp_neg_ge_third_QA
    linarith
  exact absurd (le_trans hL h)
    (not_le.2 (lt_trans exp_half_lt_five_thirds_QA (by norm_num : (5 : ℝ) / 3 < 57 / 20)))

/-! ### The positive instance at the fair coin -/

/-- The proved MGF lemma instantiated at the fair-coin Rademacher
variable, interval `[-1, 1]`, `λ = 1`: every hypothesis discharged
genuinely (measurability discreteness; pointwise bound; the mean
`rademacherMeasure_mean_QA`). The bound reads `exp (1/2)`. -/
theorem hoeffding_lemma_mgf_rademacher_QA :
    ∫ b : Bool, Real.exp (1 * rademacherX b) ∂rademacherMeasure
      ≤ Real.exp (1 ^ 2 * (1 - (-(1 : ℝ))) ^ 2 / 8) := by
  refine hoeffding_lemma_mgf (a := -1) (b := 1) (by norm_num)
    rademacherX_measurable_QA ?_ rademacherMeasure_mean_QA 1
  intro b
  cases b <;> simp [rademacherX]

/-- The instance's two-sided window: the true MGF sits in the provable
bracket `[3/2, exp (1/2)] ⊂ [3/2, 5/3)` — the closed-form value
`(e + e⁻¹)/2 ≈ 1.543` against the theorem's bound `exp (1/2) ≈ 1.649`.
The bracket is narrow (width `< 1/6`), so the instance is non-vacuous
on both sides: a theorem stating less than the true value (the
`K = 12` fence above) or a degenerate trivial bound would break one of
the two ends. -/
theorem hoeffding_lemma_mgf_window_QA :
    (3 : ℝ) / 2 ≤ (Real.exp 1 + Real.exp (-1 : ℝ)) / 2
      ∧ (Real.exp 1 + Real.exp (-1 : ℝ)) / 2 ≤ Real.exp ((1 : ℝ) / 2)
      ∧ Real.exp ((1 : ℝ) / 2) < 5 / 3 := by
  refine ⟨?_, ?_, exp_half_lt_five_thirds_QA⟩
  · have hgeo := rademacher_mgf_ge_three_halves_QA
    rwa [rademacherMeasure_mgf_QA] at hgeo
  · have h := hoeffding_lemma_mgf_rademacher_QA
    rwa [rademacherMeasure_mgf_QA,
      show (1 : ℝ) ^ 2 * (1 - (-(1 : ℝ))) ^ 2 / 8 = 1 / 2 from by norm_num] at h

/-! ### The genuinely random family on the fair two-coin product space

The zero-family instantiations above cannot exercise the independence
clause at all (constant families are independent trivially). This
section instantiates `hoeffding_inequality` and `hoeffding_empirical`
at the fair two-coin BernoulliProduct space — the Rademacher lift
`scRadX` of the coordinate projections — where mutual independence is
real content (`iIndepFun_coord` composed through the ±1 map), and
computes the tail event's exact measure through the design's own
independence machinery. -/

/-- The fair design on two coordinates. -/
noncomputable def scHalf : Fin 2 → ℝ := fun _ => 1 / 2

theorem scHalf_nonneg : ∀ i, 0 ≤ scHalf i := fun _ => by norm_num [scHalf]

theorem scHalf_le_one : ∀ i, scHalf i ≤ 1 := fun _ => by norm_num [scHalf]

local instance : IsProbabilityMeasure
    (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
      scHalf scHalf_nonneg scHalf_le_one).toMeasure :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Measurability of the ±1 map out of `Bool` (discrete σ-algebra). -/
private theorem measurable_scRad_lift :
    Measurable (fun b : Bool => if b then (1 : ℝ) else -1) :=
  fun _s _ => Set.Countable.measurableSet (Set.to_countable _)

/-- Measurability of the `{0, 1}` map out of `Bool`. -/
private theorem measurable_scInd_lift :
    Measurable (fun b : Bool => if b then (1 : ℝ) else 0) :=
  fun _s _ => Set.Countable.measurableSet (Set.to_countable _)

/-- The Rademacher lift of the coordinates: `+1` at `true`, `-1` at
`false` — a genuinely nonconstant, centered, bounded family. -/
def scRadX (i : Fin 2) (ω : (Fin 2) → Bool) : ℝ := if ω i then 1 else -1

theorem scRadX_measurable_QA (i : Fin 2) : Measurable (scRadX i) := by
  exact measurable_scRad_lift.comp
    (Scaffold.Mathlib.Probability.BernoulliProduct.measurable_coord i)

theorem scRadX_abs_QA (i : Fin 2) (ω : (Fin 2) → Bool) : |scRadX i ω| = 1 := by
  cases h : ω i <;> simp [scRadX, h]

/-- The family is mutually independent: the coordinates' `iIndepFun`
composed through the measurable ±1 map. -/
theorem scRad_iIndepFun_QA :
    iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace ℝ)) scRadX
      (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure :=
  (Scaffold.Mathlib.Probability.BernoulliProduct.iIndepFun_coord
    scHalf scHalf_nonneg scHalf_le_one).comp
    (fun _ b => if b then (1 : ℝ) else -1)
    (fun _ => measurable_scRad_lift)

/-- Each coordinate is centered: through `integral_delta`,
`∫ 2δ_i − 1 = 2 · (1/2) − 1 = 0` at the fair design. -/
theorem scRad_mean_QA (i : Fin 2) :
    ∫ ω : (Fin 2) → Bool, scRadX i ω
      ∂(Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure = 0 := by
  have heq : (fun ω : (Fin 2) → Bool => scRadX i ω)
      = fun ω : (Fin 2) → Bool => (if ω i then (1 : ℝ) else 0) • 2 - 1 := by
    funext ω
    cases h : ω i with
    | true => simp [scRadX, h]; norm_num
    | false => simp [scRadX, h]
  rw [heq, integral_sub (Integrable.of_finite) (integrable_const _),
    integral_smul_const,
    Scaffold.Mathlib.Probability.BernoulliProduct.integral_delta
      scHalf scHalf_nonneg scHalf_le_one i, integral_const, measure_univ,
    ENNReal.one_toReal, one_smul, smul_eq_mul]
  norm_num [scHalf]

/-- **The closed-form Hoeffding instance at a genuinely random family**:
`P {|X₀ + X₁| ≥ 2} ≤ 2 exp (−1)` on the fair two-coin space, every
hypothesis discharged with real content (mutual independence above,
the centered means, the uniform bound `|X i ω| = 1`). -/
theorem hoeffding_inequality_scRad_QA :
    (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scRadX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ))) := by
  have h := hoeffding_inequality (n := 2) (X := scRadX) (a := fun _ => 1)
    (fun i => scRadX_measurable_QA i) scRad_iIndepFun_QA
    (fun i ω => by rw [scRadX_abs_QA i ω]) (fun i => scRad_mean_QA i) 2 (by norm_num)
  rwa [show ∑ i : Fin 2, (1 : ℝ) ^ 2 = 2 from by simp,
    show -(2 : ℝ) ^ 2 / (2 * 2) = -(1 : ℝ) from by norm_num] at h

/-- The single-coordinate cylinder masses at the fair coin. -/
theorem scRad_cyl_mass (e : Fin 2) (b : Bool) :
    (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure
        ((fun ω : (Fin 2) → Bool => ω e) ⁻¹' {b})
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  rw [Scaffold.Mathlib.Probability.BernoulliProduct.toMeasure_cyl
    scHalf scHalf_nonneg scHalf_le_one e {b}]
  cases b with
  | true => simp [Scaffold.Mathlib.Probability.BernoulliProduct.bern, scHalf]
  | false =>
      simp [Scaffold.Mathlib.Probability.BernoulliProduct.bern, scHalf]
      ring_nf

/-- **The exact event measure**: the tail event at `t = 2` is exactly
the agreement event of the two coordinates (`|X₀ + X₁| = 2` iff both
coins agree), of measure `1/4 + 1/4 = 1/2` — computed through the
design's own independence machinery (`indepFun_coord` +
`toMeasure_cyl`), independently of the tail theorem. -/
theorem scRad_agreement_event_QA :
    (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scRadX i ω| ≥ 2}
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hE : {ω : (Fin 2) → Bool | |∑ i, scRadX i ω| ≥ 2}
      = ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {true}
            ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {true})
        ∪ ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {false}
            ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {false}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff, Fin.sum_univ_two]
    cases h1 : ω 0 with
    | true =>
        cases h2 : ω 1 with
        | true => simp [scRadX, h1, h2]; norm_num
        | false => simp [scRadX, h1, h2]
    | false =>
        cases h2 : ω 1 with
        | true => simp [scRadX, h1, h2]
        | false => simp [scRadX, h1, h2]; norm_num
  have hdisj : Disjoint
      ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {true}
        ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {true})
      ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {false}
        ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {false}) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false]
    cases ω 0 <;> simp
  have hm2 : MeasurableSet
      ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {false}
        ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {false}) :=
    ((Scaffold.Mathlib.Probability.BernoulliProduct.measurable_coord 0)
      (Set.toFinite ({false} : Set Bool)).measurableSet).inter
      ((Scaffold.Mathlib.Probability.BernoulliProduct.measurable_coord 1)
        (Set.toFinite ({false} : Set Bool)).measurableSet)
  have hnee : (0 : Fin 2) ≠ 1 := by decide
  have hindep := Scaffold.Mathlib.Probability.BernoulliProduct.indepFun_coord
    scHalf scHalf_nonneg scHalf_le_one hnee
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hindep
  have hTT := hindep {true} {true}
    ((Set.toFinite ({true} : Set Bool)).measurableSet)
    ((Set.toFinite ({true} : Set Bool)).measurableSet)
  have hFF := hindep {false} {false}
    ((Set.toFinite ({false} : Set Bool)).measurableSet)
    ((Set.toFinite ({false} : Set Bool)).measurableSet)
  rw [hE, measure_union hdisj hm2, hTT, hFF,
    scRad_cyl_mass 0 true, scRad_cyl_mass 1 true,
    scRad_cyl_mass 0 false, scRad_cyl_mass 1 false]
  rw [← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  ring_nf

/-- `exp (−2) < 1/4`, i.e. `exp 2 > 4` — the dropped-factor arithmetic
for the denominator fence, from the pinned `2.7182818283 < e`. -/
theorem exp_neg_two_lt_quarter_QA : Real.exp (-(2 : ℝ)) < 1 / 4 := by
  have h4 : (4 : ℝ) < Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      ring_nf
    rw [h2]
    nlinarith [h1]
  rw [Real.exp_neg, one_div]
  exact (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num)).mpr h4

/-- The bound-side non-vacuity: `1/2 < 2 exp (−1)` — the exact event
measure against the closed-form bound, so the instance above has
genuine content on both sides. -/
theorem scRad_tail_slack_QA : (1 : ℝ) / 2 < 2 * Real.exp (-(1 : ℝ)) := by
  rw [show (2 : ℝ) * Real.exp (-(1 : ℝ)) = 2 / Real.exp 1 from by
    rw [Real.exp_neg]
    ring_nf, lt_div_iff₀ (Real.exp_pos 1)]
  have h4 : Real.exp 1 < 4 := by linarith [Real.exp_one_lt_d9]
  linarith

/-- **The tail-level denominator fence.** The exact event measure `1/2`
refutes the theorem with the factor `2` dropped from the exponent
denominator: `2 exp (−t²/∑aᵢ²) = 2 exp (−2) ≈ 0.27 < 1/2`. A future
edit that weakens the proved exponent `−t² / (2 ∑aᵢ²)` breaks exactly
this fence (the same wrong-constant class the `√6 · a` repair belongs
to, now at the tail level, with the event measure computed exactly
rather than through the bound). -/
theorem hoeffding_inequality_denominator_fence_QA
    (h : (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scRadX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 : ℝ) ^ 2 / (∑ _i : Fin 2, (1 : ℝ) ^ 2)))) :
    False := by
  have hsum : ∑ _i : Fin 2, (1 : ℝ) ^ 2 = 2 := by simp
  have hR : 2 * Real.exp (-(2 : ℝ) ^ 2 / (∑ _i : Fin 2, (1 : ℝ) ^ 2))
      = 2 * Real.exp (-(2 : ℝ)) := by rw [hsum]; norm_num
  rw [hR, scRad_agreement_event_QA] at h
  have hlt : 2 * Real.exp (-(2 : ℝ)) < 1 / 2 := by
    calc 2 * Real.exp (-(2 : ℝ))
        < 2 * (1 / 4) := mul_lt_mul_of_pos_left exp_neg_two_lt_quarter_QA (by norm_num)
      _ = 1 / 2 := by norm_num
  exact absurd h (not_le.2 (ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hlt, by norm_num⟩))

/-! ### The `hoeffding_empirical` instance -/

/-- The `[0, 1]`-valued coordinate indicators on the fair two-coin
space. -/
def scInd (i : Fin 2) (ω : (Fin 2) → Bool) : ℝ := if ω i then 1 else 0

theorem scInd_measurable_QA (i : Fin 2) : Measurable (scInd i) := by
  exact measurable_scInd_lift.comp
    (Scaffold.Mathlib.Probability.BernoulliProduct.measurable_coord i)

theorem scInd_iIndepFun_QA :
    iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace ℝ)) scInd
      (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure :=
  (Scaffold.Mathlib.Probability.BernoulliProduct.iIndepFun_coord
    scHalf scHalf_nonneg scHalf_le_one).comp
    (fun _ b => if b then (1 : ℝ) else 0)
    (fun _ => measurable_scInd_lift)

theorem scInd_mean_QA (i : Fin 2) :
    ∫ ω : (Fin 2) → Bool, scInd i ω
      ∂(Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure = 1 / 2 := by
  exact Scaffold.Mathlib.Probability.BernoulliProduct.integral_delta
    scHalf scHalf_nonneg scHalf_le_one i

/-- **The closed-form empirical instance**: `P {|mean − E mean| ≥ 1/2}
≤ 2 exp (−1)` on the fair two-coin space. The event is again the
agreement event (the empirical mean takes values `0, 1/2, 1` with
`E mean = 1/2`, so the deviation reaches `1/2` exactly when both coins
agree), of measure `1/2` — bounded by `2 exp (−2 · 2 · (1/2)²) =
2 exp (−1) ≈ 0.736`, genuinely non-vacuous on both sides. -/
theorem hoeffding_empirical_scInd_QA :
    (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool |
          |(1 / (2 : ℝ)) * ∑ i, scInd i ω
            - (1 / (2 : ℝ)) * ∑ i, ∫ ω', scInd i ω' ∂
              (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
                scHalf scHalf_nonneg scHalf_le_one).toMeasure| ≥ 1 / 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ))) := by
  have hmean : ∑ i : Fin 2, ∫ ω' : (Fin 2) → Bool, scInd i ω' ∂
      (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure = 1 := by
    rw [Fin.sum_univ_two, scInd_mean_QA, scInd_mean_QA]
    norm_num
  have h := hoeffding_empirical (n := 2) (X := scInd)
    (fun i => scInd_measurable_QA i) scInd_iIndepFun_QA
    (fun i ω => by cases h : ω i <;> simp [scInd, h]) (1 / 2) (by norm_num)
  rw [hmean] at h ⊢
  rwa [show (-2 : ℝ) * ((2 : ℕ) : ℝ) * (1 / 2) ^ 2 = -(1 : ℝ) from by norm_num] at h

/-- The empirical instance's event measure pinned: the deviation event
is exactly the two-coin agreement event, of measure `1/2` — the same
independence-machinery computation as `scRad_agreement_event_QA`. -/
theorem scInd_deviation_event_QA :
    (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
        scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool |
          |(1 / (2 : ℝ)) * ∑ i, scInd i ω
            - (1 / (2 : ℝ)) * ∑ i, ∫ ω', scInd i ω' ∂
              (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
                scHalf scHalf_nonneg scHalf_le_one).toMeasure| ≥ 1 / 2}
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hmean : ∀ ω : (Fin 2) → Bool,
      (1 / (2 : ℝ)) * ∑ i, scInd i ω
        - (1 / (2 : ℝ)) * ∑ i, ∫ ω', scInd i ω' ∂
          (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
            scHalf scHalf_nonneg scHalf_le_one).toMeasure
        = ((if ω 0 then (1 : ℝ) else 0) + (if ω 1 then (1 : ℝ) else 0)) / 2 - 1 / 2 := by
    intro ω
    simp only [Fin.sum_univ_two, scInd_mean_QA]
    cases h0 : ω 0 with
    | true =>
        cases h1 : ω 1 with
        | true => simp [scInd, h0, h1]; norm_num
        | false => simp [scInd, h0, h1]; norm_num
    | false =>
        cases h1 : ω 1 with
        | true => simp [scInd, h0, h1]; norm_num
        | false => simp [scInd, h0, h1]; norm_num
  have hE : {ω : (Fin 2) → Bool |
      |(1 / (2 : ℝ)) * ∑ i, scInd i ω
        - (1 / (2 : ℝ)) * ∑ i, ∫ ω', scInd i ω' ∂
          (Scaffold.Mathlib.Probability.BernoulliProduct.bernPMF
            scHalf scHalf_nonneg scHalf_le_one).toMeasure| ≥ 1 / 2}
      = ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {true}
            ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {true})
        ∪ ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {false}
            ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {false}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [hmean ω]
    cases h0 : ω 0 with
    | true =>
        cases h1 : ω 1 with
        | true => simp [h0, h1]; rw [abs_of_nonneg (by norm_num)]; norm_num
        | false => simp [h0, h1]
    | false =>
        cases h1 : ω 1 with
        | true => simp [h0, h1]
        | false => simp [h0, h1]; rw [abs_of_nonneg (by norm_num)]
  have hdisj : Disjoint
      ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {true}
        ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {true})
      ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {false}
        ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {false}) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false]
    cases ω 0 <;> simp
  have hm2 : MeasurableSet
      ((fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {false}
        ∩ (fun ω : (Fin 2) → Bool => ω 1) ⁻¹' {false}) :=
    ((Scaffold.Mathlib.Probability.BernoulliProduct.measurable_coord 0)
      (Set.toFinite ({false} : Set Bool)).measurableSet).inter
      ((Scaffold.Mathlib.Probability.BernoulliProduct.measurable_coord 1)
        (Set.toFinite ({false} : Set Bool)).measurableSet)
  have hnee : (0 : Fin 2) ≠ 1 := by decide
  have hindep := Scaffold.Mathlib.Probability.BernoulliProduct.indepFun_coord
    scHalf scHalf_nonneg scHalf_le_one hnee
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hindep
  have hTT := hindep {true} {true}
    ((Set.toFinite ({true} : Set Bool)).measurableSet)
    ((Set.toFinite ({true} : Set Bool)).measurableSet)
  have hFF := hindep {false} {false}
    ((Set.toFinite ({false} : Set Bool)).measurableSet)
    ((Set.toFinite ({false} : Set Bool)).measurableSet)
  rw [hE, measure_union hdisj hm2, hTT, hFF,
    scRad_cyl_mass 0 true, scRad_cyl_mass 1 true,
    scRad_cyl_mass 0 false, scRad_cyl_mass 1 false]
  rw [← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  ring_nf


/-!
## The Bernstein retirement QA (2026-08-30): the uncentered-bound
refutation witness and closed-form instances

The 2026-08-30 repair-and-retirement of `bernstein_inequality` and
`bernstein_bounded_variance` (Errata §8) replaced the *uncentered* bound
hypothesis `|X i ω| ≤ a` with the source-faithful centered shape. The
falsification content for that repair lives here: at the biased coin
every hypothesis of the **pre-repair** shape holds genuinely at `a = 1`,
with the *true* variance `V = 9/25`, yet the per-variable MGF bound the
claimed denominator `2V + 2at/3` prices —
`E e^{λY} ≤ exp (λ²V/(2(1 − λa/3)))` at `λ = 5/9` — is violated.
-/

/-- The biased coin measure: mass `1/10` at `true`, `9/10` at `false`. -/
noncomputable def biasedCoin : Measure Bool :=
  ((1 : ℝ≥0∞) / 10) • Measure.dirac true + ((9 : ℝ≥0∞) / 10) • Measure.dirac false

theorem biasedCoin_univ_QA : biasedCoin Set.univ = 1 := by
  have h1 : (Measure.dirac true) Set.univ = 1 := measure_univ
  have h2 : (Measure.dirac false) Set.univ = 1 := measure_univ
  show (((1 : ℝ≥0∞) / 10) • Measure.dirac true
      + ((9 : ℝ≥0∞) / 10) • Measure.dirac false) Set.univ = 1
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, h1, h2,
    smul_eq_mul, smul_eq_mul, mul_one, mul_one, div_eq_mul_inv, div_eq_mul_inv,
    ← add_mul, show ((1 : ℝ≥0∞) + 9) = 10 from by norm_num]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

instance : IsProbabilityMeasure biasedCoin := ⟨biasedCoin_univ_QA⟩

/-- Every real function on `Bool` is measurable (the σ-algebra is
discrete). -/
theorem biasedCoin_bool_measurable_QA (f : Bool → ℝ) : Measurable f :=
  fun _s _ => Set.Countable.measurableSet (Set.to_countable _)

/-- Integrals of bounded functions at the biased coin. -/
theorem biasedCoin_integral_QA (f : Bool → ℝ) (c : ℝ) (hb : ∀ b, |f b| ≤ c) :
    ∫ b, f b ∂biasedCoin = (1 / 10) * f true + (9 / 10) * f false := by
  have hintd : ∀ b : Bool, Integrable f (Measure.dirac b) :=
    fun b => integrable_of_bounded_measurable (biasedCoin_bool_measurable_QA f) hb
  have hsmulT : Integrable f (((1 : ℝ≥0∞) / 10) • Measure.dirac true) :=
    (hintd true).smul_measure (c := (1 : ℝ≥0∞) / 10)
      (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne
  have hsmulF : Integrable f (((9 : ℝ≥0∞) / 10) • Measure.dirac false) :=
    (hintd false).smul_measure (c := (9 : ℝ≥0∞) / 10)
      (ENNReal.div_lt_top (by norm_num) (by norm_num)).ne
  rw [biasedCoin, integral_add_measure hsmulT hsmulF,
    integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac]
  simp

/-- The biased coin variable: `+1` at `true`, `−1` at `false`. -/
def biasedX : Bool → ℝ := fun b => if b then 1 else -1

theorem biasedX_true_QA : biasedX true = 1 := by simp [biasedX]

theorem biasedX_false_QA : biasedX false = -1 := by simp [biasedX]

/-- The **pre-repair hypothesis** `|X i ω| ≤ a` (uncentered) holds
genuinely at `a = 1`: this is the clause whose reading the repair
changed. -/
theorem biasedX_abs_QA (b : Bool) : |biasedX b| ≤ 1 := by
  cases b with
  | true => rw [biasedX_true_QA]; norm_num
  | false => rw [biasedX_false_QA]; norm_num

/-- The mean of the biased coin: `E X = −4/5` — the coin is genuinely
biased, so the centered variable reaches `9/5` on the `+` side. -/
theorem biasedX_mean_QA : ∫ b, biasedX b ∂biasedCoin = -(4 / 5) := by
  rw [biasedCoin_integral_QA biasedX 1 biasedX_abs_QA, biasedX_true_QA, biasedX_false_QA]
  norm_num

/-- The centered second moment is the *true* variance `9/25` — the
statistic the Bernstein denominator prices, so the witness below fails
at the honest `V`, not at a misstated one. -/
theorem biasedX_var_QA :
    ∫ b, (biasedX b - ∫ b', biasedX b' ∂biasedCoin) ^ 2 ∂biasedCoin = 9 / 25 := by
  have hb : ∀ b, |(biasedX b - ∫ b', biasedX b' ∂biasedCoin)| ≤ 9 / 5 := by
    intro b
    rw [biasedX_mean_QA]
    cases b with
    | true =>
        rw [biasedX_true_QA, abs_le]
        constructor <;> norm_num
    | false =>
        rw [biasedX_false_QA, abs_le]
        constructor <;> norm_num
  have hb2 : ∀ b, |(biasedX b - ∫ b', biasedX b' ∂biasedCoin) ^ 2| ≤ (9 / 5) ^ 2 := by
    intro b
    rw [sq, abs_mul, ← sq]
    exact pow_le_pow_left₀ (abs_nonneg _) (hb b) 2
  rw [biasedCoin_integral_QA (fun b => (biasedX b - ∫ b', biasedX b' ∂biasedCoin) ^ 2)
      ((9 / 5) ^ 2) hb2,
    biasedX_mean_QA, biasedX_true_QA, biasedX_false_QA]
  norm_num

/-- The centered biased coin's MGF at `λ = 5/9`: the `+`-deviation `9/5`
gives exponent exactly `1` (so the `e` pins apply) and the `−`-side
gives `−1/9`. -/
theorem biasedX_mgf_QA :
    ∫ b, Real.exp ((5 / 9 : ℝ) * (biasedX b - ∫ b', biasedX b' ∂biasedCoin)) ∂biasedCoin
      = (9 / 10) * Real.exp (-(1 / 9 : ℝ)) + (1 / 10) * Real.exp 1 := by
  have hb : ∀ b, |Real.exp ((5 / 9 : ℝ)
      * (biasedX b - ∫ b', biasedX b' ∂biasedCoin))| ≤ Real.exp 1 := by
    intro b
    rw [abs_of_nonneg (Real.exp_pos _).le, biasedX_mean_QA]
    refine Real.exp_le_exp.mpr ?_
    cases b with
    | true => rw [biasedX_true_QA]; norm_num
    | false => rw [biasedX_false_QA]; norm_num
  rw [biasedCoin_integral_QA
      (fun b => Real.exp ((5 / 9 : ℝ) * (biasedX b - ∫ b', biasedX b' ∂biasedCoin)))
      (Real.exp 1) hb]
  simp only [biasedX_mean_QA, biasedX_true_QA, biasedX_false_QA]
  norm_num
  ring

/-- **The MGF-separation witness.** At the biased coin, the claimed
exponential `exp (3/44)` — exactly `λ²V/(2(1 − λa/3))` at `λ = 5/9`,
`a = 1`, `V = 9/25` — sits strictly below the true MGF. The proof:
`exp (3/44) < 44/41` by the reciprocal trick (`exp (−x) > 1 − x`), and
`(9/10)·exp (−1/9) + (1/10)·e ≥ (9/10)·(17/18)² + e/10 > 44/41` by the
squaring trick (`exp (−1/9) ≥ (exp (−1/18))² ≥ (1 − 1/18)²`) and the
pinned `e > 2.7182818283`. -/
theorem bernstein_mgf_separation_QA :
    Real.exp (3 / 44 : ℝ)
      < ∫ b, Real.exp ((5 / 9 : ℝ) * (biasedX b - ∫ b', biasedX b' ∂biasedCoin)) ∂biasedCoin := by
  rw [biasedX_mgf_QA]
  have hneg : (1 : ℝ) - 3 / 44 < Real.exp (-(3 / 44 : ℝ)) := by
    have h1 : -(3 / 44 : ℝ) + 1 < Real.exp (-(3 / 44 : ℝ)) :=
      Real.add_one_lt_exp (by norm_num : -((3 : ℝ) / 44) ≠ 0)
    rwa [show -((3 : ℝ) / 44) + 1 = 1 - 3 / 44 from by norm_num] at h1
  have hprod : Real.exp (3 / 44 : ℝ) * Real.exp (-(3 / 44 : ℝ)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hmul : Real.exp (3 / 44 : ℝ) * (1 - 3 / 44 : ℝ) < 1 := by
    calc Real.exp (3 / 44 : ℝ) * (1 - 3 / 44 : ℝ)
        < Real.exp (3 / 44 : ℝ) * Real.exp (-(3 / 44 : ℝ)) :=
          mul_lt_mul_of_pos_left hneg (Real.exp_pos _)
      _ = 1 := hprod
  have hden : (0 : ℝ) < 1 - 3 / 44 := by norm_num
  have hinv : Real.exp (3 / 44 : ℝ) < 44 / 41 := by
    have hlt : Real.exp (3 / 44 : ℝ) < 1 / (1 - 3 / 44 : ℝ) := by
      rw [lt_div_iff₀ hden]
      exact hmul
    calc Real.exp (3 / 44 : ℝ) < 1 / (1 - 3 / 44 : ℝ) := hlt
      _ = 44 / 41 := by field_simp; ring
  have hsq : (17 / 18 : ℝ) ^ 2 ≤ Real.exp (-(1 / 9 : ℝ)) := by
    have h1 : (1 : ℝ) - 1 / 18 ≤ Real.exp (-(1 / 18 : ℝ)) :=
      Real.one_sub_le_exp_neg _
    have h2 : Real.exp (-(1 / 9 : ℝ))
        = Real.exp (-(1 / 18 : ℝ)) * Real.exp (-(1 / 18 : ℝ)) := by
      rw [← Real.exp_add]
      norm_num
    have hsqeq : ((1 : ℝ) - 1 / 18) ^ 2
        = (1 - 1 / 18) * (1 - 1 / 18) := by ring
    have h17 : (17 / 18 : ℝ) = 1 - 1 / 18 := by norm_num
    rw [h2, h17, hsqeq]
    exact mul_le_mul h1 h1 (by positivity) (by positivity)
  refine hinv.trans_le ?_
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  calc (44 / 41 : ℝ) = 289 / 360 + 3991 / 14760 := by norm_num
    _ = (9 / 10) * (17 / 18) ^ 2 + 3991 / 14760 := by norm_num
    _ ≤ (9 / 10) * (17 / 18) ^ 2 + Real.exp 1 / 10 := by
        refine add_le_add_left ?_ _
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 10)]
        linarith
    _ = (9 / 10) * (17 / 18) ^ 2 + (1 / 10) * Real.exp 1 := by ring
    _ ≤ (9 / 10) * Real.exp (-(1 / 9 : ℝ)) + (1 / 10) * Real.exp 1 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hsq (by norm_num)) _

/-- **The refutation fence for the pre-repair hypothesis shape.** The
pre-repair `bernstein_inequality` hypothesized the uncentered bound
`|X i ω| ≤ a`; at this fixture every such hypothesis holds genuinely at
`a = 1` (measurability `biasedCoin_bool_measurable_QA`, singleton
independence, `biasedX_abs_QA`, and the *true* variance
`biasedX_var_QA` = `9/25`), yet the per-variable MGF bound the claimed
denominator `2V + 2at/3` prices — stated here at `λ = 5/9`, whose
exponent `λ²V/(2(1 − λa/3))` is exactly `3/44` — is violated. The
mechanism: the centered variable reaches `9/5 > a`, so the linear term
prices `a = 1` while the true Bennett price needs `M = 9/5`. (The
tail-level violation needs `n ≳ 500–1000` variables — beyond exact Lean
witness scale; see the proposal's numerical large-deviation record.) -/
theorem old_bernstein_mgf_uncentered_refuted_QA
    (h : ∫ b, Real.exp ((5 / 9 : ℝ) * (biasedX b - ∫ b', biasedX b' ∂biasedCoin)) ∂biasedCoin
      ≤ Real.exp ((5 / 9 : ℝ) ^ 2 * (9 / 25) / (2 * (1 - (5 / 9 : ℝ) * 1 / 3)))) : False := by
  have hR : (5 / 9 : ℝ) ^ 2 * (9 / 25) / (2 * (1 - (5 / 9 : ℝ) * 1 / 3)) = 3 / 44 := by
    norm_num
  rw [hR] at h
  exact absurd h (not_le.2 bernstein_mgf_separation_QA)

/-! ### The repaired statements' closed-form instances -/

/-- The centered second moment of the fair-coin Rademacher variable is
exactly `1` (the mean is the proved `rademacherMeasure_mean_QA`). -/
theorem rademacher_var_QA :
    ∫ b : Bool, (rademacherX b - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure) ^ 2
      ∂rademacherMeasure = 1 := by
  have hfn : (fun b : Bool => (rademacherX b
      - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure) ^ 2) = fun _ => (1 : ℝ) := by
    funext b
    rw [rademacherMeasure_mean_QA, sub_zero, rademacherX_sq_QA b]
  rw [hfn, integral_const, measure_univ]
  simp

/-- The exp tail slack: `1 ≤ 2 exp (−3/8)`, via
`1 − 3/8 = 5/8 ≤ exp (−3/8)`. -/
theorem exp_neg_three_eighth_ge_half_QA : (1 : ℝ) / 2 < Real.exp (-(3 / 8 : ℝ)) := by
  have h := Real.one_sub_le_exp_neg (3 / 8 : ℝ)
  have h58 : (1 : ℝ) - 3 / 8 = 5 / 8 := by norm_num
  rw [h58] at h
  linarith

/-- The repaired (and retired) `bernstein_inequality` instantiated at
its first genuinely random family — the fair-coin Rademacher variable,
`a = 1`, `t = 1`: every clause discharged genuinely (measurability
discreteness; singleton independence by `iIndepFun.of_subsingleton`;
the centered bound through `rademacherX_abs_QA`; the variance statistic
`rademacher_var_QA`), the event is all of `Bool` with measure `1`, and
the bound evaluates to the closed form `2 exp (−3/8) > 1`. -/
theorem bernstein_inequality_rademacher_QA :
    rademacherMeasure {b : Bool |
        |∑ i : Fin 1, (rademacherX b - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure)| ≥ 1}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ) ^ 2 / (2 * 1 + (2 * 1 * 1) / 3))) := by
  have hint := bernstein_inequality (μ := rademacherMeasure) (a := 1)
    (X := fun (_ : Fin 1) (b : Bool) => rademacherX b) (by norm_num)
    (fun _ => rademacherX_measurable_QA) iIndepFun.of_subsingleton
    (fun _ b => by
      show |rademacherX b - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure| ≤ 1
      rw [rademacherMeasure_mean_QA, sub_zero, rademacherX_abs_QA b])
    1 (by norm_num)
  have hvar : ∑ i : Fin 1, ∫ b : Bool,
      (rademacherX b - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure) ^ 2
        ∂rademacherMeasure = 1 := by
    rw [Finset.sum_congr rfl (fun _ _ => rademacher_var_QA), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [hvar] at hint
  have hevent : {b : Bool |
      |∑ i : Fin 1, (rademacherX b - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure)| ≥ 1}
      = Set.univ := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [Fin.sum_univ_one, rademacherMeasure_mean_QA, sub_zero, rademacherX_abs_QA b]
  rw [hevent, measure_univ]
  have hbound : (2 : ℝ) * Real.exp (-(1 : ℝ) ^ 2 / (2 * 1 + (2 * 1 * 1) / 3))
      = 2 * Real.exp (-(3 / 8 : ℝ)) := by norm_num
  rw [hbound]
  refine ENNReal.one_le_ofReal.mpr ?_
  have h := exp_neg_three_eighth_ge_half_QA
  nlinarith [h, (Real.exp_pos (-(3 / 8 : ℝ))).le]

/-- The repaired (and retired) `bernstein_bounded_variance` at the same
fixture with the tight budget `v = 1`: the same closed form, exercising
the (now dead-hypothesis-free) budget clause set. -/
theorem bernstein_bounded_variance_rademacher_QA :
    rademacherMeasure {b : Bool |
        |∑ i : Fin 1, (rademacherX b - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure)| ≥ 1}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ) ^ 2 / (2 * 1 + (2 * 1 * 1) / 3))) := by
  have hint := bernstein_bounded_variance (μ := rademacherMeasure) (a := 1) (v := 1)
    (X := fun (_ : Fin 1) (b : Bool) => rademacherX b) (by norm_num)
    (fun _ => rademacherX_measurable_QA) iIndepFun.of_subsingleton
    (fun _ b => by
      show |rademacherX b - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure| ≤ 1
      rw [rademacherMeasure_mean_QA, sub_zero, rademacherX_abs_QA b])
    (by
      rw [Finset.sum_congr rfl (fun _ _ => rademacher_var_QA), Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num)
    1 (by norm_num)
  have hevent : {b : Bool |
      |∑ i : Fin 1, (rademacherX b - ∫ b' : Bool, rademacherX b' ∂rademacherMeasure)| ≥ 1}
      = Set.univ := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [Fin.sum_univ_one, rademacherMeasure_mean_QA, sub_zero, rademacherX_abs_QA b]
  rw [hevent, measure_univ] at hint ⊢
  have hbound : (2 : ℝ) * Real.exp (-(1 : ℝ) ^ 2 / (2 * 1 + (2 * 1 * 1) / 3))
      = 2 * Real.exp (-(3 / 8 : ℝ)) := by norm_num
  rw [hbound] at hint ⊢
  exact hint


end Scaffold.Mathlib.Probability.Concentration.Scalar.QA
