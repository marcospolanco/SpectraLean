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

  The measurability/integrability-guard follow-up (2026-09-05, the
  audit proposal's own follow-up record) added the `MeasurabilityFences`
  section: eleven hypothesis-form fences at the biased two-point
  trivial-σ-algebra space, closing the family's non-measurable-fixture
  clause surface (with the trim-saturation deferral and the
  truth-removable-through-junk MGF classifications recorded in the
  proposal). The same day's deferral closure (the proposal's
  deferral-closure record) added the `SaturationFences` section: the
  saturation lemma and the saturated-independence machinery fence the
  two deferred siblings at the four-cell family, completing the
  family's falsification surface.

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


/-!
## Adversarial fences

The hypothesis-necessity pass (`governance/ADVERSARIAL_REVIEW.md`;
proposal `proposals/adversarial-fences-scalar-concentration-family.md`,
2026-09-05): eleven hypothesis-form fences over the family's unfenced
priceable surface — the `h_indep` clauses of nine tail/MGF theorems at
the perfectly-correlated two-coin fixture `scCorrX` (the retirement
QA instantiated independence genuinely at `scRadX` but never refuted a
dropped-independence statement), and the `ht : 0 ≤ t` backward-time
clauses of the Hoeffding and Bernstein head theorems at the delivered
`scRadX` fixture. Each fence assumes the theorem's conclusion with one
clause dropped at a fixture keeping every kept clause genuine, and
derives `False`.
-/

section AdversarialFences

open Scaffold.Mathlib.Probability.BernoulliProduct

/-! ## The perfectly-correlated fixture -/

private theorem scF_ne_ff_ft : (![false, false] : Fin 2 → Bool) ≠ ![false, true] := fun he =>
  absurd (congrFun he 1) (by decide)

private theorem scF_ne_ff_tf : (![false, false] : Fin 2 → Bool) ≠ ![true, false] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem scF_ne_ff_tt : (![false, false] : Fin 2 → Bool) ≠ ![true, true] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem scF_ne_ft_tf : (![false, true] : Fin 2 → Bool) ≠ ![true, false] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem scF_ne_ft_tt : (![false, true] : Fin 2 → Bool) ≠ ![true, true] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem scF_ne_tf_tt : (![true, false] : Fin 2 → Bool) ≠ ![true, true] := fun he =>
  absurd (congrFun he 1) (by decide)

set_option linter.unusedVariables false in
/-- The perfectly-correlated family: both coordinates are the ±1 lift
of coordinate `0`. Every non-independence clause of every theorem in
the family is genuine here (measurable, `|X| = 1`, mean `0`,
variance `1`) — the family is distributionally identical to `scRadX`;
only the joint law differs. -/
def scCorrX (i : Fin 2) (ω : (Fin 2) → Bool) : ℝ := if ω 0 then 1 else -1

theorem scCorrX_measurable_QA (i : Fin 2) : Measurable (scCorrX i) :=
  measurable_scRad_lift.comp (measurable_coord 0)

theorem scCorrX_abs_QA (i : Fin 2) (ω : (Fin 2) → Bool) : |scCorrX i ω| = 1 := by
  cases h : ω 0 <;> simp [scCorrX, h]

theorem scCorrX_mean_QA (i : Fin 2) :
    ∫ ω : (Fin 2) → Bool, scCorrX i ω
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 0 := by
  have heq : (fun ω : (Fin 2) → Bool => scCorrX i ω)
      = fun ω : (Fin 2) → Bool => (if ω 0 then (1 : ℝ) else 0) • 2 - 1 := by
    funext ω
    cases h : ω 0 with
    | true => simp [scCorrX, h]; norm_num
    | false => simp [scCorrX, h]
  rw [heq, integral_sub (Integrable.of_finite) (integrable_const _),
    integral_smul_const,
    integral_delta scHalf scHalf_nonneg scHalf_le_one 0, integral_const,
    measure_univ, ENNReal.one_toReal, one_smul, smul_eq_mul]
  norm_num [scHalf]

/-- The `h_indep` breaker is genuine: the family is NOT mutually
independent (both coordinates are the same function of the same
coordinate). -/
theorem scCorr_not_iIndepFun_QA :
    ¬ iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace ℝ)) scCorrX
      (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure := by
  intro hind
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hind
  have h' := hind (Finset.univ : Finset (Fin 2)) (sets := fun _ => {1})
    (fun _ _ => (Set.toFinite {1} : Set.Finite _).measurableSet)
  have hprei : ∀ (i : Fin 2), scCorrX i ⁻¹' {1}
      = (fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {true} := by
    intro i
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, scCorrX]
    cases h : ω 0
    · simp [h]; norm_num
    · simp [h]
  have hint : (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
      (fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {true})
      = (fun ω : (Fin 2) → Bool => ω 0) ⁻¹' {true} := by
    ext ω
    simp only [Set.mem_iInter]
    exact ⟨fun hh => hh 0 (Finset.mem_univ 0), fun hh k _ => hh⟩
  simp only [hprei, hint] at h'
  rw [scRad_cyl_mass 0 true, Finset.prod_const, Finset.card_fin, pow_two,
    ← ENNReal.ofReal_mul (by norm_num)] at h'
  apply_fun ENNReal.toReal at h'
  rw [ENNReal.toReal_ofReal (by norm_num), ENNReal.toReal_ofReal (by norm_num)] at h'
  norm_num at h'

/-- The MGF pin: the exponential moment of the correlated family at
parameter `z` is `cosh z` (the four-atom enumeration; the mass of every
atom is `1/4` and the summand only sees coordinate `0`). -/
theorem scCorr_integral_exp (z : ℝ) :
    ∫ ω : (Fin 2) → Bool, Real.exp (z * scCorrX 0 ω)
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
      = (Real.exp z + Real.exp (-z)) / 2 := by
  have hb : ∀ (i : Fin 2) (b : Bool), bern scHalf i b = ENNReal.ofReal ((1 : ℝ) / 2) := by
    intro i b
    cases b
    · simp [bern, scHalf]
      congr 1; norm_num
    · simp [bern, scHalf]
  have hmass : ∀ ω : (Fin 2) → Bool,
      ((bernPMF scHalf scHalf_nonneg scHalf_le_one) ω).toReal = 1 / 4 := by
    intro ω
    have h1 : jointMass scHalf ω
        = ENNReal.ofReal ((1 : ℝ) / 2) * ENNReal.ofReal ((1 : ℝ) / 2) := by
      simp only [jointMass, Fin.prod_univ_two, hb]
    rw [bernPMF_apply, h1, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  have huniv : (Finset.univ : Finset ((Fin 2) → Bool))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by
    ext ω
    cases h0 : ω 0 <;> cases h1 : ω 1 <;>
      simp [Set.mem_singleton_iff, Set.mem_insert_iff, funext_iff, h0, h1]
    · exact Or.inl fun x => by fin_cases x <;> simp [h0, h1]
    · exact Or.inr (Or.inl fun x => by fin_cases x <;> simp [h0, h1])
    · exact Or.inr (Or.inr (Or.inl fun x => by fin_cases x <;> simp [h0, h1]))
    · exact Or.inr (Or.inr (Or.inr fun x => by fin_cases x <;> simp [h0, h1]))
  rw [PMF.integral_eq_sum, huniv,
    Finset.sum_insert (by simp [scF_ne_ff_ft, scF_ne_ff_tf, scF_ne_ff_tt]),
    Finset.sum_insert (by simp [scF_ne_ft_tf, scF_ne_ft_tt]),
    Finset.sum_insert (by simp [scF_ne_tf_tt]), Finset.sum_singleton]
  simp only [hmass, scCorrX, Matrix.cons_val_zero]
  norm_num
  ring

/-! ## The empirical-lift fixture and the shared exp pins -/

set_option linter.unusedVariables false in
/-- The `[0, 1]`-valued lift of the correlated family (for the
empirical form's `h_indep` breaker). -/
def scCorr01 (i : Fin 2) (ω : (Fin 2) → Bool) : ℝ := if ω 0 then 1 else 0

theorem scCorr01_measurable_QA (i : Fin 2) : Measurable (scCorr01 i) :=
  measurable_scInd_lift.comp (measurable_coord 0)

theorem scCorr01_mean_QA (i : Fin 2) :
    ∫ ω : (Fin 2) → Bool, scCorr01 i ω
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 1 / 2 := by
  simp only [scCorr01]
  exact integral_delta scHalf scHalf_nonneg scHalf_le_one 0

theorem scF_exp_gt_two_sevenths : (27 : ℝ) / 10 < Real.exp 1 :=
  lt_trans (show (27 : ℝ) / 10 < 2.7182818283 by norm_num) Real.exp_one_gt_d9

theorem scF_exp_lt_fourteen_fifths : Real.exp 1 < 14 / 5 := by
  have hsq : Real.exp 1 = (Real.exp ((1 : ℝ) / 2)) ^ 2 := by
    rw [pow_two, ← Real.exp_add]; norm_num
  have h := exp_half_lt_five_thirds_QA
  have h2 : (Real.exp ((1 : ℝ) / 2)) ^ 2 < (5 / 3 : ℝ) ^ 2 := by
    nlinarith [h, Real.exp_nonneg ((1 : ℝ) / 2)]
  rw [hsq]
  exact lt_trans h2 (by norm_num)

theorem scF_two_exp_neg_lt_one : 2 * Real.exp (-(1 : ℝ)) < 1 := by
  have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) scF_exp_gt_two_sevenths
  calc 2 * Real.exp (-(1 : ℝ)) < Real.exp 1 * Real.exp (-(1 : ℝ)) :=
        mul_lt_mul_of_pos_right he (Real.exp_pos (-1))
    _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]

theorem scF_exp_cube_eq : Real.exp 1 * Real.exp 1 * Real.exp 1 = Real.exp 3 := by
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num

theorem scF_exp_cube_gt_sixteen : (16 : ℝ) < Real.exp 1 * Real.exp 1 * Real.exp 1 := by
  have h1 : (27 : ℝ) / 10 < Real.exp 1 := scF_exp_gt_two_sevenths
  have h2 : (27 / 10 : ℝ) * (27 / 10 : ℝ) < Real.exp 1 * Real.exp 1 := by
    nlinarith [h1, sq_nonneg (Real.exp 1 - 27 / 10)]
  have h3 : (16 : ℝ) < (27 / 10 : ℝ) * ((27 / 10 : ℝ) * (27 / 10 : ℝ)) := by norm_num
  nlinarith [h1, h2, h3]

theorem scF_two_exp_neg_three_quarters_lt_one : 2 * Real.exp (-((3 : ℝ) / 4)) < 1 := by
  have hL : (Real.exp ((3 : ℝ) / 4)) ^ 4 = Real.exp 3 := by
    have hpow : (Real.exp ((3 : ℝ) / 4)) ^ 4
        = Real.exp ((3 : ℝ) / 4) * Real.exp ((3 : ℝ) / 4)
          * Real.exp ((3 : ℝ) / 4) * Real.exp ((3 : ℝ) / 4) := by ring
    rw [hpow, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num
  have hgt : (2 : ℝ) < Real.exp ((3 : ℝ) / 4) := by
    by_contra hcon
    push_neg at hcon
    have hle : (Real.exp ((3 : ℝ) / 4)) ^ 4 ≤ (2 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hcon 4
    rw [hL, show ((2 : ℝ)) ^ 4 = 16 from by norm_num] at hle
    rw [← scF_exp_cube_eq] at hle
    linarith [scF_exp_cube_gt_sixteen]
  have hinv : Real.exp (-((3 : ℝ) / 4)) < (2 : ℝ) ⁻¹ := by
    rw [Real.exp_neg, inv_lt_inv₀ (Real.exp_pos _) (by norm_num)]
    exact hgt
  rw [show (1 : ℝ) = 2 * (2 : ℝ) ⁻¹ from by field_simp]
  exact mul_lt_mul_of_pos_left hinv (by norm_num)

theorem scF_two_exp_neg_three_halves_lt_one : 2 * Real.exp (-((3 : ℝ) / 2)) < 1 := by
  have hL : (Real.exp ((3 : ℝ) / 2)) ^ 2 = Real.exp 3 := by
    have hpow : (Real.exp ((3 : ℝ) / 2)) ^ 2
        = Real.exp ((3 : ℝ) / 2) * Real.exp ((3 : ℝ) / 2) := by ring
    rw [hpow, ← Real.exp_add]
    congr 1
    norm_num
  have hgt : (2 : ℝ) < Real.exp ((3 : ℝ) / 2) := by
    by_contra hcon
    push_neg at hcon
    have hle : (Real.exp ((3 : ℝ) / 2)) ^ 2 ≤ (2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hcon 2
    rw [hL, show ((2 : ℝ)) ^ 2 = 4 from by norm_num] at hle
    rw [← scF_exp_cube_eq] at hle
    linarith [scF_exp_cube_gt_sixteen]
  have hinv : Real.exp (-((3 : ℝ) / 2)) < (2 : ℝ) ⁻¹ := by
    rw [Real.exp_neg, inv_lt_inv₀ (Real.exp_pos _) (by norm_num)]
    exact hgt
  rw [show (1 : ℝ) = 2 * (2 : ℝ) ⁻¹ from by field_simp]
  exact mul_lt_mul_of_pos_left hinv (by norm_num)


/-! ## The fences -/

/-- **Fence: `integral_prod_exp_of_iIndepFun`'s `h_indep`.** At the
perfectly-correlated family with `lam = 1`, `s = univ`: the left side is
`∫ exp (X₀ + X₁) = cosh 2` while the right side is
`(∫ exp X₀) · (∫ exp X₁) = cosh² 1` — the product-integral identity is
Cauchy–Schwarz-strict at perfect correlation (the difference is
`(e − e⁻¹)²/4 > 0`, pure algebra from `e · e⁻¹ = 1`). -/
theorem scFence_prod_exp_indep
    (h : ∫ ω : (Fin 2) → Bool, ∏ i, Real.exp ((1 : ℝ) * scCorrX i ω)
        ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
      = ∏ i, ∫ ω : (Fin 2) → Bool, Real.exp ((1 : ℝ) * scCorrX i ω)
          ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure) : False := by
  have hsum : ∀ ω : (Fin 2) → Bool, ∑ i : Fin 2, (1 : ℝ) * scCorrX i ω
      = 2 * scCorrX 0 ω := by
    intro ω
    simp only [Fin.sum_univ_two, scCorrX]
    ring
  have hcongr : ∀ ω : (Fin 2) → Bool,
      ∏ i : Fin 2, Real.exp ((1 : ℝ) * scCorrX i ω) = Real.exp (2 * scCorrX 0 ω) := by
    intro ω
    rw [← Real.exp_sum, hsum ω]
  rw [integral_congr_ae (ae_of_all _ (fun ω => hcongr ω)), scCorr_integral_exp 2] at h
  have hR : ∏ i : Fin 2, ∫ ω : (Fin 2) → Bool, Real.exp ((1 : ℝ) * scCorrX i ω)
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
      = ((Real.exp 1 + Real.exp (-1)) / 2) ^ 2 := by
    have hf : ∀ i : Fin 2, ∫ ω : (Fin 2) → Bool, Real.exp ((1 : ℝ) * scCorrX i ω)
        ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        = (Real.exp 1 + Real.exp (-1)) / 2 := fun i => scCorr_integral_exp 1
    rw [Fin.prod_univ_two, hf 0, hf 1]
    ring
  rw [hR] at h
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hem2 : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  rw [he2, hem2] at h
  have hprod : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hd : (Real.exp 1 - Real.exp (-1)) * (Real.exp 1 - Real.exp (-1)) = 0 := by
    nlinarith [h, hprod]
  have hz : Real.exp 1 - Real.exp (-1) = 0 := by
    exact (mul_self_eq_zero).mp hd
  have hne : Real.exp 1 = Real.exp (-1) := by linarith
  have h12 : (1 : ℝ) = -1 := Real.exp_strictMono.injective hne
  norm_num at h12

set_option linter.unusedVariables false in
/-- **Fence: `mgf_sum_le_of_iIndepFun`'s `h_indep`.** At the same
fixture with `lam = 1`, `c = -1`, `d = 1`: the MGF is `cosh 2` against
the bound `exp 1` — `cosh 2 > e` from the pins `27/10 < e < 14/5`. -/
theorem scFence_mgf_sum_indep
    (h : ∫ ω : (Fin 2) → Bool, Real.exp ((1 : ℝ) * ∑ i, scCorrX i ω)
        ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
      ≤ Real.exp ((1 : ℝ) ^ 2 * (∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2) / 8)) : False := by
  have hsum : ∀ ω : (Fin 2) → Bool, (1 : ℝ) * ∑ i, scCorrX i ω = 2 * scCorrX 0 ω := by
    intro ω
    simp only [Fin.sum_univ_two, scCorrX]
    ring
  have hcongr : ∀ ω : (Fin 2) → Bool, Real.exp ((1 : ℝ) * ∑ i, scCorrX i ω)
      = Real.exp (2 * scCorrX 0 ω) := by
    intro ω
    rw [hsum ω]
  rw [integral_congr_ae (ae_of_all _ (fun ω => hcongr ω)), scCorr_integral_exp 2] at h
  have hb : (1 : ℝ) ^ 2 * (∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2) / 8 = 1 := by
    have hs : ∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2 = 8 := by simp; norm_num
    rw [hs]
    norm_num
  rw [hb] at h
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hem2 : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  rw [he2, hem2] at h
  nlinarith [h, scF_exp_gt_two_sevenths, scF_exp_lt_fourteen_fifths,
    sq_nonneg (Real.exp 1 - 27 / 10), Real.exp_nonneg (-1 : ℝ)]

/-- The shared `t = 2` tail-event pin at the correlated family: the
event is all of `Ω` (the sum is `±2` everywhere). -/
theorem scCorr_event_eq_univ :
    {ω : (Fin 2) → Bool | |∑ i, scCorrX i ω| ≥ 2} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  simp only [Set.mem_setOf_eq]
  have hsum : ∑ i, scCorrX i ω = 2 * scCorrX 0 ω := by
    simp only [Fin.sum_univ_two, scCorrX]
    ring
  rw [hsum]
  cases hw : ω 0 <;> simp [scCorrX, hw]

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_inequality_interval`'s `h_indep`.** At `t = 2`
the tail event is all of `Ω` (measure `1`) against the bound
`2e⁻¹ < 1` (from `e > 2`). -/
theorem scFence_hoeffding_interval_indep
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scCorrX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (2 : ℝ) ^ 2
          / ∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2))) : False := by
  have hb : ∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2 = 8 := by
    simp
    norm_num
  rw [scCorr_event_eq_univ, measure_univ, hb,
    show (-2 * (2 : ℝ) ^ 2 / 8) = -(1 : ℝ) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_lt_one)

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_inequality`'s `h_indep`.** The same kill at the
uniform-radius form (`a := 1`, bound again `2e⁻¹`). -/
theorem scFence_hoeffding_indep
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scCorrX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 : ℝ) ^ 2
          / (2 * ∑ i : Fin 2, (1 : ℝ) ^ 2)))) : False := by
  have hb : ∑ i : Fin 2, (1 : ℝ) ^ 2 = 2 := by simp
  rw [scCorr_event_eq_univ, measure_univ, hb,
    show -(2 : ℝ) ^ 2 / (2 * 2) = -(1 : ℝ) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_lt_one)

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_iid`'s `h_indep`.** The same kill at the
identically-distributed form (`n = 2`, `a = 1`). -/
theorem scFence_hoeffding_iid_indep
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scCorrX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 : ℝ) ^ 2
          / (2 * ((2 : ℝ) * (1 : ℝ) ^ 2))))) : False := by
  rw [scCorr_event_eq_univ, measure_univ,
    show -(2 : ℝ) ^ 2 / (2 * ((2 : ℝ) * (1 : ℝ) ^ 2)) = -(1 : ℝ) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_lt_one)

/-- **Fence: `hoeffding_empirical`'s `h_indep`.** At the `[0, 1]`-lift
of the correlated family with `t = 1/2`: the empirical deviation is
`±1/2` everywhere (measure `1`) against the bound `2e⁻¹`. -/
theorem scFence_hoeffding_empirical_indep
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |(1 / (2 : ℝ)) * ∑ i, scCorr01 i ω
            - (1 / (2 : ℝ)) * ∑ i, ∫ ω' : (Fin 2) → Bool, scCorr01 i ω'
              ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure| ≥ 1 / 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (2 : ℝ) * ((1 : ℝ) / 2) ^ 2))) : False := by
  have hev : {ω : (Fin 2) → Bool | |(1 / (2 : ℝ)) * ∑ i, scCorr01 i ω
      - (1 / (2 : ℝ)) * ∑ i, ∫ ω' : (Fin 2) → Bool, scCorr01 i ω'
        ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure| ≥ 1 / 2}
      = Set.univ := by
    apply Set.eq_univ_of_forall
    intro ω
    simp only [Set.mem_setOf_eq]
    have hsum : ∑ i, scCorr01 i ω = 2 * (if ω 0 then (1 : ℝ) else 0) := by
      simp only [Fin.sum_univ_two, scCorr01]
      ring
    have hmean : ∑ i, ∫ ω' : (Fin 2) → Bool, scCorr01 i ω'
        ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 1 := by
      rw [Finset.sum_congr rfl (fun i _ => scCorr01_mean_QA i)]
      norm_num
    rw [hsum, hmean]
    cases hw : ω 0
    · simp [scCorr01, hw]
      exact le_abs_self _
    · simp [scCorr01, hw]
      rw [show ((1 : ℝ) - 2⁻¹) = 2⁻¹ from by norm_num]
      exact le_abs_self _
  rw [hev, measure_univ,
    show (-2 * (2 : ℝ) * ((1 : ℝ) / 2) ^ 2) = -(1 : ℝ) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_lt_one)

/-- The shared variance pin at the correlated family: the centered
second-moment sum is `2` (each coordinate has `|X| = 1`, mean `0`). -/
theorem scCorr_var_sum :
    ∑ i, ∫ ω : (Fin 2) → Bool, (scCorrX i ω
        - ∫ ω' : (Fin 2) → Bool, scCorrX i ω'
          ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure) ^ 2
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 2 := by
  have hint : ∀ i : Fin 2, ∫ ω : (Fin 2) → Bool, (scCorrX i ω
      - ∫ ω' : (Fin 2) → Bool, scCorrX i ω'
        ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure) ^ 2
    ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 1 := by
    intro i
    rw [scCorrX_mean_QA i]
    have hc : (fun ω : (Fin 2) → Bool => (scCorrX i ω - 0) ^ 2) = fun _ => 1 := by
      funext ω
      cases hw : ω 0 <;> simp [scCorrX, hw]
    rw [hc, integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  rw [Finset.sum_congr rfl (fun i _ => hint i)]
  norm_num

/-- The shared `t = 2` centered tail-event pin at the correlated family:
the centering integrals vanish (mean `0`) and the centered sum is
`±2` everywhere. -/
theorem scCorr_centered_event_eq_univ :
    {ω : (Fin 2) → Bool | |∑ i, (scCorrX i ω
        - ∫ ω' : (Fin 2) → Bool, scCorrX i ω'
          ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure)| ≥ 2} = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω
  simp only [Set.mem_setOf_eq, scCorrX_mean_QA]
  have hsum : ∑ i, (scCorrX i ω - 0) = 2 * scCorrX 0 ω := by
    simp only [Fin.sum_univ_two, scCorrX, sub_zero]
    ring
  rw [hsum]
  cases hw : ω 0 <;> simp [scCorrX, hw]

/-- **Fence: `bernstein_inequality`'s `h_indep`.** At `t = 2`, `a = 1`:
the centered tail event is all of `Ω` (measure `1`) against the bound
`2e^{-3/4} < 1` (from `e³ > (27/10)³ > 16`). -/
theorem scFence_bernstein_indep
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, (scCorrX i ω
            - ∫ ω' : (Fin 2) → Bool, scCorrX i ω'
              ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure)| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-((2 : ℝ) ^ 2 /
          (2 * ∑ i, ∫ ω : (Fin 2) → Bool, (scCorrX i ω
              - ∫ ω' : (Fin 2) → Bool, scCorrX i ω'
                ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure) ^ 2
            ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
          + (2 * (1 : ℝ) * 2) / 3))))) : False := by
  rw [scCorr_var_sum,
    show (2 * 2 + (2 * (1 : ℝ) * 2) / 3) = (16 : ℝ) / 3 from by norm_num,
    show (-((2 : ℝ) ^ 2 / ((16 : ℝ) / 3))) = -((3 : ℝ) / 4) from by norm_num,
    scCorr_centered_event_eq_univ, measure_univ, ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_three_quarters_lt_one)

/-- **Fence: `bernstein_bounded_variance`'s `h_indep`.** The same kill
at the budget form (`v := 2` exactly the variance statistic). -/
theorem scFence_bernstein_bounded_variance_indep
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, (scCorrX i ω
            - ∫ ω' : (Fin 2) → Bool, scCorrX i ω'
              ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure)| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-((2 : ℝ) ^ 2
          / (2 * (2 : ℝ) + (2 * (1 : ℝ) * 2) / 3))))) : False := by
  rw [scCorr_centered_event_eq_univ, measure_univ,
    show (2 * (2 : ℝ) + (2 * (1 : ℝ) * 2) / 3) = (16 : ℝ) / 3 from by norm_num,
    show (-((2 : ℝ) ^ 2 / ((16 : ℝ) / 3))) = -((3 : ℝ) / 4) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_three_quarters_lt_one)

/-- **Fence: `bernstein_iid`'s `h_indep`.** The same kill at the
identically-distributed form (`σ² := 1`). -/
theorem scFence_bernstein_iid_indep
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, (scCorrX i ω
            - ∫ ω' : (Fin 2) → Bool, scCorrX i ω'
              ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure)| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-((2 : ℝ) ^ 2
          / (2 * ((2 : ℝ) * (1 : ℝ)) + (2 * (1 : ℝ) * 2) / 3))))) : False := by
  rw [scCorr_centered_event_eq_univ, measure_univ,
    show (2 * ((2 : ℝ) * (1 : ℝ)) + (2 * (1 : ℝ) * 2) / 3) = (16 : ℝ) / 3 from by norm_num,
    show (-((2 : ℝ) ^ 2 / ((16 : ℝ) / 3))) = -((3 : ℝ) / 4) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_three_quarters_lt_one)

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_inequality`'s `ht : 0 ≤ t`.** At the genuine
scRad fixture with `t = -2`: the tail event `{|Σ| ≥ -2}` is all of `Ω`
(absolute values are nonnegative), so the measure is `1` against the
bound `2e⁻¹ < 1`. -/
theorem scFence_hoeffding_ht
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scRadX i ω| ≥ -2}
      ≤ ENNReal.ofReal (2 * Real.exp (-((-2 : ℝ) ^ 2
          / (2 * ∑ i : Fin 2, (1 : ℝ) ^ 2))))) : False := by
  have hev : {ω : (Fin 2) → Bool | |∑ i, scRadX i ω| ≥ -2} = Set.univ :=
    Set.eq_univ_of_forall fun ω => le_trans (show (-2 : ℝ) ≤ 0 by norm_num) (abs_nonneg _)
  have hs : ∑ i : Fin 2, (1 : ℝ) ^ 2 = 2 := by simp
  rw [hev, measure_univ, hs,
    show -((-2 : ℝ) ^ 2 / (2 * 2)) = -(1 : ℝ) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_lt_one)

/-- **Fence: `bernstein_inequality`'s `ht : 0 ≤ t`.** At the genuine
scRad fixture with `t = -2`: the centered tail event is all of `Ω`
against the bound `2e^{-3/2} < 1` (from `e³ > 16 > 8`). -/
theorem scFence_bernstein_ht
    (h : (bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, (scRadX i ω
            - ∫ ω' : (Fin 2) → Bool, scRadX i ω'
              ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure)| ≥ -2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(((-2 : ℝ)) ^ 2 /
          (2 * ∑ i, ∫ ω : (Fin 2) → Bool, (scRadX i ω
              - ∫ ω' : (Fin 2) → Bool, scRadX i ω'
                ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure) ^ 2
            ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
          + (2 * (1 : ℝ) * (-2)) / 3))))) : False := by
  simp only [scRad_mean_QA] at h
  have hint : ∀ i : Fin 2, ∫ ω : (Fin 2) → Bool, (scRadX i ω - 0) ^ 2
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 1 := by
    intro i
    have hc : (fun ω : (Fin 2) → Bool => (scRadX i ω - 0) ^ 2) = fun _ => 1 := by
      funext ω
      cases hw : ω i <;> simp [scRadX, hw]
    rw [hc, integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  have hvar : ∑ i, ∫ ω : (Fin 2) → Bool, (scRadX i ω - 0) ^ 2
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 2 := by
    rw [Finset.sum_congr rfl (fun i _ => hint i)]
    norm_num
  have hev : {ω : (Fin 2) → Bool | |∑ i, (scRadX i ω - 0)| ≥ -2} = Set.univ :=
    Set.eq_univ_of_forall fun ω => le_trans (show (-2 : ℝ) ≤ 0 by norm_num) (abs_nonneg _)
  rw [hvar, hev, measure_univ,
    show (2 * 2 + (2 * (1 : ℝ) * (-2)) / 3) = (8 : ℝ) / 3 from by norm_num,
    show (-(((-2 : ℝ)) ^ 2 / ((8 : ℝ) / 3))) = -((3 : ℝ) / 2) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_three_halves_lt_one)

end AdversarialFences

section DeferralFences

open Scaffold.Mathlib.Probability.BernoulliProduct

/-!
## The audit's priced deferrals, closed

The two deferrals recorded by
`proposals/adversarial-fences-scalar-concentration-family.md`, closed
2026-09-05: D1 — `mgf_sum_le_bernstein`'s `h_indep` at the
perfectly-correlated fixture (the audit's own deferred kill, re-priced
through `3/2 < cosh 1 > exp (3/10)`); D2 — the `h_mean : ∀ i, ∫ X i = 0`
centering cluster of the four Hoeffding-family theorems at a NEW
genuinely-independent biased product (the audit had no independent
non-centered witness: every prior fence broke independence, every
genuine-independence instance was centered). Each fence keeps every
kept clause genuine and drops exactly one.
-/

/-- The biased factor distribution: every coordinate `true` with
probability `9/10`. -/
noncomputable def scBias : Fin 2 → ℝ := ![9 / 10, 9 / 10]

theorem scBias_nonneg : ∀ i, 0 ≤ scBias i := by
  intro i; fin_cases i <;> norm_num [scBias]

theorem scBias_le_one : ∀ i, scBias i ≤ 1 := by
  intro i; fin_cases i <;> norm_num [scBias]

/-- The biased ±1 coordinate lift: `+1` at `true`, `-1` at `false`,
each coordinate through its OWN coordinate projection — genuinely
mutually independent (unlike `scCorrX`), with every clause of the
Hoeffding family genuine except the centering: `∫ scBiasX i = 4/5`. -/
def scBiasX (i : Fin 2) (ω : (Fin 2) → Bool) : ℝ := if ω i then 1 else -1

theorem scBiasX_measurable_QA (i : Fin 2) : Measurable (scBiasX i) :=
  measurable_scRad_lift.comp (measurable_coord i)

theorem scBiasX_abs_QA (i : Fin 2) (ω : (Fin 2) → Bool) : |scBiasX i ω| = 1 := by
  cases h : ω i <;> simp [scBiasX, h]

/-- The kept `h_indep` clause is genuine: the family is the ±1 lift
of genuinely independent coordinate projections at the biased
product. -/
theorem scBiasX_iIndepFun_QA :
    iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace ℝ)) scBiasX
      (bernPMF scBias scBias_nonneg scBias_le_one).toMeasure :=
  (iIndepFun_coord scBias scBias_nonneg scBias_le_one).comp
    (fun _ b => if b then (1 : ℝ) else -1) (fun _ => measurable_scRad_lift)

/-- The dropped `h_mean` clause genuinely fails: the coordinate mean
is `9/10 - 1/10 = 4/5 ≠ 0`. -/
theorem scBiasX_mean_QA (i : Fin 2) :
    ∫ ω : (Fin 2) → Bool, scBiasX i ω
      ∂(bernPMF scBias scBias_nonneg scBias_le_one).toMeasure = 4 / 5 := by
  have heq : (fun ω : (Fin 2) → Bool => scBiasX i ω)
      = fun ω : (Fin 2) → Bool => (if ω i then (1 : ℝ) else 0) • 2 - 1 := by
    funext ω
    cases h : ω i with
    | true => simp [scBiasX, h]; norm_num
    | false => simp [scBiasX, h]
  rw [heq, integral_sub (Integrable.of_finite) (integrable_const _),
    integral_smul_const,
    integral_delta scBias scBias_nonneg scBias_le_one i, integral_const,
    measure_univ, ENNReal.one_toReal, one_smul, smul_eq_mul]
  fin_cases i <;> norm_num [scBias]

private theorem scB_huniv :
    (Finset.univ : Finset ((Fin 2) → Bool))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by
  ext ω
  cases h0 : ω 0 <;> cases h1 : ω 1 <;>
    simp [Set.mem_singleton_iff, Set.mem_insert_iff, funext_iff, h0, h1]
  · exact Or.inl fun x => by fin_cases x <;> simp [h0, h1]
  · exact Or.inr (Or.inl fun x => by fin_cases x <;> simp [h0, h1])
  · exact Or.inr (Or.inr (Or.inl fun x => by fin_cases x <;> simp [h0, h1]))
  · exact Or.inr (Or.inr (Or.inr fun x => by fin_cases x <;> simp [h0, h1]))

private theorem scB_joint_ff : jointMass scBias ![false, false]
    = ENNReal.ofReal ((1 : ℝ) / 100) := by
  have h : jointMass scBias ![false, false]
      = ENNReal.ofReal (1 - 9 / 10) * ENNReal.ofReal (1 - 9 / 10) := by
    simp [bern, scBias, jointMass, Fin.prod_univ_two]
  rw [h, show (1 : ℝ) - 9 / 10 = 1 / 10 from by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 10)]
  congr 1
  norm_num

private theorem scB_joint_ft : jointMass scBias ![false, true]
    = ENNReal.ofReal ((9 : ℝ) / 100) := by
  have h : jointMass scBias ![false, true]
      = ENNReal.ofReal (1 - 9 / 10) * ENNReal.ofReal (9 / 10) := by
    simp [bern, scBias, jointMass, Fin.prod_univ_two]
  rw [h, show (1 : ℝ) - 9 / 10 = 1 / 10 from by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 10)]
  congr 1
  norm_num

private theorem scB_joint_tf : jointMass scBias ![true, false]
    = ENNReal.ofReal ((9 : ℝ) / 100) := by
  have h : jointMass scBias ![true, false]
      = ENNReal.ofReal (9 / 10) * ENNReal.ofReal (1 - 9 / 10) := by
    simp [bern, scBias, jointMass, Fin.prod_univ_two]
  rw [h, show (1 : ℝ) - 9 / 10 = 1 / 10 from by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9 / 10)]
  congr 1
  norm_num

private theorem scB_joint_tt : jointMass scBias ![true, true]
    = ENNReal.ofReal ((81 : ℝ) / 100) := by
  have h : jointMass scBias ![true, true]
      = ENNReal.ofReal (9 / 10) * ENNReal.ofReal (9 / 10) := by
    simp [bern, scBias, jointMass, Fin.prod_univ_two]
  rw [h, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 9 / 10)]
  congr 1
  norm_num

private theorem scB_mass_ff :
    ((bernPMF scBias scBias_nonneg scBias_le_one) ![false, false]).toReal
      = 1 / 100 := by
  rw [bernPMF_apply, scB_joint_ff, ENNReal.toReal_ofReal (by norm_num)]

private theorem scB_mass_ft :
    ((bernPMF scBias scBias_nonneg scBias_le_one) ![false, true]).toReal
      = 9 / 100 := by
  rw [bernPMF_apply, scB_joint_ft, ENNReal.toReal_ofReal (by norm_num)]

private theorem scB_mass_tf :
    ((bernPMF scBias scBias_nonneg scBias_le_one) ![true, false]).toReal
      = 9 / 100 := by
  rw [bernPMF_apply, scB_joint_tf, ENNReal.toReal_ofReal (by norm_num)]

private theorem scB_mass_tt :
    ((bernPMF scBias scBias_nonneg scBias_le_one) ![true, true]).toReal
      = 81 / 100 := by
  rw [bernPMF_apply, scB_joint_tt, ENNReal.toReal_ofReal (by norm_num)]

/-- The `t = 2` tail-event mass at the biased independent family: the
event is `{ω | ω 0 = ω 1}` (both coordinates equal — the sum is `±2`),
at measure `81/100 + 1/100 = 41/50`. -/
theorem scBias_event_mass :
    (bernPMF scBias scBias_nonneg scBias_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2}
      = ENNReal.ofReal ((41 : ℝ) / 50) := by
  have hmeas : MeasurableSet {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have meff : (![false, false] : Fin 2 → Bool)
      ∈ {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2} := by
    simp only [Set.mem_setOf_eq, Fin.sum_univ_two, scBiasX]
    norm_num
  have mft : ¬(![false, true] : Fin 2 → Bool)
      ∈ {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2} := by
    simp only [Set.mem_setOf_eq, Fin.sum_univ_two, scBiasX, not_false_iff]
    norm_num
  have mtf : ¬(![true, false] : Fin 2 → Bool)
      ∈ {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2} := by
    simp only [Set.mem_setOf_eq, Fin.sum_univ_two, scBiasX, not_false_iff]
    norm_num
  have mett : (![true, true] : Fin 2 → Bool)
      ∈ {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2} := by
    simp only [Set.mem_setOf_eq, Fin.sum_univ_two, scBiasX]
    norm_num
  have hff : (bernPMF scBias scBias_nonneg scBias_le_one) ![false, false]
      = ENNReal.ofReal ((1 : ℝ) / 100) := by
    rw [bernPMF_apply, scB_joint_ff]
  have htt : (bernPMF scBias scBias_nonneg scBias_le_one) ![true, true]
      = ENNReal.ofReal ((81 : ℝ) / 100) := by
    rw [bernPMF_apply, scB_joint_tt]
  rw [PMF.toMeasure_apply _ _ hmeas, tsum_fintype]
  simp only [Set.indicator_apply]
  rw [scB_huniv,
    Finset.sum_insert (by simp [scF_ne_ff_ft, scF_ne_ff_tf, scF_ne_ff_tt]),
    Finset.sum_insert (by simp [scF_ne_ft_tf, scF_ne_ft_tt]),
    Finset.sum_insert (by simp [scF_ne_tf_tt]), Finset.sum_singleton,
    if_pos meff, if_neg mft, if_neg mtf, if_pos mett, hff, htt]
  simp only [zero_add, add_zero]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 100)
      (by norm_num : (0 : ℝ) ≤ 81 / 100)]
  congr 1
  norm_num

/-- The MGF pin at `lam = 1`: the exponential moment of the biased
independent family is `(81/100)e² + 18/100 + (1/100)e⁻²` (the
four-atom enumeration; the `tt` atom alone carries `(81/100)e²`). -/
theorem scBias_integral_exp_one :
    ∫ ω : (Fin 2) → Bool, Real.exp ((1 : ℝ) * ∑ i, scBiasX i ω)
      ∂(bernPMF scBias scBias_nonneg scBias_le_one).toMeasure
      = (81 / 100) * (Real.exp 1 * Real.exp 1) + 18 / 100
          + (1 / 100) * (Real.exp (-1) * Real.exp (-1)) := by
  have vff : (1 : ℝ) * ∑ i, scBiasX i (![false, false] : Fin 2 → Bool) = -2 := by
    simp only [Fin.sum_univ_two, scBiasX]; norm_num
  have vft : (1 : ℝ) * ∑ i, scBiasX i (![false, true] : Fin 2 → Bool) = 0 := by
    simp only [Fin.sum_univ_two, scBiasX]; norm_num
  have vtf : (1 : ℝ) * ∑ i, scBiasX i (![true, false] : Fin 2 → Bool) = 0 := by
    simp only [Fin.sum_univ_two, scBiasX]; norm_num
  have vtt : (1 : ℝ) * ∑ i, scBiasX i (![true, true] : Fin 2 → Bool) = 2 := by
    simp only [Fin.sum_univ_two, scBiasX]; norm_num
  rw [PMF.integral_eq_sum, scB_huniv,
    Finset.sum_insert (by simp [scF_ne_ff_ft, scF_ne_ff_tf, scF_ne_ff_tt]),
    Finset.sum_insert (by simp [scF_ne_ft_tf, scF_ne_ft_tt]),
    Finset.sum_insert (by simp [scF_ne_tf_tt]), Finset.sum_singleton,
    scB_mass_ff, scB_mass_ft, scB_mass_tf, scB_mass_tt, vff, vft, vtf, vtt]
  have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have hem2 : Real.exp (-2) = Real.exp (-1) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  rw [he2, hem2, Real.exp_zero]
  norm_num
  ring

private theorem scF_ofReal_le_ofReal' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ENNReal.ofReal a ≤ ENNReal.ofReal b) : a ≤ b := by
  have h1 := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top
    ENNReal.ofReal_ne_top).mpr h
  rwa [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at h1

theorem scF_exp_inv_lt_ten_27s : Real.exp (-1) < 10 / 27 := by
  have hprod : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hepos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  by_contra hcon
  push_neg at hcon
  nlinarith [hcon, hprod, hepos, scF_exp_gt_two_sevenths]

theorem scF_two_exp_neg_lt_41_50 : 2 * Real.exp (-(1 : ℝ)) < 41 / 50 := by
  calc 2 * Real.exp (-(1 : ℝ)) < 2 * (10 / 27) :=
        mul_lt_mul_of_pos_left scF_exp_inv_lt_ten_27s (by norm_num)
    _ < 41 / 50 := by norm_num

set_option linter.unusedVariables false in
/-- **Fence: `mgf_sum_le_of_iIndepFun`'s `h_mean`.** At the genuinely
independent biased family with `lam = 1`, `c = -1`, `d = 1`: the MGF
is at least the `tt` atom's `(81/100)e²` while the bound is
`exp 1` — and `(81/100)e > 1` already at `e > 27/10`, so the centering
clause is load-bearing against non-centered independent input. -/
theorem scFence_mgf_sum_mean
    (h : ∫ ω : (Fin 2) → Bool, Real.exp ((1 : ℝ) * ∑ i, scBiasX i ω)
        ∂(bernPMF scBias scBias_nonneg scBias_le_one).toMeasure
      ≤ Real.exp ((1 : ℝ) ^ 2 * (∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2) / 8)) : False := by
  have hb : (1 : ℝ) ^ 2 * (∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2) / 8 = 1 := by
    have hs : ∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2 = 8 := by simp; norm_num
    rw [hs]
    norm_num
  rw [scBias_integral_exp_one, hb] at h
  have hepos : (0 : ℝ) < Real.exp 1 := lt_trans (by norm_num) scF_exp_gt_two_sevenths
  nlinarith [h, scF_exp_gt_two_sevenths, hepos, sq_nonneg (Real.exp 1 - 27 / 10),
    mul_nonneg (Real.exp_nonneg (-1 : ℝ)) (Real.exp_nonneg (-1 : ℝ))]

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_inequality_interval`'s `h_mean`.** At `t = 2`
the tail event `{ω 0 = ω 1}` carries `41/50` against the bound
`2e⁻¹ < 41/50` (from `e > 27/10`, i.e. `e⁻¹ < 10/27`). -/
theorem scFence_hoeffding_interval_mean
    (h : (bernPMF scBias scBias_nonneg scBias_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (2 : ℝ) ^ 2
          / ∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2))) : False := by
  have hb : ∑ i : Fin 2, ((1 : ℝ) - (-(1 : ℝ))) ^ 2 = 8 := by
    simp
    norm_num
  rw [scBias_event_mass, hb,
    show (-2 * (2 : ℝ) ^ 2 / 8) = -(1 : ℝ) from by norm_num] at h
  exact absurd (scF_ofReal_le_ofReal' (by norm_num : (0 : ℝ) ≤ 41 / 50)
    (by positivity) h) (not_le.2 scF_two_exp_neg_lt_41_50)

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_inequality`'s `h_mean`.** The same kill at the
uniform-radius form (`a := 1`, bound again `2e⁻¹ < 41/50`). -/
theorem scFence_hoeffding_mean
    (h : (bernPMF scBias scBias_nonneg scBias_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 : ℝ) ^ 2
          / (2 * ∑ i : Fin 2, (1 : ℝ) ^ 2)))) : False := by
  have hb : ∑ i : Fin 2, (1 : ℝ) ^ 2 = 2 := by simp
  rw [scBias_event_mass, hb,
    show -(2 : ℝ) ^ 2 / (2 * 2) = -(1 : ℝ) from by norm_num] at h
  exact absurd (scF_ofReal_le_ofReal' (by norm_num : (0 : ℝ) ≤ 41 / 50)
    (by positivity) h) (not_le.2 scF_two_exp_neg_lt_41_50)

/-- **Fence: `hoeffding_iid`'s `h_mean`.** The same kill at the
identically-distributed form (`n = 2`, `a = 1`). -/
theorem scFence_hoeffding_iid_mean
    (h : (bernPMF scBias scBias_nonneg scBias_le_one).toMeasure
        {ω : (Fin 2) → Bool | |∑ i, scBiasX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 : ℝ) ^ 2
          / (2 * ((2 : ℝ) * (1 : ℝ) ^ 2))))) : False := by
  rw [scBias_event_mass,
    show -(2 : ℝ) ^ 2 / (2 * ((2 : ℝ) * (1 : ℝ) ^ 2)) = -(1 : ℝ) from by norm_num] at h
  exact absurd (scF_ofReal_le_ofReal' (by norm_num : (0 : ℝ) ≤ 41 / 50)
    (by positivity) h) (not_le.2 scF_two_exp_neg_lt_41_50)

/-- The variance-statistic pin at the correlated family: each
coordinate squares to the constant `1`, so the sum is `2`. -/
theorem scCorr_sq_sum :
    ∑ i, ∫ ω : (Fin 2) → Bool, (scCorrX i ω) ^ 2
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 2 := by
  have hint : ∀ i : Fin 2, ∫ ω : (Fin 2) → Bool, (scCorrX i ω) ^ 2
      ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure = 1 := by
    intro i
    have hc : (fun ω : (Fin 2) → Bool => (scCorrX i ω) ^ 2) = fun _ => 1 := by
      funext ω
      cases hw : ω 0 <;> simp [scCorrX, hw]
    rw [hc, integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  rw [Finset.sum_congr rfl (fun i _ => hint i)]
  norm_num

theorem scF_exp_inv_gt_three_tenths : (3 : ℝ) / 10 < Real.exp (-1) := by
  by_contra hcon
  push_neg at hcon
  have h1 : Real.exp 1 * Real.exp (-1) ≤ Real.exp 1 * (3 / 10) :=
    mul_le_mul_of_nonneg_left hcon (Real.exp_nonneg 1)
  have h2 : Real.exp 1 * (3 / 10) < (14 / 5) * (3 / 10) :=
    mul_lt_mul_of_pos_right scF_exp_lt_fourteen_fifths (by norm_num)
  rw [show Real.exp 1 * Real.exp (-1) = 1 from by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]] at h1
  norm_num at h1 h2
  linarith

theorem scF_cosh_gt_three_halves : (3 : ℝ) / 2 < (Real.exp 1 + Real.exp (-1)) / 2 := by
  have h1 : 27 / 10 + 3 / 10 < Real.exp 1 + Real.exp (-1) :=
    add_lt_add scF_exp_gt_two_sevenths scF_exp_inv_gt_three_tenths
  have h2 : (27 : ℝ) / 10 + 3 / 10 = 3 := by norm_num
  linarith

theorem scF_exp_three_tenths_lt_three_halves : Real.exp ((3 : ℝ) / 10) < 3 / 2 := by
  have hL : (Real.exp ((3 : ℝ) / 10)) ^ 3 = Real.exp ((9 : ℝ) / 10) := by
    have hpow : (Real.exp ((3 : ℝ) / 10)) ^ 3
        = Real.exp (3 / 10) * Real.exp (3 / 10) * Real.exp (3 / 10) := by ring
    rw [hpow, ← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num
  have he9 : Real.exp ((9 : ℝ) / 10) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  by_contra hcon
  push_neg at hcon
  have hle : (3 / 2 : ℝ) ^ 3 ≤ (Real.exp ((3 : ℝ) / 10)) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3 / 2) hcon 3
  rw [show (3 / 2 : ℝ) ^ 3 = 27 / 8 from by norm_num, hL] at hle
  linarith [he9, scF_exp_lt_fourteen_fifths]

set_option linter.unusedVariables false in
/-- **Fence: `mgf_sum_le_bernstein`'s `h_indep`.** At the
perfectly-correlated family with `a = 1`, `lam = 1/2`: the MGF is
`cosh 1 = (e + e⁻¹)/2 > 3/2` (from `e > 27/10` and `e⁻¹ > 3/10`, the
latter via `e < 14/5`) while the bound is `exp (3/10) < 3/2` (the
cubing route: `exp(3/10)³ = exp(9/10) < e < 14/5 < 27/8`). The
audit's deferred D1 — the family's priciest single fence, and the
last never-refuted clause of the Bernstein MGF engine. -/
theorem scFence_bernstein_mgf_indep
    (h : ∫ ω : (Fin 2) → Bool, Real.exp ((1 / 2 : ℝ) * ∑ i, scCorrX i ω)
        ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure
      ≤ Real.exp ((1 / 2 : ℝ) ^ 2 * (∑ i : Fin 2, ∫ ω : (Fin 2) → Bool, (scCorrX i ω) ^ 2
            ∂(bernPMF scHalf scHalf_nonneg scHalf_le_one).toMeasure)
          / (2 * (1 - (1 / 2 : ℝ) * (1 : ℝ) / 3)))) : False := by
  have hsum : ∀ ω : (Fin 2) → Bool, (1 / 2 : ℝ) * ∑ i, scCorrX i ω
      = 1 * scCorrX 0 ω := by
    intro ω
    simp only [Fin.sum_univ_two, scCorrX]
    ring
  have hcongr : ∀ ω : (Fin 2) → Bool, Real.exp ((1 / 2 : ℝ) * ∑ i, scCorrX i ω)
      = Real.exp (1 * scCorrX 0 ω) := fun ω => by rw [hsum ω]
  rw [integral_congr_ae (ae_of_all _ fun ω => hcongr ω),
    scCorr_integral_exp 1, scCorr_sq_sum,
    show (1 / 2 : ℝ) ^ 2 * 2 / (2 * (1 - (1 / 2 : ℝ) * (1 : ℝ) / 3)) = 3 / 10 from by
      norm_num] at h
  linarith [scF_cosh_gt_three_halves, scF_exp_three_tenths_lt_three_halves]

end DeferralFences

section MeasurabilityFences

/-!
## The measurability and integrability-guard follow-up

The scalar-concentration audit's last recorded follow-up (its delivery
record, 2026-09-05): the `h_meas` measurability clauses of the MGF
engines and the same-class integrability guards, fenceable only at a
non-measurable fixture. The fixture is the two-point trivial-σ-algebra
space with biased masses `9/10 : 1/10` (the matrix audit's `mcTwoBot`
pattern at the bias the tail kills need): every `⊥`-measurable real
function is constant, so the two-valued breakers below are
non-measurable and not almost-everywhere strongly measurable (both
atoms carry positive mass), and every integral of them evaluates to
the junk zero of `MeasureTheory.integral_undef` — the exact hypothesis
class whose absence made `matrix_azuma_hoeffding` materially false
(Errata §7). Mass lower bounds are all the kills need, so the fixture
avoids the trim-saturation trap entirely (see the follow-up record for
the two deferred siblings that do not).
-/

/-- The two-point trivial-σ-algebra space with biased masses
`9/10 : 1/10`. -/
noncomputable def scM2μ : @MeasureTheory.Measure (Fin 2) (⊥ : MeasurableSpace (Fin 2)) :=
  (9 / 10 : ℝ≥0∞) • @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 0
    + (1 / 10 : ℝ≥0∞) • @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 1

instance : @IsProbabilityMeasure (Fin 2) (⊥ : MeasurableSpace (Fin 2)) scM2μ := by
  constructor
  have h0 : ((9 / 10 : ℝ≥0∞) •
      @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 0) Set.univ
      = 9 / 10 := by
    rw [Measure.smul_apply,
      @Measure.dirac_apply_of_mem (Fin 2) (⊥ : MeasurableSpace (Fin 2)) (s := Set.univ)
        (a := 0) (Set.mem_univ 0)]
    simp
  have h1 : ((1 / 10 : ℝ≥0∞) •
      @MeasureTheory.Measure.dirac (Fin 2) (⊥ : MeasurableSpace (Fin 2)) 1) Set.univ
      = 1 / 10 := by
    rw [Measure.smul_apply,
      @Measure.dirac_apply_of_mem (Fin 2) (⊥ : MeasurableSpace (Fin 2)) (s := Set.univ)
        (a := 1) (Set.mem_univ 1)]
    simp
  show scM2μ Set.univ = 1
  rw [scM2μ, Measure.add_apply, h0, h1]
  rw [ENNReal.div_add_div_same, show ((9 : ℝ≥0∞) + 1) = 10 from by norm_num,
    ENNReal.div_self (by norm_num) (by norm_num)]

theorem scM2μ_ofReal_coe : ENNReal.ofReal (9 / 10 : ℝ) = (9 / 10 : ℝ≥0∞) := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 10)]
  simp

theorem scM2μ_ge_zero (S : Set (Fin 2)) (h0 : (0 : Fin 2) ∈ S) :
    ENNReal.ofReal (9 / 10 : ℝ) ≤ scM2μ S := by
  rw [scM2μ, Measure.add_apply]
  refine le_trans ?_ (le_add_of_nonneg_right (zero_le _))
  rw [Measure.smul_apply,
    @Measure.dirac_apply_of_mem (Fin 2) (⊥ : MeasurableSpace (Fin 2)) (s := S)
      (a := 0) h0, ← scM2μ_ofReal_coe]
  simp

theorem scM2μ_ge_one (S : Set (Fin 2)) (h1 : (1 : Fin 2) ∈ S) :
    (1 / 10 : ℝ≥0∞) ≤ scM2μ S := by
  rw [scM2μ, Measure.add_apply]
  refine le_trans ?_ (le_add_of_nonneg_left (zero_le _))
  rw [Measure.smul_apply,
    @Measure.dirac_apply_of_mem (Fin 2) (⊥ : MeasurableSpace (Fin 2)) (s := S)
      (a := 1) h1]
  simp

theorem scM2μ_pos (j : Fin 2) (S : Set (Fin 2)) (hj : j ∈ S) : 0 < scM2μ S := by
  fin_cases j
  · refine lt_of_lt_of_le ?_ (scM2μ_ge_zero S (by simpa using hj))
    rw [scM2μ_ofReal_coe]
    exact ENNReal.div_pos (by norm_num) (by norm_num)
  · exact lt_of_lt_of_le (ENNReal.div_pos (by norm_num) (by norm_num))
      (scM2μ_ge_one S (by simpa using hj))

/-- On the two-point trivial-σ-algebra space, a two-valued function with
distinct values is not almost-everywhere strongly measurable (both atoms
carry positive mass, so a.e.-equality with a constant — what
`stronglyMeasurable_bot_iff` forces — would make the values agree). The
`mcTwoBot_not_aeSM` pattern, packaged at the biased measure. -/
theorem scM2_not_aeSM {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : Fin 2 → W) (hF : F 0 ≠ F 1) : ¬ AEStronglyMeasurable F scM2μ := by
  intro haes
  obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.1
    (AEStronglyMeasurable.stronglyMeasurable_mk haes)
  have heq : F =ᵐ[scM2μ] (fun _ => c) := haes.ae_eq_mk.trans (by rw [hc])
  have hnull := ae_iff.1 (Filter.EventuallyEq.eventually heq)
  by_cases hc0 : c = F 0
  · have hsub : ({(1 : Fin 2)} : Set (Fin 2))
        ⊆ {ω | ¬ (F ω = c)} := by
      intro ω hω
      simp only [Set.mem_singleton_iff] at hω
      subst ω
      simp only [Set.mem_setOf_eq]
      intro hcon
      exact hF (hcon.trans hc0).symm
    have hmono := measure_mono_null hsub hnull
    have hpos := scM2μ_pos 1 {1} (Set.mem_singleton 1)
    rw [hmono] at hpos
    exact absurd hpos (lt_irrefl (0 : ℝ≥0∞))
  · have hsub : ({(0 : Fin 2)} : Set (Fin 2))
        ⊆ {ω | ¬ (F ω = c)} := by
      intro ω hω
      simp only [Set.mem_singleton_iff] at hω
      subst ω
      simp only [Set.mem_setOf_eq]
      exact fun hcon => hc0 hcon.symm
    have hmono := measure_mono_null hsub hnull
    have hpos := scM2μ_pos 0 {0} (Set.mem_singleton 0)
    rw [hmono] at hpos
    exact absurd hpos (lt_irrefl (0 : ℝ≥0∞))

/-- The two-valued breaker: value `2` on the heavy atom, `0` on the
light one. Non-`⊥`-measurable (nonconstant), not ae-strongly-measurable,
and of junk zero integral. -/
def scM2X (ω : Fin 2) : ℝ := if ω = 0 then 2 else 0

theorem scM2X_vals (j : Fin 2) : scM2X j = if j = 0 then 2 else 0 := rfl

theorem scM2X_zero : scM2X 0 = 2 := by simp [scM2X]

theorem scM2X_one : scM2X 1 = 0 := by simp [scM2X]

theorem scM2X_ne : scM2X 0 ≠ scM2X 1 := by
  rw [scM2X_zero, scM2X_one]
  norm_num

theorem scM2X_not_aeSM : ¬ AEStronglyMeasurable scM2X scM2μ :=
  scM2_not_aeSM _ scM2X_ne

theorem scM2X_not_measurable : ¬ Measurable[(⊥ : MeasurableSpace (Fin 2))] scM2X :=
  fun hm => scM2X_not_aeSM hm.aestronglyMeasurable

theorem scM2X_not_integrable : ¬ Integrable scM2X scM2μ :=
  fun hi => scM2X_not_aeSM hi.aestronglyMeasurable

/-- The single-coordinate breaker family: the dropped `h_meas` clause
genuinely fails. -/
def scM2Fam : Fin 1 → Fin 2 → ℝ := fun _ => scM2X

theorem scM2Fam_not_meas : ¬ ∀ i, Measurable[(⊥ : MeasurableSpace (Fin 2))] (scM2Fam i) :=
  fun hall => scM2X_not_measurable (hall 0)

theorem scM2X_integral : ∫ ω : Fin 2, scM2X ω ∂scM2μ = 0 :=
  integral_undef fun hi => scM2X_not_aeSM hi.aestronglyMeasurable

theorem scM2X_sq_not_aeSM : ¬ AEStronglyMeasurable (fun ω => (scM2X ω) ^ 2) scM2μ := by
  refine scM2_not_aeSM _ ?_
  rw [scM2X_zero, scM2X_one]
  norm_num

theorem scM2X_sq_integral :
    ∫ ω : Fin 2, (scM2X ω - ∫ ω' : Fin 2, scM2X ω' ∂scM2μ) ^ 2 ∂scM2μ = 0 := by
  have hint : ¬ Integrable (fun ω : Fin 2 => (scM2X ω) ^ 2) scM2μ :=
    fun hi => scM2X_sq_not_aeSM hi.aestronglyMeasurable
  rw [scM2X_integral]
  simp only [sub_zero]
  exact integral_undef hint

/-- The `h_mean`-shaped integrals of the breaker family are the junk
zero (`integral_undef` at a non-ae-strongly-measurable integrand) — the
fences' kept centering clauses hold through the junk, recorded as such. -/
theorem scM2Fam_integral (i : Fin 1) :
    ∫ ω : Fin 2, scM2Fam i ω ∂scM2μ = 0 := scM2X_integral

theorem scM2Fam_sq_integral (i : Fin 1) :
    ∫ ω : Fin 2, (scM2Fam i ω - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ) ^ 2 ∂scM2μ = 0 :=
  scM2X_sq_integral

/-- The kept `h_indep` clause is genuine at a single coordinate:
independence over `Fin 1` holds for any family. -/
theorem scM2Fam_iIndepFun_QA :
    iIndepFun (fun _ : Fin 1 => (inferInstance : MeasurableSpace ℝ)) scM2Fam scM2μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hS
  rcases Finset.eq_empty_or_nonempty S with rfl | ⟨a, ha⟩
  · simp
  · have hS : S = {a} := Finset.ext fun x => by
      constructor
      · intro hx
        exact Finset.mem_singleton.2 (Subsingleton.elim x a)
      · intro hx
        rw [Finset.mem_singleton] at hx
        rw [hx]
        exact ha
    rw [hS, Finset.set_biInter_singleton, Finset.prod_singleton]

/-- The empirical breaker: `[0, 1]`-valued lift of the same atom split. -/
def scM2Emp : Fin 1 → Fin 2 → ℝ := fun _ ω => if ω = 0 then 1 else 0

theorem scM2Emp_not_meas : ¬ ∀ i, Measurable[(⊥ : MeasurableSpace (Fin 2))] (scM2Emp i) := by
  intro hall
  have hm : Measurable[(⊥ : MeasurableSpace (Fin 2))] (scM2Emp 0) := hall 0
  refine scM2_not_aeSM (fun ω => scM2Emp 0 ω) ?_ hm.aestronglyMeasurable
  simp [scM2Emp]

theorem scM2Emp_integral (i : Fin 1) :
    ∫ ω : Fin 2, scM2Emp i ω ∂scM2μ = 0 := by
  refine integral_undef fun hi => ?_
  have htwo : (fun ω => scM2Emp i ω) = scM2Emp i := rfl
  refine scM2_not_aeSM (scM2Emp i) ?_ ?_
  · simp [scM2Emp]
  · rw [← htwo]
    exact hi.aestronglyMeasurable

theorem scM2Emp_bound (i : Fin 1) (ω : Fin 2) :
    0 ≤ scM2Emp i ω ∧ scM2Emp i ω ≤ 1 := by
  simp only [scM2Emp]
  by_cases hω : ω = 0 <;> simp [hω]

theorem scM2Fam_abs_le (i : Fin 1) (ω : Fin 2) : |scM2Fam i ω| ≤ 2 := by
  simp only [scM2Fam]
  by_cases hω : ω = 0 <;> simp [scM2X, hω]

/-- Pin: `2e⁻² < 9/10` (from `e > 27/10`). -/
theorem scM_two_exp_neg_two_lt_nine_tenths : 2 * Real.exp (-(2 : ℝ)) < 9 / 10 := by
  have he : (27 : ℝ) / 10 < Real.exp 1 := scF_exp_gt_two_sevenths
  have hpos : (0 : ℝ) < Real.exp 1 := lt_trans (by norm_num) he
  have he2 : Real.exp 1 * Real.exp 1 = Real.exp 2 := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hprod : Real.exp (-(2 : ℝ)) * Real.exp 2 = 1 := by
    rw [← Real.exp_add, show (-(2 : ℝ)) + 2 = 0 from by ring, Real.exp_zero]
  nlinarith [he, he2, hprod, hpos]

/-- Pin: `2e^{-3/2} < 9/10` (from `e³ > 16`). -/
theorem scM_two_exp_neg_three_halves_lt_nine_tenths :
    2 * Real.exp (-((3 : ℝ) / 2)) < 9 / 10 := by
  have hcube : (16 : ℝ) < Real.exp 1 * Real.exp 1 * Real.exp 1 := scF_exp_cube_gt_sixteen
  have hpos : (0 : ℝ) < Real.exp ((3 : ℝ) / 2) := Real.exp_pos _
  have hprod : Real.exp (-((3 : ℝ) / 2)) * Real.exp ((3 : ℝ) / 2) = 1 := by
    rw [← Real.exp_add, show -((3 : ℝ) / 2) + 3 / 2 = 0 from by ring, Real.exp_zero]
  have heee : Real.exp 1 * Real.exp 1 * Real.exp 1 = Real.exp 3 := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hsq : Real.exp ((3 : ℝ) / 2) * Real.exp ((3 : ℝ) / 2) = Real.exp 3 := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [hcube, hprod, hsq, hpos, heee]

/-- **Fence: `measurable_finset_prod'`'s `hf`.** The dropped statement
fails at the breaker family on the one-element index: the product is
the non-measurable breaker itself. -/
theorem scMfence_finset_prod_meas
    (h : Measurable[(⊥ : MeasurableSpace (Fin 2))]
      (∏ i ∈ (Finset.univ : Finset (Fin 1)), scM2Fam i)) : False := by
  rw [Finset.univ_unique, Finset.prod_singleton] at h
  exact scM2X_not_measurable h

/-- **Fence: `measurable_finset_sum'`'s `hf`.** Same kill at the sum. -/
theorem scMfence_finset_sum_meas
    (h : Measurable[(⊥ : MeasurableSpace (Fin 2))]
      (∑ i ∈ (Finset.univ : Finset (Fin 1)), scM2Fam i)) : False := by
  rw [Finset.univ_unique, Finset.sum_singleton] at h
  exact scM2X_not_measurable h

/-- **Fence: `integrable_of_bounded_measurable`'s `h_meas`.** The kept
`h_bound` clause is genuine (`|scM2X| ≤ 2`), the dropped measurability
clause genuinely fails, and the conclusion `Integrable` fails with it. -/
theorem scMfence_integrable_bounded_meas
    (h : Integrable scM2X scM2μ) : False :=
  scM2X_not_integrable h

/-- **Fence: `integrable_sq_sub_mean`'s `h_meas`.** The kept `h_bound`
clause is genuine; the centered square (at the junk zero mean) is the
two-valued `scM2X ^ 2`, not integrable. -/
theorem scMfence_integrable_sq_sub_mean_meas
    (h : Integrable (fun ω => (scM2X ω - ∫ ω' : Fin 2, scM2X ω' ∂scM2μ) ^ 2) scM2μ) : False := by
  simp only [scM2X_integral, sub_zero] at h
  exact scM2X_sq_not_aeSM h.aestronglyMeasurable

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_inequality_interval`'s `h_meas`.** At the breaker
family with `c = 0`, `d = 2`, `t = 2`: the tail event contains the heavy
atom (mass `9/10`) while the bound is `2e⁻² < 9/10`. The kept clauses:
`h_indep` genuine (single coordinate), `h_bound` genuine, `h_mean` through
the junk zero. -/
theorem scMfence_interval_meas
    (h : scM2μ {ω : Fin 2 | |∑ i : Fin 1, scM2Fam i ω| ≥ (2 : ℝ)}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (2 : ℝ) ^ 2 / ∑ i : Fin 1, ((2 : ℝ) - 0) ^ 2))) :
    False := by
  have hmem : (0 : Fin 2) ∈ {ω : Fin 2 | |∑ i : Fin 1, scM2Fam i ω| ≥ (2 : ℝ)} := by
    simp [Fin.sum_univ_one, scM2Fam, scM2X_zero]
  have hmass := scM2μ_ge_zero _ hmem
  refine absurd (le_trans hmass h) (not_le.2 ?_)
  have hsum : ∑ i : Fin 1, ((2 : ℝ) - 0) ^ 2 = 4 := by
    simp
    norm_num
  rw [hsum]
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos (show (0:ℝ) < 2 by norm_num) (Real.exp_pos _)).le).2 ?_
  have hv : (-2 * (2 : ℝ) ^ 2 / 4) = -(2 : ℝ) := by norm_num
  rw [hv]
  exact scM_two_exp_neg_two_lt_nine_tenths

/-- **Fence: `hoeffding_empirical`'s `h_meas`.** At the `[0,1]`-valued
breaker with `t = 1`: the tail event contains the heavy atom against
the bound `2e⁻² < 9/10`. The kept clauses: `h_indep` genuine, `h_bound`
genuine, no centering clause to hold. -/
theorem scMfence_empirical_meas
    (h : scM2μ {ω : Fin 2 | |(1 / (1 : ℝ)) * ∑ i : Fin 1, scM2Emp i ω
          - (1 / (1 : ℝ)) * ∑ i : Fin 1, ∫ ω' : Fin 2, scM2Emp i ω' ∂scM2μ| ≥ (1 : ℝ)}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (1 : ℝ) * (1 : ℝ) ^ 2))) : False := by
  have hmem : (0 : Fin 2) ∈ {ω : Fin 2 | |(1 / (1 : ℝ)) * ∑ i : Fin 1, scM2Emp i ω
      - (1 / (1 : ℝ)) * ∑ i : Fin 1, ∫ ω' : Fin 2, scM2Emp i ω' ∂scM2μ| ≥ (1 : ℝ)} := by
    simp only [Fin.sum_univ_one, scM2Emp_integral]
    simp [scM2Emp]
  have hmass := scM2μ_ge_zero _ hmem
  refine absurd (le_trans hmass h) (not_le.2 ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos (show (0:ℝ) < 2 by norm_num) (Real.exp_pos _)).le).2 ?_
  have hv : (-2 * (1 : ℝ) * (1 : ℝ) ^ 2) = -(2 : ℝ) := by norm_num
  rw [hv]
  exact scM_two_exp_neg_two_lt_nine_tenths

/-- **Fence: `bernstein_inequality`'s `h_meas`.** At the breaker family
with `a = 2`, `t = 2`: the variance statistic is ITSELF the junk zero
(the Errata §7 mechanism at the scalar sibling), so the denominator
collapses to `2at/3` and the bound to `2e^{-3/2} < 9/10` against the
heavy-atom tail. -/
theorem scMfence_bernstein_meas
    (h : scM2μ {ω : Fin 2 | |∑ i : Fin 1, (scM2Fam i ω
            - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ)| ≥ (2 : ℝ)}
      ≤ ENNReal.ofReal (2 * Real.exp (-((2 : ℝ) ^ 2) /
          (2 * ∑ i : Fin 1, ∫ ω : Fin 2, (scM2Fam i ω
              - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ) ^ 2 ∂scM2μ
            + (2 * 2 * 2) / 3)))) : False := by
  have hV : ∑ i : Fin 1, ∫ ω : Fin 2, (scM2Fam i ω
      - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ) ^ 2 ∂scM2μ = 0 := by
    simp [scM2Fam_sq_integral]
  rw [hV] at h
  have hmem : (0 : Fin 2) ∈ {ω : Fin 2 | |∑ i : Fin 1, (scM2Fam i ω
      - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ)| ≥ (2 : ℝ)} := by
    simp only [Fin.sum_univ_one]
    rw [scM2Fam_integral]
    simp [scM2Fam, scM2X_zero]
  have hmass := scM2μ_ge_zero _ hmem
  refine absurd (le_trans hmass h) (not_le.2 ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos (show (0:ℝ) < 2 by norm_num) (Real.exp_pos _)).le).2 ?_
  have hv : (-((2 : ℝ) ^ 2) / (2 * 0 + (2 * 2 * 2) / 3)) = -((3 : ℝ) / 2) := by norm_num
  rw [hv]
  exact scM_two_exp_neg_three_halves_lt_nine_tenths

/-- **Fence: `bernstein_bounded_variance`'s `h_meas`.** Same kill at
`v = 0` (the `h_var` clause holds through the junk zero). -/
theorem scMfence_bounded_variance_meas
    (h : scM2μ {ω : Fin 2 | |∑ i : Fin 1, (scM2Fam i ω
            - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ)| ≥ (2 : ℝ)}
      ≤ ENNReal.ofReal (2 * Real.exp (-((2 : ℝ) ^ 2) / (2 * 0 + (2 * 2 * 2) / 3)))) :
    False := by
  have hmem : (0 : Fin 2) ∈ {ω : Fin 2 | |∑ i : Fin 1, (scM2Fam i ω
      - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ)| ≥ (2 : ℝ)} := by
    simp only [Fin.sum_univ_one]
    rw [scM2Fam_integral]
    simp [scM2Fam, scM2X_zero]
  have hmass := scM2μ_ge_zero _ hmem
  refine absurd (le_trans hmass h) (not_le.2 ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos (show (0:ℝ) < 2 by norm_num) (Real.exp_pos _)).le).2 ?_
  have hv : (-((2 : ℝ) ^ 2) / (2 * 0 + (2 * 2 * 2) / 3)) = -((3 : ℝ) / 2) := by norm_num
  rw [hv]
  exact scM_two_exp_neg_three_halves_lt_nine_tenths

/-- **Fence: `bernstein_iid`'s `h_meas`.** Same kill at `σ² = 0` (the
`h_var` clause holds through the junk zero). -/
theorem scMfence_bernstein_iid_meas
    (h : scM2μ {ω : Fin 2 | |∑ i : Fin 1, (scM2Fam i ω
            - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ)| ≥ (2 : ℝ)}
      ≤ ENNReal.ofReal (2 * Real.exp (-((2 : ℝ) ^ 2) /
          (2 * ((1 : ℝ) * 0) + (2 * 2 * 2) / 3)))) : False := by
  have hmem : (0 : Fin 2) ∈ {ω : Fin 2 | |∑ i : Fin 1, (scM2Fam i ω
      - ∫ ω' : Fin 2, scM2Fam i ω' ∂scM2μ)| ≥ (2 : ℝ)} := by
    simp only [Fin.sum_univ_one]
    rw [scM2Fam_integral]
    simp [scM2Fam, scM2X_zero]
  have hmass := scM2μ_ge_zero _ hmem
  refine absurd (le_trans hmass h) (not_le.2 ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos (show (0:ℝ) < 2 by norm_num) (Real.exp_pos _)).le).2 ?_
  have hv : (-((2 : ℝ) ^ 2) / (2 * ((1 : ℝ) * 0) + (2 * 2 * 2) / 3))
      = -((3 : ℝ) / 2) := by norm_num
  rw [hv]
  exact scM_two_exp_neg_three_halves_lt_nine_tenths

/-- **Fence: `markov_tail_of_mgf`'s `hint`.** The integrability guard of
the Markov engine — the exact clause class that was vacuous in the
Errata §7 repair. At the breaker with `B = 0`, `t = 0`: the MGF
hypothesis holds through the junk zero while the event `{0 ≤ Y}` is all
of `Ω` (measure `1`) against the bound `ofReal 0`. -/
theorem scMfence_markov_integrability
    (h : scM2μ {ω : Fin 2 | (0 : ℝ) ≤ scM2X ω}
      ≤ ENNReal.ofReal (Real.exp (-((1 : ℝ) * 0)) * 0)) : False := by
  have hev : {ω : Fin 2 | (0 : ℝ) ≤ scM2X ω} = Set.univ :=
    Set.eq_univ_of_forall fun ω => by
      by_cases hω : ω = 0 <;> simp [scM2X, hω]
  have hval : Real.exp (-((1 : ℝ) * 0)) * 0 = 0 := by ring
  rw [hev, measure_univ, hval, ENNReal.ofReal_zero] at h
  exact absurd h (by norm_num : ¬((1 : ℝ≥0∞) ≤ 0))

/-- **Fence: `subgaussian_tail_bound`'s `h_int`.** The moment
integrability guard of the subgaussian engine: at the breaker with
`K = 1`, `t = 2` the moment hypothesis holds through the junk zero
while the tail event contains the heavy atom against `2e⁻² < 9/10`. -/
theorem scMfence_subgaussian_int
    (h : scM2μ {ω : Fin 2 | |scM2X ω| ≥ (2 : ℝ)}
      ≤ ENNReal.ofReal (2 * Real.exp (-((2 : ℝ) ^ 2) / (2 * (1 : ℝ) ^ 2)))) : False := by
  have hmem : (0 : Fin 2) ∈ {ω : Fin 2 | |scM2X ω| ≥ (2 : ℝ)} := by
    simp [scM2X_zero]
  have hmass := scM2μ_ge_zero _ hmem
  refine absurd (le_trans hmass h) (not_le.2 ?_)
  refine (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_pos (show (0:ℝ) < 2 by norm_num) (Real.exp_pos _)).le).2 ?_
  have hv : (-((2 : ℝ) ^ 2) / (2 * (1 : ℝ) ^ 2)) = -(2 : ℝ) := by norm_num
  rw [hv]
  exact scM_two_exp_neg_two_lt_nine_tenths

end MeasurabilityFences

section SaturationFences

/-!
## The trim-saturation deferral closure

The `MeasurabilityFences` follow-up deferred `hoeffding_inequality`'s
and `hoeffding_iid`'s `h_meas` on the priced trim-saturation mechanism:
on a trivial σ-algebra, exact masses of non-measurable sets are
saturated upward, which blocked the independence equality. This
section takes the priced route: the saturation itself becomes the
lemma (`scM_dirac_bot_eq_one`, via `measure_eq_iInf` — the value of a
Dirac measure at any set is the infimum over its measurable supersets,
and on `⊥` the only measurable superset of a nonempty set is `univ`).
On the saturated space every nonempty set has measure exactly `1`, so
the four-cell-partition family below is genuinely independent (every
pair of nonempty preimages intersects, hence both sides of every
independence equality are `1` or `0`), and the two deferred fences
land with the on-file pin `2e⁻¹ < 1`.
-/

/-- **Saturation lemma.** On the trivial σ-algebra, a Dirac measure's
total function sends every nonempty set to `1`: by `measure_eq_iInf`
the value is the infimum over measurable supersets, and the only
`⊥`-measurable superset of a nonempty set is `univ`. -/
theorem scM_dirac_bot_eq_one {α : Type*} (a : α) {s : Set α} (hs : s.Nonempty) :
    @Measure.dirac α (⊥ : MeasurableSpace α) a s = 1 := by
  have hUniv : @Measure.dirac α (⊥ : MeasurableSpace α) a Set.univ = 1 :=
    @Measure.dirac_apply_of_mem α (⊥ : MeasurableSpace α) Set.univ a (Set.mem_univ a)
  rw [@measure_eq_iInf α (⊥ : MeasurableSpace α)
    (@Measure.dirac α (⊥ : MeasurableSpace α) a) s]
  refine le_antisymm ?_ ?_
  · exact iInf_le_of_le Set.univ (iInf_le_of_le s.subset_univ
      (iInf_le_of_le (@MeasurableSet.univ α (⊥ : MeasurableSpace α))
        (le_of_eq hUniv)))
  · refine le_iInf fun t => le_iInf fun hsub => le_iInf fun hmeas => ?_
    rcases MeasurableSpace.measurableSet_bot_iff.1 hmeas with rfl | rfl
    · exact (hs.not_subset_empty hsub).elim
    · exact hUniv.ge

/-- The four-point trivial-σ-algebra saturated space. -/
noncomputable def scM4μ : @MeasureTheory.Measure (Fin 4) (⊥ : MeasurableSpace (Fin 4)) :=
  @Measure.dirac (Fin 4) (⊥ : MeasurableSpace (Fin 4)) 0

instance : @IsProbabilityMeasure (Fin 4) (⊥ : MeasurableSpace (Fin 4)) scM4μ :=
  ⟨@Measure.dirac_apply_of_mem (Fin 4) (⊥ : MeasurableSpace (Fin 4)) Set.univ 0
    (Set.mem_univ 0)⟩

theorem scM4μ_sat (S : Set (Fin 4)) (hS : S.Nonempty) : scM4μ S = 1 :=
  scM_dirac_bot_eq_one 0 hS

/-- On the saturated space, a function taking distinct values at two
points is not almost-everywhere strongly measurable (each point carries
full saturated mass, so a.e.-equality with a constant — what
`stronglyMeasurable_bot_iff` forces — would make the values agree). -/
theorem scM4_not_aeSM {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (F : Fin 4 → W) (p q : Fin 4) (hF : F p ≠ F q) :
    ¬ AEStronglyMeasurable F scM4μ := by
  intro haes
  obtain ⟨c, hc⟩ := stronglyMeasurable_bot_iff.1
    (AEStronglyMeasurable.stronglyMeasurable_mk haes)
  have heq : F =ᵐ[scM4μ] (fun _ => c) := haes.ae_eq_mk.trans (by rw [hc])
  have hnull := ae_iff.1 (Filter.EventuallyEq.eventually heq)
  by_cases hcp : c = F p
  · have hsub : ({q} : Set (Fin 4)) ⊆ {ω | ¬ (F ω = c)} := by
      intro ω hω
      simp only [Set.mem_singleton_iff] at hω
      subst ω
      simp only [Set.mem_setOf_eq]
      intro hcon
      exact hF (hcon.trans hcp).symm
    have hzero := measure_mono_null hsub hnull
    have hfull : scM4μ ({q} : Set (Fin 4)) = 1 := scM4μ_sat _ ⟨q, rfl⟩
    rw [hzero] at hfull
    exact one_ne_zero hfull.symm
  · have hsub : ({p} : Set (Fin 4)) ⊆ {ω | ¬ (F ω = c)} := by
      intro ω hω
      simp only [Set.mem_singleton_iff] at hω
      subst ω
      simp only [Set.mem_setOf_eq]
      exact fun hcon => hcp hcon.symm
    have hzero := measure_mono_null hsub hnull
    have hfull : scM4μ ({p} : Set (Fin 4)) = 1 := scM4μ_sat _ ⟨p, rfl⟩
    rw [hzero] at hfull
    exact one_ne_zero hfull.symm

/-- The two cells of the four-cell partition design: `A = {0, 1}` and
`B = {0, 2}`, so all four intersections `A ∩ B = {0}`, `A ∩ Bᶜ = {1}`,
`Aᶜ ∩ B = {2}`, `Aᶜ ∩ Bᶜ = {3}` are nonempty. -/
def scM4A : Set (Fin 4) := {ω | ω ≤ 1}
def scM4B : Set (Fin 4) := {ω | ω = 0 ∨ ω = 2}

theorem scM4A_zero : (0 : Fin 4) ∈ scM4A := by simp [scM4A]
theorem scM4A_one : (1 : Fin 4) ∈ scM4A := by simp [scM4A]
theorem scM4A_not_two : (2 : Fin 4) ∉ scM4A := by simp [scM4A]
theorem scM4A_not_three : (3 : Fin 4) ∉ scM4A := by simp [scM4A]
theorem scM4B_zero : (0 : Fin 4) ∈ scM4B := by simp [scM4B]
theorem scM4B_two : (2 : Fin 4) ∈ scM4B := by simp [scM4B]
theorem scM4B_not_one : (1 : Fin 4) ∉ scM4B := by simp [scM4B]
theorem scM4B_not_three : (3 : Fin 4) ∉ scM4B := by simp [scM4B]

/-- The breaker coordinates: `X₀ = 2·1_A`, `X₁ = 2·1_B` (the cell
predicates spelled decibaly so the value definitions elaborate). -/
def scM4X0 (ω : Fin 4) : ℝ := if ω ≤ 1 then 2 else 0
def scM4X1 (ω : Fin 4) : ℝ := if ω = 0 ∨ ω = 2 then 2 else 0
def scM4X : Fin 2 → Fin 4 → ℝ := ![scM4X0, scM4X1]

theorem scM4X_zero : scM4X 0 = scM4X0 := rfl
theorem scM4X_one : scM4X 1 = scM4X1 := rfl

theorem scM4X0_point : scM4X0 0 = 2 := by simp [scM4X0]
theorem scM4X0_point' : scM4X0 2 = 0 := by simp [scM4X0]
theorem scM4X1_point : scM4X1 0 = 2 := by simp [scM4X1]
theorem scM4X1_point' : scM4X1 1 = 0 := by simp [scM4X1]

theorem scM4X0_ne : scM4X0 0 ≠ scM4X0 2 := by
  rw [scM4X0_point, scM4X0_point']
  norm_num

theorem scM4X1_ne : scM4X1 0 ≠ scM4X1 1 := by
  rw [scM4X1_point, scM4X1_point']
  norm_num

theorem scM4X0_not_aeSM : ¬ AEStronglyMeasurable scM4X0 scM4μ :=
  scM4_not_aeSM _ 0 2 scM4X0_ne

theorem scM4X1_not_aeSM : ¬ AEStronglyMeasurable scM4X1 scM4μ :=
  scM4_not_aeSM _ 0 1 scM4X1_ne

/-- The dropped `h_meas` clause genuinely fails: neither coordinate is
`⊥`-measurable (both are nonconstant). -/
theorem scM4X_not_meas : ¬ ∀ i, Measurable[(⊥ : MeasurableSpace (Fin 4))] (scM4X i) :=
  fun hall => scM4X0_not_aeSM (hall 0).aestronglyMeasurable

/-- The `h_mean`-shaped integrals are the junk zero (recorded as such —
the fences' kept centering clauses hold through the junk). -/
theorem scM4X_integral (i : Fin 2) :
    ∫ ω : Fin 4, scM4X i ω ∂scM4μ = 0 := by
  fin_cases i
  · exact integral_undef fun hi => scM4X0_not_aeSM hi.aestronglyMeasurable
  · exact integral_undef fun hi => scM4X1_not_aeSM hi.aestronglyMeasurable

theorem scM4X_abs_le (i : Fin 2) (ω : Fin 4) : |scM4X i ω| ≤ 2 := by
  fin_cases i
  · by_cases h : ω ≤ 1
    · simp [scM4X_zero, scM4X0, h]
    · simp [scM4X_zero, scM4X0, h]
  · by_cases h : ω = 0 ∨ ω = 2
    · simp [scM4X_one, scM4X1, h]
    · simp [scM4X_one, scM4X1, h]

/-- Every nonempty preimage pair of the two coordinates intersects:
on the four cells the value pairs are `(2,2)`, `(2,0)`, `(0,2)`,
`(0,0)`, so whichever values land in `S` and `T`, some cell is inside
both preimages. -/
theorem scM4X_indep_hint (S T : Set ℝ)
    (h1 : (scM4X0 ⁻¹' S).Nonempty) (h2 : (scM4X1 ⁻¹' T).Nonempty) :
    (scM4X0 ⁻¹' S ∩ scM4X1 ⁻¹' T).Nonempty := by
  have hf : (2 : ℝ) ∈ S ∨ (0 : ℝ) ∈ S := by
    obtain ⟨ω, hω⟩ := h1
    simp only [Set.mem_preimage, scM4X0] at hω
    by_cases h : ω ≤ 1
    · exact Or.inl (by rw [if_pos h] at hω; exact hω)
    · exact Or.inr (by rw [if_neg h] at hω; exact hω)
  have hg : (2 : ℝ) ∈ T ∨ (0 : ℝ) ∈ T := by
    obtain ⟨ω, hω⟩ := h2
    simp only [Set.mem_preimage, scM4X1] at hω
    by_cases h : ω = 0 ∨ ω = 2
    · exact Or.inl (by rw [if_pos h] at hω; exact hω)
    · exact Or.inr (by rw [if_neg h] at hω; exact hω)
  rcases hf with h2S | h0S <;> rcases hg with h2T | h0T
  · exact ⟨0, by simp [Set.mem_inter_iff, Set.mem_preimage, scM4X0, scM4X1, h2S, h2T]⟩
  · exact ⟨1, by simp [Set.mem_inter_iff, Set.mem_preimage, scM4X0, scM4X1, h2S, h0T]⟩
  · exact ⟨2, by simp [Set.mem_inter_iff, Set.mem_preimage, scM4X0, scM4X1, h0S, h2T]⟩
  · exact ⟨3, by simp [Set.mem_inter_iff, Set.mem_preimage, scM4X0, scM4X1, h0S, h0T]⟩

/-- Independence on a saturated measure: every pair of nonempty
preimages intersects, so both sides of every independence equality are
`1` (or `0` through the empty side). -/
theorem scM_indepFun_of_saturated {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (hsat : ∀ S : Set Ω, S.Nonempty → μ S = 1) (f g : Ω → ℝ)
    (hint : ∀ S T : Set ℝ, (f ⁻¹' S).Nonempty → (g ⁻¹' T).Nonempty →
      (f ⁻¹' S ∩ g ⁻¹' T).Nonempty) :
    IndepFun f g μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  rcases Set.eq_empty_or_nonempty (f ⁻¹' s) with h1 | h1
  · rw [h1, Set.empty_inter, measure_empty]
    simp
  rcases Set.eq_empty_or_nonempty (g ⁻¹' t) with h2 | h2
  · rw [h2, Set.inter_empty, measure_empty]
    simp
  rw [hsat _ (hint s t h1 h2), hsat _ h1, hsat _ h2]
  ring

/-- The kept `h_indep` clause is genuine: the four-cell family is
mutually independent on the saturated space. -/
theorem scM4X_iIndepFun_QA :
    iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace ℝ)) scM4X scM4μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp
  rcases (S.erase a).eq_empty_or_nonempty with h | ⟨b, hb⟩
  · rw [← Finset.insert_erase ha, h,
      Finset.set_biInter_insert a ∅ (fun i => scM4X i ⁻¹' sets i),
      Finset.prod_insert (by simp : a ∉ (∅ : Finset (Fin 2)))]
    simp
  · have hba : b ≠ a := (Finset.mem_erase.1 hb).1
    have hsub : (Finset.univ : Finset (Fin 2)) ⊆ S := by
      intro x _
      fin_cases x <;> fin_cases a <;> fin_cases b <;> simp_all [ha, hb, hba]
    have hfull : S = Finset.univ := Finset.univ_subset_iff.mp hsub
    have hind : IndepFun scM4X0 scM4X1 scM4μ :=
      scM_indepFun_of_saturated scM4μ_sat scM4X0 scM4X1 scM4X_indep_hint
    have huniv : (Finset.univ : Finset (Fin 2)) = insert 0 {1} := by decide
    rw [hfull, huniv]
    have hm0 : MeasurableSet (sets 0) := hS 0 (by rw [hfull]; exact Finset.mem_univ _)
    have hm1 : MeasurableSet (sets 1) := hS 1 (by rw [hfull]; exact Finset.mem_univ _)
    have hfinal := hind.measure_inter_preimage_eq_mul (sets 0) (sets 1) hm0 hm1
    simp only [Finset.set_biInter_insert, Finset.set_biInter_singleton,
      Set.inter_univ]
    rw [Finset.prod_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
      Finset.prod_singleton]
    exact hfinal

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_inequality`'s `h_meas`** — the follow-up's
deferred sibling, closed by the saturation route. At the four-cell
family with `a = 2`, `t = 4`: the tail event `A ∩ B = {0}` is
nonempty, hence of saturated measure `1`, against the bound
`2exp(−16/16) = 2e⁻¹ < 1` (on-file pin). The kept clauses:
`h_indep` genuine (the saturated-independence lemma at the four-cell
partition), `h_bound` genuine (`|X i ω| ≤ 2`), `h_mean` through the
junk zero, `ht` genuine. -/
theorem scMfence_hoeffding_meas
    (h : scM4μ {ω : Fin 4 | |∑ i : Fin 2, scM4X i ω| ≥ (4 : ℝ)}
      ≤ ENNReal.ofReal (2 * Real.exp (-((4 : ℝ) ^ 2)
          / (2 * ∑ i : Fin 2, (2 : ℝ) ^ 2)))) : False := by
  have hmem : (0 : Fin 4) ∈ {ω : Fin 4 | |∑ i : Fin 2, scM4X i ω| ≥ (4 : ℝ)} := by
    have hvals : ∑ i : Fin 2, scM4X i (0 : Fin 4) = 4 := by
      simp only [Fin.sum_univ_two]
      rw [scM4X_zero, scM4X_one, scM4X0_point, scM4X1_point]
      norm_num
    simp only [Set.mem_setOf_eq]
    rw [hvals]
    norm_num
  rw [scM4μ_sat _ ⟨0, hmem⟩] at h
  have hsum : ∑ i : Fin 2, (2 : ℝ) ^ 2 = 8 := by
    rw [Fin.sum_univ_two]
    norm_num
  rw [hsum, show (-((4 : ℝ) ^ 2) / (2 * 8)) = -(1 : ℝ) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_lt_one)

set_option linter.unusedVariables false in
/-- **Fence: `hoeffding_iid`'s `h_meas`** — the second deferred sibling,
same fixture and kill (the iid denominator `2·(n·a²)` also evaluates to
`16`). -/
theorem scMfence_hoeffding_iid_meas
    (h : scM4μ {ω : Fin 4 | |∑ i : Fin 2, scM4X i ω| ≥ (4 : ℝ)}
      ≤ ENNReal.ofReal (2 * Real.exp (-((4 : ℝ) ^ 2)
          / (2 * ((2 : ℝ) * (2 : ℝ) ^ 2))))) : False := by
  have hmem : (0 : Fin 4) ∈ {ω : Fin 4 | |∑ i : Fin 2, scM4X i ω| ≥ (4 : ℝ)} := by
    have hvals : ∑ i : Fin 2, scM4X i (0 : Fin 4) = 4 := by
      simp only [Fin.sum_univ_two]
      rw [scM4X_zero, scM4X_one, scM4X0_point, scM4X1_point]
      norm_num
    simp only [Set.mem_setOf_eq]
    rw [hvals]
    norm_num
  rw [scM4μ_sat _ ⟨0, hmem⟩] at h
  rw [show (-((4 : ℝ) ^ 2) / (2 * ((2 : ℝ) * (2 : ℝ) ^ 2))) = -(1 : ℝ) from by norm_num,
    ENNReal.one_le_ofReal] at h
  exact absurd h (not_le.2 scF_two_exp_neg_lt_one)

end SaturationFences

end Scaffold.Mathlib.Probability.Concentration.Scalar.QA
