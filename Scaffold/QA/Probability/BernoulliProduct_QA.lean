/-
  BernoulliProduct_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Probability.BernoulliProduct`: the
  independent-Bernoulli product sampling space (Step 1, Slice 1 of the
  leverage-score sparsification program).

  The pins run on the fixture `ι = Fin 2` at `p = ![1/2, 1/3]`, with the
  four-atom enumeration of `Fin 2 → Bool` as the independent raw route
  against the module's ∑-∏ machinery; the degenerate `Fin 1` fixtures
  carry the two hypothesis fences.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove any axiom (this module admits none); it checks that the
  sampling-space interfaces return the classical numbers.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Probability.BernoulliProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix.L2OpNorm

namespace Scaffold.Mathlib.Probability.BernoulliProduct.QA

open Scaffold.Mathlib.Probability.BernoulliProduct

/-!
## The `Fin 2` fixture and its raw-route machinery
-/

/-- The QA fixture probability vector. -/
noncomputable def p12 : Fin 2 → ℝ := ![1/2, 1/3]

theorem p12_le_one : ∀ i, p12 i ≤ 1 := by
  intro i; fin_cases i <;> norm_num [p12]

theorem p12_nonneg : ∀ i, 0 ≤ p12 i := by
  intro i; fin_cases i <;> norm_num [p12]

/-- The four-atom enumeration of the sampling space. -/
theorem univ_fin2_bool :
    (Finset.univ : Finset (Fin 2 → Bool))
      = {![false, false], ![false, true], ![true, false], ![true, true]} := by
  ext ω
  cases h0 : ω 0 <;> cases h1 : ω 1 <;>
    simp [Set.mem_singleton_iff, Set.mem_insert_iff, funext_iff, h0, h1]
  · exact Or.inl fun x => by fin_cases x <;> simp [h0, h1]
  · exact Or.inr (Or.inl fun x => by fin_cases x <;> simp [h0, h1])
  · exact Or.inr (Or.inr (Or.inl fun x => by fin_cases x <;> simp [h0, h1]))
  · exact Or.inr (Or.inr (Or.inr fun x => by fin_cases x <;> simp [h0, h1]))

/-- The six pairwise atom disequalities, shared by every raw-route
enumeration below. -/
private theorem bp_ne_ff_ft : (![false, false] : Fin 2 → Bool) ≠ ![false, true] := fun he =>
  absurd (congrFun he 1) (by decide)

private theorem bp_ne_ff_tf : (![false, false] : Fin 2 → Bool) ≠ ![true, false] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem bp_ne_ff_tt : (![false, false] : Fin 2 → Bool) ≠ ![true, true] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem bp_ne_ft_tf : (![false, true] : Fin 2 → Bool) ≠ ![true, false] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem bp_ne_ft_tt : (![false, true] : Fin 2 → Bool) ≠ ![true, true] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem bp_ne_tf_tt : (![true, false] : Fin 2 → Bool) ≠ ![true, true] := fun he =>
  absurd (congrFun he 1) (by decide)

/-!
## The product structure pinned
-/

/-- The four joint-mass values of the fixture, computed raw from the
coordinate masses (no ∑-∏ machinery). -/
theorem bp_mass_ff_QA : jointMass p12 ![false, false] = ENNReal.ofReal ((1 : ℝ) / 3) := by
  have h : jointMass p12 ![false, false]
      = ENNReal.ofReal ((1 : ℝ) - 1 / 2) * ENNReal.ofReal ((1 : ℝ) - 1 / 3) := by
    simp [jointMass, bern, p12]
  rw [h, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; norm_num

theorem bp_mass_ft_QA : jointMass p12 ![false, true] = ENNReal.ofReal ((1 : ℝ) / 6) := by
  have h : jointMass p12 ![false, true]
      = ENNReal.ofReal ((1 : ℝ) - 1 / 2) * ENNReal.ofReal ((1 : ℝ) / 3) := by
    simp [jointMass, bern, p12]
  rw [h, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; norm_num

theorem bp_mass_tf_QA : jointMass p12 ![true, false] = ENNReal.ofReal ((1 : ℝ) / 3) := by
  have h : jointMass p12 ![true, false]
      = ENNReal.ofReal ((1 : ℝ) / 2) * ENNReal.ofReal ((1 : ℝ) - 1 / 3) := by
    simp [jointMass, bern, p12]
  rw [h, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; norm_num

theorem bp_mass_tt_QA : jointMass p12 ![true, true] = ENNReal.ofReal ((1 : ℝ) / 6) := by
  have h : jointMass p12 ![true, true]
      = ENNReal.ofReal ((1 : ℝ) / 2) * ENNReal.ofReal ((1 : ℝ) / 3) := by
    simp [jointMass, bern, p12]
  rw [h, ← ENNReal.ofReal_mul (by norm_num)]; congr 1; norm_num

/-- Total mass `1` by the theorem. -/
theorem bp_total_mass_theorem_QA :
    ∑ ω : Fin 2 → Bool, jointMass p12 ω = 1 :=
  sum_jointMass_eq_one p12 p12_nonneg p12_le_one

/-- Total mass `1` by raw four-atom enumeration — the independent
route (no ∑-∏ swap anywhere). -/
theorem bp_total_mass_raw_QA :
    ∑ ω : Fin 2 → Bool, jointMass p12 ω = 1 := by
  rw [univ_fin2_bool, Finset.sum_insert (by simp [bp_ne_ff_ft, bp_ne_ff_tf, bp_ne_ff_tt]),
    Finset.sum_insert (by simp [bp_ne_ft_tf, bp_ne_ft_tt]),
    Finset.sum_insert (by simp [bp_ne_tf_tt]), Finset.sum_singleton,
    bp_mass_ff_QA, bp_mass_ft_QA, bp_mass_tf_QA, bp_mass_tt_QA]
  have m1 : ENNReal.ofReal ((1 : ℝ) / 3) + ENNReal.ofReal ((1 : ℝ) / 6)
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; congr 1; norm_num
  have m2 : ENNReal.ofReal ((1 : ℝ) / 6) + ENNReal.ofReal ((1 : ℝ) / 2)
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; congr 1; norm_num
  have m3 : ENNReal.ofReal ((1 : ℝ) / 3) + ENNReal.ofReal ((2 : ℝ) / 3)
      = ENNReal.ofReal (1 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; congr 1; norm_num
  rw [m1, m2, m3, ENNReal.ofReal_one]

/-- The one-coordinate marginal at coordinate `0`: the theorem's value
`p 0 = 1/2`, with the Bool-side sum computed raw. -/
theorem bp_marginal_QA :
    ∑ ω : Fin 2 → Bool, (if ω 0 then (1 : ℝ≥0∞) else 0) * jointMass p12 ω
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  rw [sum_coord_mul p12 p12_nonneg p12_le_one 0 (fun b => if b then 1 else 0)]
  have hb : (Finset.univ : Finset Bool) = {false, true} := by
    ext b; cases b <;> simp
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [bern, p12]

/-- The cylinder measure `{ω | ω 1 = true}` is the Bernoulli mass
`p 1 = 1/3`, by the cylinder theorem with the Bool-side sum raw. -/
theorem bp_measure_cyl_QA :
    (bernPMF p12 p12_nonneg p12_le_one).toMeasure {ω : Fin 2 → Bool | ω 1 = true}
      = ENNReal.ofReal ((1 : ℝ) / 3) := by
  have hset : {ω : Fin 2 → Bool | ω 1 = true} = (fun ω : Fin 2 → Bool => ω 1) ⁻¹' {true} := by
    ext ω; simp [Set.mem_singleton_iff]
  rw [hset, toMeasure_cyl p12 p12_nonneg p12_le_one 1 {true}]
  have hb : (Finset.univ : Finset Bool) = {false, true} := by
    ext b; cases b <;> simp
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [bern, p12]

/-- The complementary cylinder `{ω | ω 1 = false}` at `1 - p 1 = 2/3`. -/
theorem bp_measure_cyl_false_QA :
    (bernPMF p12 p12_nonneg p12_le_one).toMeasure {ω : Fin 2 → Bool | ω 1 = false}
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
  have hset : {ω : Fin 2 → Bool | ω 1 = false} = (fun ω : Fin 2 → Bool => ω 1) ⁻¹' {false} := by
    ext ω; simp [Set.mem_singleton_iff]
  rw [hset, toMeasure_cyl p12 p12_nonneg p12_le_one 1 {false}]
  have hb : (Finset.univ : Finset Bool) = {false, true} := by
    ext b; cases b <;> simp
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
  have h2 : bern p12 1 false = ENNReal.ofReal ((2 : ℝ) / 3) := by
    simp only [bern, p12, Matrix.cons_val_one, Bool.false_eq_true, if_false]
    congr 1; norm_num
  rw [h2]; simp

/-- The coordinate-`0` cylinder `{ω | ω 0 = true}` at `p 0 = 1/2`. -/
theorem bp_measure_cyl0_QA :
    (bernPMF p12 p12_nonneg p12_le_one).toMeasure {ω : Fin 2 → Bool | ω 0 = true}
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hset : {ω : Fin 2 → Bool | ω 0 = true} = (fun ω : Fin 2 → Bool => ω 0) ⁻¹' {true} := by
    ext ω; simp [Set.mem_singleton_iff]
  rw [hset, toMeasure_cyl p12 p12_nonneg p12_le_one 0 {true}]
  have hb : (Finset.univ : Finset Bool) = {false, true} := by
    ext b; cases b <;> simp
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [bern, p12]

/-- Independence pinned numerically, theorem route: the intersection
measure `{ω 0 = true} ∩ {ω 1 = false}` splits as the product of the
cylinder measures, `1/2 · 2/3 = 1/3`. -/
theorem bp_indep_numeric_QA :
    (bernPMF p12 p12_nonneg p12_le_one).toMeasure
        ({ω : Fin 2 → Bool | ω 0 = true} ∩ {ω : Fin 2 → Bool | ω 1 = false})
      = ENNReal.ofReal ((1 : ℝ) / 3) := by
  have h01 : (0 : Fin 2) ≠ 1 := by norm_num
  have hpre : ({ω : Fin 2 → Bool | ω 0 = true} ∩ {ω : Fin 2 → Bool | ω 1 = false})
      = (fun ω : Fin 2 → Bool => ω 0) ⁻¹' {true} ∩ (fun ω : Fin 2 → Bool => ω 1) ⁻¹' {false} := by
    ext ω; simp [Set.mem_setOf_eq, Set.mem_singleton_iff]
  have hsplit := (indepFun_iff_measure_inter_preimage_eq_mul.mp
    (indepFun_coord p12 p12_nonneg p12_le_one h01)) {true} {false}
    ((Set.toFinite {true} : Set.Finite _).measurableSet)
    ((Set.toFinite {false} : Set.Finite _).measurableSet)
  have h0 : (fun ω : Fin 2 → Bool => ω 0) ⁻¹' {true} = {ω : Fin 2 → Bool | ω 0 = true} := by
    ext ω; simp [Set.mem_singleton_iff]
  have h1 : (fun ω : Fin 2 → Bool => ω 1) ⁻¹' {false} = {ω : Fin 2 → Bool | ω 1 = false} := by
    ext ω; simp [Set.mem_singleton_iff]
  rw [hpre, hsplit, h0, h1, bp_measure_cyl0_QA, bp_measure_cyl_false_QA,
    ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; norm_num

/-!
## The centering integrals pinned
-/

/-- The centering integral `∫ δ_1 ∂μ = p 1 = 1/3`, by the theorem. -/
theorem bp_integral_delta_QA :
    ∫ ω : Fin 2 → Bool, (if ω 1 then (1 : ℝ) else 0)
      ∂(bernPMF p12 p12_nonneg p12_le_one).toMeasure = 1 / 3 :=
  integral_delta p12 p12_nonneg p12_le_one 1

/-- The same centering integral by raw enumeration: the two true-at-`1`
atoms carry real mass `1/6 + 1/6`, computed through
`PMF.integral_eq_sum` with no `integral_delta` input. -/
theorem bp_integral_delta_raw_QA :
    ∫ ω : Fin 2 → Bool, (if ω 1 then (1 : ℝ) else 0)
      ∂(bernPMF p12 p12_nonneg p12_le_one).toMeasure = 1 / 3 := by
  rw [PMF.integral_eq_sum, univ_fin2_bool,
    Finset.sum_insert (by simp [bp_ne_ff_ft, bp_ne_ff_tf, bp_ne_ff_tt]),
    Finset.sum_insert (by simp [bp_ne_ft_tf, bp_ne_ft_tt]),
    Finset.sum_insert (by simp [bp_ne_tf_tt]), Finset.sum_singleton]
  simp [bernPMF_apply, bp_mass_ff_QA, bp_mass_ft_QA, bp_mass_tf_QA, bp_mass_tt_QA]
  norm_num

/-!
## The matrix layer
-/

/-- The QA matrix family: `!![1,2;3,4]` at `true`, zero at `false`. -/
noncomputable def bpMat (b : Bool) : Matrix (Fin 2) (Fin 2) ℝ :=
  if b then !![1, 2; 3, 4] else 0

theorem bp_measurable_matrix_QA :
    Measurable fun ω : Fin 2 → Bool => bpMat (ω 0) :=
  measurable_coord_matrix bpMat 0

theorem bp_stronglyMeasurable_matrix_QA :
    StronglyMeasurable fun ω : Fin 2 → Bool => bpMat (ω 0) :=
  stronglyMeasurable_coord_matrix bpMat 0

theorem bp_indepFun_matrix_QA :
    IndepFun (fun ω : Fin 2 → Bool => bpMat (ω 0))
      (fun ω : Fin 2 → Bool => bpMat (ω 1))
      (bernPMF p12 p12_nonneg p12_le_one).toMeasure :=
  indepFun_coord_matrix p12 p12_nonneg p12_le_one bpMat bpMat (by norm_num)

/-- The matrix centering building block pinned numerically: the scalar
Bernoulli factor smuling the fixed matrix integrates to `p 0 • M`. -/
theorem bp_integral_smul_matrix_QA :
    ∫ ω : Fin 2 → Bool, (if ω 0 then (1 : ℝ) else 0) • (bpMat true)
      ∂(bernPMF p12 p12_nonneg p12_le_one).toMeasure
      = ((1 : ℝ) / 2) • (bpMat true) := by
  simpa only [p12, Matrix.cons_val_zero] using
      integral_coord_smul p12 p12_nonneg p12_le_one 0 (bpMat true)

/-- The centered affine combination integrates to zero at `p 1 = 1/3 ≠ 0`
— the exact `h_mean` clause shape of `matrix_bernstein` at the matrix
codomain, on a concrete matrix. -/
theorem bp_integral_center_matrix_QA :
    ∫ ω : Fin 2 → Bool, ((if ω 1 then (1 : ℝ) else 0) / (1 / 3) - 1) • (bpMat true)
      ∂(bernPMF p12 p12_nonneg p12_le_one).toMeasure = 0 := by
  have hp1 : p12 1 ≠ 0 := by simp [p12]
  have h := integral_coord_center_smul p12 p12_nonneg p12_le_one hp1 (bpMat true)
  rwa [show p12 1 = 1 / 3 from rfl] at h

/-!
## Fences
-/

/-- **Fence: the `[0,1]` bounds are load-bearing for the mass
normalization.** At `p 0 = 2 > 1` the joint masses sum to `2`, not
`1` — `bernPMF`'s hypotheses `hp0 hp1` cannot be discharged, and the
degenerate `ofReal (1 - 2) = 0` atom makes the failure visible. -/
theorem bp_out_of_bounds_fence_QA :
    ∑ ω : (Fin 1 → Bool), jointMass ![2] ω ≠ 1 := by
  have hne : (![false] : Fin 1 → Bool) ≠ ![true] := fun he =>
    absurd (congrFun he 0) (by decide)
  have huniv : (Finset.univ : Finset (Fin 1 → Bool))
      = {![false], ![true]} := by
    ext ω
    cases h : ω 0 <;> simp [Set.mem_singleton_iff, Set.mem_insert_iff, funext_iff, h]
    · exact Or.inl fun x => by fin_cases x; simp [h]
    · exact Or.inr fun x => by fin_cases x; simp [h]
  have hf : jointMass ![2] ![false] = ENNReal.ofReal ((1 : ℝ) - 2) := by
    simp [jointMass, bern, Fin.prod_univ_one]
  have ht : jointMass ![2] ![true] = ENNReal.ofReal ((2 : ℝ)) := by
    simp [jointMass, bern, Fin.prod_univ_one]
  rw [huniv, Finset.sum_insert (by simp [hne]), Finset.sum_singleton, hf, ht]
  have hneg : ENNReal.ofReal ((1 : ℝ) - 2) = 0 := by
    rw [ENNReal.ofReal_eq_zero]; norm_num
  have hpos : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) :=
    ENNReal.ofReal_natCast 2
  rw [hneg, hpos, zero_add]
  exact ENNReal.one_lt_two.ne.symm

/-- The degenerate `Fin 1` fixture probability vector. -/
noncomputable def p0 : Fin 1 → ℝ := ![0]

private theorem p0_nonneg : ∀ i, 0 ≤ p0 i := by
  intro i; fin_cases i; norm_num [p0]

private theorem p0_le_one : ∀ i, p0 i ≤ 1 := by
  intro i; fin_cases i; norm_num [p0]

/-- **Fence: the centering hypothesis `p e ≠ 0` is load-bearing.** At
`p 0 = 0` the sampling measure is the point mass at the all-false atom
(where `δ_0 = 0`), so the "centered" integrand evaluates through the
junk quotient `0 / 0 = 0` to the constant `(-1) • M` — the integral is
`-M`, not `0`. The conclusion of `integral_coord_center_smul` is
refuted, not merely un instantiable, exactly at the dropped
hypothesis. -/
theorem bp_center_zero_fence_QA :
    ∫ ω : (Fin 1 → Bool), ((if ω 0 then (1 : ℝ) else 0) / (0 : ℝ) - 1) • (bpMat true)
      ∂(bernPMF p0 p0_nonneg p0_le_one).toMeasure = -(bpMat true) := by
  rw [integral_smul_const]
  have hint : ∫ ω : (Fin 1 → Bool), ((if ω 0 then (1 : ℝ) else 0) / (0 : ℝ) - 1)
      ∂(bernPMF p0 p0_nonneg p0_le_one).toMeasure = -1 := by
    have h1 : ∫ ω : (Fin 1 → Bool), (1 : ℝ)
        ∂(bernPMF p0 p0_nonneg p0_le_one).toMeasure = 1 := by
      rw [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
    have hfint : Integrable (fun ω : Fin 1 → Bool => (if ω 0 then (1 : ℝ) else 0) / (0 : ℝ))
        (bernPMF p0 p0_nonneg p0_le_one).toMeasure := Integrable.of_finite
    have hgint : Integrable (fun _ : Fin 1 → Bool => (1 : ℝ))
        (bernPMF p0 p0_nonneg p0_le_one).toMeasure := Integrable.of_finite
    rw [integral_sub hfint hgint, integral_div, integral_delta p0 p0_nonneg p0_le_one 0,
      show p0 0 = 0 from rfl, zero_div, h1, zero_sub]
  rw [hint, neg_smul, one_smul]

/-- The fence's nonvanishing: the computed value `-M` is provably `≠ 0`
at the concrete matrix. -/
theorem bp_center_zero_fence_nonzero_QA :
    ∫ ω : (Fin 1 → Bool), ((if ω 0 then (1 : ℝ) else 0) / (0 : ℝ) - 1) • (bpMat true)
      ∂(bernPMF p0 p0_nonneg p0_le_one).toMeasure ≠ 0 := by
  rw [bp_center_zero_fence_QA]
  intro h
  have h00 : (bpMat true) 0 0 = 1 := rfl
  have := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℝ => X 0 0) h
  simp [Matrix.neg_apply, h00] at this

end Scaffold.Mathlib.Probability.BernoulliProduct.QA
