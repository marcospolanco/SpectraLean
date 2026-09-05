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

  Since 2026-09-05 the `AdversarialFences` section carries the shelf's
  hypothesis-necessity pass; the two pre-discipline free-form fences
  are subsumed as the proof engines of its hypothesis-form wrappers.

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

/-!
## Adversarial fences

The hypothesis-necessity pass (`governance/ADVERSARIAL_REVIEW.md`;
proposal `proposals/adversarial-fences-bernoulli-product-family.md`,
2026-09-05): fifteen hypothesis-form fences over the shelf's priceable
clause surface — the `hp0`/`hp1` bounds clauses of the four ∑-theorems
(the `bernPMF`-consumers' bounds clauses are signature-entangled: the
sampling measure does not exist out of bounds, and these mass-level
fences are exactly that entanglement's visible boundary), the `hee`
distinctness clauses (Cauchy–Schwarz strictness for the double
marginal; `μ(A ∩ A) ≠ μ(A)²` for both independence statements, scalar
and matrix codomain), the `he` injectivity clauses of the
mutual-independence transfer trio at the constant reindexing, and the
centering `hpne` clause. Each fence assumes the theorem's conclusion
with one clause dropped at a fixture keeping every kept clause genuine,
and derives `False`.
-/

section AdversarialFences

/-! ## The Fin 1 enumeration helper -/

private theorem univ_fin1_bool :
    (Finset.univ : Finset (Fin 1 → Bool)) = {![false], ![true]} := by
  ext ω
  cases h : ω 0 <;> simp [Set.mem_singleton_iff, Set.mem_insert_iff, funext_iff, h]
  · exact Or.inl fun x => by fin_cases x; simp [h]
  · exact Or.inr fun x => by fin_cases x; simp [h]

private theorem bpS1_ne_f_t : (![false] : Fin 1 → Bool) ≠ ![true] := fun he =>
  absurd (congrFun he 0) (by decide)

/-! ## Fixtures -/

/-- The all-genuine one-coordinate fixture `p = ![1/2]`. -/
noncomputable def bpHalf : Fin 1 → ℝ := ![1/2]

theorem bpHalf_nonneg : ∀ i, 0 ≤ bpHalf i := by
  intro i; fin_cases i; norm_num [bpHalf]

theorem bpHalf_le_one : ∀ i, bpHalf i ≤ 1 := by
  intro i; fin_cases i; norm_num [bpHalf]

/-- The out-of-upper-bound two-coordinate fixture `p = ![2, 2]`. -/
noncomputable def bpTwo : Fin 2 → ℝ := ![2, 2]

theorem bpTwo_nonneg : ∀ i, 0 ≤ bpTwo i := by
  intro i; fin_cases i <;> norm_num [bpTwo]

/-- The out-of-lower-bound two-coordinate fixture `p = ![-1, -1]`. -/
noncomputable def bpNeg2 : Fin 2 → ℝ := ![-1, -1]

theorem bpNeg2_le_one : ∀ i, bpNeg2 i ≤ 1 := by
  intro i; fin_cases i <;> norm_num [bpNeg2]

/-- The `hp1` breaker for `sum_coord2_mul`: only coordinate `2` out of
bounds, so the broken mass multiplies the left side only. -/
noncomputable def bp3T : Fin 3 → ℝ := ![1, 1, 2]

theorem bp3T_nonneg : ∀ i, 0 ≤ bp3T i := by
  intro i; fin_cases i <;> norm_num [bp3T]

/-- The `hp0` breaker for `sum_coord2_mul`: only coordinate `0` out of
bounds, sitting outside the statement's `{e, e'} = {1, 2}`. -/
noncomputable def bp3N : Fin 3 → ℝ := ![-1, 1, 1]

theorem bp3N_le_one : ∀ i, bp3N i ≤ 1 := by
  intro i; fin_cases i <;> norm_num [bp3N]

/-! ## Shared kill engines -/

private theorem bpF_ofReal_ne_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a ≠ b)
    (h : ENNReal.ofReal a = ENNReal.ofReal b) : False := by
  apply_fun ENNReal.toReal at h
  rw [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at h
  exact hne h

/-- The coordinate-`0` true-cylinder measure at the all-genuine
fixture: `1/2`. -/
theorem bpF_cyl_half :
    (bernPMF bpHalf bpHalf_nonneg bpHalf_le_one).toMeasure
        ((fun ω : Fin 1 → Bool => ω 0) ⁻¹' {true}) = ENNReal.ofReal ((1 : ℝ) / 2) := by
  rw [toMeasure_cyl bpHalf bpHalf_nonneg bpHalf_le_one 0 {true}]
  have hb : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
  simp [bern, bpHalf]

/-- The matrix entry projection is measurable at the hand-rolled
product σ-algebra (the nested `measurable_pi_apply` composition). -/
theorem bpF_matrix_entry_measurable :
    Measurable fun N : Matrix (Fin 2) (Fin 2) ℝ => N 0 0 :=
  (measurable_pi_apply (0 : Fin 2)).comp (measurable_pi_apply (0 : Fin 2))

/-- The entry cylinder `{N | 1/2 < N 0 0}` is measurable. -/
theorem bpF_entry_cyl_measurable :
    MeasurableSet ((fun N : Matrix (Fin 2) (Fin 2) ℝ => N 0 0) ⁻¹' Set.Ioi ((1 : ℝ) / 2)) :=
  bpF_matrix_entry_measurable measurableSet_Ioi

/-- The matrix-valued single-coordinate family's preimage of the entry
cylinder is exactly the true-cylinder at the coordinate. -/
theorem bpF_entry_cyl_preimage :
    (fun ω : Fin 1 → Bool => bpMat (ω 0)) ⁻¹'
        ((fun N : Matrix (Fin 2) (Fin 2) ℝ => N 0 0) ⁻¹' Set.Ioi ((1 : ℝ) / 2))
      = (fun ω : Fin 1 → Bool => ω 0) ⁻¹' {true} := by
  have h1 : bpMat true 0 0 = 1 := rfl
  have h0 : bpMat false 0 0 = 0 := rfl
  ext ω
  simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_singleton_iff]
  cases h : ω 0
  · rw [h0]; simp
  · rw [h1]; norm_num

/-! ## Fences 1-4: the mass-level `hp0`/`hp1` clauses -/

/-- **Fence: `sum_bern_eq_one`'s `hp1 : ∀ i, p i ≤ 1`.** At `p = ![2]`
(kept `hp0` genuine: `0 ≤ 2`) the coordinate mass sum is
`0 + 2 = 2 ≠ 1` — the `ofReal` clamp zeroes the negative false-mass
`ofReal (1 - 2) = 0` while the true-mass stays `2`. -/
theorem bpFence_sum_bern_le_one
    (h : ∑ b, bern (![2] : Fin 1 → ℝ) 0 b = 1) : False := by
  have hb : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  have hf : bern (![2] : Fin 1 → ℝ) 0 false = ENNReal.ofReal ((1 : ℝ) - 2) := by
    simp [bern]
  have hzero : ENNReal.ofReal ((1 : ℝ) - 2) = 0 := ENNReal.ofReal_eq_zero.2 (by norm_num)
  have ht : bern (![2] : Fin 1 → ℝ) 0 true = ENNReal.ofReal ((2 : ℝ)) := by
    simp [bern]
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton, hf, hzero, zero_add, ht] at h
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal ((1 : ℝ)) from ENNReal.ofReal_one.symm] at h
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_bern_eq_one`'s `hp0 : ∀ i, 0 ≤ p i`.** At `p = ![-1]`
(kept `hp1` genuine: `-1 ≤ 1`) the clamp doubles the false-mass
`ofReal (1 - (-1)) = 2` and zeroes the true-mass: `2 + 0 = 2 ≠ 1`. -/
theorem bpFence_sum_bern_nonneg
    (h : ∑ b, bern (![-1] : Fin 1 → ℝ) 0 b = 1) : False := by
  have hb : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  have hf : bern (![-1] : Fin 1 → ℝ) 0 false = ENNReal.ofReal ((1 : ℝ) - (-1)) := by
    simp [bern]
  have hone : ((1 : ℝ) - (-1)) = 2 := by norm_num
  have ht : bern (![-1] : Fin 1 → ℝ) 0 true = ENNReal.ofReal ((-1 : ℝ)) := by
    simp [bern]
  have htzero : ENNReal.ofReal ((-1 : ℝ)) = 0 := ENNReal.ofReal_eq_zero.2 (by norm_num)
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton, hf, hone, ht, htzero,
    add_zero, show (1 : ℝ≥0∞) = ENNReal.ofReal ((1 : ℝ)) from ENNReal.ofReal_one.symm] at h
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_jointMass_eq_one`'s `hp0`.** At `p = ![-1]` (kept
`hp1` genuine) the joint mass sums to `2 + 0 = 2 ≠ 1`. The `hp1`
sibling is the delivered `bp_out_of_bounds_fence_QA`, reconciled in
the landed section as its hypothesis-form wrapper. -/
theorem bpFence_sum_joint_nonneg
    (h : ∑ ω : Fin 1 → Bool, jointMass (![-1] : Fin 1 → ℝ) ω = 1) : False := by
  have hf : jointMass (![-1] : Fin 1 → ℝ) ![false] = ENNReal.ofReal ((1 : ℝ) - (-1)) := by
    simp [jointMass, bern, Fin.prod_univ_one]
  have hone : ((1 : ℝ) - (-1)) = 2 := by norm_num
  have ht : jointMass (![-1] : Fin 1 → ℝ) ![true] = ENNReal.ofReal ((-1 : ℝ)) := by
    simp [jointMass, bern, Fin.prod_univ_one]
  have htzero : ENNReal.ofReal ((-1 : ℝ)) = 0 := ENNReal.ofReal_eq_zero.2 (by norm_num)
  rw [univ_fin1_bool, Finset.sum_insert (by simp [bpS1_ne_f_t]), Finset.sum_singleton,
    hf, hone, ht, htzero, add_zero,
    show (1 : ℝ≥0∞) = ENNReal.ofReal ((1 : ℝ)) from ENNReal.ofReal_one.symm] at h
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-! ## Fences 5-6: `sum_coord_mul`'s `hp0`/`hp1` -/

/-- **Fence: `sum_coord_mul`'s `hp1`.** At `p = ![2, 2]` (kept `hp0`
genuine) with `e = 0` and `F` the true-indicator, the left side is
the `true ⊗ true` atom's mass `4` while the right side is the
coordinate-`0` true-marginal `2`: the broken coordinate-`1` mass sum
`2` multiplies the left side only. -/
theorem bpFence_sum_coord_mul_le_one
    (h : ∑ ω : Fin 2 → Bool, (if ω 0 then (1 : ℝ≥0∞) else 0) * jointMass bpTwo ω
      = ∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bpTwo 0 b) : False := by
  have hzero : ENNReal.ofReal ((1 : ℝ) - 2) = 0 := ENNReal.ofReal_eq_zero.2 (by norm_num)
  have hff : jointMass bpTwo ![false, false] = 0 := by
    have h' : jointMass bpTwo ![false, false]
        = ENNReal.ofReal ((1 : ℝ) - 2) * ENNReal.ofReal ((1 : ℝ) - 2) := by
      simp [jointMass, bern, bpTwo]
    rw [h', hzero, zero_mul]
  have hft : jointMass bpTwo ![false, true] = 0 := by
    have h' : jointMass bpTwo ![false, true]
        = ENNReal.ofReal ((1 : ℝ) - 2) * ENNReal.ofReal ((2 : ℝ)) := by
      simp [jointMass, bern, bpTwo]
    rw [h', hzero, zero_mul]
  have htf : jointMass bpTwo ![true, false] = 0 := by
    have h' : jointMass bpTwo ![true, false]
        = ENNReal.ofReal ((2 : ℝ)) * ENNReal.ofReal ((1 : ℝ) - 2) := by
      simp [jointMass, bern, bpTwo]
    rw [h', hzero, mul_zero]
  have htt : jointMass bpTwo ![true, true] = ENNReal.ofReal ((4 : ℝ)) := by
    have h' : jointMass bpTwo ![true, true]
        = ENNReal.ofReal ((2 : ℝ)) * ENNReal.ofReal ((2 : ℝ)) := by
      simp [jointMass, bern, bpTwo]
    rw [h', ← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num
  have hR : ∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bpTwo 0 b = ENNReal.ofReal ((2 : ℝ)) := by
    have hb : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
    have hf : bern bpTwo 0 false = ENNReal.ofReal ((1 : ℝ) - 2) := by simp [bern, bpTwo]
    have ht : bern bpTwo 0 true = ENNReal.ofReal ((2 : ℝ)) := by simp [bern, bpTwo]
    rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton, hf, hzero, ht]
    simp
  rw [univ_fin2_bool,
    Finset.sum_insert (by simp [bp_ne_ff_ft, bp_ne_ff_tf, bp_ne_ff_tt]),
    Finset.sum_insert (by simp [bp_ne_ft_tf, bp_ne_ft_tt]),
    Finset.sum_insert (by simp [bp_ne_tf_tt]), Finset.sum_singleton,
    hff, hft, htf, htt, hR] at h
  simp at h

/-- **Fence: `sum_coord_mul`'s `hp0`.** At `p = ![-1, -1]` (kept `hp1`
genuine) with `e = 0` and `F` the false-indicator, the left side is
the `false ⊗ false` atom's mass `4` while the right side is the
coordinate-`0` false-marginal `2`. -/
theorem bpFence_sum_coord_mul_nonneg
    (h : ∑ ω : Fin 2 → Bool, (if ω 0 then (0 : ℝ≥0∞) else 1) * jointMass bpNeg2 ω
      = ∑ b, (if b then (0 : ℝ≥0∞) else 1) * bern bpNeg2 0 b) : False := by
  have hzero : ENNReal.ofReal ((-1 : ℝ)) = 0 := ENNReal.ofReal_eq_zero.2 (by norm_num)
  have hone : ((1 : ℝ) - (-1)) = 2 := by norm_num
  have hff : jointMass bpNeg2 ![false, false] = ENNReal.ofReal ((4 : ℝ)) := by
    have h' : jointMass bpNeg2 ![false, false]
        = ENNReal.ofReal ((1 : ℝ) - (-1)) * ENNReal.ofReal ((1 : ℝ) - (-1)) := by
      simp [jointMass, bern, bpNeg2]
    rw [h', ← ENNReal.ofReal_mul (by norm_num), hone]
    congr 1; norm_num
  have hft : jointMass bpNeg2 ![false, true] = 0 := by
    have h' : jointMass bpNeg2 ![false, true]
        = ENNReal.ofReal ((1 : ℝ) - (-1)) * ENNReal.ofReal ((-1 : ℝ)) := by
      simp [jointMass, bern, bpNeg2]
    rw [h', hzero, mul_zero]
  have htf : jointMass bpNeg2 ![true, false] = 0 := by
    have h' : jointMass bpNeg2 ![true, false]
        = ENNReal.ofReal ((-1 : ℝ)) * ENNReal.ofReal ((1 : ℝ) - (-1)) := by
      simp [jointMass, bern, bpNeg2]
    rw [h', hzero, zero_mul]
  have htt : jointMass bpNeg2 ![true, true] = 0 := by
    have h' : jointMass bpNeg2 ![true, true]
        = ENNReal.ofReal ((-1 : ℝ)) * ENNReal.ofReal ((-1 : ℝ)) := by
      simp [jointMass, bern, bpNeg2]
    rw [h', hzero, zero_mul]
  have hR : ∑ b, (if b then (0 : ℝ≥0∞) else 1) * bern bpNeg2 0 b = ENNReal.ofReal ((2 : ℝ)) := by
    have hb : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
    have hf : bern bpNeg2 0 false = ENNReal.ofReal ((1 : ℝ) - (-1)) := by simp [bern, bpNeg2]
    have ht : bern bpNeg2 0 true = ENNReal.ofReal ((-1 : ℝ)) := by simp [bern, bpNeg2]
    rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton, hf, hone, ht, hzero]
    simp
  rw [univ_fin2_bool,
    Finset.sum_insert (by simp [bp_ne_ff_ft, bp_ne_ff_tf, bp_ne_ff_tt]),
    Finset.sum_insert (by simp [bp_ne_ft_tf, bp_ne_ft_tt]),
    Finset.sum_insert (by simp [bp_ne_tf_tt]), Finset.sum_singleton,
    hff, hft, htf, htt, hR] at h
  simp at h

/-! ## Fences 7-8: `sum_coord2_mul`'s `hp0`/`hp1` -/

/-- **Fence: `sum_coord2_mul`'s `hp1`.** At `p = ![1, 1, 2]` (kept `hp0`
genuine) with `e = 0`, `e' = 1` and `F = G` the true-indicator, the
broken coordinate-`2` mass sum `2` multiplies the left side only:
`2 ≠ 1`. Both quantified coordinates are consumed by the statement,
so the breaker must sit *outside* `{e, e'}` — on `Fin 2` the dropped
statement is true (Fubini). -/
theorem bpFence_sum_coord2_le_one
    (h : ∑ ω : Fin 3 → Bool, (if ω 0 then (1 : ℝ≥0∞) else 0) * (if ω 1 then (1 : ℝ≥0∞) else 0)
        * jointMass bp3T ω
      = (∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bp3T 0 b)
        * (∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bp3T 1 b)) : False := by
  classical
  have hb2f : bern bp3T 2 false = 0 := by
    have h' : bern bp3T 2 false = ENNReal.ofReal ((1 : ℝ) - 2) := by simp [bern, bp3T]
    rw [h']
    exact ENNReal.ofReal_eq_zero.2 (by norm_num : ((1 : ℝ) - 2) ≤ 0)
  have hb2t : bern bp3T 2 true = ENNReal.ofReal ((2 : ℝ)) := by simp [bern, bp3T]
  set g : Fin 3 → Bool → ℝ≥0∞ := fun i b =>
    if i = 0 then (if b then (1 : ℝ≥0∞) else 0) * bern bp3T 0 b
    else if i = 1 then (if b then (1 : ℝ≥0∞) else 0) * bern bp3T 1 b else bern bp3T 2 b with hg
  have hg0 : ∀ b, g 0 b = (if b then (1 : ℝ≥0∞) else 0) * bern bp3T 0 b := by
    intro b; simp [hg]
  have hg1 : ∀ b, g 1 b = (if b then (1 : ℝ≥0∞) else 0) * bern bp3T 1 b := by
    intro b; simp [hg]
  have hg2 : ∀ b, g 2 b = bern bp3T 2 b := by intro b; simp [hg]
  have hprod : ∀ ω : Fin 3 → Bool, (if ω 0 then (1 : ℝ≥0∞) else 0)
      * (if ω 1 then (1 : ℝ≥0∞) else 0) * jointMass bp3T ω = ∏ i, g i (ω i) := by
    intro ω
    rw [Fin.prod_univ_three, hg0, hg1, hg2]
    rw [show jointMass bp3T ω
        = bern bp3T 0 (ω 0) * bern bp3T 1 (ω 1) * bern bp3T 2 (ω 2) from by
      simp [jointMass, Fin.prod_univ_three]]
    ac_rfl
  have hpi : (Finset.univ : Finset (Fin 3 → Bool)) = Fintype.piFinset fun _ => Finset.univ := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hpi, Finset.sum_congr rfl (fun ω _ => hprod ω),
    Finset.sum_prod_piFinset (Finset.univ : Finset Bool) g, Fin.prod_univ_three] at h
  simp only [hg0, hg1, hg2] at h
  have hbb : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  have hS0 : ∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bp3T 0 b = 1 := by
    rw [hbb, Finset.sum_insert (by simp), Finset.sum_singleton]
    simp [bern, bp3T]
  have hS1 : ∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bp3T 1 b = 1 := by
    rw [hbb, Finset.sum_insert (by simp), Finset.sum_singleton]
    simp [bern, bp3T]
  have hS2 : ∑ b, bern bp3T 2 b = ENNReal.ofReal ((2 : ℝ)) := by
    rw [hbb, Finset.sum_insert (by simp), Finset.sum_singleton, hb2f, hb2t]
    simp
  rw [hS0, hS1, hS2] at h
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal ((1 : ℝ)) from ENNReal.ofReal_one.symm] at h
  simp at h

/-- **Fence: `sum_coord2_mul`'s `hp0`.** At `p = ![-1, 1, 1]` (kept
`hp1` genuine) with `e = 1`, `e' = 2` and `F = G` the true-indicator,
the broken coordinate-`0` mass sum `2` multiplies the left side only
(sitting outside `{e, e'}`): `2 ≠ 1`. -/
theorem bpFence_sum_coord2_nonneg
    (h : ∑ ω : Fin 3 → Bool, (if ω 1 then (1 : ℝ≥0∞) else 0) * (if ω 2 then (1 : ℝ≥0∞) else 0)
        * jointMass bp3N ω
      = (∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bp3N 1 b)
        * (∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bp3N 2 b)) : False := by
  classical
  have hb0f : bern bp3N 0 false = ENNReal.ofReal ((2 : ℝ)) := by
    have h' : bern bp3N 0 false = ENNReal.ofReal ((1 : ℝ) - (-1)) := by simp [bern, bp3N]
    rw [h']
    congr 1; norm_num
  have hb0t : bern bp3N 0 true = 0 := by
    have h' : bern bp3N 0 true = ENNReal.ofReal ((-1 : ℝ)) := by simp [bern, bp3N]
    rw [h']
    exact ENNReal.ofReal_eq_zero.2 (by norm_num : ((-1 : ℝ)) ≤ 0)
  set g : Fin 3 → Bool → ℝ≥0∞ := fun i b =>
    if i = 0 then bern bp3N 0 b
    else if i = 1 then (if b then (1 : ℝ≥0∞) else 0) * bern bp3N 1 b
    else (if b then (1 : ℝ≥0∞) else 0) * bern bp3N 2 b with hg
  have hg0 : ∀ b, g 0 b = bern bp3N 0 b := by intro b; simp [hg]
  have hg1 : ∀ b, g 1 b = (if b then (1 : ℝ≥0∞) else 0) * bern bp3N 1 b := by
    intro b; simp [hg]
  have hg2 : ∀ b, g 2 b = (if b then (1 : ℝ≥0∞) else 0) * bern bp3N 2 b := by
    intro b; simp [hg]
  have hprod : ∀ ω : Fin 3 → Bool, (if ω 1 then (1 : ℝ≥0∞) else 0)
      * (if ω 2 then (1 : ℝ≥0∞) else 0) * jointMass bp3N ω = ∏ i, g i (ω i) := by
    intro ω
    rw [Fin.prod_univ_three, hg0, hg1, hg2]
    rw [show jointMass bp3N ω
        = bern bp3N 0 (ω 0) * bern bp3N 1 (ω 1) * bern bp3N 2 (ω 2) from by
      simp [jointMass, Fin.prod_univ_three]]
    ac_rfl
  have hpi : (Finset.univ : Finset (Fin 3 → Bool)) = Fintype.piFinset fun _ => Finset.univ := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hpi, Finset.sum_congr rfl (fun ω _ => hprod ω),
    Finset.sum_prod_piFinset (Finset.univ : Finset Bool) g, Fin.prod_univ_three] at h
  simp only [hg0, hg1, hg2] at h
  have hbb : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  have hS0 : ∑ b, bern bp3N 0 b = ENNReal.ofReal ((2 : ℝ)) := by
    rw [hbb, Finset.sum_insert (by simp), Finset.sum_singleton, hb0f, hb0t]
    simp
  have hS1 : ∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bp3N 1 b = 1 := by
    rw [hbb, Finset.sum_insert (by simp), Finset.sum_singleton]
    simp [bern, bp3N]
  have hS2 : ∑ b, (if b then (1 : ℝ≥0∞) else 0) * bern bp3N 2 b = 1 := by
    rw [hbb, Finset.sum_insert (by simp), Finset.sum_singleton]
    simp [bern, bp3N]
  rw [hS0, hS1, hS2] at h
  rw [show (1 : ℝ≥0∞) = ENNReal.ofReal ((1 : ℝ)) from ENNReal.ofReal_one.symm] at h
  simp at h

/-! ## Fence 9: `sum_coord2_mul`'s `hee` (Cauchy–Schwarz strictness) -/

/-- **Fence: `sum_coord2_mul`'s `hee : e ≠ e'`.** At the all-genuine
fixture `p = ![1/2]` with `e = e' = 0` and `F = G` two-valued (`2` at
false, `3` at true), the left side is `∑ F²·bern = 13/2` while the
right side is `(∑ F·bern)² = 25/4`: Cauchy–Schwarz is strict on a
two-point space, so a single coordinate cannot play the role of two. -/
theorem bpFence_sum_coord2_hee
    (h : ∑ ω : Fin 1 → Bool, (if ω 0 then (3 : ℝ≥0∞) else 2) * (if ω 0 then (3 : ℝ≥0∞) else 2)
        * jointMass bpHalf ω
      = (∑ b, (if b then (3 : ℝ≥0∞) else 2) * bern bpHalf 0 b)
        * (∑ b, (if b then (3 : ℝ≥0∞) else 2) * bern bpHalf 0 b)) : False := by
  have h2 : (2 : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ)) := (ENNReal.ofReal_natCast 2).symm
  have h3 : (3 : ℝ≥0∞) = ENNReal.ofReal ((3 : ℝ)) := (ENNReal.ofReal_natCast 3).symm
  have hbf : bern bpHalf 0 false = ENNReal.ofReal ((1 : ℝ) / 2) := by
    have h' : bern bpHalf 0 false = ENNReal.ofReal ((1 : ℝ) - 1 / 2) := by simp [bern, bpHalf]
    rw [h']; congr 1; norm_num
  have hbt : bern bpHalf 0 true = ENNReal.ofReal ((1 : ℝ) / 2) := by
    simp [bern, bpHalf]
  have hL : ∑ ω : Fin 1 → Bool, (if ω 0 then (3 : ℝ≥0∞) else 2)
      * (if ω 0 then (3 : ℝ≥0∞) else 2) * jointMass bpHalf ω
      = ENNReal.ofReal ((13 : ℝ) / 2) := by
    have hmf : jointMass bpHalf ![false] = ENNReal.ofReal ((1 : ℝ) / 2) := by
      have h' : jointMass bpHalf ![false] = ENNReal.ofReal ((1 : ℝ) - 1 / 2) := by
        simp [jointMass, bern, bpHalf, Fin.prod_univ_one]
      rw [h']; congr 1; norm_num
    have hmt : jointMass bpHalf ![true] = ENNReal.ofReal ((1 : ℝ) / 2) := by
      simp [jointMass, bern, bpHalf, Fin.prod_univ_one]
    rw [univ_fin1_bool, Finset.sum_insert (by simp [bpS1_ne_f_t]), Finset.sum_singleton,
      hmf, hmt]
    simp only [Matrix.cons_val_zero]
    simp
    rw [h2, h3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1; norm_num
  have hsum : ∑ b, (if b then (3 : ℝ≥0∞) else 2) * bern bpHalf 0 b
      = ENNReal.ofReal ((5 : ℝ) / 2) := by
    have hbb : (Finset.univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
    rw [hbb, Finset.sum_insert (by simp), Finset.sum_singleton, hbf, hbt]
    simp
    rw [h2, h3, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1; norm_num
  rw [hL, hsum, ← ENNReal.ofReal_mul (by norm_num)] at h
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-! ## Fences 10-11: the independence statements' `hee` -/

/-- **Fence: `indepFun_coord`'s `hee`.** At the all-genuine fixture with
`e = e' = 0` the two "independent" coordinates are the same function:
at `s = t = {true}`, `μ(A ∩ A) = μ(A) = 1/2 ≠ 1/4 = μ(A) · μ(A)` —
a coordinate is not independent of itself. -/
theorem bpFence_indepFun_coord_hee
    (h : IndepFun (fun ω : Fin 1 → Bool => ω 0) (fun ω : Fin 1 → Bool => ω 0)
      (bernPMF bpHalf bpHalf_nonneg bpHalf_le_one).toMeasure) : False := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
  have h' := h {true} {true}
    ((Set.toFinite {true} : Set.Finite _).measurableSet)
    ((Set.toFinite {true} : Set.Finite _).measurableSet)
  rw [Set.inter_self, bpF_cyl_half, ← ENNReal.ofReal_mul (by norm_num)] at h'
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h'

/-- **Fence: `indepFun_coord_matrix`'s `hee`.** The same clause at the
matrix codomain: with `e = e' = 0` and `F = G = bpMat`, the kill is at
the measurable entry cylinder `{N | 1/2 < N 0 0}` (measurable at the
hand-rolled product σ-algebra through the nested `measurable_pi_apply`
composition). -/
theorem bpFence_indepFun_matrix_hee
    (h : IndepFun (fun ω : Fin 1 → Bool => bpMat (ω 0)) (fun ω : Fin 1 → Bool => bpMat (ω 0))
      (bernPMF bpHalf bpHalf_nonneg bpHalf_le_one).toMeasure) : False := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
  have h' := h _ _ bpF_entry_cyl_measurable bpF_entry_cyl_measurable
  rw [bpF_entry_cyl_preimage, Set.inter_self, bpF_cyl_half, ← ENNReal.ofReal_mul (by norm_num)] at h'
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h'

/-! ## Fences 12-14: the injectivity clauses `he` -/

/-- **Fence: `iIndepFun_of_injective`'s `he : Function.Injective e`.**
At the constant reindexing `e : Fin 2 → Fin 1` both reindexed
coordinates are `ω ↦ ω 0` — perfectly correlated — killed at
`T = univ`, `sets = {true}, {true}`: mutual independence fails as
`1/2 ≠ 1/4`. The sparsification designs reindex edges into coordinates
injectively; this clause is what makes that transfer sound. -/
theorem bpFence_iIndep_injective_he
    (h : iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace Bool))
      (fun (_ : Fin 2) (ω : Fin 1 → Bool) => ω (0 : Fin 1))
      (bernPMF bpHalf bpHalf_nonneg bpHalf_le_one).toMeasure) : False := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  have h' := h (Finset.univ : Finset (Fin 2)) (sets := fun _ => {true})
    (fun _ _ => (Set.toFinite {true} : Set.Finite _).measurableSet)
  have hint : (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
      (fun ω : Fin 1 → Bool => ω (0 : Fin 1)) ⁻¹' {true})
      = (fun ω : Fin 1 → Bool => ω (0 : Fin 1)) ⁻¹' {true} := by
    ext ω
    simp only [Set.mem_iInter]
    exact ⟨fun hh => hh 0 (Finset.mem_univ 0), fun hh k _ => hh⟩
  simp only [hint, bpF_cyl_half] at h'
  rw [Finset.prod_const, Finset.card_fin, pow_two, ← ENNReal.ofReal_mul (by norm_num)] at h'
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h'

/-- **Fence: `iIndepFun_coord_apply`'s `he`.** The same clause at the
scalar `apply` interface (`F k = id`, kept `hF : Measurable id`
genuine): the reindexed family is again `(ω ↦ ω 0, ω ↦ ω 0)`. -/
theorem bpFence_iIndep_apply_he
    (h : iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace Bool))
      (fun (_ : Fin 2) (ω : Fin 1 → Bool) => (fun (b : Bool) => b) (ω (0 : Fin 1)))
      (bernPMF bpHalf bpHalf_nonneg bpHalf_le_one).toMeasure) : False := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  have h' := h (Finset.univ : Finset (Fin 2)) (sets := fun _ => {true})
    (fun _ _ => (Set.toFinite {true} : Set.Finite _).measurableSet)
  have hint : (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
      (fun ω : Fin 1 → Bool => (fun (b : Bool) => b) (ω (0 : Fin 1))) ⁻¹' {true})
      = (fun ω : Fin 1 → Bool => (fun (b : Bool) => b) (ω (0 : Fin 1))) ⁻¹' {true} := by
    ext ω
    simp only [Set.mem_iInter]
    exact ⟨fun hh => hh 0 (Finset.mem_univ 0), fun hh k _ => hh⟩
  simp only [hint, bpF_cyl_half] at h'
  rw [Finset.prod_const, Finset.card_fin, pow_two, ← ENNReal.ofReal_mul (by norm_num)] at h'
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h'

/-- **Fence: `iIndepFun_coord_matrix`'s `he`.** The same clause at the
matrix codomain (`F k = bpMat`): the reindexed family is
`(ω ↦ bpMat (ω 0), ω ↦ bpMat (ω 0))`, killed at `T = univ` and the
measurable entry cylinder on both sets. -/
theorem bpFence_iIndep_matrix_he
    (h : iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace (Matrix (Fin 2) (Fin 2) ℝ)))
      (fun (_ : Fin 2) (ω : Fin 1 → Bool) => bpMat (ω (0 : Fin 1)))
      (bernPMF bpHalf bpHalf_nonneg bpHalf_le_one).toMeasure) : False := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  have h' := h (Finset.univ : Finset (Fin 2))
    (sets := fun _ => (fun N : Matrix (Fin 2) (Fin 2) ℝ => N 0 0) ⁻¹' Set.Ioi ((1 : ℝ) / 2))
    (fun _ _ => bpF_entry_cyl_measurable)
  have hint : (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
      (fun ω : Fin 1 → Bool => ω (0 : Fin 1)) ⁻¹' {true})
      = (fun ω : Fin 1 → Bool => ω (0 : Fin 1)) ⁻¹' {true} := by
    ext ω
    simp only [Set.mem_iInter]
    exact ⟨fun hh => hh 0 (Finset.mem_univ 0), fun hh k _ => hh⟩
  simp only [bpF_entry_cyl_preimage, hint, bpF_cyl_half] at h'
  rw [Finset.prod_const, Finset.card_fin, pow_two, ← ENNReal.ofReal_mul (by norm_num)] at h'
  exact bpF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h'

/-- **Fence: `sum_jointMass_eq_one`'s `hp1`.** At `p = ![2]` (kept `hp0`
genuine) the joint masses sum to `2 ≠ 1` — the hypothesis-form wrapper
of the file's delivered free-form fence `bp_out_of_bounds_fence_QA`,
reconciling it into the per-clause discipline. -/
theorem bpFence_sum_joint_le_one
    (h : ∑ ω : Fin 1 → Bool, jointMass (![2] : Fin 1 → ℝ) ω = 1) : False :=
  bp_out_of_bounds_fence_QA h

/-- **Fence: `integral_coord_center_smul`'s `hpne : p e ≠ 0`.** At
`p = ![0]` (kept `hp0`/`hp1` genuine) the junk quotient `0 / 0 = 0`
makes the "centered" integrand the constant `-M`: the hypothesis-form
wrapper of the file's delivered free-form fence pair
(`bp_center_zero_fence_QA` computing the value, its `≠ 0` companion),
reconciling it into the per-clause discipline. -/
theorem bpFence_center_hpne
    (h : ∫ ω : Fin 1 → Bool, ((if ω 0 then (1 : ℝ) else 0) / (0 : ℝ) - 1) • (bpMat true)
      ∂(bernPMF p0 p0_nonneg p0_le_one).toMeasure = 0) : False :=
  bp_center_zero_fence_nonzero_QA h

end AdversarialFences

end Scaffold.Mathlib.Probability.BernoulliProduct.QA
