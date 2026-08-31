/-
  EmpiricalStationary_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Derived.EmpiricalStationary`: the fixed-time
  empirical-stationary-distribution concentration theorems —
  `hoeffding_empirical`'s first theorem consumer, per
  `proposals/empirical-stationary-distribution-concentration.md`
  Step 1's three named QA obligations:

  1. the closed-form walk-law fixture (the three-vertex path's
     `t = 2` law `![1/2, 0, 1/2]`, pinned raw in `Mixing_QA`), the
     theorem instance on it, and the event-side identification at
     `t = 1` (the deviation bounded strictly below the threshold for
     every outcome — the instance's event honestly characterized);
  2. the `n = 0` degenerate boundary consistent with the axiom's own
     documented junk-value behavior (the raw statement instantiated,
     its event identified as `univ`, its bound evaluated to `2`), and
     the clean form's `n ≠ 0` hypothesis load-bearing (the centering
     collapse `q i` refuted at `n = 0`);
  3. the raw two-sample instantiation at `V = Fin 2`,
     `q = ![2/3, 1/3]`, `t = 1/2`: the event's measure computed raw
     as `1/9` by four-atom enumeration, the theorem instance, and the
     classical numeric comparison `1/9 ≤ 2 exp (-1)` proved from
     `Real.add_one_le_exp` at `-1/2` — the axiom-backed statement and
     raw arithmetic agreeing at one number.

  The two `hoeffding_empirical`-consuming pins instantiate what was
  an admitted axiom at delivery time (2026-08-27) and has been a
  locally proved theorem since the 2026-08-30 retirement — they check
  the interface and the classical numbers.

  4. the Step-2 QA section (`proposals/
  empirical-stationary-distribution-concentration.md`'s deferred
  stationarity-limit form, delivered 2026-08-31) — the raw deviation
  and bias pins on the triangle, both theorem instances (the
  bias-folded exponent at `t₀ = 2`; the depth-form capstone at
  `t₀ = 3` closing at exactly `2 exp (−1/16)`), the event-mass
  non-vacuity witness (the both-samples-at-`0` cylinder at mass
  `1/16`), the **bias-free naive-form refutation** at `t₀ = 0` (the
  sampler law is `δ₀`, the event is the whole space at measure `1`
  against `2 exp (−16/9) < 1` — the bias term load-bearing), and the
  `t₀ = 0` corner instance of the delivered form itself (admitted
  with honest large bias, not excluded).

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Derived.EmpiricalStationary
import Scaffold.QA.SpectralGraph.Mixing_QA
import Scaffold.QA.Probability.IIDProduct_QA

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Scaffold.Derived.EmpiricalStationary.QA

open Scaffold.Mathlib.Probability.IIDProduct
open Scaffold.Mathlib.Probability.IIDProduct.QA
open SpectralGraphTheory SpectralGraphTheory.QA

/-!
## Obligation 1: the closed-form walk-law fixture and the graph instance
-/

/-- The path adjacency is entrywise nonnegative (the walk-law
nonnegativity hypothesis, at the fixture). -/
theorem pathAdj_nonneg (i j : Fin 3) : 0 ≤ pathAdj i j := by
  fin_cases i <;> fin_cases j <;> simp [pathAdj]

/-- The fixture's `t = 2` walk law is the probability vector
`![1/2, 0, 1/2]` (raw pin, `Mixing_QA.path_dist_two_QA`). -/
theorem path_law_QA :
    walkDistribution pathAdj 2 0 = ![1/2, 0, 1/2] :=
  path_dist_two_QA

theorem path_law_entry_zero_QA : walkDistribution pathAdj 2 0 0 = 1/2 := by
  rw [path_law_QA]; simp

/-- The instance's event side honestly characterized: at `t = 1` the
deviation is strictly below the threshold for *every* outcome (the
empirical frequency of vertex `0` in two samples of the `![1/2, 0,
1/2]` law always sits within `1/2` of `1/2`), so the theorem's event
set is empty at `t = 1` — the instance is about a genuinely-empty
event, not an opaque one. -/
theorem path_event_dev_lt_QA (ω : Fin 2 → Fin 3) :
    |(1 / (2 : ℝ)) * ∑ k : Fin 2, (if ω k = 0 then (1 : ℝ) else 0)
      - walkDistribution pathAdj 2 0 0| < 1 := by
  have b0 : (0 : ℝ) ≤ (if ω (0 : Fin 2) = 0 then 1 else 0)
        ∧ (if ω (0 : Fin 2) = 0 then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  have b1 : (0 : ℝ) ≤ (if ω (1 : Fin 2) = 0 then 1 else 0)
        ∧ (if ω (1 : Fin 2) = 0 then (1 : ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  rw [path_law_entry_zero_QA, Fin.sum_univ_two, abs_lt]
  constructor <;> nlinarith

/-- **The graph theorem instantiated** at the path fixture (`t₀ = 2`,
`n = 2`, `i = 0`, `t = 1`): the interface instance of
`empiricalWalkDistribution_tail`, conditional on
`hoeffding_empirical`. The event is `path_event_dev_lt_QA`'s empty
set and the bound evaluates at exponent `-4`. -/
theorem path_tail_instance_QA :
    (iidPMF (walkDistribution pathAdj 2 0)
        (walkDistribution_nonneg pathAdj (fun i j => pathAdj_nonneg i j) pathAdj_deg_pos 2 0)
        (sum_walkDistribution pathAdj pathAdj_deg_pos 2 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - walkDistribution pathAdj 2 0 0| ≥ 1}
      ≤ ENNReal.ofReal (2 * Real.exp (-4)) := by
  have h := empiricalWalkDistribution_tail (V := Fin 3)
    (fun i j => pathAdj_nonneg i j) pathAdj_deg_pos 2 0 two_ne_zero 0 1 zero_le_one
  have h' : -2 * ((2 : ℕ) : ℝ) * (1 : ℝ) ^ 2 = -4 := by norm_num
  rw [h'] at h
  exact h

/-!
## Obligation 2: the `n = 0` boundary
-/

/-- The raw statement of `hoeffding_empirical` instantiated at
`n = 0` on the fixture sampling space (vacuous clause hypotheses) —
the axiom's own documented junk-value behavior made concrete: both
the deviation and the centering constant evaluate through `1/0 = 0`
to `0`, the event at `t = 0` is everything, and the bound evaluates
to `2`. Interface pin; the axiom is instantiated, not validated. -/
theorem junk_n_zero_QA :
    (iidPMF q23 q23_nonneg q23_sum).toMeasure
      {ω : Fin 0 → Fin 2 | |(1 / ((0 : ℕ) : ℝ)) * ∑ k : Fin 0,
            (if ω k = 0 then (1 : ℝ) else 0)
          - (1 / ((0 : ℕ) : ℝ)) * ∑ k : Fin 0, ∫ ω',
              (if ω' k = 0 then (1 : ℝ) else 0)
              ∂(iidPMF (V := Fin 2) q23 q23_nonneg q23_sum).toMeasure| ≥ 0}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * ((0 : ℕ) : ℝ) * 0 ^ 2)) := by
  refine Scaffold.Mathlib.Probability.Concentration.Scalar.hoeffding_empirical
    (fun k => measurable_indicator_coord (V := Fin 2) k 0)
    (iIndepFun_indicator_coord (V := Fin 2) q23 q23_nonneg q23_sum 0)
    (fun _k ω => by split_ifs <;> simp) 0 le_rfl

/-- The `n = 0` event is everything (identified, not opaque). -/
theorem junk_n_zero_event_QA :
    {ω : Fin 0 → Fin 2 | |(1 / ((0 : ℕ) : ℝ)) * ∑ k : Fin 0,
            (if ω k = 0 then (1 : ℝ) else 0)
          - (1 / ((0 : ℕ) : ℝ)) * ∑ k : Fin 0, ∫ ω',
              (if ω' k = 0 then (1 : ℝ) else 0)
              ∂(iidPMF (V := Fin 2) q23 q23_nonneg q23_sum).toMeasure| ≥ 0}
      = Set.univ := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_univ, Fin.sum_univ_zero, mul_zero, sub_zero,
    abs_zero, ge_iff_le]
  exact ⟨fun _ => trivial, fun _ => le_rfl⟩

/-- The `n = 0` bound evaluates to `2` (identified, not opaque). -/
theorem junk_n_zero_bound_QA :
    2 * Real.exp (-2 * ((0 : ℕ) : ℝ) * 0 ^ 2) = 2 := by norm_num

/-- The clean form's `n ≠ 0` hypothesis is load-bearing: the
centering collapse `(1/n) ∑ k, ∫ X k = q i` fails outright at
`n = 0` (the left side is the junk `0`, the right side `q 0 = 2/3`),
so the `q i`-centered statement cannot be stated at `n = 0`. -/
theorem centering_fails_at_zero_QA :
    (1 / ((0 : ℕ) : ℝ)) * ∑ _k : Fin 0, q23 0 ≠ q23 0 := by
  rw [Fin.sum_univ_zero, mul_zero, q23_zero]
  norm_num

/-!
## Obligation 3: the raw two-sample instantiation
-/

/-- The classical numeric comparison behind the fixture instance:
`1/9 ≤ 2 exp (-1)`, proved from `Real.add_one_le_exp` at `-1/2`
(`exp (-1/2) ≥ 1/2`, so `exp (-1) = exp (-1/2)² ≥ 1/4`). -/
theorem exp_lower_bound_QA : (1 : ℝ) / 9 ≤ 2 * Real.exp (-(1 : ℝ)) := by
  have hhalf : (1 : ℝ) / 2 ≤ Real.exp (-(1 / 2)) := by
    have h := Real.add_one_le_exp (-(1 / 2 : ℝ))
    linarith
  have hsq : Real.exp (-(1 : ℝ))
      = Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) := by
    rw [← Real.exp_add]; congr 1; ring
  have he : (0 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) := by positivity
  have hquarter : (1 : ℝ) / 4
      ≤ Real.exp (-(1 / 2 : ℝ)) * Real.exp (-(1 / 2 : ℝ)) := by
    nlinarith [hhalf, he]
  rw [hsq]
  linarith

/-- Raw route: the event's measure computed by four-atom enumeration
— only the atom `![1, 1]` (both samples off vertex `0`) sits in
`{|p̂ - 2/3| ≥ 1/2}`, carrying mass `q 1 · q 1 = 1/9`. -/
theorem twoSample_event_measure_raw_QA :
    (iidPMF q23 q23_nonneg q23_sum).toMeasure
      {ω : Fin 2 → Fin 2 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
            (if ω k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2}
      = ENNReal.ofReal ((1 : ℝ) / 9) := by
  have hms : Measurable fun ω : Fin 2 → Fin 2 =>
      |(1 / (2 : ℝ)) * ∑ k : Fin 2, (if ω k = 0 then (1 : ℝ) else 0) - q23 0| := by
    fun_prop
  have hmeas : MeasurableSet
      {ω : Fin 2 → Fin 2 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if ω k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2} :=
    hms measurableSet_Ici
  have v00_0 : (if (![0, 0] : Fin 2 → Fin 2) (0 : Fin 2) = 0 then (1 : ℝ) else 0) = 1 := by
    simp
  have v00_1 : (if (![0, 0] : Fin 2 → Fin 2) (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 1 := by
    simp
  have v01_0 : (if (![0, 1] : Fin 2 → Fin 2) (0 : Fin 2) = 0 then (1 : ℝ) else 0) = 1 := by
    simp
  have v01_1 : (if (![0, 1] : Fin 2 → Fin 2) (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by
    simp
  have v10_0 : (if (![1, 0] : Fin 2 → Fin 2) (0 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by
    simp
  have v10_1 : (if (![1, 0] : Fin 2 → Fin 2) (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 1 := by
    simp
  have v11_0 : (if (![1, 1] : Fin 2 → Fin 2) (0 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by
    simp
  have v11_1 : (if (![1, 1] : Fin 2 → Fin 2) (1 : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by
    simp
  have s00 : ∑ k : Fin 2, (if (![0, 0] : Fin 2 → Fin 2) k = 0 then (1 : ℝ) else 0) = 2 := by
    rw [Fin.sum_univ_two, v00_0, v00_1]; norm_num
  have s01 : ∑ k : Fin 2, (if (![0, 1] : Fin 2 → Fin 2) k = 0 then (1 : ℝ) else 0) = 1 := by
    rw [Fin.sum_univ_two, v01_0, v01_1]; norm_num
  have s10 : ∑ k : Fin 2, (if (![1, 0] : Fin 2 → Fin 2) k = 0 then (1 : ℝ) else 0) = 1 := by
    rw [Fin.sum_univ_two, v10_0, v10_1]; norm_num
  have s11 : ∑ k : Fin 2, (if (![1, 1] : Fin 2 → Fin 2) k = 0 then (1 : ℝ) else 0) = 0 := by
    rw [Fin.sum_univ_two, v11_0, v11_1]; norm_num
  have d00 : ¬ |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if (![0, 0] : Fin 2 → Fin 2) k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2 := by
    have e : (1 / (2 : ℝ)) * 2 - 2 / 3 = 1 / 3 := by norm_num
    rw [s00, q23_zero, e, abs_of_nonneg (by norm_num)]; norm_num
  have d01 : ¬ |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if (![0, 1] : Fin 2 → Fin 2) k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2 := by
    have e : (1 / (2 : ℝ)) * 1 - 2 / 3 = -(1 / 6) := by norm_num
    rw [s01, q23_zero, e, abs_of_nonpos (by norm_num)]; norm_num
  have d10 : ¬ |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if (![1, 0] : Fin 2 → Fin 2) k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2 := by
    have e : (1 / (2 : ℝ)) * 1 - 2 / 3 = -(1 / 6) := by norm_num
    rw [s10, q23_zero, e, abs_of_nonpos (by norm_num)]; norm_num
  have d11 : |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if (![1, 1] : Fin 2 → Fin 2) k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2 := by
    have e : (1 / (2 : ℝ)) * 0 - 2 / 3 = -(2 / 3) := by norm_num
    rw [s11, q23_zero, e, abs_of_nonpos (by norm_num)]; norm_num
  have m00 : ¬ (![0, 0] : Fin 2 → Fin 2) ∈
      {ω : Fin 2 → Fin 2 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if ω k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2} := by
    simp only [Set.mem_setOf_eq]; exact d00
  have m01 : ¬ (![0, 1] : Fin 2 → Fin 2) ∈
      {ω : Fin 2 → Fin 2 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if ω k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2} := by
    simp only [Set.mem_setOf_eq]; exact d01
  have m10 : ¬ (![1, 0] : Fin 2 → Fin 2) ∈
      {ω : Fin 2 → Fin 2 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if ω k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2} := by
    simp only [Set.mem_setOf_eq]; exact d10
  have m11 : (![1, 1] : Fin 2 → Fin 2) ∈
      {ω : Fin 2 → Fin 2 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
        (if ω k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2} := by
    simp only [Set.mem_setOf_eq]; exact d11
  rw [PMF.toMeasure_apply _ _ hmeas, tsum_fintype, univ_fin2_fin2,
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton,
    Set.indicator_of_not_mem m00, Set.indicator_of_not_mem m01,
    Set.indicator_of_not_mem m10, Set.indicator_of_mem m11,
    zero_add, zero_add, zero_add]
  exact mass_11_QA

/-- **The generic theorem instantiated** at the two-sample fixture
(`q = ![2/3, 1/3]`, `i = 0`, `t = 1/2`), with the exponent evaluated
to `-1`. Conditional on `hoeffding_empirical`. -/
theorem twoSample_tail_instance_QA :
    (iidPMF q23 q23_nonneg q23_sum).toMeasure
      {ω : Fin 2 → Fin 2 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
            (if ω k = 0 then (1 : ℝ) else 0) - q23 0| ≥ 1 / 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ))) := by
  have h := hoeffding_empirical_iid q23_nonneg q23_sum two_ne_zero 0 (1 / 2)
    (by norm_num)
  have h' : -2 * ((2 : ℕ) : ℝ) * (1 / 2) ^ 2 = -(1 : ℝ) := by norm_num
  rw [h'] at h
  exact h

/-- The agreement pin: the event's measure computed raw (`1/9`) and
the axiom-backed bound (`2 exp (-1)`) meet the classical numeric
comparison `1/9 ≤ 2 exp (-1)` proved above from
`Real.add_one_le_exp` — the raw enumeration and the theorem instance
confronted at one number, through no shared mechanism. -/
theorem twoSample_agreement_QA :
    ENNReal.ofReal ((1 : ℝ) / 9) ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ))) :=
  ENNReal.ofReal_le_ofReal exp_lower_bound_QA

/-!
## Step 2 QA: the stationarity-limit form on the triangle
-/

/-- The true deviation at `t = 2` from vertex `0`, raw: the walk law
`(1/2, 1/4, 1/4)` against `π 0 = 1/3` — the value the bias term must
dominate. -/
theorem tri_stationary_deviation_two_QA :
    |walkDistribution triAdj 2 0 0 - stationaryVec triAdj 0| = 1/6 := by
  have h : walkDistribution triAdj 2 0 0 = 1/2 := by
    rw [tri_dist_two_QA]; simp
  have e : (1/2 : ℝ) - 1/3 = 1/6 := by norm_num
  rw [h, tri_pi_QA 0, e, abs_of_nonneg (by norm_num)]

/-- The bias term dominates the true deviation at the fixture: the
theorem's `r ^ t₀ √(π i ((π x)⁻¹ − 1))` (here `(1/2)² √(2/3)`) sits
above the raw `1/6` — the fold-in is honest slack, not tightness. -/
theorem tri_stationary_bias_two_le_QA :
    |walkDistribution triAdj 2 0 0 - stationaryVec triAdj 0|
      ≤ (1/2 : ℝ) ^ (2 : ℕ) * Real.sqrt (2/3) := by
  have hs : (2/3 : ℝ) ≤ Real.sqrt (2/3) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2/3),
      Real.sqrt_nonneg (2/3 : ℝ)]
  have hq : (1/2 : ℝ) ^ (2 : ℕ) = 1/4 := by norm_num
  rw [tri_stationary_deviation_two_QA, hq]
  calc (1/6 : ℝ) = (1/4) * (2/3) := by norm_num
    _ ≤ (1/4) * Real.sqrt (2/3) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)

/-- The general-form instance at `t₀ = 2`, `n = 2`, threshold
`1/2`: the bias-folded exponent at the honest certificate. -/
theorem tri_stationary_tail_bias_QA :
    (iidPMF (walkDistribution triAdj 2 0)
        (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 2 0)
        (sum_walkDistribution triAdj triAdj_deg_pos 2 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec triAdj 0| ≥ 1/2}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * 2 * (1/2 - (1/2 : ℝ) ^ (2 : ℕ)
          * Real.sqrt (2/3)) ^ 2)) := by
  have hb : (1/2 : ℝ) ^ (2 : ℕ)
      * Real.sqrt (stationaryVec triAdj 0
          * ((stationaryVec triAdj 0)⁻¹ - 1)) < 1/2 := by
    rw [tri_oversmoothingConstant_eq_QA 0 0]
    have hs : Real.sqrt (2/3) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (by norm_num : (2/3 : ℝ) ≤ 1)
      rwa [Real.sqrt_one] at h
    have hq : (1/2 : ℝ) ^ (2 : ℕ) = 1/4 := by norm_num
    rw [hq]
    linarith
  have h := empiricalWalkDistribution_stationary_tail triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (by norm_num)
    tri_rate_QA 2 0 0 two_ne_zero hb
  rw [tri_oversmoothingConstant_eq_QA 0 0] at h
  push_cast at h
  exact h

/-- **The depth-form capstone instance** — the consumer's own numbers:
past the delivered depth-3 certificate (at `ε / 2 = 1/8`), two
simulated trajectories of length `3` estimate `π 0` to `1/4` with
failure probability at most `2 exp (−1/16)`. -/
theorem tri_stationary_tail_depth_QA :
    (iidPMF (walkDistribution triAdj 3 0)
        (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 3 0)
        (sum_walkDistribution triAdj triAdj_deg_pos 3 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec triAdj 0| ≥ 1/4}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ) / 16)) := by
  have hthr : Real.log (Real.sqrt (stationaryVec triAdj 0
        * ((stationaryVec triAdj 0)⁻¹ - 1)) / ((1/4 : ℝ) / 2))
      / Real.log (1 / (1/2 : ℝ)) ≤ ((3 : ℕ) : ℝ) := by
    rw [tri_oversmoothingConstant_eq_QA 0 0]
    have h18 : (1/4 : ℝ) / 2 = 1/8 := by norm_num
    have h2 : 1 / (1/2 : ℝ) = 2 := by norm_num
    rw [h18, h2]
    exact_mod_cast tri_ceiling_threshold_three_QA
  have h := empiricalWalkDistribution_stationary_tail_of_depth triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (1/4) (by norm_num)
    (by norm_num) (by norm_num) tri_rate_QA 3 0 0 two_ne_zero hthr
  push_cast at h
  have e : (-2 : ℝ) * (1/4) ^ 2 / 2 = -(1 : ℝ) / 16 := by norm_num
  rw [e] at h
  exact h

/-- **Non-vacuity**: the depth-form instance's measured event genuinely
carries mass — the both-samples-at-`0` cylinder (mass `(1/4)² = 1/16`
at the `t₀ = 3` law) sits inside it, so the `2 exp (−1/16)` bound
bounds a real event, not an empty one. -/
theorem tri_stationary_event_ge_QA :
    ENNReal.ofReal (1 / 16) ≤
      (iidPMF (walkDistribution triAdj 3 0)
        (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 3 0)
        (sum_walkDistribution triAdj triAdj_deg_pos 3 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec triAdj 0| ≥ 1/4} := by
  have hq0 : walkDistribution triAdj 3 0 0 = 1/4 := by
    rw [tri_dist_three_zero_QA]; simp
  have hcyl : (iidPMF (walkDistribution triAdj 3 0)
      (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 3 0)
      (sum_walkDistribution triAdj triAdj_deg_pos 3 0)).toMeasure
      (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
        (fun ω : Fin 2 → Fin 3 => ω k) ⁻¹' ({0} : Set (Fin 3)))
      = ENNReal.ofReal (1 / 16) := by
    rw [toMeasure_cyl_inter _ _ _ Finset.univ
      (fun _ => ({0} : Set (Fin 3)))]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_eq_single (0 : Fin 3)]
    · rw [if_pos (Set.mem_singleton_iff.mpr rfl), hq0, one_mul, pow_two,
        ← ENNReal.ofReal_mul]
      norm_num
      norm_num
    · intro b _ hb
      rw [if_neg (fun h => hb (Set.mem_singleton_iff.mp h))]
      exact zero_mul _
    · intro h
      exact absurd (Finset.mem_univ _) h
  refine le_trans (le_of_eq hcyl.symm) (measure_mono ?_)
  intro ω hω
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hω
  simp only [Set.mem_setOf_eq]
  have hsum : ∑ k : Fin 2, (if ω k = 0 then (1 : ℝ) else 0) = 2 := by
    simp [hω]
  rw [hsum, tri_pi_QA 0]
  have e : (1 / (2 : ℝ)) * 2 - 1/3 = 2/3 := by norm_num
  rw [e, abs_of_nonneg (by norm_num)]
  norm_num

/-- **The fence: the bias-free naive form is materially false.** The
tempting shortcut — concluding around `stationaryVec` at the empirical
exponent `2 exp (−2 n t²)` with no bias term, i.e. treating the
`t₀`-step law as already stationary — is refuted at `t₀ = 0` on the
triangle: the sampler law is `δ₀`, the event `{|p̂ − 1/3| ≥ 2/3}`
contains the whole space (every sample is `0`, `p̂ = 1`, deviation
`2/3`), so its measure is `1`, against `2 exp (−16/9) < 1` from
`Real.add_one_lt_exp` (`exp (16/9) > 25/9 > 2`). The bias term —
equivalently, the depth — is load-bearing. -/
theorem tri_naive_stationary_refuted_QA :
    ¬ ((iidPMF (walkDistribution triAdj 0 0)
        (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 0 0)
        (sum_walkDistribution triAdj triAdj_deg_pos 0 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec triAdj 0| ≥ 2/3}
      ≤ ENNReal.ofReal (2 * Real.exp (-(16 : ℝ) / 9))) := by
  have hq0 : walkDistribution triAdj 0 0 0 = 1 := by
    rw [walkDistribution_zero]; simp
  have hcyl : (iidPMF (walkDistribution triAdj 0 0)
      (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 0 0)
      (sum_walkDistribution triAdj triAdj_deg_pos 0 0)).toMeasure
      (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
        (fun ω : Fin 2 → Fin 3 => ω k) ⁻¹' ({0} : Set (Fin 3)))
      = 1 := by
    rw [toMeasure_cyl_inter _ _ _ Finset.univ
      (fun _ => ({0} : Set (Fin 3)))]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_eq_single (0 : Fin 3)]
    · rw [if_pos (Set.mem_singleton_iff.mpr rfl), hq0, one_mul, pow_two,
        ENNReal.ofReal_one, one_mul]
    · intro b _ hb
      rw [if_neg (fun h => hb (Set.mem_singleton_iff.mp h))]
      exact zero_mul _
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hsub : (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
        (fun ω : Fin 2 → Fin 3 => ω k) ⁻¹' ({0} : Set (Fin 3)))
      ⊆ {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec triAdj 0| ≥ 2/3} := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp only [Set.mem_setOf_eq]
    have hsum : ∑ k : Fin 2, (if ω k = 0 then (1 : ℝ) else 0) = 2 := by
      simp [hω]
    rw [hsum, tri_pi_QA 0]
    have e : (1 / (2 : ℝ)) * 2 - 1/3 = 2/3 := by norm_num
    rw [e, abs_of_nonneg (by norm_num)]
  have hone : (1 : ℝ≥0∞) ≤ (iidPMF (walkDistribution triAdj 0 0)
      (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 0 0)
      (sum_walkDistribution triAdj triAdj_deg_pos 0 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec triAdj 0| ≥ 2/3} :=
    le_trans (le_of_eq hcyl.symm) (measure_mono hsub)
  intro hcontra
  have hnum : 2 * Real.exp (-(16 : ℝ) / 9) < 1 := by
    have hlow : (16 : ℝ) / 9 + 1 ≤ Real.exp (16 / 9) :=
      Real.add_one_le_exp (16 / 9)
    have hpos : (0 : ℝ) < 16 / 9 + 1 := by positivity
    have hinv : Real.exp (-(16 : ℝ) / 9) ≤ (16 / 9 + 1)⁻¹ := by
      rw [neg_div, Real.exp_neg]
      exact inv_anti₀ hpos hlow
    have hval : (16 : ℝ) / 9 + 1 = 25 / 9 := by norm_num
    rw [hval, inv_div] at hinv
    linarith
  have hlt : ENNReal.ofReal (2 * Real.exp (-(16 : ℝ) / 9)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact hnum
  exact lt_irrefl 1 (lt_of_le_of_lt hone (lt_of_le_of_lt hcontra hlt))

/-- **The `t₀ = 0` corner is admitted, not excluded**: the general form
instantiates soundly at zero depth — the bias is the honest large
`√(2/3)`, the threshold `1` clears it, and the event is genuinely
empty (the deviation `|p̂ − 1/3| ≤ 2/3 < 1` for every outcome), so the
bound holds with honest content rather than by exclusion. -/
theorem tri_stationary_tail_zero_depth_QA :
    (iidPMF (walkDistribution triAdj 0 0)
        (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 0 0)
        (sum_walkDistribution triAdj triAdj_deg_pos 0 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec triAdj 0| ≥ 1}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * 2 * (1 - Real.sqrt (2/3)) ^ 2)) := by
  have hb : (1/2 : ℝ) ^ (0 : ℕ)
      * Real.sqrt (stationaryVec triAdj 0
          * ((stationaryVec triAdj 0)⁻¹ - 1)) < 1 := by
    rw [pow_zero, one_mul, tri_oversmoothingConstant_eq_QA 0 0]
    have hs : Real.sqrt (2/3) < 1 := by
      have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2/3)
        (by norm_num : (2/3 : ℝ) < 1)
      rwa [Real.sqrt_one] at h
    linarith
  have h := empiricalWalkDistribution_stationary_tail (V := Fin 3)
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected (1/2)
    (by norm_num) tri_rate_QA 0 0 0 two_ne_zero hb
  rw [pow_zero, one_mul, tri_oversmoothingConstant_eq_QA 0 0] at h
  push_cast at h
  exact h

end Scaffold.Derived.EmpiricalStationary.QA
