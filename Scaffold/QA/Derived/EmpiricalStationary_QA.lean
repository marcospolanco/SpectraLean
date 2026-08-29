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

  The two `hoeffding_empirical`-consuming pins instantiate an
  admitted axiom; they check the interface and the classical numbers,
  and do not — and are not presented as — proving the axiom.

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

end Scaffold.Derived.EmpiricalStationary.QA
