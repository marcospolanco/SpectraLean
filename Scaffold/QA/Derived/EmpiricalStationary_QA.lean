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

  5. the lazy section (`proposals/
      empirical-lazy-stationary-sampling.md`, delivered 2026-09-01) —
      the lazy twins' instances on the **bipartite path**, the fixture
      class the plain program cannot reach: the fixed-time instance,
      **the plain-certificate unsatisfiability fence** (no `r ∈ (0, 1)`
      rate certificate for the plain walk exists on the path —
      `chiSquareDistance_le_of_connected` at a would-be certificate
      against the pinned `χ²_plain(center) ≡ 1` forces `r² ≥ 1`), the
      bias-term instance at the pinned intrinsic rate `(1/2)² · √3/2`
      with the raw true deviation `1/8` dominated beside it, the
      depth-form capstone instance closing at `2 exp (−1/16)` past the
      same `log (4√3)/log 2 ≤ 3` threshold the delivered lazy-ceiling
      QA pinned, the event-mass non-vacuity witness (`25/256`), and the
      exact-stationary contrast from the center start (true deviation
      `0` at every `t₀ ≥ 1`, the quoted bias honestly positive).

  6. the self-contained PageRank capstone section
      (`proposals/selfcontained-empirical-pagerank.md`, delivered
      2026-09-02) — the theorem that *produces* its own target `π`,
      QA'd on the identification obligation first: **any vector
      carrying the theorem's certificate clauses equals the
      hand-verified `u2`** (through the proved `∃!`'s uniqueness
      clause — the composition's falsification surface), the display
      threshold pinned (`⌈log 8/log 2⌉ = 3` at `ε = 1/4`), the
      display form's slack witnessed against the exact uniform object
      (`2 < 3`), and the fully-self-contained instance at `t₀ = 3`,
      every start, bound `2 exp (−1/32)`.

  7. the primitivity-supplier section
     (`proposals/primitivity-supplier-plain-walk.md`, 2026-09-02): the
     supplier's `IsPrimitive` output instantiated on the triangle through
     the odd walk `0 → 1 → 2 → 0`, the primitive square pinned
     (`P² = (1/4)(J − I)` with the `m = 1` diagonal-zero fence), the
     Doeblin rate attained *exactly* at the even time `t = 2` (both the
     truth `1/6` and the engine's `(1/4)^{2/2} · (2/3)` evaluate equal)
     with the odd-time factor-`2` slack pinned beside it, the `K₂`
     periodicity fence (no odd power of the edge's walk matrix returns —
     the `hodd` hypothesis exactly isolating the bipartite class), the
     self-contained capstone instantiated at `ε = 1/4` with the produced
     threshold's arithmetic (`K = ⌈log 8/log 4⌉ = 2`) and its honest
     slack witnessed on the truth side (`TV(ν₂) = 1/6 > 1/8`), and the
     convergence corollary instantiated;

  8. the capstone's consumer fences
     (`proposals/adversarial-fences-primitivity-supplier-family.md`'s
     priced follow-on, delivered 2026-09-03): the self-contained
     capstone's two graph clauses closed with hypothesis-form fences —
     `hp` at `K₂` (connectivity genuine, every closed walk even; past
     any threshold the even-time law from `0` is `δ₀`, the sampling
     measure concentrates on the all-zero trajectory, the deviation
     event carries the full mass `1 > 2 exp(−4)`) and `hconn` at
     `triIso4` started at the absorbing vertex `x = 3` (a genuine odd
     closed walk and every walk-level clause genuine, but the law is
     `δ₃` at *every* time — convergent to the wrong vector while the
     deviation `|1 − 1/7| = 6/7` carries full mass) — plus the shared
     point-mass cylinder helper (`toMeasure_cyl_singleton_one`, the
     measure-of-singleton machinery: one `toMeasure_cyl_inter`
     application collapsing to a single factor) and isolation
     companions attributing each failure to its clause alone.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/
import Scaffold.Derived.EmpiricalStationary
import Scaffold.QA.SpectralGraph.Mixing_QA
import Scaffold.QA.Probability.IIDProduct_QA
import Scaffold.QA.SpectralGraph.DirectedMixing_QA

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

/-!
## The lazy twins on the bipartite path (2026-09-01)

`proposals/empirical-lazy-stationary-sampling.md`: the lazy
stationarity-limit theorems instantiated on the three-vertex path — the
fixture class where the plain program's `r < 1` certificate is provably
unsatisfiable (fenced below), so only the lazy twins certify anything.
-/

local notation "pathL" => normalizedLaplacian pathAdj
local notation "pathH" => normalizedLaplacian_symmetric pathAdj pathAdj_isSymm

/-- The fixed-time instance on the bipartite path: `n = 2` samples of
the one-step lazy law from the corner, threshold `1`, bound
`2 exp (−4)` — the lazy law's probability-vector certification
exercised at a genuinely lazy input. -/
theorem path_lazy_tail_instance_QA :
    (iidPMF (lazyWalkDistribution pathAdj 1 0)
        (lazyWalkDistribution_nonneg pathAdj pathAdj_nonneg
          pathAdj_deg_pos 1 0)
        (sum_lazyWalkDistribution pathAdj pathAdj_deg_pos 1 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0)
          - lazyWalkDistribution pathAdj 1 0 0| ≥ 1}
      ≤ ENNReal.ofReal (2 * Real.exp (-4)) := by
  have h := empiricalLazyWalkDistribution_tail (V := Fin 3)
    pathAdj_nonneg pathAdj_deg_pos 1 0 two_ne_zero 0 1
    zero_le_one
  have h' : -2 * ((2 : ℕ) : ℝ) * (1 : ℝ) ^ 2 = -4 := by norm_num
  rw [h'] at h
  exact h

/-- **The leverage case made negative**: no `r ∈ (0, 1)` rate
certificate for the *plain* walk exists on the bipartite path — the
plain capstone `empiricalWalkDistribution_stationary_tail_of_depth`'s
hypothesis set is provably unsatisfiable there. Route: a would-be
certificate fed to the proved `chiSquareDistance_le_of_connected`
bounds the plain χ² from the center start by `r² · ((π center)⁻¹ − 1) =
r²`, against the pinned `path_plain_never_QA` (`χ²_plain(center, t)
≡ 1` at every time) — forcing `r² ≥ 1`. The lazy capstone instantiates
on this same fixture (`path_lazy_capstone_depth_QA` below): the
periodicity fix read at the sampling level. -/
theorem path_plain_cert_fenced_QA :
    ¬ ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i : Fin 3,
      eigvalOf pathL pathH i ≠ 0 →
        |1 - eigvalOf pathL pathH i| ≤ r := by
  rintro ⟨r, hr0, hr1, hrate⟩
  have h := chiSquareDistance_le_of_connected pathAdj pathAdj_isSymm
    pathAdj_nonneg pathAdj_deg_pos path_connected r 1 1 hrate
  rw [path_plain_never_QA 1] at h
  have hπ : stationaryVec pathAdj 1 = 1/2 := by
    rw [path_pi_QA]; rfl
  rw [hπ] at h
  norm_num at h
  rw [abs_of_pos hr0] at h
  linarith

/-- The corner-start bias constant, raw: `√(π 0 · ((π 0)⁻¹ − 1)) =
√3/2` at the pinned stationary vector. -/
theorem path_lazy_corner_biasConstant_QA :
    Real.sqrt (stationaryVec pathAdj 0 * ((stationaryVec pathAdj 0)⁻¹ - 1))
      = Real.sqrt 3 / 2 := by
  have hπ0 : stationaryVec pathAdj 0 = 1/4 := by
    rw [path_pi_QA]; rfl
  have hin : stationaryVec pathAdj 0 * ((stationaryVec pathAdj 0)⁻¹ - 1)
      = 3/4 := by
    rw [hπ0]
    norm_num
  have h2 : Real.sqrt ((4 : ℝ)) = 2 := by
    rw [show ((4 : ℝ)) = (2 : ℝ) ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hin, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 3) 4, h2]

/-- **The bias-term instance on the bipartite path** — the fixture class
the plain twin cannot reach: corner start, `t₀ = 2`, `n = 2`, threshold
`1/2`, the bias computed at the pinned intrinsic rate `(1/2)^2 · √3/2
= √3/8` (the true deviation `|ν_lazy(2) − π 0|` pinned raw beside it
in `path_lazy_corner_deviation_two_QA`, dominated with honest slack in
`path_lazy_corner_bias_two_le_QA`). -/
theorem path_lazy_stationary_tail_bias_QA :
    (iidPMF (lazyWalkDistribution pathAdj 2 0)
        (lazyWalkDistribution_nonneg pathAdj pathAdj_nonneg
          pathAdj_deg_pos 2 0)
        (sum_lazyWalkDistribution pathAdj pathAdj_deg_pos 2 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec pathAdj 0| ≥ 1/2}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (2 : ℝ)
          * (1/2 - (1/2 : ℝ) ^ (2 : ℕ) * (Real.sqrt 3 / 2)) ^ 2)) := by
  have hs3 : Real.sqrt 3 ≤ 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (3 : ℝ) ≤ 4)
    rwa [show ((4 : ℝ)) = 2 ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hb : (1 - secondEval pathL pathH
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) ^ (2 : ℕ)
      * Real.sqrt (stationaryVec pathAdj 0
          * ((stationaryVec pathAdj 0)⁻¹ - 1)) < 1/2 := by
    rw [path_lazy_corner_biasConstant_QA]
    have hrate : (1 - secondEval pathL pathH
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) = 1/2 := by
      rw [path_secondEval_QA]
      norm_num
    rw [hrate]
    have he : (1/2 : ℝ) ^ (2 : ℕ) * (Real.sqrt 3 / 2) = Real.sqrt 3 / 8 := by
      ring
    rw [he, div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)]
    linarith
  have h := empiricalLazyWalkDistribution_stationary_tail (V := Fin 3)
    pathAdj_isSymm pathAdj_nonneg pathAdj_deg_pos
    (by norm_num : 2 ≤ Fintype.card (Fin 3)) path_connected 2 0 0 two_ne_zero hb
  have hrate : (1 - secondEval pathL pathH
      (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) = 1/2 := by
    rw [path_secondEval_QA]
    norm_num
  have hπ0 : stationaryVec pathAdj 0 = 1/4 := by
    rw [path_pi_QA]; rfl
  rw [path_lazy_corner_biasConstant_QA, hrate, hπ0] at h
  rw [hπ0]
  push_cast at h
  exact h

/-- The lazy law on the path from the corner at `t = 2` (one more
adjoint lazy step applied to the pinned `t = 1` law). -/
theorem path_lazy_corner_law_two_QA :
    lazyWalkDistribution pathAdj 2 0 = ![3/8, 1/2, 1/8] := by
  show lazyWalkDistribution pathAdj (1 + 1) 0 = ![3/8, 1/2, 1/8]
  rw [lazyWalkDistribution_succ, path_lazy_corner_law_one_QA]
  funext i
  fin_cases i
  all_goals simp [lazyWalkTransitionMatrix, walkTransitionMatrix, deg, pathAdj,
    Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three]
  all_goals norm_num

theorem path_lazy_corner_deviation_two_QA :
    |lazyWalkDistribution pathAdj 2 0 0 - stationaryVec pathAdj 0| = 1/8 := by
  have h : lazyWalkDistribution pathAdj 2 0 0 = 3/8 := by
    rw [path_lazy_corner_law_two_QA]; simp
  have hπ0 : stationaryVec pathAdj 0 = 1/4 := by
    rw [path_pi_QA]; rfl
  rw [h, hπ0]
  norm_num

/-- The bias term dominates the true deviation at the fixture — the
fold-in is honest slack, not tightness: `1/8 ≤ √3/8`. -/
theorem path_lazy_corner_bias_two_le_QA :
    |lazyWalkDistribution pathAdj 2 0 0 - stationaryVec pathAdj 0|
      ≤ (1/2 : ℝ) ^ (2 : ℕ) * (Real.sqrt 3 / 2) := by
  rw [path_lazy_corner_deviation_two_QA]
  have hq : (1/2 : ℝ) ^ (2 : ℕ) = 1/4 := by norm_num
  have hs : (1 : ℝ) ≤ Real.sqrt 3 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 3)
    rwa [Real.sqrt_one] at h
  rw [hq]
  calc (1/8 : ℝ) = (1/8) * 1 := by norm_num
    _ ≤ (1/8) * Real.sqrt 3 := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = (1/4) * (Real.sqrt 3 / 2) := by ring

/-- The capstone's threshold on the path's corner start, at the pinned
intrinsic rate: `log (√3/2 / (1/8)) / log 2 = log (4√3)/log 2 ≤ 3` —
the same threshold the delivered lazy-ceiling QA pinned
(`path_lazy_corner_ceiling_slack_QA`). -/
theorem path_lazy_capstone_threshold_QA :
    Real.log (Real.sqrt (stationaryVec pathAdj 0
        * ((stationaryVec pathAdj 0)⁻¹ - 1)) / ((1/4 : ℝ) / 2))
      / Real.log (1 / (1 - secondEval pathL pathH
          (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2))
      ≤ ((3 : ℕ) : ℝ) := by
  have hrate : (1 - secondEval pathL pathH
      (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) = 1/2 := by
    rw [path_secondEval_QA]
    norm_num
  have hone : (1 : ℝ) / (1/2) = 2 := by norm_num
  rw [path_lazy_corner_biasConstant_QA, hrate, hone]
  have he : ((1/4 : ℝ)) / 2 = 1/8 := by norm_num
  rw [he]
  have hratio : (Real.sqrt 3 / 2) / ((1/8 : ℝ)) = 4 * Real.sqrt 3 := by
    field_simp
    ring
  rw [hratio]
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog8 : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
    rw [show ((8 : ℝ)) = ((2 : ℝ)) ^ 3 from by norm_num, Real.log_pow 2 3]
    push_cast
    ring
  have hs3 : Real.sqrt 3 ≤ 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (3 : ℝ) ≤ 4)
    rwa [show ((4 : ℝ)) = 2 ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hup : (4 : ℝ) * Real.sqrt 3 ≤ 8 := by nlinarith
  have hle3 : Real.log ((4 : ℝ) * Real.sqrt 3) / Real.log 2 ≤ (3 : ℝ) := by
    rw [div_le_iff₀ hlog2, ← hlog8]
    exact Real.log_le_log (by positivity) hup
  exact_mod_cast hle3

/-- **The depth-form capstone instance on the bipartite path**: past
the `log(4√3)/log 2 ≤ 3` threshold at `ε = 1/4`, two simulated lazy
trajectories of length `3` estimate `π 0` to `1/4` with failure
probability at most `2 exp (−1/16)`. On the fixture where the plain
capstone's hypothesis set is provably unsatisfiable
(`path_plain_cert_fenced_QA`) — the periodicity fix delivered at the
sampling level. -/
theorem path_lazy_capstone_depth_QA :
    (iidPMF (lazyWalkDistribution pathAdj 3 0)
        (lazyWalkDistribution_nonneg pathAdj pathAdj_nonneg
          pathAdj_deg_pos 3 0)
        (sum_lazyWalkDistribution pathAdj pathAdj_deg_pos 3 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec pathAdj 0| ≥ 1/4}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ) / 16)) := by
  have hslt : secondEval pathL pathH
      (by norm_num : 2 ≤ Fintype.card (Fin 3)) < 2 := by
    rw [path_secondEval_QA]
    norm_num
  have h := empiricalLazyWalkDistribution_stationary_tail_of_depth (V := Fin 3)
    pathAdj_isSymm pathAdj_nonneg pathAdj_deg_pos
    (by norm_num : 2 ≤ Fintype.card (Fin 3)) path_connected hslt (ε := 1/4)
    (by norm_num) 3 0 0 two_ne_zero path_lazy_capstone_threshold_QA
  push_cast at h
  have e : (-(2 : ℝ) * (1/4) ^ 2 / 2) = -(1 : ℝ) / 16 := by norm_num
  rw [e] at h
  exact h

/-- The corner-start lazy law at `t = 3`, one entry: `5/16` (one more
adjoint lazy step applied to the pinned `t = 2` law). -/
theorem path_lazy_corner_entry_three_QA :
    lazyWalkDistribution pathAdj 3 0 0 = 5/16 := by
  show lazyWalkDistribution pathAdj (2 + 1) 0 0 = 5/16
  rw [lazyWalkDistribution_succ, path_lazy_corner_law_two_QA]
  simp [lazyWalkTransitionMatrix, walkTransitionMatrix, deg, pathAdj,
    Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three]
  norm_num

/-- **Non-vacuity**: the capstone instance's measured event genuinely
carries mass — the both-samples-at-`0` cylinder (mass `(5/16)² =
25/256` at the `t₀ = 3` law) sits inside it (`p̂ = 1`, deviation
`3/4 ≥ 1/4`), so the `2 exp (−1/16)` bound bounds a real event, not an
empty one. -/
theorem path_lazy_capstone_event_ge_QA :
    ENNReal.ofReal (25 / 256) ≤
      (iidPMF (lazyWalkDistribution pathAdj 3 0)
        (lazyWalkDistribution_nonneg pathAdj pathAdj_nonneg
          pathAdj_deg_pos 3 0)
        (sum_lazyWalkDistribution pathAdj pathAdj_deg_pos 3 0)).toMeasure
      {ω : Fin 2 → Fin 3 | |(1 / (2 : ℝ)) * ∑ k : Fin 2,
          (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec pathAdj 0| ≥ 1/4} := by
  have hq0 : lazyWalkDistribution pathAdj 3 0 0 = 5/16 :=
    path_lazy_corner_entry_three_QA
  have hcyl : (iidPMF (lazyWalkDistribution pathAdj 3 0)
      (lazyWalkDistribution_nonneg pathAdj pathAdj_nonneg
        pathAdj_deg_pos 3 0)
      (sum_lazyWalkDistribution pathAdj pathAdj_deg_pos 3 0)).toMeasure
      (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
        (fun ω : Fin 2 → Fin 3 => ω k) ⁻¹' ({0} : Set (Fin 3)))
      = ENNReal.ofReal (25 / 256) := by
    rw [toMeasure_cyl_inter _ _ _ Finset.univ
      (fun _ => ({0} : Set (Fin 3)))]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_eq_single (0 : Fin 3)]
    · rw [if_pos (Set.mem_singleton_iff.mpr rfl), hq0, one_mul, pow_two,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5/16)]
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
  have hπ0 : stationaryVec pathAdj 0 = 1/4 := by
    rw [path_pi_QA]; rfl
  rw [hsum, hπ0]
  have e : (1 / (2 : ℝ)) * 2 - 1/4 = 3/4 := by norm_num
  rw [e, abs_of_nonneg (by norm_num)]
  norm_num

/-- **The exact-stationary contrast**: from the path's center start the
lazy law is *exactly* stationary at every `t₀ ≥ 1` (the pinned
`path_lazy_center_mix_all_QA` — the true deviation is `0`), while the
bias-term theorem still quotes the honest *positive* bias
`(1/2)^t₀ · √(π i · 1)` — the theorem never claims the bias vanishes,
even where the truth does. The slack is the price of the certificate's
generality, witnessed on the fixture where it is maximal. -/
theorem path_lazy_center_contrast_QA (t₀ : ℕ) (i : Fin 3) (ht : 1 ≤ t₀) :
    |lazyWalkDistribution pathAdj t₀ 1 i - stationaryVec pathAdj i| = 0
      ∧ 0 < (1 - secondEval pathL pathH
          (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) ^ t₀
          * Real.sqrt (stationaryVec pathAdj i
              * ((stationaryVec pathAdj 1)⁻¹ - 1)) := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, t₀ = 1 + k := ⟨t₀ - 1, by omega⟩
  rw [hk]
  refine ⟨?_, ?_⟩
  · rw [path_lazy_center_mix_all_QA k]
    simp
  · have hrate : (1 - secondEval pathL pathH
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) = 1/2 := by
      rw [path_secondEval_QA]
      norm_num
    have hπ : (stationaryVec pathAdj 1)⁻¹ - 1 = 1 := by
      have h : stationaryVec pathAdj 1 = 1/2 := by
        rw [path_pi_QA]; rfl
      rw [h]
      norm_num
    have hπpos : 0 < stationaryVec pathAdj i :=
      stationaryVec_pos pathAdj pathAdj_deg_pos i
    rw [hrate, hπ]
    exact mul_pos (pow_pos (by norm_num) _)
      (Real.sqrt_pos.mpr (by rw [mul_one]; exact hπpos))


/-!
## The PageRank capstone instances

The directed `t_mix` object's named consumer
(`proposals/directed-mixing-time-object.md`, 2026-09-02), instantiated
on `DirectedMixing_QA`'s Section G fixture (the periodic 2-cycle's
Google matrix at `α = 1/2`, uniform stationary `u2`, the object pinned
`t_mix(1/8) = 2`): the bias-term instance at `2 exp (−1/8)` and the
depth-form capstone instance at `2 exp (−1/32)` — one simulated
random-surfer trajectory of length `2` estimates the PageRank weight
`u2 1 = 1/2` to `1/4`. The **uniform capstone instance**
(`PRU_capstone_instance_QA`, 2026-09-02,
`proposals/directed-uniform-mixing-time.md`) instantiates the
worst-start twin at the same numbers, at the start `x = 1` — the same
*uniform* threshold pin `t_mix^unif(1/8) = 2` certifying the start
whose per-start pin it subsumes.
-/
section PageRankCapstone

open Scaffold.Mathlib.Probability.IIDProduct MeasureTheory
open Scaffold.QA.SpectralGraph SpectralGraphTheory

/-- **The bias-term instance**: on the fixture at `t₀ = 1`, the quoted
bias is `α^1 · TV(δ_0, u2) = 1/4` and the bound at threshold `1/2`
reads `2 exp (−2 · (1/2 − 1/4)²) = 2 exp (−1/8)`. -/
theorem PR_bias_instance_QA :
    (iidPMF (pageRankDistribution A2 (1/2) 1 0)
        (fun j => pageRankDistribution_nonneg A2 A2_nonneg_QA A2_deg_QA
          (by norm_num) (by norm_num) 1 0 j)
        (sum_pageRankDistribution A2 A2_deg_QA (1/2) 1 0)).toMeasure
      {ω : Fin 1 → Fin 2 | |(1 / (1 : ℝ)) * ∑ k : Fin 1,
          (if ω k = 1 then (1 : ℝ) else 0) - u2 1| ≥ 1/2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1/8))) := by
  have htv : tvDistance (Pi.single (0 : Fin 2) (1 : ℝ)) u2 = 1/2 := by
    rw [piSingle_zero_eq_e0]; exact tv_e0_u2
  have h := empiricalPageRank_stationary_tail (A := A2) (t := 1/2)
    A2_nonneg_QA A2_deg_QA (by norm_num) (by norm_num) u2_sum
    u2_stationary_Gd 1 0 1 one_ne_zero (by rw [pow_one, htv]; norm_num)
  rw [pow_one, htv] at h
  push_cast at h
  have e : (1/2 : ℝ) - (1/2) * (1/2) = 1/4 := by norm_num
  rw [e] at h
  have e2 : (-2 : ℝ) * (1 : ℝ) * (1/4) ^ 2 = -(1/8) := by norm_num
  rw [e2] at h
  exact h

/-- **The capstone instance**: past the directed mixing time at
`ε/2 = 1/8` — exactly the pinned `t_mix = 2` — one simulated
random-surfer trajectory of length `2` estimates the PageRank weight
`u2 1 = 1/2` to `ε = 1/4` with failure probability at most
`2 exp (−1/32)`. -/
theorem PR_capstone_instance_QA :
    (iidPMF (pageRankDistribution A2 (1/2) 2 0)
        (fun j => pageRankDistribution_nonneg A2 A2_nonneg_QA A2_deg_QA
          (by norm_num) (by norm_num) 2 0 j)
        (sum_pageRankDistribution A2 A2_deg_QA (1/2) 2 0)).toMeasure
      {ω : Fin 1 → Fin 2 | |(1 / (1 : ℝ)) * ∑ k : Fin 1,
          (if ω k = 1 then (1 : ℝ) else 0) - u2 1| ≥ 1/4}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ) / 32)) := by
  have h := empiricalPageRank_stationary_tail_of_depth (A := A2)
    A2_nonneg_QA A2_deg_QA (by norm_num) (by norm_num) u2_sum
    u2_stationary_Gd (by norm_num : (0 : ℝ) < 1/4) 2 0 1 one_ne_zero
    (by rw [show ((1/4 : ℝ) / 2) = 1/8 from by norm_num]
        rw [PR_tmix_eighth_QA])
  push_cast at h
  have e : (-(1 : ℝ)) * (1/4) ^ 2 / 2 = -(1 : ℝ) / 32 := by norm_num
  rw [e] at h
  exact h

/-- **The worst-start capstone instance**: the *same* uniform threshold
pin `t_mix^unif(1/8) = 2` certifies one simulated random-surfer
trajectory of length `2` from *either* start to estimate the PageRank
weight `u2 1 = 1/2` to `ε = 1/4` at `2 exp (−1/32)` — instantiated
here at the start `x = 1`, the start whose per-start pin the uniform
certificate subsumes. -/
theorem PRU_capstone_instance_QA :
    (iidPMF (pageRankDistribution A2 (1/2) 2 1)
        (fun j => pageRankDistribution_nonneg A2 A2_nonneg_QA A2_deg_QA
          (by norm_num) (by norm_num) 2 1 j)
        (sum_pageRankDistribution A2 A2_deg_QA (1/2) 2 1)).toMeasure
      {ω : Fin 1 → Fin 2 | |(1 / (1 : ℝ)) * ∑ k : Fin 1,
          (if ω k = 1 then (1 : ℝ) else 0) - u2 1| ≥ 1/4}
      ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ) / 32)) := by
  have h := empiricalPageRank_uniform_tail_of_depth (A := A2)
    A2_nonneg_QA A2_deg_QA (by norm_num) (by norm_num) u2_nonneg u2_sum
    u2_stationary_Gd (by norm_num : (0 : ℝ) < 1/4) 2 1 one_ne_zero
    (by rw [show ((1/4 : ℝ) / 2) = 1/8 from by norm_num]
        rw [PRU_tmix_eighth_QA])
  have h1 := h 1
  push_cast at h1
  have e : (-(1 : ℝ)) * (1/4) ^ 2 / 2 = -(1 : ℝ) / 32 := by norm_num
  rw [e] at h1
  exact h1

end PageRankCapstone

/-!
## The self-contained PageRank capstone section

The self-contained composition's QA
(`proposals/selfcontained-empirical-pagerank.md`, 2026-09-02): the
theorem produces its own target `π`, so the QA's first obligation is
to prove the produced vector is *the right one* — the identification
pin runs any vector carrying the theorem's three certificate clauses
through the proved `∃!`'s uniqueness clause against the hand-verified
`u2`. Beside it: the display threshold pinned (`⌈log 8/log 2⌉ = 3` at
`ε = 1/4`), the display form's slack witnessed against the exact
uniform object (`2 < 3`), and the fully-self-contained instance (the
theorem instantiated, the vector identified, the guarantee discharged
at `t₀ = 3` for *every* start, closing at `2 exp (−1/32)`).
-/
section PageRankSelfContained

open scoped Matrix
open Scaffold.Mathlib.Probability.IIDProduct MeasureTheory
open Scaffold.QA.SpectralGraph SpectralGraphTheory

/-- **The identification pin**: any vector carrying the self-contained
theorem's three certificate clauses (strict positivity, mass one,
stationarity at the fixture's Google matrix) equals the hand-verified
`u2` — through the proved `existsUnique_pageRankVec`'s uniqueness
clause. This is the composition's falsification surface: the theorem
hands the agent an opaque vector, and this pin proves the certificate
clauses pin it exactly. Load-bearing on the re-proved stationary
layer's exact statement. -/
theorem PR_selfcontained_vec_QA {π : Fin 2 → ℝ}
    (hpos : ∀ j, 0 < π j) (hsum : ∑ j, π j = 1)
    (hstat : π ᵥ* googleMatrix A2 (1/2) = π) : π = u2 := by
  obtain ⟨π', -, huniq⟩ := existsUnique_pageRankVec A2 A2_nonneg_QA A2_deg_QA
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
  exact (huniq π ⟨fun j => le_of_lt (hpos j), hsum, hstat⟩).trans
    (huniq u2 ⟨u2_nonneg, u2_sum, u2_stationary_Gd⟩).symm

/-- **The threshold pin**: the self-contained theorem's display
threshold at `ε = 1/4` is exactly `⌈log 8 / log 2⌉ = 3` — the
`(α, ε)`-computable bound the agent uses, pinned (joining the uniform
display ceiling's own arithmetic at `2/ε = 8 = 1/(1/8)`). -/
theorem PR_selfcontained_threshold_QA :
    Nat.ceil (Real.log (2 / (1/4:ℝ)) / Real.log (1 / (1/2:ℝ))) = 3 := by
  have h2 : (2:ℝ) / (1/4) = 8 := by norm_num
  have h8 : (8:ℝ) = 1 / (1/8:ℝ) := by norm_num
  rw [h2, h8]
  exact PRU_display_ceiling_arith_QA

/-- **The display-slack witness**: the start-free display threshold
(`3`) is strictly coarser than the exact uniform object (`2`, the
pinned `t_mix^unif(1/8)`) — the simplex diameter's price made visible
on the fixture where the exact object is known. The self-contained
theorem's threshold is honest about being the display bound. -/
theorem PR_selfcontained_display_slack_QA :
    pageRankMixingTime A2 (1/2) u2 (1/8)
      < Nat.ceil (Real.log (2 / (1/4:ℝ)) / Real.log (1 / (1/2:ℝ))) := by
  rw [PRU_tmix_eighth_QA, PR_selfcontained_threshold_QA]
  norm_num

/-- **The fully-self-contained instance**: the theorem instantiated at
the fixture (`ε = 1/4`, `n = 1`, `i = 1`) — the produced vector is
exactly `u2` (the identification pin) and the guarantee clause
discharges at `t₀ = 3` (the pinned display threshold) for *every*
start, closing at `2 exp (−1/32)`. No hypothesis about `π` anywhere:
the theorem supplies it, the QA proves it is the right one. -/
theorem PR_selfcontained_instance_QA :
    ∃ π : Fin 2 → ℝ, π = u2 ∧
      ∀ (x : Fin 2),
        (iidPMF (pageRankDistribution A2 (1/2) 3 x)
            (fun j => pageRankDistribution_nonneg A2 A2_nonneg_QA A2_deg_QA
              (by norm_num) (by norm_num) 3 x j)
            (sum_pageRankDistribution A2 A2_deg_QA (1/2) 3 x)).toMeasure
          {ω : Fin 1 → Fin 2 | |(1 / (1 : ℝ)) * ∑ k : Fin 1,
              (if ω k = 1 then (1 : ℝ) else 0) - u2 1| ≥ 1/4}
          ≤ ENNReal.ofReal (2 * Real.exp (-(1 : ℝ) / 32)) := by
  obtain ⟨π, hpos, hsum, hstat, hguar⟩ :=
    empiricalPageRank_tail_selfcontained_of_depth (A := A2) A2_nonneg_QA A2_deg_QA
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1/4) 1 one_ne_zero
  have hπu2 : π = u2 := PR_selfcontained_vec_QA hpos hsum hstat
  refine ⟨π, hπu2, fun x => ?_⟩
  have h := hguar 3 (by rw [PR_selfcontained_threshold_QA]) x
  rw [hπu2] at h
  push_cast at h
  have e : (-(1 : ℝ)) * (1/4) ^ 2 / 2 = -(1 : ℝ) / 32 := by norm_num
  rw [e] at h
  exact h

end PageRankSelfContained

section Primitivity

open Filter

/-! ## The primitivity supplier and the self-contained plain-walk
capstone QA -/

/-! ### The triangle's walk matrix, its primitive square, and the odd
closed walk witness -/

theorem triP_apply (i j : Fin 3) :
    walkTransitionMatrix triAdj i j = (1/2) * triAdj i j := by
  rw [walkTransitionMatrix_apply, triAdj_deg_eq]
  norm_num

/-- The primitive square's entry table: `P² = (1/4)(J − I)` — diagonal
`1/2`, off-diagonal `1/4`, so `m = 2` is a primitive power with floor
`δ = 1/4` (`triP_one_diag_zero_QA` below shows `m = 1` is not). -/
theorem triP_two_apply (i j : Fin 3) :
    (walkTransitionMatrix triAdj ^ 2) i j = if i = j then 1/2 else 1/4 := by
  rw [pow_two, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [triP_apply, triAdj_apply, Fin.sum_univ_three] <;> norm_num

theorem triP_one_diag_zero_QA : (walkTransitionMatrix triAdj ^ 1) 0 0 = 0 := by
  rw [pow_one, triP_apply, triAdj_apply, if_pos rfl, mul_zero]

/-- The triangle's odd closed walk: around `0 → 1 → 2 → 0`. -/
def triWalk3 : (supportGraph triAdj triAdj_isSymm).Walk 0 0 := by
  have e01 : (supportGraph triAdj triAdj_isSymm).Adj 0 1 :=
    supportGraph_adj.mpr ⟨by decide, by
      rw [triAdj_apply, if_neg (show ¬((0 : Fin 3) = 1) from by decide)];
      norm_num⟩
  have e12 : (supportGraph triAdj triAdj_isSymm).Adj 1 2 :=
    supportGraph_adj.mpr ⟨by decide, by
      rw [triAdj_apply, if_neg (show ¬((1 : Fin 3) = 2) from by decide)];
      norm_num⟩
  have e20 : (supportGraph triAdj triAdj_isSymm).Adj 2 0 :=
    supportGraph_adj.mpr ⟨by decide, by
      rw [triAdj_apply, if_neg (show ¬((2 : Fin 3) = 0) from by decide)];
      norm_num⟩
  exact SimpleGraph.Walk.cons e01
    (SimpleGraph.Walk.cons e12 (SimpleGraph.Walk.cons e20
      SimpleGraph.Walk.nil))

theorem triWalk3_length : triWalk3.length = 3 := by
  simp [triWalk3]

theorem triWalk3_odd : Odd triWalk3.length := ⟨1, by
  rw [triWalk3_length]; norm_num⟩

/-- **The supplier instantiated**: the triangle's walk matrix is
primitive — the standing handoff's blocker discharged on the canonical
non-bipartite fixture. -/
theorem tri_isPrimitive_QA : (walkTransitionMatrix triAdj).IsPrimitive :=
  walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk triAdj
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected triWalk3 triWalk3_odd

/-! ### The rate: attainment at even times, slack at odd -/

theorem tri_tv_zero_eq_QA :
    tvDistance (Pi.single (0 : Fin 3) (1 : ℝ)) (stationaryVec triAdj) = 2/3 := by
  have h1 : ¬((1 : Fin 3) = 0) := by decide
  have h2 : ¬((2 : Fin 3) = 0) := by decide
  simp only [tvDistance, Pi.single_apply, tri_pi_QA, Fin.sum_univ_three,
    if_pos rfl, if_neg h1, if_neg h2, if_true]
  rw [show ((1 : ℝ) - 1/3) = 2/3 from by norm_num,
    show ((0 : ℝ) - 1/3) = -(1/3) from by norm_num, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2/3),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/3)]
  norm_num

theorem tri_tv_two_eq_QA :
    tvDistance (walkDistribution triAdj 2 0) (stationaryVec triAdj) = 1/6 := by
  have e0 : walkDistribution triAdj 2 0 0 = 1/2 := by
    rw [tri_dist_two_QA]; rfl
  have e1 : walkDistribution triAdj 2 0 1 = 1/4 := by
    rw [tri_dist_two_QA]; rfl
  have e2 : walkDistribution triAdj 2 0 2 = 1/4 := by
    rw [tri_dist_two_QA]; rfl
  rw [tvDistance, Fin.sum_univ_three, e0, e1, e2, tri_pi_QA, tri_pi_QA,
    tri_pi_QA, show ((1 : ℝ)/2 - 1/3) = 1/6 from by norm_num,
    show ((1 : ℝ)/4 - 1/3) = -(1/12) from by norm_num, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/6),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/12)]
  norm_num

theorem tri_tv_three_eq_QA :
    tvDistance (walkDistribution triAdj 3 0) (stationaryVec triAdj) = 1/12 := by
  have e0 : walkDistribution triAdj 3 0 0 = 1/4 := by
    rw [tri_dist_three_zero_QA]; rfl
  have e1 : walkDistribution triAdj 3 0 1 = 3/8 := by
    rw [tri_dist_three_zero_QA]; rfl
  have e2 : walkDistribution triAdj 3 0 2 = 3/8 := by
    rw [tri_dist_three_zero_QA]; rfl
  rw [tvDistance, Fin.sum_univ_three, e0, e1, e2, tri_pi_QA, tri_pi_QA,
    tri_pi_QA, show ((1 : ℝ)/4 - 1/3) = -(1/12) from by norm_num,
    show ((3 : ℝ)/8 - 1/3) = 1/24 from by norm_num, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/12),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/24)]
  norm_num

/-- **The engine attained exactly at the even time `t = 2`**: both the
truth `TV(ν₂, π) = 1/6` and the engine's right side
`(1 − 3·(1/4))^{2/2} · TV(δ₀, π) = (1/4)(2/3)` evaluate to `1/6` —
the Doeblin rate's start factor is exactly right on the fixture, not
merely an upper bound. -/
theorem tri_engine_two_attained_QA :
    tvDistance (walkDistribution triAdj 2 0) (stationaryVec triAdj)
      = (1 - (Fintype.card (Fin 3) : ℝ) * (1/4)) ^ (2 / 2)
        * tvDistance (Pi.single (0 : Fin 3) (1 : ℝ)) (stationaryVec triAdj) := by
  rw [tri_tv_two_eq_QA, tri_tv_zero_eq_QA]
  simp only [Fintype.card_fin]
  norm_num

theorem tri_rate_le_QA (t : ℕ) (x : Fin 3) :
    tvDistance (walkDistribution triAdj t x) (stationaryVec triAdj)
      ≤ (1 - (Fintype.card (Fin 3) : ℝ) * (1/4)) ^ (t / 2) := by
  refine walkDistribution_tvDistance_le_of_pos_power triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos ?_ t x
  intro a b
  rw [triP_two_apply]
  split <;> norm_num

/-- **The odd-time slack pinned**: at `t = 3` the bound is `(1/4)^1 =
1/4` against the truth `1/12` — exactly the factor `2` the `t/m` floor
leaves on the table at odd times (the truth decays as `(1/2)^t`,
the block rate as `(1/4)^{⌊t/2⌋}`). -/
theorem tri_rate_three_slack_QA :
    (1/12 : ℝ)
      < (1 - (Fintype.card (Fin 3) : ℝ) * (1/4)) ^ (3 / 2) := by
  norm_num

/-! ### The periodicity fence: the odd-walk hypothesis load-bearing -/

theorem k2P_apply (i j : Fin 2) :
    walkTransitionMatrix k2Adj i j = k2Adj i j := by
  rw [walkTransitionMatrix_apply, k2Adj_deg_eq]
  norm_num

theorem k2P_two_eq_one : walkTransitionMatrix k2Adj ^ 2 = 1 := by
  funext i j
  rw [pow_two, Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [k2P_apply, k2Adj_apply, Fin.sum_univ_two]

/-- **No odd power of the edge's walk matrix returns**: `(P^t) 0 0 = 0`
at every odd `t` — the supplier's `hodd` hypothesis is unsatisfiable
on the bipartite fixture, exactly the class the lazy program was built
to patch. The supplier's hypothesis set is what separates the triangle
from the edge. -/
theorem k2_odd_diag_zero_QA (t : ℕ) (ht : Odd t) :
    (walkTransitionMatrix k2Adj ^ t) 0 0 = 0 := by
  obtain ⟨q, hq⟩ := ht
  have hsplit : walkTransitionMatrix k2Adj ^ t
      = (walkTransitionMatrix k2Adj ^ 2) ^ q * walkTransitionMatrix k2Adj := by
    rw [hq, pow_add, pow_one, ← pow_mul]
  rw [hsplit, k2P_two_eq_one, one_pow, Matrix.one_mul, k2P_apply,
    k2Adj_apply, if_pos rfl]

/-! ### The self-contained capstone instantiated -/

/-- The produced threshold's arithmetic: `K = ⌈log (2/ε) / log (1/ρ)⌉`
at `ε = 1/4`, `ρ = 1/4` is `⌈log 8 / log 4⌉ = ⌈3/2⌉ = 2`. -/
theorem tri_threshold_arith_QA :
    Nat.ceil (Real.log (2 / (1/4 : ℝ))
      / Real.log (1 / (1 - (3 : ℝ) * (1/4)))) = 2 := by
  have hr1 : (2 : ℝ) / (1/4) = 8 := by norm_num
  have hr2 : (1 : ℝ) / (1 - (3:ℝ) * (1/4)) = 4 := by norm_num
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 from by norm_num, Real.log_pow (2 : ℝ) 3]
    push_cast
    ring
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow (2 : ℝ) 2]
    push_cast
    ring
  have hlog2ne : Real.log 2 ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  have hdiv : (3 : ℝ) * Real.log 2 / (2 * Real.log 2) = 3/2 := by
    field_simp
    ring
  have hle : (3 : ℝ) / 2 ≤ 2 := by norm_num
  have hge : (1 : ℝ) < 3/2 := by norm_num
  rw [hr1, hr2, hlog8, hlog4, hdiv]
  have hceil_le : Nat.ceil ((3 : ℝ) / 2) ≤ 2 := Nat.ceil_le.mpr hle
  have hceil_ge : 2 ≤ Nat.ceil ((3 : ℝ) / 2) := by
    have h1 : (1 : ℕ) < Nat.ceil ((3 : ℝ) / 2) := by
      rw [Nat.lt_ceil]
      norm_num
    omega
  omega

/-- The bias half at the produced threshold: past `s = 4` the bias term
`ρ^{s/2} · TV(δ₀, π)` is at most `(1/4)²·(2/3) = 1/24 ≤ 1/8 = ε/2`. -/
theorem tri_bias_four_le_QA :
    (1 - (Fintype.card (Fin 3) : ℝ) * (1/4)) ^ (4 / 2)
      * tvDistance (Pi.single (0 : Fin 3) (1 : ℝ)) (stationaryVec triAdj)
      ≤ (1/4) / 2 := by
  rw [tri_tv_zero_eq_QA]
  simp only [Fintype.card_fin]
  norm_num

/-- **The produced threshold's honest slack**: at `s = 2` the true TV
distance is still `1/6 > 1/8 = ε/2` — no threshold below `3` could
make the truth-side concentration premise hold, so the produced `t₀ =
4` (from `K = 2`, `m = 2`) is one past the truth's minimum, not a
loose display artifact hiding a much smaller certificate. -/
theorem tri_tv_two_gt_half_QA :
    (1/4) / 2 < tvDistance (walkDistribution triAdj 2 0)
      (stationaryVec triAdj) := by
  rw [tri_tv_two_eq_QA]
  norm_num

/-- **The fully-self-contained instance**: the theorem's `∃ t₀`
instantiated on the triangle at `ε = 1/4`, target `i = 0` — no
caller-supplied rate, no caller-supplied stationarity: connectivity
and the odd walk `0 → 1 → 2 → 0` are the entire hypothesis set. -/
theorem tri_selfcontained_instance_QA {n : ℕ} (hn : n ≠ 0) :
    ∃ t₀ : ℕ, ∀ s : ℕ, t₀ ≤ s → ∀ x : Fin 3,
      (iidPMF (walkDistribution triAdj s x)
        (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos s x)
        (sum_walkDistribution triAdj triAdj_deg_pos s x)).toMeasure
        {ω : Fin n → Fin 3 | |(1 / (n : ℝ)) * ∑ k : Fin n,
            (if ω k = 0 then (1 : ℝ) else 0) - stationaryVec triAdj 0| ≥ 1/4}
        ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * (1/4) ^ 2 / 2)) :=
  empiricalWalkDistribution_tail_selfcontained_of_depth (A := triAdj)
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected
    (w := 0) triWalk3 triWalk3_odd (by norm_num : (0:ℝ) < 1/4) 0 hn

/-- The convergence corollary instantiated: the plain walk law on the
triangle converges to the uniform stationary vector — the retired
`primitive_power_tendsto`'s first undirected consumer on its fixture. -/
theorem tri_tendsto_instance_QA :
    Filter.Tendsto (fun t : ℕ => walkDistribution triAdj t 0) Filter.atTop
      (nhds (stationaryVec triAdj)) :=
  walkDistribution_tendsto_stationaryVec (A := triAdj) triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (w := 0) triWalk3 triWalk3_odd 0

end Primitivity

/-!
## The primitivity-supplier family's adversarial fences (2026-09-03)

`proposals/adversarial-fences-primitivity-supplier-family.md`: the
audit-shaped adversarial pass over the primitivity-supplier family —
`PrimitiveConvergence.lean`'s concatenation/bounce/supplier trio,
`Mixing.lean`'s walk-to-power bridge, walk-level supplier, plain-walk
Doeblin rate, and convergence corollary — the mixing cascade's last
unaudited family (its QA was delivered 2026-09-02 by its own run and
never independently re-read). Every load-bearing clause with no
negative witness anywhere in the repository, closed with a
hypothesis-form fence plus isolation companion; the fixtures include
the exact-cube rotation `!![1,-3;1,1]` (`M^3 = -8*1`), the directed
3-cycle permutation (no reciprocal pair anywhere), the
negative-diagonal triangle `negDiagTri` (the negative weight is
invisible to the support graph; the closed forms carry the
antisymmetric eigenvalue `-11/4`), and the triangle-plus-isolated-
vertex `triIso4` (cross-block power entries identically zero, the
absorbed law `delta_3 != pi`). Pure hard crust, zero axiom contact.
-/

section PrimitivityFences

open Filter
open scoped Matrix

/-! ## The engine fences (`PrimitiveConvergence.lean`) -/

section EngineFences

/-! ### Fixtures -/

/-- Concatenation fixture: negative diagonal, positive seed entries. -/
def concatNeg : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![-2, 1; 0, 1]

theorem concatNeg_00 : concatNeg 0 0 = -2 := by rw [concatNeg]; rfl
theorem concatNeg_01 : concatNeg 0 1 = 1 := by rw [concatNeg]; rfl
theorem concatNeg_11 : concatNeg 1 1 = 1 := by rw [concatNeg]; rfl

theorem concatNeg_not_nonneg : ¬ (∀ i j : Fin 2, 0 ≤ concatNeg i j) := by
  intro h
  have := h 0 0
  rw [concatNeg_00] at this
  norm_num at this

/-- **The `hnn` fence for concatenation positivity**: with `i = 0`,
`k = 1`, `j = 1`, `a = b = 1` both seed entries are genuinely positive
while the off-path negative diagonal makes the defining sum negative:
`(M²) 0 1 = (−2)(1) + (1)(1) = −1`. -/
theorem concat_pos_hnn_fence_QA :
    ¬ (0 < (concatNeg ^ (1 + 1)) 0 1) := by
  have h1 : 0 < (concatNeg ^ 1) 0 1 := by
    rw [pow_one, concatNeg_01]
    norm_num
  have h2 : 0 < (concatNeg ^ 1) 1 1 := by
    rw [pow_one, concatNeg_11]
    norm_num
  -- isolation companions: h1, h2 genuine; hnn failing (concatNeg_not_nonneg)
  rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two, concatNeg_00,
    concatNeg_01, concatNeg_11]
  norm_num

/-- Bounce fixture: negative off-diagonal, positive loop. -/
def bounceNeg : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![1, -2; 1, 1]

theorem bounceNeg_00 : bounceNeg 0 0 = 1 := by rw [bounceNeg]; rfl
theorem bounceNeg_01 : bounceNeg 0 1 = -2 := by rw [bounceNeg]; rfl
theorem bounceNeg_10 : bounceNeg 1 0 = 1 := by rw [bounceNeg]; rfl
theorem bounceNeg_11 : bounceNeg 1 1 = 1 := by rw [bounceNeg]; rfl

theorem bounceNeg_not_nonneg : ¬ (∀ i j : Fin 2, 0 ≤ bounceNeg i j) := by
  intro h
  have := h 0 1
  rw [bounceNeg_01] at this
  norm_num at this

/-- **The `hnn` fence for the bounce**: at `u = v = 0`, `e = 0`,
`z = 0`, `n = 1` the seed and both bounce entries are genuinely
positive (`(M⁰) 0 0 = 1`, `M 0 0 = 1` both ways), but the off-path
entry `M 0 1 = −2` makes `(M²) 0 0 = 1·1 + (−2)·1 = −1`. -/
theorem bounce_hnn_fence_QA : ¬ (0 < (bounceNeg ^ (0 + 2 * 1)) 0 0) := by
  have h1 : 0 < (bounceNeg ^ 0) 0 0 := by
    rw [pow_zero, Matrix.one_apply, if_pos rfl]
    norm_num
  have hz1 : 0 < bounceNeg 0 0 := by rw [bounceNeg_00]; norm_num
  have hz2 : 0 < bounceNeg 0 0 := by rw [bounceNeg_00]; norm_num
  show ¬ (0 < (bounceNeg ^ 2) 0 0)
  rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two, bounceNeg_00,
    bounceNeg_01, bounceNeg_10]
  norm_num

/-- No-up bounce fixture: `hz1` fails (`M 0 1 = 0`), `hz2` genuine. -/
def bounceNoUp : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![0, 0; 1, 1]

theorem bounceNoUp_01 : bounceNoUp 0 1 = 0 := by rw [bounceNoUp]; rfl
theorem bounceNoUp_10 : bounceNoUp 1 0 = 1 := by rw [bounceNoUp]; rfl

theorem bounceNoUp_nonneg (i j : Fin 2) : 0 ≤ bounceNoUp i j := by
  fin_cases i <;> fin_cases j <;> simp [bounceNoUp]

/-- **The `hz1` fence for the bounce**: at `v = 0`, `z = 1` the
up-step is zero while the down-step and the `e = 0` seed are genuine;
`(M²) 0 0 = 0`. -/
theorem bounce_hz1_fence_QA : ¬ (0 < (bounceNoUp ^ (0 + 2 * 1)) 0 0) := by
  have h1 : 0 < (bounceNoUp ^ 0) 0 0 := by
    rw [pow_zero, Matrix.one_apply, if_pos rfl]
    norm_num
  have hz1 : ¬ (0 < bounceNoUp 0 1) := by rw [bounceNoUp_01]; norm_num
  have hz2 : 0 < bounceNoUp 1 0 := by rw [bounceNoUp_10]; norm_num
  show ¬ (0 < (bounceNoUp ^ 2) 0 0)
  rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [bounceNoUp]

/-- No-down bounce fixture: `hz2` fails (`M 1 0 = 0`), `hz1` genuine. -/
def bounceNoDown : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![0, 1; 0, 1]

theorem bounceNoDown_01 : bounceNoDown 0 1 = 1 := by rw [bounceNoDown]; rfl
theorem bounceNoDown_10 : bounceNoDown 1 0 = 0 := by rw [bounceNoDown]; rfl

theorem bounceNoDown_nonneg (i j : Fin 2) : 0 ≤ bounceNoDown i j := by
  fin_cases i <;> fin_cases j <;> simp [bounceNoDown]

/-- **The `hz2` fence for the bounce**: at `v = 0`, `z = 1` the
down-step is zero while the up-step and the seed are genuine;
`(M²) 0 0 = 0`. -/
theorem bounce_hz2_fence_QA : ¬ (0 < (bounceNoDown ^ (0 + 2 * 1)) 0 0) := by
  have h1 : 0 < (bounceNoDown ^ 0) 0 0 := by
    rw [pow_zero, Matrix.one_apply, if_pos rfl]
    norm_num
  have hz1 : 0 < bounceNoDown 0 1 := by rw [bounceNoDown_01]; norm_num
  have hz2 : ¬ (0 < bounceNoDown 1 0) := by rw [bounceNoDown_10]; norm_num
  show ¬ (0 < (bounceNoDown ^ 2) 0 0)
  rw [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  norm_num [bounceNoDown]

/-- The swap matrix (the walk matrix of `K₂`): kills the seed
hypotheses `h1`/`h2` of the concatenation lemmas. -/
def swap2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![0, 1; 1, 0]

theorem swap2_00 : swap2 0 0 = 0 := by rw [swap2]; rfl
theorem swap2_01 : swap2 0 1 = 1 := by rw [swap2]; rfl
theorem swap2_11 : swap2 1 1 = 0 := by rw [swap2]; rfl

theorem swap2_sq : swap2 ^ 2 = 1 := by
  funext i j
  rw [pow_two, Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp [swap2, Fin.sum_univ_two]

theorem swap2_nonneg (i j : Fin 2) : 0 ≤ swap2 i j := by
  fin_cases i <;> fin_cases j <;> simp [swap2]

theorem swap2_sq_01 : (swap2 ^ 2) 0 1 = 0 := by
  rw [swap2_sq]; rfl

/-- **The `h1` fence for concatenation positivity**: at `i = 0`,
`k = 0`, `j = 1`, `a = b = 1` the second seed is genuine but the
first is zero (the identity diagonal), and `(M²) 0 1 = 0`. -/
theorem concat_pos_h1_fence_QA : ¬ (0 < (swap2 ^ (1 + 1)) 0 1) := by
  have h1 : ¬ (0 < (swap2 ^ 1) 0 0) := by
    rw [pow_one, swap2_00]
    norm_num
  have h2 : 0 < (swap2 ^ 1) 0 1 := by
    rw [pow_one, swap2_01]
    norm_num
  rw [swap2_sq_01]
  norm_num

/-- **The `h2` fence for concatenation positivity**: at `i = 0`,
`k = 1`, `j = 1` the first seed is genuine but the second is zero,
and `(M²) 0 1 = 0`. -/
theorem concat_pos_h2_fence_QA : ¬ (0 < (swap2 ^ (1 + 1)) 0 1) := by
  have h1 : 0 < (swap2 ^ 1) 0 1 := by
    rw [pow_one, swap2_01]
    norm_num
  have h2 : ¬ (0 < (swap2 ^ 1) 1 1) := by
    rw [pow_one, swap2_11]
    norm_num
  rw [swap2_sq_01]
  norm_num

/-- **The `h1` fence for the bounce**: at `u = 0`, `v = 1`, `z = 0`,
`e = 0`, `n = 1` both bounce entries are genuine but the seed
`(M⁰) 0 1 = 0` fails, and `(M²) 0 1 = 0`. -/
theorem bounce_h1_fence_QA : ¬ (0 < (swap2 ^ (0 + 2 * 1)) 0 1) := by
  have h1 : ¬ (0 < (swap2 ^ 0) 0 1) := by
    rw [pow_zero, Matrix.one_apply, if_neg (by decide)]
    norm_num
  have hz1 : 0 < swap2 1 0 := by rw [swap2]; norm_num
  have hz2 : 0 < swap2 0 1 := swap2_01 ▸ by norm_num
  rw [swap2_sq_01]
  norm_num

/-! ### The `hodd` fence at the swap (the bipartite class) -/

theorem swap2_apply (i j : Fin 2) : swap2 i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem fin2_eq (v : Fin 2) : v = 0 ∨ v = 1 := by
  have hv : v.val < 2 := v.isLt
  rcases (show v.val = 0 ∨ v.val = 1 by omega) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext (show v.val = (1 : Fin 2).val by simpa using h))

theorem fin3_eq (v : Fin 3) : v = 0 ∨ v = 1 ∨ v = 2 := by
  have hv : v.val < 3 := v.isLt
  rcases (show v.val = 0 ∨ v.val = 1 ∨ v.val = 2 by omega) with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext (show v.val = (1 : Fin 3).val by simpa using h)))
  · exact Or.inr (Or.inr (Fin.ext (show v.val = (2 : Fin 3).val by simpa using h)))

theorem swap2_even_offdiag_zero (q : ℕ) :
    (swap2 ^ (2 * q)) 0 1 = 0 := by
  rw [pow_mul, swap2_sq, one_pow]
  show (if (0 : Fin 2) = 1 then (1:ℝ) else 0) = 0
  rw [if_neg (by decide)]

theorem swap2_odd_diag_zero (t : ℕ) (ht : Odd t) :
    (swap2 ^ t) 0 0 = 0 := by
  obtain ⟨q, hq⟩ := ht
  rw [hq, pow_add, pow_one, pow_mul, swap2_sq, one_pow, Matrix.one_mul,
    swap2_apply, if_pos rfl]

/-- The swap's reachability witnesses: `hreach` genuine. -/
theorem swap2_reach : ∀ u v : Fin 2, ∃ a : ℕ, 0 < (swap2 ^ a) u v := by
  intro u v
  fin_cases u <;> fin_cases v
  · exact ⟨2, by rw [swap2_sq]; simp [Matrix.one_apply]⟩
  · exact ⟨1, by rw [pow_one, swap2_apply, if_neg (by decide)]; norm_num⟩
  · exact ⟨1, by rw [pow_one, swap2_apply, if_neg (by decide)]; norm_num⟩
  · exact ⟨2, by rw [swap2_sq]; simp [Matrix.one_apply]⟩

/-- The swap's positive 2-cycles: `htwo` genuine. -/
theorem swap2_two_cycle : ∀ v : Fin 2, ∃ z : Fin 2,
    0 < swap2 v z ∧ 0 < swap2 z v := by
  intro v
  rcases fin2_eq v with h | h
  · subst h
    exact ⟨1, by rw [swap2_apply, if_neg (by decide)]; norm_num,
      by rw [swap2_apply, if_neg (by decide)]; norm_num⟩
  · subst h
    exact ⟨0, by rw [swap2_apply, if_neg (by decide)]; norm_num,
      by rw [swap2_apply, if_neg (by decide)]; norm_num⟩

/-- **The `hodd` fence for the supplier**: at the swap every
hypothesis except the odd closed loop is genuine — nonnegative,
reachable (diagonal at `a = 2`, off-diagonal at `a = 1`), reciprocal
2-cycles — but every odd power has zero diagonal and every even power
is the identity, so no power is entrywise positive. -/
theorem sup_hodd_fence_QA : ¬ swap2.IsPrimitive := by
  rintro ⟨k, hk, hpos⟩
  rcases Nat.even_or_odd k with ⟨q, hq⟩ | hq
  · have hk2 : k = 2 * q := by omega
    exact absurd (hpos 0 1) (by rw [hk2, swap2_even_offdiag_zero]; norm_num)
  · exact absurd (hpos 0 0) (by rw [swap2_odd_diag_zero k hq]; norm_num)

theorem swap2_no_odd_loop :
    ¬ (∃ t : ℕ, Odd t ∧ 0 < (swap2 ^ t) 0 0) := by
  rintro ⟨t, ht, hpos⟩
  rw [swap2_odd_diag_zero t ht] at hpos
  norm_num at hpos

/-! ### The `hreach` fence at the identity -/

theorem ident2_offdiag_zero (k : ℕ) :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) ^ k) 0 1 = 0 := by
  rw [one_pow]
  show (if (0 : Fin 2) = 1 then (1:ℝ) else 0) = 0
  rw [if_neg (by decide)]

/-- The identity's self-loop 2-cycles: `htwo` genuine. -/
theorem ident2_two_cycle : ∀ v : Fin 2, ∃ z : Fin 2,
    0 < (1 : Matrix (Fin 2) (Fin 2) ℝ) v z ∧
      0 < (1 : Matrix (Fin 2) (Fin 2) ℝ) z v := fun v =>
  ⟨v, by simp [Matrix.one_apply], by simp [Matrix.one_apply]⟩

/-- **The `hreach` fence for the supplier**: at the identity matrix
`htwo` (self-loops) and `hodd` (`t = 1`) are genuine, but `(0,1)` has
no positive power entry at all — the unreachable pair. -/
theorem sup_hreach_fence_QA :
    ¬ (1 : Matrix (Fin 2) (Fin 2) ℝ).IsPrimitive := by
  rintro ⟨k, hk, hpos⟩
  exact absurd (hpos 0 1) (by rw [ident2_offdiag_zero]; norm_num)

theorem ident2_no_reach :
    ¬ (∃ a : ℕ, 0 < ((1 : Matrix (Fin 2) (Fin 2) ℝ) ^ a) 0 1) := by
  rintro ⟨a, hpos⟩
  rw [ident2_offdiag_zero] at hpos
  norm_num at hpos

/-! ### The `htwo` fence at the directed 3-cycle -/

/-- The directed 3-cycle permutation: strongly connected with an odd
loop (`cycle3 ^ 3 = 1`) but no reciprocal positive pair anywhere. -/
def cycle3 : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem cycle3_apply (i j : Fin 3) :
    cycle3 i j = if i = 0 ∧ j = 1 then 1
      else if i = 1 ∧ j = 2 then 1
      else if i = 2 ∧ j = 0 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem cycle3_nonneg (i j : Fin 3) : 0 ≤ cycle3 i j := by
  simp only [cycle3_apply]
  split_ifs <;> norm_num

theorem cycle3_sq_apply (i j : Fin 3) :
    (cycle3 ^ 2) i j = if i = 0 ∧ j = 2 then 1
      else if i = 1 ∧ j = 0 then 1
      else if i = 2 ∧ j = 1 then 1 else 0 := by
  rw [pow_two, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;>
    simp [cycle3_apply, Fin.sum_univ_three]

theorem cycle3_sq_02 : (cycle3 ^ 2) 0 2 = 1 := by rw [cycle3_sq_apply]; rfl
theorem cycle3_sq_10 : (cycle3 ^ 2) 1 0 = 1 := by rw [cycle3_sq_apply]; rfl
theorem cycle3_sq_21 : (cycle3 ^ 2) 2 1 = 1 := by rw [cycle3_sq_apply]; rfl
theorem cycle3_sq_00 : (cycle3 ^ 2) 0 0 = 0 := by rw [cycle3_sq_apply]; rfl

theorem cycle3_cube : cycle3 ^ 3 = 1 := by
  have hstep : cycle3 ^ 3 = cycle3 ^ 2 * cycle3 := pow_succ cycle3 2
  rw [hstep]
  funext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [cycle3_sq_apply, cycle3_apply, Fin.sum_univ_three]

theorem cycle3_02 : cycle3 0 2 = 0 := by rw [cycle3]; rfl
theorem cycle3_01 : cycle3 0 1 = 1 := by rw [cycle3]; rfl
theorem cycle3_00 : cycle3 0 0 = 0 := by rw [cycle3]; rfl
theorem cycle3_10 : cycle3 1 0 = 0 := by rw [cycle3]; rfl
theorem cycle3_12 : cycle3 1 2 = 1 := by rw [cycle3]; rfl
theorem cycle3_20 : cycle3 2 0 = 1 := by rw [cycle3]; rfl

/-- The 3-cycle's reachability witnesses (`hreach` genuine). -/
theorem cycle3_reach : ∀ u v : Fin 3, ∃ a : ℕ, 0 < (cycle3 ^ a) u v := by
  intro u v
  rcases fin3_eq u with hu | hu | hu <;> rcases fin3_eq v with hv | hv | hv
  · subst hu; subst hv
    exact ⟨3, by rw [cycle3_cube]; simp [Matrix.one_apply]⟩
  · subst hu; subst hv
    exact ⟨1, by rw [pow_one, cycle3_01]; norm_num⟩
  · subst hu; subst hv
    exact ⟨2, by rw [cycle3_sq_02]; norm_num⟩
  · subst hu; subst hv
    exact ⟨2, by rw [cycle3_sq_10]; norm_num⟩
  · subst hu; subst hv
    exact ⟨3, by rw [cycle3_cube]; simp [Matrix.one_apply]⟩
  · subst hu; subst hv
    exact ⟨1, by rw [pow_one, cycle3_12]; norm_num⟩
  · subst hu; subst hv
    exact ⟨1, by rw [pow_one, cycle3_20]; norm_num⟩
  · subst hu; subst hv
    exact ⟨2, by rw [cycle3_sq_21]; norm_num⟩
  · subst hu; subst hv
    exact ⟨3, by rw [cycle3_cube]; simp [Matrix.one_apply]⟩

/-- The 3-cycle's odd closed loops (`hodd` genuine, `t = 3`). -/
theorem cycle3_odd_loop : ∀ v : Fin 3, ∃ t : ℕ,
    Odd t ∧ 0 < (cycle3 ^ t) v v := fun _ =>
  ⟨3, ⟨1, by norm_num⟩, by rw [cycle3_cube]; simp [Matrix.one_apply]⟩

/-- **The `htwo` fence for the supplier**: at the 3-cycle permutation
`hreach` and `hodd` are genuine (period 3), but vertex `0` has no
reciprocal positive pair — every power is a permutation matrix with a
zero entry. -/
theorem sup_htwo_fence_QA : ¬ cycle3.IsPrimitive := by
  rintro ⟨k, hk, hpos⟩
  obtain ⟨q, r, hr, hmod⟩ :
      ∃ q r, k = 3 * q + r ∧ r < 3 :=
    ⟨k / 3, k % 3, (Nat.div_add_mod k 3).symm, Nat.mod_lt k (by omega)⟩
  rcases r with _ | _ | _ | r'
  · refine absurd (hpos 0 1) ?_
    have hentry : (cycle3 ^ k) 0 1 = 0 := by
      rw [hr, pow_add, pow_mul, cycle3_cube, one_pow, pow_zero,
        Matrix.one_mul]
      rfl
    rw [hentry]; norm_num
  · refine absurd (hpos 0 2) ?_
    have hentry : (cycle3 ^ k) 0 2 = 0 := by
      rw [hr, pow_add, pow_mul, cycle3_cube, one_pow, pow_one,
        Matrix.one_mul, cycle3_02]
    rw [hentry]; norm_num
  · refine absurd (hpos 0 0) ?_
    have hentry : (cycle3 ^ k) 0 0 = 0 := by
      rw [hr, pow_add, pow_mul, cycle3_cube, one_pow, Matrix.one_mul,
        cycle3_sq_00]
    rw [hentry]; norm_num
  · exact absurd hmod (by omega)

theorem cycle3_no_two_cycle :
    ¬ (∃ z : Fin 3, 0 < cycle3 0 z ∧ 0 < cycle3 z 0) := by
  rintro ⟨z, h1, h2⟩
  rcases fin3_eq z with h | h | h
  · subst h
    rw [cycle3_00] at h1
    norm_num at h1
  · subst h
    rw [cycle3_10] at h2
    norm_num at h2
  · subst h
    rw [cycle3_02] at h1
    norm_num at h1

/-! ### The `hnn` fence at the exact-cube rotation -/

/-- The rotation-dilation fixture: `M³ = −8 · 1`, so every power is a
signed multiple of `1`, `M`, or `M²`, each of which has a nonpositive
entry that no sign flip repairs everywhere at once. -/
def rot2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of !![1, -3; 1, 1]

theorem rot2_00 : rot2 0 0 = 1 := by rw [rot2]; rfl
theorem rot2_01 : rot2 0 1 = -3 := by rw [rot2]; rfl
theorem rot2_10 : rot2 1 0 = 1 := by rw [rot2]; rfl
theorem rot2_11 : rot2 1 1 = 1 := by rw [rot2]; rfl

theorem rot2_apply (i j : Fin 2) :
    rot2 i j = if i = 0 ∧ j = 1 then -3 else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem rot2_not_nonneg : ¬ (∀ i j : Fin 2, 0 ≤ rot2 i j) := by
  intro h
  have := h 0 1
  rw [rot2_01] at this
  norm_num at this

theorem rot2_sq_apply (i j : Fin 2) :
    (rot2 ^ 2) i j = if i = j then -2 else if i = 0 then -6 else 2 := by
  rw [pow_two, Matrix.mul_apply]
  fin_cases i <;> fin_cases j <;> simp [rot2_apply, Fin.sum_univ_two] <;>
    norm_num

theorem rot2_sq_00 : (rot2 ^ 2) 0 0 = -2 := by rw [rot2_sq_apply]; rfl
theorem rot2_sq_10 : (rot2 ^ 2) 1 0 = 2 := by rw [rot2_sq_apply]; rfl

theorem rot2_cube_eq : rot2 ^ 3 = (-8 : ℝ) • 1 := by
  have hstep : rot2 ^ 3 = rot2 ^ 2 * rot2 := pow_succ rot2 2
  rw [hstep]
  funext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [rot2_sq_apply, rot2_apply, Fin.sum_univ_two, Matrix.smul_apply,
      Matrix.one_apply] <;>
    norm_num

theorem rot2_pow_three_mul (q : ℕ) :
    rot2 ^ (3 * q) = ((-8 : ℝ) ^ q) • 1 := by
  induction q with
  | zero => rw [show (3:ℕ) * 0 = 0 by omega, pow_zero, pow_zero, one_smul]
  | succ q ih =>
    rw [show (3:ℕ) * (q + 1) = 3 * q + 3 by ring, pow_add, ih, rot2_cube_eq,
      pow_succ, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_one]

/-- The rotation fixture's reachability witnesses (`hreach` genuine,
through the exact cube: diagonals at `a = 6` via `M⁶ = 64 · 1`, the
`(0,1)` pair at `a = 4` via `M⁴ = −8 · M`). -/
theorem rot2_reach : ∀ u v : Fin 2, ∃ a : ℕ, 0 < (rot2 ^ a) u v := by
  intro u v
  rcases fin2_eq u with hu | hu <;> rcases fin2_eq v with hv | hv
  · subst hu; subst hv
    refine ⟨6, ?_⟩
    rw [show (6:ℕ) = 3 * 2 by omega, rot2_pow_three_mul, Matrix.smul_apply,
      Matrix.one_apply, if_pos rfl]
    norm_num
  · subst hu; subst hv
    refine ⟨4, ?_⟩
    have h4 : rot2 ^ 4 = ((-8 : ℝ) ^ 1) • rot2 := by
      rw [show (4:ℕ) = 3 * 1 + 1 by omega, pow_add, rot2_pow_three_mul,
        Matrix.smul_mul, one_mul, pow_one, pow_one]
    rw [h4, Matrix.smul_apply, rot2_01]
    norm_num
  · subst hu; subst hv
    exact ⟨1, by rw [pow_one, rot2_10]; norm_num⟩
  · subst hu; subst hv
    refine ⟨6, ?_⟩
    rw [show (6:ℕ) = 3 * 2 by omega, rot2_pow_three_mul, Matrix.smul_apply,
      Matrix.one_apply, if_pos rfl]
    norm_num

/-- The rotation fixture's positive 2-cycles (`htwo` genuine, the
self-loops). -/
theorem rot2_two_cycle : ∀ v : Fin 2, ∃ z : Fin 2,
    0 < rot2 v z ∧ 0 < rot2 z v := by
  intro v
  rcases fin2_eq v with h | h
  · subst h
    exact ⟨0, by rw [rot2_00]; norm_num, by rw [rot2_00]; norm_num⟩
  · subst h
    exact ⟨1, by rw [rot2_11]; norm_num, by rw [rot2_11]; norm_num⟩

/-- The rotation fixture's odd closed loops (`hodd` genuine, `t = 1`). -/
theorem rot2_odd_loop : ∀ v : Fin 2, ∃ t : ℕ,
    Odd t ∧ 0 < (rot2 ^ t) v v := by
  intro v
  rcases fin2_eq v with h | h
  · subst h
    exact ⟨1, ⟨0, by omega⟩, by rw [pow_one, rot2_00]; norm_num⟩
  · subst h
    exact ⟨1, ⟨0, by omega⟩, by rw [pow_one, rot2_11]; norm_num⟩

theorem neg_pow_two_mul (a : ℝ) (j : ℕ) : (-a)^(2*j) = a^(2*j) := by
  rw [pow_mul, pow_mul, neg_sq]

theorem neg_pow_two_mul_succ (a : ℝ) (j : ℕ) :
    (-a)^(2*j+1) = -a^(2*j+1) := by
  rw [pow_add, pow_one, pow_add, pow_one, neg_pow_two_mul]
  ring

/-- **The `hnn` fence for the supplier**: at the rotation fixture
every hypothesis except entrywise nonnegativity is genuine —
reachable, self-loop 2-cycles, odd loops at `t = 1` — but every power
`M^k = (−8)^q • M^r` (`k = 3q + r`) has a nonpositive entry. -/
theorem sup_hnn_fence_QA : ¬ rot2.IsPrimitive := by
  rintro ⟨k, hk, hpos⟩
  obtain ⟨q, r, hr, hmod⟩ :
      ∃ q r, k = 3 * q + r ∧ r < 3 :=
    ⟨k / 3, k % 3, (Nat.div_add_mod k 3).symm, Nat.mod_lt k (by omega)⟩
  have hsplit : rot2 ^ k = ((-8 : ℝ) ^ q) • (rot2 ^ r) := by
    rw [hr, pow_add, rot2_pow_three_mul, Matrix.smul_mul, one_mul]
  rw [hsplit] at hpos
  rcases r with _ | _ | _ | r'
  · refine absurd (hpos 0 1) ?_
    have hval : (((-8 : ℝ) ^ q) • rot2 ^ 0) 0 1 = 0 := by
      show ((-8 : ℝ) ^ q) * ((rot2 ^ 0) 0 1) = 0
      rw [pow_zero, Matrix.one_apply, if_neg (by decide), mul_zero]
    rw [hval]
    norm_num
  · rcases Nat.even_or_odd q with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine absurd (hpos 0 1) ?_
      have hval : (((-8 : ℝ) ^ q) • rot2 ^ 1) 0 1 = ((-8 : ℝ) ^ q) * (-3) := by
        show ((-8 : ℝ) ^ q) * (rot2 ^ 1) 0 1 = _
        rw [pow_one, rot2_01]
      have hq : (-8 : ℝ) ^ q = ((8 : ℝ) ^ q) := by
        rw [show q = 2 * j by omega, neg_pow_two_mul]
      rw [hval, hq]
      have h8 : (0 : ℝ) < (8 : ℝ) ^ q := by positivity
      nlinarith [h8]
    · refine absurd (hpos 0 0) ?_
      have hval : (((-8 : ℝ) ^ q) • rot2 ^ 1) 0 0 = ((-8 : ℝ) ^ q) * 1 := by
        show ((-8 : ℝ) ^ q) * (rot2 ^ 1) 0 0 = _
        rw [pow_one, rot2_00]
      have hq : (-8 : ℝ) ^ q = -((8 : ℝ) ^ q) := by
        rw [hj, neg_pow_two_mul_succ]
      rw [hval, hq]
      have h8 : (0 : ℝ) < (8 : ℝ) ^ q := by positivity
      nlinarith [h8]
  · rcases Nat.even_or_odd q with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine absurd (hpos 0 0) ?_
      have hval : (((-8 : ℝ) ^ q) • rot2 ^ 2) 0 0 = ((-8 : ℝ) ^ q) * (-2) := by
        show ((-8 : ℝ) ^ q) * (rot2 ^ 2) 0 0 = _
        rw [rot2_sq_00]
      have hq : (-8 : ℝ) ^ q = ((8 : ℝ) ^ q) := by
        rw [show q = 2 * j by omega, neg_pow_two_mul]
      rw [hval, hq]
      have h8 : (0 : ℝ) < (8 : ℝ) ^ q := by positivity
      nlinarith [h8]
    · refine absurd (hpos 1 0) ?_
      have hval : (((-8 : ℝ) ^ q) • rot2 ^ 2) 1 0 = ((-8 : ℝ) ^ q) * 2 := by
        show ((-8 : ℝ) ^ q) * (rot2 ^ 2) 1 0 = _
        rw [rot2_sq_10]
      have hq : (-8 : ℝ) ^ q = -((8 : ℝ) ^ q) := by
        rw [hj, neg_pow_two_mul_succ]
      rw [hval, hq]
      have h8 : (0 : ℝ) < (8 : ℝ) ^ q := by positivity
      nlinarith [h8]
  · exact absurd hmod (by omega)

end EngineFences

/-! ## The walk-level fences (`Mixing.lean`) -/

section WalkFences

/-- Generic extraction: the walk law at time `t` reads off the `x`-th
row of the `t`-th power — `ν_t x j = (P^t) x j`, the general form of
the lazy fences' `transpose_mulVec_single_apply`. -/
theorem walkDistribution_apply_pow {V : Type} [Fintype V] [DecidableEq V]
    (A : WAdj (V := V)) (t : ℕ) (x : V) :
    ∀ j : V, walkDistribution A t x j = (walkTransitionMatrix A ^ t) x j := by
  induction t with
  | zero =>
    intro j
    rw [walkDistribution_zero, pow_zero]
    by_cases h : j = x
    · subst h; simp [Pi.single_apply, Matrix.one_apply]
    · simp [h, Ne.symm h, Pi.single_apply, Matrix.one_apply]
  | succ t ih =>
    intro j
    rw [walkDistribution_succ]
    simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply, ih]
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem dist_ge_entry {n : ℕ} (f g : Fin n → ℝ) (i : Fin n) :
    |f i - g i| ≤ dist f g := by
  rw [dist_eq_norm]
  simpa using norm_le_pi_norm (f - g) i

/-! ### The `K₂` power plumbing -/

theorem k2P_pow_even (q : ℕ) :
    walkTransitionMatrix k2Adj ^ (2 * q) = 1 := by
  rw [pow_mul, k2P_two_eq_one, one_pow]

theorem k2P_pow_odd (q : ℕ) :
    walkTransitionMatrix k2Adj ^ (2 * q + 1) = walkTransitionMatrix k2Adj := by
  rw [pow_add, pow_mul, k2P_two_eq_one, one_pow, one_mul, pow_one]

theorem k2_law_even_entry (q : ℕ) :
    walkDistribution k2Adj (2 * q) 0 0 = 1
      ∧ walkDistribution k2Adj (2 * q) 0 1 = 0 := by
  constructor
  · rw [walkDistribution_apply_pow, k2P_pow_even]
    simp [Matrix.one_apply]
  · rw [walkDistribution_apply_pow, k2P_pow_even]
    simp [Matrix.one_apply]

theorem k2_law_odd_entry (q : ℕ) :
    walkDistribution k2Adj (2 * q + 1) 0 0 = 0
      ∧ walkDistribution k2Adj (2 * q + 1) 0 1 = 1 := by
  constructor
  · rw [walkDistribution_apply_pow, k2P_pow_odd, k2P_apply, k2Adj_apply,
      if_pos rfl]
  · rw [walkDistribution_apply_pow, k2P_pow_odd, k2P_apply, k2Adj_apply,
      if_neg (by decide)]

/-! ### The rate fences -/

/-- **The `hle` fence for the plain-walk Doeblin rate**: at `K₂`,
`δ = 1`, `m = t = 1`, `x = 0` — the certificate hypothesis fails at
the diagonal (`(P^1) 0 0 = 0 < 1`), and the dropped statement reads
`TV = 1/2 ≤ (1 − 2·1)^1 = −1`. -/
theorem k2_rate_hle_fence_QA :
    ¬ (tvDistance (walkDistribution k2Adj 1 0) (stationaryVec k2Adj)
        ≤ (1 - (Fintype.card (Fin 2) : ℝ) * 1) ^ (1 / 1)) := by
  have hlaw := k2_law_odd_entry 0
  rw [show (2 * 0 + 1 : ℕ) = 1 by norm_num] at hlaw
  obtain ⟨e0, e1⟩ := hlaw
  have hTV : tvDistance (walkDistribution k2Adj 1 0) (stationaryVec k2Adj)
      = 1/2 := by
    rw [tvDistance, Fin.sum_univ_two, e0, e1, k2_pi_QA, k2_pi_QA,
      show ((0:ℝ) - 1/2) = -(1/2) from by norm_num,
      show ((1:ℝ) - 1/2) = 1/2 from by norm_num, abs_neg,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num
  intro h
  rw [hTV] at h
  norm_num at h

/-- The isolation companion for the `hle` fence: the certificate
hypothesis genuinely fails at the diagonal. -/
theorem k2_hle_one_not_genuine :
    ¬ (∀ i j : Fin 2, (1:ℝ) ≤ (walkTransitionMatrix k2Adj ^ 1) i j) := by
  intro h
  have h00 := h 0 0
  rw [pow_one, k2P_apply, k2Adj_apply, if_pos rfl] at h00
  norm_num at h00

/-- The asymmetric-loop walk matrix is the doubly-stochastic
`(1/2)·J`. -/
theorem asym_P_apply (i j : Fin 2) :
    walkTransitionMatrix asymLoopAdj i j = 1/2 := by
  rw [walkTransitionMatrix_apply]
  rcases fin2_eq i with h | h <;> rcases fin2_eq j with h' | h'
  · subst h; subst h'
    rw [asymLoopAdj_deg_zero, asymLoopAdj_00]; norm_num
  · subst h; subst h'
    rw [asymLoopAdj_deg_zero, asymLoopAdj_01]; norm_num
  · subst h; subst h'
    rw [asymLoopAdj_deg_one, asymLoopAdj_10]; norm_num
  · subst h; subst h'
    rw [asymLoopAdj_deg_one, asymLoopAdj_11]; norm_num

theorem asym_law_one_entry (j : Fin 2) :
    walkDistribution asymLoopAdj 1 0 j = 1/2 := by
  rw [walkDistribution_apply_pow, pow_one, asym_P_apply]

theorem asym_TV_one :
    tvDistance (walkDistribution asymLoopAdj 1 0) (stationaryVec asymLoopAdj)
      = 1/4 := by
  rw [tvDistance, Fin.sum_univ_two, asym_law_one_entry 0,
    asym_law_one_entry 1, asym_pi_zero, asym_pi_one,
    show ((1:ℝ)/2 - 3/4) = -(1/4) from by norm_num,
    show ((1:ℝ)/2 - 1/4) = 1/4 from by norm_num, abs_neg,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4)]
  norm_num

/-- **The `hA` fence for the plain-walk Doeblin rate**: at the
asymmetric loop fixture with `δ = 1/2`, `m = t = 1`, `x = 0` — every
hypothesis except symmetry is genuine (the certificate holds at
equality on `P = (1/2)·J`), but `π = (3/4, 1/4)` is *not* stationary
at the asymmetric chain: the law is `(1/2, 1/2)` after one step, and
the dropped statement reads `TV = 1/4 ≤ 0^1 = 0`. -/
theorem asym_rate_hA_fence_QA :
    ¬ (tvDistance (walkDistribution asymLoopAdj 1 0) (stationaryVec asymLoopAdj)
        ≤ (1 - (Fintype.card (Fin 2) : ℝ) * (1/2)) ^ (1 / 1)) := by
  intro h
  rw [asym_TV_one] at h
  norm_num at h

theorem asym_hle_genuine :
    ∀ i j : Fin 2, (1/2) ≤ (walkTransitionMatrix asymLoopAdj ^ 1) i j := by
  intro i j
  rw [pow_one, asym_P_apply]

theorem asymLoopAdj_not_symm : ¬ asymLoopAdj.IsSymm := by
  intro h
  have h01 := h.apply 0 1
  rw [asymLoopAdj_01, asymLoopAdj_10] at h01
  norm_num at h01

/-! ### The walk-to-power bridge's `hnn` fence: the negative-diagonal
chord fixture `negWalkAdj`

Symmetric, degrees `(1/2, 2, 2)` positive, the two-edge walk
`0 → 1 → 2` exists in the support graph (both weights positive) — but
the negative diagonal `A 0 0 = −3/2` makes `(P²) 0 2 = −5 < 0`: the
off-walk weight poisons the defining sum of the walk's own power. -/

noncomputable def negWalkAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![-3/2, 1, 1; 1, 0, 1; 1, 1, 0]

theorem negWalkAdj_00 : negWalkAdj 0 0 = -3/2 := by rw [negWalkAdj]; rfl
theorem negWalkAdj_01 : negWalkAdj 0 1 = 1 := by rw [negWalkAdj]; rfl
theorem negWalkAdj_02 : negWalkAdj 0 2 = 1 := by rw [negWalkAdj]; rfl
theorem negWalkAdj_10 : negWalkAdj 1 0 = 1 := by rw [negWalkAdj]; rfl
theorem negWalkAdj_11 : negWalkAdj 1 1 = 0 := by rw [negWalkAdj]; rfl
theorem negWalkAdj_12 : negWalkAdj 1 2 = 1 := by rw [negWalkAdj]; rfl
theorem negWalkAdj_20 : negWalkAdj 2 0 = 1 := by rw [negWalkAdj]; rfl
theorem negWalkAdj_21 : negWalkAdj 2 1 = 1 := by rw [negWalkAdj]; rfl
theorem negWalkAdj_22 : negWalkAdj 2 2 = 0 := by rw [negWalkAdj]; rfl

theorem negWalkAdj_isSymm : negWalkAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases fin3_eq i with hi | hi | hi <;> rcases fin3_eq j with hj | hj | hj
  all_goals subst hi; all_goals subst hj
  all_goals rfl

theorem negWalkAdj_not_nonneg : ¬ (∀ i j : Fin 3, 0 ≤ negWalkAdj i j) := by
  intro h
  have := h 0 0
  rw [negWalkAdj_00] at this
  norm_num at this

theorem negWalkAdj_deg0 : deg negWalkAdj 0 = 1/2 := by
  rw [deg, Fin.sum_univ_three, negWalkAdj_00, negWalkAdj_01, negWalkAdj_02]
  norm_num

theorem negWalkAdj_deg1 : deg negWalkAdj 1 = 2 := by
  rw [deg, Fin.sum_univ_three, negWalkAdj_10, negWalkAdj_11, negWalkAdj_12]
  norm_num

theorem negWalkAdj_deg2 : deg negWalkAdj 2 = 2 := by
  rw [deg, Fin.sum_univ_three, negWalkAdj_20, negWalkAdj_21, negWalkAdj_22]
  norm_num

theorem negWalkAdj_deg_pos : ∀ i : Fin 3, 0 < deg negWalkAdj i := by
  intro i
  rcases fin3_eq i with h | h | h
  · subst h; rw [negWalkAdj_deg0]; norm_num
  · subst h; rw [negWalkAdj_deg1]; norm_num
  · subst h; rw [negWalkAdj_deg2]; norm_num

theorem negWalkAdjP_00 : walkTransitionMatrix negWalkAdj 0 0 = -3 := by
  rw [walkTransitionMatrix_apply, negWalkAdj_deg0, negWalkAdj_00]; norm_num
theorem negWalkAdjP_01 : walkTransitionMatrix negWalkAdj 0 1 = 2 := by
  rw [walkTransitionMatrix_apply, negWalkAdj_deg0, negWalkAdj_01]; norm_num
theorem negWalkAdjP_02 : walkTransitionMatrix negWalkAdj 0 2 = 2 := by
  rw [walkTransitionMatrix_apply, negWalkAdj_deg0, negWalkAdj_02]; norm_num
theorem negWalkAdjP_12 : walkTransitionMatrix negWalkAdj 1 2 = 1/2 := by
  rw [walkTransitionMatrix_apply, negWalkAdj_deg1, negWalkAdj_12]; norm_num
theorem negWalkAdjP_22 : walkTransitionMatrix negWalkAdj 2 2 = 0 := by
  rw [walkTransitionMatrix_apply, negWalkAdj_deg2, negWalkAdj_22]; norm_num

theorem negWalkAdj_adj01 : (supportGraph negWalkAdj negWalkAdj_isSymm).Adj 0 1 :=
  supportGraph_adj.mpr ⟨by decide, by rw [negWalkAdj_01]; norm_num⟩

theorem negWalkAdj_adj12 : (supportGraph negWalkAdj negWalkAdj_isSymm).Adj 1 2 :=
  supportGraph_adj.mpr ⟨by decide, by rw [negWalkAdj_12]; norm_num⟩

/-- The bridge's witness walk `0 → 1 → 2` — both edges positive, so
the walk exists in the support graph. -/
def negWalk02 : (supportGraph negWalkAdj negWalkAdj_isSymm).Walk 0 2 :=
  SimpleGraph.Walk.cons negWalkAdj_adj01
    (SimpleGraph.Walk.cons negWalkAdj_adj12 SimpleGraph.Walk.nil)

theorem negWalk02_length : negWalk02.length = 2 := by
  simp [negWalk02]

/-- **The `hnn` fence for the walk-to-power bridge**: at `negWalkAdj`
(symmetric, positive degrees, the walk `0 → 1 → 2` genuine) the
conclusion fails — `(P²) 0 2 = (−3)(2) + (2)(1/2) + (2)(0) = −5`. -/
theorem negWalk_pow_walk_hnn_fence_QA :
    ¬ (0 < (walkTransitionMatrix negWalkAdj ^ negWalk02.length) 0 2) := by
  rw [negWalk02_length, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    negWalkAdjP_00, negWalkAdjP_01, negWalkAdjP_02, negWalkAdjP_12,
    negWalkAdjP_22]
  norm_num

/-! ### The negative-diagonal triangle `negDiagTri`: the supplier's
and the corollary's `hnn` fences

Symmetric, degrees `(2, 4, 4)` positive, support graph the full
positive triangle with its odd walk — every supplier hypothesis
except entrywise nonnegativity (the negative weight is the diagonal
`A 0 0 = −4`, invisible to the support graph). The walk matrix has
the symmetric-subspace eigenvalue `−11/4`: the action on
`w = (0,1,1)` and the `(1,0)`-entry of every power carry exact
`((−11/4)^{k−1})`-closed forms, so no power is entrywise positive and
the walk law diverges. -/

def negDiagTri : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of !![-4, 3, 3; 3, 0, 1; 3, 1, 0]

theorem negDiagTri_00 : negDiagTri 0 0 = -4 := by rw [negDiagTri]; rfl
theorem negDiagTri_01 : negDiagTri 0 1 = 3 := by rw [negDiagTri]; rfl
theorem negDiagTri_02 : negDiagTri 0 2 = 3 := by rw [negDiagTri]; rfl
theorem negDiagTri_10 : negDiagTri 1 0 = 3 := by rw [negDiagTri]; rfl
theorem negDiagTri_11 : negDiagTri 1 1 = 0 := by rw [negDiagTri]; rfl
theorem negDiagTri_12 : negDiagTri 1 2 = 1 := by rw [negDiagTri]; rfl
theorem negDiagTri_20 : negDiagTri 2 0 = 3 := by rw [negDiagTri]; rfl
theorem negDiagTri_21 : negDiagTri 2 1 = 1 := by rw [negDiagTri]; rfl
theorem negDiagTri_22 : negDiagTri 2 2 = 0 := by rw [negDiagTri]; rfl

theorem negDiagTri_isSymm : negDiagTri.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases fin3_eq i with hi | hi | hi <;> rcases fin3_eq j with hj | hj | hj
  all_goals subst hi; all_goals subst hj
  all_goals rfl

theorem negDiagTri_not_nonneg : ¬ (∀ i j : Fin 3, 0 ≤ negDiagTri i j) := by
  intro h
  have := h 0 0
  rw [negDiagTri_00] at this
  norm_num at this

theorem negDiagTri_deg0 : deg negDiagTri 0 = 2 := by
  rw [deg, Fin.sum_univ_three, negDiagTri_00, negDiagTri_01, negDiagTri_02]
  norm_num

theorem negDiagTri_deg1 : deg negDiagTri 1 = 4 := by
  rw [deg, Fin.sum_univ_three, negDiagTri_10, negDiagTri_11, negDiagTri_12]
  norm_num

theorem negDiagTri_deg2 : deg negDiagTri 2 = 4 := by
  rw [deg, Fin.sum_univ_three, negDiagTri_20, negDiagTri_21, negDiagTri_22]
  norm_num

theorem negDiagTri_deg_pos : ∀ i : Fin 3, 0 < deg negDiagTri i := by
  intro i
  rcases fin3_eq i with h | h | h
  · subst h; rw [negDiagTri_deg0]; norm_num
  · subst h; rw [negDiagTri_deg1]; norm_num
  · subst h; rw [negDiagTri_deg2]; norm_num

theorem negDiagTriP_00 : walkTransitionMatrix negDiagTri 0 0 = -2 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg0, negDiagTri_00]; norm_num
theorem negDiagTriP_01 : walkTransitionMatrix negDiagTri 0 1 = 3/2 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg0, negDiagTri_01]; norm_num
theorem negDiagTriP_02 : walkTransitionMatrix negDiagTri 0 2 = 3/2 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg0, negDiagTri_02]; norm_num
theorem negDiagTriP_10 : walkTransitionMatrix negDiagTri 1 0 = 3/4 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg1, negDiagTri_10]; norm_num
theorem negDiagTriP_11 : walkTransitionMatrix negDiagTri 1 1 = 0 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg1, negDiagTri_11]; norm_num
theorem negDiagTriP_12 : walkTransitionMatrix negDiagTri 1 2 = 1/4 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg1, negDiagTri_12]; norm_num
theorem negDiagTriP_20 : walkTransitionMatrix negDiagTri 2 0 = 3/4 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg2, negDiagTri_20]; norm_num
theorem negDiagTriP_21 : walkTransitionMatrix negDiagTri 2 1 = 1/4 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg2, negDiagTri_21]; norm_num
theorem negDiagTriP_22 : walkTransitionMatrix negDiagTri 2 2 = 0 := by
  rw [walkTransitionMatrix_apply, negDiagTri_deg2, negDiagTri_22]; norm_num

theorem negDiagTri_adj01 : (supportGraph negDiagTri negDiagTri_isSymm).Adj 0 1 :=
  supportGraph_adj.mpr ⟨by decide, by rw [negDiagTri_01]; norm_num⟩

theorem negDiagTri_adj12 : (supportGraph negDiagTri negDiagTri_isSymm).Adj 1 2 :=
  supportGraph_adj.mpr ⟨by decide, by rw [negDiagTri_12]; norm_num⟩

theorem negDiagTri_adj20 : (supportGraph negDiagTri negDiagTri_isSymm).Adj 2 0 :=
  supportGraph_adj.mpr ⟨by decide, by rw [negDiagTri_20]; norm_num⟩

/-- The negative-diagonal triangle's odd closed walk: around
`0 → 1 → 2 → 0`, all three weights positive — the negative diagonal
is invisible to the support graph. -/
def negDiagTriWalk3 : (supportGraph negDiagTri negDiagTri_isSymm).Walk 0 0 :=
  SimpleGraph.Walk.cons negDiagTri_adj01
    (SimpleGraph.Walk.cons negDiagTri_adj12
      (SimpleGraph.Walk.cons negDiagTri_adj20 SimpleGraph.Walk.nil))

theorem negDiagTriWalk3_length : negDiagTriWalk3.length = 3 := by
  simp [negDiagTriWalk3]

theorem negDiagTriWalk3_odd : Odd negDiagTriWalk3.length := ⟨1, by
  rw [negDiagTriWalk3_length]; norm_num⟩

theorem negDiagTri_connected : (supportGraph negDiagTri negDiagTri_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  rcases fin3_eq v with h | h | h
  · subst h; exact ⟨SimpleGraph.Walk.nil⟩
  · subst h; exact ⟨SimpleGraph.Walk.cons negDiagTri_adj01 SimpleGraph.Walk.nil⟩
  · subst h
    exact ⟨SimpleGraph.Walk.cons negDiagTri_adj01
      (SimpleGraph.Walk.cons negDiagTri_adj12 SimpleGraph.Walk.nil)⟩

/-- The swap-symmetric probe vector for the closed forms. -/
noncomputable def wNeg : Fin 3 → ℝ := ![0, 1, 1]

theorem wNeg_0 : wNeg 0 = 0 := rfl
theorem wNeg_1 : wNeg 1 = 1 := rfl
theorem wNeg_2 : wNeg 2 = 1 := rfl

theorem negDiagTri_pow_mulVec_w : ∀ k : ℕ, 1 ≤ k →
    ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) 0
        = (11/5) * ((-11/4:ℝ)^(k-1)) + 4/5
      ∧ ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) 1
        = -(11/20) * ((-11/4:ℝ)^(k-1)) + 4/5
      ∧ ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) 2
        = -(11/20) * ((-11/4:ℝ)^(k-1)) + 4/5 := by
  intro k
  induction k with
  | zero => intro h; exact absurd h (by omega)
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      intro _
      have hbase : (walkTransitionMatrix negDiagTri ^ 1) *ᵥ wNeg
          = ![3, 1/4, 1/4] := by
        funext i
        rcases fin3_eq i with h | h | h
        · subst h
          rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, pow_one,
            negDiagTriP_00, negDiagTriP_01, negDiagTriP_02,
            wNeg_0, wNeg_1, wNeg_2]
          norm_num
        · subst h
          rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, pow_one,
            negDiagTriP_10, negDiagTriP_11, negDiagTriP_12,
            wNeg_0, wNeg_1, wNeg_2]
          norm_num
        · subst h
          rw [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, pow_one,
            negDiagTriP_20, negDiagTriP_21, negDiagTriP_22,
            wNeg_0, wNeg_1, wNeg_2]
          norm_num
      rw [hbase]
      constructor
      · show ((3:ℝ)) = (11/5) * ((-11/4:ℝ)^(0:ℕ)) + 4/5
        rw [pow_zero]; norm_num
      constructor
      · show ((1/4:ℝ)) = -(11/20) * ((-11/4:ℝ)^(0:ℕ)) + 4/5
        rw [pow_zero]; norm_num
      · show ((1/4:ℝ)) = -(11/20) * ((-11/4:ℝ)^(0:ℕ)) + 4/5
        rw [pow_zero]; norm_num
    · intro _
      obtain ⟨i0, i1, i2⟩ := ih (by omega)
      have hstep : (walkTransitionMatrix negDiagTri ^ (k+1)) *ᵥ wNeg
          = (walkTransitionMatrix negDiagTri) *ᵥ
            ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) := by
        rw [pow_succ', ← Matrix.mulVec_mulVec]
      have hkexp : ((-11/4:ℝ)^(k+1-1)) = ((-11/4:ℝ)^((k-1)+1)) := by
        congr 1
        omega
      have hγ : ((-11/4:ℝ)^((k-1)+1)) = ((-11/4:ℝ)^(k-1)) * (-11/4) :=
        pow_succ _ _
      rw [hstep]
      constructor
      · show (∑ x : Fin 3, walkTransitionMatrix negDiagTri 0 x
            * ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) x)
            = (11/5) * ((-11/4:ℝ)^(k+1-1)) + 4/5
        rw [hkexp, hγ, Fin.sum_univ_three, negDiagTriP_00, negDiagTriP_01,
          negDiagTriP_02, i0, i1, i2]
        ring
      constructor
      · show (∑ x : Fin 3, walkTransitionMatrix negDiagTri 1 x
            * ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) x)
            = -(11/20) * ((-11/4:ℝ)^(k+1-1)) + 4/5
        rw [hkexp, hγ, Fin.sum_univ_three, negDiagTriP_10, negDiagTriP_11,
          negDiagTriP_12, i0, i1, i2]
        ring
      · show (∑ x : Fin 3, walkTransitionMatrix negDiagTri 2 x
            * ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) x)
            = -(11/20) * ((-11/4:ℝ)^(k+1-1)) + 4/5
        rw [hkexp, hγ, Fin.sum_univ_three, negDiagTriP_20, negDiagTriP_21,
          negDiagTriP_22, i0, i1, i2]
        ring

/-- Power monotonicity at a base ≥ 1. -/
theorem pow_mono_base_ge_one (a : ℝ) (ha : (1:ℝ) ≤ a) :
    ∀ n m : ℕ, n ≤ m → a ^ n ≤ a ^ m := by
  intro n m h
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst hn
    exact le_refl _
  | succ m ih =>
    by_cases hmn : n ≤ m
    · have h1 := ih hmn
      have ha0 : (0:ℝ) ≤ a ^ m := by positivity
      rw [pow_succ]
      calc a ^ n ≤ a ^ m * 1 := by rw [mul_one]; exact h1
        _ ≤ a ^ m * a := mul_le_mul_of_nonneg_left ha ha0
    · have hn : n = m + 1 := by omega
      subst hn
      exact le_refl _

/-- **The supplier's `hnn` fence**: at `negDiagTri` every hypothesis
except entrywise nonnegativity is genuine (the negative weight is the
diagonal, invisible to the support graph), and no power is entrywise
positive — `P^k` maps the positive vector `w = (0,1,1)` to a vector
with a negative entry at every `k ≥ 1`. -/
theorem negDiagTri_supplier_hnn_fence_QA :
    ¬ (walkTransitionMatrix negDiagTri).IsPrimitive := by
  rintro ⟨k, hk, hpos⟩
  have hside0 : ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) 0
      = (walkTransitionMatrix negDiagTri ^ k) 0 1
        + (walkTransitionMatrix negDiagTri ^ k) 0 2 := by
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      wNeg_0, wNeg_1, wNeg_2]
    ring
  have hside1 : ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) 1
      = (walkTransitionMatrix negDiagTri ^ k) 1 1
        + (walkTransitionMatrix negDiagTri ^ k) 1 2 := by
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
      wNeg_0, wNeg_1, wNeg_2]
    ring
  rcases Nat.even_or_odd k with ⟨q, hq⟩ | ⟨q, hq⟩
  · -- even k ≥ 2: entry 0 of the closed form is negative
    obtain ⟨hp, _, _⟩ := negDiagTri_pow_mulVec_w k hk
    have hexp : k - 1 = 2 * (q - 1) + 1 := by omega
    have hγ : ((-11/4:ℝ)^(k-1)) = -((11/4:ℝ)^(k-1)) := by
      rw [hexp]
      have h := neg_pow_two_mul_succ (11/4) (q - 1)
      have hconv : (-(11/4:ℝ)) = (-11/4:ℝ) := by norm_num
      rw [hconv] at h
      exact h
    rw [hγ] at hp
    have hge : ((11/4:ℝ)^(1:ℕ)) ≤ ((11/4:ℝ)^(k-1)) :=
      pow_mono_base_ge_one (11/4) (by norm_num) 1 (k-1) (by omega)
    have hlt : ((11/5:ℝ)) * -((11/4:ℝ)^(k-1)) + 4/5 < 0 := by
      nlinarith [hge]
    have hgt : (0:ℝ) < ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) 0 := by
      rw [hside0]
      have h1 := hpos 0 1
      have h2 := hpos 0 2
      linarith
    rw [hp] at hgt
    linarith
  · -- odd k: k = 1 directly; k ≥ 3 via entry 1
    rcases q with _ | q'
    · have hk1 : k = 1 := by omega
      subst hk1
      exact absurd (hpos 0 0) (by rw [pow_one, negDiagTriP_00]; norm_num)
    · obtain ⟨_, hp, _⟩ := negDiagTri_pow_mulVec_w k hk
      have hexp : k - 1 = 2 * (q' + 1) := by omega
      have hγ : ((-11/4:ℝ)^(k-1)) = ((11/4:ℝ)^(k-1)) := by
        rw [hexp]
        have h := neg_pow_two_mul (11/4) (q' + 1)
        have hconv : (-(11/4:ℝ)) = (-11/4:ℝ) := by norm_num
        rw [hconv] at h
        exact h
      rw [hγ] at hp
      have hge : ((11/4:ℝ)^(2:ℕ)) ≤ ((11/4:ℝ)^(k-1)) :=
        pow_mono_base_ge_one (11/4) (by norm_num) 2 (k-1) (by omega)
      have hlt : -((11/20:ℝ)) * ((11/4:ℝ)^(k-1)) + 4/5 < 0 := by
        have h2 : ((11/4:ℝ)^(2:ℕ)) = 121/16 := by norm_num
        nlinarith [hge, h2]
      have hgt : (0:ℝ) < ((walkTransitionMatrix negDiagTri ^ k) *ᵥ wNeg) 1 := by
        rw [hside1]
        have h1 := hpos 1 1
        have h2 := hpos 1 2
        linarith
      rw [hp] at hgt
      linarith

/-- **The `(1,0)`-entry of every power** (`k ≥ 1`): the exact
`((−11/4)^{k−1})`-closed form, through the row-sum identity. -/
theorem negDiagTri_row1_col0 : ∀ k : ℕ, 1 ≤ k →
    (walkTransitionMatrix negDiagTri ^ k) 1 0
      = 1/5 + (11/20) * ((-11/4:ℝ)^(k-1)) := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    by_cases hk : k = 0
    · subst hk
      intro _
      rw [pow_one, negDiagTriP_10]
      norm_num
    · intro _
      have ihc := ih (by omega)
      have hrow : ∑ j, (walkTransitionMatrix negDiagTri ^ k) 1 j = 1 :=
        Scaffold.LinearAlgebra.pow_row_sum
          (fun i => walkTransitionMatrix_row_sum negDiagTri negDiagTri_deg_pos i)
          k 1
      rw [Fin.sum_univ_three] at hrow
      have hde : (walkTransitionMatrix negDiagTri ^ k) 1 1
          + (walkTransitionMatrix negDiagTri ^ k) 1 2
          = 1 - (walkTransitionMatrix negDiagTri ^ k) 1 0 := by linarith
      have hkexp : ((-11/4:ℝ)^(k+1-1)) = ((-11/4:ℝ)^((k-1)+1)) := by
        congr 1
        omega
      have hγ : ((-11/4:ℝ)^((k-1)+1)) = ((-11/4:ℝ)^(k-1)) * (-11/4) :=
        pow_succ _ _
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, negDiagTriP_00,
        negDiagTriP_10, negDiagTriP_20, ihc, hkexp, hγ]
      linarith

/-- **The convergence corollary's `hnn` fence**: at `negDiagTri`
started at `x = 1` the law's zeroth coordinate
`ν_t 1 0 = 1/5 + (11/20)(−11/4)^{t−1}` blows up in magnitude with
alternating sign — consecutive even-spaced terms differ by at least
`231/64`, so the sequence has no limit. -/
theorem negDiagTri_tendsto_hnn_fence_QA :
    ¬ Filter.Tendsto (fun t : ℕ => walkDistribution negDiagTri t 1) Filter.atTop
      (nhds (stationaryVec negDiagTri)) := by
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1/4) (by norm_num)
  have d1 := hN N (le_refl N)
  have d2 := hN (N + 2) (by omega)
  have htri := dist_triangle (walkDistribution negDiagTri N 1)
    (stationaryVec negDiagTri) (walkDistribution negDiagTri (N + 2) 1)
  rw [dist_comm (stationaryVec negDiagTri)
    (walkDistribution negDiagTri (N+2) 1)] at htri
  have hlow : (21/16:ℝ) ≤ dist (walkDistribution negDiagTri N 1)
      (walkDistribution negDiagTri (N + 2) 1) := by
    have hentry := dist_ge_entry (walkDistribution negDiagTri N 1)
      (walkDistribution negDiagTri (N + 2) 1) 0
    rcases N with _ | N'
    · have e0 : walkDistribution negDiagTri 0 1 0 = 0 := by
        rw [walkDistribution_zero]
        simp [Pi.single_apply]
      have e2 : walkDistribution negDiagTri 2 1 0
          = 1/5 + (11/20) * ((-11/4:ℝ)^(2-1)) := by
        rw [walkDistribution_apply_pow]
        exact negDiagTri_row1_col0 2 (by omega)
      rw [e0, e2, show ((-11/4:ℝ)^(2-1)) = -11/4 from by rw [pow_one]] at hentry
      rw [show |(0:ℝ) - (1/5 + (11/20) * (-11/4))| = 21/16 from by norm_num] at hentry
      exact hentry
    · have e1 : walkDistribution negDiagTri (N'+1) 1 0
          = 1/5 + (11/20) * ((-11/4:ℝ)^(N')) := by
        rw [walkDistribution_apply_pow]
        exact negDiagTri_row1_col0 (N'+1) (by omega)
      have e2 : walkDistribution negDiagTri (N'+3) 1 0
          = 1/5 + (11/20) * ((-11/4:ℝ)^(N'+2)) := by
        rw [walkDistribution_apply_pow]
        exact negDiagTri_row1_col0 (N'+3) (by omega)
      rw [e1, e2] at hentry
      have hdiff : (1/5 + (11/20) * ((-11/4:ℝ)^(N'+2)))
            - (1/5 + (11/20) * ((-11/4:ℝ)^(N')))
            = (11/20) * ((-11/4:ℝ)^N') * (105/16) := by
        have hγ2 : ((-11/4:ℝ)^(N'+2)) = ((-11/4:ℝ)^(N'+1)) * (-11/4) :=
          pow_succ _ _
        have hγ1 : ((-11/4:ℝ)^(N'+1)) = ((-11/4:ℝ)^(N')) * (-11/4) :=
          pow_succ _ _
        rw [hγ2, hγ1]
        ring
      have hdiff' : (1/5 + (11/20) * ((-11/4:ℝ)^(N')))
            - (1/5 + (11/20) * ((-11/4:ℝ)^(N'+2)))
            = -((11/20) * ((-11/4:ℝ)^N') * (105/16)) := by
        have := hdiff
        linarith
      have habase : |(-11/4:ℝ)| = 11/4 := by norm_num
      rw [hdiff', abs_neg, abs_mul, abs_mul, abs_pow, habase] at hentry
      have habs2 : |(11/20:ℝ)| = 11/20 := by norm_num
      have habs3 : |(105/16:ℝ)| = 105/16 := by norm_num
      rw [habs2, habs3] at hentry
      have h1 : (1:ℝ) ≤ ((11/4:ℝ)^N') :=
        pow_mono_base_ge_one (11/4) (by norm_num) 0 N' (by omega)
      nlinarith [hentry, h1]
  linarith

/-! ### The supplier's `hp` fence and the corollary's `hp` fence at
`K₂` -/

theorem k2Adj_adj01 : (supportGraph k2Adj k2Adj_isSymm).Adj 0 1 :=
  supportGraph_adj.mpr ⟨by decide, by norm_num [k2Adj]⟩

theorem k2Adj_adj10 : (supportGraph k2Adj k2Adj_isSymm).Adj 1 0 :=
  supportGraph_adj.mpr ⟨by decide, by norm_num [k2Adj]⟩

/-- The edge's even closed walk `0 → 1 → 0` — the periodicity
witness: its length is even, so `hp` fails at exactly this walk. -/
def k2WalkEven : (supportGraph k2Adj k2Adj_isSymm).Walk 0 0 :=
  SimpleGraph.Walk.cons k2Adj_adj01
    (SimpleGraph.Walk.cons k2Adj_adj10 SimpleGraph.Walk.nil)

theorem k2WalkEven_length : k2WalkEven.length = 2 := by
  simp [k2WalkEven]

theorem k2WalkEven_not_odd : ¬ Odd k2WalkEven.length := by
  rw [k2WalkEven_length]
  decide

/-- **The `K₂` walk matrix is not primitive** — the shared core of the
supplier's `hodd` and `hp` fences: even powers are the identity (zero
off-diagonal), odd powers have zero diagonal. -/
theorem k2P_not_isPrimitive : ¬ (walkTransitionMatrix k2Adj).IsPrimitive := by
  rintro ⟨k, hk, hpos⟩
  rcases Nat.even_or_odd k with ⟨q, hq⟩ | hq
  · have hoff : (walkTransitionMatrix k2Adj ^ k) 0 1 = 0 := by
      rw [show k = 2 * q by omega, pow_mul, k2P_two_eq_one, one_pow]
      show (if (0 : Fin 2) = 1 then (1:ℝ) else 0) = 0
      rw [if_neg (by decide)]
    exact absurd (hpos 0 1) (by rw [hoff]; norm_num)
  · exact absurd (hpos 0 0)
      (by rw [k2_odd_diag_zero_QA k hq]; norm_num)

/-- **The supplier's `hp` fence**: at `K₂` every hypothesis except the
odd closed walk is genuine — nonnegative, positive degrees, connected,
and the closed walk `0 → 1 → 0` exists — but its length is even, and
the conclusion fails (no power of the edge's walk matrix is
entrywise positive). -/
theorem k2_supplier_hp_fence_QA : ¬ (walkTransitionMatrix k2Adj).IsPrimitive :=
  k2P_not_isPrimitive

/-- **The convergence corollary's `hp` fence**: at `K₂` the law from
`0` alternates `δ₀/δ₁` by the parity of `t` — at distance `1`
forever, so it has no limit. -/
theorem k2_tendsto_hp_fence_QA :
    ¬ Filter.Tendsto (fun t : ℕ => walkDistribution k2Adj t 0) Filter.atTop
      (nhds (stationaryVec k2Adj)) := by
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h (1/4) (by norm_num)
  have d1 := hN N (le_refl N)
  have d2 := hN (N + 1) (by omega)
  have htri := dist_triangle (walkDistribution k2Adj N 0)
    (stationaryVec k2Adj) (walkDistribution k2Adj (N + 1) 0)
  rw [dist_comm (stationaryVec k2Adj) (walkDistribution k2Adj (N+1) 0)] at htri
  have hlow : (1:ℝ) ≤ dist (walkDistribution k2Adj N 0)
      (walkDistribution k2Adj (N + 1) 0) := by
    have hentry := dist_ge_entry (walkDistribution k2Adj N 0)
      (walkDistribution k2Adj (N + 1) 0) 0
    rcases Nat.even_or_odd N with ⟨q, hq⟩ | ⟨q, hq⟩
    · have e1 : walkDistribution k2Adj N 0 0 = 1 := by
        rw [show N = 2 * q by omega, (k2_law_even_entry q).1]
      have e2 : walkDistribution k2Adj (N + 1) 0 0 = 0 := by
        rw [show N + 1 = 2 * q + 1 by omega, (k2_law_odd_entry q).1]
      rw [e1, e2] at hentry
      simpa using hentry
    · have e1 : walkDistribution k2Adj N 0 0 = 0 := by
        rw [show N = 2 * q + 1 by omega, (k2_law_odd_entry q).1]
      have e2 : walkDistribution k2Adj (N + 1) 0 0 = 1 := by
        rw [show N + 1 = 2 * (q + 1) by omega, (k2_law_even_entry (q+1)).1]
      rw [e1, e2] at hentry
      simpa using hentry
  linarith


/-! ### The triangle ⊕ isolated-vertex fixture `triIso4`: the
supplier's and the corollary's `hconn` fences

Symmetric, nonnegative, degrees `(2, 2, 2, 1)` positive, the
triangle's odd walk genuine — but vertex `3` carries only a
self-weight (`A 3 3 = 1`, invisible to the loopless support graph),
so the support graph is disconnected, the cross-block entry
`(P^k) 0 3` is zero at every power, and the walk from `3` is
absorbed at `δ₃ ≠ π`. -/

theorem fin4_eq (v : Fin 4) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  have hv : v.val < 4 := v.isLt
  rcases (show v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 by omega) with
    h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext (show v.val = (1 : Fin 4).val by simpa using h)))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext (show v.val = (2 : Fin 4).val by simpa using h)))
    )
  · exact Or.inr (Or.inr (Or.inr (Fin.ext (show v.val = (3 : Fin 4).val by simpa using h)))
    )

def triIso4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 1, 0; 1, 0, 1, 0; 1, 1, 0, 0; 0, 0, 0, 1]

theorem triIso4_00 : triIso4 0 0 = 0 := by rw [triIso4]; rfl
theorem triIso4_01 : triIso4 0 1 = 1 := by rw [triIso4]; rfl
theorem triIso4_02 : triIso4 0 2 = 1 := by rw [triIso4]; rfl
theorem triIso4_03 : triIso4 0 3 = 0 := by rw [triIso4]; rfl
theorem triIso4_10 : triIso4 1 0 = 1 := by rw [triIso4]; rfl
theorem triIso4_11 : triIso4 1 1 = 0 := by rw [triIso4]; rfl
theorem triIso4_12 : triIso4 1 2 = 1 := by rw [triIso4]; rfl
theorem triIso4_13 : triIso4 1 3 = 0 := by rw [triIso4]; rfl
theorem triIso4_20 : triIso4 2 0 = 1 := by rw [triIso4]; rfl
theorem triIso4_21 : triIso4 2 1 = 1 := by rw [triIso4]; rfl
theorem triIso4_22 : triIso4 2 2 = 0 := by rw [triIso4]; rfl
theorem triIso4_23 : triIso4 2 3 = 0 := by rw [triIso4]; rfl
theorem triIso4_30 : triIso4 3 0 = 0 := by rw [triIso4]; rfl
theorem triIso4_31 : triIso4 3 1 = 0 := by rw [triIso4]; rfl
theorem triIso4_32 : triIso4 3 2 = 0 := by rw [triIso4]; rfl
theorem triIso4_33 : triIso4 3 3 = 1 := by rw [triIso4]; rfl

theorem triIso4_isSymm : triIso4.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases fin4_eq i with hi | hi | hi | hi <;>
    rcases fin4_eq j with hj | hj | hj | hj
  all_goals subst hi; all_goals subst hj
  all_goals rfl

theorem triIso4_nonneg (i j : Fin 4) : 0 ≤ triIso4 i j := by
  rcases fin4_eq i with hi | hi | hi | hi <;>
    rcases fin4_eq j with hj | hj | hj | hj
  all_goals subst hi; all_goals subst hj
  all_goals first | rfl | exact zero_le_one

theorem triIso4_deg0 : deg triIso4 0 = 2 := by
  rw [deg, Fin.sum_univ_four, triIso4_00, triIso4_01, triIso4_02,
    triIso4_03]; norm_num

theorem triIso4_deg1 : deg triIso4 1 = 2 := by
  rw [deg, Fin.sum_univ_four, triIso4_10, triIso4_11, triIso4_12,
    triIso4_13]; norm_num

theorem triIso4_deg2 : deg triIso4 2 = 2 := by
  rw [deg, Fin.sum_univ_four, triIso4_20, triIso4_21, triIso4_22,
    triIso4_23]; norm_num

theorem triIso4_deg3 : deg triIso4 3 = 1 := by
  rw [deg, Fin.sum_univ_four, triIso4_30, triIso4_31, triIso4_32,
    triIso4_33]; norm_num

theorem triIso4_deg_pos : ∀ i : Fin 4, 0 < deg triIso4 i := by
  intro i
  rcases fin4_eq i with h | h | h | h
  · subst h; rw [triIso4_deg0]; norm_num
  · subst h; rw [triIso4_deg1]; norm_num
  · subst h; rw [triIso4_deg2]; norm_num
  · subst h; rw [triIso4_deg3]; norm_num

theorem triIso4_adj01 : (supportGraph triIso4 triIso4_isSymm).Adj 0 1 :=
  supportGraph_adj.mpr ⟨by decide, by rw [triIso4_01]; norm_num⟩

theorem triIso4_adj12 : (supportGraph triIso4 triIso4_isSymm).Adj 1 2 :=
  supportGraph_adj.mpr ⟨by decide, by rw [triIso4_12]; norm_num⟩

theorem triIso4_adj20 : (supportGraph triIso4 triIso4_isSymm).Adj 2 0 :=
  supportGraph_adj.mpr ⟨by decide, by rw [triIso4_20]; norm_num⟩

/-- The triangle block's odd closed walk, genuine on the fixture. -/
def triIso4Walk3 : (supportGraph triIso4 triIso4_isSymm).Walk 0 0 :=
  SimpleGraph.Walk.cons triIso4_adj01
    (SimpleGraph.Walk.cons triIso4_adj12
      (SimpleGraph.Walk.cons triIso4_adj20 SimpleGraph.Walk.nil))

theorem triIso4Walk3_length : triIso4Walk3.length = 3 := by
  simp [triIso4Walk3]

theorem triIso4Walk3_odd : Odd triIso4Walk3.length := ⟨1, by
  rw [triIso4Walk3_length]; norm_num⟩

/-- The support graph's zero row toward the isolated vertex: with
`i.val < 3` there is no positive entry in column `3`. -/
theorem triIso4_off_block_zero : ∀ i j : Fin 4, i.val < 3 → j = 3 →
    triIso4 i j = 0 := by
  intro i j hi hj
  subst hj
  rcases fin4_eq i with h | h | h | h
  · subst h; exact triIso4_03
  · subst h; exact triIso4_13
  · subst h; exact triIso4_23
  · subst h; exact absurd hi (by decide)

/-- Walks from a triangle-block vertex cannot reach the isolated
vertex: adjacency out of the block stays in the block. -/
theorem triIso4_walk_stays : ∀ {i j : Fin 4},
    (supportGraph triIso4 triIso4_isSymm).Walk i j → i.val < 3 → j.val < 3 := by
  intro i j w
  induction w with
  | nil => intro hi; exact hi
  | @cons u k v hadj rest ih =>
    intro hi
    have hk : k.val < 3 := by
      obtain ⟨_, hpos⟩ := supportGraph_adj.1 hadj
      by_contra hcon
      have hk3 : k = 3 := by
        have hv : k.val < 4 := k.isLt
        have h3 : (3 : Fin 4).val = 3 := rfl
        have : 3 ≤ k.val := by omega
        exact Fin.ext (by omega)
      have h0 : triIso4 u k = 0 :=
        triIso4_off_block_zero u k hi hk3
      rw [h0] at hpos
      norm_num at hpos
    exact ih hk

theorem triIso4_not_connected :
    ¬ (supportGraph triIso4 triIso4_isSymm).Connected := by
  intro hconn
  obtain ⟨w⟩ := hconn.1 0 3
  have := triIso4_walk_stays w (by decide)
  exact absurd this (by decide)

/-- The cross-block entry of every power is zero. -/
theorem triIso4_pow_off (k : ℕ) :
    (walkTransitionMatrix triIso4 ^ k) 0 3 = 0 := by
  have hcol : ∀ x : Fin 4, x ≠ 3 → walkTransitionMatrix triIso4 x 3 = 0 := by
    intro x hx
    rw [walkTransitionMatrix_apply, triIso4_off_block_zero x 3 (by
      rcases fin4_eq x with h | h | h | h
      · subst h; omega
      · subst h; omega
      · subst h; omega
      · subst h; exact absurd rfl hx) (by rfl)]
    ring
  induction k with
  | zero =>
    rw [pow_zero]
    show (((1 : Matrix (Fin 4) (Fin 4) ℝ)) 0 3) = 0
    rw [Matrix.one_apply, if_neg (by decide)]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply,
      Finset.sum_eq_single_of_mem (3 : Fin 4) (Finset.mem_univ 3)
        (fun b _ hb => by rw [hcol b hb, mul_zero])]
    rw [ih]
    rw [show walkTransitionMatrix triIso4 3 3 = 1 from by
      rw [walkTransitionMatrix_apply, triIso4_deg3, triIso4_33]
      norm_num]
    ring

/-- **The supplier's `hconn` fence**: at `triIso4` every hypothesis
except connectivity is genuine — symmetric, nonnegative, positive
degrees, the triangle's odd closed walk — and the conclusion fails:
the cross-block entry `(P^k) 0 3` is zero at every power. -/
theorem triIso4_supplier_hconn_fence_QA :
    ¬ (walkTransitionMatrix triIso4).IsPrimitive := by
  rintro ⟨k, hk, hpos⟩
  exact absurd (hpos 0 3) (by rw [triIso4_pow_off]; norm_num)

/-- Row 3 of every power is the absorbed point mass. -/
theorem triIso4_pow_row3 (k : ℕ) : ∀ j : Fin 4,
    (walkTransitionMatrix triIso4 ^ k) 3 j
      = if j = 3 then 1 else 0 := by
  induction k with
  | zero =>
    intro j
    rw [pow_zero]
    show (((1 : Matrix (Fin 4) (Fin 4) ℝ)) 3 j) = if j = 3 then 1 else 0
    by_cases h : j = 3
    · subst h; simp [Matrix.one_apply]
    · have h' : ¬((3 : Fin 4) = j) := fun hh => h hh.symm
      simp [h, h', Matrix.one_apply]
  | succ k ih =>
    intro j
    have hrow : ∀ x : Fin 4, x ≠ 3 →
        (walkTransitionMatrix triIso4 ^ k) 3 x = 0 := by
      intro x hx
      rw [ih x, if_neg hx]
    rw [pow_succ, Matrix.mul_apply,
      Finset.sum_eq_single_of_mem (3 : Fin 4) (Finset.mem_univ 3)
        (fun b _ hb => by rw [hrow b hb, zero_mul]),
      ih 3, if_pos rfl, walkTransitionMatrix_apply, triIso4_deg3, inv_one,
      one_mul]
    rcases fin4_eq j with h | h | h | h
    · subst h; rw [triIso4_30, if_neg (by decide)]; norm_num
    · subst h; rw [triIso4_31, if_neg (by decide)]; norm_num
    · subst h; rw [triIso4_32, if_neg (by decide)]; norm_num
    · subst h; rw [triIso4_33, if_pos rfl]; norm_num

theorem triIso4_vol : vol triIso4 (Finset.univ : Finset (Fin 4)) = 7 := by
  rw [vol, Fin.sum_univ_four, triIso4_deg0, triIso4_deg1, triIso4_deg2,
    triIso4_deg3]
  norm_num

theorem triIso4_pi_three : stationaryVec triIso4 3 = 1/7 := by
  rw [stationaryVec, triIso4_vol, triIso4_deg3]

/-- **The convergence corollary's `hconn` fence**: at `triIso4`
started at `x = 3` the law is constantly `δ₃` (the self-weighted
vertex is absorbing), which converges — to `δ₃ ≠ π`, `π 3 = 1/7`. -/
theorem triIso4_tendsto_hconn_fence_QA :
    ¬ Filter.Tendsto (fun t : ℕ => walkDistribution triIso4 t 3) Filter.atTop
      (nhds (stationaryVec triIso4)) := by
  intro h
  have hconst : (fun t : ℕ => walkDistribution triIso4 t 3)
      = (fun _ : ℕ => (fun j : Fin 4 => if j = 3 then (1:ℝ) else 0)) := by
    funext t j
    rw [walkDistribution_apply_pow]
    exact triIso4_pow_row3 t j
  rw [hconst] at h
  have hlim : Filter.Tendsto
      (fun _ : ℕ => (fun j : Fin 4 => if j = 3 then (1:ℝ) else 0)) Filter.atTop
      (nhds (fun j : Fin 4 => if j = 3 then (1:ℝ) else 0)) :=
    tendsto_const_nhds
  have huniq := tendsto_nhds_unique h hlim
  have he3 := congrArg (fun f : Fin 4 → ℝ => f 3) huniq
  simp only [triIso4_pi_three] at he3
  norm_num at he3

end WalkFences

/-! ### The capstone's consumer fences (the priced follow-ons)

`proposals/adversarial-fences-primitivity-supplier-family.md`'s priced
follow-on section (2026-09-03): the audit closed every supplier, rate,
and convergence clause of the family but deferred exactly the two
graph clauses of the consumer capstone
`empiricalWalkDistribution_tail_selfcontained_of_depth` — both fenced
here, completing the theorem's falsification surface (every hypothesis
now has a negative witness or a recorded non-fenceable mechanism). The
stated `(ε, n)` is `(1/2, 32)`: the priced `(1/4, 32)` needs a strict
`2 < exp 1` that `Real.add_one_le_exp` cannot deliver, and `(1/2, 32)`
closes by the non-strict engine at the same honest deviations. -/

/-- At a point-mass factor (`q v = 1`), the all-`v` coordinate
cylinder carries the full mass `1` — the capstone fence route's
central computation (the measure-of-singleton machinery: one
`toMeasure_cyl_inter` application collapses to a single factor and
`1 ^ n`). -/
theorem toMeasure_cyl_singleton_one {V : Type} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V] {n : ℕ}
    {q : V → ℝ} (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1) (v : V)
    (hqv : q v = 1) :
    (iidPMF (V := V) (ι := Fin n) q hq0 hq1).toMeasure
      (⋂ k ∈ (Finset.univ : Finset (Fin n)),
        (fun ω : Fin n → V => ω k) ⁻¹' ({v} : Set V)) = 1 := by
  rw [toMeasure_cyl_inter _ _ _ Finset.univ (fun _ => ({v} : Set V)),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Finset.sum_eq_single v]
  · rw [if_pos (Set.mem_singleton_iff.mpr rfl), hqv, one_mul,
      ENNReal.ofReal_one, one_pow]
  · intro b _ hb
    rw [if_neg (fun h => hb (Set.mem_singleton_iff.mp h))]
    exact zero_mul _
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The shared numeric: the fences' right side `2 exp(−4)` sits
strictly below `1` by the non-strict engine (`exp 4 ≥ 4 + 1`, so
`exp(−4) ≤ 1/5` and `2 · 1/5 < 1`). -/
theorem two_mul_exp_neg_four_lt_one : 2 * Real.exp (-(4 : ℝ)) < 1 := by
  have hlow : (4 : ℝ) + 1 ≤ Real.exp 4 := Real.add_one_le_exp 4
  have hpos : (0 : ℝ) < 4 + 1 := by norm_num
  have hinv : Real.exp (-(4 : ℝ)) ≤ (4 + 1)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hpos hlow
  have hval : (4 : ℝ) + 1 = 5 := by norm_num
  rw [hval] at hinv hpos
  have hinv' : Real.exp (-(4 : ℝ)) ≤ 1/5 := hinv.trans_eq (one_div (5 : ℝ)).symm
  linarith

/-- **The capstone's `hp` fence**: the self-contained capstone's
odd-closed-walk clause is load-bearing. At `K₂` every other hypothesis
is genuine — including connectivity — but every closed walk has even
length, and the dropped statement's conclusion fails: past *any*
threshold, at the even time `s = 2(t₀ + 1)` the law from `x = 0` is
`δ₀`, the sampling measure concentrates on the all-zero trajectory,
and the deviation event `{|p̂ − 1/2| ≥ 1/2}` carries the full mass `1`
against the bound `2 exp(−4) < 1`. The odd walk is not decoration: it
excludes exactly the bipartite class where the walk never mixes. -/
theorem k2_capstone_hp_fence_QA :
    ¬ (∃ t₀ : ℕ, ∀ s : ℕ, t₀ ≤ s → ∀ x : Fin 2,
        (iidPMF (walkDistribution k2Adj s x)
            (walkDistribution_nonneg k2Adj k2Adj_nonneg k2Adj_deg_pos s x)
            (sum_walkDistribution k2Adj k2Adj_deg_pos s x)).toMeasure
          {ω : Fin 32 → Fin 2 | |(1 / (32 : ℝ)) * ∑ k : Fin 32,
              (if ω k = 0 then (1 : ℝ) else 0)
              - stationaryVec k2Adj 0| ≥ 1/2}
          ≤ ENNReal.ofReal (2 * Real.exp (-(32 : ℝ) * (1/2 : ℝ) ^ 2 / 2))) := by
  intro h
  obtain ⟨t₀, ht₀⟩ := h
  have hs0 : walkDistribution k2Adj (2 * (t₀ + 1)) 0 0 = 1 :=
    (k2_law_even_entry (t₀ + 1)).1
  have hcyl := toMeasure_cyl_singleton_one
    (V := Fin 2) (n := 32)
    (walkDistribution_nonneg k2Adj k2Adj_nonneg k2Adj_deg_pos (2 * (t₀ + 1)) 0)
    (sum_walkDistribution k2Adj k2Adj_deg_pos (2 * (t₀ + 1)) 0) 0 hs0
  have hsub : (⋂ k ∈ (Finset.univ : Finset (Fin 32)),
        (fun ω : Fin 32 → Fin 2 => ω k) ⁻¹' ({0} : Set (Fin 2)))
      ⊆ {ω : Fin 32 → Fin 2 | |(1 / (32 : ℝ)) * ∑ k : Fin 32,
          (if ω k = 0 then (1 : ℝ) else 0)
          - stationaryVec k2Adj 0| ≥ 1/2} := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp only [Set.mem_setOf_eq]
    have hsum : ∑ k : Fin 32, (if ω k = 0 then (1 : ℝ) else 0) = 32 := by
      simp [hω]
    rw [hsum, k2_pi_QA 0]
    have e : (1 / (32 : ℝ)) * 32 - 1/2 = 1/2 := by norm_num
    rw [e, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/2)]
  have hone : (1 : ℝ≥0∞) ≤ (iidPMF (walkDistribution k2Adj (2 * (t₀ + 1)) 0)
      (walkDistribution_nonneg k2Adj k2Adj_nonneg k2Adj_deg_pos
        (2 * (t₀ + 1)) 0)
      (sum_walkDistribution k2Adj k2Adj_deg_pos (2 * (t₀ + 1)) 0)).toMeasure
      {ω : Fin 32 → Fin 2 | |(1 / (32 : ℝ)) * ∑ k : Fin 32,
          (if ω k = 0 then (1 : ℝ) else 0)
          - stationaryVec k2Adj 0| ≥ 1/2} :=
    le_trans (le_of_eq hcyl.symm) (measure_mono hsub)
  have hcontra := ht₀ (2 * (t₀ + 1)) (by omega) 0
  have he : -(32 : ℝ) * (1/2 : ℝ) ^ 2 / 2 = -4 := by norm_num
  rw [he] at hcontra
  have hnum : 2 * Real.exp (-(4 : ℝ)) < 1 := two_mul_exp_neg_four_lt_one
  have hlt : ENNReal.ofReal (2 * Real.exp (-(4 : ℝ))) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact hnum
  exact lt_irrefl 1 (lt_of_le_of_lt hone (lt_of_le_of_lt hcontra hlt))

/-- The isolation companion for the capstone's `hp` fence: at `K₂`
with the genuine even closed walk, every other hypothesis of the
capstone is genuine — symmetry, nonnegativity, positive degrees,
**connectivity**, `0 < ε`, `n ≠ 0` — and only `hp` fails (the
exhibited closed walk has even length). Connectivity is what makes
the failure attributable to `hp` alone. -/
theorem k2_capstone_hp_isolation_QA :
    k2Adj.IsSymm ∧ (∀ i j : Fin 2, 0 ≤ k2Adj i j)
      ∧ (∀ i : Fin 2, 0 < deg k2Adj i)
      ∧ (supportGraph k2Adj k2Adj_isSymm).Connected
      ∧ ¬ Odd k2WalkEven.length
      ∧ 0 < (1/2 : ℝ) ∧ (32 : ℕ) ≠ 0 :=
  ⟨k2Adj_isSymm, k2Adj_nonneg, k2Adj_deg_pos, k2_connected,
    k2WalkEven_not_odd, by norm_num, by norm_num⟩

/-- **The capstone's `hconn` fence**: the connectivity clause is
load-bearing, and differently from `hp` — at `triIso4` (triangle ⊕ a
self-weighted isolated vertex) a genuine odd closed walk exists and
every walk-level hypothesis is genuine, but vertex `3` is absorbing:
the law from `x = 3` is `δ₃` at *every* time, the sampling measure
concentrates on the all-`3` trajectory, and the deviation
`|1 − 1/7| = 6/7 ≥ 1/2` carries the full mass `1` against
`2 exp(−4) < 1` — at every threshold time, not just even ones. -/
theorem triIso4_capstone_hconn_fence_QA :
    ¬ (∃ t₀ : ℕ, ∀ s : ℕ, t₀ ≤ s → ∀ x : Fin 4,
        (iidPMF (walkDistribution triIso4 s x)
            (walkDistribution_nonneg triIso4 triIso4_nonneg triIso4_deg_pos s x)
            (sum_walkDistribution triIso4 triIso4_deg_pos s x)).toMeasure
          {ω : Fin 32 → Fin 4 | |(1 / (32 : ℝ)) * ∑ k : Fin 32,
              (if ω k = 3 then (1 : ℝ) else 0)
              - stationaryVec triIso4 3| ≥ 1/2}
          ≤ ENNReal.ofReal (2 * Real.exp (-(32 : ℝ) * (1/2 : ℝ) ^ 2 / 2))) := by
  intro h
  obtain ⟨t₀, ht₀⟩ := h
  have hs3 : walkDistribution triIso4 t₀ 3 3 = 1 := by
    rw [walkDistribution_apply_pow, triIso4_pow_row3 t₀ 3, if_pos rfl]
  have hcyl := toMeasure_cyl_singleton_one
    (V := Fin 4) (n := 32)
    (walkDistribution_nonneg triIso4 triIso4_nonneg triIso4_deg_pos t₀ 3)
    (sum_walkDistribution triIso4 triIso4_deg_pos t₀ 3) 3 hs3
  have hsub : (⋂ k ∈ (Finset.univ : Finset (Fin 32)),
        (fun ω : Fin 32 → Fin 4 => ω k) ⁻¹' ({3} : Set (Fin 4)))
      ⊆ {ω : Fin 32 → Fin 4 | |(1 / (32 : ℝ)) * ∑ k : Fin 32,
          (if ω k = 3 then (1 : ℝ) else 0)
          - stationaryVec triIso4 3| ≥ 1/2} := by
    intro ω hω
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp only [Set.mem_setOf_eq]
    have hsum : ∑ k : Fin 32, (if ω k = 3 then (1 : ℝ) else 0) = 32 := by
      simp [hω]
    rw [hsum, triIso4_pi_three]
    have e : (1 / (32 : ℝ)) * 32 - 1/7 = 6/7 := by norm_num
    rw [e, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6/7)]
    norm_num
  have hone : (1 : ℝ≥0∞) ≤ (iidPMF (walkDistribution triIso4 t₀ 3)
      (walkDistribution_nonneg triIso4 triIso4_nonneg triIso4_deg_pos t₀ 3)
      (sum_walkDistribution triIso4 triIso4_deg_pos t₀ 3)).toMeasure
      {ω : Fin 32 → Fin 4 | |(1 / (32 : ℝ)) * ∑ k : Fin 32,
          (if ω k = 3 then (1 : ℝ) else 0)
          - stationaryVec triIso4 3| ≥ 1/2} :=
    le_trans (le_of_eq hcyl.symm) (measure_mono hsub)
  have hcontra := ht₀ t₀ (le_refl t₀) 3
  have he : -(32 : ℝ) * (1/2 : ℝ) ^ 2 / 2 = -4 := by norm_num
  rw [he] at hcontra
  have hnum : 2 * Real.exp (-(4 : ℝ)) < 1 := two_mul_exp_neg_four_lt_one
  have hlt : ENNReal.ofReal (2 * Real.exp (-(4 : ℝ))) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    exact hnum
  exact lt_irrefl 1 (lt_of_le_of_lt hone (lt_of_le_of_lt hcontra hlt))

/-- The isolation companion for the capstone's `hconn` fence: at
`triIso4` every other hypothesis of the capstone is genuine —
symmetry, nonnegativity, positive degrees, **the odd closed walk
itself** (`triIso4Walk3` of length `3`), `0 < ε`, `n ≠ 0` — and only
`hconn` fails (the support graph is triangle ⊕ isolated vertex). The
genuine odd walk is what makes the failure attributable to `hconn`
alone: this is not the bipartite class. -/
theorem triIso4_capstone_hconn_isolation_QA :
    triIso4.IsSymm ∧ (∀ i j : Fin 4, 0 ≤ triIso4 i j)
      ∧ (∀ i : Fin 4, 0 < deg triIso4 i)
      ∧ ¬ (supportGraph triIso4 triIso4_isSymm).Connected
      ∧ Odd triIso4Walk3.length
      ∧ 0 < (1/2 : ℝ) ∧ (32 : ℕ) ≠ 0 :=
  ⟨triIso4_isSymm, triIso4_nonneg, triIso4_deg_pos, triIso4_not_connected,
    triIso4Walk3_odd, by norm_num, by norm_num⟩

end PrimitivityFences

end Scaffold.Derived.EmpiricalStationary.QA
