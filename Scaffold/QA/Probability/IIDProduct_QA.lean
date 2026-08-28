/-
  IIDProduct_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Probability.IIDProduct`: the
  V-valued i.i.d. product sampling space (the
  empirical-stationary-distribution program's Step-0 survey verdict,
  delivered with the module).

  The pins run on the fixture `V = Fin 2` at `q = ![2/3, 1/3]` with
  the four-atom enumeration of `Fin 2 → Fin 2` as the independent raw
  route against the module's ∑-∏ machinery; the mean/independence
  clause shapes `hoeffding_empirical` demands are pinned numerically,
  and the `Fin 2` non-normalized vector carries the mass-hypothesis
  fence.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove any axiom (this module admits none); it checks that the
  sampling-space interfaces return the classical numbers.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Probability.IIDProduct

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Scaffold.Mathlib.Probability.IIDProduct.QA

open Scaffold.Mathlib.Probability.IIDProduct

/-!
## The `Fin 2` fixture and its raw-route machinery
-/

/-- The QA fixture factor distribution: `q = ![2/3, 1/3]`. -/
noncomputable def q23 : Fin 2 → ℝ := ![2/3, 1/3]

theorem q23_nonneg : ∀ v, 0 ≤ q23 v := by
  intro v; fin_cases v <;> norm_num [q23]

theorem q23_sum : ∑ v, q23 v = 1 := by
  simp only [q23, Fin.sum_univ_two]
  norm_num

theorem q23_zero : q23 0 = 2/3 := by norm_num [q23]

theorem q23_one : q23 1 = 1/3 := by norm_num [q23]

/-- The four-atom enumeration of the sampling space. -/
theorem univ_fin2_fin2 :
    (Finset.univ : Finset (Fin 2 → Fin 2))
      = {![0, 0], ![0, 1], ![1, 0], ![1, 1]} := by
  ext ω
  have key : ∀ i : Fin 2, ω i = 0 ∨ ω i = 1 := by
    intro i
    rcases (by omega : (ω i).val = 0 ∨ (ω i).val = 1) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton]
  refine iff_of_true trivial ?_
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1
  · exact Or.inl (by funext i; fin_cases i <;> simp [h0, h1])
  · exact Or.inr (Or.inl (by funext i; fin_cases i <;> simp [h0, h1]))
  · exact Or.inr (Or.inr (Or.inl (by funext i; fin_cases i <;> simp [h0, h1])))
  · exact Or.inr (Or.inr (Or.inr (by funext i; fin_cases i <;> simp [h0, h1])))

/-- The six pairwise atom disequalities, shared by the raw-route
enumerations below. -/
private theorem ne_00_01 : (![0, 0] : Fin 2 → Fin 2) ≠ ![0, 1] := fun he =>
  absurd (congrFun he 1) (by decide)

private theorem ne_00_10 : (![0, 0] : Fin 2 → Fin 2) ≠ ![1, 0] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem ne_00_11 : (![0, 0] : Fin 2 → Fin 2) ≠ ![1, 1] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem ne_01_10 : (![0, 1] : Fin 2 → Fin 2) ≠ ![1, 0] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem ne_01_11 : (![0, 1] : Fin 2 → Fin 2) ≠ ![1, 1] := fun he =>
  absurd (congrFun he 0) (by decide)

private theorem ne_10_11 : (![1, 0] : Fin 2 → Fin 2) ≠ ![1, 1] := fun he =>
  absurd (congrFun he 1) (by decide)

/-!
## The product structure pinned by two routes
-/

/-- The first joint-mass value of the fixture, computed raw from the
coordinate masses: atom `(0,0)` carries `q 0 · q 0 = 4/9`. -/
theorem mass_00_QA :
    iidMass q23 ![0, 0] = ENNReal.ofReal ((4 : ℝ) / 9) := by
  have h : iidMass q23 ![0, 0]
      = ENNReal.ofReal (q23 0) * ENNReal.ofReal (q23 0) := by
    simp [iidMass, Fin.prod_univ_two]
  rw [h, ← ENNReal.ofReal_mul (q23_nonneg 0), q23_zero]
  congr 1; norm_num

/-- Atom `(0,1)`: `q 0 · q 1 = 2/9`. -/
theorem mass_01_QA :
    iidMass q23 ![0, 1] = ENNReal.ofReal ((2 : ℝ) / 9) := by
  have h : iidMass q23 ![0, 1]
      = ENNReal.ofReal (q23 0) * ENNReal.ofReal (q23 1) := by
    simp [iidMass, Fin.prod_univ_two]
  rw [h, ← ENNReal.ofReal_mul (q23_nonneg 0), q23_zero, q23_one]
  congr 1; norm_num

/-- Atom `(1,0)`: `2/9`. -/
theorem mass_10_QA :
    iidMass q23 ![1, 0] = ENNReal.ofReal ((2 : ℝ) / 9) := by
  have h : iidMass q23 ![1, 0]
      = ENNReal.ofReal (q23 1) * ENNReal.ofReal (q23 0) := by
    simp [iidMass, Fin.prod_univ_two]
  rw [h, ← ENNReal.ofReal_mul (q23_nonneg 1), q23_zero, q23_one]
  congr 1; norm_num

/-- Atom `(1,1)`: `1/9`. -/
theorem mass_11_QA :
    iidMass q23 ![1, 1] = ENNReal.ofReal ((1 : ℝ) / 9) := by
  have h : iidMass q23 ![1, 1]
      = ENNReal.ofReal (q23 1) * ENNReal.ofReal (q23 1) := by
    simp [iidMass, Fin.prod_univ_two]
  rw [h, ← ENNReal.ofReal_mul (q23_nonneg 1), q23_one]
  congr 1; norm_num

/-- Theorem route: the joint masses sum to one through the ∑-∏
machinery. -/
theorem sum_iidMass_thm_QA :
    ∑ ω : Fin 2 → Fin 2, iidMass q23 ω = 1 :=
  sum_iidMass_eq_one q23_nonneg q23_sum

/-- Raw route: the same total by direct four-atom enumeration — no
∑-∏ swap anywhere, so a wrong product structure or atom mass breaks
exactly one route. -/
theorem sum_iidMass_raw_QA :
    ∑ ω : Fin 2 → Fin 2, iidMass q23 ω = 1 := by
  rw [univ_fin2_fin2,
    Finset.sum_insert (by simp [ne_00_01, ne_00_10, ne_00_11]),
    Finset.sum_insert (by simp [ne_01_10, ne_01_11]),
    Finset.sum_insert (by simp [ne_10_11]), Finset.sum_singleton,
    mass_00_QA, mass_01_QA, mass_10_QA, mass_11_QA]
  have m1 : ENNReal.ofReal ((4 : ℝ) / 9) + ENNReal.ofReal ((2 : ℝ) / 9)
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; congr 1; norm_num
  have m2 : ENNReal.ofReal ((2 : ℝ) / 3) + ENNReal.ofReal ((2 : ℝ) / 9)
      = ENNReal.ofReal ((8 : ℝ) / 9) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; congr 1; norm_num
  have m3 : ENNReal.ofReal ((8 : ℝ) / 9) + ENNReal.ofReal ((1 : ℝ) / 9)
      = ENNReal.ofReal (1 : ℝ) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; congr 1; norm_num
  rw [← add_assoc, ← add_assoc, m1, m2, m3,
    ENNReal.ofReal_one]

/-!
## The clause shapes `hoeffding_empirical` demands, pinned
-/

/-- Raw route: the one-coordinate indicator marginal — the indicator
of `{ω | ω 0 = 0}` summed against the joint mass gives `q 0 = 2/3`,
by enumeration. -/
theorem indicator_marginal_raw_QA :
    ∑ ω : Fin 2 → Fin 2, (if ω 0 = 0 then (1 : ℝ≥0∞) else 0) * iidMass q23 ω
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
  have i00 : (if (![0, 0] : Fin 2 → Fin 2) 0 = 0 then (1 : ℝ≥0∞) else 0) = 1 := by
    simp
  have i01 : (if (![0, 1] : Fin 2 → Fin 2) 0 = 0 then (1 : ℝ≥0∞) else 0) = 1 := by
    simp
  have i10 : (if (![1, 0] : Fin 2 → Fin 2) 0 = 0 then (1 : ℝ≥0∞) else 0) = 0 := by
    simp
  have i11 : (if (![1, 1] : Fin 2 → Fin 2) 0 = 0 then (1 : ℝ≥0∞) else 0) = 0 := by
    simp
  rw [univ_fin2_fin2,
    Finset.sum_insert (by simp [ne_00_01, ne_00_10, ne_00_11]),
    Finset.sum_insert (by simp [ne_01_10, ne_01_11]),
    Finset.sum_insert (by simp [ne_10_11]), Finset.sum_singleton,
    mass_00_QA, mass_01_QA, mass_10_QA, mass_11_QA,
    i00, i01, i10, i11]
  simp only [one_mul, zero_mul, add_zero, zero_add, add_assoc]
  have m1 : ENNReal.ofReal ((4 : ℝ) / 9) + ENNReal.ofReal ((2 : ℝ) / 9)
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; congr 1; norm_num
  rw [m1]

/-- The centering integral pinned: `∫ 1_{ω 0 = 0} ∂μ = q 0 = 2/3` —
the exact mean-clause constant `hoeffding_empirical`'s internal
centering collapses to, at this sampling space, joined to the raw
marginal above (the two agree at one number through no shared
mechanism). -/
theorem integral_indicator_QA :
    ∫ ω : Fin 2 → Fin 2, (if ω 0 = 0 then (1 : ℝ) else 0)
        ∂(iidPMF q23 q23_nonneg q23_sum).toMeasure
      = 2/3 := by
  rw [integral_indicator q23 q23_nonneg q23_sum 0 0, q23_zero]

/-- The cylinder measure pinned: `μ {ω | ω 0 = 0} = q 0 = 2/3`,
through `toMeasure_cyl` at the singleton set. -/
theorem cylinder_QA :
    (iidPMF q23 q23_nonneg q23_sum).toMeasure
        ((fun ω : Fin 2 → Fin 2 => ω 0) ⁻¹' {0})
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
  rw [toMeasure_cyl q23 q23_nonneg q23_sum 0 {0}]
  rw [Finset.sum_eq_single (0 : Fin 2)]
  · rw [q23_zero]; norm_num
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ 0) h

/-- Independence pinned numerically: the intersection of the two
coordinate cylinders at `{0}` splits as the product of the marginals,
`μ(cyl₀ ∩ cyl₁) = q 0 · q 0 = 4/9` — through `indepFun_coord`
instantiated at the two singleton cylinders, joined to the raw
atom-mass pin `mass_00_QA` (the atom `(0,0)` carries `4/9`, the same
number by two routes through no shared mechanism). -/
theorem independence_split_QA :
    (iidPMF q23 q23_nonneg q23_sum).toMeasure
        ((fun ω : Fin 2 → Fin 2 => ω 0) ⁻¹' {0}
          ∩ (fun ω : Fin 2 → Fin 2 => ω 1) ⁻¹' {0})
      = ENNReal.ofReal ((4 : ℝ) / 9) := by
  have hind : IndepFun (fun ω : Fin 2 → Fin 2 => ω 0)
      (fun ω : Fin 2 → Fin 2 => ω 1)
      (iidPMF q23 q23_nonneg q23_sum).toMeasure :=
    indepFun_coord q23 q23_nonneg q23_sum (by decide)
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind
  have h01 : MeasurableSet ({0} : Set (Fin 2)) := by simp
  have hsplit := hind {0} {0} h01 h01
  have hcyl1 : (iidPMF q23 q23_nonneg q23_sum).toMeasure
      ((fun ω : Fin 2 → Fin 2 => ω 1) ⁻¹' {0})
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
    rw [toMeasure_cyl q23 q23_nonneg q23_sum 1 {0},
      Finset.sum_eq_single (0 : Fin 2)]
    · rw [q23_zero]; norm_num
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ 0) h
  rw [hsplit, cylinder_QA, hcyl1, ← ENNReal.ofReal_mul (by norm_num)]
  congr 1; norm_num

/-!
## The mass-hypothesis fence
-/

/-- The normalization hypothesis is load-bearing: at the
non-normalized vector `q = ![2, 0]` (coordinate masses summing to
`2 ≠ 1`) the joint masses sum to `4`, so `sum_iidMass_eq_one`'s
conclusion fails at exactly this vector and `iidPMF`'s hypothesis
cannot be discharged. -/
theorem junk_normalization_fence_QA :
    ∑ ω : Fin 2 → Fin 2, iidMass ![2, 0] ω = 4 := by
  have h00 : iidMass ![2, 0] ![0, 0] = 4 := by
    have h : iidMass ![2, 0] ![0, 0]
        = ENNReal.ofReal 2 * ENNReal.ofReal 2 := by
      simp [iidMass, Fin.prod_univ_two]
    rw [h, ← ENNReal.ofReal_mul (by norm_num),
      show ((2 : ℝ) * 2) = 4 from by norm_num]
    norm_num
  have h01 : iidMass ![2, 0] ![0, 1] = 0 := by
    have h : iidMass ![2, 0] ![0, 1]
        = ENNReal.ofReal 2 * ENNReal.ofReal 0 := by
      simp [iidMass, Fin.prod_univ_two]
    rw [h]
    simp
  have h10 : iidMass ![2, 0] ![1, 0] = 0 := by
    have h : iidMass ![2, 0] ![1, 0]
        = ENNReal.ofReal 0 * ENNReal.ofReal 2 := by
      simp [iidMass, Fin.prod_univ_two]
    rw [h]
    simp
  have h11 : iidMass ![2, 0] ![1, 1] = 0 := by
    have h : iidMass ![2, 0] ![1, 1]
        = ENNReal.ofReal 0 * ENNReal.ofReal 0 := by
      simp [iidMass, Fin.prod_univ_two]
    rw [h]
    simp
  rw [univ_fin2_fin2,
    Finset.sum_insert (by simp [ne_00_01, ne_00_10, ne_00_11]),
    Finset.sum_insert (by simp [ne_01_10, ne_01_11]),
    Finset.sum_insert (by simp [ne_10_11]), Finset.sum_singleton,
    h00, h01, h10, h11]
  norm_num

end Scaffold.Mathlib.Probability.IIDProduct.QA
