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

  Since 2026-09-05 the `AdversarialFences` section carries the shelf's
  hypothesis-necessity pass
  (`proposals/adversarial-fences-iid-product-family.md`): a fence for
  every priceable named clause of the seventeen theorems — the
  `hq0`/`hq1` bounds clauses of the three ∑-theorems at clamp
  fixtures, `sum_coord2_mul`'s pair at the three-coordinate breaker,
  the three signature-free `hee` clauses and `iIndepFun_coord_apply`'s
  `he` at the all-genuine `q23`, the hF-free strengthening twin, and
  the reconciliation of this file's free-form
  `junk_normalization_fence_QA` as `sum_iidMass_eq_one`'s `hq1` fence
  engine. QA-only, zero axiom contact.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove any axiom (this module admits none); it checks that the
  sampling-space interfaces return the classical numbers.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Probability.IIDProduct
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Scaffold.Mathlib.Probability.IIDProduct.QA

open Scaffold.Mathlib.Probability.IIDProduct
open Scaffold.Mathlib.Probability.Concentration.Scalar

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

section AdversarialFences

/-!
## The hypothesis-necessity pass

Each fence below assumes the theorem's conclusion with exactly one
named hypothesis dropped, at a fixture keeping every kept clause
genuine, and derives `False` — the per-clause discipline of
`governance/ADVERSARIAL_REVIEW.md`
(`proposals/adversarial-fences-iid-product-family.md`). Everything
here is a theorem-instantiation audit of an all-proved shelf: no
axiom is consumed, no `-- @refutes` tag applies.
-/

/-- The out-of-lower-bound factor fixture `q = ![-1, 2]`: breaks `hq0`
only — the `ENNReal.ofReal` clamp zeroes the negative coordinate's
mass — while the kept `hq1` stays genuine at `-1 + 2 = 1`. -/
noncomputable def iidNeg : Fin 2 → ℝ := ![-1, 2]

/-- The out-of-upper-bound factor fixture `q = ![2, 0]`: breaks `hq1`
only (the coordinate masses sum to `2 ≠ 1`) while the kept `hq0` stays
genuine. This is the factor-distribution shape of the file's delivered
free-form fence. -/
noncomputable def iidTwo : Fin 2 → ℝ := ![2, 0]

/-- Kept-clause pin: `hq1` is genuine at `iidNeg`. -/
theorem iidNeg_sum : ∑ v, iidNeg v = 1 := by
  simp only [Fin.sum_univ_two, iidNeg]
  norm_num

/-- Kept-clause pin: `hq0` is genuine at `iidTwo`. -/
theorem iidTwo_nonneg : ∀ v, 0 ≤ iidTwo v := by
  intro v; fin_cases v <;> norm_num [iidTwo]

theorem iidNeg_ofReal_sum :
    ∑ v, ENNReal.ofReal (iidNeg v) = ENNReal.ofReal ((2 : ℝ)) := by
  have h0 : iidNeg 0 = -1 := by norm_num [iidNeg]
  have h1 : iidNeg 1 = 2 := by norm_num [iidNeg]
  rw [Fin.sum_univ_two, h0, h1,
    show ENNReal.ofReal ((-1 : ℝ)) = 0 from ENNReal.ofReal_eq_zero.2 (by norm_num),
    zero_add]

theorem iidTwo_ofReal_sum :
    ∑ v, ENNReal.ofReal (iidTwo v) = ENNReal.ofReal ((2 : ℝ)) := by
  simp only [Fin.sum_univ_two, iidTwo]
  norm_num

/-- The joint-mass total at `iidTwo`, by the delivered free-form
fence's computation (the shapes are definitionally equal). -/
theorem iidTwo_mass_sum : ∑ ω : Fin 2 → Fin 2, iidMass iidTwo ω = 4 :=
  junk_normalization_fence_QA

theorem iidNeg_mass_sum : ∑ ω : Fin 2 → Fin 2, iidMass iidNeg ω = 4 := by
  have hclamp : ENNReal.ofReal ((-1 : ℝ)) = 0 := ENNReal.ofReal_eq_zero.2 (by norm_num)
  have h00 : iidMass iidNeg ![0, 0] = 0 := by
    have h : iidMass iidNeg ![0, 0]
        = ENNReal.ofReal ((-1 : ℝ)) * ENNReal.ofReal ((-1 : ℝ)) := by
      simp [iidMass, Fin.prod_univ_two, iidNeg]
    rw [h, hclamp, zero_mul]
  have h01 : iidMass iidNeg ![0, 1] = 0 := by
    have h : iidMass iidNeg ![0, 1]
        = ENNReal.ofReal ((-1 : ℝ)) * ENNReal.ofReal ((2 : ℝ)) := by
      simp [iidMass, Fin.prod_univ_two, iidNeg]
    rw [h, hclamp, zero_mul]
  have h10 : iidMass iidNeg ![1, 0] = 0 := by
    have h : iidMass iidNeg ![1, 0]
        = ENNReal.ofReal ((2 : ℝ)) * ENNReal.ofReal ((-1 : ℝ)) := by
      simp [iidMass, Fin.prod_univ_two, iidNeg]
    rw [h, hclamp, mul_zero]
  have h11 : iidMass iidNeg ![1, 1] = 4 := by
    have h : iidMass iidNeg ![1, 1]
        = ENNReal.ofReal ((2 : ℝ)) * ENNReal.ofReal ((2 : ℝ)) := by
      simp [iidMass, Fin.prod_univ_two, iidNeg]
    rw [h, ← ENNReal.ofReal_mul (by norm_num),
      show ((2 : ℝ) * 2) = 4 from by norm_num]
    norm_num
  rw [univ_fin2_fin2,
    Finset.sum_insert (by simp [ne_00_01, ne_00_10, ne_00_11]),
    Finset.sum_insert (by simp [ne_01_10, ne_01_11]),
    Finset.sum_insert (by simp [ne_10_11]), Finset.sum_singleton,
    h00, h01, h10, h11]
  norm_num

private theorem iidF_ofReal_ne_ofReal {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hne : a ≠ b)
    (h : ENNReal.ofReal a = ENNReal.ofReal b) : False := by
  apply_fun ENNReal.toReal at h
  rw [ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb] at h
  exact hne h

/-- **Fence: `sum_mass_eq_one`'s `hq0 : ∀ v, 0 ≤ q v`.** At `q = ![-1, 2]`
(kept `hq1` genuine: `-1 + 2 = 1`) the `ofReal` clamp zeroes the
negative coordinate's mass, so the coordinate mass sum is
`0 + 2 = 2 ≠ 1`. -/
theorem iidFence_sum_mass_nonneg
    (h : ∑ v, ENNReal.ofReal (iidNeg v) = 1) : False := by
  rw [iidNeg_ofReal_sum, ← ENNReal.ofReal_one] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_mass_eq_one`'s `hq1 : ∑ v, q v = 1`.** At `q = ![2, 0]`
(kept `hq0` genuine) the coordinate mass sum is `2 + 0 = 2 ≠ 1`. -/
theorem iidFence_sum_mass_sum
    (h : ∑ v, ENNReal.ofReal (iidTwo v) = 1) : False := by
  rw [iidTwo_ofReal_sum, ← ENNReal.ofReal_one] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_iidMass_eq_one`'s `hq0`.** At `q = ![-1, 2]` (kept
`hq1` genuine) the clamped joint masses sum to `4 ≠ 1`: the `(1,1)`
atom carries `2 · 2 = 4` and every atom touching the negative
coordinate is zeroed. -/
theorem iidFence_sum_iidMass_nonneg
    (h : ∑ ω : Fin 2 → Fin 2, iidMass iidNeg ω = 1) : False := by
  rw [iidNeg_mass_sum,
    show (4 : ℝ≥0∞) = ENNReal.ofReal ((4 : ℝ)) from (ENNReal.ofReal_natCast 4).symm,
    ← ENNReal.ofReal_one] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_iidMass_eq_one`'s `hq1`.** At `q = ![2, 0]` (kept
`hq0` genuine) the joint masses sum to `4 ≠ 1` — the hypothesis-form
wrapper consuming the file's delivered free-form fence
`junk_normalization_fence_QA` as its proof engine, reconciling it
into the per-clause discipline. -/
theorem iidFence_sum_iidMass_sum
    (h : ∑ ω : Fin 2 → Fin 2, iidMass (![2, 0] : Fin 2 → ℝ) ω = 1) : False := by
  rw [junk_normalization_fence_QA,
    show (4 : ℝ≥0∞) = ENNReal.ofReal ((4 : ℝ)) from (ENNReal.ofReal_natCast 4).symm,
    ← ENNReal.ofReal_one] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_coord_mul`'s `hq0`.** At `q = ![-1, 2]` with `e = 0`
and `F` the constant `1`, the left side is the total joint mass `4`
while the right side is the coordinate mass sum `2`: the clamped
negative coordinate zeroes three atoms on the left but only one
summand on the right. -/
theorem iidFence_sum_coord_mul_nonneg
    (h : ∑ ω : Fin 2 → Fin 2, (1 : ℝ≥0∞) * iidMass iidNeg ω
      = ∑ v, (1 : ℝ≥0∞) * ENNReal.ofReal (iidNeg v)) : False := by
  simp only [one_mul] at h
  rw [iidNeg_mass_sum, iidNeg_ofReal_sum,
    show (4 : ℝ≥0∞) = ENNReal.ofReal ((4 : ℝ)) from (ENNReal.ofReal_natCast 4).symm] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_coord_mul`'s `hq1`.** At `q = ![2, 0]` with `e = 0`
and `F` the constant `1`, the left side is the joint mass total `4`
while the right side is the coordinate mass sum `2`. -/
theorem iidFence_sum_coord_mul_sum
    (h : ∑ ω : Fin 2 → Fin 2, (1 : ℝ≥0∞) * iidMass iidTwo ω
      = ∑ v, (1 : ℝ≥0∞) * ENNReal.ofReal (iidTwo v)) : False := by
  simp only [one_mul] at h
  rw [iidTwo_mass_sum, iidTwo_ofReal_sum,
    show (4 : ℝ≥0∞) = ENNReal.ofReal ((4 : ℝ)) from (ENNReal.ofReal_natCast 4).symm] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_coord2_mul`'s `hq0`.** At `q = ![-1, 2]` on THREE
sample coordinates with `e = 0`, `e' = 1` and `F = G` the constant
`1`, the left side is the full product total `2³ = 8` while the right
side is `2 · 2 = 4`. The third coordinate is the breaker: on
`ι = Fin 2` both quantified coordinates are consumed by the statement
and the dropped identity holds there by Fubini (`(0+2)² = 2·2`). -/
theorem iidFence_sum_coord2_nonneg
    (h : ∑ ω : Fin 3 → Fin 2, (1 : ℝ≥0∞) * (1 : ℝ≥0∞) * iidMass iidNeg ω
      = (∑ v, (1 : ℝ≥0∞) * ENNReal.ofReal (iidNeg v))
        * (∑ v, (1 : ℝ≥0∞) * ENNReal.ofReal (iidNeg v))) : False := by
  simp only [one_mul] at h
  rw [show ∑ ω : Fin 3 → Fin 2, iidMass iidNeg ω
      = ∑ ω : Fin 3 → Fin 2, ∏ i,
          (fun (_ : Fin 3) (v : Fin 2) => ENNReal.ofReal (iidNeg v)) i (ω i) from by
      exact Finset.sum_congr rfl fun ω _ => rfl,
    show (Finset.univ : Finset (Fin 3 → Fin 2)) = Fintype.piFinset fun _ => Finset.univ from by
      ext ω; simp [Fintype.mem_piFinset],
    Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 2))
      (fun (_ : Fin 3) (v : Fin 2) => ENNReal.ofReal (iidNeg v)),
    iidNeg_ofReal_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hL : ENNReal.ofReal ((2 : ℝ)) ^ 3 = ENNReal.ofReal ((8 : ℝ)) := by
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; norm_num
  have hR : ENNReal.ofReal ((2 : ℝ)) * ENNReal.ofReal ((2 : ℝ)) = ENNReal.ofReal ((4 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num
  rw [hL, hR] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_coord2_mul`'s `hq1`.** At `q = ![2, 0]` on three
sample coordinates with `e = 0`, `e' = 1` and `F = G` the constant
`1`, the left side is `2³ = 8` against the right side `2 · 2 = 4` —
the same outside-the-consumed-coordinates breaker as the `hq0` twin,
with the kept `hq0` genuine this time. -/
theorem iidFence_sum_coord2_sum
    (h : ∑ ω : Fin 3 → Fin 2, (1 : ℝ≥0∞) * (1 : ℝ≥0∞) * iidMass iidTwo ω
      = (∑ v, (1 : ℝ≥0∞) * ENNReal.ofReal (iidTwo v))
        * (∑ v, (1 : ℝ≥0∞) * ENNReal.ofReal (iidTwo v))) : False := by
  simp only [one_mul] at h
  rw [show ∑ ω : Fin 3 → Fin 2, iidMass iidTwo ω
      = ∑ ω : Fin 3 → Fin 2, ∏ i,
          (fun (_ : Fin 3) (v : Fin 2) => ENNReal.ofReal (iidTwo v)) i (ω i) from by
      exact Finset.sum_congr rfl fun ω _ => rfl,
    show (Finset.univ : Finset (Fin 3 → Fin 2)) = Fintype.piFinset fun _ => Finset.univ from by
      ext ω; simp [Fintype.mem_piFinset],
    Finset.sum_prod_piFinset (Finset.univ : Finset (Fin 2))
      (fun (_ : Fin 3) (v : Fin 2) => ENNReal.ofReal (iidTwo v)),
    iidTwo_ofReal_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hL : ENNReal.ofReal ((2 : ℝ)) ^ 3 = ENNReal.ofReal ((8 : ℝ)) := by
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1; norm_num
  have hR : ENNReal.ofReal ((2 : ℝ)) * ENNReal.ofReal ((2 : ℝ)) = ENNReal.ofReal ((4 : ℝ)) := by
    rw [← ENNReal.ofReal_mul (by norm_num)]
    congr 1; norm_num
  rw [hL, hR] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `sum_coord2_mul`'s `hee : e ≠ e'`.** At the all-genuine
fixture `q23` with `e = e' = 0` and `F = G` the coordinate-`0`
indicator, the left side is the one-coordinate marginal `2/3` while
the right side is its square `4/9`: Cauchy–Schwarz is strict on a
two-point value space, so a single coordinate cannot play the role of
two. -/
theorem iidFence_sum_coord2_hee
    (h : ∑ ω : Fin 2 → Fin 2, (if ω 0 = 0 then (1 : ℝ≥0∞) else 0)
          * (if ω 0 = 0 then (1 : ℝ≥0∞) else 0) * iidMass q23 ω
      = (∑ v, (if v = 0 then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (q23 v))
        * (∑ v, (if v = 0 then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (q23 v))) : False := by
  have i00 : (if (![0, 0] : Fin 2 → Fin 2) 0 = 0 then (1 : ℝ≥0∞) else 0) = 1 := by simp
  have i01 : (if (![0, 1] : Fin 2 → Fin 2) 0 = 0 then (1 : ℝ≥0∞) else 0) = 1 := by simp
  have i10 : (if (![1, 0] : Fin 2 → Fin 2) 0 = 0 then (1 : ℝ≥0∞) else 0) = 0 := by simp
  have i11 : (if (![1, 1] : Fin 2 → Fin 2) 0 = 0 then (1 : ℝ≥0∞) else 0) = 0 := by simp
  have hL : ∑ ω : Fin 2 → Fin 2, (if ω 0 = 0 then (1 : ℝ≥0∞) else 0)
      * (if ω 0 = 0 then (1 : ℝ≥0∞) else 0) * iidMass q23 ω
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
    rw [univ_fin2_fin2,
      Finset.sum_insert (by simp [ne_00_01, ne_00_10, ne_00_11]),
      Finset.sum_insert (by simp [ne_01_10, ne_01_11]),
      Finset.sum_insert (by simp [ne_10_11]), Finset.sum_singleton,
      i00, i01, i10, i11, mass_00_QA, mass_01_QA]
    simp only [one_mul, zero_mul, add_zero, zero_add]
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
    congr 1; norm_num
  have hR : ∑ v, (if v = 0 then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (q23 v)
      = ENNReal.ofReal ((2 : ℝ) / 3) := by
    rw [Finset.sum_eq_single (0 : Fin 2)]
    · simp [q23_zero]
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ 0) h
  rw [hL, hR, ← ENNReal.ofReal_mul (by norm_num)] at h
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h

/-- **Fence: `indepFun_coord`'s `hee`.** At the all-genuine fixture
with `e = e' = 0` the two "independent" coordinates are the same
function: at `s = t = {0}`, `μ(A ∩ A) = μ(A) = 2/3 ≠ 4/9 = μ(A) ·
μ(A)` — a coordinate is not independent of itself. -/
theorem iidFence_indepFun_coord_hee
    (h : IndepFun (fun ω : Fin 2 → Fin 2 => ω 0) (fun ω : Fin 2 → Fin 2 => ω 0)
      (iidPMF q23 q23_nonneg q23_sum).toMeasure) : False := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
  have h' := h {0} {0}
    ((Set.toFinite ({0} : Set (Fin 2))).measurableSet)
    ((Set.toFinite ({0} : Set (Fin 2))).measurableSet)
  rw [Set.inter_self, cylinder_QA, ← ENNReal.ofReal_mul (by norm_num)] at h'
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h'

/-- **Fence: `indepFun_indicator_coord`'s `hee`.** The same clause at
the indicator codomain: with `e = e' = 0` and `i = j = 0` the two
"independent" indicators are the same function, killed at the
measurable set `{1}` (the indicator's support) through the preimage
identification with the `{ω | ω 0 = 0}` cylinder. -/
theorem iidFence_indepFun_indicator_hee
    (h : IndepFun (fun ω : Fin 2 → Fin 2 => (if ω 0 = 0 then (1 : ℝ) else 0))
        (fun ω : Fin 2 → Fin 2 => (if ω 0 = 0 then (1 : ℝ) else 0))
        (iidPMF q23 q23_nonneg q23_sum).toMeasure) : False := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h
  have hm : MeasurableSet ({1} : Set ℝ) := measurableSet_singleton 1
  have h' := h {1} {1} hm hm
  have hpre : (fun ω : Fin 2 → Fin 2 => (if ω 0 = 0 then (1 : ℝ) else 0)) ⁻¹' {1}
      = (fun ω : Fin 2 → Fin 2 => ω 0) ⁻¹' {0} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    by_cases hω : ω 0 = 0 <;> simp [hω]
  rw [hpre, Set.inter_self, cylinder_QA, ← ENNReal.ofReal_mul (by norm_num)] at h'
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h'

/-- **Fence: `iIndepFun_coord_apply`'s `he : Function.Injective e`.**
At the constant reindexing `e : Fin 2 → Fin 2 := fun _ => 0` with
`F k = id` (kept `hF` genuine: the identity is measurable) both
reindexed coordinates are `ω ↦ ω 0` — perfectly correlated — killed at
`T = univ`, `sets = {0}, {0}`: mutual independence fails as
`2/3 ≠ 4/9`. The empirical-stationary designs reindex trajectory
times into coordinates injectively; this clause is what makes that
transfer sound. -/
theorem iidFence_iIndep_apply_he
    (h : iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace (Fin 2)))
      (fun (_ : Fin 2) (ω : Fin 2 → Fin 2) => (fun (v : Fin 2) => v) (ω (0 : Fin 2)))
      (iidPMF q23 q23_nonneg q23_sum).toMeasure) : False := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h
  have h' := h (Finset.univ : Finset (Fin 2)) (sets := fun _ => {0})
    (fun _ _ => (Set.toFinite ({0} : Set (Fin 2))).measurableSet)
  have hint : (⋂ k ∈ (Finset.univ : Finset (Fin 2)),
      (fun ω : Fin 2 → Fin 2 => (fun (v : Fin 2) => v) (ω (0 : Fin 2))) ⁻¹' {0})
      = (fun ω : Fin 2 → Fin 2 => ω (0 : Fin 2)) ⁻¹' {0} := by
    ext ω
    simp only [Set.mem_iInter]
    exact ⟨fun hh => hh 0 (Finset.mem_univ 0), fun hh k _ => hh⟩
  simp only [hint, cylinder_QA] at h'
  rw [Finset.prod_const, Finset.card_fin, pow_two,
    ← ENNReal.ofReal_mul (by norm_num)] at h'
  exact iidF_ofReal_ne_ofReal (by norm_num) (by norm_num) (by norm_num) h'

/-- The strengthening companion: `iIndepFun_coord_apply`'s
`hF : ∀ k, Measurable (F k)` clause is decorative at the shelf's own
generality — `V` is a `Fintype` with `MeasurableSingletonClass`, so
every subset of `V` is measurable and `measurable_of_finite`
discharges the clause for any `F`. The hF-free twin holds verbatim. -/
theorem iIndepFun_coord_apply_strict {ι : Type*} [Fintype ι] [DecidableEq ι]
    {V : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
    (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    {γ : Type*} {mγ : MeasurableSpace γ}
    {ι' : Type*} [Fintype ι'] (e : ι' → ι) (he : Function.Injective e)
    (F : ι' → V → γ) :
    iIndepFun (fun _ : ι' => mγ)
      (fun (k : ι') (ω : ι → V) => F k (ω (e k))) (iidPMF q hq0 hq1).toMeasure :=
  iIndepFun_coord_apply q hq0 hq1 e he F (fun _ => measurable_of_finite _)

end AdversarialFences


/-! ## Singles pins: the probability trio — the iid twins and the
pairwise indicator clause

The first genuine consumption of the census's three remaining
probability singles (`indepFun_indicator_coord`,
`hoeffding_iid`, `bernstein_iid` — the scalar concentration stack's
never-instantiated iid forms), all on ONE shared fixture: the fair coin
`prFair` on `Fin 2 → Fin 2` with the ±1 family
`prX k ω = if ω k = 0 then 1 else -1` — centered at exactly the fair
coin, bounded by `a = 1`, variance `σ² = 1`, mutually independent
through the shelf's `iIndepFun_coord_apply`. The pins: the pairwise
theorem consumed with a two-route joint-mass join (the independence
factorization vs raw cylinder arithmetic); both twins instantiated at
`t = 2` where the tail event is exactly the same-value pairs, of raw
mass `1/2` (non-vacuous); and the honest bound contrast — at this
Rademacher fixture (`σ² = a²`, the extremal-variance case) the
Hoeffding bound is the strictly smaller one.
-/

section SinglesPins

/-- The fair coin distribution. -/
noncomputable def prFair : Fin 2 → ℝ := ![1 / 2, 1 / 2]

theorem prFair_nonneg : ∀ v, 0 ≤ prFair v := by
  intro v; fin_cases v <;> simp [prFair]

theorem prFair_sum : ∑ v, prFair v = 1 := by
  simp [prFair, Fin.sum_univ_two]; norm_num

/-- The ±1 family at the fair coin: centered, bounded by `1`. -/
def prX : Fin 2 → (Fin 2 → Fin 2) → ℝ :=
  fun k ω => if ω k = 0 then 1 else -1

theorem prX_meas (k : Fin 2) : Measurable (prX k) :=
  (measurable_of_finite (fun v : Fin 2 => if v = 0 then (1 : ℝ) else -1)).comp
    (measurable_coord k)

theorem prX_bound : ∀ k ω, |prX k ω| ≤ 1 := by
  intro k ω
  by_cases h : ω k = 0
  · simp [prX, h]
  · simp [prX, h]

theorem prX_indep :
    iIndepFun (fun _ : Fin 2 => (inferInstance : MeasurableSpace ℝ)) prX
      (iidPMF prFair prFair_nonneg prFair_sum).toMeasure :=
  iIndepFun_coord_apply prFair prFair_nonneg prFair_sum id Function.injective_id
    (fun _ v => if v = 0 then (1 : ℝ) else -1) (fun _ => measurable_of_finite _)

theorem prX_mean (k : Fin 2) :
    ∫ ω : Fin 2 → Fin 2, prX k ω ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure = 0 := by
  have hptw : ∀ ω : Fin 2 → Fin 2,
      prX k ω = (if ω k = 0 then (1 : ℝ) else 0) - (if ω k = 1 then (1 : ℝ) else 0) := by
    intro ω
    have hk : ω k = 0 ∨ ω k = 1 := by omega
    rcases hk with h | h
    · simp [prX, h]
    · simp [prX, h]
  have hmeasI : ∀ i : Fin 2, Measurable
      (fun ω : Fin 2 → Fin 2 => if ω k = i then (1 : ℝ) else 0) :=
    fun i => (measurable_of_finite
      (fun v : Fin 2 => if v = i then (1 : ℝ) else 0)).comp (measurable_coord k)
  have hintI : ∀ i : Fin 2, Integrable
      (fun ω : Fin 2 → Fin 2 => if ω k = i then (1 : ℝ) else 0)
      (iidPMF prFair prFair_nonneg prFair_sum).toMeasure :=
    fun i => integrable_of_bounded_measurable (a := 1) (hmeasI i)
      (fun ω => by
        by_cases h : ω k = i
        · simp [h]
        · simp [h])
  calc ∫ ω : Fin 2 → Fin 2, prX k ω ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure
      = ∫ ω : Fin 2 → Fin 2,
          ((if ω k = 0 then (1 : ℝ) else 0) - (if ω k = 1 then (1 : ℝ) else 0))
            ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure :=
        integral_congr_ae (ae_of_all _ hptw)
    _ = (∫ ω : Fin 2 → Fin 2, (if ω k = 0 then (1 : ℝ) else 0)
          ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure)
        - (∫ ω : Fin 2 → Fin 2, (if ω k = 1 then (1 : ℝ) else 0)
          ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure) :=
        integral_sub (hintI 0) (hintI 1)
    _ = prFair 0 - prFair 1 := by
        rw [integral_indicator prFair prFair_nonneg prFair_sum k 0,
          integral_indicator prFair prFair_nonneg prFair_sum k 1]
    _ = 0 := by simp [prFair]

/-- **The pairwise indicator-independence theorem consumed** (the
census's `indepFun_indicator_coord`). -/
theorem pri_indepFun_indicator_pin :
    IndepFun (fun ω : Fin 2 → Fin 2 => (if ω 0 = 0 then (1 : ℝ) else 0))
      (fun ω : Fin 2 → Fin 2 => (if ω 1 = 1 then (1 : ℝ) else 0))
      (iidPMF prFair prFair_nonneg prFair_sum).toMeasure :=
  indepFun_indicator_coord prFair prFair_nonneg prFair_sum (by decide) 0 1

/-- Route A: the joint preimage mass through the consumed independence
theorem (the inter-preimage factorization at the singleton level set
`{1} : Set ℝ`). -/
theorem pri_joint_mass_via_indep :
    (iidPMF prFair prFair_nonneg prFair_sum).toMeasure
        {ω : Fin 2 → Fin 2 | ω 0 = 0 ∧ ω 1 = 1}
      = ENNReal.ofReal ((1 : ℝ) / 4) := by
  have hind := pri_indepFun_indicator_pin
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind
  have hset : MeasurableSet ({1} : Set ℝ) := by simp
  have hsplit := hind {1} {1} hset hset
  have heq1 : (fun ω : Fin 2 → Fin 2 => (if ω 0 = 0 then (1 : ℝ) else 0)) ⁻¹' ({1} : Set ℝ)
      = {ω : Fin 2 → Fin 2 | ω 0 = 0} := by
    ext ω; simp
  have heq2 : (fun ω : Fin 2 → Fin 2 => (if ω 1 = 1 then (1 : ℝ) else 0)) ⁻¹' ({1} : Set ℝ)
      = {ω : Fin 2 → Fin 2 | ω 1 = 1} := by
    ext ω; simp
  have hint2 : {ω : Fin 2 → Fin 2 | ω 0 = 0} ∩ {ω : Fin 2 → Fin 2 | ω 1 = 1}
      = {ω : Fin 2 → Fin 2 | ω 0 = 0 ∧ ω 1 = 1} := by
    ext ω; simp [Set.mem_inter_iff]
  rw [heq1, heq2, hint2] at hsplit
  have hcyl : ∀ (e : Fin 2) (v : Fin 2),
      (iidPMF prFair prFair_nonneg prFair_sum).toMeasure
        {ω : Fin 2 → Fin 2 | ω e = v}
      = ENNReal.ofReal (prFair v) := by
    intro e v
    have hpre : {ω : Fin 2 → Fin 2 | ω e = v}
        = (fun ω : Fin 2 → Fin 2 => ω e) ⁻¹' ({v} : Set (Fin 2)) := by
      ext ω; simp
    rw [hpre, toMeasure_cyl prFair prFair_nonneg prFair_sum e {v},
      Finset.sum_eq_single v]
    · simp [prFair]
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ v) h
  rw [hcyl 0 0, hcyl 1 1] at hsplit
  calc (iidPMF prFair prFair_nonneg prFair_sum).toMeasure
          {ω : Fin 2 → Fin 2 | ω 0 = 0 ∧ ω 1 = 1}
      = ENNReal.ofReal (prFair 0) * ENNReal.ofReal (prFair 1) := hsplit
    _ = ENNReal.ofReal ((1 : ℝ) / 4) := by
        rw [← ENNReal.ofReal_mul (prFair_nonneg 0)]
        congr 1; simp [prFair]; norm_num

/-- Route B: the same joint mass by raw cylinder arithmetic
(`toMeasure_cyl_inter` — no independence consumed). Two routes, one
value. -/
theorem pri_joint_mass_raw :
    (iidPMF prFair prFair_nonneg prFair_sum).toMeasure
        {ω : Fin 2 → Fin 2 | ω 0 = 0 ∧ ω 1 = 1}
      = ENNReal.ofReal ((1 : ℝ) / 4) := by
  classical
  have hset : {ω : Fin 2 → Fin 2 | ω 0 = 0 ∧ ω 1 = 1}
      = ⋂ i ∈ (Finset.univ : Finset (Fin 2)),
          (fun ω : Fin 2 → Fin 2 => ω i) ⁻¹'
            (if i = 0 then ({0} : Set (Fin 2)) else {1}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ,
      Set.mem_preimage, Fin.forall_fin_two]
    by_cases h0 : ω 0 = 0 <;> by_cases h1 : ω 1 = 0 <;>
      simp [h0, h1]
  rw [hset, toMeasure_cyl_inter prFair prFair_nonneg prFair_sum
    (Finset.univ : Finset (Fin 2))
    (fun i => if i = 0 then ({0} : Set (Fin 2)) else {1})]
  simp [Fin.prod_univ_two, Finset.sum_ite_eq', Set.mem_singleton_iff,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, prFair, Fin.isValue]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  norm_num

/-- **The raw event mass**: the Hoeffding/Bernstein tail event
`{|∑ X| ≥ 2}` is exactly the same-value pairs, of raw mass `1/2` —
the bound's non-vacuity witness. -/
theorem pri_event_mass_raw :
    (iidPMF prFair prFair_nonneg prFair_sum).toMeasure
        {ω : Fin 2 → Fin 2 | |∑ i, prX i ω| ≥ 2}
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  classical
  have hsplit : {ω : Fin 2 → Fin 2 | |∑ i, prX i ω| ≥ 2}
      = {ω : Fin 2 → Fin 2 | ω 0 = 0 ∧ ω 1 = 0}
        ∪ {ω : Fin 2 → Fin 2 | ω 0 = 1 ∧ ω 1 = 1} := by
    ext ω
    have ha : ω 0 = 0 ∨ ω 0 = 1 := by omega
    have hb : ω 1 = 0 ∨ ω 1 = 1 := by omega
    rcases ha with a | a <;> rcases hb with b | b <;>
      simp [prX, a, b, Set.mem_union, Fin.sum_univ_two] <;> norm_num
  have hpart : ∀ v : Fin 2,
      (iidPMF prFair prFair_nonneg prFair_sum).toMeasure
        {ω : Fin 2 → Fin 2 | ω 0 = v ∧ ω 1 = v}
      = ENNReal.ofReal ((1 : ℝ) / 4) := by
    intro v
    have hset : {ω : Fin 2 → Fin 2 | ω 0 = v ∧ ω 1 = v}
        = ⋂ i ∈ (Finset.univ : Finset (Fin 2)),
            (fun ω : Fin 2 → Fin 2 => ω i) ⁻¹' ({v} : Set (Fin 2)) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ,
        Set.mem_preimage, Fin.forall_fin_two, Set.mem_singleton_iff]
      by_cases h0 : ω 0 = v <;> by_cases h1 : ω 1 = v <;>
        simp [h0, h1]
    rw [hset, toMeasure_cyl_inter prFair prFair_nonneg prFair_sum
      (Finset.univ : Finset (Fin 2)) (fun _ => ({v} : Set (Fin 2)))]
    simp [Fin.prod_univ_two, Finset.sum_ite_eq', Set.mem_singleton_iff,
      mul_ite, mul_one, mul_zero, prFair, Fin.isValue]
    fin_cases v <;> simp [prFair]
    all_goals rw [sq, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
    all_goals norm_num
  have hdis : Disjoint {ω : Fin 2 → Fin 2 | ω 0 = 0 ∧ ω 1 = 0}
      {ω : Fin 2 → Fin 2 | ω 0 = 1 ∧ ω 1 = 1} := by
    intro z h1 h2
    have ha : ∀ ω : Fin 2 → Fin 2, ω ∈ z → ω 0 = 0 ∧ ω 1 = 0 :=
      fun ω hω => h1 hω
    have hb : ∀ ω : Fin 2 → Fin 2, ω ∈ z → ω 0 = 1 ∧ ω 1 = 1 :=
      fun ω hω => h2 hω
    exact fun ω hω => absurd ((ha ω hω).1.symm.trans (hb ω hω).1) (by decide)
  have hmeasA : MeasurableSet {ω : Fin 2 → Fin 2 | ω 0 = 0 ∧ ω 1 = 0} :=
    Set.Finite.measurableSet (Set.toFinite _)
  have hmeasB : MeasurableSet {ω : Fin 2 → Fin 2 | ω 0 = 1 ∧ ω 1 = 1} :=
    Set.Finite.measurableSet (Set.toFinite _)
  rw [hsplit, measure_union hdis hmeasB, hpart 0, hpart 1]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- **The Hoeffding iid twin consumed**: the theorem instance at
`t = 2`, `a = 1`, `n = 2`, stated at the theorem's verbatim bound. -/
theorem pri_hoeffding_iid_pin :
    (iidPMF prFair prFair_nonneg prFair_sum).toMeasure
        {ω : Fin 2 → Fin 2 | |∑ i, prX i ω| ≥ 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-(2 : ℝ) ^ 2 / (2 * ((2 : ℝ) * 1 ^ 2)))) :=
  hoeffding_iid (a := 1) (by norm_num) prX_meas prX_indep prX_bound prX_mean 2
    (by norm_num)

/-- The display collapse: the verbatim bound is `2 exp(−1)`. -/
theorem pri_hoeffding_display :
    2 * Real.exp (-(2 : ℝ) ^ 2 / (2 * ((2 : ℝ) * 1 ^ 2)))
      = 2 * Real.exp (-(1 : ℝ)) := by norm_num

/-- **The Bernstein iid twin consumed**: the same fixture at `σ² = 1`,
stated at the theorem's verbatim bound. -/
theorem pri_bernstein_iid_pin :
    (iidPMF prFair prFair_nonneg prFair_sum).toMeasure
        {ω : Fin 2 → Fin 2
            | |∑ i, (prX i ω - ∫ ω', prX i ω' ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure)| ≥ 2}
      ≤ ENNReal.ofReal
          (2 * Real.exp (-(2 : ℝ) ^ 2 / (2 * ((2 : ℝ) * 1) + (2 * 1 * 2) / 3))) := by
  have hbound : ∀ i ω, |prX i ω - ∫ ω', prX i ω'
      ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure| ≤ 1 := by
    intro i ω
    rw [prX_mean i, sub_zero]
    exact prX_bound i ω
  have hvar : ∀ i, ∫ ω, (prX i ω
      - ∫ ω', prX i ω' ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure) ^ 2
      ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure = 1 := by
    intro i
    have hptw : ∀ ω : Fin 2 → Fin 2,
        (prX i ω
          - ∫ ω', prX i ω' ∂(iidPMF prFair prFair_nonneg prFair_sum).toMeasure) ^ 2
          = 1 := by
      intro ω
      rw [prX_mean i]
      by_cases h : ω i = 0 <;> simp [prX, h]
    rw [integral_congr_ae (ae_of_all _ hptw)]
    simp
  exact bernstein_iid (a := 1) (σ_sq := 1) (by norm_num) (by norm_num)
    prX_meas prX_indep hbound hvar 2 (by norm_num)

/-- The display collapse: the verbatim Bernstein bound is `2 exp(−3/4)`. -/
theorem pri_bernstein_display :
    2 * Real.exp (-(2 : ℝ) ^ 2 / (2 * ((2 : ℝ) * 1) + (2 * 1 * 2) / 3))
      = 2 * Real.exp (-(3 / 4 : ℝ)) := by norm_num

/-- **The bound contrast, honestly stated**: at this Rademacher
fixture (`σ² = a² = 1`, the extremal-variance case) the variance term
cannot help and the Hoeffding bound is the strictly smaller one —
`2 exp(−1) < 2 exp(−3/4)` by pure monotonicity (no numeric bound on
`e`). The opposite direction — Bernstein strictly sharper — needs an
asymmetric family with `σ² < a²` at a biased coin (a second fixture
family, priced not owed). -/
theorem pri_bound_contrast :
    2 * Real.exp (-(1 : ℝ)) < 2 * Real.exp (-(3 / 4 : ℝ)) := by
  have h : Real.exp (-(1 : ℝ)) < Real.exp (-(3 / 4 : ℝ)) :=
    Real.exp_lt_exp.mpr (by norm_num)
  exact mul_lt_mul_of_pos_left h (by norm_num)

end SinglesPins

end Scaffold.Mathlib.Probability.IIDProduct.QA
