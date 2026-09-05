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

end Scaffold.Mathlib.Probability.IIDProduct.QA
