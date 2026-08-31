/-
  Poincare_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Poincare` — the Poincaré
  inequality family, per `proposals/poincare-inequality.md`'s named
  obligations, all on the repo's counted fixture family (K₂, P₃, K₃,
  and a disconnected two-edge `Fin 4` fixture):

  1. **Exact-attainment pins** — the strongest QA shape a bound theorem
     can have: on `K₂` at the Fiedler vector `(1,−1)` both sides of the
     combinatorial inequality compute to exactly `2` (gap `2`, energy
     `4`); on `P₃` at the Fiedler vector `(1,0,−1)` both sides compute
     to exactly `2` (gap `1`, energy `2`); on `K₃` at `(1,−1,0)` both
     sides of the *normalized* inequality compute to exactly `4`
     (weighted variance `4`, energy `6` over gap `3/2`, the gap itself
     pinned through the entrywise identity `L_sym(K₃) = (1/2) • L(K₃)`
     and the scaling lemma). No smaller denominator constant is
     possible — the wrong-constant refutation below proves the shape
     with the gap replaced by `3` false at the very fixture that
     attains the true constant.

  2. **The no-constant connectivity fence** — on the disconnected
     two-edge fixture, the component indicator has variance exactly
     `1` and energy exactly `0`, so *for every* `c : ℝ` the
     Poincaré-shaped `variance ≤ c · energy` is false: the
     `0 < λ₂` hypothesis (derivable from connectivity) is exactly the
     boundary of the true region, not a convenience. The fixture's
     spectral gap is also proved nonpositive, showing precisely why the
     division form's hypothesis cannot fire there.

  3. **Edge-expansion instances** — `spectral_gap_edge_expansion`
     instantiated at singleton cuts of `K₂` and `K₃`, with both sides
     pinned and attained with equality (`1 = 1` and `2 = 2`): the
     linear-in-gap bound is tight at these fixtures, and the instances
     consume `Multiway.lean`'s indicator energy identity.

  Supporting spectrum pins (λ₂ of K₂/P₃/K₃ and the boundary values) are
  reconstructed locally by the repo's established idioms (energy
  identities through `laplacian_quadForm`, two-sided
  `secondEval_le_rayleigh` / `le_csInf` sandwiches). Everything here is
  pure hard crust: `#print axioms` via `wip/poincare_axcheck.lean`
  reads exactly `propext, Classical.choice, Quot.sound` on every
  audited declaration.
-/

import Scaffold.Mathlib.GraphTheory.Poincare

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Fixtures and spectrum pins -/

/-- Adjacency matrix of the two-vertex edge `K₂`. -/
def pcEdge : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; 1, 0]

theorem pcEdge_apply (i j : Fin 2) :
    pcEdge i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem pcEdge_card : 2 ≤ Fintype.card (Fin 2) := le_refl 2

theorem pcEdge_isSymm : pcEdge.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [pcEdge]

theorem pcEdge_nonneg : ∀ i j, 0 ≤ pcEdge i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pcEdge]

/-- The `K₂` energy identity: `xᵀ L x = (x₀ − x₁)²`. -/
theorem pcEdge_energy_QA (x : Fin 2 → ℝ) :
    quadForm (laplacian pcEdge) x = (x 0 - x 1) ^ 2 := by
  rw [laplacian_quadForm pcEdge pcEdge_isSymm]
  have hsum : (∑ i, ∑ j, pcEdge i j * (x i - x j) ^ 2)
      = 2 * (x 0 - x 1) ^ 2 := by
    simp only [pcEdge, Matrix.of_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead]
    have hsymm : (x 1 - x 0) ^ 2 = (x 0 - x 1) ^ 2 := by
      rw [← neg_sub (x 1) (x 0), neg_sq]
    have hdiag : (x 0 - x 0) ^ 2 + ((x 1 - x 1) ^ 2
        + (x 0 - x 1) ^ 2 + (x 1 - x 0) ^ 2) = 2 * (x 0 - x 1) ^ 2 := by
      rw [hsymm]
      ring
    linarith [hdiag]
  rw [hsum]
  ring

theorem pcEdge_secondEval_eq_two_QA :
    secondEval (laplacian pcEdge) (laplacian_symmetric pcEdge pcEdge_isSymm)
      (by decide) = 2 := by
  have hx0 : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, -1] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have hxorth : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.vecTail, Matrix.vecHead]
    norm_num
  have hdot : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) ![1, -1] = 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.vecTail, Matrix.vecHead]
    norm_num
  have hray : rayleigh (laplacian pcEdge) (![1, -1] : Fin 2 → ℝ) = 2 := by
    rw [rayleigh, if_neg hx0, pcEdge_energy_QA, hdot]
    norm_num
  refine le_antisymm ?_ ?_
  · have h := secondEval_le_rayleigh (laplacian_symmetric pcEdge pcEdge_isSymm)
      (laplacian_psd pcEdge pcEdge_isSymm pcEdge_nonneg)
      (laplacian_ones_in_kernel pcEdge) (by decide) hx0 hxorth
    rw [hray] at h
    exact h
  · have hx0' : (![1, -1] : Fin 2 → ℝ) ≠ 0 := hx0
    have hxorth' : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) onesVec = 0 := hxorth
    rw [secondEval_variational (laplacian_symmetric pcEdge pcEdge_isSymm)
      (laplacian_psd pcEdge pcEdge_isSymm pcEdge_nonneg)
      (laplacian_ones_in_kernel pcEdge) (by decide)]
    refine le_csInf ⟨2, ![1, -1], hx0', hxorth', hray⟩ ?_
    rintro r ⟨z, hz0, hzorth, hzr⟩
    rw [← hzr, rayleigh, if_neg hz0, pcEdge_energy_QA,
      le_div_iff₀ (dotProduct_self_pos hz0)]
    have hzsum : z 0 + z 1 = 0 := by
      simpa [Matrix.dotProduct, onesVec, Fin.sum_univ_two, mul_one] using hzorth
    have hz1 : z 1 = - z 0 := by linarith
    have hzz : Matrix.dotProduct z z = 2 * z 0 ^ 2 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_two]
      rw [hz1]
      ring
    have hkey : (z 0 - - z 0) ^ 2 = 2 * (2 * z 0 ^ 2) := by ring
    rw [hz1, hzz]
    linarith

/-- Adjacency matrix of the three-vertex path `P₃`. -/
def pcP3 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem pcP3_card : 2 ≤ Fintype.card (Fin 3) := by decide

theorem pcP3_isSymm : pcP3.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [pcP3]

theorem pcP3_nonneg : ∀ i j, 0 ≤ pcP3 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pcP3]

/-- The `P₃` energy identity: `xᵀ L x = (x₀ − x₁)² + (x₁ − x₂)²`. -/
theorem pcP3_energy_QA (x : Fin 3 → ℝ) :
    quadForm (laplacian pcP3) x = (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 := by
  rw [laplacian_quadForm pcP3 pcP3_isSymm]
  have hsum : (∑ i, ∑ j, pcP3 i j * (x i - x j) ^ 2)
      = 2 * ((x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2) := by
    simp only [pcP3, Matrix.of_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hsum]
  ring

theorem pcP3_secondEval_eq_one_QA :
    secondEval (laplacian pcP3) (laplacian_symmetric pcP3 pcP3_isSymm)
      (by decide) = 1 := by
  have hx0 : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, 0, -1] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have hxorth : Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ) onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead]
    norm_num
  have hdot : Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ) ![1, 0, -1] = 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead]
    norm_num
  have he : quadForm (laplacian pcP3) (![1, 0, -1] : Fin 3 → ℝ) = 2 := by
    rw [pcP3_energy_QA]
    norm_num
  have hray : rayleigh (laplacian pcP3) (![1, 0, -1] : Fin 3 → ℝ) = 1 := by
    rw [rayleigh, if_neg hx0, he, hdot]
    norm_num
  refine le_antisymm ?_ ?_
  · have h := secondEval_le_rayleigh (laplacian_symmetric pcP3 pcP3_isSymm)
      (laplacian_psd pcP3 pcP3_isSymm pcP3_nonneg)
      (laplacian_ones_in_kernel pcP3) (by decide) hx0 hxorth
    rw [hray] at h
    exact h
  · rw [secondEval_variational (laplacian_symmetric pcP3 pcP3_isSymm)
      (laplacian_psd pcP3 pcP3_isSymm pcP3_nonneg)
      (laplacian_ones_in_kernel pcP3) (by decide)]
    refine le_csInf ⟨1, ![1, 0, -1], hx0, hxorth, hray⟩ ?_
    rintro r ⟨z, hz0, hzorth, hzr⟩
    rw [← hzr, rayleigh, if_neg hz0, pcP3_energy_QA,
      le_div_iff₀ (dotProduct_self_pos hz0)]
    have hzsum : z 0 + z 1 + z 2 = 0 := by
      simpa [Matrix.dotProduct, onesVec, Fin.sum_univ_three, mul_one] using hzorth
    have hzz : Matrix.dotProduct z z = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_three]
      ring
    have hkey : (z 0 - z 1) ^ 2 + (z 1 - z 2) ^ 2
        = (z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) + 3 * z 1 ^ 2 := by
      have hsplit : (z 0 - z 1) ^ 2 + (z 1 - z 2) ^ 2
            - ((z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2) + 3 * z 1 ^ 2)
          = -2 * z 1 * (z 0 + z 1 + z 2) := by ring
      rw [hzsum] at hsplit
      linarith
    rw [hkey, hzz]
    linarith [sq_nonneg (z 1)]

/-- Adjacency matrix of the triangle `K₃`. -/
def pcK3 : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 1; 1, 0, 1; 1, 1, 0]

theorem pcK3_card : 2 ≤ Fintype.card (Fin 3) := by decide

theorem pcK3_apply (i j : Fin 3) :
    pcK3 i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem pcK3_isSymm : pcK3.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [pcK3_apply, pcK3_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem pcK3_nonneg : ∀ i j, 0 ≤ pcK3 i j := by
  intro i j
  rw [pcK3_apply]
  split <;> norm_num

theorem pcK3_deg_eq_two : ∀ i, deg pcK3 i = 2 := by
  intro i
  fin_cases i <;> simp [deg, pcK3_apply, Fin.sum_univ_three] <;>
    try norm_num

theorem pcK3_deg_pos : ∀ i, 0 < deg pcK3 i := by
  intro i
  rw [pcK3_deg_eq_two]
  norm_num

/-- The `K₃` energy identity: `xᵀ L x = 3‖x‖² − (∑ x)²`. -/
theorem pcK3_energy_identity_QA (x : Fin 3 → ℝ) :
    quadForm (laplacian pcK3) x
      = 3 * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2)
        - (x 0 + x 1 + x 2) ^ 2 := by
  have hedges : (∑ i, ∑ j, pcK3 i j * (x i - x j) ^ 2)
      = 2 * ((x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 2 - x 0) ^ 2) := by
    simp only [pcK3, Matrix.of_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [laplacian_quadForm pcK3 pcK3_isSymm, hedges]
  ring

theorem pcK3_secondEval_eq_three_QA :
    secondEval (laplacian pcK3) (laplacian_symmetric pcK3 pcK3_isSymm)
      (by decide) = 3 := by
  have hx0 : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, -1, 0] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have hxorth : Matrix.dotProduct (![1, -1, 0] : Fin 3 → ℝ) onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead]
    norm_num
  have hdot : Matrix.dotProduct (![1, -1, 0] : Fin 3 → ℝ) ![1, -1, 0] = 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead]
    norm_num
  have hsum : (![1, -1, 0] : Fin 3 → ℝ) 0 + (![1, -1, 0] : Fin 3 → ℝ) 1
      + (![1, -1, 0] : Fin 3 → ℝ) 2 = 0 := by norm_num
  have he : quadForm (laplacian pcK3) (![1, -1, 0] : Fin 3 → ℝ) = 6 := by
    rw [pcK3_energy_identity_QA]
    norm_num
  have hray : rayleigh (laplacian pcK3) (![1, -1, 0] : Fin 3 → ℝ) = 3 := by
    rw [rayleigh, if_neg hx0, he, hdot]
    norm_num
  refine le_antisymm ?_ ?_
  · have h := secondEval_le_rayleigh (laplacian_symmetric pcK3 pcK3_isSymm)
      (laplacian_psd pcK3 pcK3_isSymm pcK3_nonneg)
      (laplacian_ones_in_kernel pcK3) (by decide) hx0 hxorth
    rw [hray] at h
    exact h
  · rw [secondEval_variational (laplacian_symmetric pcK3 pcK3_isSymm)
      (laplacian_psd pcK3 pcK3_isSymm pcK3_nonneg)
      (laplacian_ones_in_kernel pcK3) (by decide)]
    refine le_csInf ⟨3, ![1, -1, 0], hx0, hxorth, hray⟩ ?_
    rintro r ⟨z, hz0, hzorth, hzr⟩
    rw [← hzr, rayleigh, if_neg hz0,
      le_div_iff₀ (dotProduct_self_pos hz0)]
    have hzsum : z 0 + z 1 + z 2 = 0 := by
      simpa [Matrix.dotProduct, onesVec, Fin.sum_univ_three, mul_one] using hzorth
    have he : quadForm (laplacian pcK3) z
        = 3 * (z 0 * z 0 + z 1 * z 1 + z 2 * z 2) := by
      rw [pcK3_energy_identity_QA, hzsum]
      norm_num
    have hzz : Matrix.dotProduct z z = z 0 * z 0 + z 1 * z 1 + z 2 * z 2 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_three]
    rw [he, hzz]

/-! ## The normalized-Laplacian pin on `K₃` -/

theorem pcK3_sqrt2_inv_mul : ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) = 1 / 2 := by
  rw [← mul_inv_rev, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    inv_eq_one_div]

/-- The triangle's normalized Laplacian is exactly half its
combinatorial Laplacian (entrywise, degrees all `2`). -/
theorem pcK3_normalizedLaplacian_eq_half_QA :
    normalizedLaplacian pcK3 = ((1 : ℝ) / 2) • laplacian pcK3 := by
  have hentry : ∀ i j : Fin 3,
      (degreeInvSqrt pcK3 * pcK3 * degreeInvSqrt pcK3) i j
        = pcK3 i j / 2 := by
    intro i j
    rw [degreeInvSqrt, Matrix.mul_diagonal, Matrix.diagonal_mul,
      pcK3_deg_eq_two i, pcK3_deg_eq_two j]
    calc ((Real.sqrt 2)⁻¹ * pcK3 i j) * (Real.sqrt 2)⁻¹
        = pcK3 i j * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) := by ring
      _ = pcK3 i j * (1 / 2) := by rw [pcK3_sqrt2_inv_mul]
      _ = pcK3 i j / 2 := by ring
  apply Matrix.ext fun i j => ?_
  rw [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    hentry i j, Matrix.smul_apply, smul_eq_mul, laplacian, Matrix.sub_apply,
    degreeMatrix, pcK3_deg_eq_two i]
  fin_cases i <;> fin_cases j <;> rw [pcK3_apply] <;> split <;> norm_num

theorem pcK3_secondEval_normalized_eq_QA :
    secondEval (normalizedLaplacian pcK3)
      (normalizedLaplacian_symmetric pcK3 pcK3_isSymm) pcK3_card
      = 3 / 2 := by
  have hhalf : secondEval (((1 : ℝ) / 2) • laplacian pcK3)
      (smul_isSymm (laplacian_symmetric pcK3 pcK3_isSymm) ((1 : ℝ) / 2))
      (by decide)
      = 1 / 2 * secondEval (laplacian pcK3)
          (laplacian_symmetric pcK3 pcK3_isSymm) pcK3_card :=
    secondEval_smul_of_pos (laplacian_symmetric pcK3 pcK3_isSymm)
      (laplacian_psd pcK3 pcK3_isSymm pcK3_nonneg)
      (laplacian_ones_in_kernel pcK3) pcK3_card (by norm_num)
  rw [secondEval_congr (normalizedLaplacian_symmetric pcK3 pcK3_isSymm)
    (smul_isSymm (laplacian_symmetric pcK3 pcK3_isSymm) ((1 : ℝ) / 2))
    pcK3_normalizedLaplacian_eq_half_QA (by decide),
    hhalf, pcK3_secondEval_eq_three_QA]
  norm_num

theorem pcEdge_secondEval_pos_QA :
    0 < secondEval (laplacian pcEdge)
      (laplacian_symmetric pcEdge pcEdge_isSymm) pcEdge_card := by
  rw [pcEdge_secondEval_eq_two_QA]
  norm_num

theorem pcP3_secondEval_pos_QA :
    0 < secondEval (laplacian pcP3)
      (laplacian_symmetric pcP3 pcP3_isSymm) pcP3_card := by
  rw [pcP3_secondEval_eq_one_QA]
  norm_num

theorem pcK3_secondEval_normalized_pos_QA :
    0 < secondEval (normalizedLaplacian pcK3)
      (normalizedLaplacian_symmetric pcK3 pcK3_isSymm) pcK3_card := by
  rw [pcK3_secondEval_normalized_eq_QA]
  norm_num

/-! ## The headline QA obligations -/

/-- **The `K₂` attainment pin**: at the Fiedler vector `(1, −1)` both
sides of the Poincaré inequality compute to exactly `2` — the constant
is sharp (no smaller denominator constant can hold, which the
wrong-constant refutation below proves at the same fixture). -/
theorem pcEdge_poincare_instance_QA :
    (∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
          / (Fintype.card (Fin 2) : ℝ)) ^ 2)
      ≤ quadForm (laplacian pcEdge) (![1, -1] : Fin 2 → ℝ)
        / secondEval (laplacian pcEdge)
            (laplacian_symmetric pcEdge pcEdge_isSymm) pcEdge_card :=
  poincare_inequality pcEdge pcEdge_isSymm pcEdge_nonneg pcEdge_card
    pcEdge_secondEval_pos_QA ![1, -1]

theorem pcEdge_poincare_attained_QA :
    (∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j)
          / (Fintype.card (Fin 2) : ℝ)) ^ 2)
      = 2
      ∧ quadForm (laplacian pcEdge) (![1, -1] : Fin 2 → ℝ)
          / secondEval (laplacian pcEdge)
              (laplacian_symmetric pcEdge pcEdge_isSymm) pcEdge_card = 2 := by
  refine ⟨?_, ?_⟩
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead,
      Fintype.card_fin]
    norm_num
  · rw [pcEdge_energy_QA, pcEdge_secondEval_eq_two_QA]
    norm_num

/-- **The wrong-constant refutation**: replacing the spectral gap `2` by
`3` in the `K₂` instance makes the conclusion false at the same Fiedler
vector (`2 ≤ 4/3` refuted) — the attained constant is load-bearing. -/
theorem pcEdge_wrong_constant_refuted_QA :
    ¬ ((∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
        - (∑ j, (![1, -1] : Fin 2 → ℝ) j) / (Fintype.card (Fin 2) : ℝ)) ^ 2)
        ≤ quadForm (laplacian pcEdge) (![1, -1] : Fin 2 → ℝ) / 3) := by
  have h1 : (∑ i : Fin 2, ((![1, -1] : Fin 2 → ℝ) i
      - (∑ j, (![1, -1] : Fin 2 → ℝ) j) / (Fintype.card (Fin 2) : ℝ)) ^ 2)
      = 2 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.vecTail, Matrix.vecHead,
      Fintype.card_fin]
    norm_num
  rw [h1, pcEdge_energy_QA]
  norm_num

/-- **The `P₃` attainment pin**: at the Fiedler vector `(1, 0, −1)` both
sides compute to exactly `2` (gap `1`, energy `2`). -/
theorem pcP3_poincare_instance_QA :
    (∑ i : Fin 3, ((![1, 0, -1] : Fin 3 → ℝ) i
        - (∑ j, (![1, 0, -1] : Fin 3 → ℝ) j)
          / (Fintype.card (Fin 3) : ℝ)) ^ 2)
      ≤ quadForm (laplacian pcP3) (![1, 0, -1] : Fin 3 → ℝ)
        / secondEval (laplacian pcP3)
            (laplacian_symmetric pcP3 pcP3_isSymm) pcP3_card :=
  poincare_inequality pcP3 pcP3_isSymm pcP3_nonneg pcP3_card
    pcP3_secondEval_pos_QA ![1, 0, -1]

theorem pcP3_poincare_attained_QA :
    (∑ i : Fin 3, ((![1, 0, -1] : Fin 3 → ℝ) i
        - (∑ j, (![1, 0, -1] : Fin 3 → ℝ) j)
          / (Fintype.card (Fin 3) : ℝ)) ^ 2)
      = 2
      ∧ quadForm (laplacian pcP3) (![1, 0, -1] : Fin 3 → ℝ)
          / secondEval (laplacian pcP3)
              (laplacian_symmetric pcP3 pcP3_isSymm) pcP3_card = 2 := by
  refine ⟨?_, ?_⟩
  · simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      Fintype.card_fin]
    norm_num
  · rw [pcP3_energy_QA, pcP3_secondEval_eq_one_QA]
    norm_num

/-- **The `K₃` normalized-form attainment pin**: at `f = (1, −1, 0)` (a
Fiedler vector of the triangle, in the degree-weighted sense) both sides
of the normalized Poincaré inequality compute to exactly `4` (weighted
variance `4`, energy `6` over gap `3/2`). -/
theorem pcK3_normalized_poincare_instance_QA :
    (∑ i : Fin 3, deg pcK3 i * ((![1, -1, 0] : Fin 3 → ℝ) i
        - (∑ j, deg pcK3 j * (![1, -1, 0] : Fin 3 → ℝ) j)
          / (∑ j, deg pcK3 j)) ^ 2)
      ≤ quadForm (laplacian pcK3) (![1, -1, 0] : Fin 3 → ℝ)
        / secondEval (normalizedLaplacian pcK3)
            (normalizedLaplacian_symmetric pcK3 pcK3_isSymm) pcK3_card :=
  poincare_inequality_normalized pcK3 pcK3_isSymm pcK3_nonneg
    pcK3_deg_pos pcK3_card pcK3_secondEval_normalized_pos_QA ![1, -1, 0]

theorem pcK3_normalized_poincare_attained_QA :
    (∑ i : Fin 3, deg pcK3 i * ((![1, -1, 0] : Fin 3 → ℝ) i
        - (∑ j, deg pcK3 j * (![1, -1, 0] : Fin 3 → ℝ) j)
          / (∑ j, deg pcK3 j)) ^ 2)
      = 4
      ∧ quadForm (laplacian pcK3) (![1, -1, 0] : Fin 3 → ℝ)
          / secondEval (normalizedLaplacian pcK3)
              (normalizedLaplacian_symmetric pcK3 pcK3_isSymm)
              pcK3_card = 4 := by
  refine ⟨?_, ?_⟩
  · simp only [pcK3_deg_eq_two, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    norm_num
  · have he : quadForm (laplacian pcK3) (![1, -1, 0] : Fin 3 → ℝ) = 6 := by
      rw [pcK3_energy_identity_QA]
      norm_num
    rw [he, pcK3_secondEval_normalized_eq_QA]
    norm_num

/-! ## The disconnected fence fixture -/

/-- Two disjoint edges on `Fin 4`: the connectivity-failure fixture. -/
def pcDisc : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

theorem pcDisc_card : 2 ≤ Fintype.card (Fin 4) := by decide

theorem pcDisc_isSymm : pcDisc.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [pcDisc, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail]

theorem pcDisc_nonneg : ∀ i j, 0 ≤ pcDisc i j := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pcDisc, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail]

/-- On the support of the disconnected fixture's adjacency, both
component-indicator-family vectors agree — the two edges lie inside the
components. -/
theorem pcDisc_agree_QA {g : Fin 4 → ℝ} (h01 : g 0 = g 1) (h23 : g 2 = g 3)
    {i j : Fin 4} (h : pcDisc i j ≠ 0) : g i = g j := by
  fin_cases i <;> fin_cases j <;>
    simp_all [pcDisc, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Matrix.vecHead, Matrix.vecTail]

theorem pcDisc_energy_component_QA :
    quadForm (laplacian pcDisc) (![1, 1, 0, 0] : Fin 4 → ℝ) = 0 := by
  rw [laplacian_quadForm pcDisc pcDisc_isSymm]
  have hsum : (∑ i, ∑ j, pcDisc i j
      * ((![1, 1, 0, 0] : Fin 4 → ℝ) i - (![1, 1, 0, 0] : Fin 4 → ℝ) j) ^ 2)
      = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h : pcDisc i j = 0
    · rw [h, zero_mul]
    · rw [pcDisc_agree_QA (g := (![1, 1, 0, 0] : Fin 4 → ℝ)) rfl rfl h,
        sub_self, zero_pow two_ne_zero, mul_zero]
  rw [hsum, zero_div]

/-- The component indicator's variance on the disconnected fixture is
exactly `1` — nonzero while its energy is exactly zero. -/
theorem pcDisc_variance_component_QA :
    (∑ i : Fin 4, ((![1, 1, 0, 0] : Fin 4 → ℝ) i
      - (∑ j, (![1, 1, 0, 0] : Fin 4 → ℝ) j)
        / (Fintype.card (Fin 4) : ℝ)) ^ 2) = 1 := by
  simp only [Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, Fintype.card_fin]
  norm_num

/-- The disconnected fixture's spectral gap is not positive (the
component indicator's centered self is a null-energy test vector). -/
theorem pcDisc_secondEval_nonpos_QA :
    secondEval (laplacian pcDisc) (laplacian_symmetric pcDisc pcDisc_isSymm) pcDisc_card ≤ 0 := by
  have hx0 : (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) 3 = 0 :=
      congrFun h 3
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.vecTail, Matrix.vecHead] at h0
  have hxorth :
      Matrix.dotProduct (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ)
        onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Matrix.vecTail, Matrix.vecHead]
    norm_num
  have he : quadForm (laplacian pcDisc)
      (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) = 0 := by
    rw [laplacian_quadForm pcDisc pcDisc_isSymm]
    have hsumc : (∑ i, ∑ j, pcDisc i j
        * ((![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) i
            - (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ) j) ^ 2)
        = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h : pcDisc i j = 0
      · rw [h, zero_mul]
      · rw [pcDisc_agree_QA
            (g := (![1 / 2, 1 / 2, -1 / 2, -1 / 2] : Fin 4 → ℝ))
            rfl rfl h, sub_self, zero_pow two_ne_zero, mul_zero]
    rw [hsumc, zero_div]
  have h := secondEval_le_rayleigh (laplacian_symmetric pcDisc pcDisc_isSymm)
    (laplacian_psd pcDisc pcDisc_isSymm pcDisc_nonneg)
    (laplacian_ones_in_kernel pcDisc) pcDisc_card hx0 hxorth
  rw [rayleigh, if_neg hx0, he, zero_div] at h
  exact h

/-- **The no-constant connectivity fence**: on the disconnected fixture
there is *no* finite constant `c` making any Poincaré-shaped inequality
`variance ≤ c · energy` true — the component indicator has variance
exactly `1` and energy exactly `0`. The `0 < λ₂` hypothesis (derivable
from connectivity) is exactly the boundary of the true region, not a
convenience. -/
theorem pcDisc_no_poincare_constant_QA :
    ¬ ∃ c : ℝ, ∀ f : Fin 4 → ℝ,
      (∑ i, (f i - (∑ j, f j) / (Fintype.card (Fin 4) : ℝ)) ^ 2)
        ≤ c * quadForm (laplacian pcDisc) f := by
  rintro ⟨c, hc⟩
  have h := hc (![1, 1, 0, 0] : Fin 4 → ℝ)
  rw [pcDisc_energy_component_QA, mul_zero] at h
  have hvar := pcDisc_variance_component_QA
  linarith

/-! ## The edge-expansion instances -/

/-- **The `K₂` edge-expansion pin**: at the singleton cut the bound
computes to exactly the boundary (`1 = 1`) — attained with equality. -/
theorem pcEdge_edge_expansion_instance_QA :
    secondEval (laplacian pcEdge)
        (laplacian_symmetric pcEdge pcEdge_isSymm) pcEdge_card
      * (({0} : Finset (Fin 2)).card : ℝ)
      * ((Fintype.card (Fin 2) : ℝ)
          - (({0} : Finset (Fin 2)).card : ℝ))
      / (Fintype.card (Fin 2) : ℝ)
      ≤ boundary pcEdge ({0} : Finset (Fin 2)) :=
  spectral_gap_edge_expansion pcEdge pcEdge_isSymm pcEdge_nonneg
    pcEdge_card {0}

theorem pcEdge_edge_expansion_attained_QA :
    boundary pcEdge ({0} : Finset (Fin 2)) = 1
      ∧ secondEval (laplacian pcEdge)
            (laplacian_symmetric pcEdge pcEdge_isSymm) pcEdge_card
          * (({0} : Finset (Fin 2)).card : ℝ)
          * ((Fintype.card (Fin 2) : ℝ)
              - (({0} : Finset (Fin 2)).card : ℝ))
          / (Fintype.card (Fin 2) : ℝ) = 1 := by
  refine ⟨?_, ?_⟩
  · simp [boundary, pcEdge,
      show ({0} : Finset (Fin 2))ᶜ = {1} by decide, Finset.sum_singleton]
  · rw [pcEdge_secondEval_eq_two_QA]
    norm_num
/-- **The `K₃` edge-expansion pin**: at the singleton cut the bound
computes to exactly the boundary (`2 = 2`, gap `3`, `s(n−s)/n = 2/3`)
— attained with equality. -/
theorem pcK3_edge_expansion_instance_QA :
    secondEval (laplacian pcK3)
        (laplacian_symmetric pcK3 pcK3_isSymm) pcK3_card
      * (({0} : Finset (Fin 3)).card : ℝ)
      * ((Fintype.card (Fin 3) : ℝ)
          - (({0} : Finset (Fin 3)).card : ℝ))
      / (Fintype.card (Fin 3) : ℝ)
      ≤ boundary pcK3 ({0} : Finset (Fin 3)) :=
  spectral_gap_edge_expansion pcK3 pcK3_isSymm pcK3_nonneg
    pcK3_card {0}

theorem pcK3_edge_expansion_attained_QA :
    boundary pcK3 ({0} : Finset (Fin 3)) = 2
      ∧ secondEval (laplacian pcK3)
            (laplacian_symmetric pcK3 pcK3_isSymm) pcK3_card
          * (({0} : Finset (Fin 3)).card : ℝ)
          * ((Fintype.card (Fin 3) : ℝ)
              - (({0} : Finset (Fin 3)).card : ℝ))
          / (Fintype.card (Fin 3) : ℝ) = 2 := by
  refine ⟨?_, ?_⟩
  · have hcompl : ({0} : Finset (Fin 3))ᶜ = {1, 2} := by decide
    have hb : boundary pcK3 ({0} : Finset (Fin 3)) = pcK3 0 1 + pcK3 0 2 := by
      simp only [boundary, hcompl, Finset.sum_singleton, Finset.sum_insert,
        Finset.sum_empty]
      simp
    rw [hb, pcK3_apply, pcK3_apply]
    have e1 : ¬((0 : Fin 3) = 2) := by decide
    simp only [if_neg e1]
    norm_num
  · rw [pcK3_secondEval_eq_three_QA]
    norm_num


end SpectralGraphTheory
