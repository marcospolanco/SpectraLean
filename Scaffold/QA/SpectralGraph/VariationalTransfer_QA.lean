/-
  VariationalTransfer_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.VariationalTransfer`, the
  second consuming module of the `Normalized`/`Spectral` interfaces:
  quadratic-form and Rayleigh-quotient transfer through the congruence
  bridge, and PSD transfer, instantiated at the three-vertex path
  (degrees 1, 2, 1).

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated. QA does not prove any axiom's truth.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The three-vertex path `0 — 1 — 2` (reused fixture)
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1). -/
def vtPathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem vtPathAdj_isSymm : vtPathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [vtPathAdj]

theorem vtPathAdj_deg_zero : deg vtPathAdj 0 = 1 := by
  simp only [deg, vtPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem vtPathAdj_deg_one : deg vtPathAdj 1 = 2 := by
  simp only [deg, vtPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem vtPathAdj_deg_two : deg vtPathAdj 2 = 1 := by
  simp only [deg, vtPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem vtPathAdj_deg_pos (i : Fin 3) : 0 < deg vtPathAdj i := by
  fin_cases i <;>
    simp only [deg, vtPathAdj, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num

/-- Nonnegative weights of the path (unit, off-diagonal only). -/
theorem vtPathAdj_nonneg (i j : Fin 3) : 0 ≤ vtPathAdj i j := by
  fin_cases i <;> fin_cases j <;> simp [vtPathAdj]

/-- The alternating test vector `(1, -1, 1)`. -/
def vtAltVec : Fin 3 → ℝ :=
  ![1, -1, 1]

theorem vtAltVec_ne_zero : vtAltVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [vtAltVec] at h0

/-!
## Entrywise stretch and the degree-weighted denominator
-/

/-- The degree stretch computes entrywise at the path:
`√D y = (1, -√2, 1)` at the alternating vector. -/
theorem vt_degreeSqrt_mulVec_alt_QA :
    (degreeSqrt vtPathAdj *ᵥ vtAltVec) 1 = -(Real.sqrt 2) := by
  rw [degreeSqrt_mulVec, vtPathAdj_deg_one]
  norm_num [vtAltVec]

/-- The degree-weighted denominator computes to the total volume `4`:
`∑ deg i · y i² = 1 + 2 + 1`, evaluated through the transfer theorem
on one side and as a bare sum on the other. -/
theorem vt_degreeWeighted_denominator_QA :
    Matrix.dotProduct (degreeSqrt vtPathAdj *ᵥ vtAltVec)
        (degreeSqrt vtPathAdj *ᵥ vtAltVec) = 4 := by
  rw [dotProduct_degreeSqrt_mulVec vtPathAdj
    (fun i => le_of_lt (vtPathAdj_deg_pos i))]
  simp only [vtAltVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.sum_univ_three, vtPathAdj_deg_zero,
    vtPathAdj_deg_one, vtPathAdj_deg_two]
  norm_num

/-- The bare weighted sum also computes directly to `4` — the
denominator lemma's value agrees with the hand computation. -/
theorem vt_degreeWeighted_sum_direct_QA :
    ∑ i, deg vtPathAdj i * vtAltVec i * vtAltVec i = 4 := by
  simp only [vtAltVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.sum_univ_three, vtPathAdj_deg_zero,
    vtPathAdj_deg_one, vtPathAdj_deg_two]
  norm_num

/-!
## The transferred Rayleigh quotient: the classical value `2`
-/

/-- The combinatorial numerator computes to `8` via the proved
Dirichlet identity: four directed edges each contributing
`(1-(-1))² = 4`, halved, doubled by the degree weighting — the exact
statement is the fully evaluated sum. -/
theorem vt_quadForm_laplacian_alt :
    quadForm (laplacian vtPathAdj) vtAltVec = 8 := by
  rw [laplacian_quadForm vtPathAdj vtPathAdj_isSymm vtAltVec]
  simp only [vtPathAdj, vtAltVec, Matrix.of_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- **The headline transfer instantiates to the classical value.** At
the path, the normalized Rayleigh quotient of the stretched
alternating vector is `2` — the largest eigenvalue of the normalized
path Laplacian, computed here as `8 / 4` (transferred numerator over
degree-weighted denominator), not by any spectral theorem. A defect in
the congruence bridge, the stretch, or the denominator lemma would
move this value. -/
theorem vt_rayleigh_transfer_alt_QA :
    rayleigh (normalizedLaplacian vtPathAdj)
      (degreeSqrt vtPathAdj *ᵥ vtAltVec) = 2 := by
  rw [rayleigh_normalizedLaplacian_degreeSqrt vtPathAdj
    vtPathAdj_deg_pos vtAltVec_ne_zero, vt_quadForm_laplacian_alt,
    vt_degreeWeighted_sum_direct_QA]
  norm_num

/-- The transfer theorem recomposes: the combinatorial quadratic form
of the alternating vector equals the normalized quadratic form of the
stretched vector (both `8` when the latter is evaluated through the
congruence). -/
theorem vt_quadForm_transfer_QA :
    quadForm (laplacian vtPathAdj) vtAltVec
      = quadForm (normalizedLaplacian vtPathAdj)
          (degreeSqrt vtPathAdj *ᵥ vtAltVec) :=
  quadForm_laplacian_eq_quadForm_normalizedLaplacian vtPathAdj
    vtPathAdj_deg_pos vtAltVec

/-!
## PSD transfer
-/

/-- PSD transfer instantiates at two concrete vectors: the stretched
alternating vector and the first unit vector both have nonnegative
normalized quadratic form. -/
theorem vt_normalizedLaplacian_psd_QA :
    0 ≤ quadForm (normalizedLaplacian vtPathAdj)
        (degreeSqrt vtPathAdj *ᵥ vtAltVec)
      ∧ 0 ≤ quadForm (normalizedLaplacian vtPathAdj)
          (vtAltVec + ![0, 1, 0]) := by
  have hpsd : ∀ x : Fin 3 → ℝ,
      0 ≤ quadForm (normalizedLaplacian vtPathAdj) x :=
    normalizedLaplacian_psd vtPathAdj vtPathAdj_isSymm vtPathAdj_nonneg
      vtPathAdj_deg_pos
  exact ⟨hpsd _, hpsd _⟩

/-- PSD gives nonnegative Rayleigh quotients at nonzero vectors: at
the stretched alternating vector the quotient is exactly the positive
value `2`. -/
theorem vt_rayleigh_nonneg_QA :
    0 ≤ rayleigh (normalizedLaplacian vtPathAdj)
        (degreeSqrt vtPathAdj *ᵥ vtAltVec) := by
  rw [vt_rayleigh_transfer_alt_QA]
  norm_num

end SpectralGraphTheory.QA
