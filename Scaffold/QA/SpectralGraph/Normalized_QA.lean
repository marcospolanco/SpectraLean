/-
  Normalized_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Normalized`: the general
  (irregular) normalized Laplacian and its diagonal square-root
  scaffolding, instantiated at a concrete three-vertex path graph — a
  genuinely irregular graph with degrees (1, 2, 1) — and at the regular
  two-vertex edge.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  (including the symbolic `√2` entries) is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Normalized
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## A concrete irregular graph: the three-vertex path `0 — 1 — 2`
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1). -/
def pathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem pathAdj_isSymm : pathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [pathAdj]

theorem pathAdj_deg_zero : deg pathAdj 0 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_one : deg pathAdj 1 = 2 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_two : deg pathAdj 2 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

/-- All degrees of the path are positive: the interface hypothesis of
the normalized-Laplacian theorems holds. Computed directly per vertex. -/
theorem pathAdj_deg_pos (i : Fin 3) : 0 < deg pathAdj i := by
  fin_cases i <;>
    simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num

/-- Normalized-Laplacian diagonal of the path: the center entry is `1`
(the path has no self-loops, so the diagonal of `L_sym` is `1 - 0`). -/
theorem path_normalizedLaplacian_diag_QA :
    normalizedLaplacian pathAdj 1 1 = 1 := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    degreeInvSqrt, pathAdj, Real.sqrt_one, inv_one, one_mul,
    Matrix.of_apply, Fin.isValue]
  norm_num

/-- Normalized-Laplacian adjacent entry: `(L_sym) 0 1 = -1/√2` — the
degree-2 center scales the edge by `1/√(1·2)`. -/
theorem path_normalizedLaplacian_offdiag_QA :
    normalizedLaplacian pathAdj 0 1 = -(Real.sqrt 2)⁻¹ := by
  have hp01 : pathAdj 0 1 = 1 := by norm_num [pathAdj]
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    degreeInvSqrt, Real.sqrt_one, inv_one, one_mul, zero_sub,
    pathAdj_deg_zero, pathAdj_deg_one]
  rw [hp01]
  norm_num

/-- Normalized-Laplacian non-adjacent entry: `(L_sym) 0 2 = 0`. -/
theorem path_normalizedLaplacian_far_QA :
    normalizedLaplacian pathAdj 0 2 = 0 := by
  have hp02 : pathAdj 0 2 = 0 := by norm_num [pathAdj]
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    degreeInvSqrt, Real.sqrt_one, inv_one, one_mul,
    pathAdj_deg_zero, pathAdj_deg_two]
  rw [hp02]
  have hne : ¬(0 : ℕ) = 2 := by decide
  simp [hne]

/-- The congruence bridge computes at the path: the `(0,1)` entry of
`√D L_sym √D` is `-1`, the combinatorial-Laplacian entry — the square
roots cancel. -/
theorem path_congruence_entry_QA :
    (degreeSqrt pathAdj * normalizedLaplacian pathAdj
      * degreeSqrt pathAdj) 0 1 = -1 := by
  have h := congrFun (congrFun
    (degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt pathAdj
      pathAdj_deg_pos) 0) 1
  have hval : laplacian pathAdj 0 1 = -1 := by
    simp only [laplacian, degreeMatrix, Matrix.sub_apply, pathAdj,
      Matrix.of_apply, Fin.isValue, pathAdj_deg_zero]
    norm_num
  rw [hval] at h
  exact h

/-!
## Agreement with the regular cone at the two-vertex edge
-/

/-- The adjacency matrix of the single edge on `Fin 2` (symmetric,
1-regular). -/
def edgeAdj2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; 1, 0]

theorem edgeAdj2_deg (i : Fin 2) : deg edgeAdj2 i = 1 := by
  fin_cases i <;>
    simp only [deg, edgeAdj2, Matrix.of_apply, Fin.sum_univ_two] <;>
    norm_num

/-- On the regular edge, the general normalized Laplacian agrees with
the Cheeger-bridge `regularNormalizedLaplacian` — the two normalizations
coincide on the regular cone. -/
theorem edge_normalized_agrees_regular_QA :
    normalizedLaplacian edgeAdj2 = regularNormalizedLaplacian edgeAdj2 1 :=
  normalizedLaplacian_eq_regularNormalizedLaplacian edgeAdj2 1
    edgeAdj2_deg one_pos

/-!
## The walk form at the path
-/

/-- Every row of the walk transition matrix of the path sums to one:
row-stochasticity on a genuinely irregular graph. -/
theorem path_walk_row_sum_QA (i : Fin 3) :
    ∑ j, walkTransitionMatrix pathAdj i j = 1 :=
  walkTransitionMatrix_row_sum pathAdj pathAdj_deg_pos i

/-- Walk entries of the path compute: the center row places `1/2` on
each neighbor (`P 1 0 = 1/2`), the leaf rows place all mass on the
center (`P 0 1 = 1`). -/
theorem path_walk_entries_QA :
    walkTransitionMatrix pathAdj 1 0 = 1 / 2
      ∧ walkTransitionMatrix pathAdj 0 1 = 1 := by
  have h10 : pathAdj 1 0 = 1 := by norm_num [pathAdj]
  have h01 : pathAdj 0 1 = 1 := by norm_num [pathAdj]
  constructor
  · simp only [walkTransitionMatrix, Matrix.diagonal_mul, pathAdj_deg_one]
    rw [h10]
    norm_num
  · simp only [walkTransitionMatrix, Matrix.diagonal_mul, pathAdj_deg_zero]
    rw [h01]
    norm_num

/-- The similarity identity instantiated and checked entrywise at the
path: the `(1,2)` entry of `√D · L_walk · (1/√D)` equals the `(1,2)`
entry of `L_sym`, both `-1/√2` — the walk form is similar to the
symmetric normalized Laplacian. -/
theorem path_similarity_entry_QA :
    (degreeSqrt pathAdj * walkLaplacian pathAdj * degreeInvSqrt pathAdj) 1 2
      = normalizedLaplacian pathAdj 1 2 :=
  congrFun (congrFun
    (degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt pathAdj pathAdj_deg_pos)
    1) 2

end SpectralGraphTheory.QA
