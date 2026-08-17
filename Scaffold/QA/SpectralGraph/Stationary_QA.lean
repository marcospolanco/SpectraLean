/-
  Stationary_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Stationary`: the
  stationary/kernel structure of the walk and normalized Laplacians,
  instantiated at the concrete three-vertex path (degrees 1, 2, 1) and
  with one fully computed entry.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Stationary
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The three-vertex path `0 — 1 — 2` (reused fixture)
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

theorem pathAdj_deg_pos (i : Fin 3) : 0 < deg pathAdj i := by
  fin_cases i <;>
    simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num

/-!
## Kernel and stationarity
-/

/-- The normalized-Laplacian kernel theorem instantiated at the path:
`L_sym *ᵥ √deg = 0` with `√deg = (1, √2, 1)`. -/
theorem path_normalized_kernel_QA :
    normalizedLaplacian pathAdj
      *ᵥ (fun i => Real.sqrt (deg pathAdj i)) = 0 :=
  normalizedLaplacian_mulVec_sqrtDeg_eq_zero pathAdj pathAdj_isSymm
    pathAdj_deg_pos

/-- The stationarity theorem instantiated at the path: the degree
vector `(1, 2, 1)` is stationary for the adjoint walk. -/
theorem path_walk_stationary_QA :
    (walkTransitionMatrix pathAdj)ᵀ *ᵥ (deg pathAdj) = deg pathAdj :=
  walkTransitionMatrix_transpose_mulVec_deg pathAdj pathAdj_isSymm
    pathAdj_deg_pos

/-- One kernel entry fully computed: `(L_sym *ᵥ √deg) 1 = 0` — the
center row contracts `√2` to itself through the two `1/√2` edges. -/
theorem path_normalized_kernel_entry_QA :
    (normalizedLaplacian pathAdj
      *ᵥ (fun i => Real.sqrt (deg pathAdj i))) 1 = 0 := by
  have h := normalizedLaplacian_mulVec_sqrtDeg_eq_zero pathAdj
    pathAdj_isSymm pathAdj_deg_pos
  rw [h]
  rfl

/-- Row sums in vector form instantiated at the path: the walk's
adjoint fixes the degree vector because `A *ᵥ 1 = deg` computes with
row sums `(1, 2, 1)`. -/
theorem path_mulVec_one_eq_deg_QA :
    pathAdj *ᵥ (fun _ => (1 : ℝ)) = deg pathAdj :=
  mulVec_one_eq_deg pathAdj

/-!
## Conservation of mass at both fixtures
-/

/-- Conservation of mass, irregular case: the walk Laplacian of the
path kills the constant vector. -/
theorem path_walkLaplacian_kernel_QA :
    walkLaplacian pathAdj *ᵥ (fun _ => (1 : ℝ)) = 0 :=
  walkLaplacian_mulVec_one_eq_zero pathAdj pathAdj_deg_pos

/-- The adjacency matrix of the single edge on `Fin 2` (symmetric,
1-regular). -/
def edgeAdj2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; 1, 0]

theorem edgeAdj2_deg (i : Fin 2) : deg edgeAdj2 i = 1 := by
  fin_cases i <;>
    simp only [deg, edgeAdj2, Matrix.of_apply, Fin.sum_univ_two] <;>
    norm_num

/-- Conservation of mass, regular case: the walk Laplacian of the edge
kills the constant vector — total probability is preserved by each step
of the walk. -/
theorem edge_randomWalkLaplacian_kernel_QA :
    randomWalkLaplacian edgeAdj2 1 *ᵥ (fun _ => (1 : ℝ)) = 0 :=
  randomWalkLaplacian_mulVec_one_eq_zero edgeAdj2 1 edgeAdj2_deg one_pos

end SpectralGraphTheory.QA
