/-
  RandomWalk_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.RandomWalk`: the transition
  matrix and walk Laplacian interfaces, instantiated at a concrete
  two-vertex graph (the edge `0 — 1`) where every quantity computes.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces at a point where the
  arithmetic is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.RandomWalk

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## A concrete two-vertex graph: the single edge `0 — 1`
-/

/-- The adjacency matrix of the single edge on `Fin 2` (symmetric,
1-regular, nonnegative). -/
def edgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem edgeAdj_isSymm : edgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [edgeAdj]

theorem edgeAdj_deg (i : Fin 2) : deg edgeAdj i = 1 := by
  fin_cases i <;>
    simp only [deg, edgeAdj, Matrix.of_apply, Fin.sum_univ_two] <;>
    simp

/-- Row-stochasticity computes at the edge: both rows of the transition
  matrix are the distribution placing all mass on the neighbor. -/
theorem edge_row_sum_QA (i : Fin 2) :
    ∑ j, transitionMatrix edgeAdj 1 i j = 1 :=
  transitionMatrix_row_sum edgeAdj 1 edgeAdj_deg one_pos i

/-- The transition matrix of the edge computes entrywise: it is the
  anti-diagonal (swapping) matrix. -/
theorem edge_transitionMatrix_entries_QA :
    transitionMatrix edgeAdj 1
      = Matrix.of fun (i j : Fin 2) => if i = j then 0 else 1 := by
  simp only [transitionMatrix, inv_one, one_smul, edgeAdj]

/-- The scaling bridge computes at the edge: the walk Laplacian is the
  combinatorial Laplacian itself (degree `d = 1`). -/
theorem edge_randomWalkLaplacian_eq_laplacian_QA :
    randomWalkLaplacian edgeAdj 1 = laplacian edgeAdj := by
  rw [randomWalkLaplacian_eq_smul_laplacian edgeAdj 1 edgeAdj_deg one_pos,
    inv_one, one_smul]

/-- Interop with the Cheeger bridge computes at the edge: the walk
  Laplacian is the normalized Laplacian used by the Cheeger axioms. -/
theorem edge_randomWalkLaplacian_eq_normalized_QA :
    randomWalkLaplacian edgeAdj 1 = regularNormalizedLaplacian edgeAdj 1 :=
  randomWalkLaplacian_eq_regularNormalizedLaplacian edgeAdj 1

/-- The combinatorial Laplacian of the edge computes: it is `1 - A`, the
  standard two-vertex Laplacian with eigenvalues `0` and `2`. -/
theorem edge_laplacian_entries_QA :
    laplacian edgeAdj
      = Matrix.of fun (i j : Fin 2) => if i = j then 1 else -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, edgeAdj, deg]

end SpectralGraphTheory.QA
