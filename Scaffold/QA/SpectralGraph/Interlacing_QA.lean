/-
  Interlacing_QA.lean

  Purpose
  -------
  QA lemmas for the interlacing interface of
  `Scaffold.Mathlib.GraphTheory.Spectral`: principal submatrix
  extraction and symmetry, and perturbation-matrix structure in the
  ℓ² operator norm.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Principal submatrices
-/

/-- Entries of the principal submatrix are entries of the ambient
matrix. -/
theorem principal_submatrix_entries_QA (M : Matrix V V ℝ)
    (S : Finset V) (a b : ↥S) :
    M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V)) a b
      = M (a : V) (b : V) := by
  rfl

/-- The principal submatrix of a symmetric matrix is symmetric. -/
theorem principal_submatrix_preserves_symmetry_QA (M : Matrix V V ℝ)
    (hM : M.IsSymm) (S : Finset V) :
    (M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V))).IsSymm :=
  principalSubmatrix_symmetric M hM S

/-!
## Perturbation structure
-/

/-- The difference of symmetric matrices is symmetric. -/
theorem symmetric_difference_is_symmetric_QA (M N : Matrix V V ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm) :
    (M - N).IsSymm :=
  hM.sub hN

/-- Zero perturbation has zero operator norm. -/
theorem zero_perturbation_zero_norm_QA (M : Matrix V V ℝ) :
    ‖M - M‖ = 0 := by
  rw [sub_self, norm_zero]

/-- The operator norm satisfies the triangle inequality. -/
theorem norm_triangle_QA (M N P : Matrix V V ℝ) :
    ‖M - P‖ ≤ ‖M - N‖ + ‖N - P‖ := by
  have h : M - P = (M - N) + (N - P) := by
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [h]
  exact norm_add_le _ _

end SpectralGraphTheory.QA
