/-
  Interlacing_QA.lean

  Purpose
  -------
  QA lemmas for eigenvalue interlacing and perturbation theorems.

  These verify basic structural properties that should hold for
  eigenvalue perturbations and interlacing inequalities.

  Compilation Status: ⏳ NOT YET VERIFIED
  ----------------------------------------
  Created: 2025-02-10
  Next: Verify compilation with `lake build` (waiting for mathlib download).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## QA 1: Principal submatrix preserves symmetry

Verify that taking a principal submatrix of a symmetric matrix
produces a symmetric matrix. This is a basic sanity check for
interlacing theorems.
-/

theorem principal_submatrix_preserves_symmetry_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (M : Matrix V V ℝ)
  (hM : Matrix.IsSymm M)
  (S : Finset V) :
  Matrix.IsSymm (fun (i j : ↥S) => M i j) := by
  -- Real proof: Symmetry is preserved when restricting to any subset
  intro i j
  simp only [Matrix.IsSymm, Subtype.coe_mk]
  exact hM i j

/-!
## QA 2: Principal submatrix preserves PSD

Verify that taking a principal submatrix of a PSD matrix
produces a PSD matrix. This is a basic sanity check for
interlacing theorems applied to Laplacians.
-/


/-!
## QA 2: Perturbation matrix is symmetric for symmetric perturbations

Verify that if two symmetric matrices are perturbed, their
difference is also symmetric. This is basic for perturbation bounds.
-/

theorem symmetric_difference_is_symmetric_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (M N : Matrix V V ℝ)
  (hM : Matrix.IsSymm M)
  (hN : Matrix.IsSymm N) :
  Matrix.IsSymm (M - N) := by
  -- Real proof: Difference of symmetric matrices is symmetric
  intro i j
  simp only [Matrix.IsSymm, Matrix.sub_apply]
  rw [hM, hN]

/-!
## QA 3: Zero perturbation has zero norm

Verify that if the perturbation is zero, its operator norm is zero.
This is a basic sanity check for perturbation theorems.
-/

theorem zero_perturbation_zero_norm_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (M : Matrix V V ℝ) :
  ‖M - M‖ = 0 := by
  -- Real proof: Any norm satisfies ‖x - x‖ = 0
  simp only [Matrix.sub_self, norm_zero]

/-!
## QA 4: Norm satisfies triangle inequality

Verify that the operator norm satisfies the triangle inequality.
This is a basic sanity check for perturbation bounds.
-/

theorem norm_triangle_inequality_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (M N P : Matrix V V ℝ) :
  ‖M - P‖ ≤ ‖M - N‖ + ‖N - P‖ := by
  -- Real proof: This follows from the triangle inequality for the operator norm
  -- ‖M - P‖ = ‖(M - N) + (N - P)‖ ≤ ‖M - N‖ + ‖N - P‖
  have h : M - P = (M - N) + (N - P) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    abel
  rw [h]
  exact norm_add_le (M - N) (N - P)

end SpectralGraphTheory.QA
