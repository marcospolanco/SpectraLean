/-
  Basic_QA.lean

  Purpose
  -------
  QA lemmas for the basic spectral graph theory definitions of
  `Scaffold.Mathlib.GraphTheory.Spectral`: degree matrix, Laplacian,
  quadratic form, cuts and volumes, and event updates.

  All proofs are real Lean proofs (no `sorry`/`admit`). They check the
  public interface by deriving elementary consequences directly from the
  definitions; a failure indicates an API-shape defect.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Degree matrix
-/

/-- Off-diagonal entries of the degree matrix vanish. -/
theorem degreeMatrix_is_diagonal_QA (A : WAdj (V := V)) {i j : V} (h : i ≠ j) :
    degreeMatrix A i j = 0 := by
  simp [degreeMatrix, h]

/-- Diagonal entries of the degree matrix are the row sums. -/
theorem degreeMatrix_diagonal_QA (A : WAdj (V := V)) (i : V) :
    degreeMatrix A i i = ∑ j, A i j := by
  simp [degreeMatrix, deg]

/-!
## Laplacian
-/

/-- The Laplacian of a symmetric adjacency matrix is symmetric: exercises
the public `laplacian_symmetric` through the `IsSymm.sub` interface. -/
theorem laplacian_preserves_symmetry_QA (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) :
    Matrix.IsSymm (laplacian A) :=
  laplacian_symmetric A hA

/-- The all-ones vector is in the Laplacian kernel: direct row-sum
computation from the definitions. -/
theorem laplacian_ones_in_kernel_QA (A : WAdj (V := V)) :
    (laplacian A).mulVec onesVec = 0 := by
  funext i
  have hrow : ∑ j, degreeMatrix A i j = deg A i := by
    simp only [degreeMatrix, eq_comm]
    simp
  simp only [laplacian, Matrix.sub_apply, Matrix.mulVec, Matrix.dotProduct,
    onesVec, mul_one, Finset.sum_sub_distrib]
  rw [hrow, deg]
  simp

/-- Each Laplacian row sums to zero. -/
theorem laplacian_row_sum_zero_QA (A : WAdj (V := V)) (i : V) :
    ∑ j, laplacian A i j = 0 := by
  have hrow : ∑ j, degreeMatrix A i j = deg A i := by
    refine (Finset.sum_eq_single i ?_ ?_).trans ?_
    · intro j _ hj
      exact degreeMatrix_off_diagonal A (Ne.symm hj)
    · intro hi
      exact absurd (Finset.mem_univ i) hi
    · rw [degreeMatrix_diagonal]
  simp only [laplacian, Matrix.sub_apply, Finset.sum_sub_distrib, sub_eq_zero]
  rw [hrow, deg]

/-!
## Cuts, volumes, conductance
-/

/-- Volume is additive on disjoint vertex sets. -/
theorem vol_add_disjoint_QA (A : WAdj (V := V)) (S T : Finset V)
    (hdisj : Disjoint S T) :
    vol A (S ∪ T) = vol A S + vol A T := by
  simp only [vol]
  exact Finset.sum_union hdisj

/-- A set and its complement carry the total volume. -/
theorem vol_complement_QA (A : WAdj (V := V)) (S : Finset V) :
    vol A S + vol A Sᶜ = ∑ i, deg A i :=
  Finset.sum_add_sum_compl S (deg A)

/-- Conductance is nonnegative for nonnegative weights. -/
theorem conductance_nonneg_QA (A : WAdj (V := V))
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V) :
    0 ≤ conductance A S :=
  conductance_nonneg A hnonneg S

/-- The Cheeger constant is a lower bound for every nonempty proper
subset's conductance. -/
theorem cheegerConstant_le_conductance_QA (A : WAdj (V := V))
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    cheegerConstant A ≤ conductance A S :=
  conductance_ge_cheegerConstant A hnonneg S hS hSc

/-!
## Quadratic form
-/

/-- The quadratic form at the zero vector vanishes. -/
theorem quadForm_zero_QA (M : Matrix V V ℝ) :
    quadForm M 0 = 0 := by
  simp [quadForm, Matrix.dotProduct]

/-- The Rayleigh quotient has the documented junk value at zero. -/
theorem rayleigh_zero_QA (M : Matrix V V ℝ) :
    rayleigh M 0 = 0 := by
  simp [rayleigh]

/-!
## Event updates
-/

/-- An event update writes the new weight into the `(u, v)` entry. -/
theorem eventUpdate_entry_QA (A : WAdj (V := V)) (u v : V) (w : ℝ) :
    eventUpdate A u v w u v = w := by
  simp [eventUpdate]

/-- Event updates preserve symmetry. -/
theorem eventUpdate_preserves_symmetry_QA (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (u v : V) (w : ℝ) :
    Matrix.IsSymm (eventUpdate A u v w) :=
  eventUpdate_preserves_symmetry A hA u v w

/-- Repeating the same event is idempotent. -/
theorem eventUpdate_idempotent_QA (A : WAdj (V := V)) (u v : V) (w : ℝ) :
    eventUpdate (eventUpdate A u v w) u v w = eventUpdate A u v w := by
  ext i j
  simp only [eventUpdate]
  by_cases h : (i = u ∧ j = v) ∨ (i = v ∧ j = u)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

end SpectralGraphTheory.QA
