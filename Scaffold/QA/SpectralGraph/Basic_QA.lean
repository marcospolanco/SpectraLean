/-
  Basic_QA.lean

  Purpose
  -------
  QA lemmas for basic spectral graph theory definitions and properties.

  These are simple sanity checks that verify our axioms were stated correctly.
  Each lemma proves a well-known consequence that should follow immediately
  from the definitions and axioms.

  Compilation Status: 📋 TODO
  -------------------------------
  Imports the canonical `Scaffold.Mathlib.GraphTheory.Spectral` module.
  Next: Verify compilation with `lake build` (waiting for mathlib download).

  Notes
  -----
  - All proofs here are real Lean proofs (not `sorry`)
  - If any of these fail, it indicates a problem with the axiom formulation
  - These document the intended meaning of the basic spectral graph theory API

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## QA 1: Degree matrix is diagonal

Verify that the degree matrix definition actually produces a diagonal matrix.
-/

theorem degreeMatrix_is_diagonal
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V)) (i j : V) :
  i ≠ j → degreeMatrix A i j = 0 := by
  -- Real proof from definition
  rw [degreeMatrix]
  split_ifs
  · contradiction
  · rfl

/-!
## QA 2: Degree matrix diagonal entries are nonnegative

Verify that diagonal entries (degrees) are nonnegative for nonnegative weights.
-/

theorem degreeMatrix_diagonal_nonneg
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hnonneg : ∀ i j, 0 ≤ A i j)
  (i : V) :
  0 ≤ degreeMatrix A i i := by
  -- Real proof from definition
  rw [degreeMatrix]
  split_ifs
  · simp only [deg, hnonneg]
    apply Finset.sum_nonneg
    intro j _
    apply hnonneg
  · rfl

/-!
## QA 3: Laplacian preserves symmetry

Verify that Laplacian of a symmetric adjacency matrix is symmetric.
-/

theorem laplacian_preserves_symmetry
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A) :
  Matrix.IsSymm (laplacian A) := by
  -- Real proof: D is diagonal (hence symmetric), A is symmetric
  have hD : Matrix.IsSymm (degreeMatrix A) := by
    constructor
    intro i j
    by_cases h : i = j
    · simp [h, degreeMatrix]
    · simp [degreeMatrix, h]
  simpa [laplacian] using hD.sub hA

/-!
## QA 4: Ones vector in Laplacian kernel

Verify that the all-ones vector is in the kernel of the Laplacian.
This is a fundamental property that must hold.
-/

theorem laplacian_ones_in_kernel
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A) :
  (laplacian A).mulVec onesVec = 0 := by
  ext i
  simp only [laplacian, onesVec, Matrix.mulVec, Matrix.sub_mul,
    degreeMatrix, Pi.mul_apply, Pi.sub_apply, deg]
  split_ifs with h
  · simp only [Pi.one_apply, mul_one, nsmul_eq_mul, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have : (∑ j, A i j) = (∑ j, A j i) := by
      apply Finset.sum_congr rfl
      intro j _
      exact hA i j
    simp [this]
  · rfl

/-!
## QA 5: Event update preserves symmetry

Verify that event updates preserve the symmetry of adjacency matrices.
This is critical for event-driven dynamics.
-/

theorem eventUpdate_preserves_symmetry
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (u v : V) (w : ℝ) :
  Matrix.IsSymm (eventUpdate A u v w) := by
  intro i j
  rw [Matrix.IsSymm, eventUpdate]
  by_cases h1 : i = u ∧ j = v
  · simp [h1, hA]
  by_cases h2 : i = v ∧ j = u
  · simp [h2, hA]
  by_cases h3 : i = u ∧ j = u
  · simp [h3, hA]
  by_cases h4 : i = v ∧ j = v
  · simp [h4, hA]
  by_cases h5 : i = u
  · simp [h5]
  by_cases h6 : i = v
  · simp [h6]
  by_cases h7 : j = u
  · simp [h7]
  by_cases h8 : j = v
  · simp [h8]
  simp [hA]

/-!
## QA 6: Volume is additive for disjoint sets

Verify that volume behaves additively on disjoint finite sets.
-/

theorem vol_add_disjoint
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (S T : Finset V)
  (hdisj : Disjoint S T) :
  vol A (S ∪ T) = vol A S + vol A T := by
  -- Real proof from definition of vol and Finset properties
  rw [vol, vol, vol]
  apply Finset.sum_union
  exact hdisj

/-!
## QA 7: Boundary is symmetric

Verify that boundary(S) = boundary(Sᶜ).
-/

theorem boundary_complement_symmetry
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (S : Finset V) :
  boundary A S = boundary A Sᶜ := by
  -- Real proof using symmetry of adjacency matrix
  rw [boundary, boundary]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact hA i j

/-!
## QA 8: Cheeger constant is nonnegative

Verify that Cheeger constant is always nonnegative for any graph.
-/

theorem cheegerConstant_nonneg
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnonneg : ∀ i j, 0 ≤ A i j) :
  0 ≤ cheegerConstant A := by
  -- Cheeger constant is inf of conductance values, which are all nonnegative
  unfold cheegerConstant
  apply le_inf_i18n
  intro S
  rw [conductance]
  apply div_nonneg
  · exact boundary_nonneg A hnonneg S
  · apply Real.max_nonneg
    · exact vol_nonneg A hnonneg S
    · exact vol_nonneg A hnonneg Sᶜ

/-!
## QA 9: Volume is nonnegative

Verify that volume of any vertex set is nonnegative for nonnegative weights.
-/

theorem vol_nonneg
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hnonneg : ∀ i j, 0 ≤ A i j)
  (S : Finset V) :
  0 ≤ vol A S := by
  -- Real proof from definition of vol and nonnegativity
  rw [vol]
  apply Finset.sum_nonneg
  intro i _
  apply hnonneg

/-!
## QA 10: Boundary is nonnegative

Verify that edge boundary is nonnegative for nonnegative weights.
-/

theorem boundary_nonneg
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hnonneg : ∀ i j, 0 ≤ A i j)
  (S : Finset V) :
  0 ≤ boundary A S := by
  -- Real proof from definition of boundary and nonnegativity
  rw [boundary]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply hnonneg

/-!
## QA 11: Conductance is nonnegative

Verify that conductance is always nonnegative.
-/

theorem conductance_nonneg
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnonneg : ∀ i j, 0 ≤ A i j)
  (S : Finset V) :
  0 ≤ conductance A S := by
  rw [conductance]
  apply div_nonneg
  · exact boundary_nonneg A hnonneg S
  · apply Real.max_nonneg
    · exact vol_nonneg A hnonneg S
    · exact vol_nonneg A hnonneg Sᶜ

/-!
## QA 12: quadForm of zero vector is zero

Verify that quadForm M 0 = 0.
-/

theorem quadForm_zero_vector
  {V : Type} [Fintype V] [DecidableEq V]
  (M : Matrix V V ℝ) :
  quadForm M 0 = 0 := by
  rw [quadForm]
  simp

end SpectralGraphTheory.QA
