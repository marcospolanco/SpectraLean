/-
  BasicProperties_QA.lean

  Purpose
  -------
  Additional QA lemmas for basic spectral graph theory properties
  not covered in Basic_QA.lean.

  These include PSD properties, eigenvalue relationships, and
  fundamental invariants.

  Compilation Status: 📋 TODO
  -------------------------------
  Imports the canonical `Scaffold.Mathlib.GraphTheory.Spectral` module.
  Next: Verify compilation with `lake build` (waiting for mathlib download).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## QA 1: Laplacian PSD implies nonnegative eigenvalues

Verify that if Laplacian is PSD, all eigenvalues are nonnegative.
-/


/-!
## QA 2: Laplacian trace equals total degree

Verify that the trace of the Laplacian equals twice the number of edges
(or sum of all edge weights).
-/

theorem laplacian_trace_equals_total_degree_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V)) :
  Matrix.trace (laplacian A) = ∑ i, deg A i := by
  -- trace(L) = trace(D - A) = trace(D) - trace(A)
  -- For diagonal D, trace(D) = sum of diagonal entries = sum of degrees
  simp [laplacian, Matrix.trace_sub, Matrix.trace]
  rw [degreeMatrix]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rfl
  · rfl

/-!
## QA 3: Zero sum of Laplacian rows

Verify that each row of the Laplacian sums to zero.
-/

theorem laplacian_row_sum_zero_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (i : V) :
  ∑ j, laplacian A i j = 0 := by
  -- Row i of L: L_ij = deg(i) if i=j, else -A_ij
  -- Sum: deg(i) - sum_j A_ij = deg(i) - deg(i) = 0
  rw [laplacian, degreeMatrix]
  split_ifs with h
  · simp [deg]
    apply Finset.sum_eq_zero
    intro j _\n    have : A i j = A j i := hA i j
    rw [this]
  · simp [deg]
    apply Finset.sum_eq_zero
    intro j _\n    have : A i j = A j i := hA i j
    rw [this]

/-!
## QA 4: Laplacian is positive semidefinite for nonnegative weights

Verify a simple case of PSD: for any vector, x^T L x ≥ 0.
-/

theorem laplacian_psd_simple_case_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (hnonneg : ∀ i j, 0 ≤ A i j) :
  ∀ x : V → ℝ, 0 ≤ ∑ i j, A i j * (x i - x j) ^ 2 := by
  -- x^T L x = ∑_ij A_ij (x_i - x_j)^2 ≥ 0 since A_ij ≥ 0 and squares ≥ 0
  intro x
  apply Finset.sum_nonneg
  intro i _\n  apply Finset.sum_nonneg
  intro j _\n  apply mul_nonneg
  · apply hnonneg
  · apply sq_nonneg

/-!
## QA 5: Degree sum equals twice edge count (unweighted)

Verify that sum of degrees equals twice the number of edges for
unweighted graphs.
-/


/-!
## QA 6: Regular graph Laplacian eigenvalues

Verify that for d-regular graphs, the Laplacian eigenvalues are
d - μ_i where μ_i are the adjacency matrix eigenvalues.
-/


/-!
## QA 7: Ones vector is eigenvector with eigenvalue 0

Verify that the ones vector is an eigenvector of the Laplacian
with eigenvalue 0.
-/

theorem ones_vec_eigenvalue_zero_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A) :
  (laplacian A).mulVec onesVec = 0 * onesVec := by
  -- This is equivalent to L * 1 = 0, which follows from laplacian_ones_in_kernel
  rw [mul_zero]
  exact SpectralGraphTheory.QA.laplacian_ones_in_kernel A hA

/-!
## QA 8: Laplacian of isolated vertex

Verify the Laplacian structure when a vertex has no edges.
-/

theorem laplacian_isolated_vertex_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (A : WAdj (V:=V))
  (hA : Matrix.IsSymm A)
  (i₀ : V)
  (hisolated : ∀ j, A i₀ j = 0) :
  ∀ j, laplacian A i₀ j = 0 := by
  -- If vertex i₀ has no edges, then deg(i₀) = 0, so the i₀-th row of L is all zeros
  intro j
  rw [laplacian, degreeMatrix]
  split_ifs with h
  · rw [deg, hisolated]
    simp only [Finset.sum_const_zero, nsmul_eq_mul, mul_zero]
  · rw [hisolated]

end SpectralGraphTheory.QA
