/-
  BasicProperties_QA.lean

  Purpose
  -------
  Additional QA lemmas for the SGT center: Laplacian trace, Dirichlet
  form, PSD, isolated vertices, and the kernel eigenvector statement.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Laplacian trace
-/

/-- Trace of the Laplacian equals the total degree, provided the
adjacency has no self-loops. (Without the no-self-loop hypothesis the
identity fails: `trace L = ∑ deg A i - ∑ A i i`. The hypothesis was
missing from an earlier draft of this QA and its absence is exactly the
kind of interface defect this file exists to catch.) -/
theorem laplacian_trace_equals_total_degree_QA (A : WAdj (V := V))
    (hnoLoop : ∀ i, A i i = 0) :
    Matrix.trace (laplacian A) = ∑ i, deg A i := by
  have hdiag : ∀ i, laplacian A i i = deg A i - A i i := by
    intro i
    rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal]
  simp only [Matrix.trace, Matrix.diag, Matrix.diag_apply, hdiag,
    Finset.sum_sub_distrib]
  rw [Finset.sum_eq_zero fun i _ => hnoLoop i, sub_zero]

/-!
## Dirichlet form and PSD
-/

/-- The Dirichlet form identity: the Laplacian quadratic form is half the
weighted sum of squared vertex differences (public theorem). -/
theorem laplacian_quadForm_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (x : V → ℝ) :
    quadForm (laplacian A) x = (∑ i, ∑ j, A i j * (x i - x j) ^ 2) / 2 :=
  laplacian_quadForm A hA x

/-- Positive semidefiniteness, derived through the Dirichlet form: every
summand of the Dirichlet sum is nonnegative for nonnegative weights. -/
theorem laplacian_psd_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (x : V → ℝ) :
    0 ≤ quadForm (laplacian A) x := by
  rw [laplacian_quadForm A hA x]
  exact div_nonneg
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hnonneg i j) (sq_nonneg (x i - x j)))
    zero_le_two

/-!
## Kernel structure
-/

/-- The all-ones vector is an eigenvector of the Laplacian with
eigenvalue `0`. -/
theorem ones_vec_eigenvalue_zero_QA (A : WAdj (V := V)) :
    (laplacian A).mulVec onesVec = (0 : ℝ) • onesVec := by
  rw [zero_smul]
  exact laplacian_ones_in_kernel A

/-- A vertex with no incident weight has an all-zero Laplacian row. -/
theorem laplacian_isolated_vertex_QA (A : WAdj (V := V)) (i₀ : V)
    (hisolated : ∀ j, A i₀ j = 0) :
    ∀ j, laplacian A i₀ j = 0 := by
  intro j
  have hdeg : deg A i₀ = 0 := by
    rw [deg]
    exact Finset.sum_eq_zero fun j _ => hisolated j
  simp only [laplacian, Matrix.sub_apply, degreeMatrix, hisolated j,
    sub_self]
  by_cases h : i₀ = j
  · subst h
    simp [hdeg]
  · simp [h]

end SpectralGraphTheory.QA
