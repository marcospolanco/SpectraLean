/-
  Variational_QA.lean

  Purpose
  -------
  QA lemmas for variational characterizations of eigenvalues.

  These verify basic properties of Rayleigh quotients and
  minimization principles for eigenvalues.

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
## QA 1: Rayleigh quotient is nonnegative for PSD matrices

Verify that for a PSD matrix, the Rayleigh quotient is always
nonnegative. This is a basic sanity check for variational principles.
-/

theorem rayleigh_quotient_nonneg_psd_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (M : Matrix V V ℝ)
  (hM : Matrix.IsSymm M)
  (hpsd : ∀ x : V → ℝ, 0 ≤ Matrix.dotProduct x (M.mulVec x))
  (x : V → ℝ)
  (hx : x ≠ 0) :
  0 ≤ (Matrix.dotProduct x (M.mulVec x)) / (∑ i, x i ^ 2) := by
  -- Real proof: For PSD matrices, x^T M x ≥ 0, and x^T x > 0 for nonzero x
  apply div_nonneg
  · exact hpsd x
  · apply Finset.sum_nonneg
    intro i _
    apply sq_nonneg

/-!
## QA 2: Rayleigh quotient is zero for kernel vectors

Verify that for vectors in the kernel of a PSD matrix,
the Rayleigh quotient is zero.
-/

theorem rayleigh_quotient_zero_in_kernel_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (M : Matrix V V ℝ)
  (hM : Matrix.IsSymm M)
  (x : V → ℝ)
  (hx : M.mulVec x = 0)
  (hx' : x ≠ 0) :
  (Matrix.dotProduct x (M.mulVec x)) / (∑ i, x i ^ 2) = 0 := by
  -- Real proof: If Mx = 0, then x^T M x = 0
  rw [hx]
  simp only [Pi.zero_apply, Matrix.dotProduct_zero, div_zero]

/-!
## QA 3: Rayleigh quotient is homogeneous

Verify that scaling the input vector doesn't change the
Rayleigh quotient. This is a basic invariance property.
-/

theorem rayleigh_quotient_homogeneous_QA
  {V : Type} [Fintype V] [DecidableEq V]
  (M : Matrix V V ℝ)
  (hM : Matrix.IsSymm M)
  (x : V → ℝ)
  (c : ℝ)
  (hx : x ≠ 0)
  (hc : c ≠ 0) :
  (Matrix.dotProduct (c • x) (M.mulVec (c • x))) /
    (∑ i, (c • x) i ^ 2) =
  (Matrix.dotProduct x (M.mulVec x)) / (∑ i, x i ^ 2) := by
  -- Real proof: The factor c^2 cancels from numerator and denominator
  -- R(cx) = (cx)^T M (cx) / (cx)^T (cx) = c^2(x^T M x) / c^2(x^T x) = R(x)
  simp only [Pi.smul_apply, Matrix.mulVec_smul, Matrix.dotProduct_smul]
  have h_csq : c ^ 2 ≠ 0 := by
    apply sq_ne_zero.mpr hc
  field_simp [h_csq, hx]

/-!
## QA 4: Ones vector has Rayleigh quotient zero for Laplacian

Verify that the all-ones vector gives Rayleigh quotient zero
for the Laplacian. This is because it's in the kernel.
-/


/-!
## QA 5: Rayleigh quotient is bounded by extremal eigenvalues

Verify that for any symmetric matrix, the Rayleigh quotient
is between the minimum and maximum eigenvalues. This is a
basic sanity check for variational characterizations.
-/


end SpectralGraphTheory.QA
