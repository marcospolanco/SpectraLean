/-
  Variational_QA.lean

  Purpose
  -------
  QA lemmas for the Rayleigh quotient interface of
  `Scaffold.Mathlib.GraphTheory.Spectral`: nonnegativity on PSD
  operators, kernel vectors, and homogeneity — the pieces composed by
  the admitted `lambda2_variational` characterization.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the variational axiom.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The Rayleigh quotient has the documented junk value at the zero
vector. -/
theorem rayleigh_zero_QA (M : Matrix V V ℝ) : rayleigh M 0 = 0 := by
  simp [rayleigh]

/-- For a nonzero vector the Rayleigh denominator (a sum of squares) is
strictly positive. -/
theorem rayleigh_denominator_pos_QA {x : V → ℝ} (hx : x ≠ 0) :
    0 < Matrix.dotProduct x x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx (funext hcon)
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

/-- For a PSD operator the Rayleigh quotient of any nonzero vector is
nonnegative. -/
theorem rayleigh_nonneg_psd_QA (M : Matrix V V ℝ)
    (hpsd : ∀ x : V → ℝ, 0 ≤ quadForm M x) (x : V → ℝ) (hx : x ≠ 0) :
    0 ≤ rayleigh M x := by
  rw [rayleigh, if_neg hx]
  exact div_nonneg (hpsd x) (rayleigh_denominator_pos_QA hx).le

/-- Kernel vectors have Rayleigh quotient zero. -/
theorem rayleigh_zero_in_kernel_QA (M : Matrix V V ℝ) (x : V → ℝ)
    (hx : x ≠ 0) (hker : M.mulVec x = 0) :
    rayleigh M x = 0 := by
  rw [rayleigh, if_neg hx, quadForm, hker, Matrix.dotProduct_zero, zero_div]

/-- The Rayleigh quotient is homogeneous of degree zero: rescaling the
vector by a nonzero constant leaves it unchanged. -/
theorem rayleigh_homogeneous_QA (M : Matrix V V ℝ) (x : V → ℝ) (c : ℝ)
    (hx : x ≠ 0) (hc : c ≠ 0) :
    rayleigh M (c • x) = rayleigh M x := by
  have hcx : c • x ≠ 0 := smul_ne_zero_iff.mpr ⟨hc, hx⟩
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  have hd : Matrix.dotProduct x x ≠ 0 :=
    ne_of_gt (rayleigh_denominator_pos_QA hx)
  rw [rayleigh, if_neg hcx, rayleigh, if_neg hx, quadForm, quadForm]
  simp only [Matrix.mulVec_smul, Matrix.smul_dotProduct,
    Matrix.dotProduct_smul, smul_eq_mul, mul_assoc]
  field_simp
  ring

end SpectralGraphTheory.QA
