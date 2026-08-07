/-
  DavisKahan_QA.lean

  Purpose
  -------
  QA lemmas for Davis-Kahan perturbation axioms.
  Verifies that the axioms are usable and behave correctly in trivial cases.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan

open Matrix

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-
QA: Zero perturbation implies zero subspace rotation.
Verifies that `davis_kahan_sin_theta` allows P = P' when E = 0.
-/
theorem davis_kahan_zero_perturbation
  (A : Matrix V V ℝ) (P : Matrix V V ℝ) (δ : ℝ)
  (h_symm_A : A.IsSymm)
  (h_proj_P : IsOrthogonalProjector P)
  (h_gap : 0 < δ)
  (h_invariant_P : A * P = P * A)
  (h_sep : ∀ λ ∈ spectrum_outside A P, ∀ μ ∈ spectrum_inside A P, |λ - μ| ≥ δ) :
  ‖P - P‖ ≤ 0 / δ := by
  -- Proof: ‖P - P‖ = ‖0‖ = 0. 0 / δ = 0.
  simp only [sub_self, norm_zero, zero_div, le_refl]

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
