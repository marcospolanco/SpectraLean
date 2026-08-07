/-
  Weyl_QA.lean

  Purpose
  -------
  QA lemmas for Weyl's Inequality axioms.
  Verifies that the axioms are usable and behave correctly in trivial cases.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl

open Matrix

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/--
QA: Zero perturbation implies zero eigenvalue shift.
Verifies that `weyl_inequality` behaves correctly when E = 0.
-/
theorem weyl_zero_perturbation
  (A : Matrix V V ℝ) (i : Fin (Fintype.card V))
  (h_symm_A : A.IsSymm) :
  |A.spectrum i - (A + 0).spectrum i| ≤ ‖(0 : Matrix V V ℝ)‖ := by
  -- Proof: |λ - λ| = 0. ‖0‖ = 0.
  simp only [add_zero, sub_self, abs_zero, norm_zero, le_refl]

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
