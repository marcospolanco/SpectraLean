/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl

/-!
# QA for the Weyl perturbation interface

Zero-perturbation instances of `weyl_inequality` and
`spectral_gap_stability`. These are real Lean proofs deriving
consequences from the admitted axioms; they do not prove the axioms.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The zero matrix is symmetric (interface convenience). -/
theorem zero_isSymm_QA : (0 : Matrix V V ℝ).IsSymm := isSymm_zero

/-- Eigenvalues are invariant under adding zero, derived from the
admitted Weyl inequality at `E = 0`. -/
theorem evals_add_zero (A : Matrix V V ℝ) (hA : A.IsSymm)
    (i : Fin (Fintype.card V)) :
    evals (show (A + 0).IsSymm by rw [add_zero]; exact hA) i = evals hA i := by
  have h := weyl_inequality A 0 hA zero_isSymm_QA i
  rw [norm_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- Instantiating Weyl's inequality at `E = 0`: every eigenvalue is
fixed. Exercises the sorted-eigenvalue indexing and the ℓ² operator
norm of the axiom's interface. -/
theorem zero_perturbation_QA (A : Matrix V V ℝ) (hA : A.IsSymm)
    (i : Fin (Fintype.card V)) :
    |evals (show (A + 0).IsSymm by rw [add_zero]; exact hA) i - evals hA i|
      ≤ ‖(0 : Matrix V V ℝ)‖ := by
  rw [evals_add_zero A hA i, sub_self, abs_zero, norm_zero]

/-- Instantiating gap stability at `E = 0`: the spectral gap is exactly
preserved, since `γ - 2 * 0 = γ`. -/
theorem spectral_gap_zero_perturbation_QA (A : Matrix V V ℝ) (hA : A.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (γ : ℝ)
    (hγ : spectralGap A hA k hk ≥ γ) :
    spectralGap (A + 0) (show (A + 0).IsSymm by rw [add_zero]; exact hA) k hk
      ≥ γ := by
  have h := spectral_gap_stability A 0 hA zero_isSymm_QA k hk 0
    (norm_zero.le) γ hγ
  simpa using h

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
