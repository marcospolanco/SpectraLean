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
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan
import Scaffold.QA.Perturbation.Weyl_QA

/-!
# QA for the Davis–Kahan interface

Zero-perturbation instance of `davis_kahan_sin_theta`: with `E = 0` the
projector bound collapses to `‖P - P‖ ≤ 0`, checking the projector
indexing, separation direction, and ℓ² operator norm of the axiom's
interface. This is a real Lean proof deriving a consequence from the
admitted axiom; it does not prove the axiom.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Zero perturbation: with an explicitly separated spectrum, the
projector bound collapses to `‖P_{A+0} - P_A‖ ≤ 0 / δ = 0`. Exercises
the axiom's projector indexing, separation direction, and ℓ² operator
norm at `E = 0`. -/
theorem davis_kahan_zero_perturbation_QA (A : Matrix V V ℝ) (hA : A.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin (Fintype.card V), (i : ℕ) ≤ (k : ℕ) → (k : ℕ) < (j : ℕ) →
      δ ≤ evals hA j - evals hA i) :
    ‖initialProjector (A + 0) (show (A + 0).IsSymm by rw [add_zero]; exact hA) k
        - initialProjector A hA k‖
      ≤ ‖(0 : Matrix V V ℝ)‖ / δ := by
  have hAE : (A + 0).IsSymm := by rw [add_zero]; exact hA
  have hevals : ∀ i, evals hAE i = evals hA i := fun i => by
    have h := weyl_inequality A 0 hA zero_isSymm_QA i
    rw [norm_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  have hsep' : ∀ i j : Fin (Fintype.card V), (i : ℕ) ≤ (k : ℕ) → (k : ℕ) < (j : ℕ) →
      δ ≤ evals hAE j - evals hA i :=
    fun i j hi kj => by rw [hevals j]; exact hsep i j hi kj
  exact davis_kahan_sin_theta A 0 hA hAE k hk δ hδ hsep'

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
