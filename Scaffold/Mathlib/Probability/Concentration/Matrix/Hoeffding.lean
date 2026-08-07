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
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Scaffold.Mathlib.Core.RandomVariable

namespace Scaffold.Mathlib.Probability.Concentration.Matrix

/-
Matrix Hoeffding inequality for bounded independent self-adjoint random matrices.

This module provides axioms for the Matrix Hoeffding concentration inequality.
-/

open Mathlib MeasureTheory ENNReal Real Matrix

variable {Ω : Type*} [MeasureSpace Ω]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-
Matrix Hoeffding inequality: tail bound for the spectral norm of sums of bounded matrices.

Source:
- Tropp, "An Introduction to Matrix Concentration Inequalities", 2015
  Theorem 1.4, Section 1.2, p. 2

Intended meaning:
Let X_1, ..., X_n be independent, self-adjoint matrix random variables of size d x d.
Assume E[X_i] = 0 and X_i² ≤ A_i² almost surely for some fixed matrices A_i.
Then P(λ_max(∑ X_i) ≥ t) ≤ d * exp(-t² / (2 σ²)) where σ² = ‖∑ A_i²‖.

QA: Exercised by `matrix_hoeffding_zero_sum_QA` in
`Scaffold/QA/Concentration/Matrix_QA.lean`.
-/
axiom matrix_hoeffding {n : ℕ} {X : Fin n → MRV Ω V} {A : Fin n → Matrix V V ℝ}
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_symm : ∀ i ω, (X i ω).IsSymm)
  (h_mean : ∀ i, ∫ ω, X i ω ∂(volume : Measure Ω) = 0)
  (h_bound : ∀ i ω, (X i ω) * (X i ω) ≤ A i * A i)
  (t : ℝ) (ht : 0 ≤ t) :
  let σ2 := ‖∑ i, A i * A i‖ in
  let d := Fintype.card V in
  (ω : Ω) ↦ Matrix.spectral_norm (∑ i, X i ω) ≥ t ≤
    d * Real.exp (-t^2 / (2 * σ2))

end Scaffold.Mathlib.Probability.Concentration.Matrix
