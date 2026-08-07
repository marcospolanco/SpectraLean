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
Matrix Bernstein inequality for sums of independent self-adjoint random matrices.

This module provides axioms for the Matrix Bernstein concentration inequality.
-/

open Mathlib MeasureTheory ENNReal Real Matrix

variable {Ω : Type*} [MeasureSpace Ω]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-
Matrix Bernstein inequality: tail bound for the spectral norm with variance.

Source:
- Tropp, "An Introduction to Matrix Concentration Inequalities", 2015
  Theorem 1.1, Section 1.2, p. 2

Intended meaning:
Let X_1, ..., X_n be independent, self-adjoint matrix random variables of size d x d.
Assume E[X_i] = 0 and λ_max(X_i) ≤ R almost surely.
Let Σ = ∑ E[X_i²] be the matrix variance.
Then P(λ_max(∑ X_i) ≥ t) ≤ d * exp(-t² / (2‖Σ‖ + 2Rt/3)).
-/
axiom matrix_bernstein {n : ℕ} {X : Fin n → MRV Ω V} {R : ℝ}
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_symm : ∀ i ω, (X i ω).IsSymm)
  (h_mean : ∀ i, ∫ ω, X i ω ∂(volume : Measure Ω) = 0)
  (h_bound : ∀ i ω, Matrix.spectral_norm (X i ω) ≤ R)
  (t : ℝ) (ht : 0 ≤ t) :
  let Σ := ∑ i, ∫ ω, (X i ω) * (X i ω) ∂(volume : Measure Ω) in
  let σ2 := Matrix.spectral_norm Σ in
  let d := Fintype.card V in
  (ω : Ω) ↦ Matrix.spectral_norm (∑ i, X i ω) ≥ t ≤
    d * Real.exp (-t^2 / (2 * σ2 + 2 * R * t / 3))

end Scaffold.Mathlib.Probability.Concentration.Matrix
