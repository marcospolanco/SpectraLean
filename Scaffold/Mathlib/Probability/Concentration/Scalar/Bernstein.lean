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

namespace Scaffold.Mathlib.Probability.Concentration.Scalar

/-
Bernstein's inequality for sums of independent random variables.

This module provides axioms for Bernstein's concentration inequality,
which incorporates variance information for tighter bounds.
-/

open Mathlib MeasureTheory ENNReal Real

variable {Ω : Type*} [MeasureSpace Ω] [ZeroOmega]

/-
Bernstein's inequality: tail bound with variance term.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Theorem 2.8.1, Chapter 2, p. 43

Intended meaning:
If X_i are independent, |X_i| ≤ a almost surely, and Var(X_i) = σ_i²,
then P(|∑ (X_i - E[X_i])| ≥ t) ≤ 2 exp(-t² / (2∑ σ_i² + 2at/3)) for all t ≥ 0.
-/
axiom bernstein_inequality {n : ℕ} {X : Fin n → RV Ω} {a : ℝ} (ha : 0 ≤ a)
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_bound : ∀ i ω, |X i ω| ≤ a)
  (t : ℝ) (ht : 0 ≤ t) :
  let σ_sq := ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂(volume : Measure Ω))^2 ∂(volume : Measure Ω) in
  (ω : Ω) ↦ |∑ i, (X i ω - ∫ ω', X i ω' ∂(volume : Measure Ω))| ≥ t ≤
    2 * Real.exp (-(t^2) / (2 * σ_sq + (2 * a * t) / 3))

/-
Bernstein's inequality for bounded variance.

Source:
- Wainwright, High-Dimensional Statistics, 1st ed.
  Theorem 2.15, Chapter 2, p. 52

Intended meaning:
If X_i are independent with |X_i| ≤ a and ∑ Var(X_i) ≤ v,
then P(|∑ (X_i - E[X_i])| ≥ t) ≤ 2 exp(-t² / (2v + 2at/3)) for all t ≥ 0.
-/
axiom bernstein_bounded_variance {n : ℕ} {X : Fin n → RV Ω} {a v : ℝ}
  (ha : 0 ≤ a) (hv : 0 ≤ v)
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_bound : ∀ i ω, |X i ω| ≤ a)
  (h_var : ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂(volume : Measure Ω))^2 ∂(volume : Measure Ω) ≤ v)
  (t : ℝ) (ht : 0 ≤ t) :
  (ω : Ω) ↦ |∑ i, (X i ω - ∫ ω', X i ω' ∂(volume : Measure Ω))| ≥ t ≤
    2 * Real.exp (-(t^2) / (2 * v + (2 * a * t) / 3))

/-
Simplified Bernstein inequality for identically distributed variables.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Corollary 2.8.3, Chapter 2, p. 45

Intended meaning:
If X_i are i.i.d. with |X_i| ≤ a and Var(X_i) = σ²,
then P(|∑ (X_i - E[X_i])| ≥ t) ≤ 2 exp(-nt² / (2nσ² + 2at/3)) for all t ≥ 0.
-/
axiom bernstein_iid {n : ℕ} {X : Fin n → RV Ω} {a σ_sq : ℝ}
  (ha : 0 ≤ a) (hσ : 0 ≤ σ_sq)
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_bound : ∀ i ω, |X i ω| ≤ a)
  (h_var : ∀ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂(volume : Measure Ω))^2 ∂(volume : Measure Ω) = σ_sq)
  (t : ℝ) (ht : 0 ≤ t) :
  (ω : Ω) ↦ |∑ i, (X i ω - ∫ ω', X i ω' ∂(volume : Measure Ω))| ≥ t ≤
    2 * Real.exp (-(n * t^2) / (2 * n * σ_sq + (2 * a * t) / 3))

end Scaffold.Mathlib.Probability.Concentration.Scalar
