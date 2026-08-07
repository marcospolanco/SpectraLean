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
Hoeffding's inequality for bounded independent random variables.

This module provides axioms for Hoeffding's concentration inequality.
-/

open Mathlib MeasureTheory ENNReal Real

variable {Ω : Type*} [MeasureSpace Ω] [ZeroOmega]

/-
Hoeffding's inequality: tail bound for sums of bounded independent variables.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Theorem 2.2.2, Chapter 2, p. 24

Intended meaning:
If X_i are independent, |X_i| ≤ a_i almost surely, and E[X_i] = 0,
then P(|∑ X_i| ≥ t) ≤ 2 exp(-t² / (2∑ a_i²)) for all t ≥ 0.
-/
axiom hoeffding_inequality {n : ℕ} {X : Fin n → RV Ω} {a : Fin n → ℝ}
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_bound : ∀ i ω, |X i ω| ≤ a i)
  (h_mean : ∀ i, ∫ ω, X i ω ∂(volume : Measure Ω) = 0)
  (t : ℝ) (ht : 0 ≤ t) :
  (ω : Ω) ↦ |∑ i, X i ω| ≥ t ≤
    2 * Real.exp (-t^2 / (2 * ∑ i, (a i)^2))

/-
Hoeffding's inequality for identically distributed bounded variables.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Corollary 2.2.3, Chapter 2, p. 25

Intended meaning:
If X_i are independent, |X_i| ≤ a almost surely, and E[X_i] = 0,
then P(|∑ X_i| ≥ t) ≤ 2 exp(-t² / (2na²)) for all t ≥ 0.
-/
axiom hoeffding_iid {n : ℕ} {X : Fin n → RV Ω} {a : ℝ} (ha : 0 ≤ a)
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_bound : ∀ i ω, |X i ω| ≤ a)
  (h_mean : ∀ i, ∫ ω, X i ω ∂(volume : Measure Ω) = 0)
  (t : ℝ) (ht : 0 ≤ t) :
  (ω : Ω) ↦ |∑ i, X i ω| ≥ t ≤
    2 * Real.exp (-t^2 / (2 * n * a^2))

/-
Hoeffding's inequality for empirical averages.

Source:
- Boucheron, Lugosi, Massart, Concentration Inequalities
  Theorem 2.8, Chapter 2, p. 32

Intended meaning:
If X_i are independent, 0 ≤ X_i ≤ 1 almost surely, then
P(|(∑ X_i)/n - E[(∑ X_i)/n]| ≥ t) ≤ 2 exp(-2nt²) for all t ≥ 0.
-/
axiom hoeffding_empirical {n : ℕ} {X : Fin n → RV Ω}
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_bound : ∀ i ω, 0 ≤ X i ω ∧ X i ω ≤ 1)
  (t : ℝ) (ht : 0 ≤ t) :
  let μ := (1 / (n : ℝ)) * ∑ i, ∫ ω, X i ω ∂(volume : Measure Ω) in
  (ω : Ω) ↦ |(1 / (n : ℝ)) * ∑ i, X i ω - μ| ≥ t ≤
    2 * Real.exp (-2 * n * t^2)

end Scaffold.Mathlib.Probability.Concentration.Scalar
