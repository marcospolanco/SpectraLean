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
import Mathlib.Probability.Notation
import Scaffold.Mathlib.Core.RandomVariable

namespace Scaffold.Mathlib.Probability.Concentration.Scalar

/-
Subgaussian random variables and their properties.

This module provides axioms for subgaussian concentration inequalities.
All axioms are cited from Vershynin, "High-Dimensional Probability",
unless otherwise noted.
-/

open Mathlib MeasureTheory ENNReal Real

variable {Ω : Type*} [MeasureSpace Ω] [ZeroOmega]

/-
The subgaussian norm (Orlicz norm) of a random variable.

This is defined as the smallest K such that E[exp(X²/K²)] ≤ 2.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Definition 2.5.1, Chapter 2, p. 27

Intended meaning:
The subgaussian norm measures the "tail behavior" of a random variable.
A random variable X is K-subgaussian iff E[exp(λX)] ≤ exp(λ²K²/2) for all λ.
-/
axiom subgaussian_norm (X : RV Ω) : ℝ

/-
Tail bound for a subgaussian random variable.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Theorem 2.1.1, Chapter 2, p. 21

Intended meaning:
If X is K-subgaussian, then P(|X| ≥ t) ≤ 2 exp(-t²/(2K²)) for all t ≥ 0.
This is the fundamental tail inequality for subgaussian random variables.
-/
axiom subgaussian_tail_bound {X : RV Ω} (K : ℝ) (hK : 0 ≤ K)
  (h_sub : subgaussian_norm X ≤ K) (t : ℝ) (ht : 0 ≤ t) :
  (ω : Ω) ↦ |X ω| ≥ t ≤ 2 * Real.exp (-t^2 / (2 * K^2))

/-
Moment growth of subgaussian random variables.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Exercise 2.1.5, Chapter 2, p. 24

Intended meaning:
If X is K-subgaussian, then (E[|X|^p])^(1/p) ≤ C * K * sqrt(p) for all p ≥ 1,
where C is a universal constant.
-/
axiom subgaussian_moment_growth {X : RV Ω} {K : ℝ} (hK : 0 ≤ K)
  (h_sub : subgaussian_norm X ≤ K) (p : ℝ) (hp : 1 ≤ p) :
  ∃ C : ℝ, 0 < C ∧ (∫ ω, |X ω|^p ∂(volume : Measure Ω))^(1/p) ≤ C * K * Real.sqrt p

/-
Linear combinations preserve subgaussian property.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Lemma 2.5.2, Chapter 2, p. 28

Intended meaning:
If X_i are independent with subgaussian_norm X_i ≤ K_i, then
subgaussian_norm (∑ a_i X_i) ≤ sqrt(∑ a_i² K_i²).
-/
axiom subgaussian_linear_combination {n : ℕ} {X : Fin n → RV Ω}
  {a : Fin n → ℝ} {K : Fin n → ℝ}
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_sub : ∀ i, subgaussian_norm (X i) ≤ K i) :
  subgaussian_norm (fun ω => ∑ i, a i * X i ω) ≤
    Real.sqrt (∑ i, (a i)^2 * (K i)^2)

/-
Centering preserves subgaussian norm.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Exercise 2.5.5, Chapter 2, p. 30

Intended meaning:
If X is K-subgaussian, then X - E[X] is also K-subgaussian
(up to a small constant factor).
-/
axiom subgaussian_centering {X : RV Ω} {K : ℝ} (hK : 0 ≤ K)
  (h_sub : subgaussian_norm X ≤ K) :
  ∃ C : ℝ, 0 < C ∧ subgaussian_norm (fun ω => X ω - ∫ ω', X ω' ∂(volume : Measure Ω)) ≤ C * K

/-
Hoeffding's lemma: bounded random variables are subgaussian.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Lemma 2.6.2, Chapter 2, p. 32

Intended meaning:
If X is a random variable with |X| ≤ a almost surely and E[X] = 0,
then X is a-subgaussian.
-/
axiom hoeffding_lemma {X : RV Ω} {a : ℝ} (ha : 0 ≤ a)
  (h_bound : ∀ ω, |X ω| ≤ a)
  (h_mean : ∫ ω, X ω ∂(volume : Measure Ω) = 0) :
  subgaussian_norm X ≤ a

/-
Sum of independent subgaussian random variables.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed.
  Theorem 2.6.3, Chapter 2, p. 33

Intended meaning:
If X_i are independent K-subgaussian, then
subgaussian_norm (∑ X_i) ≤ C * sqrt(n) * K for some universal constant C.
-/
axiom subgaussian_sum_bound {n : ℕ} {X : Fin n → RV Ω} {K : ℝ} (hK : 0 ≤ K)
  (h_indep : ∀ i j, i ≠ j → Independent (X i) (X j))
  (h_sub : ∀ i, subgaussian_norm (X i) ≤ K) :
  ∃ C : ℝ, 0 < C ∧ subgaussian_norm (fun ω => ∑ i, X i ω) ≤ C * Real.sqrt n * K

end Scaffold.Mathlib.Probability.Concentration.Scalar
