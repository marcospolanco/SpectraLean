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
import Scaffold.Mathlib.Probability.IIDProduct
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.GraphTheory.Mixing

/-!
# Concentration of the empirical walk distribution

`hoeffding_empirical`'s first real theorem consumer (the fixed-time
form of `proposals/empirical-stationary-distribution-concentration.md`,
Step 1): the empirical visit frequency of `n` i.i.d. samples of the
fixed-time walk law `walkDistribution A t₀ x` concentrates around the
law itself at Hoeffding's `2 exp (-2 n t²)`.

Two theorems, both **conditional on the admitted axiom
`hoeffding_empirical`** — the tail inequality is axiom-backed and is
reported as such by `#print axioms`; every hypothesis clause
(measurability, independence, boundedness, and the internal centering
constant) is proved hard crust through `Probability.IIDProduct`:

- `hoeffding_empirical_iid`: the generic composition at any
  normalized factor `q : V → ℝ` — the empirical frequency of vertex
  `i` in `n` i.i.d. `q`-samples concentrates around `q i`;
- `empiricalWalkDistribution_tail`: the graph instance at
  `q = walkDistribution A t₀ x`, the walk law certified a probability
  vector by the proved `walkDistribution_nonneg` and
  `sum_walkDistribution` (no connectivity or symmetry hypothesis —
  the fixed-time form needs no mixing argument, per the proposal's
  Step-0 guidance).

The stationarity-limit form (concentration around `stationaryVec`
with the mixing bound's decay folded in as a bias term) is the
proposal's priced deferred Step 2.

QA: `Scaffold/QA/Derived/EmpiricalStationary_QA.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Scaffold.Derived.EmpiricalStationary

open Scaffold.Mathlib.Probability.IIDProduct
open SpectralGraphTheory

/-- The generic composition: on the i.i.d. product sampling space at
any normalized factor `q`, the empirical visit frequency
`(1/n) ∑ k 1_{ω k = i}` of `i` concentrates around its mean `q i` at
Hoeffding's `2 exp (-2 n t²)`. Conditional on the admitted axiom
`hoeffding_empirical`; every hypothesis clause is discharged by the
proved `Probability.IIDProduct` interfaces. `n ≠ 0` is load-bearing:
the statement's clean `q i` centering is the collapse of
`(1/n) ∑ k ∫ 1_{ω k = i}`, which equals `q i` exactly when the
average is a genuine average (the `n = 0` junk boundary is fenced in
QA against the axiom's own documented behavior). -/
theorem hoeffding_empirical_iid {V : Type*} [Fintype V] [DecidableEq V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    {q : V → ℝ} (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    {n : ℕ} (hn : n ≠ 0) (i : V) (t : ℝ) (ht : 0 ≤ t) :
    (iidPMF q hq0 hq1).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0) - q i| ≥ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * t ^ 2)) := by
  have hcenter : (1 / (n : ℝ)) * ∑ k : Fin n, ∫ ω' : Fin n → V,
      (if ω' k = i then (1 : ℝ) else 0) ∂(iidPMF (V := V) q hq0 hq1).toMeasure
      = q i := by
    rw [Finset.sum_congr rfl (fun k _ => integral_indicator q hq0 hq1 k i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hset : {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0) - q i| ≥ t}
      = {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
          - (1 / (n : ℝ)) * ∑ k : Fin n, ∫ ω', (if ω' k = i then (1 : ℝ) else 0)
              ∂(iidPMF (V := V) q hq0 hq1).toMeasure| ≥ t} := by
    rw [hcenter]
  rw [hset]
  exact Scaffold.Mathlib.Probability.Concentration.Scalar.hoeffding_empirical
    (fun k => measurable_indicator_coord k i)
    (fun k k' hkk' => indepFun_indicator_coord q hq0 hq1 hkk' i i)
    (fun k ω => by split_ifs <;> simp) t ht

/-- The graph instance: for `n` i.i.d. samples of the fixed-time
walk law `walkDistribution A t₀ x` (one simulated walk step-distribution,
sampled independently `n` times), the empirical visit frequency of
vertex `i` concentrates around the walk law's own mass at `i`:

`P {|p̂_i(n) - ν_{t₀} i| ≥ t} ≤ 2 exp (-2 n t²)`.

Conditional on `hoeffding_empirical` alone (the clause proofs and the
probability-vector certification of the walk law are proved). The
hypotheses are the walk's own: nonnegative weights and positive
degrees — no symmetry, no connectivity, no mixing. -/
theorem empiricalWalkDistribution_tail
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]
    {A : WAdj (V := V)} (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (t₀ : ℕ) (x : V) {n : ℕ} (hn : n ≠ 0) (i : V) (t : ℝ) (ht : 0 ≤ t) :
    (iidPMF (walkDistribution A t₀ x) (walkDistribution_nonneg A hnn hd t₀ x)
        (sum_walkDistribution A hd t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - walkDistribution A t₀ x i| ≥ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * t ^ 2)) :=
  hoeffding_empirical_iid (walkDistribution_nonneg A hnn hd t₀ x)
    (sum_walkDistribution A hd t₀ x) hn i t ht

end Scaffold.Derived.EmpiricalStationary
