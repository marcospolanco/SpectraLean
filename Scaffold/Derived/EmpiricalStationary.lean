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
import Scaffold.Mathlib.GraphTheory.Oversmoothing

/-!
# Concentration of the empirical walk distribution

`hoeffding_empirical`'s first real theorem consumer (the fixed-time
form of `proposals/empirical-stationary-distribution-concentration.md`,
Step 1): the empirical visit frequency of `n` i.i.d. samples of the
fixed-time walk law `walkDistribution A t₀ x` concentrates around the
law itself at Hoeffding's `2 exp (-2 n t²)`.

Two theorems, both **hard crust** — the tail inequality is the
2026-08-30-retired (locally proved) `hoeffding_empirical`, so since
that retirement `#print axioms` reports exactly the standard three for
both; every hypothesis clause (measurability, independence, boundedness,
and the internal centering constant) is proved through
`Probability.IIDProduct`:

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
with the mixing bound's decay folded in as a bias term) — the
proposal's Step 2, delivered 2026-08-31 with the consumer named (the
oversmoothing ceiling's empirical counterpart:
`GraphTheory.Oversmoothing`'s depth certificate becomes a *sampling*
guarantee for an agent that can only simulate the walk) — is the
`StationaryLimit` section below:

- `empiricalWalkDistribution_stationary_tail`: the bias-term form —
  at any threshold strictly above the oversmoothing entrywise constant
  `r ^ t₀ √(π i ((π x)⁻¹ − 1))`, the Hoeffding exponent pays only for
  the residual `t − bias`;
- `empiricalWalkDistribution_stationary_tail_of_depth`: the depth-form
  capstone — past the ceiling's own threshold at `ε / 2`, `n` sampled
  trajectories estimate `π i` to `ε` at `2 exp (− n ε² / 2)`.

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
Hoeffding's `2 exp (-2 n t²)`. Hard crust since the 2026-08-30
retirement of `hoeffding_empirical` (now a locally proved theorem);
every hypothesis clause is discharged by the proved
`Probability.IIDProduct` interfaces. `n ≠ 0` is load-bearing:
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
    (iIndepFun_indicator_coord (V := V) q hq0 hq1 i)
    (fun k ω => by split_ifs <;> simp) t ht

/-- The graph instance: for `n` i.i.d. samples of the fixed-time
walk law `walkDistribution A t₀ x` (one simulated walk step-distribution,
sampled independently `n` times), the empirical visit frequency of
vertex `i` concentrates around the walk law's own mass at `i`:

`P {|p̂_i(n) - ν_{t₀} i| ≥ t} ≤ 2 exp (-2 n t²)`.

Hard crust (the clause proofs and the
probability-vector certification of the walk law are proved; the tail
engine itself was retired from axiom to proved theorem 2026-08-30). The
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

/-!
## The stationarity-limit form (the proposal's Step 2)

The oversmoothing ceiling's empirical counterpart: the depth
certificate becomes a sampling guarantee. See the module docstring
above.
-/
section StationaryLimit

/-- **The stationarity-limit concentration (the proposal's Step 2).**
On a connected graph with a certified mixing rate, the empirical visit
frequency of `i` in `n` i.i.d. samples of the `t₀`-step walk law from
`x` concentrates around the *stationary* value with the walk law's own
distance to stationarity folded in as a deterministic bias term: at any
threshold strictly above the bias `r ^ t₀ √(π i ((π x)⁻¹ − 1))`
(the oversmoothing ceiling's own entrywise constant), the Hoeffding
exponent pays only for the residual `t − bias`. Pure hard crust: the
fixed-time tail is proved (the 2026-08-30 retirement of
`hoeffding_empirical` made the whole chain axiom-free) and the bias is
the proved entrywise extraction `walkDistribution_sub_stationaryVec_abs_le`.
The triangle route: `|p̂ − π| ≤ |p̂ − ν| + |ν − π|` turns the
stationarity event into the fixed-time event at the deflated
threshold. -/
theorem empiricalWalkDistribution_stationary_tail
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hconn : (supportGraph A hA).Connected) (r : ℝ)
    (hr : 0 ≤ r)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (t₀ : ℕ) (x i : V) {n : ℕ} (hn : n ≠ 0) {t : ℝ}
    (hbias : r ^ t₀ * Real.sqrt (stationaryVec A i
        * ((stationaryVec A x)⁻¹ - 1)) < t) :
    (iidPMF (walkDistribution A t₀ x) (walkDistribution_nonneg A hnn hd t₀ x)
        (sum_walkDistribution A hd t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - stationaryVec A i| ≥ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ)
          * (t - r ^ t₀ * Real.sqrt (stationaryVec A i
              * ((stationaryVec A x)⁻¹ - 1))) ^ 2)) := by
  set b : ℝ := r ^ t₀ * Real.sqrt (stationaryVec A i
    * ((stationaryVec A x)⁻¹ - 1)) with hb_def
  have hπν := walkDistribution_sub_stationaryVec_abs_le A hA hnn hd hconn r
    hr hrate t₀ x i
  refine le_trans (measure_mono ?_)
    (empiricalWalkDistribution_tail hnn hd t₀ x hn i (t - b) (by linarith))
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hsplit : ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
      - stationaryVec A i)
      = ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
          - walkDistribution A t₀ x i)
        + (walkDistribution A t₀ x i - stationaryVec A i) := by
    ring
  rw [hsplit] at hω
  have htri := abs_add_le
    ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
      - walkDistribution A t₀ x i)
    (walkDistribution A t₀ x i - stationaryVec A i)
  linarith

/-- **The depth-form capstone — the oversmoothing ceiling's empirical
counterpart** (the consumer the Step-2 gate priced): past the same
depth `log (√(π i ((π x)⁻¹ − 1)) / (ε / 2)) / log (1 / r)` at which the
oversmoothing ceiling certifies the *true* walk law within `ε / 2` of
stationarity, `n` i.i.d. simulated trajectories of length `t₀`
estimate the stationary value at `i` to `ε` with failure probability
at most `2 exp (− n ε² / 2)` — the Hoeffding exponent at the *half*
threshold, the bias paying the other half. An agent that can only
sample the walk (never observe its law exactly) inherits the depth
certificate as a sampling guarantee. -/
theorem empiricalWalkDistribution_stationary_tail_of_depth
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hconn : (supportGraph A hA).Connected) (r ε : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (t₀ : ℕ) (x i : V) {n : ℕ} (hn : n ≠ 0)
    (hthr : Real.log (Real.sqrt (stationaryVec A i
        * ((stationaryVec A x)⁻¹ - 1)) / (ε / 2))
      / Real.log (1 / r) ≤ (t₀ : ℝ)) :
    (iidPMF (walkDistribution A t₀ x) (walkDistribution_nonneg A hnn hd t₀ x)
        (sum_walkDistribution A hd t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - stationaryVec A i| ≥ ε}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * ε ^ 2 / 2)) := by
  set b : ℝ := r ^ t₀ * Real.sqrt (stationaryVec A i
    * ((stationaryVec A x)⁻¹ - 1)) with hb_def
  have hble : b ≤ ε / 2 :=
    pow_mul_le_of_log_threshold hr hr1 (Real.sqrt_nonneg _)
      (by positivity) t₀ hthr
  have hmain := empiricalWalkDistribution_stationary_tail (V := V) hA hnn hd
    hconn r (le_of_lt hr) hrate t₀ x i hn (t := ε) (by linarith)
  rw [← hb_def] at hmain
  refine le_trans hmain ?_
  have hres : ε / 2 ≤ ε - b := by linarith
  have h1 : (ε / 2) ^ 2 ≤ (ε - b) ^ 2 := by
    nlinarith [hres, sq_nonneg (ε - b), sq_nonneg (ε / 2)]
  have h2 : (2 : ℝ) * (n : ℝ) * (ε / 2) ^ 2
      ≤ 2 * (n : ℝ) * (ε - b) ^ 2 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : (2 : ℝ) * (n : ℝ) * (ε / 2) ^ 2 = (n : ℝ) * ε ^ 2 / 2 := by
    ring
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
      (by positivity))

end StationaryLimit

end Scaffold.Derived.EmpiricalStationary
