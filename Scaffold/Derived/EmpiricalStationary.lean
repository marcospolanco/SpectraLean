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
import Scaffold.Mathlib.GraphTheory.DirectedMixing

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

The lazy twins of all three (2026-09-01,
`proposals/empirical-lazy-stationary-sampling.md` — the lazy program's
named follow-on; the plain capstone's own "agent that can only simulate
the walk" framing instantiated on the bipartite class — paths, trees,
grids — where the plain `r < 1` certificate is provably unsatisfiable,
fenced in QA) are the `LazyStationaryLimit` section below, at
`q = lazyWalkDistribution A t₀ x` with the bias **computed at the
intrinsic rate** `(1 − λ₂/2)^t₀` under connectivity alone — no
caller-supplied rate certificate anywhere:

- `empiricalLazyWalkDistribution_tail`: the fixed-time form;
- `empiricalLazyWalkDistribution_stationary_tail`: the bias-term form
  at the computed intrinsic-rate bias;
- `empiricalLazyWalkDistribution_stationary_tail_of_depth`: the
  depth-form capstone (the honest visible `λ₂ < 2`, mirroring the
  depth-form lazy TV ceiling — K₂'s rate-0 corner excluded).

QA: `Scaffold/QA/Derived/EmpiricalStationary_QA.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

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

/-!
## The lazy stationarity-limit form

The lazy twins of the section above, at `q = lazyWalkDistribution A t₀
x` — the lazy program's named follow-on
(`proposals/empirical-lazy-stationary-sampling.md`, 2026-09-01): the
plain capstone's hypothesis supplier is unsatisfiable on every
connected bipartite graph (its `r < 1` certificate must dominate the
`|1 − 2| = 1` top mode), so the plain sampling guarantee never
instantiates on paths, trees, or grids; the delivered entrywise lazy
ceiling `lazyWalkDistribution_sub_stationaryVec_abs_le` — connectivity
the only graph hypothesis, the rate computed as `1 − λ₂/2` — is the
hypothesis supplier that works there. See each theorem's docstring.
-/
section LazyStationaryLimit

/-- The graph instance at the lazy law: for `n` i.i.d. samples of the
fixed-time *lazy* walk law `lazyWalkDistribution A t₀ x`, the empirical
visit frequency of vertex `i` concentrates around the lazy law's own
mass at `i` at Hoeffding's `2 exp (-2 n t²)`. The law's
probability-vector certification is proved
(`lazyWalkDistribution_nonneg`/`sum_lazyWalkDistribution`) — no
symmetry, no connectivity, no mixing. -/
theorem empiricalLazyWalkDistribution_tail
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (t₀ : ℕ) (x : V) {n : ℕ} (hn : n ≠ 0) (i : V) (t : ℝ) (ht : 0 ≤ t) :
    (iidPMF (lazyWalkDistribution A t₀ x)
        (lazyWalkDistribution_nonneg A hnn hd t₀ x)
        (sum_lazyWalkDistribution A hd t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - lazyWalkDistribution A t₀ x i| ≥ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * t ^ 2)) :=
  hoeffding_empirical_iid (lazyWalkDistribution_nonneg A hnn hd t₀ x)
    (sum_lazyWalkDistribution A hd t₀ x) hn i t ht

/-- **The lazy stationarity-limit concentration (the bias-term form)**:
on a connected graph, the empirical visit frequency of `i` in `n` i.i.d.
samples of the `t₀`-step *lazy* walk law from `x` concentrates around
the stationary value with the lazy law's own distance to stationarity
folded in as a deterministic bias term — the bias **computed at the
intrinsic rate** `(1 − λ₂/2)^t₀ √(π i ((π x)⁻¹ − 1))`, not certified by
a caller-supplied `r`: connectivity is the only graph hypothesis, which
is the entire point of the lazy program (on every connected bipartite
graph — paths, trees, grids — the plain twin's `r < 1` certificate is
provably unsatisfiable, so the plain twin never instantiates there;
fenced in QA). Pure hard crust: the fixed-time tail is proved, the bias
is the proved entrywise lazy ceiling
`lazyWalkDistribution_sub_stationaryVec_abs_le`. -/
theorem empiricalLazyWalkDistribution_stationary_tail
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected)
    (t₀ : ℕ) (x i : V) {n : ℕ} (hn : n ≠ 0) {t : ℝ}
    (hbias : (1 - secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t₀
      * Real.sqrt (stationaryVec A i * ((stationaryVec A x)⁻¹ - 1)) < t) :
    (iidPMF (lazyWalkDistribution A t₀ x)
        (lazyWalkDistribution_nonneg A hnn hd t₀ x)
        (sum_lazyWalkDistribution A hd t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - stationaryVec A i| ≥ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ)
          * (t - (1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t₀
            * Real.sqrt (stationaryVec A i
                * ((stationaryVec A x)⁻¹ - 1))) ^ 2)) := by
  set b : ℝ := (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t₀
    * Real.sqrt (stationaryVec A i * ((stationaryVec A x)⁻¹ - 1)) with hb_def
  have hπν := lazyWalkDistribution_sub_stationaryVec_abs_le A hA hnn hd hcard
    hconn t₀ x i
  refine le_trans (measure_mono ?_)
    (empiricalLazyWalkDistribution_tail hnn hd t₀ x hn i (t - b) (by linarith))
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hsplit : ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
      - stationaryVec A i)
      = ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
          - lazyWalkDistribution A t₀ x i)
        + (lazyWalkDistribution A t₀ x i - stationaryVec A i) := by
    ring
  rw [hsplit] at hω
  have htri := abs_add_le
    ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
      - lazyWalkDistribution A t₀ x i)
    (lazyWalkDistribution A t₀ x i - stationaryVec A i)
  linarith

/-- **The depth-form capstone, lazy form — the oversmoothing ceiling's
empirical counterpart on the bipartite class**: past the same depth
`log (√(π i ((π x)⁻¹ − 1)) / (ε / 2)) / log (1 / (1 − λ₂/2))` at which
the depth-form lazy TV ceiling certifies the *true* lazy walk law within
`ε / 2` of stationarity, `n` i.i.d. simulated lazy trajectories of
length `t₀` estimate the stationary value at `i` to `ε` with failure
probability at most `2 exp (− n ε² / 2)`. The `λ₂ < 2` strictness is
honest and visible, mirroring the depth-form lazy TV ceiling: `K₂`'s
rate-0 corner is excluded (there the bias-term form still instantiates,
the bias being exactly `0` at `t₀ ≥ 1`). An agent that can only sample
the lazy walk inherits the depth certificate as a sampling guarantee —
on exactly the graphs where the plain program's certificate is provably
unsatisfiable. -/
theorem empiricalLazyWalkDistribution_stationary_tail_of_depth
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected)
    (hslt : secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard < 2)
    {ε : ℝ} (hε : 0 < ε)
    (t₀ : ℕ) (x i : V) {n : ℕ} (hn : n ≠ 0)
    (hthr : Real.log (Real.sqrt (stationaryVec A i
        * ((stationaryVec A x)⁻¹ - 1)) / (ε / 2))
      / Real.log (1 / (1 - secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard / 2)) ≤ (t₀ : ℝ)) :
    (iidPMF (lazyWalkDistribution A t₀ x)
        (lazyWalkDistribution_nonneg A hnn hd t₀ x)
        (sum_lazyWalkDistribution A hd t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - stationaryVec A i| ≥ ε}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * ε ^ 2 / 2)) := by
  set b : ℝ := (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t₀
    * Real.sqrt (stationaryVec A i * ((stationaryVec A x)⁻¹ - 1)) with hb_def
  have hsltpos : 0 < secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard :=
    secondEval_normalizedLaplacian_pos_of_connected A hA hnn hd hcard hconn
  have hr0 : 0 < (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2) := by linarith
  have hr1 : (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2) < 1 := by linarith
  have hble : b ≤ ε / 2 :=
    pow_mul_le_of_log_threshold hr0 hr1 (Real.sqrt_nonneg _)
      (by positivity) t₀ hthr
  have hmain := empiricalLazyWalkDistribution_stationary_tail (V := V) hA hnn hd
    hcard hconn t₀ x i hn (t := ε) (by linarith)
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

end LazyStationaryLimit

/-!
## The PageRank stationarity limit

The directed `t_mix` object's named consumer
(`proposals/directed-mixing-time-object.md`): the empirical-stationary
capstone cloned at the Google-walk law. On directed input the entire
symmetric `evals`/`eigvecOf` mixing toolkit is unavailable, so the
α-rate Doeblin certificate (the delivered `pageRank_tvDistance_le`) is
the only mixing route this sampling program can consume there — the
same "agent that can only simulate the walk" setting as the plain and
lazy sections, instantiated where no undirected machinery applies.
All hard crust: the tail engine (`hoeffding_empirical`) is proved, the
rate is proved, the entrywise bias comes through the new
equal-mass TV extraction `abs_sub_le_tvDistance`, and the depth-form
capstone consumes the directed object's own attainment specification
`pageRankMixingTimeFrom_spec`.
-/
section PageRankLimit

/-- **The fixed-time empirical PageRank tail**: for `n` i.i.d. samples
of the `t₀`-step Google-walk law from `x` (one simulated random-surfer
trajectory length, sampled independently `n` times), the empirical
visit frequency of vertex `i` concentrates around the law's own mass at
`i` at Hoeffding's `2 exp (−2 n t²)`. The law's probability-vector
certification is proved (`_nonneg`, `sum_pageRankDistribution`) —
nonnegative weights, positive degrees, the teleportation window; no
symmetry anywhere. -/
theorem empiricalPageRank_tail
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 ≤ α) (hα' : α < 1) [Nonempty V]
    (t₀ : ℕ) (x : V) {n : ℕ} (hn : n ≠ 0) (i : V) (t : ℝ) (ht : 0 ≤ t) :
    (iidPMF (pageRankDistribution A α t₀ x)
        (fun j => pageRankDistribution_nonneg A hnn hd hα hα' t₀ x j)
        (sum_pageRankDistribution A hd α t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - pageRankDistribution A α t₀ x i| ≥ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ) * t ^ 2)) :=
  hoeffding_empirical_iid
    (fun j => pageRankDistribution_nonneg A hnn hd hα hα' t₀ x j)
    (sum_pageRankDistribution A hd α t₀ x) hn i t ht

/-- **The stationarity-limit concentration at the PageRank bias**: on
the teleportation window with any mass-one stationary `π`, the
empirical visit frequency of `i` in `n` i.i.d. samples of the `t₀`-step
Google-walk law from `x` concentrates around the *stationary* value,
the law's own distance to stationarity folded in as a deterministic
bias term `α ^ t₀ · TV(δ_x, π)` (the rate theorem's own entrywise
extraction through `abs_sub_le_tvDistance`). At any threshold strictly
above the bias, the Hoeffking exponent pays only for the residual. -/
theorem empiricalPageRank_stationary_tail
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) (hα' : α < 1) [Nonempty V]
    {π : V → ℝ} (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π)
    (t₀ : ℕ) (x i : V) {n : ℕ} (hn : n ≠ 0) {t : ℝ}
    (hbias : α ^ t₀ * tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π < t) :
    (iidPMF (pageRankDistribution A α t₀ x)
        (fun j => pageRankDistribution_nonneg A hnn hd (le_of_lt hα) hα' t₀ x j)
        (sum_pageRankDistribution A hd α t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - π i| ≥ t}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (n : ℝ)
          * (t - α ^ t₀ * tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π) ^ 2)) := by
  set b : ℝ := α ^ t₀ * tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π with hb_def
  have hmass : ∑ j, pageRankDistribution A α t₀ x j = ∑ j, π j := by
    rw [sum_pageRankDistribution A hd α t₀ x, hπsum]
  have hentry : |pageRankDistribution A α t₀ x i - π i| ≤ b :=
    le_trans (abs_sub_le_tvDistance hmass i)
      (pageRank_tvDistance_le A hnn hd (le_of_lt hα) hα' hπsum hπstat
        (sum_piSingle x) t₀)
  refine le_trans (measure_mono ?_)
    (empiricalPageRank_tail hnn hd (le_of_lt hα) hα' t₀ x hn i (t - b)
      (by linarith))
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hsplit : ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
      - π i)
      = ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
          - pageRankDistribution A α t₀ x i)
        + (pageRankDistribution A α t₀ x i - π i) := by
    ring
  rw [hsplit] at hω
  have htri := abs_add_le
    ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
      - pageRankDistribution A α t₀ x i)
    (pageRankDistribution A α t₀ x i - π i)
  linarith

/-- **The depth-form capstone — the directed `t_mix` object's named
consumer**: past the directed mixing time at the half threshold
`ε / 2` — certifiable by the object's own α-ceiling — `n` i.i.d.
simulated random-surfer trajectories of length `t₀` estimate the
PageRank weight `π i` to `ε` with failure probability at most
`2 exp (− n ε² / 2)`. An agent that can only sample the Google walk
(never observe its law exactly) inherits the directed mixing object as
a sampling guarantee; on directed input the entire symmetric
`evals`/`eigvecOf` mixing toolkit is unavailable, so the α-rate Doeblin
certificate is the only route this sampling program can consume. The
object is load-bearing: the hypothesis is the object's attainment
condition, discharged through `pageRankMixingTimeFrom_spec`. -/
theorem empiricalPageRank_stationary_tail_of_depth
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) (hα' : α < 1) [Nonempty V]
    {π : V → ℝ} (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π)
    {ε : ℝ} (hε : 0 < ε) (t₀ : ℕ) (x i : V) {n : ℕ} (hn : n ≠ 0)
    (htmix : pageRankMixingTimeFrom A α π x (ε / 2) ≤ t₀) :
    (iidPMF (pageRankDistribution A α t₀ x)
        (fun j => pageRankDistribution_nonneg A hnn hd (le_of_lt hα) hα' t₀ x j)
        (sum_pageRankDistribution A hd α t₀ x)).toMeasure
      {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
          (if ω k = i then (1 : ℝ) else 0) - π i| ≥ ε}
      ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * ε ^ 2 / 2)) := by
  have hwit : ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      tvDistance (pageRankDistribution A α s x) π ≤ ε / 2 := by
    refine ⟨Nat.ceil (Real.log (tvDistance (Pi.single x (1 : ℝ) : V → ℝ) π
      / (ε / 2)) / Real.log (1 / α)), fun s hs => ?_⟩
    exact pageRank_tvDistance_le_of_depth A hnn hd hα hα' hπsum hπstat
      (sum_piSingle x) (by positivity) s
      (le_trans (Nat.le_ceil _) (by exact_mod_cast hs))
  have hTV : tvDistance (pageRankDistribution A α t₀ x) π ≤ ε / 2 :=
    pageRankMixingTimeFrom_spec A α π x hwit t₀ htmix
  have hmass : ∑ j, pageRankDistribution A α t₀ x j = ∑ j, π j := by
    rw [sum_pageRankDistribution A hd α t₀ x, hπsum]
  have hentry : |pageRankDistribution A α t₀ x i - π i| ≤ ε / 2 :=
    le_trans (abs_sub_le_tvDistance hmass i) hTV
  have htail := empiricalPageRank_tail (V := V) hnn hd (le_of_lt hα) hα' t₀ x
    hn i (ε - |pageRankDistribution A α t₀ x i - π i|) (by linarith)
  refine le_trans (measure_mono ?_) (le_trans htail ?_)
  · intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsplit : ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
        - π i)
        = ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
            - pageRankDistribution A α t₀ x i)
          + (pageRankDistribution A α t₀ x i - π i) := by
      ring
    rw [hsplit] at hω
    have htri := abs_add_le
      ((1 / (n : ℝ)) * ∑ k : Fin n, (if ω k = i then (1 : ℝ) else 0)
        - pageRankDistribution A α t₀ x i)
      (pageRankDistribution A α t₀ x i - π i)
    linarith
  · -- the exponent arithmetic: the deflated threshold is at least ε/2
    have hres : ε / 2 ≤ ε - |pageRankDistribution A α t₀ x i - π i| := by
      linarith
    have h1 : (ε / 2) ^ 2
        ≤ (ε - |pageRankDistribution A α t₀ x i - π i|) ^ 2 := by
      nlinarith [hres, sq_nonneg (ε - |pageRankDistribution A α t₀ x i - π i|),
        sq_nonneg (ε / 2)]
    have h2 : (2 : ℝ) * (n : ℝ) * (ε / 2) ^ 2
        ≤ 2 * (n : ℝ) * (ε - |pageRankDistribution A α t₀ x i - π i|) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (2 : ℝ) * (n : ℝ) * (ε / 2) ^ 2 = (n : ℝ) * ε ^ 2 / 2 := by
      ring
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
        (by positivity))

/-- **The worst-start depth-form capstone — the uniform `t_mix`
object's named consumer**: past the *uniform* directed mixing time at
the half threshold `ε / 2` — one start-independent certificate — `n`
i.i.d. simulated random-surfer trajectories of length `t₀` estimate
the PageRank weight `π i` to `ε` with failure probability at most
`2 exp (− n ε² / 2)`, *for every start `x` simultaneously*. The
per-start capstone needs a per-start threshold; the agent that cannot
control or does not know the surfer's start vertex gets one certificate
for all of them. On directed input the entire symmetric
`evals`/`eigvecOf` mixing toolkit is unavailable, so this uniform
Doeblin certificate is the only route the sampling program can
consume. The uniform object is load-bearing: the hypothesis is the
object's attainment condition, discharged through
`pageRankMixingTime_spec` at the witness the α-ceiling supplies. -/
theorem empiricalPageRank_uniform_tail_of_depth
    {V : Type} [Fintype V] [DecidableEq V] [MeasurableSpace V]
    [MeasurableSingletonClass V] {A : WAdj (V := V)}
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    {α : ℝ} (hα : 0 < α) (hα' : α < 1) [Nonempty V]
    {π : V → ℝ} (hπnn : ∀ i, 0 ≤ π i) (hπsum : ∑ i, π i = 1)
    (hπstat : π ᵥ* googleMatrix A α = π)
    {ε : ℝ} (hε : 0 < ε) (t₀ : ℕ) (i : V) {n : ℕ} (hn : n ≠ 0)
    (htmix : pageRankMixingTime A α π (ε / 2) ≤ t₀) :
    ∀ x : V,
      (iidPMF (pageRankDistribution A α t₀ x)
        (fun j => pageRankDistribution_nonneg A hnn hd
          (le_of_lt hα) hα' t₀ x j)
        (sum_pageRankDistribution A hd α t₀ x)).toMeasure
        {ω : Fin n → V | |(1 / (n : ℝ)) * ∑ k : Fin n,
            (if ω k = i then (1 : ℝ) else 0) - π i| ≥ ε}
        ≤ ENNReal.ofReal (2 * Real.exp (-(n : ℝ) * ε ^ 2 / 2)) := by
  intro x
  have hwit := exists_pageRankMixingTime_witness A hnn hd
    hα hα' hπnn hπsum hπstat (by positivity : 0 < ε / 2)
  have hspec := pageRankMixingTime_spec A α π hwit
  exact empiricalPageRank_stationary_tail_of_depth hnn hd hα hα' hπsum hπstat
    hε t₀ x i hn
    (pageRankMixingTimeFrom_le_of_cert A α π x t₀
      fun s hs => hspec s (Nat.le_trans htmix hs) x)

end PageRankLimit

end Scaffold.Derived.EmpiricalStationary
