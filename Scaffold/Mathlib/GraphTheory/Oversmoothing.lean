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
import Scaffold.Mathlib.GraphTheory.Mixing

/-!
# The certified oversmoothing ceiling

`proposals/message-passing-depth-mixing-bound.md`: depth-form consumers
of the mixing program's closing bound `chiSquareDistance_le_of_connected`
(`Mixing.lean`). That bound upper-bounds the χ² mixing distance by
`r ^ (2t) · ((π x)⁻¹ − 1)`, decreasing in `t` for a rate `r ∈ (0, 1)` —
so it certifies *convergence*, not divergence, and the depth statement
it supports is an **oversmoothing ceiling**: past a computable depth,
every node's `t`-step propagated view is within `ε` of the graph's
universal stationary value, regardless of where the signal started.
(The proposal's original draft inverted this direction — an upper bound
on mixing can never certify non-propagation; see its own correction
record and its "Genuine over-squashing needs a different tool" section
for what a real floor would require.)

The declarations:

- `stationaryVec_le_one`: the stationary weights are entrywise at most
  one (positive masses summing to one) — the engine that makes the
  ceiling constant nonnegative.
- `walkDistribution_sub_stationaryVec_abs_le`: the **entrywise
  extraction** (the proposal's Step 1) — a single vertex's deviation
  `|ν_t x y − π y|` is at most `r ^ t · √(π y · ((π x)⁻¹ − 1))`, by
  bounding one nonnegative summand of the χ² distance by the whole sum
  (`Finset.single_le_sum`) and taking the square root.
- `pow_mul_le_of_log_threshold`: the **calculus bridge** — if
  `log (C / ε) / log (1 / r) ≤ t` with `0 < r < 1`, `0 ≤ C`, `0 < ε`,
  then `r ^ t * C ≤ ε` (divide by the negative `log r` and the
  inequality flips: that flip is the proposal's corrected step).
- `walkDistribution_sub_stationaryVec_le_of_depth`: the **oversmoothing
  ceiling** — the entrywise bound specialized past the computed
  threshold depth.
- `walkDistribution_sub_walkDistribution_le_of_depth`: the
  **two-start indistinguishability corollary** — past the depth, the
  `t`-step views from any two starting nodes are within `2ε` of each
  other, the "representations become indistinguishable" statement
  oversmoothing papers state informally.
- `oversmoothing_log_threshold_mono`: the certified depth is
  **monotone in the rate** — a looser rate certificate provably buys a
  provably larger threshold (the engine behind the QA sanity contrast;
  the ceiling tracks the certified spectral gap, not a constant).

Everything here is proved — zero new axioms; the only external inputs
are the mixing bound's own hypotheses, with the rate `r` supplied by
the caller exactly as `davis_kahan_sin_theta`'s `δ` is.

## Honest scope

This bounds the **linearized, mean-aggregation propagation operator**
— repeated application of the random-walk transition matrix, what a
linear GCN-style layer computes up to a learned weight matrix and a
nonlinearity at each step — *not* a full nonlinear, multi-channel GNN
with learned weights and activations. The bound uses a single **global**
mixing rate `r` for the whole graph, not a per-node-pair refinement
(per-pair via `effectiveResistance` is a priced follow-on in the
proposal, not delivered here). Graphs admitting no `r < 1` certificate
— bipartite graphs, whose normalized spectrum touches `2` — are
outside the ceiling's reach entirely: no depth is certified, and the
χ² bound honestly predicts no decay there (`Mixing_QA.lean`'s path
fixture).
-/

namespace SpectralGraphTheory

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- The stationary weights are entrywise at most one: they are
positive masses summing to one, so each single term (bounded by the
total via `Finset.single_le_sum`) is at most one. This is what makes
`(π x)⁻¹ − 1 ≥ 0` and hence the oversmoothing constant real. -/
theorem stationaryVec_le_one (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (x : V) : stationaryVec A x ≤ 1 := by
  have hnn : ∀ i, 0 ≤ stationaryVec A i := fun i =>
    le_of_lt (stationaryVec_pos A hd i)
  have h1 := sum_stationaryVec A hd
  have h2 : stationaryVec A x ≤ ∑ i, stationaryVec A i :=
    Finset.single_le_sum (fun i _ => hnn i) (Finset.mem_univ x)
  linarith

/-- **The entrywise extraction** (the proposal's Step 1): on a
connected graph with symmetric nonnegative weights and positive
degrees, a single vertex's deviation of the `t`-step walk law from
stationarity is at most `r ^ t` times
`√(π y · ((π x)⁻¹ − 1))` — the square root of one nonnegative χ²
summand's ceiling, itself bounded by the whole χ² distance through
`chiSquareDistance_le_of_connected`. The constant is the per-vertex
part of the mixing bound's normalization; `hr : 0 ≤ r` keeps the
root-flip honest. Load-bearing on the mixing bound's exact shape: the
`(π x)⁻¹ − 1` prefactor enters the entrywise constant unchanged. -/
theorem walkDistribution_sub_stationaryVec_abs_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hconn : (supportGraph A hA).Connected) (r : ℝ) (hr : 0 ≤ r)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (t : ℕ) (x y : V) :
    |walkDistribution A t x y - stationaryVec A y|
      ≤ r ^ t * Real.sqrt (stationaryVec A y
          * ((stationaryVec A x)⁻¹ - 1)) := by
  have hπy := stationaryVec_pos A hd y
  have hnon : 0 ≤ stationaryVec A y * ((stationaryVec A x)⁻¹ - 1) := by
    have hle : stationaryVec A x ≤ 1 := stationaryVec_le_one A hd x
    have hpos := stationaryVec_pos A hd x
    have hon : (1 : ℝ) ≤ (stationaryVec A x)⁻¹ :=
      (one_le_inv₀ hpos).mpr hle
    exact mul_nonneg (le_of_lt hπy) (by linarith)
  have hone : (walkDistribution A t x y - stationaryVec A y) ^ 2
      / stationaryVec A y ≤ chiSquareDistance A t x := by
    rw [chiSquareDistance]
    exact Finset.single_le_sum
      (f := fun i => (walkDistribution A t x i - stationaryVec A i)^2
        / stationaryVec A i)
      (fun i _ => div_nonneg (sq_nonneg _)
        (le_of_lt (stationaryVec_pos A hd i))) (Finset.mem_univ y)
  rw [div_le_iff₀ hπy] at hone
  have htwo := chiSquareDistance_le_of_connected A hA hnonneg hd hconn r t x hrate
  have hle : (walkDistribution A t x y - stationaryVec A y) ^ 2
      ≤ (r ^ t * Real.sqrt (stationaryVec A y
          * ((stationaryVec A x)⁻¹ - 1))) ^ 2 := by
    have hsq : (r ^ t * Real.sqrt (stationaryVec A y
          * ((stationaryVec A x)⁻¹ - 1))) ^ 2
        = (r ^ (2 * t) * ((stationaryVec A x)⁻¹ - 1)) * stationaryVec A y := by
      have h2t : r ^ (2 * t) = (r ^ t) ^ 2 := by
        rw [show (2 * t : ℕ) = t + t from by omega, pow_add, pow_two]
      rw [mul_pow, Real.sq_sqrt hnon, h2t]
      ring
    calc (walkDistribution A t x y - stationaryVec A y) ^ 2
        ≤ chiSquareDistance A t x * stationaryVec A y := hone
      _ ≤ (r ^ (2 * t) * ((stationaryVec A x)⁻¹ - 1)) * stationaryVec A y :=
          mul_le_mul_of_nonneg_right htwo (le_of_lt hπy)
      _ = (r ^ t * Real.sqrt (stationaryVec A y
            * ((stationaryVec A x)⁻¹ - 1))) ^ 2 := hsq.symm
  exact abs_le_of_sq_le_sq hle
    (mul_nonneg (pow_nonneg hr t) (Real.sqrt_nonneg _))

/-- **The log-threshold calculus bridge** (the proposal's corrected
Step 2): for a rate `0 < r < 1` and a tolerance `0 < ε`, any depth
`t` at or above the threshold `log (C / ε) / log (1 / r)` brings
`r ^ t * C` under `ε`. The whole content is the sign of `log`: since
`r < 1` the denominator is positive, and dividing by it *preserves*
the inequality — the original draft's error was flipping it. `C = 0`
(the single-vertex degenerate constant) is handled trivially. -/
theorem pow_mul_le_of_log_threshold {r C ε : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hC : 0 ≤ C) (hε : 0 < ε) (t : ℕ)
    (hthr : Real.log (C / ε) / Real.log (1 / r) ≤ (t : ℝ)) :
    r ^ t * C ≤ ε := by
  rcases eq_or_lt_of_le hC with h0 | hC0
  · rw [← h0, mul_zero]
    exact le_of_lt hε
  · have hrinv : 0 < 1 / r := div_pos (by norm_num) hr
    have hrinv1 : 1 < 1 / r := (one_lt_div hr).mpr hr1
    have hlogpos : 0 < Real.log (1 / r) := Real.log_pos hrinv1
    have hCE : 0 < C / ε := div_pos hC0 hε
    have hstep : Real.log (C / ε) ≤ (t : ℝ) * Real.log (1 / r) :=
      (div_le_iff₀ hlogpos).mp hthr
    have hexp : Real.exp (Real.log (C / ε))
        ≤ Real.exp ((t : ℝ) * Real.log (1 / r)) :=
      Real.exp_le_exp.mpr hstep
    rw [Real.exp_log hCE, ← Real.log_pow (1 / r) t] at hexp
    rw [Real.exp_log (pow_pos hrinv t), one_div, inv_pow, inv_eq_one_div] at hexp
    have hfin : C * r ^ t ≤ 1 * ε :=
      (div_le_div_iff₀ hε (pow_pos hr t)).mp hexp
    rw [mul_comm]
    linarith

/-- **The oversmoothing ceiling** — the proposal's headline depth
statement: on a connected graph with a certified mixing rate
`0 < r < 1`, past the depth `log (C / ε) / log (1 / r)` (with `C` the
entrywise constant `√(π y · ((π x)⁻¹ − 1))`), the `t`-step walk law
from any start `x` is within `ε` of the stationary value at *every*
target vertex `y` — regardless of where the signal started. Directly
usable as an architecture-design ceiling: stack more layers than this
and you are provably averaging the signal away (within the module
docstring's honest scope). -/
theorem walkDistribution_sub_stationaryVec_le_of_depth (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hconn : (supportGraph A hA).Connected) (r ε : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (t : ℕ) (x y : V)
    (hthr : Real.log (Real.sqrt (stationaryVec A y
          * ((stationaryVec A x)⁻¹ - 1)) / ε)
      / Real.log (1 / r) ≤ (t : ℝ)) :
    |walkDistribution A t x y - stationaryVec A y| ≤ ε := by
  refine le_trans
    (walkDistribution_sub_stationaryVec_abs_le A hA hnonneg hd hconn r
      (le_of_lt hr) hrate t x y) ?_
  exact pow_mul_le_of_log_threshold hr hr1
    (Real.sqrt_nonneg _) hε t hthr

/-- **Two-start indistinguishability** — the corollary oversmoothing
papers state informally: past the depth at which *both* starts' views
are within `ε` of stationarity, the two `t`-step views are within
`2ε` of *each other*, at every target vertex. The node-distinguishing
information carried by the starting positions is gone. -/
theorem walkDistribution_sub_walkDistribution_le_of_depth
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hconn : (supportGraph A hA).Connected) (r ε : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (t : ℕ) (x₁ x₂ y : V)
    (hthr₁ : Real.log (Real.sqrt (stationaryVec A y
          * ((stationaryVec A x₁)⁻¹ - 1)) / ε)
      / Real.log (1 / r) ≤ (t : ℝ))
    (hthr₂ : Real.log (Real.sqrt (stationaryVec A y
          * ((stationaryVec A x₂)⁻¹ - 1)) / ε)
      / Real.log (1 / r) ≤ (t : ℝ)) :
    |walkDistribution A t x₁ y - walkDistribution A t x₂ y| ≤ 2 * ε := by
  have h1 := walkDistribution_sub_stationaryVec_le_of_depth A hA hnonneg hd
    hconn r ε hr hr1 hε hrate t x₁ y hthr₁
  have h2 := walkDistribution_sub_stationaryVec_le_of_depth A hA hnonneg hd
    hconn r ε hr hr1 hε hrate t x₂ y hthr₂
  calc |walkDistribution A t x₁ y - walkDistribution A t x₂ y|
      = |(walkDistribution A t x₁ y - stationaryVec A y)
        + (stationaryVec A y - walkDistribution A t x₂ y)| := by
          congr 1
          ring
    _ ≤ |walkDistribution A t x₁ y - stationaryVec A y|
        + |stationaryVec A y - walkDistribution A t x₂ y| :=
          abs_add _ _
    _ = |walkDistribution A t x₁ y - stationaryVec A y|
        + |walkDistribution A t x₂ y - stationaryVec A y| := by
          rw [abs_sub_comm (stationaryVec A y) (walkDistribution A t x₂ y)]
    _ ≤ ε + ε := add_le_add h1 h2
    _ = 2 * ε := by ring

/-- **The certified depth is monotone in the rate**: with the same
constant and tolerance, a larger certified rate buys a provably larger
threshold — `log (1/r₂) ≤ log (1/r₁)` for `r₁ ≤ r₂` in `(0, 1)`, and
the numerator `log (C/ε) ≥ 0` whenever `ε ≤ C`. This is the engine
behind the QA sanity contrast (the same graph at rate `1/2` vs `4/5`
certifies depths `3` vs `9` at `ε = 1/8`): the ceiling tracks the
certified spectral gap, not a fixed constant — and it makes explicit
that the bound is only as good as the caller's rate certificate. -/
theorem oversmoothing_log_threshold_mono {r₁ r₂ C ε : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : r₁ ≤ r₂) (hr₂' : r₂ < 1) (hε : 0 < ε) (hC : ε ≤ C) :
    Real.log (C / ε) / Real.log (1 / r₁)
      ≤ Real.log (C / ε) / Real.log (1 / r₂) := by
  have hr₂pos : 0 < r₂ := lt_of_lt_of_le hr₁ hr₂
  have hCE : (1 : ℝ) ≤ C / ε := (one_le_div_iff).mpr (Or.inl ⟨hε, hC⟩)
  have hnum : 0 ≤ Real.log (C / ε) := Real.log_nonneg hCE
  have hpos₁ : 0 < Real.log (1 / r₁) :=
    Real.log_pos ((one_lt_div hr₁).mpr (lt_of_le_of_lt hr₂ hr₂'))
  have hpos₂ : 0 < Real.log (1 / r₂) :=
    Real.log_pos ((one_lt_div hr₂pos).mpr hr₂')
  have hden : Real.log (1 / r₂) ≤ Real.log (1 / r₁) := by
    refine Real.log_le_log
      (div_pos (show (0:ℝ) < 1 from by norm_num) hr₂pos) ?_
    rw [div_le_div_iff₀ hr₂pos hr₁]
    linarith
  rw [div_le_div_iff₀ hpos₁ hpos₂]
  exact mul_le_mul_of_nonneg_left hden hnum

end SpectralGraphTheory
