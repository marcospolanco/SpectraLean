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
import Scaffold.Mathlib.GraphTheory.Foster
import Scaffold.Mathlib.InformationTheory.Entropy

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
- the **TV twin** (delivered 2026-08-31,
  `proposals/total-variation-mixing-conversion.md`):
  `walkDistribution_tvDistance_le_of_rate` (the split-constant rate
  form `TV ≤ (1/2)·r^t·√C`), `walkDistribution_tvDistance_le_of_depth`
  (past the threshold — the entrywise ceiling's own with `ε` at `2ε` —
  the walk law is within `ε` of stationarity *in total variation*,
  the field-standard `t_mix(ε)` statement), and
  `walkDistribution_tvDistance_sub_le_of_depth` (the two-start `2ε`
  twin through `tvDistance_triangle`), all consuming
  `Mixing.lean`'s conversion `TV ≤ (1/2)·√χ²` composed with the proved
  χ² mixing bound.

## The per-pair resistance refinement (delivered 2026-08-31)

The follow-on the proposal deferred at this module's first delivery,
now delivered (`proposals/message-passing-depth-mixing-bound.md`,
Deferred item 1) — the first bridge between the electrical axis
(`effectiveResistance`) and the mixing axis (`walkDistribution`):

- `walkDistribution_eq_sum_eigbasis`: the **entrywise eigenbasis
  expansion** of the walk law on a `d`-regular graph —
  `ν_t x y = ∑ k, (1 - λ k / d)^t * u k x * u k y` over the
  combinatorial Laplacian's orthonormal eigenbasis (kernel modes carry
  factor `1` and reconstruct the stationary weight; no connectivity
  hypothesis).
- `walkDistribution_pair_contrast_abs_le`: the **per-pair resistance
  contrast bound** — on a connected `d`-regular graph, the four-point
  contrast of the walk law is bounded by the certified mode-rate `ρ`
  times `√R(x₁,x₂) · √R(y,y')`: nearby start pairs and nearby target
  pairs become indistinguishable at the graph-global rate, with the
  global initial constant `π y · ((π x)⁻¹ − 1)` replaced by the pair's
  resistance geometry (Foster's spectral resistance formula
  `effectiveResistance_eq_sum_eigbasis` joined through
  Cauchy–Schwarz against the eigenvalue weights).
- `laplacian_quadForm_le_two_mul` / `eigvalOf_laplacian_le_two_mul`:
  the `λ ≤ 2d` engine (the Dirichlet sum with
  `(x i - x j) ^ 2 ≤ 2 x i ^ 2 + 2 x j ^ 2`).
- `walkDistribution_pair_contrast_abs_le'`: the packaged corollary at
  the walk family's own certificate shape — the contrast bound at the
  explicit mode-rate `2 d r ^ t` under `|1 - λ k / d| ≤ r`.

Supporting plumbing (public, all under regularity `deg ≡ d`):
`laplacian_eq_smul_one_sub`, `walkTransitionMatrix_eq_smul_inv`,
`walkTransitionMatrix_transpose_eq_smul`,
`adjacency_mulVec_eq`, `adjacency_mulVec_eigvecOf_laplacian`,
`eigvecOf_const_of_eigvalOf_zero`, `eigvalOf_laplacian_nonneg`.

Everything here is proved — zero new axioms; the only external inputs
are the mixing bound's own hypotheses, with the rate `r` supplied by
the caller exactly as `davis_kahan_sin_theta`'s `δ` is.

## The discrete mixing time (delivered 2026-09-01)

The TV-conversion proposal's deferred `t_mix` object, its consumer gate
discharged by the Poisson-bridge delivery (`Mixing.lean`'s transfer
corollary — its `hmix` clause is exactly the object's witness
condition). `walkMixingTimeFrom A x ε` is the least number of steps
from which the walk law stays within `ε` of stationarity in total
variation (Levin–Peres–Wilmer ch. 20's per-start reading, the discrete
twin of `Mixing.lean`'s `contMixingTimeFrom`), with the certificate
interface `_le_of_cert`, the attainment specification `_spec` (a
*minimum* — `ℕ` is well-ordered, so the witness infimum is attained, a
fact the continuous twin cannot have; this is what discharges the
transfer corollary's `hmix` clause), the spectral ceiling
`_le_of_connected` at the depth-form TV certificate's own hypothesis
set `0 < r < 1` (honest: periodic chains admit no such certificate —
the `K₂` fence), ε-antitonicity, and the bridge composition
`contWalkDistribution_tvDistance_le_of_walkMixingTime` (the named
consumer: the continuous walk's TV bound with the discrete certificate
supplied by the object itself, only the Poisson lower-tail left to the
caller).

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


/-!
## The per-pair resistance refinement

The plumbing lemmas below are stated at regularity `deg ≡ d` (the
shelf's `d : ℝ` hypothesis idiom). Throughout, `eigvecOf (laplacian A)`
is the combinatorian Laplacian's orthonormal eigenbasis and
`eigvalOf` its eigenvalues; the walk factor of mode `k` is
`1 - λ k / d` because `P = A / d = 1 - L / d` under regularity.
-/

section RegularityPlumbing

/-- Under `deg ≡ d` the walk matrix is `d⁻¹ • A`. -/
theorem walkTransitionMatrix_eq_smul_inv {A : WAdj (V := V)} {d : ℝ}
    (hd : ∀ i, deg A i = d) :
    walkTransitionMatrix A = d⁻¹ • A := by
  ext i j
  simp only [walkTransitionMatrix, Matrix.diagonal_mul, Matrix.smul_apply,
    smul_eq_mul, hd i]

/-- Under regularity and symmetry the adjoint walk action is the
scaled adjacency action: `Pᵀ = d⁻¹ • A`. -/
theorem walkTransitionMatrix_transpose_eq_smul {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hd : ∀ i, deg A i = d) :
    (walkTransitionMatrix A)ᵀ = d⁻¹ • A := by
  rw [walkTransitionMatrix_eq_smul_inv hd, Matrix.transpose_smul]
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]
  exact congrArg (fun z => d⁻¹ * z) (hA.apply i j)

/-- Entrywise regularity action: under `deg ≡ d`,
`A *ᵥ v = d • v - L *ᵥ v` for every vector. -/
theorem adjacency_mulVec_eq {A : WAdj (V := V)} {d : ℝ}
    (hd : ∀ i, deg A i = d) (v : V → ℝ) :
    A *ᵥ v = d • v - (laplacian A) *ᵥ v := by
  have hdiag : ∀ i : V, ∑ j : V, degreeMatrix A i j * v j = d * v i := by
    intro i
    simp only [degreeMatrix, dite_eq_ite, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hd i]
  funext i
  have hLap : ∀ i : V, ∑ x : V, laplacian A i x * v x
      = ∑ j : V, degreeMatrix A i j * v j - ∑ j : V, A i j * v j := by
    intro i
    simp only [laplacian, Matrix.sub_apply, sub_mul,
      Finset.sum_sub_distrib]
  have hR : (d • v - (laplacian A) *ᵥ v) i
      = d * v i - ((laplacian A) *ᵥ v) i := rfl
  simp only [Matrix.mulVec, Matrix.dotProduct, hR]
  rw [hLap i, hdiag i]
  ring

/-- The adjacency action at a Laplacian eigenvector under regularity:
`A *ᵥ u k = (d - λ k) • u k`. -/
theorem adjacency_mulVec_eigvecOf_laplacian {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hd : ∀ i, deg A i = d) (k : V) :
    A *ᵥ (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
      = (d - eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
          • (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hact : (laplacian A) *ᵥ (eigvecOf (laplacian A) hL k)
      = eigvalOf (laplacian A) hL k • (eigvecOf (laplacian A) hL k) :=
    (isHermitian_of_isSymm hL).mulVec_eigenvectorBasis k
  rw [adjacency_mulVec_eq hd, hact]
  exact (sub_smul d (eigvalOf (laplacian A) hL k)
    (eigvecOf (laplacian A) hL k)).symm

end RegularityPlumbing

section PairResistance

/-- Kernel-mode eigenvectors are constant on connected graphs (the
eigen-equation at a zero mode lands in the Laplacian kernel, which
connectivity pins to the constants). -/
theorem eigvecOf_const_of_eigvalOf_zero {A : WAdj (V := V)} (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected) (k : V)
    (hk : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0) :
    ∃ c : ℝ, eigvecOf (laplacian A) (laplacian_symmetric A hA) k = fun _ => c := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hact : (laplacian A) *ᵥ (eigvecOf (laplacian A) hL k)
      = eigvalOf (laplacian A) hL k • (eigvecOf (laplacian A) hL k) :=
    (isHermitian_of_isSymm hL).mulVec_eigenvectorBasis k
  rw [hk, zero_smul] at hact
  exact exists_const_of_laplacian_mulVec_eq_zero A hA hnn hconn hact

/-- Laplacian eigenvalues are nonnegative (positive semidefiniteness at
the unit eigenvectors). -/
theorem eigvalOf_laplacian_nonneg {A : WAdj (V := V)} (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (k : V) :
    0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) k := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have h1 := quadForm_eigvecOf_self hL k
  have h2 := laplacian_psd A hA hnn (eigvecOf (laplacian A) hL k)
  rw [h1] at h2
  exact h2

/-- **The entrywise eigenbasis expansion of the walk law** on a
`d`-regular graph: `ν_t x y` is the eigenbasis reconstruction of the
start mass, each mode evolved by its walk factor `1 - λ k / d` (the
walk matrix is `A / d = 1 - L / d` under regularity). Kernel modes
carry factor `1` and reconstruct the stationary weight, so no
connectivity hypothesis is needed. Load-bearing on the exact walk
factor: a wrong scaling or reflection in `1 - λ k / d` breaks the
identity (the QA pins it at the triangle, where the top mode's factor
is `-1/2`). -/
theorem walkDistribution_eq_sum_eigbasis {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hd : ∀ i, deg A i = d) (hd0 : d ≠ 0)
    (t : ℕ) (x : V) :
    ∀ y : V, walkDistribution A t x y
      = ∑ k, (1 - eigvalOf (laplacian A) (laplacian_symmetric A hA) k / d)^t
          * (eigvecOf (laplacian A) (laplacian_symmetric A hA) k x)
          * (eigvecOf (laplacian A) (laplacian_symmetric A hA) k y) := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  induction t with
  | zero =>
      intro y
      rw [walkDistribution_zero, ← eigvecOf_expansion_apply hL
        (Pi.single x (1 : ℝ)) y]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_zero, one_mul]
      have hdot : eigvecOf (laplacian A) hL k ⬝ᵥ (Pi.single x (1 : ℝ))
          = eigvecOf (laplacian A) hL k x := by
        simp [Matrix.dotProduct, Pi.single_apply, mul_ite]
      rw [hdot]
  | succ t ih =>
      intro y
      rw [walkDistribution_succ]
      have hinner : ∀ k : V, ∑ j' : V,
          (walkTransitionMatrix A)ᵀ y j'
            * eigvecOf (laplacian A) hL k j'
          = (1 - eigvalOf (laplacian A) hL k / d)
            * eigvecOf (laplacian A) hL k y := by
        intro k
        have hfold : ∑ j' : V, (walkTransitionMatrix A)ᵀ y j'
            * eigvecOf (laplacian A) hL k j'
            = ((walkTransitionMatrix A)ᵀ *ᵥ eigvecOf (laplacian A) hL k) y := by
          simp [Matrix.mulVec, Matrix.dotProduct]
        rw [hfold, walkTransitionMatrix_transpose_eq_smul hA hd,
          Matrix.smul_mulVec_assoc,
          adjacency_mulVec_eigvecOf_laplacian hA hd k,
          smul_smul, Pi.smul_apply, smul_eq_mul]
        field_simp
      have hunfold : ((walkTransitionMatrix A)ᵀ *ᵥ walkDistribution A t x) y
          = ∑ j' : V, (walkTransitionMatrix A)ᵀ y j'
              * walkDistribution A t x j' := by
        simp [Matrix.mulVec, Matrix.dotProduct]
      rw [hunfold]
      have hpush : ∑ j' : V, (walkTransitionMatrix A)ᵀ y j'
              * walkDistribution A t x j'
          = ∑ j' : V, (walkTransitionMatrix A)ᵀ y j'
              * ∑ k, (1 - eigvalOf (laplacian A) hL k / d)^t
                * eigvecOf (laplacian A) hL k x
                * eigvecOf (laplacian A) hL k j' := by
        simp only [ih]
      rw [hpush]
      have hswap : ∑ j' : V, (walkTransitionMatrix A)ᵀ y j'
              * ∑ k, (1 - eigvalOf (laplacian A) hL k / d)^t
                * eigvecOf (laplacian A) hL k x
                * eigvecOf (laplacian A) hL k j'
          = ∑ k, (1 - eigvalOf (laplacian A) hL k / d)^t
              * eigvecOf (laplacian A) hL k x
              * ((1 - eigvalOf (laplacian A) hL k / d)
                  * eigvecOf (laplacian A) hL k y) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hring : ∑ j' : V, (walkTransitionMatrix A)ᵀ y j'
            * ((1 - eigvalOf (laplacian A) hL k / d)^t
              * eigvecOf (laplacian A) hL k x
              * eigvecOf (laplacian A) hL k j')
          = ∑ j' : V, (1 - eigvalOf (laplacian A) hL k / d)^t
              * eigvecOf (laplacian A) hL k x
              * ((walkTransitionMatrix A)ᵀ y j'
                * eigvecOf (laplacian A) hL k j') :=
          Finset.sum_congr rfl fun j' _ => by ring
        rw [hring, ← Finset.mul_sum, hinner k]
      rw [hswap]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [pow_succ']
      ring

/-- **The per-pair resistance contrast bound.** On a connected
`d`-regular graph with symmetric nonnegative weights, the four-point
contrast of the walk law — how differently two starts see the target
pair `(y, y')`, equivalently how differently two targets are seen from
the start pair `(x₁, x₂)` — is bounded by the certified mode-rate `ρ`
(the walk factor of each decaying mode, weighted by its eigenvalue)
times the resistance geometry `√R(x₁,x₂) · √R(y,y')` of the two pairs.
The per-pair reading: nearby start pairs and nearby target pairs
become indistinguishable at the graph-global rate, with the entrywise
bound's global initial constant `π y · ((π x)⁻¹ − 1)` replaced by the
pair's resistance geometry. Foster's spectral resistance formula is
joined through Cauchy–Schwarz against the eigenvalue weights; kernel
modes contribute nothing on either side (constant eigenvectors, junk
zeros). -/
theorem walkDistribution_pair_contrast_abs_le {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, deg A i = d)
    (hd0 : d ≠ 0) (hconn : (supportGraph A hA).Connected)
    (ρ : ℝ) (hr : 0 ≤ ρ) (t : ℕ) (x₁ x₂ y y' : V)
    (hrate : ∀ k : V, eigvalOf (laplacian A) (laplacian_symmetric A hA) k ≠ 0 →
      eigvalOf (laplacian A) (laplacian_symmetric A hA) k
        * |1 - eigvalOf (laplacian A) (laplacian_symmetric A hA) k / d| ^ t ≤ ρ) :
    |(walkDistribution A t x₁ y - walkDistribution A t x₂ y)
      - (walkDistribution A t x₁ y' - walkDistribution A t x₂ y')|
      ≤ ρ * Real.sqrt (effectiveResistance A x₁ x₂)
          * Real.sqrt (effectiveResistance A y y') := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hlamnn : ∀ k : V, 0 ≤ eigvalOf (laplacian A) hL k :=
    fun k => eigvalOf_laplacian_nonneg hA hnn k
  have hdiff : (walkDistribution A t x₁ y - walkDistribution A t x₂ y)
        - (walkDistribution A t x₁ y' - walkDistribution A t x₂ y')
      = ∑ k, (1 - eigvalOf (laplacian A) hL k / d) ^ t
          * (eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂)
          * (eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y') := by
    have e1 := walkDistribution_eq_sum_eigbasis hA hd hd0 t x₁
    have e2 := walkDistribution_eq_sum_eigbasis hA hd hd0 t x₂
    have hstep : ∀ z : V,
        walkDistribution A t x₁ z - walkDistribution A t x₂ z
          = ∑ k, (1 - eigvalOf (laplacian A) hL k / d) ^ t
              * (eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂)
              * eigvecOf (laplacian A) hL k z := by
      intro z
      rw [e1 z, e2 z, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hstep y, hstep y', ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hker : ∀ (k : V), eigvalOf (laplacian A) hL k = 0 → ∀ a b : V,
      eigvecOf (laplacian A) hL k a - eigvecOf (laplacian A) hL k b = 0 := by
    intro k hk a b
    obtain ⟨c, hc⟩ := eigvecOf_const_of_eigvalOf_zero hA hnn hconn k hk
    rw [hc]
    simp
  have habs : |∑ k, (1 - eigvalOf (laplacian A) hL k / d) ^ t
        * (eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂)
        * (eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y')|
      ≤ ρ * ∑ k, |eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂|
          * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
          / eigvalOf (laplacian A) hL k := by
    calc |∑ k, (1 - eigvalOf (laplacian A) hL k / d) ^ t
            * (eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂)
            * (eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y')|
        ≤ ∑ k, |(1 - eigvalOf (laplacian A) hL k / d) ^ t
            * (eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂)
            * (eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y')| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, (eigvalOf (laplacian A) hL k
            * |1 - eigvalOf (laplacian A) hL k / d| ^ t)
            * (|eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂|
              * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
              / eigvalOf (laplacian A) hL k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hk : eigvalOf (laplacian A) hL k = 0
          · rw [hk, hker k hk x₁ x₂]
            simp
          · rw [abs_mul, abs_mul, abs_pow]
            have hlampos : 0 < eigvalOf (laplacian A) hL k :=
              lt_of_le_of_ne (hlamnn k) (Ne.symm hk)
            field_simp
            ring
      _ ≤ ∑ k, ρ * (|eigvecOf (laplacian A) hL k x₁
              - eigvecOf (laplacian A) hL k x₂|
            * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
            / eigvalOf (laplacian A) hL k) := by
          refine Finset.sum_le_sum fun k _ => ?_
          by_cases hk : eigvalOf (laplacian A) hL k = 0
          · rw [hk, hker k hk x₁ x₂]
            simp
          · exact mul_le_mul_of_nonneg_right (hrate k hk)
              (div_nonneg
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
                (hlamnn k))
      _ = ρ * ∑ k, |eigvecOf (laplacian A) hL k x₁
              - eigvecOf (laplacian A) hL k x₂|
            * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
            / eigvalOf (laplacian A) hL k := by rw [Finset.mul_sum]
  -- Cauchy–Schwarz against the resistance weights (junk-zero corners
  -- collapse: at a kernel mode both sides of each identity are `0`).
  have hcs : (∑ k, |eigvecOf (laplacian A) hL k x₁
          - eigvecOf (laplacian A) hL k x₂|
        * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
        / eigvalOf (laplacian A) hL k) ^ 2
      ≤ (∑ k, (eigvecOf (laplacian A) hL k x₁
            - eigvecOf (laplacian A) hL k x₂) ^ 2
            / eigvalOf (laplacian A) hL k)
        * (∑ k, (eigvecOf (laplacian A) hL k y
            - eigvecOf (laplacian A) hL k y') ^ 2
            / eigvalOf (laplacian A) hL k) := by
    have hAB : ∀ k : V, (|eigvecOf (laplacian A) hL k x₁
          - eigvecOf (laplacian A) hL k x₂| / Real.sqrt (eigvalOf (laplacian A) hL k))
        * (|eigvecOf (laplacian A) hL k y
          - eigvecOf (laplacian A) hL k y'| / Real.sqrt (eigvalOf (laplacian A) hL k))
        = |eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂|
          * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
          / eigvalOf (laplacian A) hL k := by
      intro k
      by_cases hk : eigvalOf (laplacian A) hL k = 0
      · simp [hk, Real.sqrt_zero]
      · have hlampos : 0 < eigvalOf (laplacian A) hL k :=
          lt_of_le_of_ne (hlamnn k) (Ne.symm hk)
        have hs : Real.sqrt (eigvalOf (laplacian A) hL k) ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.mpr hlampos)
        field_simp
    have hA2 : ∀ k : V, (|eigvecOf (laplacian A) hL k x₁
          - eigvecOf (laplacian A) hL k x₂| / Real.sqrt (eigvalOf (laplacian A) hL k)) ^ 2
        = (eigvecOf (laplacian A) hL k x₁
            - eigvecOf (laplacian A) hL k x₂) ^ 2
          / eigvalOf (laplacian A) hL k := by
      intro k
      rw [div_pow, sq_abs, Real.sq_sqrt (hlamnn k)]
    have hB2 : ∀ k : V, (|eigvecOf (laplacian A) hL k y
          - eigvecOf (laplacian A) hL k y'| / Real.sqrt (eigvalOf (laplacian A) hL k)) ^ 2
        = (eigvecOf (laplacian A) hL k y
            - eigvecOf (laplacian A) hL k y') ^ 2
          / eigvalOf (laplacian A) hL k := by
      intro k
      rw [div_pow, sq_abs, Real.sq_sqrt (hlamnn k)]
    calc (∑ k, |eigvecOf (laplacian A) hL k x₁
            - eigvecOf (laplacian A) hL k x₂|
          * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
          / eigvalOf (laplacian A) hL k) ^ 2
        = (∑ k, (|eigvecOf (laplacian A) hL k x₁
              - eigvecOf (laplacian A) hL k x₂|
            / Real.sqrt (eigvalOf (laplacian A) hL k))
          * (|eigvecOf (laplacian A) hL k y
              - eigvecOf (laplacian A) hL k y'|
            / Real.sqrt (eigvalOf (laplacian A) hL k))) ^ 2 := by
          refine congrArg (fun X => X ^ 2)
            (Finset.sum_congr rfl fun k _ => (hAB k).symm)
      _ ≤ (∑ k, (|eigvecOf (laplacian A) hL k x₁
              - eigvecOf (laplacian A) hL k x₂|
            / Real.sqrt (eigvalOf (laplacian A) hL k)) ^ 2)
          * (∑ k, (|eigvecOf (laplacian A) hL k y
              - eigvecOf (laplacian A) hL k y'|
            / Real.sqrt (eigvalOf (laplacian A) hL k)) ^ 2) :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ = (∑ k, (eigvecOf (laplacian A) hL k x₁
              - eigvecOf (laplacian A) hL k x₂) ^ 2
            / eigvalOf (laplacian A) hL k)
          * (∑ k, (eigvecOf (laplacian A) hL k y
              - eigvecOf (laplacian A) hL k y') ^ 2
            / eigvalOf (laplacian A) hL k) := by
          rw [Finset.sum_congr rfl fun k _ => hA2 k,
            Finset.sum_congr rfl fun k _ => hB2 k]
  have hc0 : 0 ≤ ∑ k, |eigvecOf (laplacian A) hL k x₁
      - eigvecOf (laplacian A) hL k x₂|
    * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
    / eigvalOf (laplacian A) hL k :=
    Finset.sum_nonneg fun k _ =>
      div_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hlamnn k)
  have hroot : ∑ k, |eigvecOf (laplacian A) hL k x₁
        - eigvecOf (laplacian A) hL k x₂|
      * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
      / eigvalOf (laplacian A) hL k
      ≤ Real.sqrt (∑ k, (eigvecOf (laplacian A) hL k x₁
            - eigvecOf (laplacian A) hL k x₂) ^ 2
            / eigvalOf (laplacian A) hL k)
        * Real.sqrt (∑ k, (eigvecOf (laplacian A) hL k y
            - eigvecOf (laplacian A) hL k y') ^ 2
            / eigvalOf (laplacian A) hL k) := by
    have hSx : 0 ≤ ∑ k, (eigvecOf (laplacian A) hL k x₁
          - eigvecOf (laplacian A) hL k x₂) ^ 2
        / eigvalOf (laplacian A) hL k :=
      Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (hlamnn k)
    have hSy : 0 ≤ ∑ k, (eigvecOf (laplacian A) hL k y
          - eigvecOf (laplacian A) hL k y') ^ 2
        / eigvalOf (laplacian A) hL k :=
      Finset.sum_nonneg fun k _ => div_nonneg (sq_nonneg _) (hlamnn k)
    have hkey : (∑ k, |eigvecOf (laplacian A) hL k x₁
            - eigvecOf (laplacian A) hL k x₂|
          * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
          / eigvalOf (laplacian A) hL k) ^ 2
        ≤ (Real.sqrt (∑ k, (eigvecOf (laplacian A) hL k x₁
              - eigvecOf (laplacian A) hL k x₂) ^ 2
              / eigvalOf (laplacian A) hL k)
          * Real.sqrt (∑ k, (eigvecOf (laplacian A) hL k y
              - eigvecOf (laplacian A) hL k y') ^ 2
              / eigvalOf (laplacian A) hL k)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hSx, Real.sq_sqrt hSy]
      exact hcs
    have habsle := abs_le_of_sq_le_sq hkey
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    rwa [abs_of_nonneg hc0] at habsle
  -- Foster's spectral resistance formula, junk-zero form.
  have hRx : effectiveResistance A x₁ x₂
      = ∑ k, (eigvecOf (laplacian A) hL k x₁
          - eigvecOf (laplacian A) hL k x₂) ^ 2
          / eigvalOf (laplacian A) hL k := by
    rw [effectiveResistance_eq_sum_eigbasis A hA hnn hconn x₁ x₂]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : eigvalOf (laplacian A) hL k = 0
    · rw [if_pos hk, hker k hk x₁ x₂, hk]
      simp
    · rw [if_neg hk]
  have hRy : effectiveResistance A y y'
      = ∑ k, (eigvecOf (laplacian A) hL k y
          - eigvecOf (laplacian A) hL k y') ^ 2
          / eigvalOf (laplacian A) hL k := by
    rw [effectiveResistance_eq_sum_eigbasis A hA hnn hconn y y']
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : eigvalOf (laplacian A) hL k = 0
    · rw [if_pos hk, hker k hk y y', hk]
      simp
    · rw [if_neg hk]
  rw [hdiff]
  calc |∑ k, (1 - eigvalOf (laplacian A) hL k / d) ^ t
        * (eigvecOf (laplacian A) hL k x₁ - eigvecOf (laplacian A) hL k x₂)
        * (eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y')|
      ≤ ρ * ∑ k, |eigvecOf (laplacian A) hL k x₁
          - eigvecOf (laplacian A) hL k x₂|
        * |eigvecOf (laplacian A) hL k y - eigvecOf (laplacian A) hL k y'|
        / eigvalOf (laplacian A) hL k := habs
    _ ≤ ρ * (Real.sqrt (effectiveResistance A x₁ x₂)
        * Real.sqrt (effectiveResistance A y y')) := by
        refine mul_le_mul_of_nonneg_left ?_ hr
        rw [hRx, hRy]
        exact hroot
    _ = ρ * Real.sqrt (effectiveResistance A x₁ x₂)
        * Real.sqrt (effectiveResistance A y y') := by ring

/-- **The `λ ≤ 2d` engine.** On a symmetric nonnegative `d`-regular
graph the Laplacian energy is at most `2d` times the Euclidean norm —
the Dirichlet sum with `(x i - x j) ^ 2 ≤ 2 x i ^ 2 + 2 x j ^ 2`, the
row sums `d` for one half and the column sums `d` (symmetry +
regularity) for the other. -/
theorem laplacian_quadForm_le_two_mul {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, deg A i = d)
    (x : V → ℝ) :
    quadForm (laplacian A) x ≤ 2 * d * Matrix.dotProduct x x := by
  have hsumcol : ∀ j : V, ∑ i, A i j = d := by
    intro j
    have h1 : ∑ i, A i j = ∑ i, A j i :=
      Finset.sum_congr rfl fun i _ => (hA.apply i j).symm
    rw [h1]
    exact hd j
  have hterm : ∀ i j : V,
      A i j * (x i - x j) ^ 2 ≤ A i j * (2 * (x i ^ 2 + x j ^ 2)) := by
    intro i j
    have h2 : (x i - x j) ^ 2 ≤ 2 * (x i ^ 2 + x j ^ 2) := by
      linarith [sq_nonneg (x i + x j)]
    exact mul_le_mul_of_nonneg_left h2 (hnn i j)
  have key1 : ∑ i, ∑ j, A i j * (2 * x i ^ 2)
      = 2 * d * Matrix.dotProduct x x := by
    have hstep : ∀ i, ∑ j, A i j * (2 * x i ^ 2)
        = deg A i * (2 * x i ^ 2) := by
      intro i
      simp only [deg]
      rw [Finset.sum_mul]
    calc ∑ i, ∑ j, A i j * (2 * x i ^ 2)
        = ∑ i, deg A i * (2 * x i ^ 2) :=
          Finset.sum_congr rfl fun i _ => hstep i
      _ = ∑ i, d * (2 * x i ^ 2) := Finset.sum_congr rfl fun i _ => by rw [hd i]
      _ = 2 * d * Matrix.dotProduct x x := by
          simp only [Matrix.dotProduct]
          rw [Finset.sum_congr rfl fun i _ => show d * (2 * x i ^ 2)
              = 2 * d * (x i * x i) from by ring, ← Finset.mul_sum]
  have key2 : ∑ i, ∑ j, A i j * (2 * x j ^ 2)
      = 2 * d * Matrix.dotProduct x x := by
    calc ∑ i, ∑ j, A i j * (2 * x j ^ 2)
        = ∑ j, ∑ i, A i j * (2 * x j ^ 2) := Finset.sum_comm
      _ = ∑ j, d * (2 * x j ^ 2) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Finset.sum_mul, ← hsumcol j]
      _ = 2 * d * Matrix.dotProduct x x := by
          simp only [Matrix.dotProduct]
          rw [Finset.sum_congr rfl fun j _ => show d * (2 * x j ^ 2)
              = 2 * d * (x j * x j) from by ring, ← Finset.mul_sum]
  have hsplit : ∑ i, ∑ j, A i j * (2 * (x i ^ 2 + x j ^ 2))
      = ∑ i, ∑ j, A i j * (2 * x i ^ 2)
        + ∑ i, ∑ j, A i j * (2 * x j ^ 2) := by
    simp only [mul_add, Finset.sum_add_distrib]
  calc quadForm (laplacian A) x
      = (∑ i, ∑ j, A i j * (x i - x j) ^ 2) / 2 := laplacian_quadForm A hA x
    _ ≤ (∑ i, ∑ j, A i j * (2 * (x i ^ 2 + x j ^ 2))) / 2 :=
        div_le_div_of_nonneg_right
          (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j)
          (by norm_num)
    _ = 2 * d * Matrix.dotProduct x x := by
        rw [hsplit, key1, key2]
        ring

/-- Every Laplacian eigenvalue is at most `2d` on a symmetric
nonnegative `d`-regular graph — the engine at the unit eigenvectors
(`λ_max = 2d` exactly on bipartite regular graphs). -/
theorem eigvalOf_laplacian_le_two_mul {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, deg A i = d)
    (k : V) :
    eigvalOf (laplacian A) (laplacian_symmetric A hA) k ≤ 2 * d := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hq := quadForm_eigvecOf_self hL k
  have hun : Matrix.dotProduct (eigvecOf (laplacian A) hL k)
      (eigvecOf (laplacian A) hL k) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner (laplacian A) hL k k
  have hle := laplacian_quadForm_le_two_mul hA hnn hd (eigvecOf (laplacian A) hL k)
  rw [hq, hun] at hle
  linarith

/-- **The packaged corollary at the family's certificate shape.** With
the walk family's own rate certificate `|1 - λ k / d| ≤ r` on the
decaying modes, the contrast bound holds at the explicit mode-rate
`2 d r ^ t` (via `λ ≤ 2d`). -/
theorem walkDistribution_pair_contrast_abs_le' {A : WAdj (V := V)} {d : ℝ}
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, deg A i = d)
    (hd0 : 0 < d) (hconn : (supportGraph A hA).Connected)
    (r : ℝ) (hr : 0 ≤ r) (t : ℕ) (x₁ x₂ y y' : V)
    (hrate : ∀ k : V, eigvalOf (laplacian A) (laplacian_symmetric A hA) k ≠ 0 →
      |1 - eigvalOf (laplacian A) (laplacian_symmetric A hA) k / d| ≤ r) :
    |(walkDistribution A t x₁ y - walkDistribution A t x₂ y)
      - (walkDistribution A t x₁ y' - walkDistribution A t x₂ y')|
      ≤ 2 * d * r ^ t * Real.sqrt (effectiveResistance A x₁ x₂)
          * Real.sqrt (effectiveResistance A y y') := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hlam : ∀ k : V, eigvalOf (laplacian A) hL k ≠ 0 →
      eigvalOf (laplacian A) hL k
        * |1 - eigvalOf (laplacian A) hL k / d| ^ t ≤ 2 * d * r ^ t := by
    intro k hk
    have h1 := eigvalOf_laplacian_le_two_mul hA hnn hd k
    have h2 : |1 - eigvalOf (laplacian A) hL k / d| ^ t ≤ r ^ t :=
      pow_le_pow_left₀ (abs_nonneg _) (hrate k hk) t
    exact mul_le_mul h1 h2 (pow_nonneg (abs_nonneg _) t)
      (mul_nonneg (by norm_num) (le_of_lt hd0))
  have hdnn : 0 ≤ d := le_of_lt hd0
  exact walkDistribution_pair_contrast_abs_le hA hnn hd (ne_of_gt hd0) hconn
    (2 * d * r ^ t) (mul_nonneg (mul_nonneg (by norm_num) hdnn)
      (pow_nonneg hr t)) t x₁ x₂ y y' hlam

end PairResistance

/-! ### The TV twin of the oversmoothing ceiling

The depth-form consumers of the total-variation mixing bound
(`proposals/total-variation-mixing-conversion.md`, delivered
2026-08-31): the field-standard statement of the oversmoothing
ceiling — past a computable depth, the propagated *distribution* is
within `ε` of stationarity in total variation (`t_mix(ε)`'s own
statement form), with the two-start `2ε` twin mirroring the entrywise
family's corollary. -/

/-- **The split-constant rate form** — `TV ≤ (1/2) · r ^ t · √C` with
`C = (π x)⁻¹ − 1 ≥ 0` (`stationaryVec_le_one`), the shape the
depth-form threshold consumes. -/
theorem walkDistribution_tvDistance_le_of_rate (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hconn : (supportGraph A hA).Connected) (r : ℝ)
    (hr : 0 ≤ r)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (t : ℕ) (x : V) :
    tvDistance (walkDistribution A t x) (stationaryVec A)
      ≤ (1/2) * r ^ t * Real.sqrt ((stationaryVec A x)⁻¹ - 1) := by
  have hC : 0 ≤ (stationaryVec A x)⁻¹ - 1 := by
    have h1 := stationaryVec_le_one A hd x
    have hpos := stationaryVec_pos A hd x
    have hinv := (one_le_inv₀ hpos).mpr h1
    linarith
  refine (walkDistribution_tvDistance_le_of_connected A hA hnn hd hconn r
    t x hrate).trans ?_
  rw [show r ^ (2 * t) = (r ^ t)^2 by rw [← pow_mul]; congr 1; ring,
    Real.sqrt_mul (sq_nonneg (r ^ t)) ((stationaryVec A x)⁻¹ - 1),
    Real.sqrt_sq (pow_nonneg hr t)]
  exact le_of_eq (by ring)

/-- **The TV twin of the oversmoothing ceiling**: past the TV
threshold depth `log (√C / (2ε)) / log (1/r)` (with
`C = (π x)⁻¹ − 1`), the walk law from `x` is within `ε` of the
stationary distribution *in total variation* — the field-standard
mixing statement (`t_mix(ε)` is TV-based), now expressible on this
shelf. The threshold is the entrywise ceiling's own with `ε` replaced
by `2ε`, exactly the factor the Cauchy–Schwarz conversion and the
`L¹` sum pay. -/
theorem walkDistribution_tvDistance_le_of_depth (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hconn : (supportGraph A hA).Connected) (r ε : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (t : ℕ) (x : V)
    (hthr : Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / (2 * ε))
      / Real.log (1 / r) ≤ (t : ℝ)) :
    tvDistance (walkDistribution A t x) (stationaryVec A) ≤ ε := by
  refine (walkDistribution_tvDistance_le_of_rate A hA hnn hd hconn r
    (le_of_lt hr) hrate t x).trans ?_
  have hthr' : Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / 2 / ε)
      / Real.log (1 / r) ≤ (t : ℝ) := by
    rw [show Real.sqrt ((stationaryVec A x)⁻¹ - 1) / 2 / ε
        = Real.sqrt ((stationaryVec A x)⁻¹ - 1) / (2 * ε) from by ring]
    exact hthr
  have hkey : r ^ t
      * (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / 2) ≤ ε :=
    pow_mul_le_of_log_threshold hr hr1
      (div_nonneg (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)) hε t
      hthr'
  have hring : (1/2) * r ^ t * Real.sqrt ((stationaryVec A x)⁻¹ - 1)
      = r ^ t * (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / 2) := by ring
  rw [hring]
  exact hkey

/-- **Two-start indistinguishability in total variation** — the TV
twin of the entrywise two-start corollary: past both starts' own TV
thresholds, the two `t`-step laws are within `2ε` of each other in
total variation. -/
theorem walkDistribution_tvDistance_sub_le_of_depth
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hconn : (supportGraph A hA).Connected) (r ε : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (t : ℕ) (x x' : V)
    (hthr : Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / (2 * ε))
      / Real.log (1 / r) ≤ (t : ℝ))
    (hthr' : Real.log (Real.sqrt ((stationaryVec A x')⁻¹ - 1) / (2 * ε))
      / Real.log (1 / r) ≤ (t : ℝ)) :
    tvDistance (walkDistribution A t x) (walkDistribution A t x')
      ≤ 2 * ε := by
  have h1 : tvDistance (walkDistribution A t x) (stationaryVec A)
      ≤ ε := walkDistribution_tvDistance_le_of_depth A hA hnn hd hconn r ε
    hr hr1 hε hrate t x hthr
  have h2 : tvDistance (stationaryVec A) (walkDistribution A t x')
      ≤ ε := by
    rw [tvDistance_symm]
    exact walkDistribution_tvDistance_le_of_depth A hA hnn hd hconn r ε
      hr hr1 hε hrate t x' hthr'
  calc tvDistance (walkDistribution A t x) (walkDistribution A t x')
      ≤ tvDistance (walkDistribution A t x) (stationaryVec A)
          + tvDistance (stationaryVec A) (walkDistribution A t x') :=
        tvDistance_triangle _ _ _
    _ ≤ ε + ε := add_le_add h1 h2
    _ = 2 * ε := by ring

/-! ## The discrete mixing time (the `t_mix` object) -/

/-- The **discrete mixing time** from `x` at threshold `ε`: the least
number of steps from which the walk law stays within `ε` of stationarity
in total variation — Levin–Peres–Wilmer ch. 20's `t_mix` reading for
the discrete walk, the twin of the delivered `contMixingTimeFrom`.
Per-start, mirroring the repo's per-start oversmoothing family; the
sup-over-starts uniform object is a trivial composition left
consumer-gated. Discrete TV monotonicity (`walkDistribution_tvDistance_anti`)
makes this the least `t` with `TV_t ≤ ε` as well — the witness set is
upward closed. Junk corner: at an unreachable `ε` the time set is empty
and `sInf ∅ = 0` on `ℕ` (`Nat.sInf_empty`) — no theorem below
instantiates there (the ceiling's `0 < r < 1` rate certificate is exactly
what periodic chains cannot discharge; see the `K₂` fence
`k2_mix_junk_corner_QA`). QA: the exact closed forms
`tri_mix_eq_third_QA`, `tri_mix_eq_sixth_QA`. -/
noncomputable def walkMixingTimeFrom (A : WAdj (V := V)) (x : V) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | ∀ s : ℕ, t ≤ s →
    tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε}

/-- The witness-time set is bounded below by `0` by construction. -/
theorem walkMixingTimeFrom_bddBelow (A : WAdj (V := V)) (x : V) (ε : ℝ) :
    BddBelow {t : ℕ | ∀ s : ℕ, t ≤ s →
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε} :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

/-- Any witness time certifies the mixing time: `∀ s ≥ T, TV ≤ ε` give
`t_mix(ε) ≤ T` — the reusable certificate interface, the discrete twin
of `contMixingTimeFrom_le_of_cert`. -/
theorem walkMixingTimeFrom_le_of_cert (A : WAdj (V := V)) (x : V)
    {ε : ℝ} (T : ℕ)
    (hT : ∀ s : ℕ, T ≤ s →
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε) :
    walkMixingTimeFrom A x ε ≤ T :=
  csInf_le (walkMixingTimeFrom_bddBelow A x ε) hT

/-- **The mixing time is attained** — the discrete object's own
specification, a fact the continuous twin cannot have: `ℕ` is
well-ordered, so the infimum of a nonempty witness set is a *member* of
it (`csInf_mem`), and membership is exactly the uniform bound. Given any
witness, `t_mix` itself satisfies `∀ s ≥ t_mix, TV_s ≤ ε` — this is the
statement that discharges the Poisson bridge transfer corollary's `hmix`
clause, closing the recorded consumer loop. -/
theorem walkMixingTimeFrom_spec (A : WAdj (V := V)) (x : V) {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s →
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε) :
    ∀ s : ℕ, walkMixingTimeFrom A x ε ≤ s →
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε :=
  csInf_mem hne

/-- **The spectral ceiling** — the field-standard discrete mixing bound
in ceiling form: under the depth-form TV certificate's own hypothesis
set (connected, rate certificate `0 < r < 1`),
`t_mix(ε) ≤ ⌈log(√C/(2ε))/log(1/r)⌉`. The honest strictness: the non-lazy
discrete walk never mixes on periodic chains, and no `r < 1` certificate
exists there (the `K₂` fence) — the hypothesis is load-bearing, not
decorative. The big-`ε` case is absorbed: a negative threshold ceilings
to `⌈·⌉ = 0`, and the depth certificate at `s = 0` carries it. QA: the
ceiling attained exactly on the triangle at `ε = √2/4`
(`tri_mix_ceiling_attained_QA`) and computed with honest slack at
`ε = 1/6` (`tri_mix_ceiling_slack_QA`). -/
theorem walkMixingTimeFrom_le_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hconn : (supportGraph A hA).Connected) (r ε : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (x : V) :
    walkMixingTimeFrom A x ε
      ≤ Nat.ceil (Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1)
          / (2 * ε)) / Real.log (1 / r)) := by
  set thr : ℝ := Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1)
    / (2 * ε)) / Real.log (1 / r) with hthrdef
  refine walkMixingTimeFrom_le_of_cert A x (Nat.ceil thr) ?_
  intro s hs
  exact walkDistribution_tvDistance_le_of_depth A hA hnn hd hconn r ε
    hr hr1 hε hrate s x
    (le_trans (Nat.le_ceil thr) (by exact_mod_cast hs))

/-- **ε-antitonicity**: a stricter threshold takes at least as long —
`t_mix(δ) ≤ t_mix(ε)` whenever `ε ≤ δ` and `ε` is reachable from `x`
(the witness hypothesis the connected ceiling always discharges).
Twin of `contMixingTimeFrom_anti`. QA: `tri_mix_anti_QA`. -/
theorem walkMixingTimeFrom_anti (A : WAdj (V := V)) (x : V) {ε δ : ℝ}
    (hεδ : ε ≤ δ)
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s →
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε) :
    walkMixingTimeFrom A x δ ≤ walkMixingTimeFrom A x ε :=
  csInf_le_csInf (walkMixingTimeFrom_bddBelow A x δ) hne
    (fun _ ht => fun s hs => (ht s hs).trans hεδ)

/-- **The bridge composition** — the discrete `t_mix` object's named
consumer: the Poisson-bridge transfer corollary with its `hmix` clause
*discharged by the object*. On a connected graph with a rate certificate
`0 < r < 1`, if the Poisson lower-tail weight below `t_mix(ε₁)` at time
`t` is at most `ε₂`, then the continuous walk is within `ε₁ + ε₂` of
stationarity at time `t`. The caller supplies only the Poisson tail —
the discrete certificate is the object's own attainment. QA:
`tri_bridge_mix_QA` re-derives `tri_mixing_transfer_QA`'s bound `5/24`
through this theorem with no hand-supplied certificate. -/
theorem contWalkDistribution_tvDistance_le_of_walkMixingTime
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) [Nonempty V]
    (hconn : (supportGraph A hA).Connected) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (x : V) {t : ℝ} (ht : 0 ≤ t)
    (htail : ∑ k in Finset.range (walkMixingTimeFrom A x ε₁),
        poissonWeight t k ≤ ε₂) :
    tvDistance (contWalkDistribution A t x) (stationaryVec A)
      ≤ ε₁ + ε₂ := by
  have hthr : Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1)
      / (2 * ε₁)) / Real.log (1 / r)
      ≤ ((Nat.ceil (Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1)
        / (2 * ε₁)) / Real.log (1 / r)) : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hwit : ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε₁ :=
    ⟨Nat.ceil _, fun s hs =>
      walkDistribution_tvDistance_le_of_depth A hA hnn hd hconn r ε₁
        hr hr1 hε₁ hrate s x
        (le_trans hthr (by exact_mod_cast hs))⟩
  exact contWalkDistribution_tvDistance_le_of_discreteMixing A hA hnn hd ht
    (walkMixingTimeFrom A x ε₁) x
    (walkMixingTimeFrom_spec A x hwit) htail
/-!
## The uniform mixing time and the submultiplicativity class

LPW ch. 20's field-standard worst-case-start reading of `t_mix`
(`walkMixingTime` — Montenegro–Tetali's distance `d̄`), together with
the submultiplicativity class that needs it: the two-start distance
`walkTVPair` (LPW's `d(t)`), the sharp Dobrushin contraction
`TV(μ(Pᵀ)ᵗ, ν(Pᵀ)ᵗ) ≤ TV(μ,ν) · d(t)` at equal masses, the classical
`d(s+t) ≤ d(s)d(t)` and `d̄(s+t) ≤ d̄(s)d(t)`, and the ε-escalation
corollary — one certified evaluation time yields every ε-level mixing
time (LPW's `t_mix := t_mix(1/4)` convention's engine). Pure hard
crust: no spectra, no connectivity anywhere in the contraction chain.
-/

section UniformMixing


omit [DecidableEq V] in
/-- **The pairing bound** — the engine of the sharp Dobrushin
contraction: for a zero-mass signed vector `c`, pairing the positive
and negative parts against any `g` bounds the pairing by *half* the
total absolute mass times the oscillation bound `D` of `g`. The
recentering at a minimum of `g` (which exists: `V` is finite) is what
makes the positive-part split valid; the naive triangle route loses a
factor of `2` exactly here. Sharp: at `c = (1, −1)`, `g = (0, 1)` the
bound is attained. -/
private theorem abs_sum_mul_le_of_pairwise [Nonempty V] {c g : V → ℝ}
    {D : ℝ} (hD : ∀ z z', |g z - g z'| ≤ D) (hc : ∑ z, c z = 0) :
    |∑ z, c z * g z| ≤ ((∑ z, |c z|) / 2) * D := by
  obtain ⟨z₀, hz₀⟩ := Finite.exists_min (α := V) g
  have hm : ∀ z, 0 ≤ g z - g z₀ := fun z => sub_nonneg.2 (hz₀ z)
  have hD' : ∀ z, g z - g z₀ ≤ D := fun z =>
    le_trans (le_abs_self _) (hD z z₀)
  have hone : ∀ cc : V → ℝ, ∑ z, cc z = 0 →
      ∑ z, cc z * g z ≤ ((∑ z, |cc z|) / 2) * D := by
    intro cc hcc
    have hzero : ∑ z, cc z * g z₀ = 0 := by
      rw [← Finset.sum_mul, hcc]
      ring
    have hrc : ∑ z, cc z * g z = ∑ z, cc z * (g z - g z₀) := by
      have heq : ∑ z, cc z * (g z - g z₀)
          = ∑ z, cc z * g z - ∑ z, cc z * g z₀ := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun z _ => by ring
      rw [heq, hzero, sub_zero]
    rw [hrc]
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset V) (fun z => 0 < cc z)
      (fun z => cc z * (g z - g z₀))
    have hneg : ∑ z ∈ (Finset.univ : Finset V).filter (fun z => ¬ 0 < cc z),
          cc z * (g z - g z₀) ≤ 0 := by
      refine Finset.sum_nonpos fun z hz => ?_
      have hcz : cc z ≤ 0 := by simpa [Finset.mem_filter] using hz
      rw [mul_comm]
      exact mul_nonpos_of_nonneg_of_nonpos (hm z) hcz
    have hpossum : ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
          cc z = (∑ z, |cc z|) / 2 := by
      have hposabs : ∑ z ∈ (Finset.univ : Finset V).filter
            (fun z => 0 < cc z), |cc z|
          = ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z), cc z :=
        Finset.sum_congr rfl fun z hz =>
          abs_of_pos (by simpa [Finset.mem_filter] using hz)
      have hnegabs : ∑ z ∈ (Finset.univ : Finset V).filter
            (fun z => ¬ 0 < cc z), |cc z|
          = ∑ z ∈ (Finset.univ : Finset V).filter (fun z => ¬ 0 < cc z),
              (-cc z) := by
        refine Finset.sum_congr rfl fun z hz => ?_
        have hcz : cc z ≤ 0 := by simpa [Finset.mem_filter] using hz
        rw [abs_of_nonpos hcz]
      have hsum := Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset V) (fun z => 0 < cc z) (fun z => |cc z|)
      have huniv : ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
            cc z + ∑ z ∈ (Finset.univ : Finset V).filter
              (fun z => ¬ 0 < cc z), cc z = 0 := by
        rw [Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset V) (fun z => 0 < cc z) cc]
        exact hcc
      have hnegsum : ∑ z ∈ (Finset.univ : Finset V).filter
            (fun z => ¬ 0 < cc z), (-cc z)
          = ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
              cc z := by
        rw [Finset.sum_neg_distrib]
        have hpair : ∑ z ∈ (Finset.univ : Finset V).filter
              (fun z => ¬ 0 < cc z), cc z
            = -∑ z ∈ (Finset.univ : Finset V).filter
              (fun z => 0 < cc z), cc z := by linarith [huniv]
        rw [hpair]
        exact neg_neg _
      rw [← hsum, hposabs, hnegabs, hnegsum]
      ring
    have hle : ∑ z, cc z * (g z - g z₀)
        ≤ ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
          cc z * (g z - g z₀) := by linarith [hsplit, hneg]
    calc ∑ z, cc z * (g z - g z₀)
        ≤ ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
              cc z * (g z - g z₀) := hle
      _ ≤ ∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
              cc z * D :=
          Finset.sum_le_sum fun z hz =>
            mul_le_mul_of_nonneg_left (hD' z)
              (le_of_lt (by simpa [Finset.mem_filter] using hz : 0 < cc z))
      _ = (∑ z ∈ (Finset.univ : Finset V).filter (fun z => 0 < cc z),
              cc z) * D := by
          rw [← Finset.sum_mul]
      _ = ((∑ z, |cc z|) / 2) * D := by rw [hpossum]
  have hmain := hone c hc
  have hnegc : ∑ z, (-c z) = 0 := by
    rw [Finset.sum_neg_distrib, hc, neg_zero]
  have hmain' := hone (-c) hnegc
  have habsneg : ∑ z, |(-c) z| = ∑ z, |c z| :=
    Finset.sum_congr rfl fun z _ => abs_neg _
  rw [habsneg] at hmain'
  have hval : ∑ z, (-c z) * g z = -∑ z, c z * g z := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun z _ => by ring
  simp only [Pi.neg_apply] at hmain'
  rw [hval] at hmain'
  exact abs_le.2 ⟨by linarith, hmain⟩

/-- **The two-start walk distance** — Levin–Peres–Wilmer's `d(t)`: the
worst-case total-variation distance between the `t`-step laws from two
starts, `d(t) = max_{x,y} TV(ν_t^x, ν_t^y)`. The distance the
submultiplicativity class lives on; on a finite type it is a genuine
maximum (`Finset.sup'`). -/
noncomputable def walkTVPair (A : WAdj (V := V)) [Nonempty V] (t : ℕ) : ℝ :=
  (Finset.univ : Finset (V × V)).sup'
    ⟨(‹Nonempty V›.some, ‹Nonempty V›.some), Finset.mem_univ _⟩ fun p =>
    tvDistance (walkDistribution A t p.1) (walkDistribution A t p.2)

/-- **The worst-start walk distance** — the `d̄(t)` of the mixing
literature: the worst-case total-variation distance from the `t`-step
law to stationarity, `d̄(t) = max_x TV(ν_t^x, π)` — Montenegro–Tetali's
distance, the one whose threshold curve *is* the mixing time. -/
noncomputable def walkTVUniform (A : WAdj (V := V)) [Nonempty V] (t : ℕ) : ℝ :=
  (Finset.univ : Finset V).sup'
    ⟨‹Nonempty V›.some, Finset.mem_univ _⟩ fun x =>
    tvDistance (walkDistribution A t x) (stationaryVec A)

/-- Both distances are nonnegative — the pointwise terms are. -/
theorem walkTVPair_nonneg (A : WAdj (V := V)) [Nonempty V] (t : ℕ) :
    0 ≤ walkTVPair A t :=
  le_trans (tvDistance_nonneg _ _)
    (Finset.le_sup' (f := fun p : V × V =>
      tvDistance (walkDistribution A t p.1) (walkDistribution A t p.2))
      (Finset.mem_univ (‹Nonempty V›.some, ‹Nonempty V›.some)))

theorem walkTVUniform_nonneg (A : WAdj (V := V)) [Nonempty V] (t : ℕ) :
    0 ≤ walkTVUniform A t :=
  le_trans (tvDistance_nonneg (walkDistribution A t ‹Nonempty V›.some)
      (stationaryVec A))
    (Finset.le_sup' (f := fun x =>
      tvDistance (walkDistribution A t x) (stationaryVec A))
      (Finset.mem_univ ‹Nonempty V›.some))

omit [DecidableEq V] in
/-- **The Dobrushin core at a sign statistic** — evolved TV through
the pairing, at the statistic the caller supplies: `2 · TV(Mμ, Mν)`
is the ℓ¹ norm of the evolved difference, evaluated through the sign
statistic `s` as a pairing `∑ (μ − ν) g` against the evolved
statistic `g`, then paired (the private pairing lemma above) against
`g`'s oscillation bound `D`. -/
private theorem tvDistance_mulVec_le_pair [Nonempty V]
    {M : Matrix V V ℝ} {μ ν : V → ℝ} (s : V → ℝ)
    (hsval : ∀ w, s w * ((M *ᵥ (μ - ν)) w) = |((M *ᵥ (μ - ν)) w)|)
    (D : ℝ) (hosc : ∀ z z' : V,
      |∑ w, M w z * s w - ∑ w, M w z' * s w| ≤ D)
    (hmass : ∑ i, μ i = ∑ i, ν i) :
    tvDistance (M *ᵥ μ) (M *ᵥ ν) ≤ tvDistance μ ν * (D / 2) := by
  have hmass0 : ∑ z, (μ - ν) z = 0 := by
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib, hmass, sub_self]
  have hpairing : ∑ w, |((M *ᵥ (μ - ν)) w)|
      = ∑ z, (μ - ν) z * (∑ w, M w z * s w) := by
    calc ∑ w, |((M *ᵥ (μ - ν)) w)|
        = ∑ w, s w * ((M *ᵥ (μ - ν)) w) :=
          Finset.sum_congr rfl fun w _ => (hsval w).symm
      _ = ∑ w, ∑ z, s w * (M w z * (μ - ν) z) := by
          refine Finset.sum_congr rfl fun w _ => ?_
          simp only [Matrix.mulVec, Matrix.dotProduct]
          rw [Finset.mul_sum]
      _ = ∑ z, ∑ w, s w * (M w z * (μ - ν) z) := Finset.sum_comm
      _ = ∑ z, (μ - ν) z * (∑ w, M w z * s w) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => by ring
  have hp := abs_sum_mul_le_of_pairwise (c := μ - ν)
    (g := fun z => ∑ w, M w z * s w) hosc hmass0
  have hL1 : ∑ z, |(μ - ν) z| = 2 * tvDistance μ ν := by
    simp only [Pi.sub_apply, tvDistance]
    ring
  have hsplit : ∀ w : V, (M *ᵥ μ) w - (M *ᵥ ν) w = ((M *ᵥ (μ - ν)) w) := by
    intro w
    rw [← Pi.sub_apply, Matrix.mulVec_sub]
  calc tvDistance (M *ᵥ μ) (M *ᵥ ν)
      = (1 / 2) * ∑ w, |((M *ᵥ (μ - ν)) w)| := by
          rw [tvDistance]
          congr 1
          exact Finset.sum_congr rfl fun w _ => by rw [hsplit w]
    _ = (1 / 2) * ∑ z, (μ - ν) z * (∑ w, M w z * s w) := by
          rw [hpairing]
    _ ≤ (1 / 2) * |∑ z, (μ - ν) z * (∑ w, M w z * s w)| := by
          exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ (1 / 2) * (((∑ z, |(μ - ν) z|) / 2) * D) := by
          exact mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = tvDistance μ ν * (D / 2) := by
          rw [hL1]
          ring

/-- **The sharp Dobrushin contraction** — the engine of the whole
submultiplicativity class: applying the `t`-step walk evolution to two
equal-mass vectors contracts their TV distance by the two-start
distance `d(t)` itself, `TV(μ(Pᵀ)ᵗ, ν(Pᵀ)ᵗ) ≤ TV(μ, ν) · d(t)`.
Hypothesis-minimal — no stochasticity, no signs, only equal masses
(the recentering mass-zero condition). Proof: the sign statistic of
the evolved difference, transported to a pairing against the evolved
statistic whose oscillation is bounded by `2 d(t)` through the
delivered distinguishing-function bound (`|s| ≤ 1`), closed by the
private pairing core. -/
theorem tvDistance_pow_walkTransitionMatrixTranspose_mulVec_le
    (A : WAdj (V := V)) [Nonempty V] (t : ℕ) (μ ν : V → ℝ)
    (hmass : ∑ i, μ i = ∑ i, ν i) :
    tvDistance ((walkTransitionMatrix A)ᵀ ^ t *ᵥ μ)
        ((walkTransitionMatrix A)ᵀ ^ t *ᵥ ν)
      ≤ tvDistance μ ν * walkTVPair A t := by
  have hrow : ∀ (z w : V), walkDistribution A t z w
      = ((walkTransitionMatrix A)ᵀ ^ t) w z := by
    intro z w
    rw [walkDistribution]
    simp [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply]
  set s : V → ℝ :=
    fun w => if 0 ≤ (((walkTransitionMatrix A)ᵀ ^ t) *ᵥ (μ - ν)) w then 1 else -1 with hsdef
  have hsabs : ∀ w, |s w| ≤ 1 := by
    intro w
    by_cases h : 0 ≤ (((walkTransitionMatrix A)ᵀ ^ t) *ᵥ (μ - ν)) w
    · simp only [hsdef, if_pos h]
      norm_num
    · simp only [hsdef, if_neg h]
      norm_num
  have hsval : ∀ w, s w * (((walkTransitionMatrix A)ᵀ ^ t) *ᵥ (μ - ν)) w
      = |(((walkTransitionMatrix A)ᵀ ^ t) *ᵥ (μ - ν)) w| := by
    intro w
    by_cases h : 0 ≤ (((walkTransitionMatrix A)ᵀ ^ t) *ᵥ (μ - ν)) w
    · simp only [hsdef, if_pos h, abs_of_nonneg h]
      ring
    · simp only [hsdef, if_neg h, abs_of_neg (lt_of_not_ge h)]
      ring
  have hosc : ∀ z z' : V,
      |(∑ w, ((walkTransitionMatrix A)ᵀ ^ t) w z * s w)
        - ∑ w, ((walkTransitionMatrix A)ᵀ ^ t) w z' * s w|
        ≤ 2 * walkTVPair A t := by
    intro z z'
    have hgg : (∑ w, ((walkTransitionMatrix A)ᵀ ^ t) w z * s w)
        - ∑ w, ((walkTransitionMatrix A)ᵀ ^ t) w z' * s w
        = ∑ w, (walkDistribution A t z w - walkDistribution A t z' w) * s w := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hrow z w, hrow z' w]
      ring
    have hd := tvDistance_ge_half_abs_sum
      (μ := walkDistribution A t z) (ν := walkDistribution A t z') s hsabs
    rw [hgg]
    have hsup : tvDistance (walkDistribution A t z)
        (walkDistribution A t z') ≤ walkTVPair A t :=
      Finset.le_sup'
        (f := fun p : V × V =>
          tvDistance (walkDistribution A t p.1) (walkDistribution A t p.2))
        (Finset.mem_univ (z, z'))
    calc |∑ w, (walkDistribution A t z w - walkDistribution A t z' w) * s w|
        ≤ 2 * tvDistance (walkDistribution A t z)
            (walkDistribution A t z') := by linarith
      _ ≤ 2 * walkTVPair A t := mul_le_mul_of_nonneg_left hsup (by norm_num)
  have hcore := tvDistance_mulVec_le_pair
    (M := (walkTransitionMatrix A)ᵀ ^ t) s hsval (2 * walkTVPair A t) hosc hmass
  calc tvDistance ((walkTransitionMatrix A)ᵀ ^ t *ᵥ μ)
        ((walkTransitionMatrix A)ᵀ ^ t *ᵥ ν)
      ≤ tvDistance μ ν * (2 * walkTVPair A t / 2) := hcore
    _ = tvDistance μ ν * walkTVPair A t := by ring


/-- **Submultiplicativity of the two-start distance** — LPW's
classical `d(s + t) ≤ d(s) · d(t)`: the Dobrushin contraction
instantiated at the pair of `s`-step laws, with the equal-mass
hypothesis discharged by mass conservation of the walk evolution. No
connectivity, no rates — pure Markovity. -/
theorem walkTVPair_submul (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (s t : ℕ) :
    walkTVPair A (s + t) ≤ walkTVPair A s * walkTVPair A t := by
  refine Finset.sup'_le
    (⟨(‹Nonempty V›.some, ‹Nonempty V›.some), Finset.mem_univ _⟩ :
      (Finset.univ : Finset (V × V)).Nonempty)
    (f := fun p : V × V =>
      tvDistance (walkDistribution A (s + t) p.1)
        (walkDistribution A (s + t) p.2))
    ?_
  intro p _
  have hev1 : walkDistribution A (s + t) p.1
      = (walkTransitionMatrix A)ᵀ ^ t *ᵥ walkDistribution A s p.1 :=
    walkDistribution_add A s t p.1
  have hev2 : walkDistribution A (s + t) p.2
      = (walkTransitionMatrix A)ᵀ ^ t *ᵥ walkDistribution A s p.2 :=
    walkDistribution_add A s t p.2
  have hmass : ∑ i, walkDistribution A s p.1 i
      = ∑ i, walkDistribution A s p.2 i := by
    rw [sum_walkDistribution A hd s p.1, sum_walkDistribution A hd s p.2]
  calc tvDistance (walkDistribution A (s + t) p.1)
          (walkDistribution A (s + t) p.2)
        = tvDistance ((walkTransitionMatrix A)ᵀ ^ t *ᵥ walkDistribution A s p.1)
            ((walkTransitionMatrix A)ᵀ ^ t *ᵥ walkDistribution A s p.2) := by
          rw [hev1, hev2]
      _ ≤ tvDistance (walkDistribution A s p.1) (walkDistribution A s p.2)
            * walkTVPair A t :=
          tvDistance_pow_walkTransitionMatrixTranspose_mulVec_le A t _ _ hmass
      _ ≤ walkTVPair A s * walkTVPair A t := by
          refine mul_le_mul_of_nonneg_right ?_ (walkTVPair_nonneg A t)
          exact Finset.le_sup'
            (f := fun p : V × V =>
              tvDistance (walkDistribution A s p.1) (walkDistribution A s p.2))
            (Finset.mem_univ p)

/-- **The stationary mixture identity** — stationarity read as: `π` is
the `π`-weighted mixture of the `t`-step laws (its own defining
fixed-point property, expanded through the evolution's linearity). The
engine of `d̄ ≤ d`. -/
theorem stationaryVec_eq_sum_smul_walkDistribution
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (t : ℕ) :
    ∑ y, stationaryVec A y • walkDistribution A t y = stationaryVec A := by
  have hlin : (walkTransitionMatrix A)ᵀ ^ t *ᵥ
        (∑ y, stationaryVec A y • (Pi.single y (1 : ℝ) : V → ℝ))
      = ∑ y, stationaryVec A y • ((walkTransitionMatrix A)ᵀ ^ t
          *ᵥ (Pi.single y (1 : ℝ) : V → ℝ)) := by
    funext w
    simp only [Matrix.mulVec, Matrix.dotProduct, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ =>
      Finset.sum_congr rfl fun x _ => by ring
  have hmass : ∑ y, stationaryVec A y • (Pi.single y (1 : ℝ) : V → ℝ)
      = stationaryVec A := by
    funext w
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc ∑ y, stationaryVec A y • walkDistribution A t y
      = ∑ y, stationaryVec A y • ((walkTransitionMatrix A)ᵀ ^ t
            *ᵥ (Pi.single y (1 : ℝ) : V → ℝ)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [walkDistribution]
    _ = (walkTransitionMatrix A)ᵀ ^ t *ᵥ
          (∑ y, stationaryVec A y • (Pi.single y (1 : ℝ) : V → ℝ)) := hlin.symm
    _ = (walkTransitionMatrix A)ᵀ ^ t *ᵥ stationaryVec A := by rw [hmass]
    _ = stationaryVec A :=
        walkTransitionMatrixTranspose_pow_mulVec_stationaryVec A hA hd t

omit [DecidableEq V] in
/-- **Finite TV convexity in mixtures**: the TV distance to a convex
combination dominates the convex combination of the TV distances —
the finite form of the Poisson bridge's countable convexity, proved
directly by the pointwise triangle inequality. -/
private theorem tvDistance_le_sum_smul {ν : V → ℝ} {w : V → ℝ} {μ : V → V → ℝ}
    (hw : ∀ y, 0 ≤ w y) (hw1 : ∑ y, w y = 1) :
    tvDistance ν (∑ y, w y • μ y) ≤ ∑ y, w y * tvDistance ν (μ y) := by
  have hpt : ∀ w' : V, ν w' - (∑ y, w y • μ y) w'
      = ∑ y, w y * (ν w' - μ y w') := by
    intro w'
    have h1 : (∑ y, w y • μ y) w' = ∑ y, w y * μ y w' := by
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun y _ => by rw [Pi.smul_apply, smul_eq_mul]
    have h2 : ∑ y, w y * (ν w' - μ y w')
        = (∑ y, w y) * ν w' - ∑ y, w y * μ y w' := by
      have hsplit : ∑ y, w y * (ν w' - μ y w')
          = ∑ y, (w y * ν w' - w y * μ y w') :=
        Finset.sum_congr rfl fun y _ => (mul_sub _ _ _)
      rw [hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [h1, h2, hw1, one_mul]
  have hterm : ∀ (y w' : V), |w y * (ν w' - μ y w')| = w y * |ν w' - μ y w'| := by
    intro y w'
    rw [abs_mul, abs_of_nonneg (hw y)]
  calc tvDistance ν (∑ y, w y • μ y)
      = (1 / 2) * ∑ w', |∑ y, w y * (ν w' - μ y w')| := by
          rw [tvDistance]
          congr 1
          exact Finset.sum_congr rfl fun w' _ => by rw [hpt w']
    _ ≤ (1 / 2) * ∑ w', ∑ y, |w y * (ν w' - μ y w')| := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Finset.sum_le_sum fun w' _ => Finset.abs_sum_le_sum_abs _ _
    _ = (1 / 2) * ∑ y, ∑ w', w y * |ν w' - μ y w'| := by
          refine congrArg ((1 / 2) * ·) ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun y _ =>
            Finset.sum_congr rfl fun w' _ => by rw [hterm y w']
    _ = (1 / 2) * ∑ y, w y * (∑ w', |ν w' - μ y w'|) := by
          refine congrArg ((1 / 2) * ·) ?_
          exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
    _ ≤ (1 / 2) * ∑ y, w y * (2 * tvDistance ν (μ y)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          exact Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (le_of_eq (by
              simp only [Pi.sub_apply, tvDistance]
              ring)) (hw y)
    _ = ∑ y, w y * tvDistance ν (μ y) := by
          calc (1 / 2 : ℝ) * ∑ y, w y * (2 * tvDistance ν (μ y))
              = (1 / 2 : ℝ) * ((∑ y, w y * tvDistance ν (μ y)) * 2) := by
                  have hterm2 : ∑ y, w y * (2 * tvDistance ν (μ y))
                      = (∑ y, w y * tvDistance ν (μ y)) * 2 := by
                    rw [Finset.sum_mul]
                    exact Finset.sum_congr rfl fun y _ => by ring
                  rw [hterm2]
            _ = ∑ y, w y * tvDistance ν (μ y) := by ring

/-- **The worst-start distance is dominated by the two-start
distance** — the classical `d̄(t) ≤ d(t)`: the TV distance to the
stationary mixture is at most the mixture of the pairwise TV
distances (`d̄` vs `d` need no reversibility here — the mixture reads
`π` as a stationary combination of the laws). -/
theorem walkTVUniform_le_walkTVPair (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ) :
    walkTVUniform A t ≤ walkTVPair A t := by
  have hnnπ : ∀ y, 0 ≤ stationaryVec A y := fun y =>
    le_of_lt (stationaryVec_pos A hd y)
  have hstat : ∑ y, stationaryVec A y • walkDistribution A t y
      = stationaryVec A :=
    stationaryVec_eq_sum_smul_walkDistribution A hA hd t
  refine Finset.sup'_le
    (⟨‹Nonempty V›.some, Finset.mem_univ _⟩ :
      (Finset.univ : Finset V).Nonempty)
    (f := fun x => tvDistance (walkDistribution A t x) (stationaryVec A))
    fun x _ => ?_
  have hcvx := tvDistance_le_sum_smul (ν := walkDistribution A t x)
    (w := stationaryVec A) (μ := walkDistribution A t) hnnπ
    (sum_stationaryVec A hd)
  rw [hstat] at hcvx
  calc tvDistance (walkDistribution A t x) (stationaryVec A)
      ≤ ∑ y, stationaryVec A y * tvDistance (walkDistribution A t x)
            (walkDistribution A t y) := hcvx
    _ ≤ ∑ y, stationaryVec A y * walkTVPair A t := by
          exact Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
            (Finset.le_sup'
              (f := fun p : V × V =>
                tvDistance (walkDistribution A t p.1)
                  (walkDistribution A t p.2))
              (Finset.mem_univ (x, y))) (hnnπ y)
    _ = (∑ y, stationaryVec A y) * walkTVPair A t := by rw [Finset.sum_mul]
    _ = walkTVPair A t := by rw [sum_stationaryVec A hd, one_mul]

/-- **The mixed submultiplicativity** — the classical companion
`d̄(s + t) ≤ d̄(s) · d(t)`: the Dobrushin contraction with the
stationary vector as the second argument (both masses one — the walk
law's by conservation, stationarity's by construction). -/
theorem walkTVUniform_mul_walkTVPair_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) [Nonempty V] (s t : ℕ) :
    walkTVUniform A (s + t) ≤ walkTVUniform A s * walkTVPair A t := by
  refine Finset.sup'_le
    (⟨‹Nonempty V›.some, Finset.mem_univ _⟩ :
      (Finset.univ : Finset V).Nonempty)
    (f := fun x =>
      tvDistance (walkDistribution A (s + t) x) (stationaryVec A))
    fun x _ => ?_
  have hev : walkDistribution A (s + t) x
      = (walkTransitionMatrix A)ᵀ ^ t *ᵥ walkDistribution A s x :=
    walkDistribution_add A s t x
  have hstat : (walkTransitionMatrix A)ᵀ ^ t *ᵥ stationaryVec A
      = stationaryVec A :=
    walkTransitionMatrixTranspose_pow_mulVec_stationaryVec A hA hd t
  have hmass : ∑ i, walkDistribution A s x i = ∑ i, stationaryVec A i := by
    rw [sum_walkDistribution A hd s x, sum_stationaryVec A hd]
  calc tvDistance (walkDistribution A (s + t) x) (stationaryVec A)
      = tvDistance ((walkTransitionMatrix A)ᵀ ^ t *ᵥ walkDistribution A s x)
            ((walkTransitionMatrix A)ᵀ ^ t *ᵥ stationaryVec A) := by
          rw [hev, hstat]
    _ ≤ tvDistance (walkDistribution A s x) (stationaryVec A)
          * walkTVPair A t :=
        tvDistance_pow_walkTransitionMatrixTranspose_mulVec_le A t _ _ hmass
    _ ≤ walkTVUniform A s * walkTVPair A t := by
          refine mul_le_mul_of_nonneg_right ?_ (walkTVPair_nonneg A t)
          exact Finset.le_sup'
            (f := fun x =>
              tvDistance (walkDistribution A s x) (stationaryVec A))
            (Finset.mem_univ x)

/-- **The escalation engine** — `d̄((k + 1)·t₀) ≤ d̄(t₀) · d(t₀)^k`: the
mixed submultiplicativity iterated, the certificate-free geometric
decay powering the ε-escalation corollary. -/
theorem walkTVUniform_succ_mul_le (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) [Nonempty V] (k t₀ : ℕ) :
    walkTVUniform A ((k + 1) * t₀)
      ≤ walkTVUniform A t₀ * (walkTVPair A t₀) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hsplit : (k + 1 + 1) * t₀ = (k + 1) * t₀ + t₀ := by ring
    rw [hsplit]
    calc walkTVUniform A ((k + 1) * t₀ + t₀)
        ≤ walkTVUniform A ((k + 1) * t₀) * walkTVPair A t₀ :=
          walkTVUniform_mul_walkTVPair_le A hA hd ((k + 1) * t₀) t₀
      _ ≤ (walkTVUniform A t₀ * (walkTVPair A t₀) ^ k) * walkTVPair A t₀ :=
          mul_le_mul_of_nonneg_right ih (walkTVPair_nonneg A t₀)
      _ = walkTVUniform A t₀ * (walkTVPair A t₀) ^ (k + 1) := by
          rw [pow_succ, mul_assoc]


/-! ### The uniform mixing-time object -/

/-- **The uniform mixing time** — Levin–Peres–Wilmer's `t_mix(ε)`
itself, at its field-standard reading (Montenegro–Tetali's distance):
the least number of steps from which *every* start's walk law stays
within `ε` of stationarity in total variation — the worst-case-start
twin of the delivered per-start `walkMixingTimeFrom`. Junk corner: at
an unreachable `ε` the time set is empty and `sInf ∅ = 0` on `ℕ` (the
`K₂` fence below pins and fences this). On a finite type the object is
the worst start's per-start mixing time
(`walkMixingTime_eq_sup_walkMixingTimeFrom`). -/
noncomputable def walkMixingTime (A : WAdj (V := V)) (ε : ℝ) : ℕ :=
  sInf {t : ℕ | ∀ s : ℕ, t ≤ s → ∀ x : V,
    tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε}

/-- The witness-time set is bounded below by `0` by construction. -/
theorem walkMixingTime_bddBelow (A : WAdj (V := V)) (ε : ℝ) :
    BddBelow {t : ℕ | ∀ s : ℕ, t ≤ s → ∀ x : V,
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε} :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

/-- Per-start times are dominated by the uniform time, *given a
uniform witness*: the worst start takes at least as long as any single
start (set inclusion — the uniform predicate implies the per-start
one). The witness hypothesis is load-bearing, not decorative: at the
junk corner (no uniform witness, `sInf ∅ = 0`) the inequality can
fail — a graph mixing on one component while another stays periodic
has genuinely-mixing per-start times against a junk-`0` uniform
object, so the un-witnessed statement is false there and no theorem
below instantiates without a witness (the escalation and the connected
ceiling both supply one). -/
theorem walkMixingTimeFrom_le_walkMixingTime (A : WAdj (V := V))
    (x : V) {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s → ∀ y : V,
      tvDistance (walkDistribution A s y) (stationaryVec A) ≤ ε) :
    walkMixingTimeFrom A x ε ≤ walkMixingTime A ε := by
  obtain ⟨t, ht⟩ := hne
  exact csInf_le_csInf (walkMixingTimeFrom_bddBelow A x ε)
    ⟨t, ht⟩ (fun t' ht' s hs => ht' s hs x)

/-- Any uniform witness time certifies the uniform mixing time. -/
theorem walkMixingTime_le_of_cert (A : WAdj (V := V)) {ε : ℝ} (T : ℕ)
    (hT : ∀ s : ℕ, T ≤ s → ∀ x : V,
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε) :
    walkMixingTime A ε ≤ T :=
  csInf_le (walkMixingTime_bddBelow A ε) hT

/-- **The uniform mixing time is attained** — `ℕ` is well-ordered, so
given any witness the infimum is a member, and membership is the
uniform bound (the statement the escalation corollary composes). -/
theorem walkMixingTime_spec (A : WAdj (V := V)) {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s → ∀ x : V,
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε) :
    ∀ s : ℕ, walkMixingTime A ε ≤ s → ∀ x : V,
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε :=
  csInf_mem hne

/-- **The uniform object is the worst start's per-start object** — on
a finite type the sup over starts commutes with the infimum over
times, through each per-start attainment (given any uniform witness).
Hypothesis-light: no graph structure at all. -/
theorem walkMixingTime_eq_sup_walkMixingTimeFrom (A : WAdj (V := V))
    [Nonempty V] {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s → ∀ x : V,
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε) :
    walkMixingTime A ε = (Finset.univ : Finset V).sup'
      ⟨‹Nonempty V›.some, Finset.mem_univ _⟩
      (fun x => walkMixingTimeFrom A x ε) := by
  obtain ⟨t₀, ht₀⟩ := hne
  refine le_antisymm ?_ ?_
  · refine walkMixingTime_le_of_cert A _ fun s hs x => ?_
    have hxle : walkMixingTimeFrom A x ε ≤ s := by
      have h1 : walkMixingTimeFrom A x ε
          ≤ (Finset.univ : Finset V).sup'
            ⟨‹Nonempty V›.some, Finset.mem_univ _⟩
            (fun y => walkMixingTimeFrom A y ε) :=
        Finset.le_sup' (f := fun y => walkMixingTimeFrom A y ε)
          (Finset.mem_univ x)
      exact le_trans h1 hs
    exact walkMixingTimeFrom_spec A x ⟨t₀, fun s' hs' => ht₀ s' hs' x⟩ s hxle
  · refine Finset.sup'_le
      (⟨‹Nonempty V›.some, Finset.mem_univ _⟩ :
        (Finset.univ : Finset V).Nonempty)
      (f := fun x => walkMixingTimeFrom A x ε) fun x _ => ?_
    exact walkMixingTimeFrom_le_walkMixingTime A x ⟨t₀, ht₀⟩

/-- **The ε-escalation corollary** — the submultiplicativity class's
consumer capstone: one evaluation time `t₀` with both distances
certified (`d̄(t₀) ≤ ε₀`, `d(t₀) ≤ ρ < 1`) yields *every* ε-level
mixing time — `t_mix(ε) ≤ (k + 1) · t₀` whenever `ε₀ · ρᵏ ≤ ε`. This
is LPW's canonical bridge from a single certified evaluation (the
`t_mix := t_mix(1/4)` convention) to arbitrary accuracy, and the
statement that needs the *uniform* object: per-start escalation is
not this (the worst start's certificate is what iterates). -/
theorem walkMixingTime_le_mul_of_escalation (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] {ε ε₀ ρ : ℝ} (t₀ k : ℕ)
    (hunif : walkTVUniform A t₀ ≤ ε₀) (hpair : walkTVPair A t₀ ≤ ρ)
    (hk : ε₀ * ρ ^ k ≤ ε) :
    walkMixingTime A ε ≤ (k + 1) * t₀ := by
  refine walkMixingTime_le_of_cert A _ fun s hs x => ?_
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hs
  have hpow : (walkTVPair A t₀) ^ k ≤ ρ ^ k :=
    pow_le_pow_left₀ (walkTVPair_nonneg A t₀) hpair k
  have hesc := walkTVUniform_succ_mul_le A hA hd k t₀
  have hsup : tvDistance (walkDistribution A ((k + 1) * t₀) x)
      (stationaryVec A) ≤ walkTVUniform A ((k + 1) * t₀) :=
    Finset.le_sup' (f := fun x =>
      tvDistance (walkDistribution A ((k + 1) * t₀) x) (stationaryVec A))
      (Finset.mem_univ x)
  rw [hj]
  calc tvDistance (walkDistribution A ((k + 1) * t₀ + j) x)
          (stationaryVec A)
      ≤ tvDistance (walkDistribution A ((k + 1) * t₀) x)
          (stationaryVec A) :=
        walkDistribution_tvDistance_anti A hA hnn hd ((k + 1) * t₀) j x
    _ ≤ walkTVUniform A ((k + 1) * t₀) := hsup
    _ ≤ walkTVUniform A t₀ * (walkTVPair A t₀) ^ k := hesc
    _ ≤ ε₀ * ρ ^ k :=
        mul_le_mul hunif hpow (pow_nonneg (walkTVPair_nonneg A t₀) k)
          (le_trans (walkTVUniform_nonneg A t₀) hunif)
    _ ≤ ε := hk

/-- **The ⌈log⌉ display form** — the escalation corollary at its
field-standard display: `t_mix(ε) ≤ (⌈log(ε₀/ε)/log(1/ρ)⌉ + 1) · t₀`
under `0 < ε₀`, `0 < ε`, `0 < ρ < 1`, the threshold discharged through
the shelf's own `pow_mul_le_of_log_threshold`. -/
theorem walkMixingTime_le_of_escalation (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] {ε ε₀ ρ : ℝ} (hε₀ : 0 < ε₀) (hε : 0 < ε) (t₀ : ℕ)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hunif : walkTVUniform A t₀ ≤ ε₀) (hpair : walkTVPair A t₀ ≤ ρ) :
    walkMixingTime A ε
      ≤ (Nat.ceil (Real.log (ε₀ / ε) / Real.log (1 / ρ)) + 1) * t₀ := by
  have hkey := pow_mul_le_of_log_threshold hρ hρ1 (le_of_lt hε₀) hε
    (Nat.ceil (Real.log (ε₀ / ε) / Real.log (1 / ρ))) (Nat.le_ceil _)
  exact walkMixingTime_le_mul_of_escalation A hA hnn hd t₀
    (Nat.ceil (Real.log (ε₀ / ε) / Real.log (1 / ρ))) hunif hpair
    (by rw [mul_comm]; exact hkey)

/-- **The uniform spectral ceiling** — the per-start ceiling's uniform
form: under the depth-form TV certificate's own hypothesis set (with
the start constants uniformly bounded by `C`, e.g. `C = 1/min π − 1`),
every start mixes within `⌈log(√C/(2ε))/log(1/r)⌉` steps. -/
theorem walkMixingTime_le_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hconn : (supportGraph A hA).Connected) (r ε : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (hε : 0 < ε)
    (hrate : ∀ i : V, eigvalOf (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i| ≤ r)
    (C : ℝ) (hC : ∀ x, (stationaryVec A x)⁻¹ - 1 ≤ C) :
    walkMixingTime A ε
      ≤ Nat.ceil (Real.log (Real.sqrt C / (2 * ε))
          / Real.log (1 / r)) := by
  refine walkMixingTime_le_of_cert A
    (Nat.ceil (Real.log (Real.sqrt C / (2 * ε)) / Real.log (1 / r)))
    fun s hs x => ?_
  have hring : Real.sqrt C / 2 / ε = Real.sqrt C / (2 * ε) := by ring
  have hthr : Real.log (Real.sqrt C / 2 / ε) / Real.log (1 / r)
      ≤ (s : ℝ) := by
    have h1 : Real.log (Real.sqrt C / (2 * ε)) / Real.log (1 / r)
        ≤ ((Nat.ceil (Real.log (Real.sqrt C / (2 * ε))
          / Real.log (1 / r)) : ℕ) : ℝ) :=
      Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.log (Real.sqrt C / (2 * ε))
        / Real.log (1 / r)) : ℕ) : ℝ) ≤ (s : ℝ) := by
      exact_mod_cast hs
    rw [hring]
    exact le_trans h1 h2
  have hkey := pow_mul_le_of_log_threshold hr hr1
    (by positivity : (0 : ℝ) ≤ Real.sqrt C / 2) hε s hthr
  calc tvDistance (walkDistribution A s x) (stationaryVec A)
      ≤ (1/2) * r ^ s * Real.sqrt ((stationaryVec A x)⁻¹ - 1) :=
        walkDistribution_tvDistance_le_of_rate A hA hnn hd hconn r
          (le_of_lt hr) hrate s x
    _ ≤ (1/2) * r ^ s * Real.sqrt C := by
        refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hC x)) ?_
        exact mul_nonneg (by norm_num) (pow_nonneg (le_of_lt hr) s)
    _ = r ^ s * (Real.sqrt C / 2) := by ring
    _ ≤ ε := hkey


end UniformMixing

/-!
## The spectral floor — the program's first lower-bound family

The exact eigen-component evolution is an *equality*, so it pins the
walk law from below: at any genuine `L_sym`-eigenpair `(μ, v)` with
`μ ≠ 0`, the TV and χ² distances to stationarity stay above the
mode's exact share — the message-passing proposal's deferred
over-squashing floor delivered on its own named route, and the
classical eigenvalue lower bound on mixing time (the delivered
ceiling's textbook companion; Levin–Peres–Wilmer ch. 12's
distinguishing-statistic technique, chapter-level locator per the
repo convention). Every prior mixing delivery is an upper bound; this
section is the first direction-reversed stress test of the same proved
eigenbasis substrate.
-/

section SpectralFloor

omit [DecidableEq V] in
private theorem dotProduct_mulVec_symm_floor {M : Matrix V V ℝ}
    (hM : M.IsSymm) (x y : V → ℝ) :
    x ⬝ᵥ (M *ᵥ y) = (M *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq]

/-- **The eigenpair power action**: for a symmetric matrix `M` and a
genuine eigenpair `(μ, v)`, the operator power `(1 − M)ᵗ` acts on the
pairing as the scalar `(1 − μ)ᵗ`, on either side of the dot product.
Generic — any eigenpair, no orthonormality, no `eigvecOf` indexing. -/
private theorem dotProduct_pow_one_sub_mulVec_of_eigenpair
    {M : Matrix V V ℝ} (hM : M.IsSymm) {μ : ℝ} {v : V → ℝ}
    (hv : M *ᵥ v = μ • v) (t : ℕ) (w : V → ℝ) :
    ((1 - M) ^ t *ᵥ w) ⬝ᵥ v = (1 - μ) ^ t * (w ⬝ᵥ v) := by
  have h1M : (1 - M).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_sub, Matrix.transpose_one, hM.eq]
  induction t with
  | zero => simp
  | succ t ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec,
        ← dotProduct_mulVec_symm_floor h1M,
        show (1 - M) *ᵥ v = v - μ • v from by
          rw [Matrix.sub_mulVec, one_mulVec, ← hv],
        Matrix.dotProduct_sub, Matrix.dotProduct_smul, ih, smul_eq_mul]
      ring

/-- The pairing bridge: testing the walk *law* against the conjugated
vector `(1/√D) • v` is the conjugated-density pairing against `v`,
rescaled by `vol⁻¹` — the density/law dictionary in one dot product.
Entrywise, so no nonemptiness hypothesis. -/
private theorem dotProduct_walkDistribution_degreeInvSqrt_eq
    (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i) [Nonempty V] (t : ℕ)
    (x : V) (v : V → ℝ) :
    (walkDistribution A t x) ⬝ᵥ (degreeInvSqrt A *ᵥ v)
      = (vol A (Finset.univ : Finset V))⁻¹
          * ((degreeSqrt A *ᵥ walkDensity A t x) ⬝ᵥ v) := by
  have hentry : ∀ i : V,
      walkDistribution A t x i * (degreeInvSqrt A *ᵥ v) i
        = (vol A (Finset.univ : Finset V))⁻¹
            * ((degreeSqrt A *ᵥ walkDensity A t x) i * v i) := by
    intro i
    have hs : Real.sqrt (deg A i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hd i)
    have hvv : vol A (Finset.univ : Finset V) ≠ 0 :=
      ne_of_gt (vol_univ_pos A hd)
    rw [degreeInvSqrt_mulVec_apply, degreeSqrt_mulVec_apply, walkDensity,
      stationaryVec,
      show deg A i = Real.sqrt (deg A i) * Real.sqrt (deg A i) from
        (Real.mul_self_sqrt (le_of_lt (hd i))).symm]
    field_simp
    ring
  rw [Matrix.dotProduct, Matrix.dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => hentry i

omit [DecidableEq V] in
/-- Strict positive-definiteness of the dot product, the manual
`Finset` route (the pinned Mathlib has no
`dotProduct_self_pos_of_ne_zero`). -/
private theorem dotProduct_self_pos_of_ne_zero_floor {v : V → ℝ}
    (hv0 : v ≠ 0) : 0 < v ⬝ᵥ v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv0 (funext hcon)
  have hnn : ∀ j ∈ (Finset.univ : Finset V), (0:ℝ) ≤ v j * v j :=
    fun j _ => mul_self_nonneg _
  have hsum : (0:ℝ) ≤ ∑ j, v j * v j := Finset.sum_nonneg hnn
  refine lt_of_le_of_ne hsum (Ne.symm ?_)
  intro hzero
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero i
    (Finset.mem_univ i)
  exact hi (by nlinarith [hterm])

/-- **Kernel orthogonality of nonzero modes, law-level form**: for a
genuine `L_sym`-eigenpair at `μ ≠ 0`, the stretched-constant kernel
direction `√D · 1` is orthogonal to `v`. Derived, not assumed — the
pairing transfers onto `μ • v` through symmetry and cancels against
`L_sym (√D · 1) = 0`. No connectivity: `μ ≠ 0` is the honest gate. -/
theorem degreeSqrt_onesVec_dotProduct_of_eigenpair
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    {μ : ℝ} {v : V → ℝ}
    (hv : normalizedLaplacian A *ᵥ v = μ • v) (hμ : μ ≠ 0) :
    (degreeSqrt A *ᵥ onesVec) ⬝ᵥ v = 0 := by
  have hM : (normalizedLaplacian A).IsSymm :=
    normalizedLaplacian_symmetric A hA
  have hstep : μ * ((degreeSqrt A *ᵥ onesVec) ⬝ᵥ v) = 0 := by
    calc μ * ((degreeSqrt A *ᵥ onesVec) ⬝ᵥ v)
        = (degreeSqrt A *ᵥ onesVec) ⬝ᵥ (μ • v) := by
              rw [Matrix.dotProduct_smul, smul_eq_mul]
      _ = (degreeSqrt A *ᵥ onesVec)
              ⬝ᵥ (normalizedLaplacian A *ᵥ v) := by rw [hv]
      _ = (normalizedLaplacian A *ᵥ (degreeSqrt A *ᵥ onesVec)) ⬝ᵥ v :=
            dotProduct_mulVec_symm_floor hM (degreeSqrt A *ᵥ onesVec) v
      _ = (0 : V → ℝ) ⬝ᵥ v := by
            rw [normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd]
      _ = 0 := Matrix.zero_dotProduct _
  exact (mul_eq_zero.mp hstep).resolve_left hμ

/-- The stationary pairing of the conjugated eigenvector — the
π-mean-zero fact the floors consume, bridged from the kernel
orthogonality above. -/
theorem stationaryVec_dotProduct_degreeInvSqrt_of_eigenpair
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] {μ : ℝ} {v : V → ℝ}
    (hv : normalizedLaplacian A *ᵥ v = μ • v) (hμ : μ ≠ 0) :
    (stationaryVec A) ⬝ᵥ (degreeInvSqrt A *ᵥ v) = 0 := by
  have hentry : ∀ i : V,
      stationaryVec A i * (degreeInvSqrt A *ᵥ v) i
        = (vol A (Finset.univ : Finset V))⁻¹
            * ((degreeSqrt A *ᵥ onesVec) i * v i) := by
    intro i
    have hs : Real.sqrt (deg A i) ≠ 0 := Real.sqrt_ne_zero'.mpr (hd i)
    have hvv : vol A (Finset.univ : Finset V) ≠ 0 :=
      ne_of_gt (vol_univ_pos A hd)
    rw [degreeInvSqrt_mulVec_apply, degreeSqrt_mulVec_apply, stationaryVec,
      show onesVec i = 1 from rfl,
      show deg A i = Real.sqrt (deg A i) * Real.sqrt (deg A i) from
        (Real.mul_self_sqrt (le_of_lt (hd i))).symm]
    field_simp
    ring
  have hbr : (stationaryVec A) ⬝ᵥ (degreeInvSqrt A *ᵥ v)
      = (vol A (Finset.univ : Finset V))⁻¹
          * ((degreeSqrt A *ᵥ onesVec) ⬝ᵥ v) := by
    rw [Matrix.dotProduct, Matrix.dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hentry i
  rw [hbr, degreeSqrt_onesVec_dotProduct_of_eigenpair A hA hd hv hμ,
    mul_zero]

/-- **The exact law-level test-function evolution** — the deferred
over-squashing item's own engine, restated at the law level: pairing
the walk law against the conjugated eigenvector `(1/√D) • v` of
`L_sym` evolves *exactly* geometrically at the walk factor `1 − μ`,
with no connectivity and no mode exclusion. An equality, not a bound —
the same fact the χ² decay engine consumes, now pointed downward: a
slow mode pins the law. -/
theorem walkDistribution_dotProduct_degreeInvSqrt_of_eigenpair
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (t : ℕ) (x : V) {μ : ℝ} {v : V → ℝ}
    (hv : normalizedLaplacian A *ᵥ v = μ • v) :
    (walkDistribution A t x) ⬝ᵥ (degreeInvSqrt A *ᵥ v)
      = (1 - μ) ^ t * ((walkDistribution A 0 x) ⬝ᵥ (degreeInvSqrt A *ᵥ v)) := by
  rw [dotProduct_walkDistribution_degreeInvSqrt_eq A hd t x v,
    dotProduct_walkDistribution_degreeInvSqrt_eq A hd 0 x v,
    walkDensity_eq_pow_walkTransitionMatrix_mulVec A hA hd t x,
    degreeSqrt_mulVec_pow_walkTransitionMatrix A hd t
      (walkDensity A 0 x),
    dotProduct_pow_one_sub_mulVec_of_eigenpair
      (normalizedLaplacian_symmetric A hA) hv t
      (degreeSqrt A *ᵥ walkDensity A 0 x)]
  ring

/-- **The TV spectral floor** — the deferred over-squashing statement
in its total-variation form: at any genuine `L_sym`-eigenpair
`(μ, v)` with `μ ≠ 0`, the walk law from `x` stays at total-variation
distance at least
`(1/2) · |1−μ|^t · |v x| / (√D x · c)` from stationarity, where `c`
bounds the conjugated test function `|(1/√D) • v|` above. The
distinguishing-function bound applied to the exactly-evolving test
function `(1/c) · (1/√D) • v`. No connectivity, no aperiodicity: at
`|1 − μ| = 1` (periodic modes) the floor never decays — which is the
point, exactly the chains no `r < 1` ceiling can reach. -/
theorem walkDistribution_tvDistance_ge_of_eigenpair
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (t : ℕ) (x : V) {μ : ℝ} {v : V → ℝ}
    (hv : normalizedLaplacian A *ᵥ v = μ • v) (hμ : μ ≠ 0)
    {c : ℝ} (hc : ∀ y, |(degreeInvSqrt A *ᵥ v) y| ≤ c) (hc0 : 0 < c) :
    (1/2) * |1 - μ| ^ t * |(degreeInvSqrt A *ᵥ v) x| / c
      ≤ tvDistance (walkDistribution A t x) (stationaryVec A) := by
  have hdisc := tvDistance_ge_half_abs_sum
    (μ := walkDistribution A t x) (ν := stationaryVec A)
    ((c⁻¹) • (degreeInvSqrt A *ᵥ v))
    (fun i => by
      rw [Pi.smul_apply, smul_eq_mul, abs_mul,
        abs_of_pos (inv_pos.mpr hc0)]
      exact le_trans (mul_le_mul_of_nonneg_left (hc i)
        (le_of_lt (inv_pos.mpr hc0))) (by rw [inv_mul_cancel₀ hc0.ne']))
  have hsum : ∑ i, (walkDistribution A t x i - stationaryVec A i)
        * ((c⁻¹) • (degreeInvSqrt A *ᵥ v)) i
      = c⁻¹ * ((1 - μ) ^ t * (degreeInvSqrt A *ᵥ v) x) := by
    have hsplit : ∀ i : V,
        (walkDistribution A t x i - stationaryVec A i)
          * ((c⁻¹) • (degreeInvSqrt A *ᵥ v)) i
        = c⁻¹ * (walkDistribution A t x i * (degreeInvSqrt A *ᵥ v) i
            - stationaryVec A i * (degreeInvSqrt A *ᵥ v) i) := by
      intro i
      rw [Pi.smul_apply, smul_eq_mul]
      ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, ← Finset.mul_sum,
      Finset.sum_sub_distrib,
      ← Matrix.dotProduct, ← Matrix.dotProduct,
      walkDistribution_dotProduct_degreeInvSqrt_of_eigenpair A hA hd t x hv,
      stationaryVec_dotProduct_degreeInvSqrt_of_eigenpair A hA hd hv hμ,
      sub_zero, walkDistribution_zero A x,
      Matrix.dotProduct_comm (Pi.single x (1 : ℝ) : V → ℝ)
        (degreeInvSqrt A *ᵥ v),
      Matrix.dotProduct_single, mul_one]
  rw [hsum] at hdisc
  have hgoal : (1/2) * |1 - μ| ^ t * |(degreeInvSqrt A *ᵥ v) x| / c
      = (1/2) * |c⁻¹ * ((1 - μ) ^ t * (degreeInvSqrt A *ᵥ v) x)| := by
    rw [abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hc0), abs_pow,
      inv_mul_eq_div]
    ring
  rw [hgoal]
  exact hdisc

/-- **The χ² spectral floor** — the Parseval twin: at any genuine
eigenpair `(μ, v)` with `μ ≠ 0` and `v ≠ 0`, the χ² distance of the
walk law from stationarity is at least the single mode's exact share
`(1−μ)^{2t} · (v x)²/(π x · ‖v‖²)`: the √D-conjugated initial centered
density pairs with `v` in coordinate exactly `vol/√D x · v x`
(kernel-orthogonal remainder), and Cauchy–Schwarz against the evolving
vector extracts that mode's slice of the exact Parseval identity. The
`|1 − μ| = 1` corner is honest: the floor is then the constant
`v(x)²/(π x ‖v‖²)` at every time — certified non-mixing on periodic
chains. -/
theorem chiSquareDistance_ge_of_eigenpair
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (t : ℕ) (x : V) {μ : ℝ} {v : V → ℝ}
    (hv : normalizedLaplacian A *ᵥ v = μ • v) (hμ : μ ≠ 0)
    (hv0 : v ≠ 0) :
    (1 - μ) ^ (2 * t) * (v x) ^ 2
      / (stationaryVec A x * (v ⬝ᵥ v))
      ≤ chiSquareDistance A t x := by
  have hM : (normalizedLaplacian A).IsSymm :=
    normalizedLaplacian_symmetric A hA
  have hvol : vol A (Finset.univ : Finset V) ≠ 0 :=
    ne_of_gt (vol_univ_pos A hd)
  have hπx2 : (0:ℝ) < stationaryVec A x := stationaryVec_pos A hd x
  set w : V → ℝ := degreeSqrt A *ᵥ (walkDensity A 0 x - 1) with hwdef
  set X : V → ℝ := (1 - normalizedLaplacian A) ^ t *ᵥ w with hxdef
  have hX : degreeSqrt A *ᵥ (walkDensity A t x - 1) = X := by
    rw [hxdef, hwdef, ← degreeSqrt_mulVec_pow_walkTransitionMatrix A hd t
      (walkDensity A 0 x - 1), walkDensity_sub_one A hA hd t x]
  have hchi : chiSquareDistance A t x
      = (vol A (Finset.univ : Finset V))⁻¹ * (X ⬝ᵥ X) := by
    rw [chiSquareDistance_eq_sum_smul A hd t x,
      sum_stationaryVec_smul_sq_eq A hd,
      show (fun i => walkDensity A t x i - 1) = walkDensity A t x - 1 from rfl,
      hX]
  have hpair : v ⬝ᵥ X = (1 - μ) ^ t * (v ⬝ᵥ w) := by
    rw [Matrix.dotProduct_comm v X, hxdef,
      dotProduct_pow_one_sub_mulVec_of_eigenpair hM hv t
        (degreeSqrt A *ᵥ (walkDensity A 0 x - 1))]
    congr 1
    exact Matrix.dotProduct_comm _ _
  have hmass : v ⬝ᵥ (degreeSqrt A *ᵥ walkDensity A 0 x)
      = (Real.sqrt (deg A x) / stationaryVec A x) * v x := by
    have hsingle : (degreeSqrt A *ᵥ walkDensity A 0 x)
        = (Real.sqrt (deg A x) / stationaryVec A x)
          • ((Pi.single x (1 : ℝ)) : V → ℝ) := by
      funext z
      by_cases hxz : x = z
      · subst hxz
        have hz : (Pi.single x (1 : ℝ) : V → ℝ) x = 1 := by
          simp [Pi.single_apply]
        have hwd : walkDensity A 0 x x
            = walkDistribution A 0 x x / stationaryVec A x := rfl
        rw [Pi.smul_apply, smul_eq_mul, degreeSqrt_mulVec_apply, hwd,
          walkDistribution_zero A x, hz]
        field_simp
      · have hz : (Pi.single x (1 : ℝ) : V → ℝ) z = 0 := by
          simp [Pi.single_apply, hxz]
        have hwd : walkDensity A 0 x z
            = walkDistribution A 0 x z / stationaryVec A z := rfl
        simp only [Pi.smul_apply, smul_eq_mul, degreeSqrt_mulVec_apply,
          hwd, walkDistribution_zero, hz, zero_div, mul_zero]
    rw [hsingle, Matrix.dotProduct_smul, smul_eq_mul,
      Matrix.dotProduct_single, mul_one]
  have hker : v ⬝ᵥ (degreeSqrt A *ᵥ onesVec) = 0 := by
    rw [Matrix.dotProduct_comm,
      degreeSqrt_onesVec_dotProduct_of_eigenpair A hA hd hv hμ]
  have hinit : v ⬝ᵥ w
      = (vol A (Finset.univ : Finset V) / Real.sqrt (deg A x)) * v x := by
    have hsplit : degreeSqrt A *ᵥ (walkDensity A 0 x - 1)
        = (degreeSqrt A *ᵥ walkDensity A 0 x)
          - (degreeSqrt A *ᵥ onesVec) := by
      rw [show (1 : V → ℝ) = onesVec from rfl, Matrix.mulVec_sub]
    calc v ⬝ᵥ w = v ⬝ᵥ ((degreeSqrt A *ᵥ walkDensity A 0 x)
          - (degreeSqrt A *ᵥ onesVec)) := by rw [hwdef, hsplit]
      _ = (Real.sqrt (deg A x) / stationaryVec A x) * v x - 0 := by
            rw [Matrix.dotProduct_sub, hmass, hker]
      _ = (vol A (Finset.univ : Finset V) / Real.sqrt (deg A x)) * v x := by
            rw [sub_zero]
            have hs : Real.sqrt (deg A x) ≠ 0 :=
              Real.sqrt_ne_zero'.mpr (hd x)
            have hπ : stationaryVec A x
                = deg A x / vol A (Finset.univ : Finset V) := rfl
            have hscalar : Real.sqrt (deg A x) / stationaryVec A x
                = vol A (Finset.univ : Finset V)
                    / Real.sqrt (deg A x) := by
              rw [hπ, show deg A x
                    = Real.sqrt (deg A x) * Real.sqrt (deg A x) from
                    (Real.mul_self_sqrt (le_of_lt (hd x))).symm]
              field_simp
              ring
            rw [hscalar]
  have hvv : 0 < v ⬝ᵥ v := dotProduct_self_pos_of_ne_zero_floor hv0
  have hcs : (v ⬝ᵥ X)^2 ≤ (v ⬝ᵥ v) * (X ⬝ᵥ X) := by
    have hgen := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V) v X
    simpa only [Matrix.dotProduct, sq] using hgen
  have key : (1 - μ) ^ (2 * t) * (v ⬝ᵥ w)^2
      ≤ (v ⬝ᵥ v) * (X ⬝ᵥ X) := by
    have hsq : ((1 - μ) ^ t * (v ⬝ᵥ w))^2
        = (1 - μ) ^ (2 * t) * (v ⬝ᵥ w)^2 := by
      rw [mul_pow, ← pow_mul, mul_comm 2 t]
    calc (1 - μ) ^ (2 * t) * (v ⬝ᵥ w)^2
        = ((1 - μ) ^ t * (v ⬝ᵥ w))^2 := hsq.symm
      _ = (v ⬝ᵥ X)^2 := by rw [← hpair]
      _ ≤ (v ⬝ᵥ v) * (X ⬝ᵥ X) := hcs
  have hwx : (v ⬝ᵥ w)^2 * deg A x
      = (vol A (Finset.univ : Finset V))^2 * (v x)^2 := by
    have hD : deg A x ≠ 0 := ne_of_gt (hd x)
    rw [hinit, mul_pow, div_pow, Real.sq_sqrt (le_of_lt (hd x))]
    field_simp
  have hstep1 : (v x)^2 * vol A (Finset.univ : Finset V)
      = (v ⬝ᵥ w)^2 * stationaryVec A x := by
    have hπ : stationaryVec A x
        = deg A x / vol A (Finset.univ : Finset V) := rfl
    rw [hπ]
    field_simp
    nlinarith [hwx]
  have hfin0 : (1 - μ) ^ (2 * t) * (v x)^2
        * vol A (Finset.univ : Finset V)
      ≤ (X ⬝ᵥ X) * (stationaryVec A x * (v ⬝ᵥ v)) := by
    calc (1 - μ) ^ (2 * t) * (v x)^2 * vol A (Finset.univ : Finset V)
        = (1 - μ) ^ (2 * t) * ((v x)^2
            * vol A (Finset.univ : Finset V)) := by ring
      _ = (1 - μ) ^ (2 * t) * ((v ⬝ᵥ w)^2 * stationaryVec A x) := by
            rw [hstep1]
      _ = (1 - μ) ^ (2 * t) * (v ⬝ᵥ w) ^ 2 * stationaryVec A x := by
            ring
      _ ≤ (v ⬝ᵥ v) * (X ⬝ᵥ X) * stationaryVec A x :=
            mul_le_mul_of_nonneg_right key (le_of_lt hπx2)
      _ = (X ⬝ᵥ X) * (stationaryVec A x * (v ⬝ᵥ v)) := by ring
  rw [hchi, inv_mul_eq_div, div_le_div_iff₀ (mul_pos hπx2 hvv)
    (vol_univ_pos A hd)]
  exact hfin0

/-- **The mixing-time floor gate**: if some witness time exists at
`ε` (the upward-closed set is nonempty) and time `t` provably fails
the threshold — `TV_t > ε` — then `t` is strictly below the mixing
time. The witness-existence hypothesis is load-bearing exactly at the
junk corner: on a periodic chain the witness set is empty, `t_mix = 0`
by `sInf ∅`, and no strict floor can be read (the `K₂` fence
`k2_mix_gate_hwit_fence_QA`). -/
theorem walkMixingTimeFrom_gt_of_tv_gt (A : WAdj (V := V)) (x : V)
    {ε : ℝ}
    (hwit : ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε)
    {t : ℕ}
    (htv : ε < tvDistance (walkDistribution A t x) (stationaryVec A)) :
    t < walkMixingTimeFrom A x ε := by
  by_contra hnl
  have hle := walkMixingTimeFrom_spec A x hwit t (by omega)
  exact absurd hle (not_le.mpr htv)

/-- **The strict log-threshold calculus bridge, floor direction** —
the downward twin of `pow_mul_le_of_log_threshold`: for a rate
`0 < r < 1`, a positive budget `b`, and a depth *strictly below* the
threshold `log b / log r` (a *negative* denominator — that is the
whole content), the decay has not yet consumed the budget:
`b < r ^ t`. The sign of `log` is the trap in this direction too:
dividing by the negative `log r` flips the inequality. -/
theorem pow_lt_of_lt_log_div {r b : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hb : 0 < b) (t : ℕ)
    (hthr : (t : ℝ) < Real.log b / Real.log r) :
    b < r ^ t := by
  have hrinv : 0 < 1 / r := div_pos (by norm_num) hr
  have hrinv1 : 1 < 1 / r := (one_lt_div hr).mpr hr1
  have hlogpos : 0 < Real.log (1 / r) := Real.log_pos hrinv1
  have hlogr : Real.log r = -Real.log (1 / r) := by
    have h1 : Real.log (1 / r) = -Real.log r := by
      rw [show (1 / r : ℝ) = r⁻¹ from (inv_eq_one_div r).symm,
        Real.log_inv]
    linarith
  rw [hlogr, div_neg, ← neg_div] at hthr
  have hstep : Real.log b < -((t : ℝ) * Real.log (1 / r)) := by
    have hmul := (lt_div_iff₀ hlogpos).mp hthr
    linarith
  have hexp : Real.exp (Real.log b)
      < Real.exp ((t : ℝ) * Real.log r) := by
    refine Real.exp_lt_exp.mpr ?_
    rw [hlogr, mul_neg]
    exact hstep
  rw [Real.exp_log hb, ← Real.log_pow r t,
    Real.exp_log (pow_pos hr t)] at hexp
  exact hexp

/-- **The spectral floor on the mixing time** — the classical
eigenvalue lower bound on `t_mix` (the delivered ceiling's textbook
companion), at a genuine aperiodic eigenpair: under a certified sup
bound `c` on the conjugated test function, a nonzero test value at the
start, `0 < |1 − μ| < 1`, and *some* witness time at `ε` (existence
certified from above — e.g. by the `r < 1` ceiling; the hypothesis is
exactly what fails on periodic chains), the mixing time is at least
`⌈log(|v x|/(√D x · 2 ε c))/log(1/|1−μ|)⌉`. Mirror of
`walkMixingTimeFrom_le_of_connected`'s ⌈·⌉ display. -/
theorem walkMixingTimeFrom_ge_of_eigenpair
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] {ε : ℝ} (hε : 0 < ε) (x : V) {μ : ℝ} {v : V → ℝ}
    (hv : normalizedLaplacian A *ᵥ v = μ • v) (hμ : μ ≠ 0)
    {c : ℝ} (hc : ∀ y, |(degreeInvSqrt A *ᵥ v) y| ≤ c) (hc0 : 0 < c)
    (hfx : (degreeInvSqrt A *ᵥ v) x ≠ 0)
    (hr0 : 0 < |1 - μ|) (hr1 : |1 - μ| < 1)
    (hwit : ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      tvDistance (walkDistribution A s x) (stationaryVec A) ≤ ε) :
    Nat.ceil (Real.log (|(degreeInvSqrt A *ᵥ v) x| / (2 * ε * c))
        / Real.log (1 / |1 - μ|))
      ≤ walkMixingTimeFrom A x ε := by
  set L : ℝ := Real.log (|(degreeInvSqrt A *ᵥ v) x| / (2 * ε * c))
      / Real.log (1 / |1 - μ|) with hLdef
  rcases le_or_lt L 0 with hL | hL
  · have hzc : Nat.ceil L ≤ 0 := Nat.ceil_le.mpr (by simpa using hL)
    omega
  · have hbx : 0 < |(degreeInvSqrt A *ᵥ v) x| := abs_pos.mpr hfx
    have hbud : 0 < 2 * ε * c := by positivity
    set b : ℝ := 2 * ε * c / |(degreeInvSqrt A *ᵥ v) x| with hbdef
    have hb : 0 < b := by positivity
    have hLeq : L = Real.log b / Real.log |1 - μ| := by
      have hinvb : b = (|(degreeInvSqrt A *ᵥ v) x| / (2 * ε * c))⁻¹ := by
        rw [hbdef, inv_div]
      have hinvr : (1 : ℝ) / |1 - μ| = |1 - μ|⁻¹ :=
        (inv_eq_one_div _).symm
      rw [hLdef, hinvb, Real.log_inv, hinvr, Real.log_inv, div_neg,
        neg_div]
    have hceil1 : 1 ≤ Nat.ceil L := by
      have := (Nat.ceil_pos).mpr hL
      omega
    have h0L : 0 ≤ L := le_of_lt hL
    have hT : ((Nat.ceil L - 1 : ℕ) : ℝ) < L := by
      have hc1 : ((Nat.ceil L : ℕ) : ℝ) < L + 1 := Nat.ceil_lt_add_one h0L
      have hcast : ((Nat.ceil L - 1 : ℕ) : ℝ)
          = ((Nat.ceil L : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub hceil1]
        norm_num
      rw [hcast]
      linarith
    have hpow : b < |1 - μ| ^ (Nat.ceil L - 1) :=
      pow_lt_of_lt_log_div hr0 hr1 hb (Nat.ceil L - 1)
        (lt_of_lt_of_eq hT hLeq)
    have hflr := walkDistribution_tvDistance_ge_of_eigenpair A hA hd
      (Nat.ceil L - 1) x hv hμ hc hc0
    have hA' : (0:ℝ) < |(degreeInvSqrt A *ᵥ v) x| / c := by positivity
    have hmono : (|(degreeInvSqrt A *ᵥ v) x| / c) * b
        < (|(degreeInvSqrt A *ᵥ v) x| / c)
          * |1 - μ| ^ (Nat.ceil L - 1) :=
      mul_lt_mul_of_pos_left hpow hA'
    have hval : (|(degreeInvSqrt A *ᵥ v) x| / c) * b = 2 * ε := by
      rw [hbdef]
      field_simp
      ring
    have hz : (2:ℝ) * ((1/2) * |1 - μ| ^ (Nat.ceil L - 1)
          * |(degreeInvSqrt A *ᵥ v) x| / c)
        = (|(degreeInvSqrt A *ᵥ v) x| / c)
            * |1 - μ| ^ (Nat.ceil L - 1) := by ring
    have hkey : ε < tvDistance (walkDistribution A (Nat.ceil L - 1) x)
        (stationaryVec A) := by
      linarith [hval, hmono, hz, hflr]
    have hlt := walkMixingTimeFrom_gt_of_tv_gt A x hwit hkey
    omega

open Scaffold.InformationTheory in
/-- **The entropy floor** — Pinsker composed with the spectral TV
floor: at a genuine `L_sym` eigenpair `(μ, v)` with sup bound `c`, the
relative entropy of the walk law from stationarity is at least twice
the squared TV floor — periodic `|1−μ| = 1` modes pin entropy bounded
away from zero forever, the floor family's first non-TV member. -/
theorem klDiv_walkDistribution_ge_of_eigenpair (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (t : ℕ) (x : V) {μ : ℝ} {v : V → ℝ}
    (hv : normalizedLaplacian A *ᵥ v = μ • v) (hμ : μ ≠ 0)
    {c : ℝ} (hc : ∀ y, |(degreeInvSqrt A *ᵥ v) y| ≤ c) (hc0 : 0 < c) :
    2 * ((1/2) * |1 - μ| ^ t * |(degreeInvSqrt A *ᵥ v) x| / c) ^ 2
      ≤ klDiv (walkDistribution A t x) (stationaryVec A) := by
  have hfl : (1/2) * |1 - μ| ^ t * |(degreeInvSqrt A *ᵥ v) x| / c
      ≤ tvDistance (walkDistribution A t x) (stationaryVec A) :=
    walkDistribution_tvDistance_ge_of_eigenpair A hA hd t x hv hμ hc hc0
  have hpin := tvDistance_le_sqrt_half_klDiv
    (p := walkDistribution A t x) (q := stationaryVec A)
    (walkDistribution_nonneg A hnn hd t x) (sum_walkDistribution A hd t x)
    (fun i => stationaryVec_pos A hd i) (sum_stationaryVec A hd)
  have hTV0 : (0:ℝ) ≤ tvDistance (walkDistribution A t x)
      (stationaryVec A) :=
    tvDistance_nonneg _ _
  have hfl0 : (0:ℝ) ≤ (1/2) * |1 - μ| ^ t
      * |(degreeInvSqrt A *ᵥ v) x| / c :=
    div_nonneg (mul_nonneg (by positivity) (abs_nonneg _)) (le_of_lt hc0)
  have hD0 : (0:ℝ) ≤ klDiv (walkDistribution A t x) (stationaryVec A) :=
    klDiv_nonneg (walkDistribution_nonneg A hnn hd t x)
      (sum_walkDistribution A hd t x) (fun i => stationaryVec_pos A hd i)
      (sum_stationaryVec A hd)
  have hs1 : ((1/2) * |1 - μ| ^ t * |(degreeInvSqrt A *ᵥ v) x| / c) ^ 2
      ≤ (tvDistance (walkDistribution A t x) (stationaryVec A)) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_self_le_mul_self hfl0 hfl
  have hs2 : (tvDistance (walkDistribution A t x) (stationaryVec A)) ^ 2
      ≤ klDiv (walkDistribution A t x) (stationaryVec A) / 2 := by
    have h1 : (tvDistance (walkDistribution A t x)
          (stationaryVec A)) ^ 2
        ≤ (Real.sqrt (klDiv (walkDistribution A t x)
            (stationaryVec A) / 2)) ^ 2 :=
      sq_le_sq' (le_trans (neg_nonpos.mpr (Real.sqrt_nonneg _)) hTV0) hpin
    rw [Real.sq_sqrt (div_nonneg hD0 (by norm_num))] at h1
    exact h1
  nlinarith [hs1, hs2]



end SpectralFloor

/-! ## The lazy mixing time: the periodicity fix at the object level

`proposals/lazy-mixing-time-objects.md` (2026-09-01): the lazy-walk
delivery's recorded follow-on compositions — the depth-form lazy
ceiling and the `t_mix` object at `lazyWalkDistribution` — with the
consumer gate discharged by naming the bipartite-input instance: the
empirical-stationary capstone's own "agent that can only simulate the
walk" setting on paths/trees/grids, where the plain family's
`r < 1` certificate is provably unsatisfiable (`lazy-walk-mixing.md`'s
leverage case, fenced as never-decay pins). The plain `t_mix` objects
are junk exactly on that class (empty witness set → `sInf = 0` with no
mixing, the `k2_mix_junk_corner_QA` fence); these twins carry the
genuine, finite mixing times, at the intrinsic rate `1 − λ₂/2`. -/

section LazyMixingTime

/-- **The entrywise lazy ceiling at the intrinsic rate** — the named
consumer's interface (the empirical-stationary capstone's lazy
extension): a single vertex's deviation of the `t`-step *lazy* walk law
from stationarity is at most `(1 − λ₂/2)^t` times
`√(π y · ((π x)⁻¹ − 1))` — the plain twin's `r`-certificate hypothesis
replaced by the computed intrinsic rate, which is the entire point of
the lazy program: on every connected bipartite graph, where the plain
twin's hypothesis set is provably unsatisfiable, this bound holds with
connectivity as the only graph hypothesis. One χ² summand against the
whole sum, then the delivered `lazyChiSquareDistance_le_of_connected`;
the rate's nonnegativity is the λ₂ ≤ 2 cap. -/
theorem lazyWalkDistribution_sub_stationaryVec_abs_le (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) (t : ℕ) (x y : V) :
    |lazyWalkDistribution A t x y - stationaryVec A y|
      ≤ (1 - secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t
        * Real.sqrt (stationaryVec A y * ((stationaryVec A x)⁻¹ - 1)) := by
  have hπy := stationaryVec_pos A hd y
  have hnon : 0 ≤ stationaryVec A y * ((stationaryVec A x)⁻¹ - 1) := by
    have hle : stationaryVec A x ≤ 1 := stationaryVec_le_one A hd x
    have hpos := stationaryVec_pos A hd x
    have hon : (1 : ℝ) ≤ (stationaryVec A x)⁻¹ :=
      (one_le_inv₀ hpos).mpr hle
    exact mul_nonneg (le_of_lt hπy) (by linarith)
  have hone : (lazyWalkDistribution A t x y - stationaryVec A y) ^ 2
      / stationaryVec A y ≤ lazyChiSquareDistance A t x := by
    rw [lazyChiSquareDistance]
    exact Finset.single_le_sum
      (f := fun i => (lazyWalkDistribution A t x i - stationaryVec A i)^2
        / stationaryVec A i)
      (fun i _ => div_nonneg (sq_nonneg _)
        (le_of_lt (stationaryVec_pos A hd i))) (Finset.mem_univ y)
  rw [div_le_iff₀ hπy] at hone
  have htwo := lazyChiSquareDistance_le_of_connected A hA hnn hd hcard
    hconn t x
  have hrate0 : 0 ≤ (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2) := by
    have h := secondEval_normalizedLaplacian_le_two A hA hnn hd hcard
    linarith
  have hle : (lazyWalkDistribution A t x y - stationaryVec A y) ^ 2
      ≤ ((1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t
          * Real.sqrt (stationaryVec A y
            * ((stationaryVec A x)⁻¹ - 1))) ^ 2 := by
    have hsq : ((1 - secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t
        * Real.sqrt (stationaryVec A y
          * ((stationaryVec A x)⁻¹ - 1))) ^ 2
        = ((1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
            * ((stationaryVec A x)⁻¹ - 1)) * stationaryVec A y := by
      have h2t : (1 - secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
          = ((1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t) ^ 2 := by
        rw [show (2 * t : ℕ) = t + t from by omega, pow_add, pow_two]
      rw [mul_pow, Real.sq_sqrt hnon, h2t]
      ring
    calc (lazyWalkDistribution A t x y - stationaryVec A y) ^ 2
        ≤ lazyChiSquareDistance A t x * stationaryVec A y := hone
      _ ≤ ((1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
            * ((stationaryVec A x)⁻¹ - 1)) * stationaryVec A y :=
            mul_le_mul_of_nonneg_right htwo (le_of_lt hπy)
      _ = ((1 - secondEval (normalizedLaplacian A)
              (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t
          * Real.sqrt (stationaryVec A y
            * ((stationaryVec A x)⁻¹ - 1))) ^ 2 := hsq.symm
  exact abs_le_of_sq_le_sq hle
    (mul_nonneg (pow_nonneg hrate0 t) (Real.sqrt_nonneg _))

/-- **The depth-form TV lazy ceiling** — the plain family's
`walkDistribution_tvDistance_le_of_depth` at the lazy law, at the
intrinsic rate `1 − λ₂/2` in place of the caller's `r` certificate. The
strictness is honest and visible: `0 < r` needs `λ₂ < 2` (exactly `K₂`'s
rate-0 corner is excluded — there the object is exact in one step, see
the QA), `r < 1` is derived from connectivity through the Fiedler
mirror. -/
theorem lazyWalkDistribution_tvDistance_le_of_depth (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected)
    (hslt : secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard < 2)
    {ε : ℝ} (hε : 0 < ε)
    (t : ℕ) (x : V)
    (hthr : Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / (2 * ε))
      / Real.log (1 / (1 - secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard / 2)) ≤ (t : ℝ)) :
    tvDistance (lazyWalkDistribution A t x) (stationaryVec A) ≤ ε := by
  have hsltpos : 0 < secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard :=
    secondEval_normalizedLaplacian_pos_of_connected A hA hnn hd hcard hconn
  have hr0 : 0 < (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2) := by linarith
  have hr1 : (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2) < 1 := by linarith
  have hC0 : 0 ≤ (stationaryVec A x)⁻¹ - 1 := by
    have hle : stationaryVec A x ≤ 1 := stationaryVec_le_one A hd x
    have hpos := stationaryVec_pos A hd x
    have hon : (1 : ℝ) ≤ (stationaryVec A x)⁻¹ :=
      (one_le_inv₀ hpos).mpr hle
    linarith
  have hTV := lazyWalkDistribution_tvDistance_le_of_connected A hA hnn hd
    hcard hconn t x
  have hsplit : (1/2) * Real.sqrt ((1 - secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
        * ((stationaryVec A x)⁻¹ - 1))
      = (1 - secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t
        * (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / 2) := by
    have h2t : (1 - secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
        = ((1 - secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t) ^ 2 := by
      rw [show (2 * t : ℕ) = t + t from by omega, pow_add, pow_two]
    have hp : (0 : ℝ) ≤ (1 - secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t :=
      pow_nonneg (le_of_lt hr0) t
    rw [h2t, Real.sqrt_mul (sq_nonneg ((1 - secondEval
        (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA)
          hcard / 2) ^ t)) _, Real.sqrt_sq hp]
    ring
  have hthr' : Real.log ((Real.sqrt ((stationaryVec A x)⁻¹ - 1) / 2) / ε)
      / Real.log (1 / (1 - secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard / 2)) ≤ (t : ℝ) := by
    have hEq : (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / 2) / ε
        = Real.sqrt ((stationaryVec A x)⁻¹ - 1) / (2 * ε) := by
      rw [div_div]
    rw [hEq]
    exact hthr
  have hfin := pow_mul_le_of_log_threshold hr0 hr1
    (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hε t hthr'
  calc tvDistance (lazyWalkDistribution A t x) (stationaryVec A)
      ≤ (1/2) * Real.sqrt ((1 - secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard / 2) ^ (2 * t)
          * ((stationaryVec A x)⁻¹ - 1)) := hTV
    _ = (1 - secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard / 2) ^ t
        * (Real.sqrt ((stationaryVec A x)⁻¹ - 1) / 2) := hsplit
    _ ≤ ε := hfin

/-- The **lazy mixing time** from `x` at threshold `ε`: the least
number of steps from which the *lazy* walk law stays within `ε` of
stationarity in total variation — the plain `walkMixingTimeFrom` object
at the lazy law. On every connected bipartite graph the plain object is
junk (its witness set is empty at every reachable `ε`: the plain walk
provably never mixes there, the `K₂` fence), and this twin carries the
genuine, finite mixing time — the periodicity fix at the object level,
which is where LPW's `t_mix := t_mix(1/4)` convention and the empirical
simulating agent read it. Junk corner unchanged: at an unreachable `ε`
the time set is empty and `sInf ∅ = 0` on `ℕ`. QA: the exact closed
forms `path_lazy_corner_mix_eq_eighth_QA`, `path_lazy_center_mix_eq_one_QA`,
`k2_lazy_mix_eq_fourth_QA`, and the object-level contrast
`k2_lazy_mix_contrast_QA`. -/
noncomputable def lazyWalkMixingTimeFrom (A : WAdj (V := V)) (x : V)
    (ε : ℝ) : ℕ :=
  sInf {t : ℕ | ∀ s : ℕ, t ≤ s →
    tvDistance (lazyWalkDistribution A s x) (stationaryVec A) ≤ ε}

/-- The witness-time set is bounded below by `0` by construction. -/
theorem lazyWalkMixingTimeFrom_bddBelow (A : WAdj (V := V)) (x : V)
    (ε : ℝ) :
    BddBelow {t : ℕ | ∀ s : ℕ, t ≤ s →
      tvDistance (lazyWalkDistribution A s x) (stationaryVec A) ≤ ε} :=
  ⟨0, fun _ _ => Nat.zero_le _⟩

/-- Any witness time certifies the lazy mixing time — the reusable
certificate interface, the lazy twin of `walkMixingTimeFrom_le_of_cert`. -/
theorem lazyWalkMixingTimeFrom_le_of_cert (A : WAdj (V := V)) (x : V)
    {ε : ℝ} (T : ℕ)
    (hT : ∀ s : ℕ, T ≤ s →
      tvDistance (lazyWalkDistribution A s x) (stationaryVec A) ≤ ε) :
    lazyWalkMixingTimeFrom A x ε ≤ T :=
  csInf_le (lazyWalkMixingTimeFrom_bddBelow A x ε) hT

/-- **The lazy mixing time is attained** — `ℕ` is well-ordered, so the
infimum of a nonempty witness set is a *member* of it, and membership
is exactly the uniform bound. The lazy twin of
`walkMixingTimeFrom_spec`. -/
theorem lazyWalkMixingTimeFrom_spec (A : WAdj (V := V)) (x : V)
    {ε : ℝ}
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s →
      tvDistance (lazyWalkDistribution A s x) (stationaryVec A) ≤ ε) :
    ∀ s : ℕ, lazyWalkMixingTimeFrom A x ε ≤ s →
      tvDistance (lazyWalkDistribution A s x) (stationaryVec A) ≤ ε :=
  csInf_mem hne

/-- **ε-antitonicity**, the lazy twin of `walkMixingTimeFrom_anti`. -/
theorem lazyWalkMixingTimeFrom_anti (A : WAdj (V := V)) (x : V)
    {ε δ : ℝ}
    (hεδ : ε ≤ δ)
    (hne : ∃ t : ℕ, ∀ s : ℕ, t ≤ s →
      tvDistance (lazyWalkDistribution A s x) (stationaryVec A) ≤ ε) :
    lazyWalkMixingTimeFrom A x δ ≤ lazyWalkMixingTimeFrom A x ε :=
  csInf_le_csInf (lazyWalkMixingTimeFrom_bddBelow A x δ) hne
    (fun _ ht => fun s hs => (ht s hs).trans hεδ)

/-- **The intrinsic-rate spectral ceiling** — the field-standard
discrete mixing bound at the lazy law:
`t_mix_lazy(ε) ≤ ⌈log(√((π x)⁻¹ − 1)/(2ε))/log(1/(1−λ₂/2))⌉` under
exactly the depth-form lazy ceiling's hypothesis set (connectivity plus
the honest `λ₂ < 2` — the `K₂` rate-0 corner is outside, and pinned
exactly in QA instead). QA: attained exactly on the path's center start
(`path_lazy_center_ceiling_attained_QA`), computed with honest slack on
the corner start (`path_lazy_corner_ceiling_slack_QA`). -/
theorem lazyWalkMixingTimeFrom_le_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    [Nonempty V] (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected)
    (hslt : secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard < 2)
    {ε : ℝ} (hε : 0 < ε) (x : V) :
    lazyWalkMixingTimeFrom A x ε
      ≤ Nat.ceil (Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1)
          / (2 * ε)) / Real.log (1 / (1 - secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard / 2))) := by
  set thr : ℝ := Real.log (Real.sqrt ((stationaryVec A x)⁻¹ - 1)
    / (2 * ε)) / Real.log (1 / (1 - secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard / 2)) with hthrdef
  refine lazyWalkMixingTimeFrom_le_of_cert A x (Nat.ceil thr) ?_
  intro s hs
  exact lazyWalkDistribution_tvDistance_le_of_depth A hA hnn hd hcard
    hconn hslt hε s x
    (le_trans (Nat.le_ceil thr) (by exact_mod_cast hs))

end LazyMixingTime


end SpectralGraphTheory
