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

end SpectralGraphTheory
