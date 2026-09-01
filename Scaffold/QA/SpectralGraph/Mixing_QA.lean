/-
  Mixing_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Mixing`: the ℓ²-mixing
  proxy of the mixing-time program's Step 2, the geometric decay
  engine of Step 3 component 1, and the χ² assembly of Step 3
  component 2 — the final mixing statement
  `chiSquareDistance_le_of_connected` instantiated at the concrete
  three-vertex path (degrees 1, 2, 1; π = (1/4, 1/2, 1/4); λ* = 1 —
  the bipartite no-decay bound, the rate derived basis-independently
  from two sum-of-squares certificates pinning the spectrum into
  `[0, 2]`), the triangle K₃ (degrees 2, 2, 2; π = (1/3, 1/3, 1/3);
  walk spectrum {1, −1/2, −1/2} — genuine decay at rate 1/2, the
  bound attained *exactly* at t = 1, 2), and the triangle⊕self-loop
  `Fin 4` fixture where connectivity fails and the conclusion is
  refuted while the rate hypothesis genuinely holds — with every
  headline quantity pinned by raw literal arithmetic independent of
  the theorem under test, and negative witnesses tying the
  load-bearing hypotheses to refuted hypothesis-free forms — plus the
  oversmoothing-ceiling section (`Oversmoothing.lean`'s depth-form
  consumers instantiated at two rate certificates: the honest `1/2`
  certifying depth exactly 3, the loose `4/5` provably needing 9, at
  the same `ε = 1/8`).

  The triangle's eigen-facts (`tri_eigvalOf_cases`, `tri_kernel_const`,
  `tri_exists_kernel_index`) and the disconnected fixture's spectrum
  serve the oversmoothing section; the per-pair resistance section
  (2026-08-31) adds the combinatorial-spectrum mirror
  (`tri_lap_eigvalOf_cases`), the exact-attainment contrast pins at
  `t = 1, 2`, and the C₄ mode-coverage fence (`c4Adj`).
  (`disc_eigvalOf_cases`) are derived without any control over
  Mathlib's classically chosen eigenbasis: only the unit norm, the
  eigen equation entrywise, and linear arithmetic — the DavisKahan_QA
  technique.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  The total-variation section (2026-08-31,
  `proposals/total-variation-mixing-conversion.md`) exercises the ℓ² →
  TV conversion and its depth-form consumers: the **exact-attainment
  pin** `k2_conversion_attained_QA` (on `K₂` at `t = 1`,
  `TV = (1/2)·√χ² = 1/2` with both sides independently pinned — the
  conversion's constant sharp, no smaller constant possible), the
  triangle's exact TV values at `t = 1, 2, 3` against the rate and
  split-rate theorem instances, the depth-2 certificate at `ε = 1/4`
  with depth 1 *proved* to fail the threshold, the two-start instance
  at depth 3 with its raw value `1/8`, and the mass-one fence
  (`tv_conversion_mass_guard_refuted_QA`: at a mass-2 weight the
  un-guarded conversion reads `1/2 ≤ (1/2)·√(1/2)`, refuted).

  The continuous-time sections (2026-08-31,
  `proposals/continuous-time-chi-square-mixing.md`, and its deferred
  path follow-on landed the same day) exercise the consumer
  `contChiSquareDistance_le`: exact attainment at every time on the
  triangle (`2e^{−3t}`), the disconnected gap-zero closed form
  `1/3 + (8/3)e^{−3t}` with its fences, and — on the only connected
  *irregular* fixture, where the `√D` conjugation is non-scalar — the
  path's exact single-mode decay `χ²_cont(t, center) = e^{−4t}` at the
  pinned gap `λ₂(L_sym P₃) = 1` (trace route), with the strict-slack
  witness `e^{−4t} < e^{−2t}` for `t > 0` and the wrong-constant fence.
  The `ContMixingTime` section (2026-08-31, the same proposal's
  Deferred items 1+2) exercises the mixing-time package: the exact
  `K₂` closed form `t_mix(ε) = ln(1/(2ε))/2` (a `sInf` pinned in both
  directions), the ceiling attained exactly at `ε = e^{−2}/2`, the
  exact TV values on `K₂` (attained at every time) and the triangle
  `(2/3)e^{−3t/2}` (Cauchy–Schwarz slack strict), the wrong-gap
  refutation, the big-`ε` corner, and the antitone instance.
  The Poisson-bridge section (2026-09-01, the same proposal's named
  follow-on) exercises the Poissonization identity and the
  comparability: the `K₂` periodic-chain fence (`TV_disc ≡ 1/2` at
  every time — no discrete certificate exists, no reverse comparability
  can hold), the `t = 0` mixture corner, and the triangle's exact
  discrete closed form `TV_disc(m) = (2/3)·2^{−m}` (the `triG`
  eigenroute) with both theorem instances at `t = 8`, `m = 2` and the
  anti-monotonicity instance.
  The `DiscMixingTime` section (2026-09-01,
  `proposals/total-variation-mixing-conversion.md`'s deferred `t_mix`
  object, consumer gate discharged by the Poisson bridge) pins the
  object at closed forms on the triangle (`t_mix(1/3) = 1`,
  `t_mix(1/6) = 2`, `t_mix(1/12) = 3`, each in both directions — the
  certificate interface above, the attainment specification below), the
  ceiling attained exactly at `ε = √2/4` and computed with honest slack
  at `ε = 1/6` (`3` against the true `2`), the `K₂` junk corner pinned
  (`sInf ∅ = 0` beside the no-certificate fence that excludes it), the
  antitone instance, and the bridge composition re-deriving the
  hand-certified transfer bound `5/24` with the certificate discharged
  by the object.
  The `SpectralFloor` section (2026-09-01, the message-passing
  proposal's deferred over-squashing item delivered on its own named
  route — the mixing program's first lower-bound family) pins the
  floors attained *exactly* at every time on `K₂` (TV `1/2`, χ² `1` —
  certified non-mixing on the periodic chain) and the χ² floor
  attained exactly at every time on the triangle at the `triG`
  eigenpair, the exact law-level evolution instances at both hand
  eigenpairs, the log-form floor hitting all three pinned `t_mix`
  closed forms exactly (completing the two-sided depth bracket:
  floor `2` = truth `2` ≤ ceiling `3` at `ε = 1/6`), the kernel-mode
  refutation fences in both metrics, and the `K₂` witness-existence
  fence for the floor gate. The `UniformMixing` section (2026-09-01,
  `proposals/total-variation-mixing-conversion.md`'s second follow-on)
  QA's LPW's uniform `t_mix` and its submultiplicativity class: the
  triangle distance pins from raw law literals, submultiplicativity
  attained with equality in all three forms (the sharp Dobrushin
  constant load-bearing), the uniform object's exact closed forms
  pinned in both directions, and the `K₂` periodicity corner at the
  uniform level (the empty-set infimum pinned and fenced).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Mixing
import Scaffold.Mathlib.GraphTheory.Oversmoothing
import Scaffold.Mathlib.GraphTheory.Electrical
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix
open Scaffold.InformationTheory

namespace SpectralGraphTheory.QA

/-!
## The three-vertex path `0 — 1 — 2` (reused fixture)
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1), volume 4, stationary π = (1/4, 1/2, 1/4). -/
def pathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem pathAdj_isSymm : pathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [pathAdj]

theorem pathAdj_deg_zero : deg pathAdj 0 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_one : deg pathAdj 1 = 2 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_two : deg pathAdj 2 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_pos (i : Fin 3) : 0 < deg pathAdj i := by
  fin_cases i <;>
    simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num

theorem path_vol_QA : vol pathAdj (Finset.univ : Finset (Fin 3)) = 4 := by
  simp only [vol, deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

/-- The stationary distribution pinned to literals: `π = (1/4, 1/2,
1/4)`. -/
theorem path_pi_QA :
    stationaryVec pathAdj = ![1/4, 1/2, 1/4] := by
  funext i
  fin_cases i
  all_goals simp only [stationaryVec, vol, deg, pathAdj,
    Matrix.of_apply, Fin.sum_univ_three]
  all_goals norm_num

/-!
## Stationarity, through the theorem and raw
-/

/-- Theorem route: the adjoint walk fixes `π`. -/
theorem path_stationary_QA :
    (walkTransitionMatrix pathAdj)ᵀ *ᵥ stationaryVec pathAdj
      = stationaryVec pathAdj :=
  walk_isStationary pathAdj pathAdj_isSymm pathAdj_deg_pos

/-- Raw cross-check, independent of the theorem: computing
`Pᵀ *ᵥ (1/4, 1/2, 1/4)` entrywise from the matrix definition gives
back `(1/4, 1/2, 1/4)`. -/
theorem path_stationary_raw_QA :
    (walkTransitionMatrix pathAdj)ᵀ *ᵥ ![1/4, 1/2, 1/4]
      = ![1/4, 1/2, 1/4] := by
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, pathAdj, Matrix.mulVec,
    Matrix.dotProduct, Matrix.transpose_apply, Fin.sum_univ_three]
  all_goals norm_num

/-!
## Walk distributions at `t = 0, 1, 2` (started at vertex 0)
-/

theorem path_dist_zero_QA :
    walkDistribution pathAdj 0 0 = ![1, 0, 0] := by
  funext i
  fin_cases i
  all_goals simp [walkDistribution_zero, Pi.single_apply]

theorem path_dist_one_QA :
    walkDistribution pathAdj 1 0 = ![0, 1, 0] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, pathAdj, Matrix.mulVec,
    Matrix.dotProduct, Matrix.transpose_apply, Fin.sum_univ_three,
    Pi.single_apply]

theorem path_dist_two_QA :
    walkDistribution pathAdj 2 0 = ![1/2, 0, 1/2] := by
  have h2 : walkDistribution pathAdj 2 0
      = (walkTransitionMatrix pathAdj)ᵀ *ᵥ walkDistribution pathAdj 1 0 :=
    walkDistribution_succ pathAdj 1 0
  rw [h2, path_dist_one_QA]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, pathAdj, Matrix.mulVec,
    Matrix.dotProduct, Matrix.transpose_apply, Fin.sum_univ_three]
  all_goals norm_num

/-- Mass conservation instantiated: the `t = 2` law sums to one. -/
theorem path_dist_sum_QA :
    ∑ i, walkDistribution pathAdj 2 0 i = 1 :=
  sum_walkDistribution pathAdj pathAdj_deg_pos 2 0

/-- The same mass recomputed from the pinned literal `t = 2` law. -/
theorem path_dist_sum_raw_QA :
    ∑ i, (![1/2, 0, 1/2] : Fin 3 → ℝ) i = 1 := by
  simp [Fin.sum_univ_three]
  norm_num

/-!
## Density evolution, through the theorem and raw
-/

/-- `h₀ = δ₀/π = (4, 0, 0)`. -/
theorem path_density_zero_QA :
    walkDensity pathAdj 0 0 = ![4, 0, 0] := by
  funext i
  fin_cases i
  all_goals simp [walkDensity, path_dist_zero_QA, path_pi_QA]

/-- `h₁ = (0, 1, 0)/(1/4, 1/2, 1/4) = (0, 2, 0)`. -/
theorem path_density_one_QA :
    walkDensity pathAdj 1 0 = ![0, 2, 0] := by
  funext i
  fin_cases i
  all_goals simp [walkDensity, path_dist_one_QA, path_pi_QA]

/-- Theorem route: the density evolution `h₁ = P *ᵥ h₀`, the
detailed-balance consumer. -/
theorem path_density_succ_QA :
    walkDensity pathAdj (0 + 1) 0
      = walkTransitionMatrix pathAdj *ᵥ walkDensity pathAdj 0 0 :=
  walkDensity_succ pathAdj pathAdj_isSymm pathAdj_deg_pos 0 0

/-- Raw cross-check: `P *ᵥ (4, 0, 0) = (0, 2, 0)` computed from the
matrix definition — the two pinned densities really are related by
`P` itself, not its adjoint. -/
theorem path_density_succ_raw_QA :
    walkTransitionMatrix pathAdj *ᵥ ![4, 0, 0] = ![0, 2, 0] := by
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, pathAdj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-!
## The χ² distance: `t = 0` and `t = 2`, theorem and raw
-/

/-- Theorem route: `χ²(0, 0) = (π 0)⁻¹ − 1 = 4 − 1 = 3`. -/
theorem path_chi2_zero_QA :
    chiSquareDistance pathAdj 0 0 = 3 := by
  rw [chiSquareDistance_zero pathAdj pathAdj_deg_pos 0, path_pi_QA]
  norm_num

/-- Raw route: `∑ (δ₀ − π)²/π` evaluated termwise from the pinned
point mass and pinned π — `9/4 + 1/2 + 1/4 = 3`. -/
theorem path_chi2_zero_raw_QA :
    chiSquareDistance pathAdj 0 0 = 3 := by
  simp only [chiSquareDistance, path_dist_zero_QA, path_pi_QA,
    Fin.sum_univ_three]
  norm_num

/-- `χ²(2, 0)` from the pinned two-step law `(1/2, 0, 1/2)`:
`1/4 + 1/2 + 1/4 = 1`. On this bipartite fixture the distance
oscillates (`χ²(1) = χ²(2) = 1`), never decaying — the λ* = 1
behavior of the path, consistent with the Step-3 bound shape. -/
theorem path_chi2_two_QA :
    chiSquareDistance pathAdj 2 0 = 1 := by
  simp only [chiSquareDistance, path_dist_two_QA, path_pi_QA,
    Fin.sum_univ_three]
  norm_num

theorem path_chi2_nonneg_QA :
    0 ≤ chiSquareDistance pathAdj 2 0 :=
  chiSquareDistance_nonneg pathAdj pathAdj_deg_pos 2 0

/-- The density-form equivalence instantiated. -/
theorem path_chi2_sum_smul_QA :
    chiSquareDistance pathAdj 2 0
      = ∑ i, stationaryVec pathAdj i
          * (walkDensity pathAdj 2 0 i - 1)^2 :=
  chiSquareDistance_eq_sum_smul pathAdj pathAdj_deg_pos 2 0

/-- The density-form sum recomputed from the pinned law and π:
`h₂ = (2, 0, 2)`, so `∑ π (h₂ − 1)² = 1/4 + 1/2 + 1/4 = 1` — agreeing
with `path_chi2_two_QA`, the equivalence's numeric content. -/
theorem path_chi2_sum_smul_raw_QA :
    ∑ i, stationaryVec pathAdj i
        * ((walkDistribution pathAdj 2 0 i
            / stationaryVec pathAdj i) - 1)^2 = 1 := by
  simp only [path_dist_two_QA, path_pi_QA, Fin.sum_univ_three]
  norm_num

/-!
## The plain-ℓ² corollary bridge
-/

/-- `c := 1/2` (the largest stationary weight) bounds every entry of
π on this fixture. -/
theorem path_pi_le_half_QA (i : Fin 3) :
    stationaryVec pathAdj i ≤ 1/2 := by
  rw [path_pi_QA]
  fin_cases i <;> simp <;> norm_num

/-- The bridge instantiated: the unweighted sum of squared deviations
`3/8` is at most `(1/2) · χ²(2, 0) = 1/2`. -/
theorem path_plain_l2_QA :
    ∑ i, (walkDistribution pathAdj 2 0 i - stationaryVec pathAdj i)^2
      ≤ (1/2) * chiSquareDistance pathAdj 2 0 :=
  sum_sub_sq_walkDistribution_le pathAdj pathAdj_deg_pos 2 0 (1/2)
    path_pi_le_half_QA

/-- The unweighted sum pinned: `∑ (ν₂ − π)² = 1/16 + 1/4 + 1/16 =
3/8 ≤ 1/2 = (1/2) · 1` — the bridge's numeric content at the fixture,
strict. -/
theorem path_plain_l2_raw_QA :
    ∑ i, (walkDistribution pathAdj 2 0 i - stationaryVec pathAdj i)^2
      = 3/8 := by
  simp only [path_dist_two_QA, path_pi_QA, Fin.sum_univ_three]
  norm_num

/-!
## Negative witness 1: symmetry is load-bearing for stationarity

The asymmetric adjacency `!![0, 2; 1, 0]` has positive degrees (2, 1),
so every hypothesis of `walk_isStationary` except `IsSymm` holds — and
the hypothesis-free stationarity statement is refuted at entry 0,
exactly where symmetry fails.
-/

/-- The asymmetric two-vertex adjacency: edge weights 2 and 1. -/
def asyAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 2; 1, 0]

theorem asyAdj_deg_pos_QA (i : Fin 2) : 0 < deg asyAdj i := by
  fin_cases i <;>
    simp only [deg, asyAdj, Matrix.of_apply, Fin.sum_univ_two] <;>
    norm_num

theorem asyAdj_not_isSymm_QA : ¬ asyAdj.IsSymm := by
  intro h
  have e := h.apply 0 1
  simp only [asyAdj, Matrix.of_apply] at e
  norm_num at e

/-- Hypothesis-free stationarity refuted: `Pᵀ *ᵥ π ≠ π` at the first
entry (`1/3 ≠ 2/3`), with degrees positive — only the symmetry
hypothesis is missing. -/
theorem asyAdj_not_stationary_QA :
    (walkTransitionMatrix asyAdj)ᵀ *ᵥ stationaryVec asyAdj
      ≠ stationaryVec asyAdj := by
  intro h
  have e0 := congrFun h 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    walkTransitionMatrix, Matrix.diagonal_mul, stationaryVec, vol,
    deg, asyAdj, Matrix.of_apply, Fin.sum_univ_two] at e0
  norm_num at e0

/-!
## Negative witness 2: degree positivity is load-bearing for the
vanishing characterization

The zero adjacency has all degrees zero, so `stationaryVec` is the
junk zero vector and `χ²(0) = 0` — while the walk law is the point
mass, not `π`. The hypothesis-free `χ² = 0 ↔ ν = π` fails.
-/

/-- The zero adjacency on `Fin 2`: all degrees zero. -/
def zeroAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 0; 0, 0]

theorem zeroAdj_deg_QA (i : Fin 2) : deg zeroAdj i = 0 := by
  fin_cases i <;>
    simp only [deg, zeroAdj, Matrix.of_apply, Fin.sum_univ_two] <;>
    norm_num

/-- The χ² distance evaluates to the junk value 0 at the zero
adjacency (every division is by the junk zero π entry). -/
theorem zeroAdj_chi2_QA :
    chiSquareDistance zeroAdj 0 0 = 0 := by
  simp [chiSquareDistance, walkDistribution_zero, stationaryVec, vol,
    deg, zeroAdj, Matrix.of_apply, Fin.sum_univ_two, Pi.single_apply,
    div_zero]

/-- …while the walk law is the point mass `δ₀`, not the junk zero
vector `π`: vanishing does *not* imply equality without the
degree-positivity hypothesis. -/
theorem zeroAdj_dist_ne_pi_QA :
    walkDistribution zeroAdj 0 0 ≠ stationaryVec zeroAdj := by
  intro h
  have e0 := congrFun h 0
  simp only [walkDistribution_zero, stationaryVec, vol, deg, zeroAdj,
    Matrix.of_apply, Fin.sum_univ_two, Pi.single_apply, div_zero] at e0
  norm_num at e0

/-!
## The path fixture: exact oscillation through the decay engine

The path's λ* is 1 (bipartite), so the decay bound there predicts *no*
decay — the engine's exact identity must reproduce the pinned
oscillation `χ²(2) = 1`. The centered initial density is
`h₀ − 1 = (4, 0, 0) − 1 = (3, −1, −1)`.
-/

/-- The centered initial density of the path walk started at vertex 0. -/
def pathG : Fin 3 → ℝ := ![3, -1, -1]

/-- One raw walk step on the centered density: `P *ᵥ (3, −1, −1) =
(−1, 1, −1)`. -/
theorem path_walk_pow_one :
    (walkTransitionMatrix pathAdj) *ᵥ pathG = ![-1, 1, -1] := by
  funext j
  fin_cases j
  all_goals simp [walkTransitionMatrix, deg, pathAdj, Matrix.of_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, pathG]
  all_goals norm_num

/-- Two raw walk steps: `P² *ᵥ (3, −1, −1) = (1, −1, 1)` — the
bipartite oscillation `h_t − 1` alternates between the two sign
patterns, never decaying. -/
theorem path_walk_pow_two :
    (walkTransitionMatrix pathAdj ^ 2) *ᵥ pathG = ![1, -1, 1] := by
  rw [pow_two, ← Matrix.mulVec_mulVec, path_walk_pow_one]
  funext j
  fin_cases j
  all_goals simp [walkTransitionMatrix, deg, pathAdj, Matrix.of_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- The conjugated two-step norm pinned raw: `‖√D (1, −1, 1)‖² =
1 + 2 + 1 = 4` (independent of any eigen machinery). -/
theorem path_engine_norm_QA :
    Matrix.dotProduct
        (degreeSqrt pathAdj *ᵥ ((walkTransitionMatrix pathAdj ^ 2) *ᵥ pathG))
        (degreeSqrt pathAdj *ᵥ ((walkTransitionMatrix pathAdj ^ 2) *ᵥ pathG))
      = 4 := by
  rw [path_walk_pow_two]
  have hdiag : ∀ k : Fin 3,
      (degreeSqrt pathAdj *ᵥ (![1, -1, 1] : Fin 3 → ℝ)) k
        = Real.sqrt (deg pathAdj k) * (![1, -1, 1] : Fin 3 → ℝ) k :=
    fun k => by simp [degreeSqrt, Matrix.mulVec_diagonal]
  have key : ∀ d c : ℝ, 0 ≤ d →
      (Real.sqrt d * c) * (Real.sqrt d * c) = d * (c * c) := by
    intro d c hd
    rw [show (Real.sqrt d * c) * (Real.sqrt d * c)
        = (Real.sqrt d * Real.sqrt d) * (c * c) from by ring,
      Real.mul_self_sqrt hd]
  have hnn : ∀ k : Fin 3, 0 ≤ deg pathAdj k :=
    fun k => le_of_lt (pathAdj_deg_pos k)
  simp only [Matrix.dotProduct, hdiag, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [key _ 1 (hnn 0), key _ (-1) (hnn 1), key _ 1 (hnn 2)]
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

/-- The exact Parseval decay identity instantiated at `t = 2` on the
path: combined with `path_engine_norm_QA`, it pins the eigencomponent
sum `∑ ((1 − μ i)² c i)²` — a basis-independent quantity — to `4`. -/
theorem path_engine_identity_QA :
    Matrix.dotProduct
        (degreeSqrt pathAdj *ᵥ ((walkTransitionMatrix pathAdj ^ 2) *ᵥ pathG))
        (degreeSqrt pathAdj *ᵥ ((walkTransitionMatrix pathAdj ^ 2) *ᵥ pathG))
      = ∑ i, ((1 - eigvalOf (normalizedLaplacian pathAdj)
              (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) ^ 2
          * Matrix.dotProduct
              (eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
              (degreeSqrt pathAdj *ᵥ pathG)) ^ 2 :=
  dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix pathAdj
    pathAdj_isSymm pathAdj_deg_pos 2 pathG

/-- The pinned eigencomponent sum: the engine's exact identity, with
both sides evaluated, reads `4 = 4`. -/
theorem path_engine_eigensum_QA :
    ∑ i, ((1 - eigvalOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) ^ 2
        * Matrix.dotProduct
            (eigvecOf (normalizedLaplacian pathAdj)
              (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
            (degreeSqrt pathAdj *ᵥ pathG)) ^ 2
      = 4 := by
  rw [← path_engine_identity_QA, path_engine_norm_QA]

/-- **The oscillation cross-check**: the π-norm bridge ties the engine's
two-step quantity to the already-pinned `χ²(2, 0) = 1` —
`∑ π (P² (h₀ − 1))² = χ²(2, 0) = 1 = (1/vol) · 4` with `vol = 4`. This
is the consistency the λ* = 1 fixture demands: no decay, exact
oscillation, engine and χ² agreeing. -/
theorem path_engine_bridge_QA :
    ∑ i, stationaryVec pathAdj i
        * (((walkTransitionMatrix pathAdj ^ 2) *ᵥ pathG) i) ^ 2
      = chiSquareDistance pathAdj 2 0 := by
  have hL : ∑ i, stationaryVec pathAdj i
      * (![1, -1, 1] : Fin 3 → ℝ) i ^ 2 = 1 := by
    simp only [path_pi_QA, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num
  rw [path_walk_pow_two, hL, path_chi2_two_QA]

/-!
## The triangle fixture: genuine decay at rate 1/2

The triangle `K₃` is connected and non-bipartite: its walk spectrum is
`{1, −1/2, −1/2}`, so λ* = 1/2 and the contraction has real content —
the bound is *exact* on the centered initial density. All eigen-facts
are derived without naming Mathlib's classically chosen basis vectors:
only the unit norm, the eigen equation entrywise, and linear arithmetic.
-/

section Triangle

/-- Adjacency of the triangle `K₃` on `Fin 3`: symmetric, unit weights,
degrees (2, 2, 2), stationary `π = (1/3, 1/3, 1/3)`. -/
def triAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 1; 1, 0, 1; 1, 1, 0]

/-- Entry table for the triangle: `0` on the diagonal, `1` off it. The
`fin_cases`-grounded statement avoids matrix-literal evaluation issues
at higher indices (entries are `rfl`). -/
theorem triAdj_apply (i j : Fin 3) :
    triAdj i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem triAdj_isSymm : triAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [triAdj_apply, triAdj_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

local notation "triL" => normalizedLaplacian triAdj
local notation "triH" => normalizedLaplacian_symmetric triAdj triAdj_isSymm

theorem triAdj_deg_eq (i : Fin 3) : deg triAdj i = 2 := by
  rw [deg]
  fin_cases i <;> simp [triAdj_apply, Fin.sum_univ_three] <;> norm_num

theorem triAdj_deg_pos (i : Fin 3) : 0 < deg triAdj i := by
  rw [triAdj_deg_eq]
  norm_num

theorem tri_vol_QA : vol triAdj (Finset.univ : Finset (Fin 3)) = 6 := by
  simp only [vol, triAdj_deg_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

theorem tri_pi_QA (i : Fin 3) : stationaryVec triAdj i = 1/3 := by
  simp only [stationaryVec, tri_vol_QA, triAdj_deg_eq]
  norm_num

/-- The symmetrized adjacency action on the triangle:
`(D^{-1/2} A D^{-1/2}) *ᵥ w = (1/2) • (A *ᵥ w)` entrywise — the
`√2 · √2 = 2` cancellation is the only input. -/
theorem tri_conj_mulVec_apply (w : Fin 3 → ℝ) (j : Fin 3) :
    (((degreeInvSqrt triAdj * triAdj * degreeInvSqrt triAdj) *ᵥ w) j)
      = (1/2) * (∑ k, triAdj j k * w k) := by
  have hinv : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1/2 := by
    have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  have hentry : ∀ k : Fin 3,
      (degreeInvSqrt triAdj * triAdj * degreeInvSqrt triAdj) j k
        = (1/2) * triAdj j k := by
    intro k
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply,
        Fin.sum_univ_three, triAdj_apply, triAdj_deg_eq, hinv, mul_one,
        one_mul]
  simp only [Matrix.mulVec, Matrix.dotProduct]
  rw [Finset.sum_congr rfl fun k _ => by rw [hentry k],
    Finset.sum_congr rfl fun k _ =>
      (show (1/2 * triAdj j k) * w k = (1/2) * (triAdj j k * w k) by ring),
    ← Finset.mul_sum]

/-- The normalized-Laplacian action on the triangle, entrywise. -/
theorem tri_normalizedLaplacian_mulVec_apply (w : Fin 3 → ℝ) (j : Fin 3) :
    ((normalizedLaplacian triAdj *ᵥ w) j)
      = w j - (1/2) * (∑ k, triAdj j k * w k) := by
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.sub_apply]
  congr 1
  exact tri_conj_mulVec_apply w j

/-- Entrywise eigen-equation for the triangle in explicit `1/2`-row
form — the workhorse both eigenbasis-independent pins consume. -/
theorem tri_eigen_entry (i j : Fin 3) :
    eigvalOf triL triH i * (eigvecOf triL triH i j)
      = (eigvecOf triL triH i j)
        - (1/2) * (∑ k, triAdj j k * (eigvecOf triL triH i k)) := by
  have h := congrFun
    ((isHermitian_of_isSymm triH).mulVec_eigenvectorBasis i) j
  rw [tri_normalizedLaplacian_mulVec_apply _ j, Pi.smul_apply, smul_eq_mul] at h
  exact h.symm

/-- **Every triangle eigenvalue is `0` or `3/2`** — derived without any
control over Mathlib's eigenbasis: summing the eigen equation over
coordinates gives `μ · (∑ v) = 0` (the row sums collapse), and the
quadratic form at a unit eigenvector pins `μ = 1 − (1/2)((∑ v)² − 1)`;
when `∑ v = 0` this forces `μ = 3/2`. -/
theorem tri_eigvalOf_cases (i : Fin 3) :
    eigvalOf triL triH i = 0 ∨ eigvalOf triL triH i = 3/2 := by
  have hentry := tri_eigen_entry i
  have hquad := quadForm_eigvecOf_self triH i
  set v : Fin 3 → ℝ := eigvecOf triL triH i with hv
  set μ : ℝ := eigvalOf triL triH i with hμdef
  have hunit : ∑ k, v k * v k = 1 := by
    rw [hv]
    simpa using eigvecOf_inner triL triH i i
  have hrow : ∀ k : Fin 3, ∑ j, triAdj j k = 2 := by
    intro k
    fin_cases k <;>
      simp [triAdj_apply, Fin.sum_univ_three] <;>
      norm_num
  have hsumrow : ∑ j, ∑ k, triAdj j k * v k = 2 * ∑ j, v j := by
    rw [Finset.sum_comm]
    have hstep : ∑ k, (∑ j, triAdj j k * v k) = ∑ k, 2 * v k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_congr rfl fun j _ => mul_comm (triAdj j k) (v k),
        ← Finset.mul_sum, hrow k]
      ring
    rw [hstep, ← Finset.mul_sum]
  have hzero : μ * (∑ j, v j) = 0 := by
    have h1 : ∑ j, μ * v j
        = ∑ j, (v j - (1/2) * (∑ k, triAdj j k * v k)) :=
      Finset.sum_congr rfl fun j _ => hentry j
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hsumrow] at h1
    linarith
  have hvAv : ∑ j, v j * (∑ k, triAdj j k * v k)
      = (∑ j, v j)^2 - 1 := by
    simp only [Fin.sum_univ_three] at hunit
    have hrow0 : (∑ k, triAdj 0 k * v k) = v 1 + v 2 := by
      simp [triAdj_apply, Fin.sum_univ_three]
    have hrow1 : (∑ k, triAdj 1 k * v k) = v 0 + v 2 := by
      simp [triAdj_apply, Fin.sum_univ_three]
    have hrow2 : (∑ k, triAdj 2 k * v k) = v 0 + v 1 := by
      simp [triAdj_apply, Fin.sum_univ_three]
    rw [show (∑ j, v j * (∑ k, triAdj j k * v k))
          = v 0 * (∑ k, triAdj 0 k * v k)
            + v 1 * (∑ k, triAdj 1 k * v k)
            + v 2 * (∑ k, triAdj 2 k * v k) from Fin.sum_univ_three _,
      hrow0, hrow1, hrow2,
      show (∑ j, v j) = v 0 + v 1 + v 2 from Fin.sum_univ_three _]
    linear_combination (-1) * hunit
  have hqf : μ = 1 - (1/2) * ((∑ j, v j)^2 - 1) := by
    rw [← hquad,
      show quadForm triL v = (v) ⬝ᵥ (triL *ᵥ v) from rfl]
    have hdot : (v) ⬝ᵥ (triL *ᵥ v)
        = (∑ j, v j * v j)
          - (1/2) * (∑ j, v j * (∑ k, triAdj j k * v k)) := by
      have hsplit : ∀ j : Fin 3,
          v j * (v j - (1/2) * (∑ k, triAdj j k * v k))
            = v j * v j
              - (1/2) * (v j * (∑ k, triAdj j k * v k)) := fun j => by ring
      simp only [Matrix.dotProduct, tri_normalizedLaplacian_mulVec_apply v]
      rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib,
        ← Finset.mul_sum]
    rw [hdot, hunit, hvAv]
  rcases mul_eq_zero.mp hzero with h0 | hs0
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [hqf, hs0]
    norm_num

/-- **The triangle kernel is the constant direction**: every
zero-eigenvalue eigenvector is a constant vector (pairwise differences
of the eigen equations force all coordinates equal). -/
theorem tri_kernel_const (i : Fin 3) (h : eigvalOf triL triH i = 0) :
    ∃ c : ℝ, ∀ j, eigvecOf triL triH i j = c := by
  have hev : ∀ j : Fin 3, (eigvecOf triL triH i j)
      = (1/2) * (∑ k, triAdj j k * (eigvecOf triL triH i k)) := by
    intro j
    have h' := tri_eigen_entry i j
    rw [h, zero_mul] at h'
    linarith
  have e0 := hev 0
  have e1 := hev 1
  have e2 := hev 2
  simp only [Fin.sum_univ_three] at e0 e1 e2
  simp [triAdj_apply] at e0 e1 e2
  refine ⟨eigvecOf triL triH i 0, ?_⟩
  intro j
  fin_cases j
  · rfl
  · show eigvecOf triL triH i 1 = eigvecOf triL triH i 0
    linarith [e0, e1, e2]
  · show eigvecOf triL triH i 2 = eigvecOf triL triH i 0
    linarith [e0, e1, e2]

/-- The trace of the triangle's normalized Laplacian: each diagonal
entry is `1 − 0 = 1` (no loops), so the trace is `3`. -/
theorem tri_trace : (normalizedLaplacian triAdj).trace = 3 := by
  have hz : ∀ j : Fin 3,
      (degreeInvSqrt triAdj * triAdj * degreeInvSqrt triAdj) j j = 0 := by
    intro j
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    fin_cases j <;>
      simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply,
        Fin.sum_univ_three, triAdj, triAdj_deg_eq,
        Real.mul_self_sqrt h2]
  simp [Matrix.trace, normalizedLaplacian, hz]

/-- The triangle has a kernel index: a zero eigenvalue must occur, since
`∑ eigvalOf = trace = 3` while three copies of `3/2` would sum to
`9/2`. -/
theorem tri_exists_kernel_index : ∃ i : Fin 3, eigvalOf triL triH i = 0 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ i : Fin 3, eigvalOf triL triH i = 3/2 := fun i => by
    rcases tri_eigvalOf_cases i with h0 | h32
    · exact absurd h0 (hcon i)
    · exact h32
  have htr := eigvalOf_sum_eq_trace triL triH
  rw [Finset.sum_congr rfl fun i _ => hall i, tri_trace] at htr
  norm_num at htr

/-- **The rate hypothesis on the triangle**: `r = 1/2` dominates every
decaying walk factor — `|1 − 3/2| = 1/2`. -/
theorem tri_rate_QA (i : Fin 3) (h : eigvalOf triL triH i ≠ 0) :
    |1 - eigvalOf triL triH i| ≤ 1/2 := by
  rcases tri_eigvalOf_cases i with h0 | h32
  · exact absurd h0 h
  · rw [h32, show (1:ℝ) - 3/2 = -1/2 from by norm_num,
      abs_of_neg (by norm_num)]
    norm_num

/-- The centered initial density of the triangle walk started at vertex
0: `h₀ − 1 = (3, 0, 0) − 1 = (2, −1, −1)`. -/
def triG : Fin 3 → ℝ := ![2, -1, -1]

theorem tri_density_zero_QA :
    walkDensity triAdj 0 0 = ![3, 0, 0] := by
  funext i
  fin_cases i
  all_goals simp [walkDensity, walkDistribution_zero, tri_pi_QA,
    Pi.single_apply]

/-- The centered density is `triG`: `h₀ − 1 = (2, −1, −1)`. -/
theorem tri_centered_density :
    (fun i => walkDensity triAdj 0 0 i - 1) = triG := by
  funext i
  fin_cases i
  all_goals simp [tri_density_zero_QA, triG]
  all_goals norm_num

/-- **The mode hypothesis on the triangle**: the conjugated centered
density has no kernel component — the kernel direction is constant, and
`(1, 1, 1) ⬝ᵥ √D (2, −1, −1) = √2 (2 − 1 − 1) = 0`. This is where mass
conservation meets the engine, on the fixture. -/
theorem tri_mode_QA (i : Fin 3) (h : eigvalOf triL triH i = 0) :
    Matrix.dotProduct (eigvecOf triL triH i)
        (degreeSqrt triAdj *ᵥ triG) = 0 := by
  obtain ⟨c, hc⟩ := tri_kernel_const i h
  have hsqrt : ∀ k : Fin 3, (degreeSqrt triAdj *ᵥ triG) k
      = Real.sqrt 2 * triG k := by
    intro k
    have h1 : (degreeSqrt triAdj *ᵥ triG) k
        = Real.sqrt (deg triAdj k) * triG k := by
      simp [degreeSqrt, Matrix.mulVec_diagonal]
    rw [h1, triAdj_deg_eq]
  have hterm : ∀ k : Fin 3,
      (eigvecOf triL triH i k) * ((degreeSqrt triAdj *ᵥ triG) k)
        = c * (Real.sqrt 2 * triG k) := by
    intro k
    simp only [hsqrt, hc k]
  rw [Matrix.dotProduct, Finset.sum_congr rfl fun k _ => hterm k,
    ← Finset.mul_sum]
  have hsum : ∑ k, Real.sqrt 2 * triG k = 0 := by
    simp [Fin.sum_univ_three, triG]
    ring
  rw [hsum]
  ring

/-- One raw walk step: `P *ᵥ (2, −1, −1) = (−1, 1/2, 1/2)`. -/
theorem tri_walk_pow_one :
    (walkTransitionMatrix triAdj ^ 1) *ᵥ triG = ![-1, 1/2, 1/2] := by
  rw [pow_one]
  funext j
  fin_cases j
  all_goals simp [walkTransitionMatrix, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, triG]
  all_goals norm_num

/-- Two raw walk steps: `P² *ᵥ (2, −1, −1) = (1/2, −1/4, −1/4)`. -/
theorem tri_walk_pow_two :
    (walkTransitionMatrix triAdj ^ 2) *ᵥ triG = ![1/2, -1/4, -1/4] := by
  rw [pow_two, ← Matrix.mulVec_mulVec triG (walkTransitionMatrix triAdj)
      (walkTransitionMatrix triAdj),
    show walkTransitionMatrix triAdj
        = walkTransitionMatrix triAdj ^ 1 from (pow_one _).symm,
    tri_walk_pow_one, pow_one]
  funext j
  fin_cases j
  all_goals simp [walkTransitionMatrix, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, triG]
  all_goals norm_num

/-- The initial π-norm pinned: `∑ π (2, −1, −1)² = (1/3) · 6 = 2`. -/
theorem tri_l2_zero_QA :
    ∑ i, stationaryVec triAdj i * (triG i)^2 = 2 := by
  simp only [tri_pi_QA, Fin.sum_univ_three, triG,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- The one-step π-norm pinned: `∑ π (−1, 1/2, 1/2)² = 1/2`. -/
theorem tri_l2_one_QA :
    ∑ i, stationaryVec triAdj i
        * (((walkTransitionMatrix triAdj ^ 1) *ᵥ triG) i)^2 = 1/2 := by
  rw [tri_walk_pow_one]
  simp only [tri_pi_QA, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num

/-- The two-step π-norm pinned: `∑ π (1/2, −1/4, −1/4)² = 1/8`. -/
theorem tri_l2_two_QA :
    ∑ i, stationaryVec triAdj i
        * (((walkTransitionMatrix triAdj ^ 2) *ᵥ triG) i)^2 = 1/8 := by
  rw [tri_walk_pow_two]
  simp only [tri_pi_QA, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  norm_num

/-- **The contraction instantiated, `t = 1`**: `1/2 ≤ (1/2)² · 2 = 1/2`
— exact. The walk spectrum `{1, −1/2, −1/2}` gives a genuine geometric
rate on this fixture, unlike the path's λ* = 1. -/
theorem tri_decay_one_QA :
    ∑ i, stationaryVec triAdj i
        * (((walkTransitionMatrix triAdj ^ 1) *ᵥ triG) i)^2
      ≤ (1/2)^(2 * 1) * ∑ i, stationaryVec triAdj i * (triG i)^2 :=
  sum_stationaryVec_smul_sq_pow_walkTransitionMatrix_le triAdj
    triAdj_isSymm triAdj_deg_pos triG (1/2) 1 tri_mode_QA tri_rate_QA

/-- **The contraction instantiated, `t = 2`**: `1/8 ≤ (1/2)⁴ · 2 = 1/8`
— exact again: on the triangle the decay is geometric at exactly rate
`1/4` per step-pair, hand-checked `2 → 1/2 → 1/8`. -/
theorem tri_decay_two_QA :
    ∑ i, stationaryVec triAdj i
        * (((walkTransitionMatrix triAdj ^ 2) *ᵥ triG) i)^2
      ≤ (1/2)^(2 * 2) * ∑ i, stationaryVec triAdj i * (triG i)^2 :=
  sum_stationaryVec_smul_sq_pow_walkTransitionMatrix_le triAdj
    triAdj_isSymm triAdj_deg_pos triG (1/2) 2 tri_mode_QA tri_rate_QA

/-- The numerics behind both instances, pinned side by side: the raw
π-norms `1/2` and `1/8` against the bounds `(1/4) · 2` and `(1/16) · 2`
— equalities. -/
theorem tri_decay_exact_QA :
    ((1/2)^(2 * 1) * ∑ i, stationaryVec triAdj i * (triG i)^2 = 1/2 ∧
     (1/2)^(2 * 2) * ∑ i, stationaryVec triAdj i * (triG i)^2 = 1/8) := by
  rw [tri_l2_zero_QA]
  norm_num

/-- The constant vector is fixed by the walk (row sums one), pinned
raw. -/
theorem tri_walk_pow_one_const :
    (walkTransitionMatrix triAdj ^ 1) *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
  rw [pow_one]
  funext j
  fin_cases j
  all_goals simp [walkTransitionMatrix, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- **Negative witness — the mode hypothesis is load-bearing**: at
`g = 1` the mode hypothesis provably fails (the kernel eigenvector is
constant with nonzero coefficient against `√D *ᵥ 1`), and the
conclusion fails with it — the hypothesis-free bound would read
`1 ≤ 1/4`. -/
theorem tri_mode_guard_QA :
    ¬ (∑ i, stationaryVec triAdj i
          * (((walkTransitionMatrix triAdj ^ 1) *ᵥ (fun _ => (1:ℝ))) i)^2
        ≤ (1/2)^(2 * 1)
          * ∑ i, stationaryVec triAdj i * ((fun _ => (1:ℝ)) i)^2) := by
  intro h
  have hsum : ∑ i, stationaryVec triAdj i * ((1:ℝ))^2 = 1 := by
    simpa using sum_stationaryVec triAdj triAdj_deg_pos
  rw [tri_walk_pow_one_const, hsum] at h
  norm_num at h

/-- The mode hypothesis itself fails at the kernel index: the kernel
eigenvector (constant, `c ≠ 0` by unit norm) has coefficient
`3 · c · √2 ≠ 0` against `√D *ᵥ 1`. -/
theorem tri_mode_guard_hyp_QA :
    ∃ i : Fin 3, eigvalOf triL triH i = 0 ∧
      Matrix.dotProduct (eigvecOf triL triH i)
        (degreeSqrt triAdj *ᵥ (fun _ => (1:ℝ))) ≠ 0 := by
  obtain ⟨i, hi⟩ := tri_exists_kernel_index
  obtain ⟨c, hc⟩ := tri_kernel_const i hi
  refine ⟨i, hi, ?_⟩
  intro hzero
  have hunit : ∑ k, (eigvecOf triL triH i k) * (eigvecOf triL triH i k)
      = 1 := by
    simpa using eigvecOf_inner triL triH i i
  have hsqrt : ∀ k : Fin 3,
      (degreeSqrt triAdj *ᵥ (fun _ => (1:ℝ))) k = Real.sqrt 2 := by
    intro k
    have h1 : (degreeSqrt triAdj *ᵥ (fun _ => (1:ℝ))) k
        = Real.sqrt (deg triAdj k) * 1 := by
      simp [degreeSqrt, Matrix.mulVec_diagonal]
    rw [h1, triAdj_deg_eq, mul_one]
  have hterm : ∀ k : Fin 3,
      (eigvecOf triL triH i k)
          * ((degreeSqrt triAdj *ᵥ (fun _ => (1:ℝ))) k)
        = c * Real.sqrt 2 := by
    intro k
    simp only [hsqrt, hc k]
  rw [Matrix.dotProduct, Finset.sum_congr rfl fun k _ => hterm k] at hzero
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hzero
  simp only [hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hunit
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hc0 : c = 0 := by
    rcases mul_eq_zero.mp hzero with h3 | hcsq
    · norm_num at h3
    · rcases mul_eq_zero.mp hcsq with h | h
      · exact h
      · exact absurd h hs2
  rw [hc0] at hunit
  norm_num at hunit

/-!
## Step 3, component 2 — the χ² assembly on the fixtures

The final mixing statement `chiSquareDistance_le_of_connected`
instantiated on both fixtures (its rate hypothesis derived
basis-independently), the centered evolution and the connectivity mode
lemma cross-checked against the pinned component-1 facts, and the two
load-bearing negative witnesses: connectivity (a triangle⊕self-loop
`Fin 4` fixture where the rate hypothesis genuinely holds at `r = 1/2`
yet the conclusion is refuted — the loop's `μ = 0` mode is excluded
from the rate hypothesis by design, exactly the hole connectivity
plugs) and the rate itself (`r = 1/4` on the triangle: hypothesis
provably unsatisfiable by the trace, conclusion refuted).
-/

/-- The triangle adjacency is entrywise nonnegative. -/
theorem triAdj_nonneg (i j : Fin 3) : 0 ≤ triAdj i j := by
  rw [triAdj_apply]
  split <;> norm_num

/-- The triangle's support graph is connected: both other vertices are
reachable from `0` by one explicit edge-walk. -/
theorem tri_connected :
    (supportGraph triAdj triAdj_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 3,
      (supportGraph triAdj triAdj_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        ⟨by decide, by norm_num [triAdj]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
        ⟨by decide, by norm_num [triAdj]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- The one-step law from vertex 0 on the triangle: `(0, 1/2, 1/2)`. -/
theorem tri_dist_one_QA :
    walkDistribution triAdj 1 0 = ![0, 1/2, 1/2] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, triAdj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_three, Pi.single_apply]
  all_goals norm_num

/-- The two-step law: `(1/2, 1/4, 1/4)`. -/
theorem tri_dist_two_QA :
    walkDistribution triAdj 2 0 = ![1/2, 1/4, 1/4] := by
  have h2 : walkDistribution triAdj 2 0
      = (walkTransitionMatrix triAdj)ᵀ *ᵥ walkDistribution triAdj 1 0 :=
    walkDistribution_succ triAdj 1 0
  rw [h2, tri_dist_one_QA]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  all_goals norm_num

/-- The one-step density: `h₁ = (0, 3/2, 3/2)`. -/
theorem tri_density_one_QA :
    walkDensity triAdj 1 0 = ![0, 3/2, 3/2] := by
  funext i
  fin_cases i
  all_goals simp [walkDensity, tri_dist_one_QA, tri_pi_QA]
  all_goals norm_num

/-- `χ²(1, 0)` pinned raw: `(1/9 + 2/36)/(1/3) = 1/2`. -/
theorem tri_chi2_one_QA :
    chiSquareDistance triAdj 1 0 = 1/2 := by
  simp only [chiSquareDistance, tri_dist_one_QA, tri_pi_QA,
    Fin.sum_univ_three]
  norm_num

/-- `χ²(2, 0)` pinned raw: `(1/36 + 2/144)/(1/3) = 1/8`. -/
theorem tri_chi2_two_QA :
    chiSquareDistance triAdj 2 0 = 1/8 := by
  simp only [chiSquareDistance, tri_dist_two_QA, tri_pi_QA,
    Fin.sum_univ_three]
  norm_num

/-- **The mixing bound instantiated, `t = 1`**: the final theorem on the
triangle at rate `1/2`. -/
theorem tri_mixing_one_QA :
    chiSquareDistance triAdj 1 0
      ≤ (1/2)^(2 * 1) * ((stationaryVec triAdj 0)⁻¹ - 1) :=
  chiSquareDistance_le_of_connected triAdj triAdj_isSymm triAdj_nonneg
    triAdj_deg_pos tri_connected (1/2) 1 0 tri_rate_QA

/-- **The mixing bound instantiated, `t = 2`.** -/
theorem tri_mixing_two_QA :
    chiSquareDistance triAdj 2 0
      ≤ (1/2)^(2 * 2) * ((stationaryVec triAdj 0)⁻¹ - 1) :=
  chiSquareDistance_le_of_connected triAdj triAdj_isSymm triAdj_nonneg
    triAdj_deg_pos tri_connected (1/2) 2 0 tri_rate_QA

/-- The numerics behind both instances: the bound's right side is
`(π 0)⁻¹ − 1 = 2` times the geometric factor, giving `1/2` at `t = 1`
and `1/8` at `t = 2` — **equalities**: on the triangle the χ² mixing
bound is exact, decay genuinely geometric at rate `1/4` per step-pair,
matching the engine's pinned π-norms `2 → 1/2 → 1/8`. -/
theorem tri_mixing_exact_QA :
    (1/2)^(2 * 1) * ((stationaryVec triAdj 0)⁻¹ - 1) = 1/2 ∧
      (1/2)^(2 * 2) * ((stationaryVec triAdj 0)⁻¹ - 1) = 1/8 := by
  rw [tri_pi_QA 0]
  norm_num

/-- Theorem route: the centered density evolves by the walk power. -/
theorem tri_centered_evolution_QA :
    walkDensity triAdj 1 0 - 1
      = (walkTransitionMatrix triAdj ^ 1) *ᵥ (walkDensity triAdj 0 0 - 1) :=
  walkDensity_sub_one triAdj triAdj_isSymm triAdj_deg_pos 1 0

/-- Raw cross-check: both sides of the centered evolution pinned to
`(−1, 1/2, 1/2)` — the theorem's numeric content at `t = 1`, computed
from the pinned densities (left) and the pinned walk step
`tri_walk_pow_one` (right). -/
theorem tri_centered_raw_QA :
    (walkDensity triAdj 1 0 - 1 = ![-1, 1/2, 1/2]) ∧
      ((walkTransitionMatrix triAdj ^ 1) *ᵥ triG = ![-1, 1/2, 1/2]) := by
  refine ⟨?_, tri_walk_pow_one⟩
  funext i
  fin_cases i
  all_goals simp [tri_density_one_QA]
  all_goals norm_num

/-- The connectivity mode derivation instantiated: on the triangle, the
kernel eigenvector is orthogonal to the conjugated centered density. -/
theorem tri_mode_conn_QA (i : Fin 3) (h : eigvalOf triL triH i = 0) :
    Matrix.dotProduct (eigvecOf triL triH i)
        (degreeSqrt triAdj *ᵥ (walkDensity triAdj 0 0 - 1)) = 0 :=
  eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero
    triAdj triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected 0 h

/-- The connectivity-derived mode fact *is* the hand-derived
`tri_mode_QA`: the centered initial density is `triG`, so the two
statements agree — the general theorem reproduces the fixture-level
derivation exactly. -/
theorem tri_mode_conn_eq_hand_QA (i : Fin 3) (_h : eigvalOf triL triH i = 0) :
    Matrix.dotProduct (eigvecOf triL triH i)
        (degreeSqrt triAdj *ᵥ (walkDensity triAdj 0 0 - 1))
      = Matrix.dotProduct (eigvecOf triL triH i)
          (degreeSqrt triAdj *ᵥ triG) := by
  have hf : walkDensity triAdj 0 0 - 1 = triG := by
    funext i
    rw [Pi.sub_apply, Pi.one_apply]
    exact congrFun tri_centered_density i
  rw [hf]

/-- **Negative witness — the rate hypothesis is load-bearing**: at
`r = 1/4` the rate hypothesis is provably unsatisfiable on the triangle
(any `3/2` eigenvalue violates it, and the trace forbids all-zero), and
the conclusion fails with it — `χ²(1, 0) = 1/2 > 1/8 = (1/16) · 2`. -/
theorem tri_rate_guard_QA :
    (¬ ∀ i : Fin 3, eigvalOf triL triH i ≠ 0 →
        |1 - eigvalOf triL triH i| ≤ 1/4) ∧
      ¬ (chiSquareDistance triAdj 1 0
          ≤ (1/4)^(2 * 1) * ((stationaryVec triAdj 0)⁻¹ - 1)) := by
  refine ⟨?_, ?_⟩
  · intro hrate
    have hall : ∀ i : Fin 3, eigvalOf triL triH i = 0 := by
      intro i
      rcases tri_eigvalOf_cases i with h0 | h32
      · exact h0
      · have h2 := hrate i (by rw [h32]; norm_num)
        rw [h32, show (1:ℝ) - 3/2 = -1/2 from by norm_num,
          abs_of_neg (by norm_num)] at h2
        norm_num at h2
    have htr := eigvalOf_sum_eq_trace triL triH
    rw [Finset.sum_congr rfl fun i _ => hall i, tri_trace] at htr
    norm_num at htr
  · intro hcon
    rw [tri_chi2_one_QA, tri_pi_QA 0] at hcon
    norm_num at hcon

/-!
### The path fixture: the λ* = 1 bound, with the rate derived
basis-independently

The path is connected but bipartite: λ* = 1, so the bound predicts no
decay — and none is observed (`χ²(1) = χ²(2) = 1`). The rate hypothesis
at `r = 1` needs every eigenvalue in `[0, 2]`, derived without any
control over Mathlib's basis: two sum-of-squares certificates for the
quadratic form, `v ⬝ L_sym v = (v₀ − v₁/√2)² + (v₂ − v₁/√2)²` and its
`2‖v‖² − ·` counterpart.
-/

local notation "pathL" => normalizedLaplacian pathAdj
local notation "pathH" => normalizedLaplacian_symmetric pathAdj pathAdj_isSymm

theorem pathAdj_nonneg (i j : Fin 3) : 0 ≤ pathAdj i j := by
  fin_cases i <;> fin_cases j <;> simp [pathAdj]

/-- The path's support graph is connected (both ends reachable from the
center by explicit walks). -/
theorem path_connected :
    (supportGraph pathAdj pathAdj_isSymm).Connected := by
  have hfrom1 : ∀ v : Fin 3,
      (supportGraph pathAdj pathAdj_isSymm).Reachable 1 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 0) (w := 0)
        ⟨by decide, by norm_num [pathAdj]⟩ SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 1) (v := 2) (w := 2)
        ⟨by decide, by norm_num [pathAdj]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨1, hfrom1⟩

/-- The symmetrized adjacency action on the path, entrywise: every edge
carries `1/√2` (the `√1 · √2` degrees). -/
theorem path_conj_mulVec_apply (w : Fin 3 → ℝ) (j : Fin 3) :
    ((degreeInvSqrt pathAdj * pathAdj * degreeInvSqrt pathAdj) *ᵥ w) j
      = (Real.sqrt 2)⁻¹ * (∑ k, pathAdj j k * w k) := by
  have hentry : ∀ (j k : Fin 3),
      (degreeInvSqrt pathAdj * pathAdj * degreeInvSqrt pathAdj) j k
        = (Real.sqrt 2)⁻¹ * pathAdj j k := by
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply,
        pathAdj, deg, Real.sqrt_one, Fin.sum_univ_three] <;>
      ring
  simp only [Matrix.mulVec, Matrix.dotProduct]
  rw [Finset.sum_congr rfl fun k _ => by rw [hentry j k],
    Finset.sum_congr rfl fun k _ =>
      (show ((Real.sqrt 2)⁻¹ * pathAdj j k) * w k
          = (Real.sqrt 2)⁻¹ * (pathAdj j k * w k) from by ring),
    ← Finset.mul_sum]

/-- The normalized-Laplacian action on the path, entrywise. -/
theorem path_normalizedLaplacian_mulVec_apply (w : Fin 3 → ℝ) (j : Fin 3) :
    ((normalizedLaplacian pathAdj *ᵥ w)) j
      = w j - (Real.sqrt 2)⁻¹ * (∑ k, pathAdj j k * w k) := by
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.sub_apply]
  congr 1
  exact path_conj_mulVec_apply w j

/-- **The Dirichlet certificate** for the path's normalized Laplacian:
the quadratic form is exactly a sum of two squares,
`(v₀ − v₁/√2)² + (v₂ − v₁/√2)²` — nonnegative for every `v`. -/
theorem path_quadForm_eq (v : Fin 3 → ℝ) :
    ∑ k, v k * ((normalizedLaplacian pathAdj *ᵥ v) k)
      = (v 0 - (Real.sqrt 2)⁻¹ * v 1)^2
        + (v 2 - (Real.sqrt 2)⁻¹ * v 1)^2 := by
  have hinv2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1/2 := by
    have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp [hs]
  have hR : ∀ k : Fin 3, (∑ j, pathAdj k j * v j)
      = ![v 1, v 0 + v 2, v 1] k := by
    intro k
    fin_cases k <;> simp [pathAdj, Fin.sum_univ_three]
  have hsplit : ∀ k : Fin 3,
      v k * ((normalizedLaplacian pathAdj *ᵥ v) k)
      = v k * v k
        - (Real.sqrt 2)⁻¹ * (v k * (![v 1, v 0 + v 2, v 1] k)) := by
    intro k
    rw [path_normalizedLaplacian_mulVec_apply, hR k]
    ring
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (-(2 * (v 1 * v 1))) * hinv2

/-- **The upper certificate**: `2‖v‖² − v ⬝ L_sym v` is exactly a sum of
two squares — nonnegative for every `v`, the second half of the
eigenvalue band `[0, 2]`. -/
theorem path_two_sub_quadForm_eq (v : Fin 3 → ℝ) :
    2 * (∑ k, v k * v k) - ∑ k, v k * ((normalizedLaplacian pathAdj *ᵥ v) k)
      = (v 0 + (Real.sqrt 2)⁻¹ * v 1)^2
        + (v 2 + (Real.sqrt 2)⁻¹ * v 1)^2 := by
  have hinv2 : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1/2 := by
    have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp [hs]
  have hR : ∀ k : Fin 3, (∑ j, pathAdj k j * v j)
      = ![v 1, v 0 + v 2, v 1] k := by
    intro k
    fin_cases k <;> simp [pathAdj, Fin.sum_univ_three]
  have hsplit : ∀ k : Fin 3,
      v k * ((normalizedLaplacian pathAdj *ᵥ v) k)
      = v k * v k
        - (Real.sqrt 2)⁻¹ * (v k * (![v 1, v 0 + v 2, v 1] k)) := by
    intro k
    rw [path_normalizedLaplacian_mulVec_apply, hR k]
    ring
  rw [Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (-(2 * (v 1 * v 1))) * hinv2

/-- **Every path eigenvalue is nonnegative** — the Dirichlet certificate
evaluated at the (unit) eigenvector. -/
theorem path_eigvalOf_nonneg (i : Fin 3) :
    0 ≤ eigvalOf pathL pathH i := by
  have hunit : ∑ k, (eigvecOf pathL pathH i k)
      * (eigvecOf pathL pathH i k) = 1 := by
    simpa using eigvecOf_inner pathL pathH i i
  have hev0 : normalizedLaplacian pathAdj *ᵥ (eigvecOf pathL pathH i)
      = eigvalOf pathL pathH i • (eigvecOf pathL pathH i) :=
    (isHermitian_of_isSymm pathH).mulVec_eigenvectorBasis i
  have hev : ∀ k, ((normalizedLaplacian pathAdj *ᵥ
        (eigvecOf pathL pathH i)) k)
      = eigvalOf pathL pathH i * (eigvecOf pathL pathH i k) := by
    intro k
    have h := congrFun hev0 k
    rw [Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hnorm : ∑ k, (eigvecOf pathL pathH i k)
        * (eigvalOf pathL pathH i * (eigvecOf pathL pathH i k))
      = eigvalOf pathL pathH i * (∑ k, (eigvecOf pathL pathH i k)
          * (eigvecOf pathL pathH i k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hqf := path_quadForm_eq (eigvecOf pathL pathH i)
  have hsum1 : ∑ k, (eigvecOf pathL pathH i k)
        * ((normalizedLaplacian pathAdj *ᵥ (eigvecOf pathL pathH i)) k)
      = ∑ k, (eigvecOf pathL pathH i k)
          * (eigvalOf pathL pathH i * (eigvecOf pathL pathH i k)) :=
    Finset.sum_congr rfl fun k _ => by rw [hev k]
  rw [hsum1, hnorm, hunit] at hqf
  have hsos : 0 ≤ (eigvecOf pathL pathH i 0
        - (Real.sqrt 2)⁻¹ * (eigvecOf pathL pathH i 1))^2
      + (eigvecOf pathL pathH i 2
          - (Real.sqrt 2)⁻¹ * (eigvecOf pathL pathH i 1))^2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

/-- **Every path eigenvalue is at most `2`** — the upper certificate
evaluated at the (unit) eigenvector. -/
theorem path_eigvalOf_le_two (i : Fin 3) :
    eigvalOf pathL pathH i ≤ 2 := by
  have hunit : ∑ k, (eigvecOf pathL pathH i k)
      * (eigvecOf pathL pathH i k) = 1 := by
    simpa using eigvecOf_inner pathL pathH i i
  have hev0 : normalizedLaplacian pathAdj *ᵥ (eigvecOf pathL pathH i)
      = eigvalOf pathL pathH i • (eigvecOf pathL pathH i) :=
    (isHermitian_of_isSymm pathH).mulVec_eigenvectorBasis i
  have hev : ∀ k, ((normalizedLaplacian pathAdj *ᵥ
        (eigvecOf pathL pathH i)) k)
      = eigvalOf pathL pathH i * (eigvecOf pathL pathH i k) := by
    intro k
    have h := congrFun hev0 k
    rw [Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hnorm : ∑ k, (eigvecOf pathL pathH i k)
        * (eigvalOf pathL pathH i * (eigvecOf pathL pathH i k))
      = eigvalOf pathL pathH i * (∑ k, (eigvecOf pathL pathH i k)
          * (eigvecOf pathL pathH i k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hqf := path_two_sub_quadForm_eq (eigvecOf pathL pathH i)
  have hsum1 : ∑ k, (eigvecOf pathL pathH i k)
        * ((normalizedLaplacian pathAdj *ᵥ (eigvecOf pathL pathH i)) k)
      = ∑ k, (eigvecOf pathL pathH i k)
          * (eigvalOf pathL pathH i * (eigvecOf pathL pathH i k)) :=
    Finset.sum_congr rfl fun k _ => by rw [hev k]
  rw [hsum1, hnorm, hunit] at hqf
  have hsos : 0 ≤ (eigvecOf pathL pathH i 0
        + (Real.sqrt 2)⁻¹ * (eigvecOf pathL pathH i 1))^2
      + (eigvecOf pathL pathH i 2
          + (Real.sqrt 2)⁻¹ * (eigvecOf pathL pathH i 1))^2 :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

/-- **The path rate hypothesis at `r = 1`** (λ* = 1): the band
`0 ≤ μ ≤ 2` gives `|1 − μ| ≤ 1` with no exact-spectrum computation. -/
theorem path_rate_QA (i : Fin 3) (_h : eigvalOf pathL pathH i ≠ 0) :
    |1 - eigvalOf pathL pathH i| ≤ 1 := by
  have h0 := path_eigvalOf_nonneg i
  have h2 := path_eigvalOf_le_two i
  refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith

/-- `χ²(1, 0)` pinned raw: `1/4 + 1/2 + 1/4 = 1` — the bipartite
oscillation begins. -/
theorem path_chi2_one_QA :
    chiSquareDistance pathAdj 1 0 = 1 := by
  simp only [chiSquareDistance, path_dist_one_QA, path_pi_QA,
    Fin.sum_univ_three]
  norm_num

/-- **The mixing bound instantiated on the path, `t = 1`**, at the λ* = 1
rate: no decay predicted. -/
theorem path_mixing_one_QA :
    chiSquareDistance pathAdj 1 0
      ≤ (1:ℝ)^(2 * 1) * ((stationaryVec pathAdj 0)⁻¹ - 1) :=
  chiSquareDistance_le_of_connected pathAdj pathAdj_isSymm pathAdj_nonneg
    pathAdj_deg_pos path_connected 1 1 0 path_rate_QA

/-- **The mixing bound instantiated on the path, `t = 2`.** -/
theorem path_mixing_two_QA :
    chiSquareDistance pathAdj 2 0
      ≤ (1:ℝ)^(2 * 2) * ((stationaryVec pathAdj 0)⁻¹ - 1) :=
  chiSquareDistance_le_of_connected pathAdj pathAdj_isSymm pathAdj_nonneg
    pathAdj_deg_pos path_connected 1 2 0 path_rate_QA

/-- The λ* = 1 numerics: the bound's right side is `1 · 3 = 3` while
`χ²(1) = χ²(2) = 1` — no decay predicted, none observed; the bound is
honest on the bipartite fixture (strict, unlike the triangle's exact
equalities). -/
theorem path_mixing_bound_raw_QA :
    (1:ℝ)^(2 * 2) * ((stationaryVec pathAdj 0)⁻¹ - 1) = 3 ∧
      chiSquareDistance pathAdj 2 0 = 1 := by
  rw [path_pi_QA, path_chi2_two_QA]
  norm_num

/-!
### Negative witness: connectivity is load-bearing — the
triangle⊕self-loop fixture

`discAdj` is the triangle on `{0, 1, 2}` plus a self-loop of weight `2`
at vertex `3`. Every degree is `2`, so `π = (1/4, 1/4, 1/4, 1/4)` — but
the support graph is *disconnected* (a loop is not a support-graph
edge), and the loop's `L_sym` row vanishes, giving the spectrum
`{0, 0, 3/2, 3/2}`: the rate hypothesis genuinely holds at `r = 1/2`
(the `μ = 0` loop mode is excluded from it *by design*), yet the walk
never mixes across components and the mixing conclusion is refuted:
`χ²(3) = 3/8 > 3/64 = (1/2)^6 · 3`. This is exactly the hole the
connectivity hypothesis plugs.
-/

/-- Adjacency of the triangle⊕self-loop fixture on `Fin 4`. -/
def discAdj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 1, 0; 1, 0, 1, 0; 1, 1, 0, 0; 0, 0, 0, 2]

theorem discAdj_isSymm : discAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [discAdj]

/-- Entry table for the fixture: unit weights on the triangle's six
ordered edges, the loop weight `2` at `(3, 3)`, zero elsewhere. Proved
by `fin_cases` + `rfl`; consumed as the entry interface so downstream
simp never has to evaluate the raw matrix literal (whose far corner
`(3, 3)` normalizes through the notation's empty default row). -/
theorem discAdj_apply (i j : Fin 4) :
    discAdj i j = if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2)
      ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) then 1
      else if i = 3 ∧ j = 3 then 2 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem discAdj_nonneg (i j : Fin 4) : 0 ≤ discAdj i j := by
  fin_cases i <;> fin_cases j <;> norm_num [discAdj]

/-- All degrees are `2` (the loop supplies its vertex's degree). -/
theorem discAdj_deg_eq (i : Fin 4) : deg discAdj i = 2 := by
  rw [deg]
  fin_cases i <;> simp [discAdj, Fin.sum_univ_four] <;> norm_num

theorem discAdj_deg_pos (i : Fin 4) : 0 < deg discAdj i := by
  rw [discAdj_deg_eq]
  norm_num

theorem disc_vol_QA : vol discAdj (Finset.univ : Finset (Fin 4)) = 8 := by
  simp only [vol, discAdj_deg_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

theorem disc_pi_QA (i : Fin 4) : stationaryVec discAdj i = 1/4 := by
  simp only [stationaryVec, disc_vol_QA, discAdj_deg_eq]
  norm_num

/-- The third row of the adjacency vanishes off the diagonal: vertex `3`
has no support-graph edges (the loop does not count). -/
theorem discAdj_row_three (j : Fin 4) (h : (3 : Fin 4) ≠ j) :
    discAdj 3 j = 0 := by
  fin_cases j
  · rfl
  · rfl
  · rfl
  · exact absurd rfl h

/-- The support graph of the fixture is disconnected: a walk from `3`
would have to leave `3` through a support edge, and there are none. -/
theorem disc_not_connected :
    ¬(supportGraph discAdj discAdj_isSymm).Connected := by
  intro h
  obtain ⟨w⟩ := h 3 0
  cases w with
  | cons hadj _ =>
      have hne : (3 : Fin 4) ≠ _ := (supportGraph_adj.1 hadj).1
      have hpos : 0 < discAdj 3 _ := (supportGraph_adj.1 hadj).2
      rw [discAdj_row_three _ hne] at hpos
      norm_num at hpos

local notation "discL" => normalizedLaplacian discAdj
local notation "discH" => normalizedLaplacian_symmetric discAdj discAdj_isSymm

/-- The symmetrized adjacency action on the fixture: all degrees are
`2`, so `D^{-1/2} A D^{-1/2} = (1/2) A` entrywise. -/
theorem disc_conj_mulVec_apply (w : Fin 4 → ℝ) (j : Fin 4) :
    ((degreeInvSqrt discAdj * discAdj * degreeInvSqrt discAdj) *ᵥ w) j
      = (1/2) * (∑ k, discAdj j k * w k) := by
  have hinv : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1/2 := by
    have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp [hs]
  have hD : degreeInvSqrt discAdj
      = (Real.sqrt 2)⁻¹ • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    ext l m
    simp only [degreeInvSqrt, Matrix.diagonal_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply]
    by_cases h : l = m
    · subst h
      rw [discAdj_deg_eq l]
      simp
    · rw [if_neg h, if_neg h, mul_zero]
  have hconj : degreeInvSqrt discAdj * discAdj * degreeInvSqrt discAdj
      = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) • discAdj := by
    rw [hD, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
  rw [hconj, hinv]
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_congr rfl fun k _ =>
      (show (1/2) * discAdj j k * w k
          = (1/2) * (discAdj j k * w k) from by ring),
    ← Finset.mul_sum]

/-- The normalized-Laplacian action on the fixture, entrywise. Note the
third row: `(L_sym *ᵥ w) 3 = w 3 − (1/2)(2 w 3) = 0` for every `w`. -/
theorem disc_normalizedLaplacian_mulVec_apply (w : Fin 4 → ℝ) (j : Fin 4) :
    ((normalizedLaplacian discAdj *ᵥ w)) j
      = w j - (1/2) * (∑ k, discAdj j k * w k) := by
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.sub_apply]
  congr 1
  exact disc_conj_mulVec_apply w j

/-- Entrywise eigen-equation for the fixture, in explicit `1/2`-row
form. -/
theorem disc_eigen_entry (i j : Fin 4) :
    eigvalOf discL discH i * (eigvecOf discL discH i j)
      = (eigvecOf discL discH i j)
        - (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)) := by
  have h := congrFun
    ((isHermitian_of_isSymm discH).mulVec_eigenvectorBasis i) j
  rw [disc_normalizedLaplacian_mulVec_apply _ j, Pi.smul_apply,
    smul_eq_mul] at h
  exact h.symm

/-- Column sums of the fixture are `2` (symmetry of the adjacency). -/
theorem disc_col_sum (k : Fin 4) : ∑ j, discAdj j k = 2 := by
  have h1 : ∑ j, discAdj j k = ∑ j, discAdj k j :=
    Finset.sum_congr rfl fun j _ => (discAdj_isSymm.apply j k).symm
  have h2 : ∑ j, discAdj k j = 2 := discAdj_deg_eq k
  rw [h1]
  exact h2

/-- Summing the eigen equation over coordinates: `μ · (∑ v) = 0` (all
row sums are `2`). -/
theorem disc_eigen_summed (i : Fin 4) :
    eigvalOf discL discH i * (∑ j, (eigvecOf discL discH i j)) = 0 := by
  have hL : ∑ j, eigvalOf discL discH i * (eigvecOf discL discH i j)
      = ∑ j, ((eigvecOf discL discH i j)
          - (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k))) :=
    Finset.sum_congr rfl fun j _ => disc_eigen_entry i j
  have hpull : eigvalOf discL discH i * (∑ j, (eigvecOf discL discH i j))
      = ∑ j, eigvalOf discL discH i * (eigvecOf discL discH i j) :=
    Finset.mul_sum _ _ _
  rw [hpull, hL]
  have hsplit : ∑ j, ((eigvecOf discL discH i j)
          - (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)))
      = (∑ j, (eigvecOf discL discH i j))
        - ∑ j, ((1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k))) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  have hstep1 : ∑ j, (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k))
      = (1/2) * ∑ j, (∑ k, discAdj j k * (eigvecOf discL discH i k)) :=
    (Finset.mul_sum _ _ _).symm
  have hstep2 : ∑ j, (∑ k, discAdj j k * (eigvecOf discL discH i k))
      = ∑ k, (∑ j, discAdj j k) * (eigvecOf discL discH i k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (∑ j, discAdj j k) * (eigvecOf discL discH i k)
        = ∑ j, discAdj j k * (eigvecOf discL discH i k) :=
      Finset.sum_mul _ _ _
    rw [hk]
  have hstep3 : ∑ k, (∑ j, discAdj j k) * (eigvecOf discL discH i k)
      = ∑ k, 2 * (eigvecOf discL discH i k) :=
    Finset.sum_congr rfl fun k _ => by rw [disc_col_sum k]
  have hstep4 : (1/2) * ∑ k, 2 * (eigvecOf discL discH i k)
      = ∑ k, (eigvecOf discL discH i k) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hstep1, hstep2, hstep3, hstep4]
  ring

/-- The eigen equation at the loop vertex: `μ · v 3 = 0` (the third
`L_sym` row vanishes). -/
theorem disc_eigen_three (i : Fin 4) :
    eigvalOf discL discH i * (eigvecOf discL discH i 3) = 0 := by
  have h := disc_eigen_entry i 3
  rw [show (∑ k, discAdj 3 k * (eigvecOf discL discH i k))
      = 2 * (eigvecOf discL discH i 3) from by
        simp [discAdj, Fin.sum_univ_four]] at h
  linarith

/-- The quadratic form at the unit eigenvector. -/
theorem disc_eigvalOf_mul_unit (i : Fin 4) :
    eigvalOf discL discH i
        * (∑ k, (eigvecOf discL discH i k) * (eigvecOf discL discH i k))
      = (∑ k, (eigvecOf discL discH i k) * (eigvecOf discL discH i k))
        - (1/2) * (∑ j, ∑ k, discAdj j k * (eigvecOf discL discH i j)
            * (eigvecOf discL discH i k)) := by
  have hL : ∑ j, (eigvalOf discL discH i * (eigvecOf discL discH i j))
        * (eigvecOf discL discH i j)
      = ∑ j, ((eigvecOf discL discH i j)
          - (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)))
          * (eigvecOf discL discH i j) :=
    Finset.sum_congr rfl fun j _ => by rw [disc_eigen_entry i j]
  have hLsum : ∑ j, (eigvalOf discL discH i * (eigvecOf discL discH i j))
        * (eigvecOf discL discH i j)
      = eigvalOf discL discH i
          * (∑ k, (eigvecOf discL discH i k) * (eigvecOf discL discH i k)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hsplit : ∑ j, ((eigvecOf discL discH i j)
          - (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)))
          * (eigvecOf discL discH i j)
      = (∑ j, (eigvecOf discL discH i j) * (eigvecOf discL discH i j))
        - ∑ j, ((1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)))
            * (eigvecOf discL discH i j) := by
    have hper : ∀ j : Fin 4,
        ((eigvecOf discL discH i j)
            - (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)))
            * (eigvecOf discL discH i j)
        = (eigvecOf discL discH i j) * (eigvecOf discL discH i j)
          - ((1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)))
              * (eigvecOf discL discH i j) := fun j => by ring
    rw [Finset.sum_congr rfl fun j _ => hper j, Finset.sum_sub_distrib]
  have hterm : ∀ j : Fin 4,
      ((1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)))
          * (eigvecOf discL discH i j)
      = (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)
            * (eigvecOf discL discH i j)) := by
    intro j
    have hq := Finset.sum_mul (Finset.univ : Finset (Fin 4))
      (fun k => discAdj j k * (eigvecOf discL discH i k))
      (eigvecOf discL discH i j)
    calc ((1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)))
          * (eigvecOf discL discH i j)
        = (1/2) * ((∑ k, discAdj j k * (eigvecOf discL discH i k))
            * (eigvecOf discL discH i j)) := by ring
      _ = (1/2) * (∑ k, discAdj j k * (eigvecOf discL discH i k)
            * (eigvecOf discL discH i j)) := by rw [hq]
  have hpull2 := Finset.mul_sum (Finset.univ : Finset (Fin 4))
    (fun j => ∑ k, discAdj j k * (eigvecOf discL discH i k)
      * (eigvecOf discL discH i j)) (1/2)
  have hfin : (1/2) * (∑ j, ∑ k, discAdj j k * (eigvecOf discL discH i k)
          * (eigvecOf discL discH i j))
      = (1/2) * (∑ j, ∑ k, discAdj j k * (eigvecOf discL discH i j)
            * (eigvecOf discL discH i k)) :=
    congrArg ((1/2) * ·) (Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring)
  rw [← hLsum, hL, hsplit, Finset.sum_congr rfl fun j _ => hterm j,
    ← hpull2, hfin]

/-- **Every fixture eigenvalue is `0` or `3/2`** — derived with no
control over Mathlib's basis: `μ ≠ 0` forces `∑ v = 0` (row sums) and
`v 3 = 0` (the loop row), and then the unit-norm quadratic form reads
`μ = 1 − (1/2) · 2(v₀v₁ + v₀v₂ + v₁v₂) = 1 + 1/2 = 3/2` (the pair sum
collapses to `−1/2` on the zero-sum unit sphere). -/
theorem disc_eigvalOf_cases (i : Fin 4) :
    eigvalOf discL discH i = 0 ∨ eigvalOf discL discH i = 3/2 := by
  have hunit : ∑ k, (eigvecOf discL discH i k)
      * (eigvecOf discL discH i k) = 1 := by
    simpa using eigvecOf_inner discL discH i i
  have hzero := disc_eigen_summed i
  have h3 := disc_eigen_three i
  rcases mul_eq_zero.mp hzero with hμ0 | hsum
  · exact Or.inl hμ0
  · by_cases hμ : eigvalOf discL discH i = 0
    · exact Or.inl hμ
    · have hv3 : eigvecOf discL discH i 3 = 0 := by
        rcases mul_eq_zero.mp h3 with h | h
        · exact absurd h hμ
        · exact h
      have hqf := disc_eigvalOf_mul_unit i
      rw [hunit] at hqf
      have hsum4 : ∑ k, (eigvecOf discL discH i k) = 0 := hsum
      simp only [Fin.sum_univ_four] at hsum4
      rw [hv3] at hsum4
      simp only [add_zero] at hsum4
      have hunit4 := hunit
      simp only [Fin.sum_univ_four] at hunit4
      rw [hv3] at hunit4
      simp only [zero_mul, add_zero] at hunit4
      have hdbl : (∑ j, ∑ k, discAdj j k * (eigvecOf discL discH i j)
            * (eigvecOf discL discH i k))
          = 2 * ((eigvecOf discL discH i 0) * (eigvecOf discL discH i 1)
              + (eigvecOf discL discH i 0) * (eigvecOf discL discH i 2)
              + (eigvecOf discL discH i 1) * (eigvecOf discL discH i 2))
          + 2 * ((eigvecOf discL discH i 3) * (eigvecOf discL discH i 3)) := by
        simp [discAdj_apply, Fin.sum_univ_four]
        ring
      rw [hdbl, hv3] at hqf
      have hpair : 2 * ((eigvecOf discL discH i 0)
            * (eigvecOf discL discH i 1)
            + (eigvecOf discL discH i 0) * (eigvecOf discL discH i 2)
            + (eigvecOf discL discH i 1) * (eigvecOf discL discH i 2))
          = -1 := by
        have hexp : ((eigvecOf discL discH i 0)
              + (eigvecOf discL discH i 1)
              + (eigvecOf discL discH i 2))^2
            = ((eigvecOf discL discH i 0)
                * (eigvecOf discL discH i 0)
                + (eigvecOf discL discH i 1) * (eigvecOf discL discH i 1)
                + (eigvecOf discL discH i 2) * (eigvecOf discL discH i 2))
              + 2 * ((eigvecOf discL discH i 0)
                  * (eigvecOf discL discH i 1)
                  + (eigvecOf discL discH i 0) * (eigvecOf discL discH i 2)
                  + (eigvecOf discL discH i 1)
                      * (eigvecOf discL discH i 2)) := by ring
        have h0 : (eigvecOf discL discH i 0)
            + (eigvecOf discL discH i 1)
            + (eigvecOf discL discH i 2) = 0 := by linarith
        rw [h0] at hexp
        simp at hexp
        linarith
      rw [hpair] at hqf
      norm_num at hqf
      exact Or.inr (by linarith)

/-- **The rate hypothesis genuinely holds on the disconnected fixture**
at `r = 1/2`: the only nonzero eigenvalue is `3/2`, with walk factor
`|1 − 3/2| = 1/2`. The loop's `μ = 0` mode never enters the hypothesis —
it is excluded by design. -/
theorem disc_rate_QA (i : Fin 4) (h : eigvalOf discL discH i ≠ 0) :
    |1 - eigvalOf discL discH i| ≤ 1/2 := by
  rcases disc_eigvalOf_cases i with h0 | h32
  · exact absurd h0 h
  · rw [h32, show (1:ℝ) - 3/2 = -1/2 from by norm_num,
      abs_of_neg (by norm_num)]
    norm_num

/-- The three-step law from vertex 0: the walk mixes inside the triangle
and never leaves it — `(1/4, 3/8, 3/8, 0)`. -/
theorem disc_dist_three_QA :
    walkDistribution discAdj 3 0 = ![1/4, 3/8, 3/8, 0] := by
  have h1 : walkDistribution discAdj 1 0 = ![0, 1/2, 1/2, 0] := by
    rw [walkDistribution_succ, walkDistribution_zero]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix, deg, discAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_four, Pi.single_apply]
    all_goals norm_num
  have h2 : walkDistribution discAdj 2 0 = ![1/2, 1/4, 1/4, 0] := by
    rw [walkDistribution_succ, h1]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix, deg, discAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_four]
    all_goals norm_num
  rw [walkDistribution_succ, h2]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, discAdj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_four]
  all_goals norm_num

/-- `χ²(3, 0)` pinned raw: `4 · (2 · (1/8)² + (1/4)²) = 3/8` — the walk
has mixed to the *component* stationary `(1/3, 1/3, 1/3, 0)`-ish law
but not to the global `π`, and the χ² distance has stalled at `3/8`. -/
theorem disc_chi2_three_QA :
    chiSquareDistance discAdj 3 0 = 3/8 := by
  simp only [chiSquareDistance, disc_dist_three_QA, disc_pi_QA,
    Fin.sum_univ_four]
  norm_num

/-- The would-be bound's right side, pinned: `(1/2)^6 · 3 = 3/64`. -/
theorem disc_bound_raw_QA :
    (1/2)^(2 * 3) * ((stationaryVec discAdj 0)⁻¹ - 1) = 3/64 := by
  rw [disc_pi_QA 0]
  norm_num

/-- **The connectivity hypothesis is load-bearing**: with every other
hypothesis of `chiSquareDistance_le_of_connected` satisfied — symmetric,
nonnegative, positive degrees, and the rate hypothesis *provably holding
at `r = 1/2`* — the conclusion is refuted on this disconnected fixture:
`χ²(3) = 3/8 > 3/64`. No mixing to global stationarity is possible
without connectivity; the value-based rate exclusion cannot detect the
second `μ = 0` mode. -/
theorem disc_connected_guard_QA :
    ¬ (chiSquareDistance discAdj 3 0
        ≤ (1/2)^(2 * 3) * ((stationaryVec discAdj 0)⁻¹ - 1)) := by
  rw [disc_chi2_three_QA, disc_bound_raw_QA]
  norm_num

/-!
### The oversmoothing ceiling (`Oversmoothing.lean`)

The depth-form consumers of this module's closing bound, instantiated
on the triangle at two different rate certificates — the QA program of
`proposals/message-passing-depth-mixing-bound.md`. The same graph
(`π = (1/3, 1/3, 1/3)`, so the entrywise constant is
`√(2/3)` at every start/target pair) is certified at the honest rate
`r = 1/2` (the exact spectrum `{0, 3/2, 3/2}`) and at the
deliberately loose rate `r = 4/5` (a valid but weaker certificate the
triangle also satisfies): at `ε = 1/8` the honest certificate
provably reaches depth `3` (and not `2` — the threshold mechanism is
load-bearing), while the loose one provably needs `9` (and does not
reach `8`). The ceiling tracks the *certified* spectral gap, exactly
the monotonicity the shelf's `oversmoothing_log_threshold_mono`
states in general and `tri_threshold_mono_QA` pins at the fixture.
Every conclusion is checked against the walk law computed by raw
literal arithmetic (`tri_ceiling_*_value_QA`), independent of the
theorem under test.
-/

/-- The entrywise constant at the triangle: `π ≡ 1/3` makes
`√(π y · ((π x)⁻¹ − 1)) = √(2/3)` at every start/target pair. -/
theorem tri_oversmoothingConstant_eq_QA (x y : Fin 3) :
    Real.sqrt (stationaryVec triAdj y * ((stationaryVec triAdj x)⁻¹ - 1))
      = Real.sqrt (2/3) := by
  rw [tri_pi_QA y, tri_pi_QA x]
  congr 1
  norm_num

/-- The square-root bound used by every threshold pin below. -/
theorem tri_sqrt_le_one_QA : Real.sqrt (2/3) ≤ 1 :=
  (Real.sqrt_le_sqrt (by norm_num : (2/3 : ℝ) ≤ 1)).trans_eq Real.sqrt_one

/-- **The honest certificate's threshold at `ε = 1/2` is at most
depth `1`** — one layer already certifies halved deviation on the
triangle. -/
theorem tri_ceiling_threshold_one_QA :
    Real.log (Real.sqrt (2/3) / (1/2)) / Real.log 2 ≤ (1 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCpos : 0 < Real.sqrt (2/3) / (1/2) := by positivity
  have hle : Real.sqrt (2/3) / (1/2) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (1/2)),
      show (2:ℝ) * (1/2) = 1 from by norm_num]
    exact tri_sqrt_le_one_QA
  have hlog := (Real.log_le_log_iff hCpos (by norm_num : (0:ℝ) < 2)).mpr hle
  rw [div_le_iff₀ hlog2, one_mul]
  exact hlog

/-- **The honest certificate's threshold at `ε = 1/8` is at most
depth `3`** (`8·√(2/3) ≤ 8` since `√(2/3) ≤ 1`); paired with
`tri_ceiling_threshold_three_sharp_QA` below, `3` is exactly the
minimal certified depth — the threshold inequality is load-bearing,
not vacuous. -/
theorem tri_ceiling_threshold_three_QA :
    Real.log (Real.sqrt (2/3) / (1/8)) / Real.log 2 ≤ (3 : ℝ) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h8 : (2:ℝ) ^ (3 : ℕ) = 8 := by norm_num
  have hCpos : 0 < Real.sqrt (2/3) / (1/8) := by positivity
  have hle : Real.sqrt (2/3) / (1/8) ≤ (2 : ℝ) ^ (3 : ℕ) := by
    rw [h8, div_le_iff₀ (by norm_num : (0:ℝ) < (1/8)),
      show (8:ℝ) * (1/8) = 1 from by norm_num]
    exact tri_sqrt_le_one_QA
  have hlog := (Real.log_le_log_iff hCpos
    (by rw [h8]; norm_num)).mpr hle
  rw [Real.log_pow] at hlog
  rw [div_le_iff₀ hlog2]
  push_cast at hlog ⊢
  exact hlog

/-- **The honest certificate's threshold at `ε = 1/8` is NOT at most
depth `2`**: `2² = 4 < 8·√(2/3)`, so the depth-3 certificate of
`tri_ceiling_threshold_three_QA` is the sharp one — the theorem's
hypothesis genuinely does the work. -/
theorem tri_ceiling_threshold_three_sharp_QA :
    ¬ (Real.log (Real.sqrt (2/3) / (1/8)) / Real.log 2 ≤ (2 : ℝ)) := by
  intro h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : Real.log (Real.sqrt (2/3) / (1/8)) ≤ (2 : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp h
  have h4 : (2:ℝ) ^ (2 : ℕ) < Real.sqrt (2/3) / (1/8) := by
    rw [show (2:ℝ) ^ (2 : ℕ) = 4 from by norm_num,
      lt_div_iff₀ (by norm_num : (0:ℝ) < (1/8)),
      show (4:ℝ) * (1/8) = 1/2 from by norm_num]
    have hsqrt : (1/2 : ℝ) < Real.sqrt (2/3) := by
      have h := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ (1/2)^2)
        (by norm_num : ((1/2 : ℝ)^2) < 2/3)
      rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/2)] at h
    exact hsqrt
  have hlt : Real.log ((2:ℝ) ^ (2 : ℕ))
      < Real.log (Real.sqrt (2/3) / (1/8)) :=
    Real.log_lt_log (by norm_num) h4
  rw [Real.log_pow] at hlt
  push_cast at hlt h2
  linarith

/-- **The ceiling at depth `1`, `ε = 1/2`**, from the honest
certificate — the first layer already certifies the deviation bound. -/
theorem tri_ceiling_one_QA :
    |walkDistribution triAdj 1 0 1 - stationaryVec triAdj 1| ≤ 1/2 := by
  refine walkDistribution_sub_stationaryVec_le_of_depth triAdj
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (1/2)
    (by norm_num) (by norm_num) (by norm_num) tri_rate_QA 1 0 1 ?_
  rw [tri_oversmoothingConstant_eq_QA 0 1,
    show (1:ℝ) / (1/2) = 2 from by norm_num]
  simpa using tri_ceiling_threshold_one_QA

/-- The true value at the depth-1 instance: deviation exactly `1/6`,
well inside the certified `1/2` — the bound's slack is honest. -/
theorem tri_ceiling_one_value_QA :
    |walkDistribution triAdj 1 0 1 - stationaryVec triAdj 1| = 1/6 := by
  simp only [tri_dist_one_QA, tri_pi_QA]
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]

/-- The three-step law from vertex `0`, by raw iteration of the
evolution equation: `(1/4, 3/8, 3/8)`. -/
theorem tri_dist_three_zero_QA :
    walkDistribution triAdj 3 0 = ![1/4, 3/8, 3/8] := by
  rw [walkDistribution_succ, tri_dist_two_QA]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- The three-step law from vertex `1`: `(3/8, 1/4, 3/8)`. -/
theorem tri_dist_three_one_QA :
    walkDistribution triAdj 3 1 = ![3/8, 1/4, 3/8] := by
  have h1 : walkDistribution triAdj 1 1 = ![1/2, 0, 1/2] := by
    rw [walkDistribution_succ, walkDistribution_zero]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, Pi.single_apply]
  have h2 : walkDistribution triAdj 2 1 = ![1/4, 1/2, 1/4] := by
    rw [walkDistribution_succ, h1]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  rw [walkDistribution_succ, h2]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- **The ceiling at depth `3`, `ε = 1/8`**, from the honest
certificate — the depth the sharpness pin above identifies as the
minimal certified one. -/
theorem tri_ceiling_three_QA :
    |walkDistribution triAdj 3 0 0 - stationaryVec triAdj 0| ≤ 1/8 := by
  refine walkDistribution_sub_stationaryVec_le_of_depth triAdj
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (1/8)
    (by norm_num) (by norm_num) (by norm_num) tri_rate_QA 3 0 0 ?_
  rw [tri_oversmoothingConstant_eq_QA 0 0,
    show (1:ℝ) / (1/2) = 2 from by norm_num]
  simpa using tri_ceiling_threshold_three_QA

/-- The true value at the depth-3 instance: deviation exactly
`1/12 ≤ 1/8` — the certified bound holds with genuine margin. -/
theorem tri_ceiling_three_value_QA :
    |walkDistribution triAdj 3 0 0 - stationaryVec triAdj 0| = 1/12 := by
  simp only [tri_dist_three_zero_QA, tri_pi_QA]
  norm_num [Matrix.cons_val_zero, Matrix.head_cons]

/-- **The two-start indistinguishability corollary at depth `3`**:
the `3`-step views from vertices `0` and `1` are within `2ε = 1/4` at
every target — the starting-position information is provably gone
past this depth. -/
theorem tri_ceiling_two_start_QA :
    |walkDistribution triAdj 3 0 0 - walkDistribution triAdj 3 1 0|
      ≤ 2 * (1/8) := by
  refine walkDistribution_sub_walkDistribution_le_of_depth triAdj
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (1/8)
    (by norm_num) (by norm_num) (by norm_num) tri_rate_QA 3 0 1 0 ?_ ?_
  · rw [tri_oversmoothingConstant_eq_QA 0 0,
      show (1:ℝ) / (1/2) = 2 from by norm_num]
    simpa using tri_ceiling_threshold_three_QA
  · rw [tri_oversmoothingConstant_eq_QA 1 0,
      show (1:ℝ) / (1/2) = 2 from by norm_num]
    simpa using tri_ceiling_threshold_three_QA

/-- The true value at the two-start instance: exactly `1/8`, half the
corollary's `2ε = 1/4` — both single-start bounds are attained with
room, and the triangle-inequality assembly is honest. -/
theorem tri_ceiling_two_start_value_QA :
    |walkDistribution triAdj 3 0 0 - walkDistribution triAdj 3 1 0|
      = 1/8 := by
  simp only [tri_dist_three_zero_QA, tri_dist_three_one_QA]
  norm_num [Matrix.cons_val_zero, Matrix.head_cons]

/-- **The deliberately loose rate certificate**: the triangle's rate
hypothesis also holds at `4/5` — a valid but weaker statement of the
same spectral fact (`1/2 ≤ 4/5`). -/
theorem tri_rate_four_fifths_QA (i : Fin 3)
    (h : eigvalOf triL triH i ≠ 0) :
    |1 - eigvalOf triL triH i| ≤ 4/5 :=
  le_trans (tri_rate_QA i h) (by norm_num)

/-- **The loose certificate's threshold at `ε = 1/8` is at most depth
`9`**: `8·√(2/3) ≤ 8·(41/50) = 164/25 ≤ (5/4)⁹`. Same graph, same
tolerance — three times the depth of the honest certificate. -/
theorem tri_ceiling_loose_threshold_QA :
    Real.log (Real.sqrt (2/3) / (1/8)) / Real.log (5/4) ≤ (9 : ℝ) := by
  have hlogpos : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  have h54 : (5/4 : ℝ) ^ (9 : ℕ) = 1953125 / 262144 := by norm_num
  have hCpos : 0 < Real.sqrt (2/3) / (1/8) := by positivity
  have hsqrt : Real.sqrt (2/3) ≤ 41/50 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (2/3 : ℝ) ≤ (41/50)^2)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 41/50)] at h
  have hnum : (41/50 : ℝ) ≤ 1953125/2097152 := by norm_num
  have hle : Real.sqrt (2/3) / (1/8) ≤ (5/4 : ℝ) ^ (9 : ℕ) := by
    rw [h54, div_le_iff₀ (by norm_num : (0:ℝ) < (1/8)),
      show (1953125/262144 : ℝ) * (1/8) = 1953125/2097152 from by norm_num]
    linarith
  have hlog := (Real.log_le_log_iff hCpos
    (by rw [h54]; norm_num)).mpr hle
  rw [Real.log_pow] at hlog
  rw [div_le_iff₀ hlogpos]
  push_cast at hlog ⊢
  exact hlog

/-- **The loose certificate does NOT reach depth `8`**:
`(5/4)⁸ ≤ 390625/65536 < 32/5 ≤ 8·√(2/3)`. The `3 → 9` jump is
entirely the certificate's, not slack in the threshold mechanism. -/
theorem tri_ceiling_loose_sharp_QA :
    ¬ (Real.log (Real.sqrt (2/3) / (1/8)) / Real.log (5/4) ≤ (8 : ℝ)) := by
  intro h
  have hlogpos : 0 < Real.log (5/4) := Real.log_pos (by norm_num)
  have h58 : (5/4 : ℝ) ^ (8 : ℕ) = 390625 / 65536 := by norm_num
  have h8 : Real.log (Real.sqrt (2/3) / (1/8)) ≤ (8 : ℝ) * Real.log (5/4) :=
    (div_le_iff₀ hlogpos).mp h
  have hsqrt : (4/5 : ℝ) ≤ Real.sqrt (2/3) := by
    have h := Real.sqrt_le_sqrt (by norm_num : ((4/5 : ℝ)^2) ≤ 2/3)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4/5)] at h
  have hnum2 : (390625/65536 : ℝ) * (1/8) = 390625/524288 := by norm_num
  have hnum3 : (390625/524288 : ℝ) < (4/5) := by norm_num
  have hpowl : (5/4 : ℝ) ^ (8 : ℕ) < Real.sqrt (2/3) / (1/8) := by
    rw [h58, lt_div_iff₀ (by norm_num : (0:ℝ) < (1/8)), hnum2]
    linarith
  have hlt : Real.log ((5/4 : ℝ) ^ (8 : ℕ))
      < Real.log (Real.sqrt (2/3) / (1/8)) :=
    Real.log_lt_log (by rw [h58]; norm_num) hpowl
  rw [Real.log_pow] at hlt
  linarith

/-- **The ceiling at depth `9` from the loose certificate alone**:
`r = 4/5` certifies `ε = 1/8` at depth `9` — the depth the honest
certificate reached at `3`. -/
theorem tri_ceiling_loose_QA :
    |walkDistribution triAdj 9 0 0 - stationaryVec triAdj 0| ≤ 1/8 := by
  refine walkDistribution_sub_stationaryVec_le_of_depth triAdj
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected (4/5) (1/8)
    (by norm_num) (by norm_num) (by norm_num) tri_rate_four_fifths_QA 9 0 0
    ?_
  rw [tri_oversmoothingConstant_eq_QA 0 0,
    show (1:ℝ) / (4/5) = 5/4 from by norm_num]
  simpa using tri_ceiling_loose_threshold_QA

/-- The nine-step law from vertex `0`, by raw iteration:
`(85/256, 171/512, 171/512)` — the alternating contraction around
`1/3` visible in the numerators. -/
theorem tri_dist_nine_zero_QA :
    walkDistribution triAdj 9 0 = ![85/256, 171/512, 171/512] := by
  have h4 : walkDistribution triAdj 4 0 = ![3/8, 5/16, 5/16] := by
    rw [walkDistribution_succ, tri_dist_three_zero_QA]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  have h5 : walkDistribution triAdj 5 0 = ![5/16, 11/32, 11/32] := by
    rw [walkDistribution_succ, h4]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  have h6 : walkDistribution triAdj 6 0 = ![11/32, 21/64, 21/64] := by
    rw [walkDistribution_succ, h5]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  have h7 : walkDistribution triAdj 7 0 = ![21/64, 43/128, 43/128] := by
    rw [walkDistribution_succ, h6]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  have h8 : walkDistribution triAdj 8 0 = ![43/128, 85/256, 85/256] := by
    rw [walkDistribution_succ, h7]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
    all_goals norm_num
  rw [walkDistribution_succ, h8]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- The true value at the depth-9 instance: deviation exactly
`1/768` — deep inside the certified `1/8`, the loose certificate's
price being depth, not correctness. -/
theorem tri_ceiling_loose_value_QA :
    |walkDistribution triAdj 9 0 0 - stationaryVec triAdj 0| = 1/768 := by
  simp only [tri_dist_nine_zero_QA, tri_pi_QA]
  norm_num [Matrix.cons_val_zero, Matrix.head_cons]

/-- **The `t = 0` corner is sound**: with `ε` exactly the entrywise
constant, the threshold is `log 1 / log (1/r) = 0 ≤ 0`, and the
conclusion at depth zero — `|δ_x y − π y| ≤ √(π y · ((π x)⁻¹ − 1))` —
is the entrywise extraction's own `t = 0` instance, true by the χ²
normalization (`1/3 ≤ √(2/3)` at the fixture). -/
theorem tri_ceiling_zero_QA :
    |walkDistribution triAdj 0 0 1 - stationaryVec triAdj 1|
      ≤ Real.sqrt (2/3) := by
  refine walkDistribution_sub_stationaryVec_le_of_depth triAdj
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected (1/2)
    (Real.sqrt (2/3)) (by norm_num) (by norm_num)
    (by positivity) tri_rate_QA 0 0 1 ?_
  rw [tri_oversmoothingConstant_eq_QA 0 1,
    show (1:ℝ) / (1/2) = 2 from by norm_num,
    div_self (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))),
    Real.log_one, zero_div]
  simp

/-- **The sanity contrast's engine, pinned at the fixture**: the
general monotonicity `oversmoothing_log_threshold_mono` at
`r₁ = 1/2 ≤ r₂ = 4/5`, `C = √(2/3)`, `ε = 1/8` — the honest
certificate's threshold is provably below the loose one's, as the
numeric pins above witness concretely. -/
theorem tri_threshold_mono_QA :
    Real.log (Real.sqrt (2/3) / (1/8)) / Real.log (1 / (1/2))
      ≤ Real.log (Real.sqrt (2/3) / (1/8)) / Real.log (1 / (4/5)) := by
  refine oversmoothing_log_threshold_mono (r₁ := 1/2) (r₂ := 4/5)
    (C := Real.sqrt (2/3)) (ε := 1/8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_
  have h := Real.sqrt_le_sqrt (by norm_num : (1/8 : ℝ)^2 ≤ 2/3)
  rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/8)] at h

end Triangle

/-!
## The per-pair resistance refinement of the oversmoothing ceiling

`Oversmoothing.lean`'s per-pair follow-on (delivered 2026-08-31,
`proposals/message-passing-depth-mixing-bound.md` Deferred item 1),
exercised on the triangle and the 4-cycle:

- **Exact attainment on K₃** at `t = 1` and `t = 2`: the four-point
  contrast at the adjacent pair is exactly the theorem's bound
  (`1 = (3/2) · √(2/3) · √(2/3)`, `1/2 = (3/4) · √(2/3) · √(2/3)`) —
  the bound is tight on the fixture, the strongest QA shape a bound
  theorem can have.
- The packaged corollary's instance at the same fixture
  (`2 · 2 · (1/2)² · (2/3) = 2/3 ≥ 1/2`, non-vacuous slack against the
  tight bound), and the `λ ≤ 2d` engine pinned at `3 ≤ 4` both by the
  engine and independently by the spectrum cases.
- **The C₄ mode-coverage fence**: the contrast bound's rate hypothesis
  must quantify over *every* decaying mode — a certificate covering
  only the mid modes `λ = 2` (where it genuinely holds at `ρ = 0`)
  makes the dropped-hypothesis statement false (the contrast is `1`
  against the bound `0`).
-/


local notation "triLap" => laplacian triAdj
local notation "triLapH" => laplacian_symmetric triAdj triAdj_isSymm

/-- Sum-linearity helpers (elaboration-safe explicit forms of the
`Finset` rewrites, avoiding the instance-stuck metavars). -/
theorem sum_sub_help {ι : Type*} [Fintype ι] (X Y : ι → ℝ) :
    ∑ j, (X j - Y j) = ∑ j, X j - ∑ j, Y j := Finset.sum_sub_distrib

theorem mul_sum_help {ι : Type*} [Fintype ι] (a : ℝ) (f : ι → ℝ) :
    a * ∑ j, f j = ∑ j, a * f j := Finset.mul_sum Finset.univ f a

/-- Entry form of the triangle's combinatorian Laplacian action. -/
theorem tri_lap_mulVec_apply (w : Fin 3 → ℝ) (j : Fin 3) :
    (triLap *ᵥ w) j = 2 * w j - (∑ k, triAdj j k * w k) := by
  simp only [laplacian, Matrix.mulVec, Matrix.dotProduct,
    Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, degreeMatrix,
    dite_eq_ite, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, triAdj_deg_eq]

/-- **The triangle's combinatorial spectrum**: every Laplacian
eigenvalue is `0` or `3` (the QA file's normalized
`tri_eigvalOf_cases`, mirrored on the combinatorian operator). -/
theorem tri_lap_eigvalOf_cases (i : Fin 3) :
    eigvalOf triLap triLapH i = 0 ∨ eigvalOf triLap triLapH i = 3 := by
  have hquad := quadForm_eigvecOf_self triLapH i
  have hunit : ∑ k, eigvecOf triLap triLapH i k
        * eigvecOf triLap triLapH i k = 1 := by
    simpa using eigvecOf_inner triLap triLapH i i
  have hrow : ∀ k : Fin 3, ∑ j, triAdj j k = 2 := by
    intro k
    fin_cases k <;>
      simp [triAdj_apply, Fin.sum_univ_three] <;>
      norm_num
  have hsumrow : ∑ j, ∑ k, triAdj j k * eigvecOf triLap triLapH i k
      = 2 * ∑ j, eigvecOf triLap triLapH i j := by
    rw [Finset.sum_comm]
    have hstep : ∑ k, (∑ j, triAdj j k * eigvecOf triLap triLapH i k)
        = ∑ k, 2 * eigvecOf triLap triLapH i k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_congr rfl
          fun j _ => mul_comm (triAdj j k) (eigvecOf triLap triLapH i k),
        ← Finset.mul_sum, hrow k]
      ring
    rw [hstep, ← Finset.mul_sum]
  have hact : triLap *ᵥ (eigvecOf triLap triLapH i)
      = eigvalOf triLap triLapH i • (eigvecOf triLap triLapH i) :=
    (isHermitian_of_isSymm triLapH).mulVec_eigenvectorBasis i
  have hzero : eigvalOf triLap triLapH i
      * (∑ j, eigvecOf triLap triLapH i j) = 0 := by
    have hsumact : ∑ j, (triLap *ᵥ eigvecOf triLap triLapH i) j
        = ∑ j, eigvalOf triLap triLapH i * eigvecOf triLap triLapH i j :=
      Finset.sum_congr rfl fun j _ => by rw [hact]; simp
    rw [← mul_sum_help (eigvalOf triLap triLapH i)
        (fun j => eigvecOf triLap triLapH i j)] at hsumact
    have hLsum : ∑ j, (triLap *ᵥ eigvecOf triLap triLapH i) j = 0 := by
      rw [Finset.sum_congr rfl
          fun j _ => tri_lap_mulVec_apply (eigvecOf triLap triLapH i) j,
        sum_sub_help (fun j => 2 * eigvecOf triLap triLapH i j)
          (fun j => ∑ k, triAdj j k * eigvecOf triLap triLapH i k),
        ← mul_sum_help 2 (fun j => eigvecOf triLap triLapH i j), hsumrow]
      ring
    rw [hLsum] at hsumact
    linarith
  have hvAv : ∑ j, eigvecOf triLap triLapH i j
        * (∑ k, triAdj j k * eigvecOf triLap triLapH i k)
      = (∑ j, eigvecOf triLap triLapH i j) ^ 2 - 1 := by
    simp only [Fin.sum_univ_three] at hunit
    have hrow0 : (∑ k, triAdj 0 k * eigvecOf triLap triLapH i k)
        = eigvecOf triLap triLapH i 1 + eigvecOf triLap triLapH i 2 := by
      simp [triAdj_apply, Fin.sum_univ_three]
    have hrow1 : (∑ k, triAdj 1 k * eigvecOf triLap triLapH i k)
        = eigvecOf triLap triLapH i 0 + eigvecOf triLap triLapH i 2 := by
      simp [triAdj_apply, Fin.sum_univ_three]
    have hrow2 : (∑ k, triAdj 2 k * eigvecOf triLap triLapH i k)
        = eigvecOf triLap triLapH i 0 + eigvecOf triLap triLapH i 1 := by
      simp [triAdj_apply, Fin.sum_univ_three]
    rw [show (∑ j, eigvecOf triLap triLapH i j
            * (∑ k, triAdj j k * eigvecOf triLap triLapH i k))
          = eigvecOf triLap triLapH i 0 * (∑ k, triAdj 0 k * eigvecOf triLap triLapH i k)
            + eigvecOf triLap triLapH i 1 * (∑ k, triAdj 1 k * eigvecOf triLap triLapH i k)
            + eigvecOf triLap triLapH i 2 * (∑ k, triAdj 2 k * eigvecOf triLap triLapH i k)
          from Fin.sum_univ_three _,
      hrow0, hrow1, hrow2,
      show (∑ j, eigvecOf triLap triLapH i j)
          = eigvecOf triLap triLapH i 0 + eigvecOf triLap triLapH i 1
            + eigvecOf triLap triLapH i 2 from Fin.sum_univ_three _]
    linear_combination (-1) * hunit
  have hqf : eigvalOf triLap triLapH i
      = 3 - (∑ j, eigvecOf triLap triLapH i j) ^ 2 := by
    have hexp : quadForm triLap (eigvecOf triLap triLapH i)
        = 2 * 1 - ((∑ j, eigvecOf triLap triLapH i j) ^ 2 - 1) := by
      have hsplit : quadForm triLap (eigvecOf triLap triLapH i)
          = ∑ j, (eigvecOf triLap triLapH i j * (2 * eigvecOf triLap triLapH i j)
              - eigvecOf triLap triLapH i j
                * (∑ k, triAdj j k * eigvecOf triLap triLapH i k)) := by
        simp only [quadForm, Matrix.dotProduct, tri_lap_mulVec_apply,
          sub_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit, sum_sub_help _ _,
        Finset.sum_congr rfl fun j _ => show eigvecOf triLap triLapH i j
          * (2 * eigvecOf triLap triLapH i j)
          = 2 * (eigvecOf triLap triLapH i j * eigvecOf triLap triLapH i j)
          from by ring,
        ← mul_sum_help 2 (fun j => eigvecOf triLap triLapH i j
          * eigvecOf triLap triLapH i j),
        hunit, hvAv]
    rw [← hquad, hexp]
    ring
  rcases mul_eq_zero.mp hzero with h0 | hs0
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [hqf, hs0]
    ring

/-- The triangle's mode-rate certificate, at equality: every decaying
mode is the top mode `λ = 3` with walk factor `1 − 3/2 = −1/2`. -/
theorem tri_lap_hrate (t : ℕ) (k : Fin 3)
    (hk : eigvalOf triLap triLapH k ≠ 0) :
    eigvalOf triLap triLapH k * |1 - eigvalOf triLap triLapH k / 2| ^ t
      = 3 * (1 / 2) ^ t := by
  rcases tri_lap_eigvalOf_cases k with h | h
  · exact absurd h hk
  · rw [h]
    have habs : |(1 : ℝ) - 3 / 2| = 1 / 2 := by norm_num
    rw [habs]

/-- `f = ![1, 1/3, 2/3]` solves the `e 0 − e 1` unit demand on the
triangle. -/
theorem tri_pot01 :
    triLap *ᵥ ![1, 1/3, 2/3]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, triAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three] <;>
    try norm_num

/-- **Triangle resistance:** `R 0 1 = 2/3` (the direct edge in parallel
with the two-edge path of resistance `2`). -/
theorem tri_R01 : effectiveResistance triAdj 0 1 = 2 / 3 :=
  effectiveResistance_eq triAdj triAdj_isSymm triAdj_nonneg tri_connected
    ⟨![1, 1/3, 2/3], tri_pot01, by norm_num [Matrix.cons_val']⟩

/-- The one-step law from vertex 1 on the triangle: `(1/2, 0, 1/2)`. -/
theorem tri_dist_one_one : walkDistribution triAdj 1 1 = ![1/2, 0, 1/2] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, triAdj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_three, Pi.single_apply]
  all_goals norm_num

/-- The two-step law from vertex 1: `(1/4, 1/2, 1/4)`. -/
theorem tri_dist_two_one : walkDistribution triAdj 2 1 = ![1/4, 1/2, 1/4] := by
  have h2 : walkDistribution triAdj 2 1
      = (walkTransitionMatrix triAdj)ᵀ *ᵥ walkDistribution triAdj 1 1 :=
    walkDistribution_succ triAdj 1 1
  rw [h2, tri_dist_one_one]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  all_goals norm_num

/-- **Exact attainment at `t = 1`**: the four-point contrast at the
pair `((0,1), (0,1))` is exactly `1`, and so is the theorem's bound
`(3/2) · √(2/3) · √(2/3)` — the resistance-contrast bound is tight on
the triangle at the first step. -/
theorem tri_contrast_one_val_QA :
    |(walkDistribution triAdj 1 0 0 - walkDistribution triAdj 1 1 0)
      - (walkDistribution triAdj 1 0 1 - walkDistribution triAdj 1 1 1)|
      = 1 := by
  rw [tri_dist_one_QA, tri_dist_one_one]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem tri_contrast_one_bound_eq_QA :
    3 * (1 / 2 : ℝ) ^ 1 * Real.sqrt (effectiveResistance triAdj 0 1)
        * Real.sqrt (effectiveResistance triAdj 0 1) = 1 := by
  rw [tri_R01]
  have h2 : Real.sqrt (2 / 3) * Real.sqrt (2 / 3) = 2 / 3 :=
    Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2 / 3)
  linear_combination (3 / 2) * h2

theorem tri_contrast_one_le_QA :
    |(walkDistribution triAdj 1 0 0 - walkDistribution triAdj 1 1 0)
      - (walkDistribution triAdj 1 0 1 - walkDistribution triAdj 1 1 1)|
      ≤ 3 * (1 / 2 : ℝ) ^ 1 * Real.sqrt (effectiveResistance triAdj 0 1)
          * Real.sqrt (effectiveResistance triAdj 0 1) :=
  walkDistribution_pair_contrast_abs_le triAdj_isSymm triAdj_nonneg
    triAdj_deg_eq (by norm_num) tri_connected _ (by norm_num) 1 0 1 0 1
    (fun k hk => le_of_eq (tri_lap_hrate 1 k hk))

/-- **Exact attainment at `t = 2`**: the contrast is `1/2` and so is
the bound `(3/4) · √(2/3) · √(2/3)` — attained again. -/
theorem tri_contrast_two_val_QA :
    |(walkDistribution triAdj 2 0 0 - walkDistribution triAdj 2 1 0)
      - (walkDistribution triAdj 2 0 1 - walkDistribution triAdj 2 1 1)|
      = 1/2 := by
  rw [tri_dist_two_QA, tri_dist_two_one]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem tri_contrast_two_le_QA :
    |(walkDistribution triAdj 2 0 0 - walkDistribution triAdj 2 1 0)
      - (walkDistribution triAdj 2 0 1 - walkDistribution triAdj 2 1 1)|
      ≤ 3 * (1 / 2 : ℝ) ^ 2 * Real.sqrt (effectiveResistance triAdj 0 1)
          * Real.sqrt (effectiveResistance triAdj 0 1) :=
  walkDistribution_pair_contrast_abs_le triAdj_isSymm triAdj_nonneg
    triAdj_deg_eq (by norm_num) tri_connected _ (by norm_num) 2 0 1 0 1
    (fun k hk => le_of_eq (tri_lap_hrate 2 k hk))

/-- **The packaged corollary's instance at the same fixture**: with the
walk family's own certificate `r = 1/2`, the `2d r^t` bound at `t = 2`
is `2 · 2 · (1/2)² · (2/3) = 2/3 ≥ 1/2` — non-vacuous slack against the
exact tight bound `1/2`. -/
theorem tri_contrast_two_packaged_QA :
    |(walkDistribution triAdj 2 0 0 - walkDistribution triAdj 2 1 0)
      - (walkDistribution triAdj 2 0 1 - walkDistribution triAdj 2 1 1)|
      ≤ 2 * (2 : ℝ) * (1 / 2) ^ 2 * Real.sqrt (effectiveResistance triAdj 0 1)
          * Real.sqrt (effectiveResistance triAdj 0 1) :=
  walkDistribution_pair_contrast_abs_le' triAdj_isSymm triAdj_nonneg
    triAdj_deg_eq (by norm_num) tri_connected (1/2) (by norm_num) 2 0 1 0 1
    (fun k hk => by
      rcases tri_lap_eigvalOf_cases k with h | h
      · exact absurd h hk
      · rw [h, show (1 : ℝ) - 3 / 2 = -(1 / 2) from by norm_num, abs_neg,
          abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)])

/-- **The `λ ≤ 2d` engine pinned at the fixture**: the triangle's top
eigenvalue `3` is at most `2 · 2 = 4` — both by the engine and
independently by the spectrum cases. -/
theorem tri_lam_le_four_engine_QA (k : Fin 3) :
    eigvalOf triLap triLapH k ≤ 2 * (2 : ℝ) :=
  eigvalOf_laplacian_le_two_mul triAdj_isSymm triAdj_nonneg triAdj_deg_eq k

theorem tri_lam_le_four_cases_QA (k : Fin 3) :
    eigvalOf triLap triLapH k ≤ 4 := by
  rcases tri_lap_eigvalOf_cases k with h | h <;> rw [h] <;> norm_num

/-!
## The C₄ mode-coverage fence

The contrast bound's rate hypothesis must cover **every** decaying
mode. On the 4-cycle the decaying modes split into the mid modes
`λ = 2` (walk factor `0`) and the top mode `λ = 4` (walk factor `−1`,
`λ · |1 − λ/2| = 4`); the whole `t = 1` contrast at the adjacent pair
is carried by the top mode. A certificate that covers only the mid
modes (`ρ = 0` genuinely certifies `λ · |1 − λ/2| ≤ 0` at every
`λ = 2` mode) makes the dropped-hypothesis statement false: the
contrast is `1` against the bound `0`. The mode quantifier is
load-bearing.
-/

section C4Fence

/-- Adjacency of the 4-cycle `0 — 1 — 2 — 3 — 0`. -/
def c4Adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

theorem c4Adj_isSymm : c4Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [c4Adj]

theorem c4Adj_nonneg : ∀ i j, 0 ≤ c4Adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [c4Adj]

theorem c4Adj_deg_eq (i : Fin 4) : deg c4Adj i = 2 := by
  fin_cases i <;> simp [deg, c4Adj, Fin.sum_univ_four] <;> norm_num

theorem c4_adj01 : (supportGraph c4Adj c4Adj_isSymm).Adj (0 : Fin 4) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [c4Adj]⟩

theorem c4_adj12 : (supportGraph c4Adj c4Adj_isSymm).Adj (1 : Fin 4) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [c4Adj]⟩

theorem c4_adj23 : (supportGraph c4Adj c4Adj_isSymm).Adj (2 : Fin 4) 3 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [c4Adj]⟩

theorem c4Adj_connected : (supportGraph c4Adj c4Adj_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons c4_adj01 SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons c4_adj01
      (SimpleGraph.Walk.cons c4_adj12 SimpleGraph.Walk.nil)⟩
  · exact ⟨SimpleGraph.Walk.cons c4_adj01
      (SimpleGraph.Walk.cons c4_adj12
        (SimpleGraph.Walk.cons c4_adj23 SimpleGraph.Walk.nil))⟩

/-- The minimal polynomial fact behind the cycle's spectrum:
`A³ = 4A` (each vertex's two-step and three-step neighborhoods on the
4-cycle collapse: `A e₀ = e₁ + e₃`, `A² e₀ = 2e₀ + 2e₂`,
`A³ e₀ = 4 (e₁ + e₃)`). -/
theorem c4Adj_cube : c4Adj * c4Adj * c4Adj = (4 : ℝ) • c4Adj := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, c4Adj] <;>
    norm_num

local notation "c4Lap" => laplacian c4Adj
local notation "c4LapH" => laplacian_symmetric c4Adj c4Adj_isSymm

/-- **The cycle's combinatorial spectrum**: every Laplacian eigenvalue
is `0`, `2`, or `4` — from `A³ = 4A` applied at the eigenvector (the
walk factor `2 − λ` satisfies `(2 − λ)³ = 4 (2 − λ)`). -/
theorem c4_lap_eigvalOf_cases (k : Fin 4) :
    eigvalOf c4Lap c4LapH k = 0 ∨ eigvalOf c4Lap c4LapH k = 2
      ∨ eigvalOf c4Lap c4LapH k = 4 := by
  have hactA : c4Adj *ᵥ (eigvecOf c4Lap c4LapH k)
      = (2 - eigvalOf c4Lap c4LapH k) • (eigvecOf c4Lap c4LapH k) :=
    adjacency_mulVec_eigvecOf_laplacian c4Adj_isSymm c4Adj_deg_eq k
  have hun : Matrix.dotProduct (eigvecOf c4Lap c4LapH k)
      (eigvecOf c4Lap c4LapH k) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner c4Lap c4LapH k k
  have hvne : eigvecOf c4Lap c4LapH k ≠ 0 := by
    intro h0
    rw [h0] at hun
    norm_num at hun
  have hcube : (c4Adj * c4Adj * c4Adj) *ᵥ (eigvecOf c4Lap c4LapH k)
      = (4 : ℝ) • (c4Adj *ᵥ eigvecOf c4Lap c4LapH k) := by
    rw [c4Adj_cube]
    exact Matrix.smul_mulVec_assoc (4 : ℝ) c4Adj _
  have hexp : (c4Adj * c4Adj * c4Adj) *ᵥ (eigvecOf c4Lap c4LapH k)
      = (((2 - eigvalOf c4Lap c4LapH k) * (2 - eigvalOf c4Lap c4LapH k))
          * (2 - eigvalOf c4Lap c4LapH k)) • (eigvecOf c4Lap c4LapH k) := by
    rw [show (c4Adj * c4Adj * c4Adj) *ᵥ (eigvecOf c4Lap c4LapH k)
          = c4Adj *ᵥ (c4Adj *ᵥ (c4Adj *ᵥ eigvecOf c4Lap c4LapH k)) from by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]]
    rw [hactA, Matrix.mulVec_smul, hactA, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hactA, smul_smul, smul_smul]
  have hkey : ((2 - eigvalOf c4Lap c4LapH k) * (2 - eigvalOf c4Lap c4LapH k))
        * (2 - eigvalOf c4Lap c4LapH k)
      = 4 * (2 - eigvalOf c4Lap c4LapH k) := by
    have h1 : (((2 - eigvalOf c4Lap c4LapH k)
            * (2 - eigvalOf c4Lap c4LapH k))
            * (2 - eigvalOf c4Lap c4LapH k)
          - 4 * (2 - eigvalOf c4Lap c4LapH k)) •
        (eigvecOf c4Lap c4LapH k) = 0 := by
      have hA3 : (((2 - eigvalOf c4Lap c4LapH k)
              * (2 - eigvalOf c4Lap c4LapH k))
            * (2 - eigvalOf c4Lap c4LapH k)) •
          (eigvecOf c4Lap c4LapH k)
          = (c4Adj * c4Adj * c4Adj) *ᵥ (eigvecOf c4Lap c4LapH k) :=
        hexp.symm
      have h4 : (4 * (2 - eigvalOf c4Lap c4LapH k))
          • (eigvecOf c4Lap c4LapH k)
          = (4 : ℝ) • (c4Adj *ᵥ eigvecOf c4Lap c4LapH k) := by
        rw [(smul_smul (4 : ℝ) _ _).symm, ← hactA]
      rw [sub_smul, hA3, h4, hcube]
      exact sub_self _
    rw [smul_eq_zero] at h1
    rcases h1 with h2 | h3
    · linarith
    · exact absurd h3 hvne
  have h3 : (2 - eigvalOf c4Lap c4LapH k)
        * ((2 - eigvalOf c4Lap c4LapH k) ^ 2 - 4) = 0 := by
    linear_combination hkey
  rcases mul_eq_zero.mp h3 with h4 | h5
  · exact Or.inr (Or.inl (by linarith))
  · have h6 : ((2 - eigvalOf c4Lap c4LapH k) + 2)
        * ((2 - eigvalOf c4Lap c4LapH k) - 2) = 0 := by
      linear_combination h5
    rcases mul_eq_zero.mp h6 with h7 | h8
    · exact Or.inr (Or.inr (by linarith))
    · exact Or.inl (by linarith)

/-- `f = ![3/8, -3/8, -1/8, 1/8]` solves the `e 0 − e 1` unit demand on
the cycle (the antisymmetric potential). -/
theorem c4_pot01 :
    c4Lap *ᵥ ![3/8, -3/8, -1/8, 1/8]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, c4Adj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_four] <;>
    try norm_num

/-- **Cycle resistance:** `R 0 1 = 3/4` (the direct edge in parallel
with the three-edge path: `1 ⊕ 3 = 3/4`). -/
theorem c4_R01 : effectiveResistance c4Adj 0 1 = 3 / 4 :=
  effectiveResistance_eq c4Adj c4Adj_isSymm c4Adj_nonneg c4Adj_connected
    ⟨![3/8, -3/8, -1/8, 1/8], c4_pot01, by norm_num [Matrix.cons_val']⟩

theorem c4_dist_one_zero :
    walkDistribution c4Adj 1 0 = ![0, 1/2, 0, 1/2] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, c4Adj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_four, Pi.single_apply]
  all_goals norm_num

theorem c4_dist_one_one :
    walkDistribution c4Adj 1 1 = ![1/2, 0, 1/2, 0] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, c4Adj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_four, Pi.single_apply]
  all_goals norm_num

/-- **The mode-coverage fence**: the contrast bound's rate hypothesis
must quantify over *every* decaying mode. The statement below weakens
it to the `λ ≠ 4` modes only — a certificate `ρ = 0` that genuinely
holds there (the `λ = 2` modes have walk factor `0`) — and is refuted:
the `t = 1` contrast at the adjacent pair is exactly `1` against the
bound `ρ · √R · √R = 0`. -/
theorem c4_contrast_dropped_hyp_refuted_QA :
    ¬ (∀ ρ : ℝ, (∀ k : Fin 4, eigvalOf c4Lap c4LapH k ≠ 4 →
          eigvalOf c4Lap c4LapH k
            * |1 - eigvalOf c4Lap c4LapH k / 2| ^ 1 ≤ ρ) →
        |(walkDistribution c4Adj 1 0 0 - walkDistribution c4Adj 1 1 0)
          - (walkDistribution c4Adj 1 0 1 - walkDistribution c4Adj 1 1 1)|
          ≤ ρ * Real.sqrt (effectiveResistance c4Adj 0 1)
              * Real.sqrt (effectiveResistance c4Adj 0 1)) := by
  intro h
  have hcert : ∀ k : Fin 4, eigvalOf c4Lap c4LapH k ≠ 4 →
      eigvalOf c4Lap c4LapH k
        * |1 - eigvalOf c4Lap c4LapH k / 2| ^ 1 ≤ 0 := by
    intro k hk
    rcases c4_lap_eigvalOf_cases k with h0 | h2 | h4
    · rw [h0]
      norm_num
    · rw [h2]
      norm_num
    · exact absurd h4 hk
  have hbad := h 0 hcert
  rw [c4_dist_one_zero, c4_dist_one_one, c4_R01] at hbad
  have hzero : (0 : ℝ) * Real.sqrt (3 / 4) * Real.sqrt (3 / 4) = 0 := by
    ring
  rw [hzero] at hbad
  norm_num at hbad




end C4Fence

/-! ### The ℓ² → TV conversion QA (2026-08-31)

`proposals/total-variation-mixing-conversion.md`: the conversion
`tvDistance_le_half_sqrt` and its walk-level/depth-form consumers,
exercised at the counted triangle fixture plus a new `K₂` edge
fixture — the conversion's constant is *attained exactly* on `K₂`
(the strongest QA shape a bound theorem can have), and the generic
conversion's mass-one hypothesis is fenced. -/

/-- Adjacency of the unit edge `K₂` on `Fin 2`. -/
def k2Adj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; 1, 0]

theorem k2Adj_apply (i j : Fin 2) : k2Adj i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem k2Adj_isSymm : k2Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [k2Adj_apply, k2Adj_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem k2Adj_nonneg (i j : Fin 2) : 0 ≤ k2Adj i j := by
  rw [k2Adj_apply]
  by_cases h : i = j <;> simp [h]

theorem k2Adj_deg_eq (i : Fin 2) : deg k2Adj i = 1 := by
  rw [deg]
  fin_cases i <;> simp [k2Adj_apply, Fin.sum_univ_two]

theorem k2Adj_deg_pos (i : Fin 2) : 0 < deg k2Adj i := by
  simp [k2Adj_deg_eq]

/-- The edge's support graph is connected. -/
theorem k2_connected : (supportGraph k2Adj k2Adj_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 2,
      (supportGraph k2Adj k2Adj_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        ⟨by decide, by norm_num [k2Adj]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- `π = (1/2, 1/2)` on the edge. -/
theorem k2_pi_QA (i : Fin 2) : stationaryVec k2Adj i = 1/2 := by
  have hv : vol k2Adj (Finset.univ : Finset (Fin 2)) = 2 := by
    simp only [vol, k2Adj_deg_eq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  rw [stationaryVec, k2Adj_deg_eq, hv]

/-- The one-step law from vertex `0` on the edge: `(0, 1)`. -/
theorem k2_dist_one_QA :
    walkDistribution k2Adj 1 0 = ![0, 1] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, k2Adj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_two, Pi.single_apply]

/-- **The exact TV value on the edge at `t = 1`**: the walk law has
moved the whole mass across the edge, so the distance to the uniform
stationary vector is maximal, `1/2`. -/
theorem k2_tv_one_QA :
    tvDistance (walkDistribution k2Adj 1 0) (stationaryVec k2Adj) = 1/2 := by
  rw [tvDistance]
  norm_num [k2_dist_one_QA, k2_pi_QA, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    neg_sub, abs_of_neg, abs_of_nonneg]

/-- **The exact χ² value on the edge at `t = 1`**: `1`. -/
theorem k2_chi2_one_QA :
    chiSquareDistance k2Adj 1 0 = 1 := by
  simp only [chiSquareDistance, k2_dist_one_QA, k2_pi_QA,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  norm_num

/-- **The conversion constant attained exactly**: on `K₂` at `t = 1`,
`TV = 1/2 = (1/2) · √χ² = (1/2) · √1` — no sharper constant in front
of the square root can hold, the strongest QA shape a bound theorem
can have. (Cauchy–Schwarz attains equality here: the centered density
`h₁ = (0, 2)` has `|h − 1|` constant on the two vertices.) -/
theorem k2_conversion_attained_QA :
    tvDistance (walkDistribution k2Adj 1 0) (stationaryVec k2Adj)
      = (1/2) * Real.sqrt (chiSquareDistance k2Adj 1 0) := by
  rw [k2_tv_one_QA, k2_chi2_one_QA, Real.sqrt_one]
  norm_num

/-- **The conversion instance on the edge** (the unconditional
walk-level form; the bipartite edge admits no `r < 1` rate, so the
rate form is honestly vacuous here — the conversion itself is not). -/
theorem k2_conversion_le_QA :
    tvDistance (walkDistribution k2Adj 1 0) (stationaryVec k2Adj)
      ≤ (1/2) * Real.sqrt (chiSquareDistance k2Adj 1 0) :=
  walkDistribution_tvDistance_le k2Adj k2Adj_deg_pos 1 0

/-- The conversion's one remaining hypothesis holds genuinely at the
mass-refutation fixture below (positive weight) — the refutation
isolates exactly the mass clause. -/
theorem tv_conversion_fixture_clauses_QA :
    ∀ i : Fin 2, 0 < (![1, 1] : Fin 2 → ℝ) i := by
  intro i
  fin_cases i <;> norm_num

/-- **The mass-one hypothesis is load-bearing**: at the mass-`2`
weight `w = (1, 1)` (positive, as the conversion's only other
hypothesis demands — see `tv_conversion_fixture_clauses_QA`) and the
genuine probability vector `ν = (1/2, 1/2)`, the un-guarded
conclusion reads `1/2 ≤ (1/2)·√(1/2)`, which is false — total mass
`∑ w = 1` cannot be dropped from the generic conversion. -/
theorem tv_conversion_mass_guard_refuted_QA :
    ¬ (tvDistance (![(1/2 : ℝ), 1/2] : Fin 2 → ℝ) (![1, 1] : Fin 2 → ℝ)
      ≤ (1/2) * Real.sqrt (∑ i : Fin 2,
          ((![(1/2 : ℝ), 1/2] : Fin 2 → ℝ) i
            - (![1, 1] : Fin 2 → ℝ) i)^2
          / (![1, 1] : Fin 2 → ℝ) i)) := by
  intro h
  have hsum : ∑ i : Fin 2,
      ((![(1/2 : ℝ), 1/2] : Fin 2 → ℝ) i
        - (![1, 1] : Fin 2 → ℝ) i)^2
      / (![1, 1] : Fin 2 → ℝ) i = 1/2 := by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  have hL : tvDistance (![(1/2 : ℝ), 1/2] : Fin 2 → ℝ)
      (![1, 1] : Fin 2 → ℝ) = 1/2 := by
    rw [tvDistance]
    norm_num [Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, neg_sub, abs_of_neg,
      abs_of_nonneg]
  rw [hL, hsum] at h
  have hs : Real.sqrt (1/2) < 1 := by
    have hlt := (Real.sqrt_lt_sqrt_iff
      (by norm_num : (0 : ℝ) ≤ 1/2)).mpr (by norm_num : (1/2 : ℝ) < 1)
    rwa [Real.sqrt_one] at hlt
  have hlt : (1/2 : ℝ) * Real.sqrt (1/2) < (1/2) * 1 :=
    mul_lt_mul_of_pos_left hs (by norm_num)
  rw [mul_one] at hlt
  linarith

/-- **The exact TV value on the triangle at `t = 1`**: `1/3`. -/
theorem tri_tv_one_eq_QA :
    tvDistance (walkDistribution triAdj 1 0) (stationaryVec triAdj)
      = 1/3 := by
  rw [tvDistance]
  norm_num [tri_dist_one_QA, tri_pi_QA, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, neg_sub, abs_of_neg, abs_of_nonneg]

/-- **The exact TV value on the triangle at `t = 2`**: `1/6`. -/
theorem tri_tv_two_eq_QA :
    tvDistance (walkDistribution triAdj 2 0) (stationaryVec triAdj)
      = 1/6 := by
  rw [tvDistance]
  norm_num [tri_dist_two_QA, tri_pi_QA, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, neg_sub, abs_of_neg, abs_of_nonneg]

/-- **The exact TV value on the triangle at `t = 3`**: `1/12` (the raw
`ν₃` pinned beside it by `tri_dist_three_zero_QA`). -/
theorem tri_tv_three_eq_QA :
    tvDistance (walkDistribution triAdj 3 0) (stationaryVec triAdj)
      = 1/12 := by
  rw [tvDistance]
  norm_num [tri_dist_three_zero_QA, tri_pi_QA, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, neg_sub, abs_of_neg, abs_of_nonneg]

/-- **The rate form instantiated** — the un-split TV bound on the
triangle at rate `1/2`, `t = 1`. -/
theorem tri_tv_rate_one_QA :
    tvDistance (walkDistribution triAdj 1 0) (stationaryVec triAdj)
      ≤ (1/2) * Real.sqrt
          ((1/2)^(2 * 1) * ((stationaryVec triAdj 0)⁻¹ - 1)) :=
  walkDistribution_tvDistance_le_of_connected triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (1/2) 1 0 tri_rate_QA

/-- The numerics behind the instance: the bound's right side is
`(1/2)·√(1/2)` while the pinned true value is `1/3` — honest Cauchy–
Schwarz slack (equality in the conversion needs `|h − 1|` constant,
which fails on the triangle). -/
theorem tri_tv_rate_one_holds_QA :
    (1/3 : ℝ) ≤ (1/2) * Real.sqrt (1/2) := by
  have hsq : ((2/3 : ℝ))^2 ≤ 1/2 := by norm_num
  have h23 : (2/3 : ℝ) ≤ Real.sqrt (1/2) :=
    Real.le_sqrt_of_sq_le hsq
  linarith

/-- **The split rate form instantiated** — `TV ≤ (1/2)·(1/2)·√2` at
`t = 1` on the triangle. -/
theorem tri_tv_rate_split_one_QA :
    tvDistance (walkDistribution triAdj 1 0) (stationaryVec triAdj)
      ≤ (1/2) * (1/2)^1 * Real.sqrt 2 := by
  have hpi : (stationaryVec triAdj 0)⁻¹ - 1 = 2 := by
    rw [tri_pi_QA 0]
    norm_num
  have h := walkDistribution_tvDistance_le_of_rate triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (by norm_num)
    tri_rate_QA 1 0
  rw [hpi] at h
  exact h

theorem sqrt_two_le_two_QA : Real.sqrt 2 ≤ 2 := by
  have h4 : Real.sqrt ((4 : ℝ)) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ)^2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  exact (Real.sqrt_le_sqrt (by norm_num : (2 : ℝ) ≤ 4)).trans (le_of_eq h4)

/-- **The TV-depth certificate on the triangle**: at rate `1/2` and
`ε = 1/4`, depth `2` already brings the walk law within `1/4` of
stationarity in total variation (threshold: `log (2√2)/log 2 = 3/2
≤ 2`; the true value `TV(2) = 1/6` sits inside). -/
theorem tri_tv_depth_two_QA :
    tvDistance (walkDistribution triAdj 2 0) (stationaryVec triAdj)
      ≤ 1/4 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < Real.sqrt 2 / (2 * (1/4 : ℝ)) := by positivity
  have h4 : (2 : ℝ) ^ (2 : ℕ) = 4 := by norm_num
  have hle : Real.sqrt 2 / (2 * (1/4 : ℝ)) ≤ (2 : ℝ) ^ (2 : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2 * (1/4)), h4,
      show (4 : ℝ) * (2 * (1/4 : ℝ)) = 2 from by norm_num]
    exact sqrt_two_le_two_QA
  have hlog := (Real.log_le_log_iff hpos
    (by rw [h4]; norm_num)).mpr hle
  rw [Real.log_pow] at hlog
  refine walkDistribution_tvDistance_le_of_depth triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (1/4) (by norm_num)
    (by norm_num) (by norm_num) tri_rate_QA 2 0 ?_
  have hpi : (stationaryVec triAdj 0)⁻¹ - 1 = 2 := by
    rw [tri_pi_QA 0]
    norm_num
  rw [hpi, show Real.log (1 / (1/2 : ℝ)) = Real.log 2 from by
      rw [show (1 : ℝ) / (1/2) = 2 from by norm_num],
    div_le_iff₀ hlog2]
  push_cast at hlog ⊢
  linarith

/-- **Depth `1` does not meet the same threshold**: `2 < 2√2`, so the
depth-2 certificate is the sharp one — the threshold hypothesis
genuinely does the work (the true value `TV(1) = 1/3 > 1/4` confirms
no depth-1 TV statement was available on this fixture). -/
theorem tri_tv_depth_one_fails_QA :
    ¬ (Real.log (Real.sqrt 2 / (2 * (1/4 : ℝ)))
      / Real.log 2 ≤ (1 : ℝ)) := by
  intro h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2 : Real.log (Real.sqrt 2 / (2 * (1/4 : ℝ)))
      ≤ (1 : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog2).mp h
  rw [one_mul] at h2
  have hlt : (2 : ℝ) < Real.sqrt 2 / (2 * (1/4 : ℝ)) := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2 * (1/4)),
      show (2 : ℝ) * (2 * (1/4 : ℝ)) = 1 from by norm_num]
    have h1 : (1 : ℝ) < Real.sqrt 2 := by
      have hlt2 := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
        (by norm_num : (1 : ℝ) < 2)
      rwa [Real.sqrt_one] at hlt2
    linarith
  have hmono := (Real.log_lt_log_iff (by norm_num : (0 : ℝ) < 2)
    (by positivity : 0 < Real.sqrt 2 / (2 * (1/4 : ℝ)))).mpr hlt
  linarith

/-- **The two-start TV twin instantiated**: at depth `3` both starts'
thresholds hold (`log (2√2)/log 2 = 3/2 ≤ 3`), so the two `3`-step
laws are within `2·(1/4) = 1/2` of each other in total variation. -/
theorem tri_tv_two_start_three_QA :
    tvDistance (walkDistribution triAdj 3 0) (walkDistribution triAdj 3 1)
      ≤ 2 * (1/4) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos : 0 < Real.sqrt 2 / (2 * (1/4 : ℝ)) := by positivity
  have h8 : (2 : ℝ) ^ (3 : ℕ) = 8 := by norm_num
  have hle : Real.sqrt 2 / (2 * (1/4 : ℝ)) ≤ (2 : ℝ) ^ (3 : ℕ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2 * (1/4)), h8,
      show (8 : ℝ) * (2 * (1/4 : ℝ)) = 4 from by norm_num]
    linarith [sqrt_two_le_two_QA]
  have hlog := (Real.log_le_log_iff hpos (by rw [h8]; norm_num)).mpr hle
  rw [Real.log_pow] at hlog
  have hthr0 : Real.log (Real.sqrt 2 / (2 * (1/4 : ℝ)))
      / Real.log 2 ≤ (3 : ℝ) := by
    rw [div_le_iff₀ hlog2]
    push_cast at hlog ⊢
    linarith
  have e0 : (stationaryVec triAdj 0)⁻¹ - 1 = 2 := by
    rw [tri_pi_QA 0]
    norm_num
  have e1 : (stationaryVec triAdj 1)⁻¹ - 1 = 2 := by
    rw [tri_pi_QA 1]
    norm_num
  refine walkDistribution_tvDistance_sub_le_of_depth triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (1/4) (by norm_num)
    (by norm_num) (by norm_num) tri_rate_QA 3 0 1 ?_ ?_
  · rw [e0, show Real.log (1 / (1/2 : ℝ)) = Real.log 2 from by
      rw [show (1 : ℝ) / (1/2) = 2 from by norm_num]]
    exact hthr0
  · rw [e1, show Real.log (1 / (1/2 : ℝ)) = Real.log 2 from by
      rw [show (1 : ℝ) / (1/2) = 2 from by norm_num]]
    exact hthr0

/-- **The two-start raw value**: `TV(ν₃ 0, ν₃ 1) = 1/8` — the true
distance at a quarter of the `2ε = 1/2` bound, honest slack beside
the certified statement. -/
theorem tri_tv_two_start_value_QA :
    tvDistance (walkDistribution triAdj 3 0) (walkDistribution triAdj 3 1)
      = 1/8 := by
  rw [tvDistance]
  norm_num [tri_dist_three_zero_QA, tri_dist_three_one_QA,
    Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, neg_sub, abs_of_neg,
    abs_of_nonneg]

/-!
## Continuous-time χ² mixing

 `proposals/continuous-time-chi-square-mixing.md` (2026-08-31): exact
attainment at every time on the triangle (both nonzero modes at
`3/2`, so value equals bound at every `t`), the `t = 0` corner, mass
preservation, the wrong-constant refutation, and on the disconnected
fixture the exact closed form `1/3 + (8/3)e^{-3t}` with the gap pinned
exactly zero, the rate-1 instance, and the positive-gap fence. The
path (irregular) exact-decay QA was delivered 2026-08-31 as the
delivery's deferred follow-on (`path_cont_chi2_exact_QA`:
`χ²_cont(t, center) = e^{−4t}` at every time, the conjugation
`√D(−1, 1, −1) = (−1, √2, −1)` non-scalar, with the `λ₂(L_sym P₃) = 1`
trace-route pin, the strict-slack witness, and the wrong-constant
fence).
-/

local notation "triL" => normalizedLaplacian triAdj
local notation "triH" => normalizedLaplacian_symmetric triAdj triAdj_isSymm
local notation "pathL" => normalizedLaplacian pathAdj
local notation "pathH" => normalizedLaplacian_symmetric pathAdj pathAdj_isSymm
local notation "discL" => normalizedLaplacian discAdj
local notation "discH" => normalizedLaplacian_symmetric discAdj discAdj_isSymm

/-! ## Continuous-time χ²: the triangle (exact attainment) -/

/-- The triangle's normalized spectral gap is exactly `3/2`: every
sorted eigenvalue is `0` or `3/2` (`tri_eigvalOf_cases` +
`evals_mem_eigvalOf`) and they sum to the trace `3`
(`evals_sum_eq_trace` + `tri_trace`), forcing two `3/2`'s and one `0` —
so the middle entry is `3/2`. -/
theorem tri_secondEval_QA :
    secondEval triL triH (by norm_num) = 3/2 := by
  have hcases : ∀ k : Fin (Fintype.card (Fin 3)),
      evals triH k = 0 ∨ evals triH k = 3/2 := by
    intro k
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf triH k
    rw [hi]
    exact tri_eigvalOf_cases i
  have hsum : ∑ k, evals triH k = 3 := by
    rw [evals_sum_eq_trace triH, tri_trace]
  have hsum3 : ∑ i : Fin 3, evals triH i = 3 := hsum
  simp only [Fin.sum_univ_three] at hsum3
  have hse : secondEval triL triH (by norm_num) = evals triH (1 : Fin 3) := rfl
  rw [hse]
  rcases hcases (1 : Fin 3) with h1 | h1
  · exfalso
    have hmono : evals triH (0 : Fin 3) ≤ evals triH (1 : Fin 3) :=
      evals_sorted triH (by norm_num)
    rw [h1] at hmono
    rcases hcases (0 : Fin 3) with h0' | h0'
    · have h2le : evals triH (2 : Fin 3) ≤ 3/2 := by
        rcases hcases (2 : Fin 3) with h | h
        · rw [h]; norm_num
        · exact le_of_eq h
      rw [h0', h1] at hsum3
      linarith
    · rw [h0'] at hmono
      linarith
  · exact h1

/-- The centered initial density `triG` is a `3/2`-eigenvector of the
triangle's normalized Laplacian (raw entrywise computation through the
fixture's entrywise action table). -/
theorem tri_lapsym_mulVec_triG_QA : triL *ᵥ triG = (3/2 : ℝ) • triG := by
  have h : ∀ j : Fin 3, (triL *ᵥ triG) j = ((3/2 : ℝ) • triG) j := by
    intro j
    rw [Pi.smul_apply, smul_eq_mul, tri_normalizedLaplacian_mulVec_apply]
    fin_cases j <;> simp [triAdj_apply, triG, Fin.sum_univ_three] <;> norm_num
  funext j
  exact h j

/-- **Exact attainment at every time** on the triangle: both nonzero
`L_sym`-modes sit at `3/2`, so the continuous-time χ² decays at exactly
the bound's rate — `χ²_cont(t, 0) = 2·e^{−3t}` for every `t`, the
strongest QA shape a bound theorem can have. Route: the conjugated
centered density is `√2 • triG` (a single mode), the eigenmode engine
damps it by `e^{−3t/2}`, and the π-isometry rescales by `1/vol = 1/6`. -/
theorem tri_cont_chi2_exact_QA (t : ℝ) :
    contChiSquareDistance triAdj t 0 = 2 * Real.exp (-(3 * t)) := by
  have hcenter : (walkDensity triAdj 0 0 : Fin 3 → ℝ) - 1 = triG := by
    funext i
    exact congrFun tri_centered_density i
  have hD : degreeSqrt triAdj *ᵥ triG = (Real.sqrt 2) • triG := by
    funext i
    rw [degreeSqrt_mulVec_apply, triAdj_deg_eq, Pi.smul_apply, smul_eq_mul]
  have hkey : (t : ℝ) • ((3/2 : ℝ) • triG) = (t * (3/2)) • triG :=
    smul_smul t (3/2) triG
  have hmode : normalizedHeatKernel triAdj t *ᵥ triG
      = Real.exp (-(t * (3/2 : ℝ))) • triG := by
    rw [normalizedHeatKernel]
    refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, tri_lapsym_mulVec_triG_QA]
    have hstep2 : -(t • ((3/2 : ℝ) • triG)) = (-(t * (3/2 : ℝ))) • triG := by
      funext i
      rw [Pi.neg_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul, Pi.smul_apply, smul_eq_mul]
      ring
    exact hstep2
  have hn : Matrix.dotProduct triG triG = 6 := by
    simp [Matrix.dotProduct, triG, Fin.sum_univ_three]
    ring
  set E : ℝ := Real.exp (-(3 * t)) with hEdef
  have hpair : Real.exp (-(t * (3/2 : ℝ))) * Real.exp (-(t * (3/2 : ℝ)))
      = E := by
    rw [hEdef, ← Real.exp_add]
    congr 1
    ring
  have hfinal : (6 : ℝ)⁻¹ * Matrix.dotProduct
      ((Real.sqrt 2) • (Real.exp (-(t * (3/2))) • triG))
      ((Real.sqrt 2) • (Real.exp (-(t * (3/2))) • triG))
      = 2 * E := by
    rw [smul_smul, Matrix.smul_dotProduct, Matrix.dotProduct_smul,
      smul_eq_mul, smul_eq_mul, hn,
      show ((Real.sqrt 2) * Real.exp (-(t * (3/2)))
        * ((Real.sqrt 2) * Real.exp (-(t * (3/2))) * 6))
        = ((Real.sqrt 2) * (Real.sqrt 2)) * 6
          * (Real.exp (-(t * (3/2))) * Real.exp (-(t * (3/2)))) from by ring,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), hpair]
    field_simp
    ring
  rw [contChiSquareDistance_eq_inv_mul triAdj triAdj_deg_pos t 0,
    degreeSqrt_mulVec_contWalkDensity_sub_one triAdj triAdj_deg_pos t 0,
    hcenter, hD, Matrix.mulVec_smul, hmode, tri_vol_QA]
  exact hfinal

/-- The consumer theorem instantiated on the triangle — the bound's RHS
at the pinned gap `3/2`. -/
theorem tri_cont_mixing_QA (t : ℝ) (ht : 0 ≤ t) :
    contChiSquareDistance triAdj t 0
      ≤ Real.exp (-(2 * t * secondEval triL triH (by norm_num)))
        * ((stationaryVec triAdj 0)⁻¹ - 1) :=
  contChiSquareDistance_le triAdj triAdj_isSymm triAdj_nonneg
    triAdj_deg_pos (by norm_num) ht 0

/-- **The bound is attained** on the triangle: value equals bound at
every time (both reduce to `2·e^{−3t}`; the stationary weight is `1/3`,
so the constant is `3 − 1 = 2`). -/
theorem tri_cont_attained_QA (t : ℝ) :
    contChiSquareDistance triAdj t 0
      = Real.exp (-(2 * t * secondEval triL triH (by norm_num)))
        * ((stationaryVec triAdj 0)⁻¹ - 1) := by
  rw [tri_cont_chi2_exact_QA, tri_secondEval_QA, tri_pi_QA]
  have hE : (2 * t * (3/2 : ℝ)) = 3 * t := by ring
  rw [hE]
  ring

/-- **The `t = 0` corner**: the continuous χ² starts at the pinned
initial value `((π 0)⁻¹ − 1) = 2`. -/
theorem tri_cont_chi2_zero_QA : contChiSquareDistance triAdj 0 0 = 2 := by
  rw [contChiSquareDistance_zero triAdj triAdj_deg_pos 0, tri_pi_QA]
  norm_num

/-- **Mass preservation instance**: the continuous-time density stays a
density at every time. -/
theorem tri_cont_mass_QA (t : ℝ) :
    ∑ i, stationaryVec triAdj i * contWalkDensity triAdj t 0 i = 1 :=
  sum_stationaryVec_contWalkDensity triAdj triAdj_isSymm triAdj_deg_pos t 0

/-- **The wrong-constant refutation**: pretending the gap is `2` reads
`2·e^{−3} ≤ 2·e^{−4}` at `t = 1` — refuted by `e^{−4} < e^{−3}`. The
gap constant is load-bearing. -/
theorem tri_wrong_gap_refuted_QA :
    ¬ (∀ t : ℝ, 0 ≤ t → contChiSquareDistance triAdj t 0
        ≤ Real.exp (-(2 * t * 2)) * ((stationaryVec triAdj 0)⁻¹ - 1)) := by
  intro h
  have h1 := h 1 (by norm_num)
  rw [tri_cont_chi2_exact_QA, tri_pi_QA] at h1
  norm_num at h1
  have hlt : Real.exp (-(4 : ℝ)) < Real.exp (-(3 : ℝ)) :=
    Real.exp_lt_exp.mpr (by norm_num)
  linarith

/-! ## Continuous-time χ²: the path (irregular input, exact
single-mode decay) -/

/-- The trace of the path's normalized Laplacian: each diagonal entry
is `1 − 0 = 1` (no loops), so the trace is `3`. -/
theorem path_trace : (normalizedLaplacian pathAdj).trace = 3 := by
  have hz : ∀ j : Fin 3,
      (degreeInvSqrt pathAdj * pathAdj * degreeInvSqrt pathAdj) j j = 0 := by
    intro j
    have h1 : (0:ℝ) ≤ 1 := by norm_num
    have h2 : (0:ℝ) ≤ 2 := by norm_num
    fin_cases j <;>
      simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply,
        Fin.sum_univ_three, pathAdj, pathAdj_deg_zero, pathAdj_deg_one,
        pathAdj_deg_two, Real.sqrt_one, Real.mul_self_sqrt h2,
        Real.mul_self_sqrt h1]
  simp [Matrix.trace, normalizedLaplacian, hz]

/-- The path's `λ = 1` eigenvector witness: `(1, 0, −1)` (raw
entrywise). -/
theorem path_lapsym_mulVec_w1_QA :
    pathL *ᵥ (![1, 0, -1] : Fin 3 → ℝ) = (1 : ℝ) • ![1, 0, -1] := by
  funext j
  rw [path_normalizedLaplacian_mulVec_apply]
  fin_cases j <;>
    simp [pathAdj, Fin.sum_univ_three, Pi.smul_apply, smul_eq_mul]

/-- The path's `λ = 2` (top) eigenvector witness `(−1, √2, −1)`: raw
entrywise, through the fixture's entrywise action table. -/
theorem path_lapsym_mulVec_top_QA :
    pathL *ᵥ (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ)
      = (2 : ℝ) • ![-1, Real.sqrt 2, -1] := by
  have hsq : (Real.sqrt 2) * (Real.sqrt 2) = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have h0 : (pathL *ᵥ (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ)) 0
      = ((2 : ℝ) • ![-1, Real.sqrt 2, -1] : Fin 3 → ℝ) 0 := by
    rw [path_normalizedLaplacian_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    simp only [pathAdj, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons]
    norm_num
  have h1 : (pathL *ᵥ (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ)) 1
      = ((2 : ℝ) • ![-1, Real.sqrt 2, -1] : Fin 3 → ℝ) 1 := by
    rw [path_normalizedLaplacian_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    simp only [pathAdj, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons]
    norm_num
    field_simp
    nlinarith [hsq]
  have h2 : (pathL *ᵥ (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ)) 2
      = ((2 : ℝ) • ![-1, Real.sqrt 2, -1] : Fin 3 → ℝ) 2 := by
    rw [path_normalizedLaplacian_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    simp only [pathAdj, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons]
    norm_num
  funext j
  fin_cases j
  exacts [h0, h1, h2]

/-- **The path's normalized spectral gap is exactly `1`** — the trace
route: the witnesses `0` (the kernel `√D·1`), `1` (`(1, 0, −1)`), and
`2` (`(−1, √2, −1)`) all occur in the sorted spectrum, and the SOS
certificates (`path_eigvalOf_nonneg`/`_le_two`) bound every entry into
`[0, 2]`, so the three distinct member values exhaust the three-entry
list; the sum is the trace `3`. -/
theorem path_secondEval_QA :
    secondEval pathL pathH (by norm_num) = 1 := by
  have hkne : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have e := congrFun h 0
    simp at e
  have htne : (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have e := congrFun h 0
    simp at e
  have hker : pathL *ᵥ (degreeSqrt pathAdj *ᵥ onesVec) = 0 :=
    normalizedLaplacian_mulVec_degreeSqrt_onesVec pathAdj pathAdj_deg_pos
  have hkzerone : (degreeSqrt pathAdj *ᵥ onesVec : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have e := congrFun h 0
    simp [degreeSqrt, Matrix.mulVec_diagonal, onesVec, pathAdj_deg_zero,
      Real.sqrt_one] at e
  -- the three witness values occur in the sorted spectrum
  have hwit : ∀ μ : ℝ, (∃ v : Fin 3 → ℝ, v ≠ 0 ∧ pathL *ᵥ v = μ • v) →
      ∃ k : Fin (Fintype.card (Fin 3)), evals pathH k = μ := by
    intro μ ⟨v, hv0, hvμ⟩
    obtain ⟨i, hi⟩ :=
      exists_eigvalOf_eq_of_mulVec_eq_smul pathH hv0 hvμ
    obtain ⟨k, hk⟩ := eigvalOf_mem_evals pathH i
    exact ⟨k, hk.trans hi⟩
  obtain ⟨k0, hk0⟩ := hwit 0 ⟨_, hkzerone, by simpa using hker⟩
  obtain ⟨k1, hk1⟩ := hwit 1 ⟨_, hkne, path_lapsym_mulVec_w1_QA⟩
  obtain ⟨k2, hk2⟩ := hwit 2 ⟨_, htne, path_lapsym_mulVec_top_QA⟩
  -- every entry is bounded into [0, 2]
  have hb : ∀ k : Fin (Fintype.card (Fin 3)),
      0 ≤ evals pathH k ∧ evals pathH k ≤ 2 := by
    intro k
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf pathH k
    rw [hi]
    exact ⟨path_eigvalOf_nonneg i, path_eigvalOf_le_two i⟩
  have hmono : Monotone (evals pathH) := evals_sorted pathH
  have hle : Fintype.card (Fin 3) ≤ 3 := by simp
  have hk2lt : (k2 : ℕ) < 3 := lt_of_lt_of_le k2.isLt hle
  have h2val : ((2 : Fin (Fintype.card (Fin 3))) : ℕ) = 2 := by
    simp [Fintype.card_fin]
  have hk2le : k2 ≤ (2 : Fin (Fintype.card (Fin 3))) :=
    Fin.le_def.mpr (by rw [h2val]; omega)
  have h2ge : (2 : ℝ) ≤ evals pathH (2 : Fin 3) := by
    have hm := hmono hk2le
    rw [hk2] at hm
    exact hm
  have h2eq : evals pathH (2 : Fin 3) = 2 :=
    le_antisymm (hb _).2 h2ge
  have h0le' : evals pathH (0 : Fin 3) ≤ 0 :=
    (hmono (Fin.zero_le k0)).trans_eq hk0
  have h0eq : evals pathH (0 : Fin 3) = 0 :=
    le_antisymm h0le' (hb _).1
  have hsum : ∑ k, evals pathH k = 3 := by
    rw [evals_sum_eq_trace pathH, path_trace]
  have hsum3 : ∑ i : Fin 3, evals pathH i = 3 := hsum
  simp only [Fin.sum_univ_three] at hsum3
  rw [show secondEval pathL pathH (by norm_num)
      = evals pathH (1 : Fin 3) from rfl]
  rw [h0eq, h2eq] at hsum3
  have hone : evals pathH (1 : Fin 3) = 1 := by linarith
  rw [hone]

/-- The centered initial density of the path walk started at the
center vertex: `h₀ − 1 = (−1, 1, −1)`. -/
theorem path_centered_density :
    (fun i => walkDensity pathAdj 0 1 i - 1) = ![-1, 1, -1] := by
  funext i
  fin_cases i
  all_goals simp [walkDensity, walkDistribution_zero, path_pi_QA,
    Pi.single_apply]
  all_goals norm_num

/-- The conjugation step, non-scalar on this fixture: `√D` sends the
centered density `(−1, 1, −1)` to the top eigenvector
`(−1, √2, −1)` — the identity that makes the π-weighted χ² exactly the
Euclidean contraction of the normalized heat kernel. -/
theorem path_conj_centered_QA :
    degreeSqrt pathAdj *ᵥ (![-1, 1, -1] : Fin 3 → ℝ)
      = ![-1, Real.sqrt 2, -1] := by
  funext i
  rw [degreeSqrt_mulVec_apply]
  fin_cases i <;>
    simp [degreeSqrt, Matrix.diagonal_apply, pathAdj_deg_zero,
      pathAdj_deg_one, pathAdj_deg_two, Real.sqrt_one]

/-- The normalized heat kernel damps the top mode at `e^{−2t}`. -/
theorem path_heat_mulVec_top_QA (t : ℝ) :
    normalizedHeatKernel pathAdj t *ᵥ (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ)
      = Real.exp (-(2 * t)) • ![-1, Real.sqrt 2, -1] := by
  rw [normalizedHeatKernel]
  refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
  rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, path_lapsym_mulVec_top_QA]
  have hstep2 : -(t • ((2 : ℝ) • (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ)))
      = (-(2 * t)) • (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ) := by
    funext i
    rw [Pi.neg_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
      smul_eq_mul, Pi.smul_apply, smul_eq_mul]
    ring
  exact hstep2

/-- The top-mode norm pinned raw: `‖(−1, √2, −1)‖² = 1 + 2 + 1 = 4`. -/
theorem path_top_dotProduct_QA :
    Matrix.dotProduct (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ)
      (![-1, Real.sqrt 2, -1] : Fin 3 → ℝ) = 4 := by
  have h2 : (Real.sqrt 2) * (Real.sqrt 2) = 2 :=
    Real.mul_self_sqrt (by norm_num)
  simp [Matrix.dotProduct, Fin.sum_univ_three, h2]
  norm_num

/-- **The exact single-mode decay** on the path: the conjugated
centered initial density is the top eigenvector, so
`χ²_cont(t, center) = e^{−4t}` exactly, at every time — the decay at
twice the gap's rate, witnessed on the fixture where `√D` is
genuinely non-scalar. -/
theorem path_cont_chi2_exact_QA (t : ℝ) :
    contChiSquareDistance pathAdj t 1 = Real.exp (-(4 * t)) := by
  have hcenter : (walkDensity pathAdj 0 1 : Fin 3 → ℝ) - 1
      = ![-1, 1, -1] := by
    funext i
    exact congrFun path_centered_density i
  have hD : degreeSqrt pathAdj *ᵥ (![-1, 1, -1] : Fin 3 → ℝ)
      = ![-1, Real.sqrt 2, -1] := path_conj_centered_QA
  have hn := path_top_dotProduct_QA
  set E2 : ℝ := Real.exp (-(2 * t)) with hE2def
  set E4 : ℝ := Real.exp (-(4 * t)) with hE4def
  have hpair : E2 * E2 = E4 := by
    rw [hE2def, hE4def, ← Real.exp_add]
    congr 1
    ring
  have hfinal : (4 : ℝ)⁻¹ * Matrix.dotProduct
      (E2 • ![-1, Real.sqrt 2, -1])
      (E2 • ![-1, Real.sqrt 2, -1] : Fin 3 → ℝ) = E4 := by
    rw [Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hn, ← hpair]
    ring
  rw [contChiSquareDistance_eq_inv_mul pathAdj pathAdj_deg_pos t 1,
    degreeSqrt_mulVec_contWalkDensity_sub_one pathAdj pathAdj_deg_pos t 1,
    hcenter, hD, path_heat_mulVec_top_QA, path_vol_QA]
  exact hfinal

/-- The consumer theorem instantiated on the path — the bound's RHS at
the pinned gap `1`. -/
theorem path_cont_mixing_QA (t : ℝ) (ht : 0 ≤ t) :
    contChiSquareDistance pathAdj t 1
      ≤ Real.exp (-(2 * t * secondEval pathL pathH (by norm_num)))
        * ((stationaryVec pathAdj 1)⁻¹ - 1) :=
  contChiSquareDistance_le pathAdj pathAdj_isSymm pathAdj_nonneg
    pathAdj_deg_pos (by norm_num) ht 1

/-- **Honest strict slack at every positive time**: the exact value
`e^{−4t}` is strictly below the bound `e^{−2t·λ₂}·((π c)⁻¹−1) =
e^{−2t}` for every `t > 0` — the center start is a pure top mode, so
it decays at twice the certified rate. The twin of the triangle's
exact-attainment pin. -/
theorem path_cont_slack_QA (t : ℝ) (ht : 0 < t) :
    contChiSquareDistance pathAdj t 1
      < Real.exp (-(2 * t * secondEval pathL pathH (by norm_num)))
        * ((stationaryVec pathAdj 1)⁻¹ - 1) := by
  rw [path_cont_chi2_exact_QA, path_secondEval_QA, path_pi_QA]
  norm_num
  linarith

/-- **The `t = 0` corner**: the continuous χ² starts at the pinned
initial value `((π c)⁻¹ − 1) = 2 − 1 = 1`. -/
theorem path_cont_chi2_zero_QA : contChiSquareDistance pathAdj 0 1 = 1 := by
  rw [contChiSquareDistance_zero pathAdj pathAdj_deg_pos 1, path_pi_QA]
  norm_num

/-- **Mass preservation instance**: the continuous-time density stays
a density at every time on the irregular fixture too. -/
theorem path_cont_mass_QA (t : ℝ) :
    ∑ i, stationaryVec pathAdj i * contWalkDensity pathAdj t 1 i = 1 :=
  sum_stationaryVec_contWalkDensity pathAdj pathAdj_isSymm pathAdj_deg_pos t 1

/-- **The wrong-constant refutation**: pretending the gap is `3` reads
`e^{−4} ≤ e^{−6}` at `t = 1` — refuted by exp monotonicity. The gap
constant is load-bearing on the irregular fixture as well. -/
theorem path_wrong_gap_refuted_QA :
    ¬ (∀ t : ℝ, 0 ≤ t → contChiSquareDistance pathAdj t 1
        ≤ Real.exp (-(2 * t * 3)) * ((stationaryVec pathAdj 1)⁻¹ - 1)) := by
  intro h
  have h1 := h 1 (by norm_num)
  rw [path_cont_chi2_exact_QA, path_pi_QA] at h1
  norm_num at h1

/-! ## Continuous-time χ²: the disconnected fixture
(the gap-zero branch) -/

/-- The disconnected fixture's normalized gap is exactly `0` — through
the shelf's non-connectedness transfer (with PSD the other side). -/
theorem disc_secondEval_zero_QA :
    secondEval discL discH (by norm_num) = 0 :=
  secondEval_normalizedLaplacian_eq_zero_of_not_connected discAdj
    discAdj_isSymm discAdj_nonneg discAdj_deg_pos (by norm_num)
    disc_not_connected

/-- The start-at-0 density on the fixture: `h₀ = (4, 0, 0, 0)`
(`π = 1/4` everywhere). -/
theorem disc_density_zero_QA : walkDensity discAdj 0 0 = ![(4 : ℝ), 0, 0, 0] := by
  funext i
  fin_cases i
  all_goals simp [walkDensity, walkDistribution_zero, disc_pi_QA,
    Pi.single_apply]

theorem disc_lapsym_mulVec_kerTri_QA :
    discL *ᵥ (![(1 : ℝ), 1, 1, 0] : Fin 4 → ℝ) = 0 := by
  have h : ∀ j : Fin 4, (discL *ᵥ (![(1 : ℝ), 1, 1, 0] : Fin 4 → ℝ)) j = 0 := by
    intro j
    rw [disc_normalizedLaplacian_mulVec_apply]
    fin_cases j <;> simp [discAdj_apply, Fin.sum_univ_four] <;> norm_num
  funext j
  exact h j

/-- The `3/2`-eigenvector witness on the fixture: the triangle block's
centered direction `(8, −4, −4, 0)/3` (a scalar multiple of `triG`
padded with the loop zero). -/
theorem disc_lapsym_mulVec_mid_QA :
    discL *ᵥ (![(8 : ℝ)/3, -4/3, -4/3, 0] : Fin 4 → ℝ)
      = (3/2 : ℝ) • ![(8 : ℝ)/3, -4/3, -4/3, 0] := by
  have h : ∀ j : Fin 4, (discL *ᵥ (![(8 : ℝ)/3, -4/3, -4/3, 0] : Fin 4 → ℝ)) j
      = ((3/2 : ℝ) • ![(8 : ℝ)/3, -4/3, -4/3, 0] : Fin 4 → ℝ) j := by
    intro j
    rw [disc_normalizedLaplacian_mulVec_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases j <;> simp [discAdj_apply, Fin.sum_univ_four] <;> norm_num
  funext j
  exact h j

theorem disc_lapsym_mulVec_kerLoop_QA :
    discL *ᵥ (![(0 : ℝ), 0, 0, -1] : Fin 4 → ℝ) = 0 := by
  have h : ∀ j : Fin 4, (discL *ᵥ (![(0 : ℝ), 0, 0, -1] : Fin 4 → ℝ)) j = 0 := by
    intro j
    rw [disc_normalizedLaplacian_mulVec_apply]
    fin_cases j <;> simp [discAdj_apply, Fin.sum_univ_four]
  funext j
  exact h j

/-- The normalized heat kernel's action on the fixture's conjugated
centered start: the triangle block's kernel part stays, the `3/2` part
damps by `e^{−3t/2}`, the loop coordinate stays — the closed form every
exact value below evaluates. -/
theorem disc_heat_mulVec_w_QA (t : ℝ) :
    normalizedHeatKernel discAdj t *ᵥ (![(3 : ℝ), -1, -1, -1] : Fin 4 → ℝ)
      = ![(1 : ℝ)/3 + (8/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)), -1] := by
  have hfix : ∀ v : Fin 4 → ℝ, discL *ᵥ v = 0 →
      normalizedHeatKernel discAdj t *ᵥ v = v := by
    intro v hv
    rw [normalizedHeatKernel]
    refine exp_mulVec_eq_of_mulVec_eq_zero _ _ ?_
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, hv, smul_zero, neg_zero]
  have hmid : normalizedHeatKernel discAdj t *ᵥ
      (![(8 : ℝ)/3, -4/3, -4/3, 0] : Fin 4 → ℝ)
      = Real.exp (-((3/2 : ℝ) * t)) • ![(8 : ℝ)/3, -4/3, -4/3, 0] := by
    rw [normalizedHeatKernel]
    refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, disc_lapsym_mulVec_mid_QA]
    have hstep2 : -(t • ((3/2 : ℝ)
        • (![(8 : ℝ)/3, -4/3, -4/3, 0] : Fin 4 → ℝ)))
        = (-((3/2 : ℝ) * t)) • (![(8 : ℝ)/3, -4/3, -4/3, 0] : Fin 4 → ℝ) := by
      funext i
      rw [Pi.neg_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul, Pi.smul_apply, smul_eq_mul]
      ring
    exact hstep2
  have hv : (![(3 : ℝ), -1, -1, -1] : Fin 4 → ℝ)
      = ((1/3 : ℝ) • ![(1 : ℝ), 1, 1, 0]
        + ![(8 : ℝ)/3, -4/3, -4/3, 0] + ![(0 : ℝ), 0, 0, -1] :
          Fin 4 → ℝ) := by
    funext i
    fin_cases i <;> norm_num
  rw [hv, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    hfix _ disc_lapsym_mulVec_kerTri_QA, hmid,
    hfix _ disc_lapsym_mulVec_kerLoop_QA]
  funext i
  fin_cases i <;> simp <;> first
  | rfl
  | ring_nf

/-- **The disconnected exact closed form**:
`χ²_cont(t, 0) = 1/3 + (8/3)·e^{−3t}` on the triangle⊕self-loop
fixture — decay at the *within-component* rate the theorem honestly
does not claim, with limit `1/3` (not `0`: the walk never crosses
components; `χ²(0) = 3` matches `(π 0)⁻¹ − 1`). -/
theorem disc_cont_chi2_exact_QA (t : ℝ) :
    contChiSquareDistance discAdj t 0
      = 1/3 + (8/3) * Real.exp (-(3 * t)) := by
  have hcenter : (walkDensity discAdj 0 0 : Fin 4 → ℝ) - 1
      = ![(3 : ℝ), -1, -1, -1] := by
    rw [disc_density_zero_QA]
    funext i
    fin_cases i
    all_goals norm_num [walkDensity, walkDistribution_zero, disc_pi_QA,
      Pi.single_apply]
  have hD : degreeSqrt discAdj *ᵥ (![(3 : ℝ), -1, -1, -1] : Fin 4 → ℝ)
      = (Real.sqrt 2) • ![(3 : ℝ), -1, -1, -1] := by
    funext i
    rw [degreeSqrt_mulVec_apply, discAdj_deg_eq, Pi.smul_apply, smul_eq_mul]
  have hsq : (Real.sqrt 2) * (Real.sqrt 2) = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hpair : Real.exp (-((3/2 : ℝ) * t)) * Real.exp (-((3/2 : ℝ) * t))
      = Real.exp (-(3 * t)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hr : Matrix.dotProduct
      (![(1 : ℝ)/3 + (8/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)), -1] : Fin 4 → ℝ)
      (![(1 : ℝ)/3 + (8/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)), -1] : Fin 4 → ℝ)
      = 4/3 + (32/3) * Real.exp (-(3 * t)) := by
    set e : ℝ := Real.exp (-((3/2 : ℝ) * t)) with hed
    have hp2 : e * e = Real.exp (-(t * 3)) := by
      rw [hed, ← Real.exp_add]
      congr 1
      ring
    simp [Matrix.dotProduct, Fin.sum_univ_four]
    nlinarith [hp2]
  have hfinal : (8 : ℝ)⁻¹ * Matrix.dotProduct
      ((Real.sqrt 2) • (![(1 : ℝ)/3 + (8/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)), -1] : Fin 4 → ℝ))
      ((Real.sqrt 2) • (![(1 : ℝ)/3 + (8/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)),
          1/3 - (4/3) * Real.exp (-((3/2 : ℝ) * t)), -1] : Fin 4 → ℝ))
      = 1/3 + (8/3) * Real.exp (-(3 * t)) := by
    rw [Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
      smul_eq_mul, hr,
      show ((Real.sqrt 2) * ((Real.sqrt 2) * (4/3 + (32/3) * Real.exp (-(3 * t)))))
        = ((Real.sqrt 2) * (Real.sqrt 2))
          * (4/3 + (32/3) * Real.exp (-(3 * t))) from by ring, hsq]
    field_simp
    linarith
  rw [contChiSquareDistance_eq_inv_mul discAdj discAdj_deg_pos t 0,
    degreeSqrt_mulVec_contWalkDensity_sub_one discAdj discAdj_deg_pos t 0,
    hcenter, hD, Matrix.mulVec_smul, disc_heat_mulVec_w_QA, disc_vol_QA]
  exact hfinal

/-- The consumer theorem instantiated at the gap-zero fixture: the
rate is `e^{−2t·0} = 1` — the true rate-1 statement. -/
theorem disc_cont_mixing_QA (t : ℝ) (ht : 0 ≤ t) :
    contChiSquareDistance discAdj t 0
      ≤ Real.exp (-(2 * t * secondEval discL discH (by norm_num)))
        * ((stationaryVec discAdj 0)⁻¹ - 1) :=
  contChiSquareDistance_le discAdj discAdj_isSymm discAdj_nonneg
    discAdj_deg_pos (by norm_num) ht 0

/-- **The rate-1 arithmetic at the exact value**: with
`e^{−3t} ≤ 1`, the closed form `1/3 + (8/3)e^{−3t}` stays under `3` —
the theorem's bound is honest on the disconnected fixture, with slack. -/
theorem disc_rate_one_arith_QA (t : ℝ) (ht : 0 ≤ t) :
    contChiSquareDistance discAdj t 0 ≤ (stationaryVec discAdj 0)⁻¹ - 1 := by
  rw [disc_cont_chi2_exact_QA, disc_pi_QA]
  norm_num
  have hδ : Real.exp (-(3 * t)) ≤ 1 := by
    have h0 : (-(3 * t)) ≤ 0 := neg_nonpos.2 (mul_nonneg (by norm_num) ht)
    have h := Real.exp_le_exp.2 h0
    rwa [Real.exp_zero] at h
  linarith

/-- **The positive-gap fence on the gap-zero fixture**: pretending
`λ₂ = 1` reads `1/3 + (8/3)e^{−6} ≤ 4e^{−4}` at `t = 2` — refuted,
since the value is at least `1/3 > 4e^{−4}` (the latter from the pin
`2 < e`, giving `e⁴ > 16 > 12`). The gap hypothesis is load-bearing
exactly at the connectivity boundary. -/
theorem disc_gap_fence_QA :
    ¬ (∀ t : ℝ, 0 ≤ t → contChiSquareDistance discAdj t 0
        ≤ Real.exp (-(2 * t * 1)) * ((stationaryVec discAdj 0)⁻¹ - 1)) := by
  intro h
  have h2 := h 2 (by norm_num)
  rw [disc_cont_chi2_exact_QA, disc_pi_QA] at h2
  norm_num at h2
  have he : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp one_ne_zero
    norm_num at h
    exact h
  have he2 : Real.exp 1 * Real.exp 1 = Real.exp (2 : ℝ) := by
    rw [← Real.exp_add]
    norm_num
  have he4 : Real.exp (4 : ℝ) = Real.exp 2 * Real.exp 2 := by
    rw [← Real.exp_add]
    norm_num
  have hE4 : (12 : ℝ) < Real.exp 4 := by
    rw [he4]
    have hee : (2 : ℝ) * 2 < Real.exp 2 := by
      rw [← he2]
      nlinarith [he]
    have h16 : ((2 : ℝ) * 2) * ((2 : ℝ) * 2) < Real.exp 2 * Real.exp 2 := by
      nlinarith [hee]
    norm_num at h16 ⊢
    linarith
  have hp4 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have hp12 : (0 : ℝ) < 12 := by norm_num
  have hinve4 : Real.exp (-(4 : ℝ)) < 1/12 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have h1 : (1 : ℝ) / Real.exp 4 < (1 : ℝ) / 12 := by
      rw [div_lt_div_iff₀ hp4 hp12]
      linarith [hE4]
    exact h1
  have hvnn : (0 : ℝ) ≤ 8/3 * Real.exp (-(6 : ℝ)) := by positivity
  linarith [hvnn]

/-! ## Continuous-time mixing time (2026-08-31)

The `t_mix` package's QA (`contMixingTimeFrom`, the certificate
interface, the spectral ceiling, and the TV twins feeding them —
`proposals/continuous-time-chi-square-mixing.md`, Deferred items 1+2
discharged together). On `K₂`: the exact TV value `e^{−2t}/2` (the
continuous ceiling attained at every time, Cauchy–Schwarz equality),
the exact mixing time closed form `t_mix(ε) = ln(1/(2ε))/2` (a `sInf`
pinned exactly, both directions), the ceiling attained exactly at
`ε = e^{−2}/2` (`t_mix = 1 = bound`), the wrong-gap refutation, the
big-`ε` corner `t_mix = 0`, and the antitone instance with its
closed-form consistency pin. On the triangle: the exact TV values
`(2/3)e^{−3t/2}` against the ceiling's `(1/2)√2·e^{−3t/2}` with the
Cauchy–Schwarz slack proved strict, and the `t = 0` join of the
continuous law to the discrete initial law. -/

section ContMixingTime

local notation "k2L" => normalizedLaplacian k2Adj
local notation "k2H" => normalizedLaplacian_symmetric k2Adj k2Adj_isSymm

/-- The second centered mode of the edge: `k2G = (1, −1)`. -/
def k2G : Fin 2 → ℝ := ![1, -1]

theorem k2G_zero : k2G 0 = 1 := by simp [k2G]
theorem k2G_one : k2G 1 = -1 := by simp [k2G]

/-- The conjugated adjacency row on the edge: degree `1` makes the
conjugator the identity, so the row is the adjacency row itself. -/
theorem k2_conj_mulVec_apply (w : Fin 2 → ℝ) (j : Fin 2) :
    (((degreeInvSqrt k2Adj * k2Adj * degreeInvSqrt k2Adj) *ᵥ w) j)
      = ∑ k, k2Adj j k * w k := by
  have hentry : ∀ k : Fin 2,
      (degreeInvSqrt k2Adj * k2Adj * degreeInvSqrt k2Adj) j k
        = k2Adj j k := by
    intro k
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply,
        Fin.sum_univ_two, k2Adj_apply, k2Adj_deg_eq, Real.sqrt_one,
        one_mul, mul_one]
  simp only [Matrix.mulVec, Matrix.dotProduct]
  rw [Finset.sum_congr rfl fun k _ => by rw [hentry k]]

/-- The edge's normalized Laplacian in explicit row form:
`(L_sym *ᵥ w) j = w j − ∑ k, A j k w k`. -/
theorem k2_normalizedLaplacian_mulVec_apply (w : Fin 2 → ℝ) (j : Fin 2) :
    ((normalizedLaplacian k2Adj *ᵥ w) j)
      = w j - ∑ k, k2Adj j k * w k := by
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.sub_apply]
  congr 1
  exact k2_conj_mulVec_apply w j

/-- `k2G` is a `2`-eigenvector of the edge's normalized Laplacian. -/
theorem k2_lapsym_mulVec_k2G : normalizedLaplacian k2Adj *ᵥ k2G
    = (2 : ℝ) • k2G := by
  funext j
  rw [k2_normalizedLaplacian_mulVec_apply k2G j, Pi.smul_apply, smul_eq_mul]
  fin_cases j <;>
    simp only [k2Adj_apply, k2G, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Fin.zero_ne_one, if_false,
      if_true]
  all_goals norm_num

/-- On the edge the conjugator is the identity action: `√D = √1 = 1`. -/
theorem k2_degreeSqrt_mulVec (g : Fin 2 → ℝ) :
    degreeSqrt k2Adj *ᵥ g = g := by
  funext i
  rw [degreeSqrt_mulVec_apply, k2Adj_deg_eq]
  simp

/-- The centered initial density of the edge walk: `h₀ − 1 = (1, −1)`. -/
theorem k2_centered_density : walkDensity k2Adj 0 0 - 1 = k2G := by
  funext i
  fin_cases i
  all_goals simp [walkDensity, walkDistribution_zero, k2_pi_QA,
    Pi.single_apply, k2G]
  all_goals norm_num

/-- The trace of the edge's normalized Laplacian: `1 + 1 = 2`. -/
theorem k2_trace : (normalizedLaplacian k2Adj).trace = 2 := by
  have hz : ∀ j : Fin 2,
      (degreeInvSqrt k2Adj * k2Adj * degreeInvSqrt k2Adj) j j = 0 := by
    intro j
    have h2 : (0 : ℝ) ≤ 1 := by norm_num
    fin_cases j <;>
      simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply,
        Fin.sum_univ_two, k2Adj_apply, k2Adj_deg_eq,
        Real.mul_self_sqrt h2]
  simp [Matrix.trace, normalizedLaplacian, hz]

/-- The edge's normalized spectral gap is exactly `2`: the kernel pin
`evals 0 = 0` plus the trace pin `∑ evals = 2` forces the top entry,
and `secondEval` *is* the middle entry of the sorted list. -/
theorem k2_secondEval_QA : secondEval k2L k2H (by norm_num) = 2 := by
  have h0 : evals k2H (0 : Fin 2) = 0 :=
    normalizedLaplacian_evals_zero k2Adj k2Adj_isSymm k2Adj_nonneg
      k2Adj_deg_pos (by simp)
  have hsum : ∑ k, evals k2H k = 2 := by
    rw [evals_sum_eq_trace k2H, k2_trace]
  have hsum' : ∑ k : Fin 2, evals k2H k = 2 := hsum
  simp only [Fin.sum_univ_two] at hsum'
  have hse : secondEval k2L k2H (by norm_num) = evals k2H (1 : Fin 2) := rfl
  rw [hse]
  linarith

/-- The centered continuous-time density on the edge is the pure
top mode: `h_t − 1 = e^{−2t}·(1, −1)` at every time — through the
conjugation shift (trivial `√D`) and the eigenmode engine. -/
theorem k2_contWalkDensity_sub_one (t : ℝ) :
    contWalkDensity k2Adj t 0 - 1 = Real.exp (-(2 * t)) • k2G := by
  have h1 := degreeSqrt_mulVec_contWalkDensity_sub_one k2Adj k2Adj_deg_pos t 0
  rw [k2_degreeSqrt_mulVec, k2_degreeSqrt_mulVec, k2_centered_density] at h1
  have hmode : normalizedHeatKernel k2Adj t *ᵥ k2G
      = Real.exp (-(2 * t)) • k2G := by
    rw [normalizedHeatKernel]
    refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, k2_lapsym_mulVec_k2G]
    funext i
    rw [Pi.neg_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, smul_eq_mul]
    ring
  rw [hmode] at h1
  exact h1

/-- The continuous-time walk law on the edge, entrywise:
`ν_t(i) = 1/2 ± e^{−2t}/2`. -/
theorem k2_contWalkDistribution_apply (t : ℝ) (i : Fin 2) :
    contWalkDistribution k2Adj t 0 i
      = 1/2 + k2G i * Real.exp (-(2 * t)) / 2 := by
  show stationaryVec k2Adj i * contWalkDensity k2Adj t 0 i
      = 1/2 + k2G i * Real.exp (-(2 * t)) / 2
  rw [k2_pi_QA i]
  have h := congrFun (k2_contWalkDensity_sub_one t) i
  rw [Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul] at h
  have hkey : contWalkDensity k2Adj t 0 i
      = 1 + k2G i * Real.exp (-(2 * t)) := by linarith
  rw [hkey]
  ring

/-- **The exact TV value on the edge at every time**: the continuous
ceiling's constant is attained at every time — `TV(ν_t, π) = e^{−2t}/2`
(the law itself is `((1 ± e^{−2t})/2)`, so every deviation is
`e^{−2t}/2`; Cauchy–Schwarz equality, `|h − 1|` constant). -/
theorem k2_cont_tv_eq (t : ℝ) :
    tvDistance (contWalkDistribution k2Adj t 0) (stationaryVec k2Adj)
      = Real.exp (-(2 * t)) / 2 := by
  have h0 : contWalkDistribution k2Adj t 0 0
      = (1 + Real.exp (-(2 * t))) / 2 := by
    rw [k2_contWalkDistribution_apply t 0, k2G_zero]
    ring
  have h1 : contWalkDistribution k2Adj t 0 1
      = (1 - Real.exp (-(2 * t))) / 2 := by
    rw [k2_contWalkDistribution_apply t 1, k2G_one]
    ring
  have hnn : (0 : ℝ) ≤ Real.exp (-(2 * t)) := Real.exp_nonneg _
  have hpos2 : (0 : ℝ) < Real.exp (-(2 * t)) / 2 :=
    div_pos (Real.exp_pos _) (by norm_num)
  have hneg2 : -(Real.exp (-(2 * t)) / 2) < 0 := neg_lt_zero.mpr hpos2
  rw [tvDistance, Fin.sum_univ_two, h0, h1,
    k2_pi_QA (0 : Fin 2), k2_pi_QA (1 : Fin 2),
    show (1 + Real.exp (-(2 * t))) / 2 - 1/2
        = Real.exp (-(2 * t)) / 2 from by ring,
    show (1 - Real.exp (-(2 * t))) / 2 - 1/2
        = -(Real.exp (-(2 * t)) / 2) from by ring,
    abs_of_nonneg hpos2.le, abs_of_neg hneg2]
  ring

/-- **The ceiling attained at every time on the edge** — the decay-form
TV ceiling with the gap `2` and the constant `√1 = 1` reduces to the
exact value: no slack anywhere in the continuous TV chain on `K₂`. -/
theorem k2_cont_ceiling_attained_QA (t : ℝ) :
    tvDistance (contWalkDistribution k2Adj t 0) (stationaryVec k2Adj)
      = (1/2) * Real.exp (-(t * secondEval k2L k2H (by norm_num)))
        * Real.sqrt ((stationaryVec k2Adj 0)⁻¹ - 1) := by
  rw [k2_secondEval_QA, k2_pi_QA 0, k2_cont_tv_eq]
  have h1 : (1/2 : ℝ) * Real.exp (-(t * 2)) * Real.sqrt ((1/2)⁻¹ - 1)
      = Real.exp (-(2 * t)) / 2 := by
    rw [show ((1/2 : ℝ))⁻¹ - 1 = 1 from by norm_num, Real.sqrt_one,
      show -(t * (2 : ℝ)) = -(2 * t) from by ring]
    ring
  exact h1.symm

/-- **The exact mixing time on the edge** — the closed form every
textbook computes on the two-state chain: `t_mix(ε) = ln(1/(2ε))/2`
for `0 < ε < 1/2`. Both directions: the closed form is a *witness
time* (membership: `TV(s) = e^{−2s}/2` is exactly `ε` there), and it
is a *lower bound* (every witness time `t` has `TV(t) ≤ ε`, i.e.
`t ≥ ln(1/(2ε))/2`). A `sInf` object pinned exactly. -/
theorem k2_contMixingTimeFrom_eq (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1/2) :
    contMixingTimeFrom k2Adj 0 ε = Real.log (1 / (2 * ε)) / 2 := by
  have h2ε : 0 < 2 * ε := by positivity
  have hratio : 1 < 1 / (2 * ε) := (one_lt_div h2ε).mpr (by nlinarith)
  set T : ℝ := Real.log (1 / (2 * ε)) / 2 with hTdef
  have hT0 : 0 ≤ T := div_nonneg
    (Real.log_nonneg (le_of_lt hratio)) (by norm_num)
  have hval : Real.exp (-(2 * T)) = 2 * ε := by
    have h2T : 2 * T = Real.log (1 / (2 * ε)) := by
      rw [hTdef]
      field_simp
    have hposr : (0 : ℝ) < 1 / (2 * ε) := div_pos (by norm_num) h2ε
    rw [h2T, Real.exp_neg, Real.exp_log hposr]
    field_simp
  have hmem : T ∈ {t : ℝ | 0 ≤ t ∧ ∀ s : ℝ, t ≤ s →
      tvDistance (contWalkDistribution k2Adj s 0) (stationaryVec k2Adj)
        ≤ ε} := by
    refine ⟨hT0, fun s hs => ?_⟩
    have hmono : Real.exp (-(2 * s)) ≤ Real.exp (-(2 * T)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [hval] at hmono
    have hstep := k2_cont_tv_eq s
    linarith
  refine le_antisymm ?_ ?_
  · exact (csInf_le (contMixingTimeFrom_bddBelow k2Adj 0 ε) hmem).trans_eq
      (by rw [hTdef])
  · refine le_csInf ⟨T, hmem⟩ ?_
    rintro t ⟨-, ht⟩
    have hTT := ht t (le_refl t)
    rw [k2_cont_tv_eq t] at hTT
    have hlogle : Real.log (Real.exp (-(2 * t))) ≤ Real.log (2 * ε) :=
      Real.log_le_log (Real.exp_pos _) (by linarith)
    rw [Real.log_exp] at hlogle
    have hT' : T = -(Real.log (2 * ε)) / 2 := by
      rw [hTdef, Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt h2ε),
        Real.log_one]
      ring
    linarith

/-- The threshold instance of the closed form: at `ε = e^{−2}/2` the
edge's mixing time is exactly `1` — the time at which the exact TV
value `e^{−2}/2` crosses the threshold. -/
theorem k2_contMixingTimeFrom_exp_eq :
    contMixingTimeFrom k2Adj 0 (Real.exp (-(2 : ℝ)) / 2) = 1 := by
  have hlt : Real.exp (-(2 : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have heps : (0 : ℝ) < Real.exp (-(2 : ℝ)) / 2 :=
    div_pos (Real.exp_pos _) (by norm_num)
  rw [k2_contMixingTimeFrom_eq _ heps (by linarith)]
  have h2 : 2 * (Real.exp (-(2 : ℝ)) / 2) = Real.exp (-(2 : ℝ)) := by
    field_simp
  have hr : 1 / (2 * (Real.exp (-(2 : ℝ)) / 2)) = Real.exp (2 : ℝ) := by
    rw [h2, Real.exp_neg, one_div, inv_inv]
  rw [hr, Real.log_exp]
  norm_num

/-- **The spectral ceiling instance** at the same threshold: the
ceiling's `max 0 (ln(√1/e^{−2})/2)` is exactly `1` — and the closed
form pins `t_mix = 1`, so **the ceiling is attained exactly** on the
fixture (the strongest QA shape a bound theorem can have). -/
theorem k2_contMixingTimeFrom_ceiling_le :
    contMixingTimeFrom k2Adj 0 (Real.exp (-(2 : ℝ)) / 2) ≤ 1 := by
  have heps : (0 : ℝ) < Real.exp (-(2 : ℝ)) / 2 :=
    div_pos (Real.exp_pos _) (by norm_num)
  have h := contMixingTimeFrom_le_of_connected k2Adj k2Adj_isSymm
    k2Adj_nonneg k2Adj_deg_pos (by norm_num) k2_connected heps 0
  have hpi : (stationaryVec k2Adj 0)⁻¹ - 1 = 1 := by
    rw [k2_pi_QA 0]
    norm_num
  have h2 : 2 * (Real.exp (-(2 : ℝ)) / 2) = Real.exp (-(2 : ℝ)) := by
    field_simp
  have hr : Real.sqrt 1 / (2 * (Real.exp (-(2 : ℝ)) / 2))
      = Real.exp (2 : ℝ) := by
    rw [Real.sqrt_one, h2, Real.exp_neg, one_div, inv_inv]
  rw [hpi, hr, Real.log_exp, k2_secondEval_QA] at h
  rwa [max_eq_right (by norm_num : (0 : ℝ) ≤ 2 / 2),
    show (2 : ℝ) / 2 = 1 from by norm_num] at h

/-- **The wrong-gap refutation**: pretending the gap is `3` reads the
ceiling as `t_mix ≤ ln(1/(2ε))/3`, which at `ε = e^{−2}/2` claims
`1 ≤ 2/3` — refuted by the exact pin. The ceiling's gap constant is
load-bearing. -/
theorem k2_contMixingTime_wrong_gap_refuted_QA :
    ¬ (∀ ε : ℝ, 0 < ε → ε < 1/2 →
        contMixingTimeFrom k2Adj 0 ε ≤ Real.log (1 / (2 * ε)) / 3) := by
  intro h
  have hlt : Real.exp (-(2 : ℝ)) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have h1 := h (Real.exp (-(2 : ℝ)) / 2)
    (div_pos (Real.exp_pos _) (by norm_num)) (by linarith)
  rw [k2_contMixingTimeFrom_exp_eq] at h1
  have h2 : 2 * (Real.exp (-(2 : ℝ)) / 2) = Real.exp (-(2 : ℝ)) := by
    field_simp
  have hr : 1 / (2 * (Real.exp (-(2 : ℝ)) / 2)) = Real.exp (2 : ℝ) := by
    rw [h2, Real.exp_neg, one_div, inv_inv]
  rw [hr, Real.log_exp] at h1
  norm_num at h1

/-- **The big-`ε` corner**: at `ε = 3/4` (above the edge's maximal TV
distance `1/2`) the mixing time is exactly `0` — time `0` already
certifies, and no negative time is in the set. Graceful, not junk. -/
theorem k2_contMixingTimeFrom_big_corner :
    contMixingTimeFrom k2Adj 0 (3/4) = 0 := by
  have hmem : (0 : ℝ) ∈ {t : ℝ | 0 ≤ t ∧ ∀ s : ℝ, t ≤ s →
      tvDistance (contWalkDistribution k2Adj s 0) (stationaryVec k2Adj)
        ≤ 3/4} := by
    refine ⟨by norm_num, fun s hs => ?_⟩
    have hstep := k2_cont_tv_eq s
    have hnn : (0 : ℝ) ≤ Real.exp (-(2 * s)) := Real.exp_nonneg _
    have hone : Real.exp (-(2 * s)) ≤ 1 := by
      have h := (Real.exp_le_exp.mpr (by linarith) :
        Real.exp (-(2 * s)) ≤ Real.exp (0 : ℝ))
      rwa [Real.exp_zero] at h
    linarith
  refine le_antisymm ?_ ?_
  · exact csInf_le (contMixingTimeFrom_bddBelow k2Adj 0 (3/4)) hmem
  · exact le_csInf ⟨0, hmem⟩ (fun t ht => ht.1)

/-- **The antitone instance on the edge**: `t_mix(1/4) ≤ t_mix(1/8)`,
through the theorem (the witness supplied by the exact TV
computation). -/
theorem k2_contMixingTimeFrom_anti_QA :
    contMixingTimeFrom k2Adj 0 (1/4) ≤ contMixingTimeFrom k2Adj 0 (1/8) := by
  refine contMixingTimeFrom_anti k2Adj 0 (by norm_num) ?_
  have hT0 : (0 : ℝ) ≤ Real.log (1 / (2 * (1/8 : ℝ))) / 2 :=
    div_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 1 / (2 * (1/8))))
      (by norm_num)
  refine ⟨Real.log (1 / (2 * (1/8 : ℝ))) / 2, hT0, ?_⟩
  intro s hs
  have hmono : Real.exp (-(2 * s))
      ≤ Real.exp (-(2 * (Real.log (1 / (2 * (1/8 : ℝ))) / 2))) :=
    Real.exp_le_exp.mpr (by linarith)
  have hval : Real.exp (-(2 * (Real.log (1 / (2 * (1/8 : ℝ))) / 2)))
      = 2 * (1/8 : ℝ) := by
    have h2T : 2 * (Real.log (1 / (2 * (1/8 : ℝ))) / 2)
        = Real.log (1 / (2 * (1/8 : ℝ))) := by
      rw [show 2 * (Real.log (1 / (2 * (1/8 : ℝ))) / 2)
          = Real.log (1 / (2 * (1/8 : ℝ))) / 2 * 2 from by ring]
      field_simp
    have hposr : (0 : ℝ) < 1 / (2 * (1/8 : ℝ)) := by norm_num
    rw [h2T, Real.exp_neg, Real.exp_log hposr]
    field_simp
  rw [hval] at hmono
  have hstep := k2_cont_tv_eq s
  linarith

/-- **The closed forms beside the antitone instance** (consistency:
the instance reads `ln 2/2 ≤ ln 4/2`, both sides pinned) — the
antitonicity is not vacuous on the fixture. -/
theorem k2_contMixingTimeFrom_values :
    contMixingTimeFrom k2Adj 0 (1/4) = Real.log 2 / 2 ∧
      contMixingTimeFrom k2Adj 0 (1/8) = Real.log 4 / 2 := by
  constructor
  · rw [k2_contMixingTimeFrom_eq _ (by norm_num) (by norm_num)]
    congr 1
    norm_num
  · rw [k2_contMixingTimeFrom_eq _ (by norm_num) (by norm_num)]
    congr 1
    norm_num

/-- On the regular triangle the conjugator is the scalar `√2`:
`√D *ᵥ g = √2 • g`. -/
theorem tri_degreeSqrt_mulVec (g : Fin 3 → ℝ) :
    degreeSqrt triAdj *ᵥ g = Real.sqrt 2 • g := by
  funext i
  rw [degreeSqrt_mulVec_apply, triAdj_deg_eq, Pi.smul_apply, smul_eq_mul]

/-- The centered continuous-time density on the triangle is the pure
`3/2`-mode at every time: `h_t − 1 = e^{−3t/2}·(2, −1, −1)` — the
conjugation shift through the scalar `√2`, the eigenmode engine at
`3/2`. -/
theorem tri_contWalkDensity_sub_one (t : ℝ) :
    contWalkDensity triAdj t 0 - 1 = Real.exp (-(t * (3/2 : ℝ))) • triG := by
  have hc : walkDensity triAdj 0 0 - 1 = triG := tri_centered_density
  have h1 := degreeSqrt_mulVec_contWalkDensity_sub_one triAdj triAdj_deg_pos t 0
  rw [tri_degreeSqrt_mulVec, tri_degreeSqrt_mulVec, hc] at h1
  have hmode : normalizedHeatKernel triAdj t *ᵥ (Real.sqrt 2 • triG)
      = Real.exp (-(t * (3/2 : ℝ))) • (Real.sqrt 2 • triG) := by
    rw [normalizedHeatKernel]
    refine exp_mulVec_eq_smul_of_mulVec_eq_smul _ _ _ ?_
    rw [Matrix.neg_mulVec, Matrix.smul_mulVec_assoc, Matrix.mulVec_smul,
      tri_lapsym_mulVec_triG_QA]
    funext i
    simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hmode] at h1
  funext i
  have h := congrFun h1 i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [← mul_left_comm (Real.sqrt 2) (Real.exp (-(t * (3/2 : ℝ)))) (triG i)] at h
  show contWalkDensity triAdj t 0 i - 1
      = Real.exp (-(t * (3/2 : ℝ))) * triG i
  exact mul_left_cancel₀ (show (Real.sqrt 2 : ℝ) ≠ 0 by norm_num) h

/-- **The exact TV value on the triangle at every time**:
`TV(ν_t, π) = (2/3)·e^{−3t/2}` — the law's deviations are
`e^{−3t/2}(2/3, −1/3, −1/3)`. -/
theorem tri_cont_tv_eq (t : ℝ) :
    tvDistance (contWalkDistribution triAdj t 0) (stationaryVec triAdj)
      = (2/3) * Real.exp (-(t * (3/2 : ℝ))) := by
  have hterm : ∀ i : Fin 3,
      contWalkDistribution triAdj t 0 i - stationaryVec triAdj i
        = Real.exp (-(t * (3/2 : ℝ))) * triG i / 3 := by
    intro i
    have h := congrFun (tri_contWalkDensity_sub_one t) i
    rw [Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul] at h
    have hcd : contWalkDensity triAdj t 0 i
        = 1 + Real.exp (-(t * (3/2 : ℝ))) * triG i := by linarith
    show stationaryVec triAdj i * contWalkDensity triAdj t 0 i
        - stationaryVec triAdj i
      = Real.exp (-(t * (3/2 : ℝ))) * triG i / 3
    rw [tri_pi_QA i, hcd]
    ring
  have habs : ∀ i : Fin 3,
      |contWalkDistribution triAdj t 0 i - stationaryVec triAdj i|
        = (Real.exp (-(t * (3/2 : ℝ))) / 3) * |triG i| := by
    intro i
    rw [hterm i, show Real.exp (-(t * (3/2 : ℝ))) * triG i / 3
        = (Real.exp (-(t * (3/2 : ℝ))) / 3) * triG i from by ring,
      abs_mul, abs_of_nonneg (by positivity)]
  have hsumG : ∑ i, |triG i| = 4 := by
    simp only [triG, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons]
    norm_num
  rw [tvDistance, Finset.sum_congr rfl fun i _ => habs i, ← Finset.mul_sum,
    hsumG]
  ring

/-- **The decay-form ceiling instance on the triangle** at the pinned
gap `3/2`. -/
theorem tri_cont_tv_le (t : ℝ) (ht : 0 ≤ t) :
    tvDistance (contWalkDistribution triAdj t 0) (stationaryVec triAdj)
      ≤ (1/2) * Real.exp (-(t * secondEval triL triH (by norm_num)))
        * Real.sqrt ((stationaryVec triAdj 0)⁻¹ - 1) :=
  contWalkDistribution_tvDistance_le_of_decay triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos (by norm_num) ht 0

/-- **The honest Cauchy–Schwarz slack pinned**: the triangle's exact TV
value `(2/3)e^{−3t/2}` against the ceiling's `(1/2)√2·e^{−3t/2}` —
`(2/3) ≤ √2/2`, strict (equality in the conversion needs `|h − 1|`
constant, which fails on the triangle). -/
theorem tri_cont_tv_slack_QA (t : ℝ) :
    (2/3) * Real.exp (-(t * (3/2 : ℝ)))
      ≤ (1/2) * Real.exp (-(t * secondEval triL triH (by norm_num)))
        * Real.sqrt ((stationaryVec triAdj 0)⁻¹ - 1) := by
  have h23 : (2/3 : ℝ) ≤ (1/2) * Real.sqrt 2 := by
    have h43 : (4/3 : ℝ) ≤ Real.sqrt 2 :=
      Real.le_sqrt_of_sq_le (by norm_num : ((4/3 : ℝ))^2 ≤ 2)
    linarith
  rw [tri_secondEval_QA, tri_pi_QA 0,
    show ((1/3 : ℝ))⁻¹ - 1 = 2 from by norm_num]
  calc (2/3) * Real.exp (-(t * (3/2 : ℝ)))
      ≤ (1/2) * Real.sqrt 2 * Real.exp (-(t * (3/2 : ℝ))) :=
        mul_le_mul_of_nonneg_right h23 (Real.exp_nonneg _)
    _ = (1/2) * Real.exp (-(t * (3/2 : ℝ))) * Real.sqrt 2 := by ring

/-- **The `t = 0` join**: the continuous walk law at time `0` is the
discrete walk's initial law `(1, 0, 0)`, through the theorem and raw. -/
theorem tri_contWalkDistribution_zero_QA :
    contWalkDistribution triAdj 0 0 = ![1, 0, 0] := by
  rw [contWalkDistribution_zero triAdj triAdj_deg_pos 0]
  funext i
  fin_cases i
  all_goals simp [walkDistribution_zero, Pi.single_apply]

end ContMixingTime

/-!
### The Poisson bridge (2026-09-01, `proposals/continuous-time-chi-square-mixing.md`)

The Poissonization identity's and the comparability's QA: the `K₂`
periodic-chain fence (the discrete TV distance is `1/2` at every time —
no discrete mixing certificate exists, and no reverse comparability can
hold), the `t = 0` mixture corner, and the triangle's exact closed forms
(`TV_disc(m) = (2/3)·2^{−m}` by the `triG` eigenroute) with both theorem
instances at `t = 8`, `m = 2`.
-/

section PoissonBridge

/-! ### `K₂`: the periodic chain never mixes in discrete time -/

/-- The `K₂` walk matrix is the swap: `Pᵀ² = 1`. -/
theorem k2_walk_pow_two_QA :
    (walkTransitionMatrix k2Adj)ᵀ ^ 2 = 1 := by
  ext i j
  simp only [pow_two, Matrix.mul_apply, Matrix.transpose_apply,
    walkTransitionMatrix_apply, k2Adj_apply, k2Adj_deg_eq,
    Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> norm_num

/-- The `K₂` law is 2-periodic: `ν_{m+2} = ν_m`. -/
theorem k2_dist_two_step_QA (m : ℕ) :
    walkDistribution k2Adj (m + 2) 0 = walkDistribution k2Adj m 0 := by
  rw [walkDistribution_add k2Adj m 2 0, k2_walk_pow_two_QA,
    Matrix.one_mulVec]

/-- The start point mass as a vector literal. -/
theorem k2_even_law_QA :
    (Pi.single 0 (1 : ℝ) : Fin 2 → ℝ) = ![1, 0] := by
  funext i
  fin_cases i <;> simp [Pi.single_apply]

/-- The even-time laws are the start point mass. -/
theorem k2_dist_even_QA (m : ℕ) :
    walkDistribution k2Adj (2 * m) 0 = ![1, 0] := by
  induction m with
  | zero =>
    rw [Nat.mul_zero, walkDistribution_zero, k2_even_law_QA]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 from (Nat.mul_succ 2 m).symm,
      k2_dist_two_step_QA (2 * m), ih]

/-- One step of the adjoint walk swaps the point masses. -/
theorem k2_swap_law_QA :
    (walkTransitionMatrix k2Adj)ᵀ *ᵥ ![1, 0] = ![0, 1] := by
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, k2Adj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The odd-time laws are the opposite point mass. -/
theorem k2_dist_odd_QA (m : ℕ) :
    walkDistribution k2Adj (2 * m + 1) 0 = ![0, 1] := by
  rw [walkDistribution_add k2Adj (2 * m) 1 0, k2_dist_even_QA m, pow_one,
    k2_swap_law_QA]

/-- **The discrete TV distance on `K₂` is `1/2` at every time** — the
walk oscillates between the two point masses forever. -/
theorem k2_disc_tv_eq_QA (m : ℕ) :
    tvDistance (walkDistribution k2Adj m 0) (stationaryVec k2Adj)
      = 1/2 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, show k + k = 2 * k from (Nat.two_mul k).symm, k2_dist_even_QA k,
      tvDistance]
    norm_num [k2_pi_QA, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, neg_sub, abs_of_neg,
      abs_of_nonneg]
  · rw [hk, k2_dist_odd_QA k, tvDistance]
    norm_num [k2_pi_QA, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, neg_sub, abs_of_neg,
      abs_of_nonneg]

/-- **The periodic-chain fence**: no discrete mixing certificate exists
on `K₂` — the transfer corollary's hypothesis set is empty here at every
threshold below `1/2`. The recorded hazard ("the non-lazy discrete walk
never mixes on periodic chains") as a witness. -/
theorem k2_no_discrete_mixing_QA :
    ¬ ∃ m : ℕ, ∀ k : ℕ, m ≤ k →
      tvDistance (walkDistribution k2Adj k 0) (stationaryVec k2Adj)
        ≤ 1/4 := by
  intro h
  obtain ⟨m, hm⟩ := h
  have hbot := hm m (Nat.le_refl m)
  rw [k2_disc_tv_eq_QA m] at hbot
  norm_num at hbot

/-- **The reverse comparability is dead**: at time `t = 2` the
continuous TV distance is already `e^{−4}/2 < 1/4`, while the discrete
TV distance is `1/2` at *every* time — no function of the continuous TV
distance can bound the discrete one. The comparability's one-sidedness
made a witness. -/
theorem k2_reverse_comparability_QA :
    ∀ m : ℕ,
      tvDistance (contWalkDistribution k2Adj 2 0) (stationaryVec k2Adj)
        + 1/4
        < tvDistance (walkDistribution k2Adj m 0) (stationaryVec k2Adj) := by
  intro m
  have h2e : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have h16 : (16 : ℝ) < Real.exp 4 := by
    have h2e4 : (2 : ℝ) < Real.exp 4 :=
      lt_of_le_of_lt (le_of_lt h2e)
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 4))
    have hp := pow_lt_pow_left₀ h2e (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (4 : ℕ) ≠ 0)
    rw [show ((Real.exp 1 : ℝ)) ^ 4 = Real.exp 4 from by
      rw [← Real.exp_nat_mul]
      ring] at hp
    norm_num at hp
    exact hp
  have hinv : Real.exp (-4) < 1 / 16 := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (Real.exp_pos 4)
      (by norm_num : (0 : ℝ) < 16)).mpr h16
  rw [k2_cont_tv_eq 2, k2_disc_tv_eq_QA m,
    show -(2 * 2) = -(4 : ℝ) from by norm_num]
  linarith

/-- **The `t = 0` corner**: the Poisson mixture collapses to the initial
law — `poissonWeight 0` is the point mass at `k = 0`. -/
theorem k2_poisson_zero_corner_QA :
    (fun i => ∑' k, poissonWeight 0 k * walkDistribution k2Adj k 0 i)
      = walkDistribution k2Adj 0 0 := by
  funext i
  rw [tsum_eq_single 0 (fun k hk => by
    unfold poissonWeight
    rw [zero_pow hk]
    simp)]
  unfold poissonWeight
  norm_num

/-! ### The triangle: exact closed forms and both theorem instances -/

/-- `triG` is a `−1/2`-eigenvector of the triangle walk matrix. -/
theorem tri_walk_eigen_QA :
    walkTransitionMatrix triAdj *ᵥ triG = -(1/2 : ℝ) • triG := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, triG,
      walkTransitionMatrix_apply, triAdj_apply, triAdj_deg_eq] <;>
    norm_num

/-- The walk powers act on `triG` by the geometric factor. -/
theorem tri_pow_mulVec_triG_QA (m : ℕ) :
    (walkTransitionMatrix triAdj ^ m) *ᵥ triG
      = (-(1/2 : ℝ)) ^ m • triG := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul,
      tri_walk_eigen_QA, smul_smul, ← pow_succ]

/-- The centered discrete density at every time: the single decaying
mode with its sign alternation. -/
theorem tri_centered_walkDensity_sub_one_QA (m : ℕ) (i : Fin 3) :
    walkDensity triAdj m 0 i - 1 = (-(1/2 : ℝ)) ^ m * triG i := by
  have h0 : walkDensity triAdj 0 0 - 1 = triG := tri_centered_density
  have h := congrFun (walkDensity_sub_one triAdj triAdj_isSymm
    triAdj_deg_pos m 0) i
  show (walkDensity triAdj m 0 - 1) i = _
  rw [h, h0, tri_pow_mulVec_triG_QA m]
  simp

/-- **The discrete TV closed form on the triangle**:
`TV_disc(m) = (2/3)·2^{−m}` at every time. -/
theorem tri_disc_tv_eq_QA (m : ℕ) :
    tvDistance (walkDistribution triAdj m 0) (stationaryVec triAdj)
      = (2/3) * (1/2 : ℝ) ^ m := by
  have hdev : ∀ i : Fin 3,
      walkDistribution triAdj m 0 i - stationaryVec triAdj i
        = (-(1/2 : ℝ)) ^ m * (triG i / 3) := by
    intro i
    have hπ := tri_pi_QA i
    have hc := tri_centered_walkDensity_sub_one_QA m i
    have hlaw : walkDistribution triAdj m 0 i
        = stationaryVec triAdj i * walkDensity triAdj m 0 i := by
      rw [walkDensity]
      field_simp
    rw [hlaw, hπ,
      show (1 : ℝ) / 3 * walkDensity triAdj m 0 i - 1 / 3
        = 1 / 3 * (walkDensity triAdj m 0 i - 1) from by ring,
      hc]
    ring
  have habs : ∀ i : Fin 3,
      |walkDistribution triAdj m 0 i - stationaryVec triAdj i|
        = (1/2 : ℝ) ^ m * |triG i| / 3 := by
    intro i
    rw [hdev i, abs_mul, abs_pow,
      show |(-(1/2 : ℝ))| = 1/2 from by norm_num, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    ring
  rw [tvDistance, Finset.sum_congr rfl fun i _ => habs i,
    Fin.sum_univ_three]
  have hentries : |triG 0| = 2 ∧ |triG 1| = 1 ∧ |triG 2| = 1 := by
    simp [triG]
  obtain ⟨h0, h1, h2⟩ := hentries
  rw [h0, h1, h2]
  ring

/-- The exact partial Poisson weight the triangle instance consumes:
`∑_{k<2} poissonWeight 8 k = 9·e^{−8}`. -/
theorem tri_poisson_range_two_sum_QA :
    ∑ k in Finset.range 2, poissonWeight 8 k = 9 * Real.exp (-8) := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [poissonWeight]
  ring

/-- **The comparability instance on the triangle** at `t = 8`, `m = 2`,
in closed form: `TV_cont(8) ≤ 9e^{−8} + 1/6`. -/
theorem tri_comparability_closed_QA :
    tvDistance (contWalkDistribution triAdj 8 0) (stationaryVec triAdj)
      ≤ 9 * Real.exp (-8) + 1/6 := by
  have h := contWalkDistribution_tvDistance_add_le triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos (by norm_num : (0 : ℝ) ≤ 8) 2 0
  have h2 : (2/3 : ℝ) * (1/2)^2 = 1/6 := by norm_num
  rw [tri_poisson_range_two_sum_QA, tri_disc_tv_eq_QA 2, h2] at h
  exact h

/-- **Both sides exact, the domination honest**: at the instance's
parameters the continuous TV is exactly `(2/3)e^{−12}` (the delivered
`tri_cont_tv_eq`), the discrete exactly `1/6`, and the comparability's
tail-plus-bound dominates with visible slack. -/
theorem tri_comparability_both_sides_QA :
    tvDistance (contWalkDistribution triAdj 8 0) (stationaryVec triAdj)
        = (2/3) * Real.exp (-12)
      ∧ tvDistance (walkDistribution triAdj 2 0) (stationaryVec triAdj)
        = 1/6
      ∧ (2/3) * Real.exp (-12) ≤ 9 * Real.exp (-8) + 1/6 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [tri_cont_tv_eq 8,
    show -(8 * (3/2 : ℝ)) = -(12 : ℝ) from by norm_num]
  · rw [tri_disc_tv_eq_QA 2]
    norm_num
  · have hmono : Real.exp (-12) ≤ Real.exp (-8) :=
      Real.exp_le_exp.mpr (by norm_num)
    have h1 : Real.exp (-8) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (by norm_num : (-8 : ℝ) ≤ 0)
      rwa [Real.exp_zero] at h
    nlinarith [hmono, h1,
      Real.exp_nonneg (-12), Real.exp_nonneg (-8)]

/-- **The transfer corollary instance on the triangle**: the discrete
certificate `TV_disc(k) ≤ 1/6` for all `k ≥ 2` and the tail bound
`9e^{−8} ≤ 1/24` (from `2 < e`, `e⁸ ≥ 2⁸ = 256 > 216`) give
`TV_cont(8) ≤ 5/24`. -/
theorem tri_mixing_transfer_QA :
    tvDistance (contWalkDistribution triAdj 8 0) (stationaryVec triAdj)
      ≤ 5/24 := by
  have h2e : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have h256 : (256 : ℝ) ≤ Real.exp 8 := by
    have h2e8 : (2 : ℝ) < Real.exp 8 :=
      lt_of_le_of_lt (le_of_lt h2e)
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 8))
    have hp := pow_lt_pow_left₀ h2e (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (8 : ℕ) ≠ 0)
    rw [show ((Real.exp 1 : ℝ)) ^ 8 = Real.exp 8 from by
      rw [← Real.exp_nat_mul]
      ring] at hp
    norm_num at hp
    linarith
  have hfinal :
      tvDistance (contWalkDistribution triAdj 8 0) (stationaryVec triAdj)
        ≤ 1/6 + 1/24 := by
    refine contWalkDistribution_tvDistance_le_of_discreteMixing triAdj
      triAdj_isSymm triAdj_nonneg triAdj_deg_pos
      (by norm_num : (0 : ℝ) ≤ 8) 2 0 (ε₁ := 1/6) (ε₂ := 1/24) ?_ ?_
    · intro k hk
      rw [tri_disc_tv_eq_QA k]
      have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
        norm_num at hp
        exact hp
      have hpos : (0 : ℝ) < (2 : ℝ) ^ k :=
        pow_pos (by norm_num : (0 : ℝ) < 2) k
      have hinv : (1/2 : ℝ) ^ k = 1 / ((2 : ℝ) ^ k) :=
        _root_.one_div_pow 2 k
      have hkey : (1 : ℝ) / ((2 : ℝ) ^ k) ≤ 1 / 4 :=
        (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 4)).mpr h4
      rw [hinv]
      linarith
    · rw [tri_poisson_range_two_sum_QA, Real.exp_neg, ← one_div,
        ← div_eq_mul_one_div, div_le_iff₀ (Real.exp_pos 8)]
      linarith
  linarith

/-- **The anti-monotonicity instance**: the discrete TV decreases from
`2` to `3` on the triangle (strictly: `1/6 → 1/12`). -/
theorem tri_tv_anti_QA :
    tvDistance (walkDistribution triAdj 3 0) (stationaryVec triAdj)
      ≤ tvDistance (walkDistribution triAdj 2 0) (stationaryVec triAdj)
      ∧ tvDistance (walkDistribution triAdj 3 0) (stationaryVec triAdj)
        = 1/12 := by
  refine ⟨?_, by rw [tri_disc_tv_eq_QA 3]; norm_num⟩
  have h := walkDistribution_tvDistance_anti triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos 2 1 0
  have h3 : 2 + 1 = 3 := rfl
  rwa [h3] at h

end PoissonBridge

section DiscMixingTime

/-! ### The exact closed forms on the triangle -/

/-- The triangle's witness arithmetic at threshold `1/3`: from time `1`
on, `TV ≤ (2/3)·2^{−s} ≤ 1/3` — the reusable `2^s` domination pattern. -/
theorem tri_mix_le_third_cert_QA :
    ∀ s : ℕ, 1 ≤ s →
      tvDistance (walkDistribution triAdj s 0) (stationaryVec triAdj)
        ≤ 1/3 := by
  intro s hs
  rw [tri_disc_tv_eq_QA s]
  have h2 : (2 : ℝ) ≤ (2 : ℝ)^s := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs
    norm_num at hp
    exact hp
  have hpos : (0 : ℝ) < (2 : ℝ)^s := pow_pos (by norm_num) s
  have hinv : (1/2 : ℝ)^s = 1 / ((2 : ℝ)^s) := _root_.one_div_pow 2 s
  have hkey : (1 : ℝ) / ((2 : ℝ)^s) ≤ 1/2 :=
    (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 2)).mpr h2
  rw [hinv]
  calc (2/3 : ℝ) * (1 / ((2 : ℝ)^s)) ≤ (2/3) * (1/2) :=
        mul_le_mul_of_nonneg_left hkey (by norm_num)
    _ = 1/3 := by norm_num

/-- **The exact mixing-time closed form `t_mix(1/3) = 1`** — the `sInf`
pinned in both directions: the certificate interface gives `≤ 1`, and
the attainment specification at `s = 0` refutes `0` (the true value
`TV(0) = 2/3` exceeds `1/3`). Both interfaces load-bearing on the
object's exact shape. -/
theorem tri_mix_eq_third_QA :
    walkMixingTimeFrom triAdj 0 (1/3) = 1 := by
  have hle : walkMixingTimeFrom triAdj 0 (1/3) ≤ 1 :=
    walkMixingTimeFrom_le_of_cert triAdj 0 1 tri_mix_le_third_cert_QA
  by_contra hne
  have hzero : walkMixingTimeFrom triAdj 0 (1/3) = 0 := by omega
  have hspec := walkMixingTimeFrom_spec triAdj 0 (ε := 1/3)
    ⟨1, tri_mix_le_third_cert_QA⟩ 0 (by omega)
  rw [tri_disc_tv_eq_QA 0] at hspec
  norm_num at hspec

/-- **The exact mixing-time closed form `t_mix(1/6) = 2`** — the same
two-direction pin at the transfer corollary's own working threshold:
`TV(2) = 1/6` attains the threshold exactly, `TV(1) = 1/3` refutes `1`. -/
theorem tri_mix_eq_sixth_QA :
    walkMixingTimeFrom triAdj 0 (1/6) = 2 := by
  have hcert : ∀ s : ℕ, 2 ≤ s →
      tvDistance (walkDistribution triAdj s 0) (stationaryVec triAdj)
        ≤ 1/6 := by
    intro s hs
    rw [tri_disc_tv_eq_QA s]
    have h4 : (4 : ℝ) ≤ (2 : ℝ)^s := by
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs
      norm_num at hp
      exact hp
    have hpos : (0 : ℝ) < (2 : ℝ)^s := pow_pos (by norm_num) s
    have hinv : (1/2 : ℝ)^s = 1 / ((2 : ℝ)^s) := _root_.one_div_pow 2 s
    have hkey : (1 : ℝ) / ((2 : ℝ)^s) ≤ 1/4 :=
      (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 4)).mpr h4
    rw [hinv]
    nlinarith
  have hle : walkMixingTimeFrom triAdj 0 (1/6) ≤ 2 :=
    walkMixingTimeFrom_le_of_cert triAdj 0 2 hcert
  by_contra hne
  have hlt : walkMixingTimeFrom triAdj 0 (1/6) < 2 := by omega
  have hspec := walkMixingTimeFrom_spec triAdj 0 (ε := 1/6)
    ⟨2, hcert⟩ 1 (by omega)
  rw [tri_tv_one_eq_QA] at hspec
  norm_num at hspec

/-- **The exact mixing-time closed form `t_mix(1/12) = 3`** — the third
pin, for the antitone instance below. -/
theorem tri_mix_eq_twelfth_QA :
    walkMixingTimeFrom triAdj 0 (1/12) = 3 := by
  have hcert : ∀ s : ℕ, 3 ≤ s →
      tvDistance (walkDistribution triAdj s 0) (stationaryVec triAdj)
        ≤ 1/12 := by
    intro s hs
    rw [tri_disc_tv_eq_QA s]
    have h8 : (8 : ℝ) ≤ (2 : ℝ)^s := by
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs
      norm_num at hp
      exact hp
    have hpos : (0 : ℝ) < (2 : ℝ)^s := pow_pos (by norm_num) s
    have hinv : (1/2 : ℝ)^s = 1 / ((2 : ℝ)^s) := _root_.one_div_pow 2 s
    have hkey : (1 : ℝ) / ((2 : ℝ)^s) ≤ 1/8 :=
      (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 8)).mpr h8
    rw [hinv]
    nlinarith
  have hle : walkMixingTimeFrom triAdj 0 (1/12) ≤ 3 :=
    walkMixingTimeFrom_le_of_cert triAdj 0 3 hcert
  by_contra hne
  have hlt : walkMixingTimeFrom triAdj 0 (1/12) < 3 := by omega
  have hspec := walkMixingTimeFrom_spec triAdj 0 (ε := 1/12)
    ⟨3, hcert⟩ 2 (by omega)
  rw [tri_tv_two_eq_QA] at hspec
  norm_num at hspec

/-- **The antitone instance with exact values**: `1/12 ≤ 1/6` gives
`t_mix(1/6) = 2 ≤ 3 = t_mix(1/12)` — the field-standard monotonicity
pinned at closed forms on both sides. -/
theorem tri_mix_anti_QA :
    walkMixingTimeFrom triAdj 0 (1/6)
      ≤ walkMixingTimeFrom triAdj 0 (1/12) := by
  have h := walkMixingTimeFrom_anti triAdj 0 (ε := 1/12) (δ := 1/6)
    (by norm_num) ⟨3, by
      intro s hs
      rw [tri_disc_tv_eq_QA s]
      have h8 : (8 : ℝ) ≤ (2 : ℝ)^s := by
        have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs
        norm_num at hp
        exact hp
      have hpos : (0 : ℝ) < (2 : ℝ)^s := pow_pos (by norm_num) s
      have hinv : (1/2 : ℝ)^s = 1 / ((2 : ℝ)^s) := _root_.one_div_pow 2 s
      have hkey : (1 : ℝ) / ((2 : ℝ)^s) ≤ 1/8 :=
        (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 8)).mpr h8
      rw [hinv]
      nlinarith⟩
  rw [tri_mix_eq_sixth_QA, tri_mix_eq_twelfth_QA] at h ⊢
  exact h

/-! ### The ceiling: attained exactly, and computed with slack -/

/-- **The ceiling attained exactly**: on the triangle at rate `1/2` and
`ε = √2/4`, the object is `1` and the ceiling's own right side
evaluates to `1` — no slack anywhere in the package. (The threshold
ratio `√C/(2ε) = √2/(√2/2) = 2` sits exactly at the power of `2` the
rate certificate names.) -/
theorem tri_mix_ceiling_attained_QA :
    walkMixingTimeFrom triAdj 0 (Real.sqrt 2 / 4) = 1
      ∧ Nat.ceil (Real.log ((Real.sqrt 2 : ℝ) / (2 * (Real.sqrt 2 / 4)))
          / Real.log (1 / (1/2))) = 1 := by
  have hpi : (stationaryVec triAdj 0)⁻¹ - 1 = 2 := by
    rw [tri_pi_QA 0]
    norm_num
  have hratio : (Real.sqrt 2 : ℝ) / (2 * (Real.sqrt 2 / 4)) = 2 := by
    refine (div_eq_iff (by
      exact ne_of_gt (by positivity))).mpr ?_
    ring
  have hone : (1 : ℝ) / (1/2) = 2 := by norm_num
  -- the ceiling bound at this fixture: RHS = Nat.ceil (log 2 / log 2)
  have hRHS : Nat.ceil (Real.log ((Real.sqrt 2 : ℝ) / (2 * (Real.sqrt 2 / 4)))
      / Real.log (1 / (1/2))) = 1 := by
    have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    have hdiv : Real.log ((2 : ℝ)) / Real.log (2 : ℝ) = 1 :=
      div_self hlog2
    have heq : Real.log ((Real.sqrt 2 : ℝ) / (2 * (Real.sqrt 2 / 4)))
        / Real.log (1 / (1/2 : ℝ)) = 1 := by
      rw [hratio, hone, hdiv]
    rw [heq]
    norm_num
  -- the object: ≤ 1 by the ceiling, ≠ 0 by attainment at s = 0
  have hcert : ∀ s : ℕ, 1 ≤ s →
      tvDistance (walkDistribution triAdj s 0) (stationaryVec triAdj)
        ≤ Real.sqrt 2 / 4 := by
    intro s hs
    have h1 := tri_mix_le_third_cert_QA s hs
    have h34 : (1/3 : ℝ) ≤ Real.sqrt 2 / 4 := by
      have hsq : ((4/3 : ℝ))^2 ≤ 2 := by norm_num
      have h43 : (4/3 : ℝ) ≤ Real.sqrt 2 := Real.le_sqrt_of_sq_le hsq
      linarith
    exact le_trans h1 h34
  have hceil := walkMixingTimeFrom_le_of_connected triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (Real.sqrt 2 / 4)
    (by norm_num) (by norm_num) (by positivity) tri_rate_QA 0
  rw [hpi, hRHS] at hceil
  refine ⟨?_, hRHS⟩
  by_contra hne
  have hzero : walkMixingTimeFrom triAdj 0 (Real.sqrt 2 / 4) = 0 := by omega
  have hspec := walkMixingTimeFrom_spec triAdj 0 (ε := Real.sqrt 2 / 4)
    ⟨1, hcert⟩ 0 (by omega)
  rw [tri_disc_tv_eq_QA 0] at hspec
  norm_num at hspec
  linarith [sqrt_two_le_two_QA]

/-- **The ceiling computed with honest slack**: at the working threshold
`ε = 1/6` the ceiling's right side evaluates to exactly `3` against the
true `t_mix = 2` — one wasted step, the price of the Cauchy–Schwarz
conversion's slack on the triangle. -/
theorem tri_mix_ceiling_slack_QA :
    Nat.ceil (Real.log ((Real.sqrt 2 : ℝ) / (2 * (1/6 : ℝ)))
      / Real.log (1 / (1/2 : ℝ))) = 3
      ∧ walkMixingTimeFrom triAdj 0 (1/6) = 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : (Real.sqrt 2 : ℝ) / (2 * (1/6 : ℝ)) = 3 * Real.sqrt 2 := by
    refine (div_eq_iff (by norm_num)).mpr ?_
    ring
  have hone : (1 : ℝ) / (1/2) = 2 := by norm_num
  have hlog4 : Real.log ((4 : ℝ)) = 2 * Real.log 2 := by
    rw [show ((4 : ℝ)) = (2 : ℝ) * (2 : ℝ) from by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hlog8 : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
    rw [show ((8 : ℝ)) = (2 : ℝ) * (2 : ℝ) * (2 : ℝ) from by norm_num,
      Real.log_mul (by norm_num : ((2 : ℝ) * (2 : ℝ)) ≠ 0)
        (by norm_num : (2 : ℝ) ≠ 0),
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  -- 3√2 ≤ 8
  have hup : (3 : ℝ) * Real.sqrt 2 ≤ 8 := by
    nlinarith [sqrt_two_le_two_QA, Real.sqrt_nonneg (2 : ℝ)]
  have hle : Real.log ((3 : ℝ) * Real.sqrt 2) / Real.log 2
      ≤ (3 : ℝ) := by
    rw [div_le_iff₀ hlog2, ← hlog8]
    exact Real.log_le_log (by positivity) hup
  -- 4 < 3√2
  have h43 : (4/3 : ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hdown : (2 : ℝ) * Real.log 2
      < Real.log ((3 : ℝ) * Real.sqrt 2) := by
    rw [← hlog4]
    exact Real.log_lt_log (by norm_num : (0 : ℝ) < 4)
      (by nlinarith [h43, Real.sqrt_nonneg (2 : ℝ)])
  -- the two log facts in the shape the ceiling needs
  have hxle : Real.log ((Real.sqrt 2 : ℝ) / (2 * (1/6 : ℝ)))
      / Real.log (1 / (1/2 : ℝ)) ≤ (3 : ℝ) := by
    rw [hratio, hone]
    exact hle
  have hltx : (2 : ℝ) < Real.log ((Real.sqrt 2 : ℝ) / (2 * (1/6 : ℝ)))
      / Real.log (1 / (1/2 : ℝ)) := by
    rw [hratio, hone]
    exact (lt_div_iff₀ hlog2).mpr hdown
  refine ⟨?_, tri_mix_eq_sixth_QA⟩
  have h2lt : (2 : ℕ) < Nat.ceil (Real.log ((Real.sqrt 2 : ℝ)
      / (2 * (1/6 : ℝ))) / Real.log (1 / (1/2 : ℝ))) :=
    Nat.lt_ceil.mpr hltx
  have hle3 : Nat.ceil (Real.log ((Real.sqrt 2 : ℝ) / (2 * (1/6 : ℝ)))
      / Real.log (1 / (1/2 : ℝ))) ≤ 3 :=
    Nat.ceil_le.mpr hxle
  omega

/-! ### The `K₂` periodicity fence at the object level -/

/-- **The junk corner pinned**: on the periodic chain `K₂` at
`ε = 1/4` no witness time exists (`k2_no_discrete_mixing_QA`), so the
object's defining set is empty and `sInf ∅ = 0` on `ℕ` — the value
*looks* anti-conservative ("mixes instantly"), and this is exactly why
every consumer carries hypotheses that exclude the corner: the ceiling's
`0 < r < 1` rate certificate is undischargeable on `K₂` (the edge's
normalized gap is `2`, forcing `r ≥ 1`). The fence is the proof that
the junk corner is fenced, not inhabited. -/
theorem k2_mix_junk_corner_QA :
    walkMixingTimeFrom k2Adj 0 (1/4) = 0 := by
  have hempty : {t : ℕ | ∀ s : ℕ, t ≤ s →
      tvDistance (walkDistribution k2Adj s 0) (stationaryVec k2Adj)
        ≤ 1/4} = ∅ := by
    refine Set.eq_empty_iff_forall_not_mem.mpr ?_
    intro t ht
    exact k2_no_discrete_mixing_QA ⟨t, ht⟩
  rw [walkMixingTimeFrom, hempty, Nat.sInf_empty]

/-! ### The bridge: the transfer corollary through the object -/

/-- **The bridge instance** — the same bound the hand-certified
`tri_mixing_transfer_QA` derives (`TV_cont(8) ≤ 5/24`), now through the
discrete `t_mix` object: the caller supplies only the Poisson lower-tail
bound, the discrete certificate `hmix` is the object's own attainment
(`t_mix(1/6) = 2`, discharged internally from the rate certificate and
the ceiling). -/
theorem tri_bridge_mix_QA :
    tvDistance (contWalkDistribution triAdj 8 0) (stationaryVec triAdj)
      ≤ 5/24 := by
  have h2e : (2 : ℝ) < Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have h256 : (256 : ℝ) ≤ Real.exp 8 := by
    have h2e8 : (2 : ℝ) < Real.exp 8 :=
      lt_of_le_of_lt (le_of_lt h2e)
        (Real.exp_lt_exp.mpr (by norm_num : (1 : ℝ) < 8))
    have hp := pow_lt_pow_left₀ h2e (by norm_num : (0 : ℝ) ≤ 2)
      (by norm_num : (8 : ℕ) ≠ 0)
    rw [show ((Real.exp 1 : ℝ)) ^ 8 = Real.exp 8 from by
      rw [← Real.exp_nat_mul]
      ring] at hp
    norm_num at hp
    linarith
  have hfinal :
      tvDistance (contWalkDistribution triAdj 8 0) (stationaryVec triAdj)
        ≤ 1/6 + 1/24 := by
    refine contWalkDistribution_tvDistance_le_of_walkMixingTime triAdj
      triAdj_isSymm triAdj_nonneg triAdj_deg_pos tri_connected (1/2)
      (by norm_num) (by norm_num) tri_rate_QA (by norm_num) 0
      (by norm_num : (0 : ℝ) ≤ 8) ?_
    rw [tri_mix_eq_sixth_QA, tri_poisson_range_two_sum_QA,
      Real.exp_neg, ← one_div, ← div_eq_mul_one_div,
      div_le_iff₀ (Real.exp_pos 8)]
    linarith
  linarith

end DiscMixingTime

section SpectralFloorQA

/-! ### The `K₂` exact-attainment family: certified non-mixing on the periodic chain -/

/-- The conjugated test function on `K₂` is the eigenvector itself
(degrees `1`, so `1/√D = 1`). -/
theorem k2_conj_f_QA :
    degreeInvSqrt k2Adj *ᵥ k2G = k2G := by
  funext i
  rw [degreeInvSqrt_mulVec_apply, k2Adj_deg_eq]
  simp [k2G]

/-- The exact law-level evolution instantiated at `K₂`'s nontrivial
mode: pairing the law against `(1/√D) • k2G` reads `(-1)^m` at every
time — the sign alternation itself, theorem-mediated, with the
initial pairing `⟨ν₀, k2G⟩ = 1` pinned by the point-mass law. -/
theorem k2_evolution_QA (m : ℕ) :
    walkDistribution k2Adj m 0 ⬝ᵥ (degreeInvSqrt k2Adj *ᵥ k2G)
      = (-1 : ℝ) ^ m * 1 := by
  rw [walkDistribution_dotProduct_degreeInvSqrt_of_eigenpair k2Adj
    k2Adj_isSymm k2Adj_deg_pos m 0 k2_lapsym_mulVec_k2G,
    show (1:ℝ) - 2 = -1 from by norm_num, walkDistribution_zero,
    Matrix.dotProduct_comm, Matrix.dotProduct_single, k2_conj_f_QA,
    k2G_zero, mul_one]

/-- The floor instance on `K₂` at `c = 1`: `(1/2)·|1−2|^m·|k2G 0|/1`
is *at most* the TV distance — the theorem. -/
theorem k2_tv_floor_le_QA (m : ℕ) :
    (1/2) * |1 - 2| ^ m * |(degreeInvSqrt k2Adj *ᵥ k2G) 0| / 1
      ≤ tvDistance (walkDistribution k2Adj m 0) (stationaryVec k2Adj) :=
  walkDistribution_tvDistance_ge_of_eigenpair k2Adj k2Adj_isSymm
    k2Adj_deg_pos m 0 k2_lapsym_mulVec_k2G (by norm_num)
    (c := 1) (fun y => by
      rw [k2_conj_f_QA]
      fin_cases y <;> simp [k2G]) (by norm_num)

/-- **The TV floor is attained exactly at every time on `K₂`**: the
floor value is `1/2` and so is the TV distance (the pinned closed
form) — certified non-mixing, tight forever, on the chain where no
`r < 1` ceiling can reach. -/
theorem k2_tv_floor_attained_QA (m : ℕ) :
    (1/2) * |1 - 2| ^ m * |(degreeInvSqrt k2Adj *ᵥ k2G) 0| / 1
      = tvDistance (walkDistribution k2Adj m 0) (stationaryVec k2Adj) := by
  rw [k2_conj_f_QA, k2G_zero, k2_disc_tv_eq_QA]
  norm_num

/-- The χ² closed form on `K₂`: constant `1` at every time (the
alternating point masses both sit at χ²-distance `1`). -/
theorem k2_chi2_all_QA (m : ℕ) :
    chiSquareDistance k2Adj m 0 = 1 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, show k + k = 2 * k from by omega]
    simp only [chiSquareDistance, k2_dist_even_QA, k2_pi_QA,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    norm_num
  · rw [hk]
    simp only [chiSquareDistance, k2_dist_odd_QA, k2_pi_QA,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    norm_num

/-- The χ² floor instance on `K₂`. -/
theorem k2_chi2_floor_le_QA (m : ℕ) :
    (1 - 2) ^ (2 * m) * (k2G 0) ^ 2
      / (stationaryVec k2Adj 0 * (k2G ⬝ᵥ k2G))
      ≤ chiSquareDistance k2Adj m 0 :=
  chiSquareDistance_ge_of_eigenpair k2Adj k2Adj_isSymm k2Adj_deg_pos m 0
    k2_lapsym_mulVec_k2G (by norm_num)
    (by intro h; have h0 := congrFun h 0; simp [k2G] at h0)

/-- **The χ² floor is attained exactly at every time on `K₂`**: both
sides read `1` — the periodic chain pinned at non-mixing from below
and above. -/
theorem k2_chi2_floor_attained_QA (m : ℕ) :
    (1 - 2) ^ (2 * m) * (k2G 0) ^ 2
      / (stationaryVec k2Adj 0 * (k2G ⬝ᵥ k2G))
      = chiSquareDistance k2Adj m 0 := by
  rw [k2_chi2_all_QA, k2G_zero, k2_pi_QA (0 : Fin 2)]
  have hnorm : k2G ⬝ᵥ k2G = 2 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two, k2G]
    norm_num
  rw [hnorm]
  norm_num

/-- **The gate's witness-existence hypothesis is load-bearing**: on
`K₂` at threshold `1/4` no witness time exists (TV is `1/2` at every
time), so the floor gate cannot fire — and the junk-corner `t_mix = 0`
(`k2_mix_junk_corner_QA`'s mechanism) makes every strict floor
statement false there. The negation is proved, not assumed. -/
theorem k2_mix_gate_hwit_fence_QA :
    ¬ ∃ T : ℕ, ∀ s : ℕ, T ≤ s →
      tvDistance (walkDistribution k2Adj s 0) (stationaryVec k2Adj)
        ≤ 1/4 := by
  intro h
  obtain ⟨T, hT⟩ := h
  have hself := hT T (le_refl T)
  rw [k2_disc_tv_eq_QA T] at hself
  norm_num at hself

/-! ### The triangle: exact floors at the `triG` eigenpair -/

/-- The conjugated test function on the triangle: `triG/√2`. -/
noncomputable def triF : Fin 3 → ℝ :=
  degreeInvSqrt triAdj *ᵥ triG

theorem triF_zero : triF 0 = 2 * (Real.sqrt 2)⁻¹ := by
  rw [triF, degreeInvSqrt_mulVec_apply, triAdj_deg_eq]
  simp only [triG, Matrix.cons_val_zero, Matrix.head_cons]
  ring

theorem triF_abs_le (j : Fin 3) : |triF j| ≤ 2 * (Real.sqrt 2)⁻¹ := by
  have hpos : (0:ℝ) < (Real.sqrt 2)⁻¹ := by positivity
  rw [triF, degreeInvSqrt_mulVec_apply, triAdj_deg_eq, abs_mul,
    abs_of_pos hpos]
  fin_cases j
  all_goals simp only [triG, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  all_goals norm_num
  all_goals linarith [hpos]

/-- The exact evolution at the triangle's `3/2` mode, theorem-mediated. -/
theorem tri_evolution_QA (m : ℕ) :
    walkDistribution triAdj m 0 ⬝ᵥ triF
      = (-(1/2 : ℝ)) ^ m * (2 * (Real.sqrt 2)⁻¹) := by
  rw [triF, walkDistribution_dotProduct_degreeInvSqrt_of_eigenpair
    triAdj triAdj_isSymm triAdj_deg_pos m 0 tri_lapsym_mulVec_triG_QA,
    show (1:ℝ) - 3/2 = -(1/2) from by norm_num, walkDistribution_zero,
    Matrix.dotProduct_comm, Matrix.dotProduct_single,
    degreeInvSqrt_mulVec_apply, triAdj_deg_eq]
  simp only [triG, Matrix.cons_val_zero, Matrix.head_cons]
  ring

/-- The TV floor instance on the triangle at `c = 2/√2`. -/
theorem tri_tv_floor_le_QA (m : ℕ) :
    (1/2) * |1 - 3/2| ^ m * |triF 0| / (2 * (Real.sqrt 2)⁻¹)
      ≤ tvDistance (walkDistribution triAdj m 0) (stationaryVec triAdj) :=
  walkDistribution_tvDistance_ge_of_eigenpair triAdj triAdj_isSymm
    triAdj_deg_pos m 0 tri_lapsym_mulVec_triG_QA (by norm_num)
    (c := 2 * (Real.sqrt 2)⁻¹) triF_abs_le (by positivity)

/-- **The floor value and the truth, side by side**: the floor reads
`(1/2)^(m+1)` — `|triF 0|` exactly attains the sup bound — against
the pinned closed form `TV = (2/3)·2^{−m}`; the slack is honest and
strict at every time. -/
theorem tri_tv_floor_value_QA (m : ℕ) :
    (1/2) * |1 - 3/2| ^ m * |triF 0| / (2 * (Real.sqrt 2)⁻¹)
      = (1/2) ^ (m + 1)
      ∧ (1/2) ^ (m + 1)
        < tvDistance (walkDistribution triAdj m 0)
            (stationaryVec triAdj) := by
  have hne : (2:ℝ) * (Real.sqrt 2)⁻¹ ≠ 0 :=
    mul_ne_zero two_ne_zero
      (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)))
  have hab : |1 - (3/2:ℝ)| = 1/2 := by norm_num
  have hf : |triF 0| = 2 * (Real.sqrt 2)⁻¹ := by
    rw [triF_zero, abs_of_pos (by positivity)]
  refine ⟨?_, ?_⟩
  · have hcancel : (1/2:ℝ) * (1/2) ^ m * (2 * (Real.sqrt 2)⁻¹)
          / (2 * (Real.sqrt 2)⁻¹) = (1/2) * (1/2) ^ m := by
      field_simp
      ring
    rw [hf, hab, hcancel, pow_succ]
    ring
  · rw [tri_disc_tv_eq_QA m,
      show (1/2:ℝ) ^ (m + 1) = (1/2) ^ m * (1/2) from by
        rw [pow_succ]]
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) m]

/-- The χ² closed form on the triangle at every time. -/
theorem tri_chi2_all_QA (m : ℕ) :
    chiSquareDistance triAdj m 0 = 2 * (1/2) ^ (2 * m) := by
  rw [chiSquareDistance_eq_sum_smul triAdj triAdj_deg_pos m 0]
  have hdev : ∀ i : Fin 3,
      stationaryVec triAdj i * (walkDensity triAdj m 0 i - 1) ^ 2
      = (1/2:ℝ) ^ (2 * m) * (stationaryVec triAdj i * (triG i)^2) := by
    intro i
    have hsign : ((-(1/2:ℝ)) ^ m) ^ 2 = (1/2:ℝ) ^ (2 * m) := by
      have h1 : ((-(1/2:ℝ)) ^ m) ^ 2 = (-(1/2:ℝ)) ^ (m * 2) := by
        rw [← pow_mul]
      have h2 : (-(1/2:ℝ)) ^ (m * 2) = (-(1/2:ℝ)) ^ (2 * m) := by
        congr 1
        omega
      have h3 : (-(1/2:ℝ)) ^ (2 * m) = (1/2:ℝ) ^ (2 * m) := by
        rw [pow_mul, pow_mul]
        norm_num
      rw [h1, h2, h3]
    rw [tri_centered_walkDensity_sub_one_QA m i, mul_pow, hsign]
    ring
  rw [Finset.sum_congr rfl fun i _ => hdev i, ← Finset.mul_sum,
    tri_l2_zero_QA, mul_comm (2:ℝ)]

/-- The χ² floor instance on the triangle. -/
theorem tri_chi2_floor_le_QA (m : ℕ) :
    (1 - 3/2) ^ (2 * m) * (triG 0) ^ 2
      / (stationaryVec triAdj 0 * (triG ⬝ᵥ triG))
      ≤ chiSquareDistance triAdj m 0 :=
  chiSquareDistance_ge_of_eigenpair triAdj triAdj_isSymm triAdj_deg_pos
    m 0 tri_lapsym_mulVec_triG_QA (by norm_num)
    (by intro h; have h0 := congrFun h 0; simp [triG] at h0)

/-- **The χ² floor is attained exactly at every time on the triangle**:
the floor value is `2·(1/4)^m` — so is the truth (the centered
density from vertex `0` is a pure `3/2`-mode, and the floor at that
mode captures all the mass). Load-bearing on the eigenpair constant:
a wrong conjugation would miss the exact value. -/
theorem tri_chi2_floor_attained_QA (m : ℕ) :
    (1 - 3/2) ^ (2 * m) * (triG 0) ^ 2
      / (stationaryVec triAdj 0 * (triG ⬝ᵥ triG))
      = chiSquareDistance triAdj m 0 := by
  have hnorm : triG ⬝ᵥ triG = 6 := by
    simp [Matrix.dotProduct, Fin.sum_univ_three, triG]
    norm_num
  have h0 : triG 0 = 2 := by simp [triG]
  have hsign : (1 - 3/2) ^ (2 * m) = (1/2:ℝ) ^ (2 * m) := by
    rw [show (1:ℝ) - 3/2 = -(1/2) from by norm_num, pow_mul, pow_mul]
    congr 1
    norm_num
  rw [tri_chi2_all_QA, h0, hnorm, tri_pi_QA (0 : Fin 3), hsign]
  field_simp
  ring

/-! ### The mixing-time floor: exact at all three pinned thresholds -/

/-- The depth-`3` certificate (the witness-existence input the floor
theorems consume; one cert serves all three thresholds by
monotonicity `1/12 ≤ 1/6 ≤ 1/3`). -/
theorem tri_mix_cert_QA :
    ∀ s : ℕ, 3 ≤ s →
      tvDistance (walkDistribution triAdj s 0) (stationaryVec triAdj)
        ≤ 1/12 := by
  intro s hs
  rw [tri_disc_tv_eq_QA s]
  have h8 : (8 : ℝ) ≤ (2 : ℝ)^s := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs
    norm_num at hp
    exact hp
  have hpos : (0 : ℝ) < (2 : ℝ)^s := pow_pos (by norm_num) s
  have hinv : (1/2 : ℝ)^s = 1 / ((2 : ℝ)^s) := _root_.one_div_pow 2 s
  have hkey : (1 : ℝ) / ((2 : ℝ)^s) ≤ 1/8 :=
    (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 8)).mpr h8
  rw [hinv]
  nlinarith

theorem tri_floor_thr_third :
    Real.log (|triF 0| / (2 * (1/3) * (2 * (Real.sqrt 2)⁻¹)))
      / Real.log (1 / |1 - 3/2|)
      = Real.log (3/2) / Real.log 2 := by
  rw [triF_zero, abs_of_pos (by positivity),
    show |1 - (3/2:ℝ)| = 1/2 from by norm_num]
  have hne : (2 : ℝ) * (Real.sqrt 2)⁻¹ ≠ 0 := by positivity
  have hrw : (2 : ℝ) * (Real.sqrt 2)⁻¹
      / (2 * (1/3) * (2 * (Real.sqrt 2)⁻¹)) = 3/2 := by
    field_simp
    ring
  rw [hrw, show (1:ℝ) / (1/2) = 2 from by norm_num]

theorem tri_floor_thr_sixth :
    Real.log (|triF 0| / (2 * (1/6) * (2 * (Real.sqrt 2)⁻¹)))
      / Real.log (1 / |1 - 3/2|)
      = Real.log 3 / Real.log 2 := by
  rw [triF_zero, abs_of_pos (by positivity),
    show |1 - (3/2:ℝ)| = 1/2 from by norm_num]
  have hne : (2 : ℝ) * (Real.sqrt 2)⁻¹ ≠ 0 := by positivity
  have hrw : (2 : ℝ) * (Real.sqrt 2)⁻¹
      / (2 * (1/6) * (2 * (Real.sqrt 2)⁻¹)) = 3 := by
    field_simp
    ring
  rw [hrw, show (1:ℝ) / (1/2) = 2 from by norm_num]

theorem tri_floor_thr_twelfth :
    Real.log (|triF 0| / (2 * (1/12) * (2 * (Real.sqrt 2)⁻¹)))
      / Real.log (1 / |1 - 3/2|)
      = Real.log 6 / Real.log 2 := by
  rw [triF_zero, abs_of_pos (by positivity),
    show |1 - (3/2:ℝ)| = 1/2 from by norm_num]
  have hne : (2 : ℝ) * (Real.sqrt 2)⁻¹ ≠ 0 := by positivity
  have hrw : (2 : ℝ) * (Real.sqrt 2)⁻¹
      / (2 * (1/12) * (2 * (Real.sqrt 2)⁻¹)) = 6 := by
    field_simp
    ring
  rw [hrw, show (1:ℝ) / (1/2) = 2 from by norm_num]

/-- **The floor is attained exactly at `ε = 1/3`**: the spectral floor
theorem gives `⌈L⌉ ≤ t_mix`, the pinned closed form gives
`t_mix = 1`, and `0 < log(3/2)/log 2 ≤ 1` gives `⌈L⌉ = 1`. -/
theorem tri_abs_halves : |1 - (3/2 : ℝ)| = 1/2 := by norm_num

theorem triF_zero_ne : triF 0 ≠ 0 := by
  rw [triF_zero]
  exact mul_ne_zero two_ne_zero
    (inv_ne_zero (Real.sqrt_ne_zero'.mpr (by norm_num)))

theorem tri_conj_eigvec_zero_ne : (degreeInvSqrt triAdj *ᵥ triG) 0 ≠ 0 := by
  rw [show (degreeInvSqrt triAdj *ᵥ triG) 0 = triF 0 from rfl]
  exact triF_zero_ne

theorem tri_rate_abs_pos : 0 < |1 - (3/2 : ℝ)| := by
  rw [tri_abs_halves]
  norm_num

theorem tri_rate_abs_lt : |1 - (3/2 : ℝ)| < 1 := by
  rw [tri_abs_halves]
  norm_num

theorem tri_mix_floor_third_attained_QA :
    Nat.ceil (Real.log (|triF 0| / (2 * (1/3) * (2 * (Real.sqrt 2)⁻¹)))
        / Real.log (1 / |1 - 3/2|))
      = walkMixingTimeFrom triAdj 0 (1/3) := by
  have hle : Nat.ceil (Real.log (|triF 0|
        / (2 * (1/3) * (2 * (Real.sqrt 2)⁻¹)))
        / Real.log (1 / |1 - 3/2|))
      ≤ walkMixingTimeFrom triAdj 0 (1/3) :=
    walkMixingTimeFrom_ge_of_eigenpair triAdj triAdj_isSymm
      triAdj_deg_pos (by norm_num) 0 tri_lapsym_mulVec_triG_QA
      (by norm_num)
      (c := 2 * (Real.sqrt 2)⁻¹) triF_abs_le (by positivity)
      tri_conj_eigvec_zero_ne tri_rate_abs_pos tri_rate_abs_lt
      ⟨1, tri_mix_le_third_cert_QA⟩
  rw [tri_floor_thr_third, tri_mix_eq_third_QA]
  rw [tri_floor_thr_third] at hle
  rw [tri_mix_eq_third_QA] at hle
  have hlog2 : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hlog32 : 0 < Real.log (3/2) := by
    apply Real.log_pos
    norm_num
  have hlow : 0 < Real.log (3/2) / Real.log 2 :=
    div_pos hlog32 hlog2
  have hhigh : Real.log (3/2) / Real.log 2 ≤ 1 := by
    rw [div_le_iff₀ hlog2, one_mul]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h1 : 1 ≤ Nat.ceil (Real.log (3/2) / Real.log 2) := by
    have := (Nat.ceil_pos).mpr hlow
    omega
  have h2 : Nat.ceil (Real.log (3/2) / Real.log 2) ≤ 1 :=
    Nat.ceil_le.mpr (by exact_mod_cast hhigh)
  exact le_antisymm h2 h1

theorem tri_mix_floor_sixth_attained_QA :
    Nat.ceil (Real.log (|triF 0| / (2 * (1/6) * (2 * (Real.sqrt 2)⁻¹)))
        / Real.log (1 / |1 - 3/2|))
      = walkMixingTimeFrom triAdj 0 (1/6) := by
  have hle : Nat.ceil (Real.log (|triF 0|
        / (2 * (1/6) * (2 * (Real.sqrt 2)⁻¹)))
        / Real.log (1 / |1 - 3/2|))
      ≤ walkMixingTimeFrom triAdj 0 (1/6) :=
    walkMixingTimeFrom_ge_of_eigenpair triAdj triAdj_isSymm
      triAdj_deg_pos (by norm_num) 0 tri_lapsym_mulVec_triG_QA
      (by norm_num)
      (c := 2 * (Real.sqrt 2)⁻¹) triF_abs_le (by positivity)
      tri_conj_eigvec_zero_ne tri_rate_abs_pos tri_rate_abs_lt
      ⟨3, fun s hs => le_trans (tri_mix_cert_QA s hs) (by norm_num)⟩
  rw [tri_floor_thr_sixth, tri_mix_eq_sixth_QA]
  rw [tri_floor_thr_sixth] at hle
  rw [tri_mix_eq_sixth_QA] at hle
  have hlog2 : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hlow : 1 < Real.log 3 / Real.log 2 := by
    rw [lt_div_iff₀ hlog2, one_mul]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hhigh : Real.log 3 / Real.log 2 ≤ 2 := by
    rw [div_le_iff₀ hlog2]
    have h3 : Real.log ((2:ℝ)^2) = (2:ℝ) * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    rw [← h3]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hge : 2 ≤ Nat.ceil (Real.log 3 / Real.log 2) := by
    have hc := Nat.le_ceil (Real.log 3 / Real.log 2)
    have hlt : (1:ℝ) < ((Nat.ceil (Real.log 3 / Real.log 2) : ℕ) : ℝ) :=
      lt_of_lt_of_le hlow hc
    have hnat : (1:ℕ) < Nat.ceil (Real.log 3 / Real.log 2) := by
      exact_mod_cast hlt
    omega
  have h2 : Nat.ceil (Real.log 3 / Real.log 2) ≤ 2 :=
    Nat.ceil_le.mpr (by exact_mod_cast hhigh)
  exact le_antisymm h2 hge

theorem tri_mix_floor_twelfth_attained_QA :
    Nat.ceil (Real.log (|triF 0| / (2 * (1/12) * (2 * (Real.sqrt 2)⁻¹)))
        / Real.log (1 / |1 - 3/2|))
      = walkMixingTimeFrom triAdj 0 (1/12) := by
  have hle : Nat.ceil (Real.log (|triF 0|
        / (2 * (1/12) * (2 * (Real.sqrt 2)⁻¹)))
        / Real.log (1 / |1 - 3/2|))
      ≤ walkMixingTimeFrom triAdj 0 (1/12) :=
    walkMixingTimeFrom_ge_of_eigenpair triAdj triAdj_isSymm
      triAdj_deg_pos (by norm_num) 0 tri_lapsym_mulVec_triG_QA
      (by norm_num)
      (c := 2 * (Real.sqrt 2)⁻¹) triF_abs_le (by positivity)
      tri_conj_eigvec_zero_ne tri_rate_abs_pos tri_rate_abs_lt
      ⟨3, tri_mix_cert_QA⟩
  rw [tri_floor_thr_twelfth, tri_mix_eq_twelfth_QA]
  rw [tri_floor_thr_twelfth] at hle
  rw [tri_mix_eq_twelfth_QA] at hle
  have hlog2 : 0 < Real.log 2 := by
    apply Real.log_pos
    norm_num
  have hlow : 2 < Real.log 6 / Real.log 2 := by
    rw [lt_div_iff₀ hlog2]
    have h4 : Real.log ((2:ℝ)^2) = (2:ℝ) * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    rw [← h4]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hhigh : Real.log 6 / Real.log 2 ≤ 3 := by
    rw [div_le_iff₀ hlog2]
    have h8 : Real.log ((2:ℝ)^3) = (3:ℝ) * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    rw [← h8]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h3 : 3 ≤ Nat.ceil (Real.log 6 / Real.log 2) := by
    have hc := Nat.le_ceil (Real.log 6 / Real.log 2)
    have hkey : (2:ℝ) < ((Nat.ceil (Real.log 6 / Real.log 2) : ℕ) : ℝ) :=
      lt_of_lt_of_le hlow hc
    have hnat : (2:ℕ) < Nat.ceil (Real.log 6 / Real.log 2) := by
      exact_mod_cast hkey
    omega
  have h4 : Nat.ceil (Real.log 6 / Real.log 2) ≤ 3 :=
    Nat.ceil_le.mpr (by exact_mod_cast hhigh)
  exact le_antisymm h4 h3

/-! ### The kernel-mode fences -/

/-- **The χ² floor's `μ ≠ 0` hypothesis is load-bearing**: at the
kernel eigenpair `(0, ![1,1,1])` — a genuine eigenpair — every other
ingredient is satisfiable, and the dropped-hypothesis statement reads
`1 ≤ χ²(2)` against the pinned `χ²(2) = 1/8`. -/
theorem tri_floor_kernel_refuted_QA :
    ¬ ((1 - (0:ℝ)) ^ (2 * 2) * ((![1, 1, 1] : Fin 3 → ℝ) 0) ^ 2
      / (stationaryVec triAdj 0
          * ((![1, 1, 1] : Fin 3 → ℝ) ⬝ᵥ (![1, 1, 1] : Fin 3 → ℝ)))
      ≤ chiSquareDistance triAdj 2 0) := by
  intro h
  have hpair : ((![1, 1, 1] : Fin 3 → ℝ) ⬝ᵥ (![1, 1, 1] : Fin 3 → ℝ))
      = 3 := by
    simp [Matrix.dotProduct, Fin.sum_univ_three]
    norm_num
  rw [tri_pi_QA (0 : Fin 3), hpair, tri_chi2_two_QA] at h
  simp only [Matrix.cons_val_zero, Matrix.head_cons] at h
  norm_num at h

/-- **The TV floor's `μ ≠ 0` hypothesis is load-bearing**, the same
fence in total-variation form: the dropped-hypothesis statement reads
`1/2 ≤ TV(2)` against the pinned `TV(2) = 1/6`. -/
theorem tri_floor_kernel_tv_refuted_QA :
    ¬ ((1/2) * |1 - (0:ℝ)| ^ 2
        * |(degreeInvSqrt triAdj *ᵥ (![1, 1, 1] : Fin 3 → ℝ)) 0|
        / ((Real.sqrt 2)⁻¹)
      ≤ tvDistance (walkDistribution triAdj 2 0) (stationaryVec triAdj)) := by
  intro h
  have hf : (degreeInvSqrt triAdj *ᵥ (![1, 1, 1] : Fin 3 → ℝ)) 0
      = (Real.sqrt 2)⁻¹ := by
    rw [degreeInvSqrt_mulVec_apply, triAdj_deg_eq]
    simp
  have hnn : (0:ℝ) < (Real.sqrt 2)⁻¹ := by positivity
  rw [hf, tri_tv_two_eq_QA, sub_zero, abs_of_pos (by norm_num), one_pow,
    abs_of_pos hnn] at h
  have hval : (1/2:ℝ) * 1 * (Real.sqrt 2)⁻¹ / (Real.sqrt 2)⁻¹ = 1/2 := by
    field_simp
    ring
  rw [hval] at h
  norm_num at h

end SpectralFloorQA
section UniformMixing

/-! ### The triangle's walk-law pins from the other starts -/

/-- The one-step law from vertex `1`: `(1/2, 0, 1/2)`. -/
theorem tri_dist_one_one_QA :
    walkDistribution triAdj 1 1 = ![1/2, 0, 1/2] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, Pi.single_apply]

/-- The two-step law from vertex `1`: `(1/4, 1/2, 1/4)`. -/
theorem tri_dist_two_one_QA :
    walkDistribution triAdj 2 1 = ![1/4, 1/2, 1/4] := by
  rw [walkDistribution_succ, tri_dist_one_one_QA]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- The one-step law from vertex `2`: `(1/2, 1/2, 0)`. -/
theorem tri_dist_one_two_QA :
    walkDistribution triAdj 1 2 = ![1/2, 1/2, 0] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three, Pi.single_apply]

/-- The two-step law from vertex `2`: `(1/4, 1/4, 1/2)`. -/
theorem tri_dist_two_two_QA :
    walkDistribution triAdj 2 2 = ![1/4, 1/4, 1/2] := by
  rw [walkDistribution_succ, tri_dist_one_two_QA]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, triAdj_deg_eq, triAdj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- The one-step law from vertex `1` on the edge: `(1, 0)`. -/
theorem k2_dist_one_one_QA :
    walkDistribution k2Adj 1 1 = ![1, 0] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, k2Adj_deg_eq, k2Adj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, Pi.single_apply]

/-! ### The distance pins -/

/-- Every start pair's TV distance at `t = 1` is at most `1/2` — the
sup bound's per-pair engine (`omega`'s `Fin` support supplies the
numeral case split; `norm_num` then computes from the raw law
literals). -/
theorem tri_pair_tv_one_le_QA : ∀ (a b : Fin 3),
    tvDistance (walkDistribution triAdj 1 a) (walkDistribution triAdj 1 b)
      ≤ 1/2 := by
  intro a b
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with h | h | h <;> rw [h]
  all_goals rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with h | h | h <;>
    rw [h]
  all_goals norm_num [tri_dist_one_QA, tri_dist_one_one_QA,
    tri_dist_one_two_QA, tvDistance, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, neg_sub, abs_of_neg, abs_of_nonneg]

/-- **`d(1) = 1/2` on the triangle** — the two-start distance's sup
over the nine start pairs, pinned from the raw law literals (the six
off-diagonal pairs each `(1/2)^1`, the diagonal `0`). -/
theorem tri_pair_one_eq_QA : walkTVPair triAdj 1 = 1/2 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0, 1), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 3 × Fin 3)).Nonempty)
      (f := fun p : Fin 3 × Fin 3 =>
        tvDistance (walkDistribution triAdj 1 p.1)
          (walkDistribution triAdj 1 p.2))
      fun p _ => tri_pair_tv_one_le_QA p.1 p.2
  · have h0 : (1/2 : ℝ) = tvDistance (walkDistribution triAdj 1 0)
          (walkDistribution triAdj 1 1) := by
      rw [tri_dist_one_QA, tri_dist_one_one_QA, tvDistance]
      norm_num [Fin.sum_univ_three, neg_sub, abs_of_neg, abs_of_nonneg]
    rw [h0]
    exact Finset.le_sup'
      (f := fun p : Fin 3 × Fin 3 =>
        tvDistance (walkDistribution triAdj 1 p.1)
          (walkDistribution triAdj 1 p.2))
      (Finset.mem_univ (0, 1))

/-- Every start pair's TV distance at `t = 2` is at most `1/4`. -/
theorem tri_pair_tv_two_le_QA : ∀ (a b : Fin 3),
    tvDistance (walkDistribution triAdj 2 a) (walkDistribution triAdj 2 b)
      ≤ 1/4 := by
  intro a b
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by omega) with h | h | h <;> rw [h]
  all_goals rcases (show b = 0 ∨ b = 1 ∨ b = 2 by omega) with h | h | h <;>
    rw [h]
  all_goals norm_num [tri_dist_two_QA, tri_dist_two_one_QA,
    tri_dist_two_two_QA, tvDistance, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, neg_sub, abs_of_neg, abs_of_nonneg]

/-- **`d(2) = 1/4` on the triangle** — the same pin at `t = 2`. -/
theorem tri_pair_two_eq_QA : walkTVPair triAdj 2 = 1/4 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0, 1), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 3 × Fin 3)).Nonempty)
      (f := fun p : Fin 3 × Fin 3 =>
        tvDistance (walkDistribution triAdj 2 p.1)
          (walkDistribution triAdj 2 p.2))
      fun p _ => tri_pair_tv_two_le_QA p.1 p.2
  · have h0 : (1/4 : ℝ) = tvDistance (walkDistribution triAdj 2 0)
          (walkDistribution triAdj 2 1) := by
      rw [tri_dist_two_QA, tri_dist_two_one_QA, tvDistance]
      norm_num [Fin.sum_univ_three, neg_sub, abs_of_neg, abs_of_nonneg]
    rw [h0]
    exact Finset.le_sup'
      (f := fun p : Fin 3 × Fin 3 =>
        tvDistance (walkDistribution triAdj 2 p.1)
          (walkDistribution triAdj 2 p.2))
      (Finset.mem_univ (0, 1))

/-- Every start's TV distance to stationarity at `t = 1` is at most
`1/3`. -/
theorem tri_unif_tv_one_le_QA : ∀ (x : Fin 3),
    tvDistance (walkDistribution triAdj 1 x) (stationaryVec triAdj)
      ≤ 1/3 := by
  intro x
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 by omega) with h | h | h <;> rw [h]
  all_goals norm_num [tri_dist_one_QA, tri_dist_one_one_QA,
    tri_dist_one_two_QA, tri_pi_QA, tvDistance, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, neg_sub, abs_of_neg, abs_of_nonneg]

/-- **`d̄(1) = 1/3` on the triangle** — the worst-start distance's sup
over the three starts, each `1/3` by the vertex-transitive symmetry
here witnessed by raw law arithmetic. -/
theorem tri_unif_one_eq_QA : walkTVUniform triAdj 1 = 1/3 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0 : Fin 3), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 3)).Nonempty)
      (f := fun x : Fin 3 =>
        tvDistance (walkDistribution triAdj 1 x) (stationaryVec triAdj))
      fun x _ => tri_unif_tv_one_le_QA x
  · have h0 : (1/3 : ℝ) = tvDistance (walkDistribution triAdj 1 0)
          (stationaryVec triAdj) := by
      rw [tri_dist_one_QA, tvDistance]
      norm_num [tri_pi_QA, Fin.sum_univ_three, neg_sub, abs_of_neg,
        abs_of_nonneg]
    rw [h0]
    exact Finset.le_sup'
      (f := fun x : Fin 3 =>
        tvDistance (walkDistribution triAdj 1 x) (stationaryVec triAdj))
      (Finset.mem_univ 0)

/-- Every start's TV distance to stationarity at `t = 2` is at most
`1/6`. -/
theorem tri_unif_tv_two_le_QA : ∀ (x : Fin 3),
    tvDistance (walkDistribution triAdj 2 x) (stationaryVec triAdj)
      ≤ 1/6 := by
  intro x
  rcases (show x = 0 ∨ x = 1 ∨ x = 2 by omega) with h | h | h <;> rw [h]
  all_goals norm_num [tri_dist_two_QA, tri_dist_two_one_QA,
    tri_dist_two_two_QA, tri_pi_QA, tvDistance, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, neg_sub, abs_of_neg, abs_of_nonneg]

/-- **`d̄(2) = 1/6` on the triangle** — the same pin at `t = 2`. -/
theorem tri_unif_two_eq_QA : walkTVUniform triAdj 2 = 1/6 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0 : Fin 3), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 3)).Nonempty)
      (f := fun x : Fin 3 =>
        tvDistance (walkDistribution triAdj 2 x) (stationaryVec triAdj))
      fun x _ => tri_unif_tv_two_le_QA x
  · have h0 : (1/6 : ℝ) = tvDistance (walkDistribution triAdj 2 0)
          (stationaryVec triAdj) := by
      rw [tri_dist_two_QA, tvDistance]
      norm_num [tri_pi_QA, Fin.sum_univ_three, neg_sub, abs_of_neg,
        abs_of_nonneg]
    rw [h0]
    exact Finset.le_sup'
      (f := fun x : Fin 3 =>
        tvDistance (walkDistribution triAdj 2 x) (stationaryVec triAdj))
      (Finset.mem_univ 0)

/-! ### The theorem instances: every statement tight at the fixture -/

/-- The uniform `1/3` certificate: from time `1` on, every start's TV
distance is at most `1/3` — per-start monotonicity below the pinned
`d̄(1) = 1/3`. -/
theorem tri_unif_third_cert_QA : ∀ s : ℕ, 1 ≤ s → ∀ x : Fin 3,
    tvDistance (walkDistribution triAdj s x) (stationaryVec triAdj)
      ≤ 1/3 := by
  intro s hs x
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hs
  have h1 : tvDistance (walkDistribution triAdj 1 x)
      (stationaryVec triAdj) ≤ 1/3 := by
    have hsup := Finset.le_sup'
      (f := fun y : Fin 3 =>
        tvDistance (walkDistribution triAdj 1 y) (stationaryVec triAdj))
      (Finset.mem_univ x)
    exact le_trans hsup (le_of_eq tri_unif_one_eq_QA)
  rw [hj]
  exact le_trans
    (walkDistribution_tvDistance_anti triAdj triAdj_isSymm triAdj_nonneg
      triAdj_deg_pos 1 j x) h1

/-- The uniform `1/6` certificate: from time `2` on, every start's TV
distance is at most `1/6` — per-start monotonicity below the pinned
`d̄(2) = 1/6`. -/
theorem tri_unif_sixth_cert_QA : ∀ s : ℕ, 2 ≤ s → ∀ x : Fin 3,
    tvDistance (walkDistribution triAdj s x) (stationaryVec triAdj)
      ≤ 1/6 := by
  intro s hs x
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hs
  have h2 : tvDistance (walkDistribution triAdj 2 x)
      (stationaryVec triAdj) ≤ 1/6 := by
    have hsup := Finset.le_sup'
      (f := fun y : Fin 3 =>
        tvDistance (walkDistribution triAdj 2 y) (stationaryVec triAdj))
      (Finset.mem_univ x)
    exact le_trans hsup (le_of_eq tri_unif_two_eq_QA)
  rw [hj]
  exact le_trans
    (walkDistribution_tvDistance_anti triAdj triAdj_isSymm triAdj_nonneg
      triAdj_deg_pos 2 j x) h2

/-- **Submultiplicativity attained with equality** on the triangle at
`(s, t) = (1, 1)`: `d(2) = 1/4 = (1/2) · (1/2) = d(1) · d(1)` — no
slack anywhere in the package (the sharp Dobrushin constant
load-bearing: a factor-`2` statement would read `1/4 ≤ 1/2`). -/
theorem tri_pair_submul_tight_QA :
    walkTVPair triAdj 2 = walkTVPair triAdj 1 * walkTVPair triAdj 1 := by
  have hinst := walkTVPair_submul triAdj triAdj_deg_pos 1 1
  rw [show 1 + 1 = 2 from rfl] at hinst
  rw [tri_pair_two_eq_QA, tri_pair_one_eq_QA] at hinst ⊢
  linarith

/-- **The mixed submultiplicativity attained with equality** on the
triangle at `(s, t) = (1, 1)`: `d̄(2) = 1/6 = (1/3) · (1/2) =
d̄(1) · d(1)`. -/
theorem tri_unif_submul_tight_QA :
    walkTVUniform triAdj 2
      = walkTVUniform triAdj 1 * walkTVPair triAdj 1 := by
  have hinst := walkTVUniform_mul_walkTVPair_le triAdj triAdj_isSymm
    triAdj_deg_pos 1 1
  rw [show 1 + 1 = 2 from rfl] at hinst
  rw [tri_unif_two_eq_QA, tri_unif_one_eq_QA, tri_pair_one_eq_QA]
    at hinst ⊢
  norm_num

/-- **The escalation engine attained with equality** on the triangle
at `k = 1`, `t₀ = 1`: `d̄(2·1) = 1/6 = (1/3) · (1/2)¹ = d̄(1) · d(1)¹`. -/
theorem tri_escalation_tight_QA :
    walkTVUniform triAdj ((1 + 1) * 1)
      = walkTVUniform triAdj 1 * (walkTVPair triAdj 1) ^ 1 := by
  have hinst := walkTVUniform_succ_mul_le triAdj triAdj_isSymm
    triAdj_deg_pos 1 1
  rw [tri_unif_two_eq_QA, tri_unif_one_eq_QA, tri_pair_one_eq_QA]
    at hinst ⊢
  norm_num

/-- **`d̄ ≤ d` with honest slack witnessed** on the triangle at
`t = 1`: `1/3 ≤ 1/2`, both sides pinned independently. -/
theorem tri_unif_le_pair_QA : walkTVUniform triAdj 1 ≤ walkTVPair triAdj 1 :=
  walkTVUniform_le_walkTVPair triAdj triAdj_isSymm triAdj_deg_pos 1

/-- **The uniform object's exact closed form `t_mix(1/3) = 1`** —
pinned in both directions: the escalation certificate gives `≤`
(`d̄(1) = ε₀ = 1/3`, `d(1) = ρ = 1/2`, `ε₀ · ρ⁰ ≤ 1/3`), and the
per-start pin `t_mix^0(1/3) = 1` gives `≥` through the domination. -/
theorem tri_mix_uniform_eq_third_QA :
    walkMixingTime triAdj (1/3) = 1 := by
  have hle : walkMixingTime triAdj (1/3) ≤ (0 + 1) * 1 := by
    refine walkMixingTime_le_mul_of_escalation (ε := 1/3) (ε₀ := 1/3)
      (ρ := 1/2) triAdj triAdj_isSymm triAdj_nonneg triAdj_deg_pos 1 0
      ?_ ?_ ?_
    · rw [tri_unif_one_eq_QA]
    · rw [tri_pair_one_eq_QA]
    · norm_num
  have hge : walkMixingTimeFrom triAdj 0 (1/3)
      ≤ walkMixingTime triAdj (1/3) :=
    walkMixingTimeFrom_le_walkMixingTime triAdj 0 ⟨1, tri_unif_third_cert_QA⟩
  rw [tri_mix_eq_third_QA] at hge
  omega

/-- **The uniform object's exact closed form `t_mix(1/6) = 2`** — the
escalation certificate closes *exactly at the truth*: `≤ 2` from
`d̄(1) = 1/3`, `d(1) = 1/2`, `k = 1` (`(1/3) · (1/2)¹ ≤ 1/6`), `≥ 2`
from the per-start pin at the same threshold. -/
theorem tri_mix_uniform_eq_sixth_QA :
    walkMixingTime triAdj (1/6) = 2 := by
  have hle : walkMixingTime triAdj (1/6) ≤ (1 + 1) * 1 := by
    refine walkMixingTime_le_mul_of_escalation (ε := 1/6) (ε₀ := 1/3)
      (ρ := 1/2) triAdj triAdj_isSymm triAdj_nonneg triAdj_deg_pos 1 1
      ?_ ?_ ?_
    · rw [tri_unif_one_eq_QA]
    · rw [tri_pair_one_eq_QA]
    · norm_num
  have hge : walkMixingTimeFrom triAdj 0 (1/6)
      ≤ walkMixingTime triAdj (1/6) :=
    walkMixingTimeFrom_le_walkMixingTime triAdj 0 ⟨2, tri_unif_sixth_cert_QA⟩
  rw [tri_mix_eq_sixth_QA] at hge
  omega

/-- **The uniform object is the worst start's per-start object** — the
finite-sup interchange instantiated structurally at the triangle's
`1/6` threshold, the escalation supplying the witness. -/
theorem tri_uniform_eq_sup_QA :
    walkMixingTime triAdj (1/6)
      = (Finset.univ : Finset (Fin 3)).sup'
        (⟨0, Finset.mem_univ _⟩ :
          (Finset.univ : Finset (Fin 3)).Nonempty)
        (fun x => walkMixingTimeFrom triAdj x (1/6)) := by
  refine walkMixingTime_eq_sup_walkMixingTimeFrom triAdj ⟨2, ?_⟩
  exact tri_unif_sixth_cert_QA

/-- **The uniform spectral ceiling on the triangle** at `ε = 1/6`:
with `C = 2` (every start's `(π x)⁻¹ − 1 = 2`), the ceiling is the
same display as the per-start pinned ceiling at the same threshold
(the uniform `t_mix = 2 ≤ ⌈·⌉` with honest slack). -/
theorem tri_uniform_ceiling_QA :
    walkMixingTime triAdj (1/6)
      ≤ Nat.ceil (Real.log (Real.sqrt 2 / (2 * (1/6 : ℝ)))
          / Real.log (1 / (1/2 : ℝ))) := by
  refine walkMixingTime_le_of_connected triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos tri_connected (1/2) (1/6)
    (by norm_num) (by norm_num) (by norm_num) tri_rate_QA 2 ?_
  intro x
  rw [tri_pi_QA x]
  norm_num

/-! ### The `K₂` corner: periodicity at the uniform object -/

/-- Every start pair's TV distance at `t = 1` is at most `1`. -/
theorem k2_pair_tv_one_le_QA : ∀ (a b : Fin 2),
    tvDistance (walkDistribution k2Adj 1 a) (walkDistribution k2Adj 1 b)
      ≤ 1 := by
  intro a b
  rcases (show a = 0 ∨ a = 1 by omega) with h | h <;> rw [h]
  all_goals rcases (show b = 0 ∨ b = 1 by omega) with h | h <;> rw [h]
  all_goals norm_num [k2_dist_one_QA, k2_dist_one_one_QA, tvDistance,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, neg_sub, abs_of_neg, abs_of_nonneg]

/-- **`d(1) = 1` on the edge** — the two-start distance is maximal at
every time (the two laws sit on opposite vertices), so no escalation
certificate `ρ < 1` exists: submultiplicativity degenerates to
`1 ≤ 1 · 1`. -/
theorem k2_pair_one_eq_QA : walkTVPair k2Adj 1 = 1 := by
  refine le_antisymm ?_ ?_
  · refine Finset.sup'_le
      (⟨(0, 1), Finset.mem_univ _⟩ :
        (Finset.univ : Finset (Fin 2 × Fin 2)).Nonempty)
      (f := fun p : Fin 2 × Fin 2 =>
        tvDistance (walkDistribution k2Adj 1 p.1)
          (walkDistribution k2Adj 1 p.2))
      fun p _ => k2_pair_tv_one_le_QA p.1 p.2
  · have h0 : (1 : ℝ) = tvDistance (walkDistribution k2Adj 1 0)
          (walkDistribution k2Adj 1 1) := by
      rw [k2_dist_one_QA, k2_dist_one_one_QA, tvDistance]
      norm_num [Fin.sum_univ_two, neg_sub, abs_of_neg, abs_of_nonneg]
    rw [h0]
    exact Finset.le_sup'
      (f := fun p : Fin 2 × Fin 2 =>
        tvDistance (walkDistribution k2Adj 1 p.1)
          (walkDistribution k2Adj 1 p.2))
      (Finset.mem_univ (0, 1))

/-- **No uniform mixing witness exists on the edge** — the periodic
chain's TV distance to stationarity is `1/2` at every time from the
start that has moved, so no time dominates *all* starts' distances
below `1/4`: the uniform object's witness set is empty. -/
theorem k2_no_uniform_mixing_QA :
    ¬ ∃ T : ℕ, ∀ s : ℕ, T ≤ s → ∀ x : Fin 2,
      tvDistance (walkDistribution k2Adj s x) (stationaryVec k2Adj)
        ≤ 1/4 := by
  intro h
  obtain ⟨T, hT⟩ := h
  exact k2_no_discrete_mixing_QA ⟨T, fun s hs => hT s hs 0⟩

/-- **The uniform junk corner pinned**: at the unreachable threshold
`1/4`, the edge's uniform mixing time is the empty-set infimum `0` —
anti-conservative-looking, and *exactly* why every theorem above
carries a witness or a `ρ < 1` certificate (fenced by
`k2_no_uniform_mixing_QA`). -/
theorem k2_mix_uniform_junk_QA :
    walkMixingTime k2Adj (1/4) = 0 := by
  have hempty : {t : ℕ | ∀ s : ℕ, t ≤ s → ∀ x : Fin 2,
      tvDistance (walkDistribution k2Adj s x) (stationaryVec k2Adj)
        ≤ 1/4} = ∅ :=
    Set.eq_empty_iff_forall_not_mem.mpr (by
      rintro t ht
      exact k2_no_uniform_mixing_QA ⟨t, ht⟩)
  rw [walkMixingTime, hempty, Nat.sInf_empty]

end UniformMixing


/-! ## The entropy leg of the mixing program (2026-09-01, `proposals/entropy-mixing-pinsker.md`)

Pinsker's inequality (`tvDistance_le_sqrt_half_klDiv`) and the
entropy-decay family (`klDiv_walkDistribution_le`,
`klDiv_contWalkDistribution_le`), with the entropy floor
(`klDiv_walkDistribution_ge_of_eigenpair`) beside its TV-floor engine:
the triangle's exact entropies `log(3/2)` / `(1/2)·log(9/8)` from raw
law literals, the bridge instance `log(3/2) ≤ χ²(1) = 1/2` with both
sides pinned, the decay instances with honest slack, the numeric
Pinsker pin `TV(1) = 1/3 ≤ √(log(3/2)/2)`, the entropy-floor instance
`2·(1/8) ≤ log(3/2)` — and on `K₂` the **exact never-decay pin**
`D = log 2` at every time (the entropy twin of `TV ≡ 1/2`), Pinsker's
`1/2 ≤ log 2` at the Gibbs equality, the one-way fence
`¬(χ² ≤ D)`, the continuous-time `t = 0` join `D_cont(0) = log 3`,
and the q-zero refutation of the un-guarded Pinsker statement (the
junk `klTerm (1/2) 0 = 0` makes it read `1/2 ≤ 0`).
-/

/-- The triangle's exact entropy at `t = 1`: `D(ν₁ ‖ π) = log(3/2)`
from the raw law literal. -/
theorem tri_kl_one_QA :
    klDiv (walkDistribution triAdj 1 0) (stationaryVec triAdj)
      = Real.log (3/2) := by
  have h0 : klTerm (0 : ℝ) (1/3) = 0 := by simp [klTerm]
  have hA : klTerm (1/2 : ℝ) (1/3) = (1/2) * Real.log (3/2) := by
    simp only [klTerm, if_neg (by norm_num : (1/2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  rw [klDiv, tri_dist_one_QA]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.tail_cons, Matrix.cons_val_two, tri_pi_QA]
  rw [h0, hA]
  ring

/-- The triangle's exact entropy at `t = 2`: `D(ν₂ ‖ π) =
(1/2)·log(9/8)`. -/
theorem tri_kl_two_QA :
    klDiv (walkDistribution triAdj 2 0) (stationaryVec triAdj)
      = (1/2) * Real.log (9/8) := by
  have hA : klTerm (1/2 : ℝ) (1/3) = (1/2) * Real.log (3/2) := by
    simp only [klTerm, if_neg (by norm_num : (1/2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hB : klTerm (1/4 : ℝ) (1/3) = (1/4) * Real.log (3/4) := by
    simp only [klTerm, if_neg (by norm_num : (1/4 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hsum : (1/2 : ℝ) * Real.log (3/2) + (1/4) * Real.log (3/4)
      + (1/4) * Real.log (3/4)
      = (1/2) * (Real.log (3/2) + Real.log (3/4)) := by ring
  have hcomb : Real.log (3/2) + Real.log (3/4) = Real.log (9/8) := by
    rw [← Real.log_mul (by norm_num : (3:ℝ)/2 ≠ 0)
      (by norm_num : (3:ℝ)/4 ≠ 0)]
    congr 1
    norm_num
  rw [klDiv, tri_dist_two_QA]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.tail_cons, Matrix.cons_val_two, tri_pi_QA]
  rw [hA, hB, hsum, hcomb]

/-- The bridge instance at `t = 1`: `log(3/2) ≤ χ²(1) = 1/2`, both
sides independently pinned — `log(3/2) ≤ 3/2 − 1` attained. -/
theorem tri_kl_le_chi2_one_QA :
    klDiv (walkDistribution triAdj 1 0) (stationaryVec triAdj)
      ≤ chiSquareDistance triAdj 1 0 := by
  rw [tri_kl_one_QA, tri_chi2_all_QA 1]
  have h : Real.log (3/2) ≤ 3/2 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  norm_num
  linarith

/-- The decay instance at `t = 1`: `log(3/2) ≤ (1/2)²·2 = 1/2`. -/
theorem tri_kl_decay_one_QA :
    klDiv (walkDistribution triAdj 1 0) (stationaryVec triAdj)
      ≤ (1/2 : ℝ) ^ (2 * 1) * ((stationaryVec triAdj 0)⁻¹ - 1) :=
  klDiv_walkDistribution_le triAdj triAdj_isSymm triAdj_nonneg
    triAdj_deg_pos tri_connected (1/2) 1 0 tri_rate_QA

/-- The decay instance at `t = 2`, with honest slack:
`(1/2)·log(9/8) ≤ 1/16 < 1/8`. -/
theorem tri_kl_decay_two_QA :
    klDiv (walkDistribution triAdj 2 0) (stationaryVec triAdj)
      ≤ (1/2 : ℝ) ^ (2 * 2) * ((stationaryVec triAdj 0)⁻¹ - 1)
        ∧ klDiv (walkDistribution triAdj 2 0) (stationaryVec triAdj)
          ≤ 1/16 := by
  refine ⟨klDiv_walkDistribution_le triAdj triAdj_isSymm triAdj_nonneg
    triAdj_deg_pos tri_connected (1/2) 2 0 tri_rate_QA, ?_⟩
  rw [tri_kl_two_QA]
  have h : Real.log (9/8) ≤ 9/8 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  norm_num
  linarith

/-- The vector-Pinsker instance on the triangle, numeric:
`TV(1) = 1/3 ≤ √(log(3/2)/2)` (squaring: `2/9 ≤ log(3/2)`, three
Gibbs steps). -/
theorem tri_pinsker_one_QA :
    tvDistance (walkDistribution triAdj 1 0) (stationaryVec triAdj)
      ≤ Real.sqrt (klDiv (walkDistribution triAdj 1 0)
          (stationaryVec triAdj) / 2) :=
  tvDistance_le_sqrt_half_klDiv
    (walkDistribution_nonneg triAdj triAdj_nonneg triAdj_deg_pos 1 0)
    (sum_walkDistribution triAdj triAdj_deg_pos 1 0)
    (fun i => stationaryVec_pos triAdj triAdj_deg_pos i)
    (sum_stationaryVec triAdj triAdj_deg_pos)

theorem tri_pinsker_one_numeric_QA :
    tvDistance (walkDistribution triAdj 1 0) (stationaryVec triAdj)
      = 1/3
      ∧ (1/3 : ℝ) ≤ Real.sqrt (Real.log (3/2) / 2) := by
  refine ⟨by rw [tri_disc_tv_eq_QA 1]; norm_num, ?_⟩
  rw [← Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1/3)]
  refine Real.sqrt_le_sqrt ?_
  have h : (1:ℝ) - (3/2)⁻¹ ≤ Real.log (3/2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hinv : (3/2 : ℝ)⁻¹ = 2/3 := by norm_num
  rw [hinv] at h
  norm_num
  linarith

/-- The entropy floor instance on the triangle: the floor reads
`2·((1/2)^{m+1})²` against the exact entropy. -/
theorem tri_kl_floor_le_QA (m : ℕ) :
    2 * ((1/2 : ℝ) ^ (m + 1)) ^ 2
      ≤ klDiv (walkDistribution triAdj m 0) (stationaryVec triAdj) := by
  have hfl := klDiv_walkDistribution_ge_of_eigenpair triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos m 0 tri_lapsym_mulVec_triG_QA
    (by norm_num : (3/2 : ℝ) ≠ 0)
    (c := 2 * (Real.sqrt 2)⁻¹) triF_abs_le (by positivity)
  have hval : (1/2) * |1 - 3/2| ^ m * |triF 0| / (2 * (Real.sqrt 2)⁻¹)
      = (1/2) ^ (m + 1) := (tri_tv_floor_value_QA m).1
  rw [← hval]
  exact hfl

theorem tri_kl_floor_one_QA :
    2 * ((1/2 : ℝ) ^ (1 + 1)) ^ 2 = 1/8
      ∧ (1/8 : ℝ) ≤ Real.log (3/2) := by
  refine ⟨by norm_num, ?_⟩
  have h : (1:ℝ) - (3/2)⁻¹ ≤ Real.log (3/2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hinv : (3/2 : ℝ)⁻¹ = 2/3 := by norm_num
  rw [hinv] at h
  norm_num
  linarith

/-- The exact `K₂` entropy summand: `klTerm 1 (1/2) = log 2`. -/
theorem klTerm_one_half_QA : klTerm (1:ℝ) (1/2) = Real.log 2 := by
  simp only [klTerm, if_neg one_ne_zero, one_mul]
  congr 1
  norm_num

theorem klTerm_zero_half_QA : klTerm (0:ℝ) (1/2) = 0 := by
  simp [klTerm]

/-- **The exact never-decay pin on `K₂`**: entropy is `log 2` at every
time — the periodic chain pinned at non-mixing in the entropy metric
(the entropy twin of `TV ≡ 1/2`). -/
theorem k2_kl_all_QA (m : ℕ) :
    klDiv (walkDistribution k2Adj m 0) (stationaryVec k2Adj)
      = Real.log 2 := by
  rcases Nat.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk, show k + k = 2 * k from by omega, klDiv, k2_dist_even_QA k]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, k2_pi_QA]
    rw [klTerm_one_half_QA, klTerm_zero_half_QA, add_zero]
  · rw [hk, k2_dist_odd_QA k, klDiv]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, k2_pi_QA]
    rw [klTerm_zero_half_QA, klTerm_one_half_QA, zero_add]

/-- Pinsker's instance on `K₂`: `2·(1/2)² = 1/2 ≤ log 2`, the Gibbs
bound `log 2 ≥ 1 − 1/2` attained at equality. -/
theorem k2_pinsker_QA (m : ℕ) :
    2 * (tvDistance (walkDistribution k2Adj m 0)
        (stationaryVec k2Adj)) ^ 2
      ≤ klDiv (walkDistribution k2Adj m 0) (stationaryVec k2Adj) := by
  have h := k2_kl_all_QA m
  have hlog : (1:ℝ) - (2:ℝ)⁻¹ ≤ Real.log 2 :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have htv := k2_disc_tv_eq_QA m
  rw [htv]
  have hinv : (2 : ℝ)⁻¹ = 1/2 := by norm_num
  rw [hinv] at hlog
  norm_num
  linarith

/-- **The entropy never decays on `K₂`**: `D ≥ 1/4` at every time —
the entropy floor's ultimate instance (the fence the χ²-piggyback
decay bound can never reach on a periodic chain). -/
theorem k2_kl_never_decays_QA (m : ℕ) :
    1/4 ≤ klDiv (walkDistribution k2Adj m 0) (stationaryVec k2Adj) := by
  rw [k2_kl_all_QA m]
  have hlog : (1:ℝ) - (2:ℝ)⁻¹ ≤ Real.log 2 :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hinv : (2 : ℝ)⁻¹ = 1/2 := by norm_num
  rw [hinv] at hlog
  norm_num
  linarith

/-- **The bridge is one-way**: `χ² ≤ D` is false on `K₂` — `χ² = 1` at
every time while `D = log 2 < 1` strictly (`log_lt_sub_one`). -/
theorem k2_chi2_not_le_kl_QA :
    ¬ (chiSquareDistance k2Adj 1 0
        ≤ klDiv (walkDistribution k2Adj 1 0) (stationaryVec k2Adj)) := by
  intro h
  rw [k2_chi2_all_QA 1, k2_kl_all_QA 1] at h
  have hlt : Real.log 2 < 2 - 1 :=
    Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  have h2 : (2:ℝ) - 1 = 1 := by ring
  rw [h2] at hlt
  linarith

/-- The q-zero junk pin: at `q = (1, 0)` the junk convention
`klTerm (1/2) 0 = (1/2)·log 0 = 0` plus the negative first summand
make the relative entropy *negative* — `D = −(1/2)·log 2`. -/
theorem zero_q_klDiv_QA :
    klDiv (![1/2, 1/2] : Fin 2 → ℝ) (![1, 0] : Fin 2 → ℝ)
      = -(1/2) * Real.log 2 := by
  have h1 : klTerm (1/2 : ℝ) 1 = -(1/2) * Real.log 2 := by
    have hpos : (0:ℝ) < 1/2 := by norm_num
    have hlog : Real.log ((1:ℝ)/2) = -Real.log 2 := by
      rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from by norm_num, Real.log_inv]
    simp only [klTerm, if_neg (ne_of_gt hpos), div_one, hlog]
    ring
  have h2 : klTerm (1/2 : ℝ) 0 = 0 := by
    simp only [klTerm, if_neg (by norm_num : (1/2:ℝ) ≠ 0),
      div_zero, Real.log_zero, mul_zero]
  rw [klDiv]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one]
  rw [h1, h2]
  ring

/-- **Pinsker's q-positivity hypothesis is load-bearing**: the
un-guarded statement at `p = (1/2, 1/2)`, `q = (1, 0)` reads
`TV = 1/2 ≤ √(D/2) = √(negative) = 0` — refuted. -/
theorem pinsker_q_guard_refuted_QA :
    ¬ (tvDistance (![1/2, 1/2] : Fin 2 → ℝ) (![1, 0] : Fin 2 → ℝ)
        ≤ Real.sqrt (klDiv (![1/2, 1/2] : Fin 2 → ℝ)
          (![1, 0] : Fin 2 → ℝ) / 2)) := by
  intro h
  have hTV : tvDistance (![1/2, 1/2] : Fin 2 → ℝ) (![1, 0] : Fin 2 → ℝ)
      = 1/2 := by
    have e0 : |(![1/2, 1/2] : Fin 2 → ℝ) 0 - (![1, 0] : Fin 2 → ℝ) 0|
        = 1/2 := by
      simp only [Matrix.cons_val_zero, Matrix.head_cons]
      rw [abs_of_nonpos (by norm_num : (1:ℝ)/2 - 1 ≤ 0)]
      norm_num
    have e1 : |(![1/2, 1/2] : Fin 2 → ℝ) 1 - (![1, 0] : Fin 2 → ℝ) 1|
        = 1/2 := by
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.head_cons]
      rw [abs_of_pos (by norm_num : (0:ℝ) < 1/2 - 0)]
      norm_num
    rw [tvDistance, Fin.sum_univ_two, e0, e1]
    norm_num
  rw [hTV, zero_q_klDiv_QA] at h
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : Real.sqrt (-(1/2) * Real.log 2 / 2) = 0 :=
    Real.sqrt_eq_zero_of_nonpos (by nlinarith)
  rw [hsqrt] at h
  norm_num at h

/-- The continuous-time `t = 0` join on the triangle: `D_cont(0) =
log 3` at the point mass. -/
theorem tri_cont_kl_zero_QA :
    klDiv (contWalkDistribution triAdj 0 0) (stationaryVec triAdj)
      = Real.log 3 := by
  have hlaw : walkDistribution triAdj 0 0 = ![1, 0, 0] := by
    funext i
    fin_cases i
    all_goals simp [walkDistribution_zero, Pi.single_apply]
  have h1 : klTerm (1 : ℝ) (1/3) = Real.log 3 := by
    simp only [klTerm, if_neg one_ne_zero, one_mul]
    congr 1
    norm_num
  have h0 : klTerm (0 : ℝ) (1/3) = 0 := by simp [klTerm]
  rw [contWalkDistribution_zero triAdj triAdj_deg_pos 0, hlaw, klDiv]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.tail_cons, Matrix.cons_val_two, tri_pi_QA]
  rw [h1, h0]
  ring

/-- The continuous-time bridge instance (the piggyback made visible):
`D_cont(t) ≤ χ²_cont(t)` at every nonnegative time — the first QA
consumer of `contWalkDistribution_nonneg`. -/
theorem tri_cont_kl_le_chi2_QA (t : ℝ) (ht : 0 ≤ t) :
    klDiv (contWalkDistribution triAdj t 0) (stationaryVec triAdj)
      ≤ contChiSquareDistance triAdj t 0 :=
  (klDiv_le_sum_sq_div (fun i => contWalkDistribution_nonneg triAdj
    triAdj_isSymm triAdj_nonneg triAdj_deg_pos ht 0 i)
    (fun i => stationaryVec_pos triAdj triAdj_deg_pos i)
    (sum_contWalkDistribution triAdj triAdj_isSymm triAdj_deg_pos t 0)
    (sum_stationaryVec triAdj triAdj_deg_pos)).trans
    (le_of_eq (contChiSquareDistance_eq_sum_div triAdj triAdj_deg_pos t 0).symm)

/-- The continuous-time decay instance through the pinned spectrum:
`D_cont(t) ≤ 2·e^{−3t}`. -/
theorem tri_cont_kl_decay_QA (t : ℝ) (ht : 0 ≤ t) :
    klDiv (contWalkDistribution triAdj t 0) (stationaryVec triAdj)
      ≤ 2 * Real.exp (-(3 * t)) := by
  have h := klDiv_contWalkDistribution_le triAdj triAdj_isSymm
    triAdj_nonneg triAdj_deg_pos (by norm_num : 2 ≤ Fintype.card (Fin 3))
    ht 0
  rw [tri_secondEval_QA, tri_pi_QA 0] at h
  rw [show (2:ℝ) * t * (3/2) = 3 * t from by ring] at h
  have hfin : Real.exp (-(3 * t)) * ((1/3 : ℝ)⁻¹ - 1)
      = 2 * Real.exp (-(3 * t)) := by
    have h2 : ((1/3 : ℝ)⁻¹ - 1) = 2 := by norm_num
    rw [h2, mul_comm]
  rw [hfin] at h
  exact h

end SpectralGraphTheory.QA
