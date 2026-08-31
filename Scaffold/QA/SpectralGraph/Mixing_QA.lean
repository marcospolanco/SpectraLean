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

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Mixing
import Scaffold.Mathlib.GraphTheory.Oversmoothing
import Scaffold.Mathlib.GraphTheory.Electrical
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

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

end SpectralGraphTheory.QA
