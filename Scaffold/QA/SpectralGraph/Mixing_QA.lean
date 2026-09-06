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
  The `LazyWalk` section (2026-09-01, `proposals/lazy-walk-mixing.md`)
  witnesses the periodicity fix and its engine: on `K₂` (bipartite,
  certificate-free for the plain family) **the headline attained
  exactly at every time** (`χ²_lazy ≡ 0` at the intrinsic rate
  `1 − 2/2 = 0`, both sides pinned) and the TV contrast pair (plain
  `1/2` against lazy `0`); on the path `P₃` the center start (the pure
  `λ = 2` periodic mode) exactly stationary after one lazy step
  against the proved plain never-decay pin `χ²_plain ≡ 1` at every
  time, the corner values `1/2`, `1/8` with the bound instance
  evaluated at the pinned gap, and the `t = 0` normalization; and the
  signless engine's tightness at the `K₂` top mode (`0` exactly — the
  bipartite boundary) beside the `hnn` fence at the negative-diagonal
  fixture (`-4 < 0` with every other hypothesis holding).

  The `LazyMixingTime` section (2026-09-01,
  `proposals/lazy-mixing-time-objects.md`) completes the fix at the
  object level: the exact corner-start TV closed form
  `TV_lazy(1+t) = (1/2)^{t+2}` at every time on the bipartite path,
  **`t_mix_lazy(corner, 1/8) = 2` pinned in both directions** where
  the plain walk provably never mixes, `t_mix_lazy(center, 1/4) = 1`
  with the intrinsic-rate ceiling attained exactly, the corner ceiling
  with honest slack (`3` against the true `2`), **the object-level
  periodicity contrast** (plain `t_mix(K₂, 1/8) = 0` junk — empty
  witness set — against lazy `= 1` genuine), and the entrywise lazy
  ceiling attained exactly on `K₂` (both sides zero at rate `0`).

  The `LazyFences` section (2026-09-02,
  `proposals/adversarial-fences-lazy-family.md`) is the audit-shaped
  adversarial pass over the whole lazy family — hypothesis-form
  negative witnesses for the clauses no earlier section pinned: the
  `hd` clauses of lazy row-stochasticity, mass conservation, and the
  `t = 0` χ² normalization at the zero-degree fixture (where the
  `D⁻¹A` row is junk-zero, mass `1/2`, and the normalization's right
  side the junk `0⁻¹ − 1 = −1`); the `hnn` clauses of operator- and
  law-nonnegativity at the negative off-diagonal fixture (`P_L 0 1 =
  −1/2`, which the existing negative-*diagonal* fixture cannot kill);
  the `hA` clauses of detailed balance (`3/16 ≠ 1/16`), stationarity
  (`5/8 ≠ 3/4`), and attainment persistence at the asymmetric loop
  fixture whose lazy law hits `π` exactly at `t = 1` and leaves it at
  `t = 2`; and the two certificate clauses of the public lazy ℓ²(π)
  contraction engine — `hrate` refuted on the triangle at the genuine
  `3/2`-mode direction with `r = 1/8` below the factor `1/4`
  (`1/24 > 1/96`), `hmode` refuted on the edge at the constant mode
  with the genuine `r = 0` certificate (`1 > 0`) — each with its
  isolation companion proving every other hypothesis genuine and the
  dropped one failing.

  The `PoissonFences` section (2026-09-03,
  `proposals/adversarial-fences-poisson-bridge-family.md`) is the
  audit-shaped adversarial pass over the Poisson-bridge family —
  hypothesis-form negative witnesses for the clauses no earlier
  section pinned: the four mass clauses of the simplex-diameter
  lemma; the summability clause of the head–tail split at the
  non-summable constant-one sequence; the convexity bound's `hc`,
  `hc1` (direct constants) and `hν`, `hν1` (**divergent-tsum junk** —
  geometric weights against geometrically growing laws junk both
  sides to `0` against the honest left TV `1/2`); the Poisson
  weight's negative-time clause; the `hnn` clauses of the TV ≤ 1
  bound, the adjoint-walk contraction (plain and iterated), and
  discrete TV monotonicity at the negative off-diagonal fixture (TV
  `3/2 → 9/2`); the `hA` clauses of the Poissonization identity
  triple (reversibility: at the asymmetric swap the mixture of the
  constant `(3, 0)` densities sums against the heat kernel's genuine
  drift), of the stationary power, and of discrete TV monotonicity at
  the new asymmetric-flow fixture (`1/10 → 7/20`); the rate theorems'
  `hA` at the swap's `t = 2` (`1 − e⁻² > 2/3` from `e² > 4`); the
  `ht` clauses at `t = −1` on the edge (the signed weights leave the
  continuous TV at `e²/2`); and the transfer corollary's `htail` on
  the triangle at `t = 1/2` (the certificate `ε₁ = 1/6` genuine, the
  tail budget `1/20` understating the honest head, refuted from the
  series bound `e < 3`). `hmix` was already fenced
  (`k2_no_discrete_mixing_QA`); the `hd` clauses are recorded
  non-fenceable in the proposal (with `hnn` retained the junk-collapsed
  chain is honestly substochastic and every identity survives).

  The `LazyFollowOnFences` section (2026-09-03,
  `proposals/adversarial-fences-lazy-family.md`, follow-on delivery
  record) closes the lazy audit's two priced deferrals: the
  conjugated-norm contraction twin's two certificate clauses (the
  √D-weighted mirrors of the delivered ℓ²(π) pair — `hrate` on the
  triangle at the `3/2`-mode direction with the below-mode `r = 1/8`
  (`LHS = 1/4 > 1/16 = RHS`), `hmode` on the edge at the constant
  zero mode with the genuine `r = 0` (`LHS = 2 > 0 = RHS`)) — and the
  lazy `t_mix` object's `_spec` witness-clause junk corner at the
  disconnected bipartite fixture `K₂ ⊕ K₂` on `Fin 4` (the lazy-law
  closed form: `δ₀` at time zero, the component-stationary
  `(1/2,1/2,0,0)` at every positive time; `TV = 3/4` at zero and `1/2`
  after, never below `1/8` — no witness exists, `t_mix = sInf ∅ = 0`,
  and the dropped-`hne` conclusion fails at `s = 0`; every structural
  hypothesis genuine, connectivity exactly the failure — laziness
  repairs periodicity, not disconnection).

  Scoreboard: ../QA_SCOREBOARD.md

  The engine-join section (2026-09-06,
  `proposals/walktvpair-dobrushin-join.md`) pins the identity
  `walkTVPair_eq_tvDobrushinCoeff` at the delivered `triAdj` fixture:
  the engine side evaluates to the pinned walk-side closed forms, and
  the attained submultiplicativity instance is re-derived through the
  join.
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

/-! ## The lazy walk: the periodicity fix witnessed -/

/-- The lazy matrix on the path `P₃`, pinned entrywise: the diagonal
entries are all `1/2` (the stay probability), and the off-diagonal
entries are `1/4` on the support edges and `0` off-support — the
average of the walk matrix with the identity. -/
theorem path_lazy_matrix_diag_QA :
    lazyWalkTransitionMatrix pathAdj 1 1 = 1/2 := by
  simp [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply, deg,
    pathAdj, Fin.sum_univ_three]

theorem path_lazy_matrix_edge01_QA :
    lazyWalkTransitionMatrix pathAdj 0 1 = 1/2 := by
  simp [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply, deg,
    pathAdj, Fin.sum_univ_three]

theorem path_lazy_matrix_edge12_QA :
    lazyWalkTransitionMatrix pathAdj 1 2 = 1/4 := by
  simp [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply, deg,
    pathAdj, Fin.sum_univ_three]
  norm_num

theorem path_lazy_matrix_edge02_QA :
    lazyWalkTransitionMatrix pathAdj 0 2 = 0 := by
  simp [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply, deg,
    pathAdj, Fin.sum_univ_three]

/-- The `t = 0` normalization on the path's corner start: the same
point-mass value `3 = (1/4)⁻¹ − 1` as the plain walk. -/
theorem path_lazy_zero_QA :
    lazyChiSquareDistance pathAdj 0 0 = 3 := by
  rw [lazyChiSquareDistance_zero pathAdj pathAdj_deg_pos 0, path_pi_QA]
  norm_num

/-- The lazy law on the path from the center after one step: exactly
the stationary distribution — the pure periodic mode (`λ = 2`) is
killed in a single lazy step. -/
theorem path_lazy_center_law_one_QA :
    lazyWalkDistribution pathAdj 1 1 = stationaryVec pathAdj := by
  rw [lazyWalkDistribution_succ, lazyWalkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [lazyWalkTransitionMatrix, walkTransitionMatrix, deg,
    vol, pathAdj, Matrix.mulVec, Matrix.dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_three, Pi.single_apply,
    stationaryVec]
  all_goals norm_num

/-- Attainment persists (the shelf lemma): the center start's law is
stationary at every time `t ≥ 1`. -/
theorem path_lazy_center_mix_all_QA (t : ℕ) :
    lazyWalkDistribution pathAdj (1 + t) 1 = stationaryVec pathAdj :=
  lazyWalkDistribution_add_stationary pathAdj pathAdj_isSymm
    pathAdj_deg_pos 1 t 1 path_lazy_center_law_one_QA

/-- The lazy χ² from the center start is exactly zero at every
`t ≥ 1` — one-step exact mixing on the bipartite path. -/
theorem path_lazy_center_chi2_all_QA (t : ℕ) :
    lazyChiSquareDistance pathAdj (1 + t) 1 = 0 := by
  rw [lazyChiSquareDistance, path_lazy_center_mix_all_QA t]
  simp

/-- The lazy TV from the center start is exactly zero at every
`t ≥ 1`. -/
theorem path_lazy_center_tv_all_QA (t : ℕ) :
    tvDistance (lazyWalkDistribution pathAdj (1 + t) 1)
        (stationaryVec pathAdj) = 0 := by
  rw [path_lazy_center_mix_all_QA t]
  simp [tvDistance]

/-- **The contrast pair on the same start**: the *plain* walk from the
path's center never decays — `χ²_plain(t, center) = 1` at every time
(the law alternates `δ₁ ↔ (1/2, 0, 1/2)` with period two, the
`λ_max = 2` mode oscillating) — while the lazy walk is exactly
stationary after one step (`path_lazy_center_chi2_all_QA`). This is
the periodicity defect and its fix on one fixture. -/
theorem path_plain_never_QA (t : ℕ) :
    chiSquareDistance pathAdj t 1 = 1 := by
  have hbase1 : walkDistribution pathAdj 1 1 = ![1/2, 0, 1/2] := by
    rw [walkDistribution_succ, walkDistribution_zero]
    funext i
    fin_cases i
    all_goals simp [walkTransitionMatrix, deg, pathAdj, Matrix.mulVec,
      Matrix.dotProduct, Matrix.transpose_apply, Fin.sum_univ_three,
      Pi.single_apply]
    all_goals norm_num
  have hper : ∀ t : ℕ,
      walkDistribution pathAdj (t + 2) 1 = walkDistribution pathAdj t 1 := by
    intro t
    induction t with
    | zero =>
      have h1 : walkDistribution pathAdj ((0 : ℕ) + 2) 1
          = (walkTransitionMatrix pathAdj)ᵀ *ᵥ
              walkDistribution pathAdj ((0 : ℕ) + 1) 1 :=
        walkDistribution_succ _ _ _
      have h2 : walkDistribution pathAdj ((0 : ℕ) + 1) 1
          = (walkTransitionMatrix pathAdj)ᵀ *ᵥ
              walkDistribution pathAdj (0 : ℕ) 1 :=
        walkDistribution_succ _ _ _
      rw [h1, h2, walkDistribution_zero]
      funext i
      fin_cases i
      all_goals simp [walkTransitionMatrix, deg, pathAdj, Matrix.mulVec,
        Matrix.dotProduct, Matrix.transpose_apply, Fin.sum_univ_three,
        Pi.single_apply]
      all_goals norm_num
    | succ t ih =>
      have h1 : walkDistribution pathAdj (t + 1 + 2) 1
          = (walkTransitionMatrix pathAdj)ᵀ *ᵥ
              walkDistribution pathAdj (t + 2) 1 :=
        walkDistribution_succ _ _ _
      rw [h1, ih, walkDistribution_succ]
  have hstep : ∀ t : ℕ,
      chiSquareDistance pathAdj (t + 2) 1
        = chiSquareDistance pathAdj t 1 := by
    intro t
    simp only [chiSquareDistance]
    rw [hper t]
  have heven : ∀ k : ℕ, chiSquareDistance pathAdj (2 * k) 1 = 1 := by
    intro k
    induction k with
    | zero =>
      rw [chiSquareDistance_zero pathAdj pathAdj_deg_pos 1, path_pi_QA]
      norm_num
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 from by omega, hstep]
      exact ih
  have hodd : ∀ k : ℕ, chiSquareDistance pathAdj (2 * k + 1) 1 = 1 := by
    intro k
    induction k with
    | zero =>
      have hlaw : walkDistribution pathAdj (2 * 0 + 1) 1
          = ![1/2, 0, 1/2] := by
        rw [show 2 * 0 + 1 = 1 from rfl]
        exact hbase1
      simp only [chiSquareDistance, hlaw, path_pi_QA]
      norm_num [Fin.sum_univ_three]
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 from by omega, hstep]
      exact ih
  rcases Nat.even_or_odd t with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hk' : k + k = 2 * k := by ring
    rw [hk, hk']
    exact heven k
  · rw [hk]
    exact hodd k

/-- The lazy law on the path from the corner after one step. -/
theorem path_lazy_corner_law_one_QA :
    lazyWalkDistribution pathAdj 1 0 = ![1/2, 1/2, 0] := by
  rw [lazyWalkDistribution_succ, lazyWalkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [lazyWalkTransitionMatrix, walkTransitionMatrix, deg,
    pathAdj, Matrix.mulVec, Matrix.dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_three, Pi.single_apply]

/-- The lazy χ² from the corner at `t = 1`: `1/2` — the honest
intrinsic rate `1 − 1/2` at work on the surviving mode. -/
theorem path_lazy_corner_chi2_one_QA :
    lazyChiSquareDistance pathAdj 1 0 = 1/2 := by
  rw [lazyChiSquareDistance, path_lazy_corner_law_one_QA, path_pi_QA]
  norm_num [Fin.sum_univ_three]

/-- The bound instance at `t = 1`, evaluated at the pinned gap
`λ₂ = 1`: `1/2 ≤ 3/4`, slack witnessed. -/
theorem path_lazy_corner_bound_one_QA :
    lazyChiSquareDistance pathAdj 1 0 ≤ 3/4 := by
  have hval : (1 - secondEval (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) ^ (2 * 1)
      * ((stationaryVec pathAdj 0)⁻¹ - 1) = 3/4 := by
    rw [path_secondEval_QA, path_pi_QA]
    norm_num
  rw [show (3/4 : ℝ) = (1 - secondEval (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) ^ (2 * 1)
      * ((stationaryVec pathAdj 0)⁻¹ - 1) from hval.symm]
  exact lazyChiSquareDistance_le_of_connected pathAdj pathAdj_isSymm
    pathAdj_nonneg pathAdj_deg_pos
    (by norm_num : 2 ≤ Fintype.card (Fin 3)) path_connected 1 0

/-- The `K₂` lazy law after one step: exactly `π`. -/
theorem k2_lazy_law_one_QA :
    lazyWalkDistribution k2Adj 1 0 = stationaryVec k2Adj := by
  have hπ : stationaryVec k2Adj = ![1/2, 1/2] := by
    funext i
    fin_cases i <;> simp [k2_pi_QA]
  rw [lazyWalkDistribution_succ, lazyWalkDistribution_zero, hπ]
  funext i
  fin_cases i
  all_goals simp [lazyWalkTransitionMatrix, walkTransitionMatrix, deg,
    k2Adj, Matrix.mulVec, Matrix.dotProduct,
    Matrix.transpose_apply, Fin.sum_univ_two, Pi.single_apply]

/-- The `K₂` lazy χ² is exactly zero at every `t ≥ 1` — the rate
`1 − λ₂/2` is exactly `0` at the pinned gap `λ₂ = 2`, and the walk
mixes in one step on the chain where the plain walk's certificates are
provably unsatisfiable. -/
theorem k2_lazy_chi2_all_QA (t : ℕ) :
    lazyChiSquareDistance k2Adj (1 + t) 0 = 0 := by
  have hstays : lazyWalkDistribution k2Adj (1 + t) 0
      = stationaryVec k2Adj :=
    lazyWalkDistribution_add_stationary k2Adj k2Adj_isSymm
      k2Adj_deg_pos 1 t 0 k2_lazy_law_one_QA
  rw [lazyChiSquareDistance, hstays]
  simp

/-- **The bound attained exactly, at every time**: on `K₂` the
headline reads `0 ≤ (1 − 2/2)^{2t} · ((1/2)⁻¹ − 1) = 0`, and the
left side is exactly `0` — the strongest QA shape a bound theorem can
have, on the fixture where the plain family is certificate-free. -/
theorem k2_lazy_bound_attained_QA (t : ℕ) :
    lazyChiSquareDistance k2Adj (1 + t) 0
      = (1 - secondEval (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm)
            (by norm_num) / 2) ^ (2 * (1 + t))
          * ((stationaryVec k2Adj 0)⁻¹ - 1) := by
  have hval : (1 - secondEval (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm)
        (by norm_num) / 2) ^ (2 * (1 + t))
      * ((stationaryVec k2Adj 0)⁻¹ - 1) = 0 := by
    rw [k2_secondEval_QA, k2_pi_QA 0]
    have hz : ((1 : ℝ) - 2 / 2) ^ (2 * (1 + t)) = 0 := by
      have h0 : ((1 : ℝ) - 2 / 2) = 0 := by norm_num
      rw [h0, zero_pow (by omega)]
    have h1 : ((1/2 : ℝ)⁻¹ - 1) = 1 := by norm_num
    rw [hz, h1]
    norm_num
  rw [k2_lazy_chi2_all_QA t, hval]

/-- **The periodicity fix on the edge, TV form**: the plain walk's TV
is `1/2` at every time (fenced on file), the lazy walk's is exactly
`0` after one step. -/
theorem k2_periodicity_fixed_QA :
    tvDistance (walkDistribution k2Adj 1 0) (stationaryVec k2Adj) = 1/2
      ∧ tvDistance (lazyWalkDistribution k2Adj 1 0)
          (stationaryVec k2Adj) = 0 := by
  constructor
  · rw [k2_dist_one_QA]
    have hπ : ∀ i : Fin 2, stationaryVec k2Adj i = 1/2 :=
      fun i => k2_pi_QA i
    simp only [tvDistance, Fin.sum_univ_two, hπ, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
    rw [show |((0:ℝ) - 1/2)| = 1/2 from by norm_num,
      show |((1:ℝ) - 1/2)| = 1/2 from by norm_num]
    norm_num
  · rw [k2_lazy_law_one_QA]
    simp only [tvDistance, sub_self]
    simp

/-- The signless certificate saturates on the edge's top mode:
`xᵀ(2·1 − L_sym)x = 0` at `x = (1, −1)` — the bipartite mode is
exactly the `μ = 2` boundary. -/
theorem sos_k2_top_mode_QA :
    quadForm ((2 : ℝ) • 1 - normalizedLaplacian k2Adj) ![1, -1] = 0 := by
  rw [quadForm_two_sub_normalizedLaplacian_eq k2Adj k2Adj_deg_pos _]
  have hu : degreeInvSqrt k2Adj *ᵥ (![1, -1] : Fin 2 → ℝ)
      = ![1, -1] := by
    funext i
    rw [degreeInvSqrt_mulVec_apply]
    fin_cases i <;> simp [k2Adj_deg_eq]
  rw [hu, quadForm_add_eq, quadForm_degreeMatrix_eq, quadForm_eq_sum]
  have hdeg : ∀ i : Fin 2, deg k2Adj i = 1 := fun i => k2Adj_deg_eq i
  simp only [hdeg, k2Adj_apply, Fin.sum_univ_two]
  norm_num

/-- The fence fixture: symmetric, positive degrees (`deg = 1`), with
nonnegativity violated only at the diagonal. -/
def negDiagAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, 2; 2, -1]

theorem negDiagAdj_isSymm : negDiagAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [negDiagAdj]

theorem negDiagAdj_apply (i j : Fin 2) :
    negDiagAdj i j = if i = j then -1 else 2 := by
  rw [negDiagAdj]
  fin_cases i <;> fin_cases j <;> rfl

theorem negDiagAdj_deg_eq (i : Fin 2) : deg negDiagAdj i = 1 := by
  rw [deg, negDiagAdj]
  fin_cases i <;> simp [Matrix.of_apply, Fin.sum_univ_two] <;> norm_num

theorem negDiagAdj_deg_pos (i : Fin 2) : 0 < deg negDiagAdj i := by
  rw [negDiagAdj_deg_eq i]
  norm_num

/-- **The `hnn` fence for the signless certificate**: at the
negative-diagonal fixture (symmetric, positive degrees — every
hypothesis except entrywise nonnegativity), the quadratic form of
`2·1 − L_sym` at the top mode is `-4 < 0` — the dropped conclusion
refuted in proved form. -/
theorem sos_nonneg_fence_QA :
    ¬ (0 ≤ quadForm ((2 : ℝ) • 1 - normalizedLaplacian negDiagAdj)
        ![1, -1]) := by
  rw [quadForm_two_sub_normalizedLaplacian_eq negDiagAdj
    negDiagAdj_deg_pos _]
  have hu : degreeInvSqrt negDiagAdj *ᵥ (![1, -1] : Fin 2 → ℝ)
      = ![1, -1] := by
    funext i
    rw [degreeInvSqrt_mulVec_apply]
    fin_cases i <;> simp [negDiagAdj_deg_eq]
  rw [hu, quadForm_add_eq, quadForm_degreeMatrix_eq, quadForm_eq_sum]
  have hdeg : ∀ i : Fin 2, deg negDiagAdj i = 1 :=
    fun i => negDiagAdj_deg_eq i
  simp only [hdeg, negDiagAdj_apply, Fin.sum_univ_two]
  norm_num

/-! ### The lazy mixing-time objects: the periodicity fix at the object
level (`proposals/lazy-mixing-time-objects.md`): the exact closed forms
pinned in both directions on the bipartite fixtures, the ceiling
attained exactly and with honest slack, and the object-level contrast —
the plain `t_mix` junk corner against the lazy twin's genuine value. -/

section LazyMixingTimeQA

/-- The lazy operator's transpose kills the antisymmetric mode by
exactly one half: `P_Lᵀ · (1, 0, −1) = (1/2, 0, −1/2)` — the `μ = 2`
periodic mode is dead after one lazy step, and the surviving `μ = 1`
mode halves per step. The corner-start law's engine, computed entrywise
from the raw operator. -/
theorem path_lazy_transpose_antisym_QA :
    (lazyWalkTransitionMatrix pathAdj)ᵀ *ᵥ
        (![1, 0, -1] : Fin 3 → ℝ) = ![1/2, 0, -1/2] := by
  funext i
  fin_cases i
  all_goals simp [Matrix.mulVec, Matrix.dotProduct,
    Matrix.transpose_apply, lazyWalkTransitionMatrix_apply,
    walkTransitionMatrix_apply, deg, pathAdj, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ,
    Matrix.head_cons]
  all_goals norm_num

/-- **The corner-start law in closed form at every time**: after the
first lazy step the law is `π + (1/2)^{t+2} · (1, 0, −1)` — stationarity
plus a purely antisymmetric deviation halving per step (`π`'s
stationarity under `P_Lᵀ` is the shelf lemma; the antisymmetric mode's
halving is the lemma above). -/
theorem path_lazy_corner_dev_all_QA (t : ℕ) :
    lazyWalkDistribution pathAdj (1 + t) 0
      = (stationaryVec pathAdj)
        + (1/2 : ℝ)^(t+2) • (![1, 0, -1] : Fin 3 → ℝ) := by
  have hbase : lazyWalkDistribution pathAdj (1 + 0) 0
      = (stationaryVec pathAdj)
        + (1/2 : ℝ)^(0+2) • (![1, 0, -1] : Fin 3 → ℝ) := by
    have hπ : (stationaryVec pathAdj)
        + (1/2 : ℝ)^(0+2) • (![1, 0, -1] : Fin 3 → ℝ)
        = ![1/2, 1/2, 0] := by
      rw [path_pi_QA]
      funext i
      fin_cases i <;>
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> norm_num
    rw [show (1 : ℕ) + 0 = 1 from rfl, path_lazy_corner_law_one_QA, hπ]
  induction t with
  | zero => exact hbase
  | succ t ih =>
    have hstep : lazyWalkDistribution pathAdj (1 + t + 1) 0
        = (lazyWalkTransitionMatrix pathAdj)ᵀ *ᵥ
            lazyWalkDistribution pathAdj (1 + t) 0 :=
      lazyWalkDistribution_succ pathAdj (1 + t) 0
    have hst : (lazyWalkTransitionMatrix pathAdj)ᵀ *ᵥ
        (stationaryVec pathAdj) = stationaryVec pathAdj :=
      lazyWalkTransitionMatrixTranspose_mulVec_stationaryVec pathAdj
        pathAdj_isSymm pathAdj_deg_pos
    have hsmul : (lazyWalkTransitionMatrix pathAdj)ᵀ *ᵥ
        ((1/2 : ℝ)^(t+2) • (![1, 0, -1] : Fin 3 → ℝ))
        = (1/2 : ℝ)^(t+2) •
            ((lazyWalkTransitionMatrix pathAdj)ᵀ *ᵥ
              (![1, 0, -1] : Fin 3 → ℝ)) :=
      Matrix.mulVec_smul _ _ _
    have hw : (![1/2, 0, -1/2] : Fin 3 → ℝ)
        = (1/2 : ℝ) • (![1, 0, -1] : Fin 3 → ℝ) := by
      funext i
      fin_cases i
      all_goals simp [Pi.smul_apply, smul_eq_mul]
      all_goals norm_num
    have hexp : (1/2 : ℝ)^(t+2) • (![1/2, 0, -1/2] : Fin 3 → ℝ)
        = (1/2 : ℝ)^(t+1+2) • (![1, 0, -1] : Fin 3 → ℝ) := by
      have h : (1/2 : ℝ)^(t+1+2) = (1/2 : ℝ) * (1/2 : ℝ)^(t+2) := by
        rw [show t + 1 + 2 = t + 2 + 1 from by omega, pow_succ,
          mul_comm ((1/2 : ℝ)^(t+2)) (1/2 : ℝ)]
      rw [h]
      set c : ℝ := (1/2 : ℝ)^(t+2) with hc
      funext i
      fin_cases i
      all_goals simp [Pi.smul_apply, smul_eq_mul]
      all_goals ring
    rw [show 1 + (t + 1) = 1 + t + 1 from by omega, hstep, ih,
      Matrix.mulVec_add, hst, hsmul,
      path_lazy_transpose_antisym_QA, hexp]

/-- **The corner-start TV closed form at every time**:
`TV_lazy(1 + t, corner) = (1/2)^{t+2}` — exact at every time on the
bipartite path, decaying at exactly the intrinsic rate `1 − λ₂/2 = 1/2`
(the pure `μ = 2` mode dead after one lazy step, the `μ = 1` mode
halving). -/
theorem path_lazy_corner_tv_all_QA (t : ℕ) :
    tvDistance (lazyWalkDistribution pathAdj (1 + t) 0)
        (stationaryVec pathAdj) = (1/2 : ℝ)^(t+2) := by
  have hc : 0 ≤ (1/2 : ℝ)^(t+2) := pow_nonneg (by norm_num) _
  rw [path_lazy_corner_dev_all_QA t, tvDistance, path_pi_QA]
  have hterm : ∀ i : Fin 3,
      |((![1/4, 1/2, 1/4] : Fin 3 → ℝ)
          + (1/2 : ℝ)^(t+2) • (![1, 0, -1] : Fin 3 → ℝ)) i
        - (![1/4, 1/2, 1/4] : Fin 3 → ℝ) i|
        = (1/2 : ℝ)^(t+2) * |(![1, 0, -1] : Fin 3 → ℝ) i| := by
    intro i
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
      abs_mul, abs_of_nonneg hc]
  have hsum : ∑ i, |((![1/4, 1/2, 1/4] : Fin 3 → ℝ)
        + (1/2 : ℝ)^(t+2) • (![1, 0, -1] : Fin 3 → ℝ)) i
      - (![1/4, 1/2, 1/4] : Fin 3 → ℝ) i|
      = ∑ i, (1/2 : ℝ)^(t+2) * |(![1, 0, -1] : Fin 3 → ℝ) i| :=
    Finset.sum_congr rfl fun i _ => hterm i
  have hw0 : |(![1, 0, -1] : Fin 3 → ℝ) 0| = 1 := by
    simp [Matrix.cons_val_zero, abs_of_nonneg]
  have hw1 : |(![1, 0, -1] : Fin 3 → ℝ) 1| = 0 := by
    simp [Matrix.cons_val_one, abs_of_nonneg]
  have hw2 : |(![1, 0, -1] : Fin 3 → ℝ) 2| = 1 := by
    simp [Matrix.cons_val_succ, abs_of_nonneg]
  rw [hsum]
  simp only [Fin.sum_univ_three]
  rw [hw0, hw1, hw2]
  ring

/-- **The exact lazy mixing-time closed form on the path's corner
start**: `t_mix_lazy(corner, 1/8) = 2`, pinned in both directions —
`TV(2) = 1/8` attains the threshold exactly, `TV(1) = 1/4` refutes
`1`. On the bipartite fixture where the plain walk provably never
mixes. -/
theorem path_lazy_corner_mix_eq_eighth_QA :
    lazyWalkMixingTimeFrom pathAdj 0 (1/8) = 2 := by
  have hcert : ∀ s : ℕ, 2 ≤ s →
      tvDistance (lazyWalkDistribution pathAdj s 0)
        (stationaryVec pathAdj) ≤ 1/8 := by
    intro s hs
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s = 1 + k := ⟨s - 1, by omega⟩
    rw [hk, path_lazy_corner_tv_all_QA k]
    have h8 : (8 : ℝ) ≤ (2 : ℝ)^(k+2) := by
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (by omega : (3 : ℕ) ≤ k + 2)
      norm_num at hp
      exact hp
    have hpos : (0 : ℝ) < (2 : ℝ)^(k+2) := pow_pos (by norm_num) _
    have hinv : (1/2 : ℝ)^(k+2) = 1 / ((2 : ℝ)^(k+2)) :=
      _root_.one_div_pow 2 (k+2)
    have hkey : (1 : ℝ) / ((2 : ℝ)^(k+2)) ≤ 1/8 :=
      (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 8)).mpr h8
    rw [hinv]
    linarith
  refine le_antisymm ?_ ?_
  · exact lazyWalkMixingTimeFrom_le_of_cert pathAdj 0 2 hcert
  · by_contra hne
    have hle1 : lazyWalkMixingTimeFrom pathAdj 0 (1/8) ≤ 1 := by omega
    have hspec := lazyWalkMixingTimeFrom_spec pathAdj 0 (ε := 1/8)
      ⟨2, hcert⟩ (1 + 0) (by simpa using hle1)
    rw [path_lazy_corner_tv_all_QA 0] at hspec
    norm_num at hspec

/-- **The exact lazy mixing-time closed form on the path's center
start**: `t_mix_lazy(center, 1/4) = 1` — the pure periodic mode is
stationary after one lazy step. -/
theorem path_lazy_center_mix_eq_one_QA :
    lazyWalkMixingTimeFrom pathAdj 1 (1/4) = 1 := by
  have hcert : ∀ s : ℕ, 1 ≤ s →
      tvDistance (lazyWalkDistribution pathAdj s 1)
        (stationaryVec pathAdj) ≤ 1/4 := by
    intro s hs
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s = 1 + k := ⟨s - 1, by omega⟩
    rw [hk, path_lazy_center_mix_all_QA k]
    have hself : tvDistance (stationaryVec pathAdj)
        (stationaryVec pathAdj) = 0 := by simp [tvDistance]
    rw [hself]
    norm_num
  refine le_antisymm (lazyWalkMixingTimeFrom_le_of_cert pathAdj 1 1 hcert) ?_
  by_contra hne
  have hzero : lazyWalkMixingTimeFrom pathAdj 1 (1/4) = 0 := by omega
  have hspec := lazyWalkMixingTimeFrom_spec pathAdj 1 (ε := 1/4)
    ⟨1, hcert⟩ 0 (by omega)
  have hvec : (Pi.single (1 : Fin 3) (1 : ℝ) : Fin 3 → ℝ)
      = ![0, 1, 0] := by
    funext i
    fin_cases i <;> simp
  have hTV0 : tvDistance (lazyWalkDistribution pathAdj 0 1)
      (stationaryVec pathAdj) = 1/2 := by
    norm_num [tvDistance, lazyWalkDistribution_zero, hvec, path_pi_QA,
      Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_succ, Matrix.head_cons, neg_sub, abs_of_neg,
      abs_of_nonneg]
  rw [hTV0] at hspec
  norm_num at hspec

/-- **The ceiling attained exactly**: on the path's center start at
`ε = 1/4` and the pinned gap `λ₂ = 1`, the object is `1` and the
ceiling's own right side evaluates to `1` — no slack anywhere in the
package (both the threshold ratio `1/(2·(1/4)) = 2` and the rate base
`1/(1−1/2) = 2` sit exactly at `2`, cancelling in the log ratio). -/
theorem path_lazy_center_ceiling_attained_QA :
    lazyWalkMixingTimeFrom pathAdj 1 (1/4)
      = Nat.ceil (Real.log (Real.sqrt ((stationaryVec pathAdj 1)⁻¹ - 1)
          / (2 * (1/4 : ℝ))) / Real.log (1 / (1 - secondEval
            (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
            (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2)))
      ∧ Nat.ceil (Real.log (Real.sqrt ((stationaryVec pathAdj 1)⁻¹ - 1)
          / (2 * (1/4 : ℝ))) / Real.log (1 / (1 - secondEval
            (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
            (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2))) = 1 := by
  have hpi1 : (stationaryVec pathAdj 1)⁻¹ - 1 = 1 := by
    have h : stationaryVec pathAdj 1 = 1/2 := by rw [path_pi_QA]; rfl
    rw [h]
    norm_num
  have hsqrt : Real.sqrt ((stationaryVec pathAdj 1)⁻¹ - 1) = 1 := by
    rw [hpi1, Real.sqrt_one]
  have hrate : (1 - secondEval (normalizedLaplacian pathAdj)
      (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
      (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) = 1/2 := by
    rw [path_secondEval_QA]
    norm_num
  have hceil : Nat.ceil (Real.log (Real.sqrt
        ((stationaryVec pathAdj 1)⁻¹ - 1) / (2 * (1/4 : ℝ)))
        / Real.log (1 / (1/2 : ℝ))) = 1 := by
    rw [show (2 * (1/4 : ℝ)) = 1/2 from by norm_num,
      show (1 : ℝ) / (1/2) = 2 from by norm_num, hsqrt,
      show (1 : ℝ) / (1/2) = 2 from by norm_num]
    have hlog2 : Real.log (2 : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    rw [div_self hlog2]
    norm_num
  rw [hrate, hceil]
  exact ⟨path_lazy_center_mix_eq_one_QA, rfl⟩

/-- **The ceiling computed with honest slack**: at the corner start and
`ε = 1/8` the ceiling's right side evaluates to exactly `3` against
the true `t_mix = 2` — the Cauchy–Schwarz conversion's price, on the
bipartite fixture. -/
theorem path_lazy_corner_ceiling_slack_QA :
    Nat.ceil (Real.log (Real.sqrt ((stationaryVec pathAdj 0)⁻¹ - 1)
        / (2 * (1/8 : ℝ))) / Real.log (1 / (1 - secondEval
          (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
          (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2))) = 3
      ∧ lazyWalkMixingTimeFrom pathAdj 0 (1/8) = 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hπ0 : (stationaryVec pathAdj 0)⁻¹ - 1 = 3 := by
    have h : stationaryVec pathAdj 0 = 1/4 := by rw [path_pi_QA]; rfl
    rw [h]
    norm_num
  have hratio : Real.sqrt ((stationaryVec pathAdj 0)⁻¹ - 1)
      / (2 * (1/8 : ℝ)) = 4 * Real.sqrt 3 := by
    rw [hπ0, show (2 * (1/8 : ℝ)) = 1/4 from by norm_num]
    refine (div_eq_iff (by norm_num)).mpr (by ring)
  have hrate : (1 - secondEval (normalizedLaplacian pathAdj)
      (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
      (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) = 1/2 := by
    rw [path_secondEval_QA]
    norm_num
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
  have hs3 : Real.sqrt 3 ≤ 2 := by
    have h := Real.sqrt_le_sqrt (by norm_num : (3 : ℝ) ≤ 4)
    rwa [show (4 : ℝ) = 2 ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)] at h
  have hup : (4 : ℝ) * Real.sqrt 3 ≤ 8 := by nlinarith [hs3]
  have hle : Real.log ((4 : ℝ) * Real.sqrt 3) / Real.log 2
      ≤ (3 : ℝ) := by
    rw [div_le_iff₀ hlog2, ← hlog8]
    exact Real.log_le_log (by positivity) hup
  have hsq3 : (Real.sqrt 3)^2 = 3 :=
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have h13 : (1 : ℝ) < Real.sqrt 3 := by
    nlinarith [hsq3, Real.sqrt_nonneg (3 : ℝ)]
  have hdown : (2 : ℝ) * Real.log 2
      < Real.log ((4 : ℝ) * Real.sqrt 3) := by
    rw [← hlog4]
    exact Real.log_lt_log (by norm_num : (0 : ℝ) < 4)
      (by nlinarith [h13])
  have hxle : Real.log (Real.sqrt ((stationaryVec pathAdj 0)⁻¹ - 1)
      / (2 * (1/8 : ℝ))) / Real.log (1 / (1 - secondEval
        (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2)) ≤ (3 : ℝ) := by
    rw [hrate, hone, hratio]
    exact hle
  have hltx : (2 : ℝ) < Real.log (Real.sqrt ((stationaryVec pathAdj 0)⁻¹
      - 1) / (2 * (1/8 : ℝ))) / Real.log (1 / (1 - secondEval
        (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2)) := by
    rw [hrate, hone, hratio]
    exact (lt_div_iff₀ hlog2).mpr hdown
  refine ⟨?_, path_lazy_corner_mix_eq_eighth_QA⟩
  have h2lt : (2 : ℕ) < Nat.ceil (Real.log (Real.sqrt
      ((stationaryVec pathAdj 0)⁻¹ - 1) / (2 * (1/8 : ℝ)))
      / Real.log (1 / (1 - secondEval (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2))) :=
    Nat.lt_ceil.mpr hltx
  have hle3 : Nat.ceil (Real.log (Real.sqrt ((stationaryVec pathAdj 0)⁻¹
      - 1) / (2 * (1/8 : ℝ))) / Real.log (1 / (1 - secondEval
        (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
        (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2))) ≤ 3 :=
    Nat.ceil_le.mpr hxle
  omega

/-- **The exact lazy mixing-time closed form on the edge**:
`t_mix_lazy(K₂, 0, 1/4) = 1` — the lazy walk mixes exactly in one step
on the chain where the plain object is junk. -/
theorem k2_lazy_mix_eq_fourth_QA :
    lazyWalkMixingTimeFrom k2Adj 0 (1/4) = 1 := by
  have hstays : ∀ k : ℕ, lazyWalkDistribution k2Adj (1 + k) 0
      = stationaryVec k2Adj :=
    fun k => lazyWalkDistribution_add_stationary k2Adj k2Adj_isSymm
      k2Adj_deg_pos 1 k 0 k2_lazy_law_one_QA
  have hcert : ∀ s : ℕ, 1 ≤ s →
      tvDistance (lazyWalkDistribution k2Adj s 0)
        (stationaryVec k2Adj) ≤ 1/4 := by
    intro s hs
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s = 1 + k := ⟨s - 1, by omega⟩
    rw [hk, hstays k]
    have hself : tvDistance (stationaryVec k2Adj)
        (stationaryVec k2Adj) = 0 := by simp [tvDistance]
    rw [hself]
    norm_num
  refine le_antisymm (lazyWalkMixingTimeFrom_le_of_cert k2Adj 0 1 hcert) ?_
  by_contra hne
  have hzero : lazyWalkMixingTimeFrom k2Adj 0 (1/4) = 0 := by omega
  have hspec := lazyWalkMixingTimeFrom_spec k2Adj 0 (ε := 1/4)
    ⟨1, hcert⟩ 0 (by omega)
  have hvec : (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ)
      = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  have hTV0 : tvDistance (lazyWalkDistribution k2Adj 0 0)
      (stationaryVec k2Adj) = 1/2 := by
    norm_num [tvDistance, lazyWalkDistribution_zero, hvec,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, k2_pi_QA, neg_sub, abs_of_neg, abs_of_nonneg]
  rw [hTV0] at hspec
  norm_num at hspec

/-- **The object-level periodicity contrast**: on the bipartite edge at
`ε = 1/8`, the *plain* object is the junk corner (`sInf ∅ = 0`, no
mixing — the witness set is empty because the plain TV is `1/2` at
every time) while the *lazy* object is the genuine `1`. The fix, read
at the object level every consumer consumes. -/
theorem k2_lazy_mix_contrast_QA :
    walkMixingTimeFrom k2Adj 0 (1/8) = 0
      ∧ lazyWalkMixingTimeFrom k2Adj 0 (1/8) = 1 := by
  have hempty : {t : ℕ | ∀ s : ℕ, t ≤ s →
      tvDistance (walkDistribution k2Adj s 0) (stationaryVec k2Adj)
        ≤ 1/8} = ∅ := by
    refine Set.eq_empty_iff_forall_not_mem.mpr ?_
    intro t ht
    have hbot := ht t (Nat.le_refl t)
    rw [k2_disc_tv_eq_QA t] at hbot
    norm_num at hbot
  have hstays : ∀ k : ℕ, lazyWalkDistribution k2Adj (1 + k) 0
      = stationaryVec k2Adj :=
    fun k => lazyWalkDistribution_add_stationary k2Adj k2Adj_isSymm
      k2Adj_deg_pos 1 k 0 k2_lazy_law_one_QA
  have hcert : ∀ s : ℕ, 1 ≤ s →
      tvDistance (lazyWalkDistribution k2Adj s 0)
        (stationaryVec k2Adj) ≤ 1/8 := by
    intro s hs
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s = 1 + k := ⟨s - 1, by omega⟩
    rw [hk, hstays k]
    have hself : tvDistance (stationaryVec k2Adj)
        (stationaryVec k2Adj) = 0 := by simp [tvDistance]
    rw [hself]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [walkMixingTimeFrom, hempty, Nat.sInf_empty]
  · refine le_antisymm (lazyWalkMixingTimeFrom_le_of_cert k2Adj 0 1 hcert) ?_
    by_contra hne
    have hzero : lazyWalkMixingTimeFrom k2Adj 0 (1/8) = 0 := by omega
    have hspec := lazyWalkMixingTimeFrom_spec k2Adj 0 (ε := 1/8)
      ⟨1, hcert⟩ 0 (by omega)
    have hvec : (Pi.single (0 : Fin 2) (1 : ℝ) : Fin 2 → ℝ)
        = ![1, 0] := by
      funext i
      fin_cases i <;> simp
    have hTV0 : tvDistance (lazyWalkDistribution k2Adj 0 0)
        (stationaryVec k2Adj) = 1/2 := by
      rw [lazyWalkDistribution_zero, hvec, tvDistance]
      norm_num [Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, k2_pi_QA, neg_sub,
        abs_of_neg, abs_of_nonneg]
    rw [hTV0] at hspec
    norm_num at hspec

/-- **The entrywise bound attained exactly at every time's mechanism**:
on `K₂` the rate is exactly `0` (pinned gap `λ₂ = 2`), and the lazy law
*is* `π` after one step — both sides of the entrywise lazy ceiling are
exactly zero. -/
theorem k2_lazy_entrywise_attained_QA :
    |lazyWalkDistribution k2Adj 1 0 1 - stationaryVec k2Adj 1|
      = (1 - secondEval (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm)
            (by norm_num) / 2) ^ 1
        * Real.sqrt (stationaryVec k2Adj 1
            * ((stationaryVec k2Adj 0)⁻¹ - 1)) := by
  rw [k2_lazy_law_one_QA]
  have hrate : (1 - secondEval (normalizedLaplacian k2Adj)
      (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm)
      (by norm_num) / 2) ^ 1 = 0 := by
    rw [k2_secondEval_QA]
    norm_num
  rw [hrate, sub_self, abs_zero, zero_mul]

/-- **The entrywise bound instance with slack witnessed**: on the
path's corner start at `t = 1`, target vertex `2`, the deviation is
`1/4` against the bound's `√3/4` — the pinned gap `λ₂ = 1` at the
intrinsic rate `1/2`. -/
theorem path_lazy_entrywise_slack_QA :
    |lazyWalkDistribution pathAdj 1 0 2 - stationaryVec pathAdj 2| = 1/4
      ∧ (1/4 : ℝ) < (1 - secondEval (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
            (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) ^ 1
        * Real.sqrt (stationaryVec pathAdj 2
            * ((stationaryVec pathAdj 0)⁻¹ - 1)) := by
  have hπ2 : stationaryVec pathAdj 2 = 1/4 := by rw [path_pi_QA]; rfl
  have hπ0 : stationaryVec pathAdj 0 = 1/4 := by rw [path_pi_QA]; rfl
  have hlaw : lazyWalkDistribution pathAdj 1 0 2 = 0 := by
    rw [path_lazy_corner_law_one_QA]
    simp [Matrix.cons_val_succ]
  have hrate : (1 - secondEval (normalizedLaplacian pathAdj)
      (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
      (by norm_num : 2 ≤ Fintype.card (Fin 3)) / 2) ^ 1 = (1/2 : ℝ) := by
    rw [path_secondEval_QA]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [hlaw, hπ2]
    simp
  · rw [hrate, hπ2, hπ0]
    have hC : (0 : ℝ) ≤ (1/4) * 3 := by norm_num
    have hnn : 0 ≤ Real.sqrt ((1/4 : ℝ) * 3) := Real.sqrt_nonneg _
    have hsq : ((1/2 : ℝ) * Real.sqrt ((1/4 : ℝ) * 3))^2
        = (1/4) * ((1/4 : ℝ) * 3) := by
      rw [mul_pow, Real.sq_sqrt hC]
      ring
    have h14 : (0 : ℝ) ≤ 1/4 := by norm_num
    nlinarith [hsq, hnn, h14]


end LazyMixingTimeQA

/-! ## The lazy family's adversarial fences (2026-09-02)

`proposals/adversarial-fences-lazy-family.md`: the audit-shaped
adversarial pass over the lazy family (`Mixing.lean`'s lazy sections
plus `Oversmoothing.lean`'s `LazyMixingTime` section), whose QA was
delivered 2026-09-01 by its own run and never independently re-read.
The audit found ten load-bearing hypotheses with no negative
witness anywhere in the repository — the `hd` clauses of
row-stochasticity, mass conservation, and the `t = 0` χ²
normalization (killed at the zero-degree fixture `zdAdj`, where the
`D⁻¹A` row is junk-zero); the `hnn` clauses of operator- and
law-nonnegativity (killed at the negative *off*-diagonal fixture
`negOffAdj` — the existing negative-diagonal `negDiagAdj` cannot kill
them, its off-diagonal `2` keeping every `P_L` entry nonnegative);
and the `hA` clauses of detailed balance, stationarity, and
attainment persistence (killed at the asymmetric fixture
`asymLoopAdj`, whose lazy law hits `π` *exactly* at `t = 1` so the
attainment hypothesis is genuine while the conclusion fails at
`t = 2`) — plus the two certificate clauses of the public lazy ℓ²(π)
contraction engine (the `hrate` clause killed on the triangle at the
genuine `3/2`-mode direction `g = (1, −1, 0)` with `r = 1/8` below
the mode's lazy factor `1/4`; the `hmode` clause killed on the edge
at `g = (1, 1)` with the genuine certificate `r = 0`). Each fence is
the negation of the conclusion at a specific instantiation with both
sides computed to numerals; each has an isolation companion proving
every other hypothesis genuine and the dropped one failing. -/

section LazyFences

/-- Generic extraction: the adjoint action on a point mass picks the
row — `((M)ᵀ *ᵥ Pi.single x 1) j = M x j`. -/
theorem transpose_mulVec_single_apply {V : Type*} [Fintype V]
    [DecidableEq V] (M : Matrix V V ℝ) (x j : V) :
    ((M)ᵀ *ᵥ (Pi.single x (1 : ℝ))) j = M x j := by
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ x _,
    if_pos (Finset.mem_univ x)]

/-- The lazy law after one step, adjoint form — the interface every
`ν₁` computation below consumes. -/
theorem lazyWalkDistribution_one {V : Type} [Fintype V] [DecidableEq V]
    (A : WAdj (V := V)) (x : V) :
    lazyWalkDistribution A 1 x
      = (lazyWalkTransitionMatrix A)ᵀ *ᵥ (Pi.single x (1 : ℝ)) := by
  simp only [lazyWalkDistribution, pow_one]

/-! ### Fixture 1: the zero-degree corner `zdAdj` (kills the `hd` clauses) -/

/-- Adjacency of the zero-degree fixture on `Fin 2`: symmetric,
nonnegative, `deg = (0, 1)` — every lazy-family hypothesis except
degree positivity holds. -/
def zdAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 0; 0, 1]

theorem zdAdj_isSymm : zdAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [zdAdj]

theorem zdAdj_nonneg (i j : Fin 2) : 0 ≤ zdAdj i j := by
  fin_cases i <;> fin_cases j <;> simp [zdAdj]

theorem zdAdj_00 : zdAdj 0 0 = 0 := by rw [zdAdj]; rfl
theorem zdAdj_01 : zdAdj 0 1 = 0 := by rw [zdAdj]; rfl
theorem zdAdj_10 : zdAdj 1 0 = 0 := by rw [zdAdj]; rfl
theorem zdAdj_11 : zdAdj 1 1 = 1 := by rw [zdAdj]; rfl

theorem zdAdj_deg_zero : deg zdAdj 0 = 0 := by
  simp only [deg, Fin.sum_univ_two, zdAdj_00, zdAdj_01]
  norm_num

theorem zdAdj_deg_one : deg zdAdj 1 = 1 := by
  simp only [deg, Fin.sum_univ_two, zdAdj_10, zdAdj_11]
  norm_num

/-- The dropped hypothesis genuinely fails: `deg 0 = 0`. -/
theorem zdAdj_deg_not_pos : ¬ (∀ i : Fin 2, 0 < deg zdAdj i) := by
  intro h
  have := h 0
  rw [zdAdj_deg_zero] at this
  norm_num at this

/-- The lazy operator at the zero-degree corner: the zero-degree row
is `1/2 · I` (its `D⁻¹A` half is junk-zero), the positive-degree row
is untouched. -/
theorem zdAdj_lazy_00 : lazyWalkTransitionMatrix zdAdj 0 0 = 1/2 := by
  rw [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply,
    zdAdj_deg_zero, inv_zero, zdAdj_00, zero_mul, if_pos rfl]
  norm_num

theorem zdAdj_lazy_01 : lazyWalkTransitionMatrix zdAdj 0 1 = 0 := by
  rw [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply,
    zdAdj_deg_zero, inv_zero, zdAdj_01, zero_mul,
    if_neg (by decide : ¬(0 : Fin 2) = 1)]
  norm_num

/-- **The `hd` fence for lazy row-stochasticity**: at the zero-degree
fixture (symmetric, nonnegative — every hypothesis except degree
positivity), the first entry of `P_L *ᵥ 1` is `1/2 ≠ 1`. -/
theorem zd_lazy_rowsum_fence_QA :
    ¬ (lazyWalkTransitionMatrix zdAdj *ᵥ (1 : Fin 2 → ℝ) = 1) := by
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Pi.one_apply, mul_one,
    Fin.sum_univ_two, zdAdj_lazy_00, zdAdj_lazy_01] at h0
  norm_num at h0

theorem zd_vol_QA : vol zdAdj (Finset.univ : Finset (Fin 2)) = 1 := by
  simp only [vol, Fin.sum_univ_two, zdAdj_deg_zero, zdAdj_deg_one]
  norm_num

theorem zd_pi_zero : stationaryVec zdAdj 0 = 0 := by
  simp only [stationaryVec, zd_vol_QA, zdAdj_deg_zero]
  norm_num

theorem zd_pi_one : stationaryVec zdAdj 1 = 1 := by
  simp only [stationaryVec, zd_vol_QA, zdAdj_deg_one]
  norm_num

/-- The lazy law from the isolated vertex after one step: the point
mass halved (the zero-degree walk row is junk-zero). -/
theorem zd_lazy_law_one_zero :
    lazyWalkDistribution zdAdj 1 0 0 = 1/2 := by
  rw [lazyWalkDistribution_one, transpose_mulVec_single_apply,
    zdAdj_lazy_00]

theorem zd_lazy_law_one_one :
    lazyWalkDistribution zdAdj 1 0 1 = 0 := by
  rw [lazyWalkDistribution_one, transpose_mulVec_single_apply,
    zdAdj_lazy_01]

/-- **The `hd` fence for lazy mass conservation**: at the zero-degree
fixture the lazy law's mass after one step is `1/2 ≠ 1`. -/
theorem zd_lazy_mass_fence_QA :
    ¬ (∑ i, lazyWalkDistribution zdAdj 1 0 i = 1) := by
  intro h
  rw [Fin.sum_univ_two, zd_lazy_law_one_zero, zd_lazy_law_one_one] at h
  norm_num at h

/-- **The `hd` fence for the `t = 0` χ² normalization**: at the
zero-degree corner `π 0 = 0`, the identity's right side is the junk
`0⁻¹ − 1 = −1` while the left side is `1`. -/
theorem zd_lazy_chi2_zero_fence_QA :
    ¬ (lazyChiSquareDistance zdAdj 0 0
        = (stationaryVec zdAdj 0)⁻¹ - 1) := by
  have hvec : (Pi.single (0 : Fin 2) (1 : ℝ)) = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  intro h
  rw [lazyChiSquareDistance, lazyWalkDistribution_zero, hvec] at h
  norm_num [stationaryVec, zd_vol_QA, zdAdj_deg_zero, zdAdj_deg_one,
    inv_zero, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one] at h

/-! ### Fixture 2: the negative off-diagonal corner `negOffAdj`
(kills the `hnn` clauses of nonnegativity) -/

/-- Adjacency of the negative off-diagonal fixture: symmetric,
`deg = (1, 1)` positive, negative off-diagonal entries — every lazy
hypothesis except entrywise nonnegativity. The existing `negDiagAdj`
(negative diagonal) cannot kill these clauses: its off-diagonal `2`
keeps every `P_L` entry nonnegative. -/
def negOffAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![2, -1; -1, 2]

theorem negOffAdj_isSymm : negOffAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [negOffAdj]

theorem negOffAdj_deg (i : Fin 2) : deg negOffAdj i = 1 := by
  rw [deg]
  fin_cases i <;> simp [negOffAdj, Fin.sum_univ_two] <;> norm_num

theorem negOffAdj_deg_pos (i : Fin 2) : 0 < deg negOffAdj i := by
  rw [negOffAdj_deg]
  norm_num

theorem negOffAdj_not_nonneg : ¬ (∀ i j : Fin 2, 0 ≤ negOffAdj i j) := by
  intro h
  have := h 0 1
  rw [negOffAdj] at this
  norm_num at this

/-- The lazy operator at the negative off-diagonal fixture:
`D⁻¹A = A` (unit degrees), so the off-diagonal entries are
`(−1 + 0)/2 = −1/2`. -/
theorem negOffAdj_lazy_01 :
    lazyWalkTransitionMatrix negOffAdj 0 1 = -1/2 := by
  rw [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply,
    negOffAdj_deg 0, inv_one]
  simp only [negOffAdj]
  rw [if_neg (by decide : ¬(0 : Fin 2) = 1)]
  norm_num

/-- **The `hnn` fence for lazy-operator nonnegativity**: at the
fixture (symmetric, positive degrees — every hypothesis except
nonnegativity), `P_L 0 1 = −1/2 < 0`. -/
theorem negOff_lazy_nonneg_fence_QA :
    ¬ (0 ≤ lazyWalkTransitionMatrix negOffAdj 0 1) := by
  rw [negOffAdj_lazy_01]
  norm_num

theorem negOff_lazy_law_one_one :
    lazyWalkDistribution negOffAdj 1 0 1 = -1/2 := by
  rw [lazyWalkDistribution_one, transpose_mulVec_single_apply,
    negOffAdj_lazy_01]

/-- **The `hnn` fence for lazy-law nonnegativity**: at the same
fixture, `ν₁ 0 1 = P_L 0 1 = −1/2 < 0`. -/
theorem negOff_lazy_law_nonneg_fence_QA :
    ¬ (0 ≤ lazyWalkDistribution negOffAdj 1 0 1) := by
  rw [negOff_lazy_law_one_one]
  norm_num

/-! ### Fixture 3: the asymmetric loop fixture `asymLoopAdj`
(kills the `hA` clauses) -/

/-- Adjacency of the asymmetric fixture: nonnegative with self-loops,
degrees `(6, 2)` positive, `A 0 1 = 3 ≠ 1 = A 1 0` — every lazy
hypothesis except symmetry. Designed so that the lazy law from `0`
hits `π = (3/4, 1/4)` *exactly* at `t = 1` (row `0` of `P_L` is
`π`), which makes the attainment-persistence hypothesis genuine
here. -/
def asymLoopAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![3, 3; 1, 1]

theorem asymLoopAdj_nonneg (i j : Fin 2) : 0 ≤ asymLoopAdj i j := by
  fin_cases i <;> fin_cases j <;> simp [asymLoopAdj]

theorem asymLoopAdj_00 : asymLoopAdj 0 0 = 3 := by rw [asymLoopAdj]; rfl
theorem asymLoopAdj_01 : asymLoopAdj 0 1 = 3 := by rw [asymLoopAdj]; rfl
theorem asymLoopAdj_10 : asymLoopAdj 1 0 = 1 := by rw [asymLoopAdj]; rfl
theorem asymLoopAdj_11 : asymLoopAdj 1 1 = 1 := by rw [asymLoopAdj]; rfl

theorem asymLoopAdj_deg_zero : deg asymLoopAdj 0 = 6 := by
  simp only [deg, Fin.sum_univ_two, asymLoopAdj_00, asymLoopAdj_01]
  norm_num

theorem asymLoopAdj_deg_one : deg asymLoopAdj 1 = 2 := by
  simp only [deg, Fin.sum_univ_two, asymLoopAdj_10, asymLoopAdj_11]
  norm_num

theorem asymLoopAdj_deg_pos (i : Fin 2) : 0 < deg asymLoopAdj i := by
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · rw [asymLoopAdj_deg_zero]; norm_num
  · rw [asymLoopAdj_deg_one]; norm_num

theorem asymLoopAdj_not_isSymm : ¬ asymLoopAdj.IsSymm := by
  intro h
  have hrow : asymLoopAdjᵀ 1 = asymLoopAdj 1 := congrFun h.eq 1
  have h10 := congrFun hrow 0
  simp only [Matrix.transpose_apply, asymLoopAdj_01, asymLoopAdj_10] at h10
  norm_num at h10

theorem asym_vol_QA : vol asymLoopAdj (Finset.univ : Finset (Fin 2)) = 8 := by
  simp only [vol, Fin.sum_univ_two, asymLoopAdj_deg_zero, asymLoopAdj_deg_one]
  norm_num

theorem asym_pi_zero : stationaryVec asymLoopAdj 0 = 3/4 := by
  simp only [stationaryVec, asym_vol_QA, asymLoopAdj_deg_zero]
  norm_num

theorem asym_pi_one : stationaryVec asymLoopAdj 1 = 1/4 := by
  simp only [stationaryVec, asym_vol_QA, asymLoopAdj_deg_one]
  norm_num

/-- The lazy operator at the asymmetric fixture, entrywise: both walk
rows are `(1/2, 1/2)` (each degree divides its own row exactly), so
`P_L` is the symmetric `!![3/4, 1/4; 1/4, 3/4]`. -/
theorem asymLoopAdj_lazy_00 : lazyWalkTransitionMatrix asymLoopAdj 0 0 = 3/4 := by
  rw [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply,
    asymLoopAdj_deg_zero, asymLoopAdj_00, if_pos rfl]
  norm_num

theorem asymLoopAdj_lazy_01 : lazyWalkTransitionMatrix asymLoopAdj 0 1 = 1/4 := by
  rw [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply,
    asymLoopAdj_deg_zero, asymLoopAdj_01,
    if_neg (by decide : ¬(0 : Fin 2) = 1), add_zero]
  norm_num

theorem asymLoopAdj_lazy_10 : lazyWalkTransitionMatrix asymLoopAdj 1 0 = 1/4 := by
  rw [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply,
    asymLoopAdj_deg_one, asymLoopAdj_10,
    if_neg (by decide : ¬(1 : Fin 2) = 0), add_zero]
  norm_num

theorem asymLoopAdj_lazy_11 : lazyWalkTransitionMatrix asymLoopAdj 1 1 = 3/4 := by
  rw [lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply,
    asymLoopAdj_deg_one, asymLoopAdj_11, if_pos rfl]
  norm_num

/-- **The `hA` fence for lazy detailed balance**: at the fixture
(nonnegative, positive degrees — every hypothesis except symmetry),
`π 0 · P_L 0 1 = 3/16 ≠ 1/16 = π 1 · P_L 1 0`. -/
theorem asym_lazy_balance_fence_QA :
    ¬ (stationaryVec asymLoopAdj 0 * lazyWalkTransitionMatrix asymLoopAdj 0 1
        = stationaryVec asymLoopAdj 1
            * lazyWalkTransitionMatrix asymLoopAdj 1 0) := by
  rw [asym_pi_zero, asymLoopAdj_lazy_01, asym_pi_one,
    asymLoopAdj_lazy_10]
  norm_num

theorem asym_lazy_row00 :
    lazyWalkTransitionMatrix asymLoopAdj 0 0 = stationaryVec asymLoopAdj 0 := by
  rw [asymLoopAdj_lazy_00, asym_pi_zero]

theorem asym_lazy_row01 :
    lazyWalkTransitionMatrix asymLoopAdj 0 1 = stationaryVec asymLoopAdj 1 := by
  rw [asymLoopAdj_lazy_01, asym_pi_one]

theorem asym_lazy_law_one_QA :
    lazyWalkDistribution asymLoopAdj 1 0 = stationaryVec asymLoopAdj := by
  funext j
  rw [lazyWalkDistribution_one, transpose_mulVec_single_apply]
  fin_cases j
  · exact asym_lazy_row00
  · exact asym_lazy_row01

/-- **The `hA` fence for lazy stationarity**: at the same fixture,
`(P_Lᵀ *ᵥ π) 0 = 5/8 ≠ 3/4 = π 0`. -/
theorem asym_lazy_stationary_fence_QA :
    ¬ ((lazyWalkTransitionMatrix asymLoopAdj)ᵀ *ᵥ stationaryVec asymLoopAdj
        = stationaryVec asymLoopAdj) := by
  intro h
  have h0 := congrFun h 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_two, asymLoopAdj_lazy_00, asymLoopAdj_lazy_10,
    asym_pi_zero, asym_pi_one] at h0
  norm_num at h0

/-- **The `hA` fence for attainment persistence**: the hypothesis is
*genuine* at this fixture (`ν₁ 0 = π` exactly, `asym_lazy_law_one_QA`),
yet the conclusion at `s = 1` fails — the law passes through `π` at
`t = 1` and leaves it at `t = 2`: `ν₂ 0 0 = 5/8 ≠ 3/4 = π 0`. -/
theorem asym_lazy_attain_fence_QA :
    ¬ (lazyWalkDistribution asymLoopAdj (1 + 1) 0
        = stationaryVec asymLoopAdj) := by
  intro h
  have hstep : lazyWalkDistribution asymLoopAdj (1 + 1) 0
      = (lazyWalkTransitionMatrix asymLoopAdj)ᵀ *ᵥ
          lazyWalkDistribution asymLoopAdj 1 0 :=
    lazyWalkDistribution_succ asymLoopAdj 1 0
  rw [hstep, asym_lazy_law_one_QA] at h
  exact asym_lazy_stationary_fence_QA h

/-! ### The fixture isolation companions

Each fence above drops exactly one hypothesis; the companions verify
that every *other* hypothesis of the family is genuine at the fixture
and the dropped one genuinely fails — the refutation isolates the
clause, not an artifact of a degenerate fixture. -/

theorem zd_fence_isolation_QA :
    zdAdj.IsSymm ∧ (∀ i j : Fin 2, 0 ≤ zdAdj i j)
      ∧ ¬ (∀ i : Fin 2, 0 < deg zdAdj i) :=
  ⟨zdAdj_isSymm, zdAdj_nonneg, zdAdj_deg_not_pos⟩

theorem negOff_fence_isolation_QA :
    negOffAdj.IsSymm ∧ (∀ i : Fin 2, 0 < deg negOffAdj i)
      ∧ ¬ (∀ i j : Fin 2, 0 ≤ negOffAdj i j) :=
  ⟨negOffAdj_isSymm, negOffAdj_deg_pos, negOffAdj_not_nonneg⟩

theorem asym_fence_isolation_QA :
    (∀ i j : Fin 2, 0 ≤ asymLoopAdj i j)
      ∧ (∀ i : Fin 2, 0 < deg asymLoopAdj i) ∧ ¬ asymLoopAdj.IsSymm :=
  ⟨asymLoopAdj_nonneg, asymLoopAdj_deg_pos, asymLoopAdj_not_isSymm⟩

/-- The attainment fence's hypothesis is genuine: the asymmetric
fixture's lazy law from `0` equals `π` at `t = 1` exactly. -/
theorem asym_attain_isolation_QA :
    (∀ i j : Fin 2, 0 ≤ asymLoopAdj i j)
      ∧ (∀ i : Fin 2, 0 < deg asymLoopAdj i) ∧ ¬ asymLoopAdj.IsSymm
      ∧ (lazyWalkDistribution asymLoopAdj 1 0 = stationaryVec asymLoopAdj) :=
  ⟨asymLoopAdj_nonneg, asymLoopAdj_deg_pos, asymLoopAdj_not_isSymm,
    asym_lazy_law_one_QA⟩

/-! ### The certificate fences for the lazy ℓ²(π) contraction engine -/

/-- The triangle's lazy operator action on the mode `g = (1, −1, 0)`:
`P_L *ᵥ g = (1/4) • g` — the eigenaction at the `3/2`-mode's lazy
factor `1 − (3/2)/2 = 1/4`. -/
theorem tri_lazy_mulVec_mode_QA :
    (lazyWalkTransitionMatrix triAdj ^ (1 : ℕ)) *ᵥ
        (![1, -1, 0] : Fin 3 → ℝ)
      = (1/4 : ℝ) • (![1, -1, 0] : Fin 3 → ℝ) := by
  rw [pow_one]
  funext j
  have hrow : ∀ j : Fin 3,
      (∑ k, triAdj j k * (![1, -1, 0] : Fin 3 → ℝ) k)
        = -((![1, -1, 0] : Fin 3 → ℝ) j) := by
    intro j
    fin_cases j <;> simp [triAdj_apply, Fin.sum_univ_three]
  have hdiag : ∀ j : Fin 3,
      (∑ k, ((if j = k then (1 : ℝ) else 0)
          * (![1, -1, 0] : Fin 3 → ℝ) k))
        = (![1, -1, 0] : Fin 3 → ℝ) j := by
    intro j
    rw [Finset.sum_eq_single
        (f := fun k => (if j = k then (1 : ℝ) else 0)
          * (![1, -1, 0] : Fin 3 → ℝ) k) j
      (fun k _ hk => by
        simp only []
        rw [if_neg (fun h => hk h.symm), zero_mul])
      (fun hj => absurd (Finset.mem_univ j) hj), if_pos rfl, one_mul]
  have hterm : ∀ k : Fin 3,
      ((1/2 : ℝ) * ((1/2) * triAdj j k
            + (if j = k then 1 else 0)))
          * (![1, -1, 0] : Fin 3 → ℝ) k
      = (1/4) * (triAdj j k * (![1, -1, 0] : Fin 3 → ℝ) k)
        + (1/2) * ((if j = k then (1 : ℝ) else 0)
            * (![1, -1, 0] : Fin 3 → ℝ) k) := by
    intro k
    ring_nf
  simp only [Matrix.mulVec, Matrix.dotProduct,
    lazyWalkTransitionMatrix_apply, walkTransitionMatrix_apply,
    triAdj_deg_eq, Pi.smul_apply, smul_eq_mul]
  norm_num
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, hrow j, hdiag j]
  ring_nf

/-- **The `hrate` fence for the lazy ℓ²(π) contraction**: on the
triangle at `g = (1, −1, 0)` (a genuine `3/2`-mode direction), the
certificate `r = 1/8` is strictly below the mode's lazy factor `1/4`,
and the conclusion is refuted: `LHS = 1/24 > 1/96 = RHS`. -/
theorem tri_lazy_rate_fence_QA :
    ¬ (∑ i, stationaryVec triAdj i
          * (((lazyWalkTransitionMatrix triAdj ^ (1 : ℕ)) *ᵥ
              (![1, -1, 0] : Fin 3 → ℝ)) i)^2
        ≤ (1/8 : ℝ) ^ (2 * 1)
          * ∑ i, stationaryVec triAdj i
              * ((![1, -1, 0] : Fin 3 → ℝ) i)^2) := by
  intro h
  rw [tri_lazy_mulVec_mode_QA] at h
  simp only [tri_pi_QA, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three,
    mul_pow, neg_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), pow_one] at h
  norm_num at h

/-- The conjugated vector at the triangle's mode direction: `√D *ᵥ w`
is `√2 • w` (the unit degrees make the conjugator scalar). -/
theorem tri_degreeSqrt_mulVec_eq (w : Fin 3 → ℝ) :
    degreeSqrt triAdj *ᵥ w = (Real.sqrt 2) • w := by
  funext i
  rw [degreeSqrt_mulVec_apply, triAdj_deg_eq]
  simp [Pi.smul_apply, smul_eq_mul]

/-- **The `hmode` companion for the triangle rate fence**: the mode
clause is *genuine* at the fixture — every zero-eigenvalue eigvec is
constant (`tri_kernel_const`), and the constant direction pairs to
zero against `√D *ᵥ g` (whose coordinate sum is `√2 · (1 − 1 + 0)`). -/
theorem tri_lazy_mode_genuine_QA :
    ∀ i : Fin 3, eigvalOf (normalizedLaplacian triAdj)
        (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i = 0 →
      Matrix.dotProduct
        (eigvecOf (normalizedLaplacian triAdj)
          (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i)
        (degreeSqrt triAdj *ᵥ (![1, -1, 0] : Fin 3 → ℝ)) = 0 := by
  intro i hi
  obtain ⟨c, hc⟩ := tri_kernel_const i hi
  have hsumg : ∑ x, ((Real.sqrt 2) • (![1, -1, 0] : Fin 3 → ℝ)) x = 0 := by
    simp [Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  rw [tri_degreeSqrt_mulVec_eq]
  simp only [Matrix.dotProduct_smul, smul_eq_mul, Matrix.dotProduct, hc]
  rw [← Finset.mul_sum, hsumg, mul_zero]

/-- The triangle has a genuine `3/2` mode (its trace is `3`, and
every eigenvalue is `0` or `3/2` — not all modes can vanish). -/
theorem tri_exists_pos_mode_QA :
    ∃ i : Fin 3, eigvalOf (normalizedLaplacian triAdj)
        (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i = 3/2 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ i : Fin 3, eigvalOf (normalizedLaplacian triAdj)
      (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i = 0 :=
    fun i => by
      rcases tri_eigvalOf_cases i with h0 | h32
      · exact h0
      · exact absurd h32 (hcon i)
  have htr := eigvalOf_sum_eq_trace (normalizedLaplacian triAdj)
    (normalizedLaplacian_symmetric triAdj triAdj_isSymm)
  rw [Finset.sum_congr rfl fun i _ => hall i, tri_trace] at htr
  norm_num at htr

/-- **The `hrate` companion for the triangle rate fence**: the rate
clause *fails* at the fixture — the `3/2` mode's lazy factor `1/4`
exceeds `r = 1/8`. -/
theorem tri_lazy_rate_fails_QA :
    ¬ (∀ i : Fin 3, eigvalOf (normalizedLaplacian triAdj)
          (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i ≠ 0 →
        |1 - eigvalOf (normalizedLaplacian triAdj)
            (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i / 2|
          ≤ 1/8) := by
  obtain ⟨i, hi⟩ := tri_exists_pos_mode_QA
  intro h
  have hle := h i (by rw [hi]; norm_num)
  rw [hi, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 - 3/2/2)] at hle
  norm_num at hle

/-! ### The K₂ mode fence -/

/-- **Every edge eigenvalue is `0` or `2`**: summing the eigen
equation over coordinates gives `μ · (∑ v) = 0` (the adjacency
column sums are `1`), and the quadratic form at the unit eigenvector
pins `μ = 2 − (∑ v)²` — either the eigenvalue vanishes or the
coordinate sum does. -/
theorem k2_eigvalOf_cases_QA (i : Fin 2) :
    eigvalOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i = 0
      ∨ eigvalOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i = 2 := by
  have hEV := (isHermitian_of_isSymm
    (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm)).mulVec_eigenvectorBasis i
  have hev : ∀ j : Fin 2,
      eigvalOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i
        * (eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)
      = (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)
        - ∑ k, k2Adj j k * (eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k) := by
    intro j
    have h := congrFun hEV j
    rw [k2_normalizedLaplacian_mulVec_apply _ j, Pi.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  have hunit : ∑ k, (eigvecOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k)
      * (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k) = 1 := by
    simpa using eigvecOf_inner _ _ i i
  have hcol : ∀ k : Fin 2, ∑ j, k2Adj j k = 1 := by
    intro k
    fin_cases k <;> simp [k2Adj_apply, Fin.sum_univ_two]
  have hsum : eigvalOf (normalizedLaplacian k2Adj)
      (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i
      * (∑ j, eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j) = 0 := by
    have h1 : ∑ j, eigvalOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i
          * (eigvecOf (normalizedLaplacian k2Adj)
              (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)
        = ∑ j, ((eigvecOf (normalizedLaplacian k2Adj)
              (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)
            - ∑ k, k2Adj j k * (eigvecOf (normalizedLaplacian k2Adj)
                (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k)) :=
      Finset.sum_congr rfl fun j _ => hev j
    rw [← Finset.mul_sum, Finset.sum_sub_distrib] at h1
    have h2 : ∑ j, ∑ k, k2Adj j k * (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k)
        = ∑ k, eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_congr rfl fun j _ => mul_comm (k2Adj j k)
          (eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k),
        ← Finset.mul_sum, hcol k, mul_one]
    rw [h2] at h1
    linarith
  have hrow0 : (∑ k, k2Adj 0 k * (eigvecOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k))
      = eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i 1 := by
    simp [k2Adj_apply, Fin.sum_univ_two]
  have hrow1 : (∑ k, k2Adj 1 k * (eigvecOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k))
      = eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i 0 := by
    simp [k2Adj_apply, Fin.sum_univ_two]
  have hcross : ∑ j, (eigvecOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)
      * (∑ k, k2Adj j k * (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k))
      = (∑ j, eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)^2 - 1 := by
    have hexp : ∀ F : Fin 2 → ℝ, ∑ j, F j = F 0 + F 1 := fun F =>
      Fin.sum_univ_two F
    have hunit2 : (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i 0)
        * (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i 0)
      + (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i 1)
        * (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i 1) = 1 := by
      rw [← hexp (fun k => (eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k)
          * (eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k))]
      exact hunit
    rw [hexp (fun j => (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)
        * (∑ k, k2Adj j k * (eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k))),
      hrow0, hrow1,
      hexp (fun j => eigvecOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)]
    linear_combination (-1) * hunit2
  have hqf : eigvalOf (normalizedLaplacian k2Adj)
      (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i
      = 2 - (∑ j, eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)^2 := by
    have hquad := quadForm_eigvecOf_self
      (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i
    have hsplit : quadForm (normalizedLaplacian k2Adj)
        (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i)
      = (∑ j, (eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)
          * (eigvecOf (normalizedLaplacian k2Adj)
              (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j))
        - ∑ j, (eigvecOf (normalizedLaplacian k2Adj)
              (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i j)
            * (∑ k, k2Adj j k * (eigvecOf (normalizedLaplacian k2Adj)
                (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k)) := by
      simp only [quadForm, Matrix.dotProduct,
        k2_normalizedLaplacian_mulVec_apply _, mul_sub,
        Finset.sum_sub_distrib]
    rw [hsplit, hunit, hcross] at hquad
    linarith
  rcases mul_eq_zero.mp hsum with hμ0 | hS0
  · exact Or.inl hμ0
  · refine Or.inr ?_
    rw [hS0] at hqf
    linarith

/-- **The `hmode` fence for the lazy ℓ²(π) contraction**: on the edge
at `g = (1, 1)` — the constant zero mode itself — with the genuine
certificate `r = 0` (the only nonzero mode is `μ = 2`, lazy factor
`0`), the conclusion is refuted: `P_L *ᵥ 1 = 1`, so `LHS = 1 > 0 =
RHS`. -/
theorem k2_lazy_mode_fence_QA :
    ¬ (∑ i, stationaryVec k2Adj i
          * (((lazyWalkTransitionMatrix k2Adj ^ (1 : ℕ)) *ᵥ
              (![1, 1] : Fin 2 → ℝ)) i)^2
        ≤ (0 : ℝ) ^ (2 * 1)
          * ∑ i, stationaryVec k2Adj i * ((![1, 1] : Fin 2 → ℝ) i)^2) := by
  intro h
  have hone : (![1, 1] : Fin 2 → ℝ) = 1 := by
    funext i
    fin_cases i <;> simp
  have hfix : (lazyWalkTransitionMatrix k2Adj ^ (1 : ℕ)) *ᵥ
      (![1, 1] : Fin 2 → ℝ) = (1 : Fin 2 → ℝ) := by
    rw [pow_one, hone, lazyWalkTransitionMatrix_mulVec_one k2Adj k2Adj_deg_pos]
  rw [hfix] at h
  simp only [k2_pi_QA, Fin.sum_univ_two, Pi.one_apply, one_pow, mul_one,
    zero_pow (by norm_num : (2 * 1 : ℕ) ≠ 0), zero_mul] at h
  norm_num at h

/-- **The `hrate` companion for the edge mode fence**: the rate clause
is *genuine* at `r = 0` — every nonzero eigenvalue is `2`, whose lazy
factor is exactly `0`. -/
theorem k2_lazy_rate_genuine_QA :
    ∀ i : Fin 2, eigvalOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i ≠ 0 →
      |1 - eigvalOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i / 2|
        ≤ 0 := by
  intro i hi
  rcases k2_eigvalOf_cases_QA i with h0 | h2
  · exact absurd h0 hi
  · rw [h2]
    norm_num

/-- **The `hmode` companion for the edge mode fence**: the mode clause
*fails* at the fixture — a kernel eigenvector exists, is constant
nonzero, and pairs to a nonzero value against `√D *ᵥ (1, 1) = (1, 1)`. -/
theorem k2_lazy_mode_fails_QA :
    ¬ (∀ i : Fin 2, eigvalOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i = 0 →
        Matrix.dotProduct
          (eigvecOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i)
          (degreeSqrt k2Adj *ᵥ (![1, 1] : Fin 2 → ℝ)) = 0) := by
  have hkern : (normalizedLaplacian k2Adj) *ᵥ (![1, 1] : Fin 2 → ℝ)
      = (0 : ℝ) • (![1, 1] : Fin 2 → ℝ) := by
    funext j
    rw [k2_normalizedLaplacian_mulVec_apply _ j]
    fin_cases j <;> simp [k2Adj_apply, Fin.sum_univ_two]
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul
    (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm)
    (by
      intro h0
      have h1 := congrFun h0 0
      simp at h1)
    hkern
  intro hcontra
  have hzero := hcontra i hi
  have hEV0 : (normalizedLaplacian k2Adj) *ᵥ
      (eigvecOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i)
      = (0 : ℝ) • (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i) := by
    have hEV := (isHermitian_of_isSymm
      (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm)).mulVec_eigenvectorBasis i
    have hz : ((isHermitian_of_isSymm
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm)).eigenvalues i) = 0 := hi
    rw [hz] at hEV
    exact hEV
  have hconst : (eigvecOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i) 0
      = (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i) 1 := by
    have h0 := congrFun hEV0 0
    rw [k2_normalizedLaplacian_mulVec_apply _ 0] at h0
    simp only [Fin.sum_univ_two, k2Adj_apply, Pi.smul_apply, smul_eq_mul,
      zero_mul, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, Fin.zero_ne_one, if_false, if_true,
      sub_zero, sub_self] at h0
    linarith
  have hunit : ∑ k, (eigvecOf (normalizedLaplacian k2Adj)
        (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k)
      * (eigvecOf (normalizedLaplacian k2Adj)
          (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i k) = 1 := by
    simpa using eigvecOf_inner _ _ i i
  rw [Fin.sum_univ_two, hconst] at hunit
  have hv1 : (eigvecOf (normalizedLaplacian k2Adj)
      (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i) 1 ≠ 0 := by
    intro hz
    rw [hz] at hunit
    norm_num at hunit
  rw [k2_degreeSqrt_mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    hconst] at hzero
  simp only [Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, mul_one] at hzero
  exact hv1 (by linarith)

end LazyFences

/-!
## The entropy family's adversarial fences, walk level (2026-09-03)

The audit continues at `Mixing.lean`'s entropy leg (Pinsker, the decay
form, the nonnegativity plumbing) and `Oversmoothing.lean`'s entropy
floor. Fixtures: the existing `negOffAdj`, `zdAdj`, `k2Adj`, `triAdj`
plus the new asymmetric swap `asymSwapAdj`.
-/

section EntropyFences

/-! ### Pinsker's two mass clauses -/

/-- The half-mass fixture on `Fin 2` (self-contained: `Entropy_QA`'s
fixtures are not imported here). -/
noncomputable def efHalf : Fin 2 → ℝ := fun _ => 1/2
noncomputable def efQuart : Fin 2 → ℝ := fun _ => 1/4
noncomputable def efOne : Fin 2 → ℝ := fun _ => 1

theorem efHalf_sum : ∑ i, efHalf i = 1 := by
  rw [Fin.sum_univ_two]; simp only [efHalf]; norm_num
theorem efQuart_nonneg : ∀ i, 0 ≤ efQuart i := fun _ => by norm_num [efQuart]
theorem efQuart_sum : ∑ i, efQuart i = 1/2 := by
  rw [Fin.sum_univ_two]; simp only [efQuart]; norm_num
theorem efHalf_pos : ∀ i, 0 < efHalf i := fun _ => by norm_num [efHalf]
theorem efHalf_sum' : ∑ i, efHalf i = 1 := efHalf_sum
theorem efOne_pos : ∀ i, 0 < efOne i := fun _ => by norm_num [efOne]
theorem efOne_sum : ∑ i, efOne i = 2 := by
  rw [Fin.sum_univ_two]; simp only [efOne]; norm_num

/-- The shared value pin: `D(1/4, 1/4 ‖ 1/2, 1/2) = −(1/2)·log 2`. -/
theorem ef_klDiv_quart_half :
    klDiv efQuart efHalf = -(1/2) * Real.log 2 := by
  have h1 : klTerm (1/4 : ℝ) (1/2 : ℝ) = (1/4) * (-(Real.log 2)) := by
    have hpos : (0:ℝ) < 1/4 := by norm_num
    have hval : (1/4 : ℝ) / (1/2 : ℝ) = (2:ℝ)⁻¹ := by norm_num
    simp only [klTerm, if_neg (ne_of_gt hpos), hval, Real.log_inv]
  rw [klDiv, Fin.sum_univ_two]
  simp only [efQuart, efHalf]
  rw [h1]
  ring

/-- The shared value pin: `D(1/2, 1/2 ‖ 1, 1) = −log 2`. -/
theorem ef_klDiv_half_one :
    klDiv efHalf efOne = -(Real.log 2) := by
  have h1 : klTerm (1/2 : ℝ) 1 = -(1/2) * Real.log 2 := by
    have hpos : (0:ℝ) < 1/2 := by norm_num
    have hlog : Real.log ((1:ℝ)/2) = -Real.log 2 := by
      rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from by norm_num, Real.log_inv]
    simp only [klTerm, if_neg (ne_of_gt hpos), div_one, hlog]
    ring
  rw [klDiv, Fin.sum_univ_two]
  simp only [efHalf, efOne]
  rw [h1]
  ring

/-- **The `hp1` fence for `tvDistance_le_sqrt_half_klDiv`** (Pinsker):
at `p = (1/4, 1/4)` (nonneg genuine, mass `1/2` dropped) against the
genuine `q = (1/2, 1/2)`, the divergence is negative, its junk square
root is `0`, and `TV = 1/4` — refuted. -/
theorem pinsker_pmass_fence_QA :
    ¬ (tvDistance efQuart efHalf
        ≤ Real.sqrt (klDiv efQuart efHalf / 2)) := by
  have hTV : tvDistance efQuart efHalf = 1/4 := by
    rw [tvDistance, Fin.sum_univ_two]
    simp only [efQuart, efHalf,
      abs_of_nonpos (by norm_num : (1/4:ℝ) - 1/2 ≤ 0)]
    norm_num
  intro h
  rw [hTV, ef_klDiv_quart_half] at h
  rw [Real.sqrt_eq_zero_of_nonpos (by
    have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [hlog])] at h
  norm_num at h

/-- **The `hq1` fence for Pinsker**: at the genuine
`p = (1/2, 1/2)` against `q = (1, 1)` (strictly positive, mass `2`
dropped), the divergence is `−log 2` and `TV = 1/2` — refuted. -/
theorem pinsker_qmass_fence_QA :
    ¬ (tvDistance efHalf efOne
        ≤ Real.sqrt (klDiv efHalf efOne / 2)) := by
  have hTV : tvDistance efHalf efOne = 1/2 := by
    rw [tvDistance, Fin.sum_univ_two]
    simp only [efHalf, efOne,
      abs_of_nonpos (by norm_num : (1/2:ℝ) - 1 ≤ 0)]
    norm_num
  intro h
  rw [hTV, ef_klDiv_half_one] at h
  rw [Real.sqrt_eq_zero_of_nonpos (by
    have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    nlinarith [hlog])] at h
  norm_num at h

/-! ### The asymmetric swap fixture `asymSwapAdj` (kills the `hA` of
mass conservation and of the entropy floor) -/

/-- Adjacency of the asymmetric swap: nonnegative, `deg = (2, 4)`
positive, `A 0 1 = 0 ≠ 4 = A 1 0` — every hypothesis except symmetry.
Two properties make it the fence fixture of choice: its normalized
Laplacian is `[[0,0],[−√2,1]]`, so `![0,1]` is a genuine `μ = 1`
eigenvector with all-radical-free arithmetic; and its walk Laplacian
`[[0,0],[−1,1]]` is idempotent, so the heat kernel is exactly
evaluable and the mass drift is visible in closed form. -/
def asymSwapAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![2, 0; 4, 0]

theorem asymSwapAdj_nonneg (i j : Fin 2) : 0 ≤ asymSwapAdj i j := by
  fin_cases i <;> fin_cases j <;> simp [asymSwapAdj]

theorem asymSwapAdj_00 : asymSwapAdj 0 0 = 2 := by rw [asymSwapAdj]; rfl
theorem asymSwapAdj_01 : asymSwapAdj 0 1 = 0 := by rw [asymSwapAdj]; rfl
theorem asymSwapAdj_10 : asymSwapAdj 1 0 = 4 := by rw [asymSwapAdj]; rfl
theorem asymSwapAdj_11 : asymSwapAdj 1 1 = 0 := by rw [asymSwapAdj]; rfl

theorem asymSwapAdj_deg_zero : deg asymSwapAdj 0 = 2 := by
  simp only [deg, Fin.sum_univ_two, asymSwapAdj_00, asymSwapAdj_01]
  norm_num

theorem asymSwapAdj_deg_one : deg asymSwapAdj 1 = 4 := by
  simp only [deg, Fin.sum_univ_two, asymSwapAdj_10, asymSwapAdj_11]
  norm_num

theorem asymSwapAdj_deg_pos (i : Fin 2) : 0 < deg asymSwapAdj i := by
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · rw [asymSwapAdj_deg_zero]; norm_num
  · rw [asymSwapAdj_deg_one]; norm_num

theorem asymSwapAdj_not_isSymm : ¬ asymSwapAdj.IsSymm := by
  intro h
  have hrow : asymSwapAdjᵀ 1 = asymSwapAdj 1 := congrFun h.eq 1
  have h10 := congrFun hrow 0
  simp only [Matrix.transpose_apply, asymSwapAdj_01, asymSwapAdj_10] at h10
  norm_num at h10

theorem asymSwap_vol_QA : vol asymSwapAdj (Finset.univ : Finset (Fin 2)) = 6 := by
  rw [vol, Fin.sum_univ_two, asymSwapAdj_deg_zero, asymSwapAdj_deg_one]
  norm_num

theorem asymSwap_pi_zero : stationaryVec asymSwapAdj 0 = 1/3 := by
  rw [stationaryVec, asymSwap_vol_QA, asymSwapAdj_deg_zero]
  norm_num

theorem asymSwap_pi_one : stationaryVec asymSwapAdj 1 = 2/3 := by
  rw [stationaryVec, asymSwap_vol_QA, asymSwapAdj_deg_one]
  norm_num

/-- The swap's walk matrix: `P = [[1,0],[1,0]]`. -/
theorem asym_walk_00 : walkTransitionMatrix asymSwapAdj 0 0 = 1 := by
  rw [walkTransitionMatrix_apply, asymSwapAdj_deg_zero, asymSwapAdj_00]
  norm_num

theorem asym_walk_01 : walkTransitionMatrix asymSwapAdj 0 1 = 0 := by
  rw [walkTransitionMatrix_apply, asymSwapAdj_deg_zero, asymSwapAdj_01]
  norm_num

theorem asym_walk_10 : walkTransitionMatrix asymSwapAdj 1 0 = 1 := by
  rw [walkTransitionMatrix_apply, asymSwapAdj_deg_one, asymSwapAdj_10]
  norm_num

theorem asym_walk_11 : walkTransitionMatrix asymSwapAdj 1 1 = 0 := by
  rw [walkTransitionMatrix_apply, asymSwapAdj_deg_one, asymSwapAdj_11]
  norm_num

theorem asym_L_00 : walkLaplacian asymSwapAdj 0 0 = 0 := by
  simp only [walkLaplacian, Matrix.sub_apply, Matrix.one_apply, asym_walk_00]
  rw [if_true]
  norm_num

theorem asym_L_01 : walkLaplacian asymSwapAdj 0 1 = 0 := by
  simp only [walkLaplacian, Matrix.sub_apply, Matrix.one_apply, asym_walk_01]
  rw [if_neg (by decide : ¬(0 : Fin 2) = 1)]
  norm_num

theorem asym_L_10 : walkLaplacian asymSwapAdj 1 0 = -1 := by
  simp only [walkLaplacian, Matrix.sub_apply, Matrix.one_apply, asym_walk_10]
  rw [if_neg (by decide : ¬(1 : Fin 2) = 0)]
  norm_num

theorem asym_L_11 : walkLaplacian asymSwapAdj 1 1 = 1 := by
  simp only [walkLaplacian, Matrix.sub_apply, Matrix.one_apply, asym_walk_11]
  rw [if_true]
  norm_num

/-- The swap's walk Laplacian is idempotent. -/
theorem asym_L_sq :
    (walkLaplacian asymSwapAdj) * (walkLaplacian asymSwapAdj)
      = 1 • (walkLaplacian asymSwapAdj) := by
  ext i j
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h] <;>
    rcases (show j = 0 ∨ j = 1 by omega) with h' | h' <;> rw [h']
  all_goals
    simp only [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.smul_apply]
  · rw [asym_L_00, asym_L_01, asym_L_10]; norm_num
  · rw [asym_L_00, asym_L_01, asym_L_11]; norm_num
  · rw [asym_L_10, asym_L_00, asym_L_11]; norm_num
  · rw [asym_L_10, asym_L_01, asym_L_11]; norm_num

theorem asym_density_zero :
    walkDensity asymSwapAdj 0 0 = ![3, 0] := by
  have hlaw : (Pi.single (0 : Fin 2) (1 : ℝ)) = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · rw [walkDensity, walkDistribution_zero, hlaw]
    simp only [Matrix.cons_val_zero, Matrix.head_cons, asymSwap_pi_zero]
    norm_num
  · rw [walkDensity, walkDistribution_zero, hlaw]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      asymSwap_pi_one]
    norm_num

/-- The swap's idempotent walk Laplacian makes the heat kernel exactly
evaluable: `exp(−L) = 1 + (1 − e^{−1}) • (−L)`. -/
theorem asym_heat_one :
    walkHeatKernel asymSwapAdj 1
      = 1 + ((1 - Real.exp (-(1:ℝ))))
          • (-(walkLaplacian asymSwapAdj)) := by
  have hsq : (-(walkLaplacian asymSwapAdj))
      * (-(walkLaplacian asymSwapAdj))
      = (-1 : ℝ) • (-(walkLaplacian asymSwapAdj)) := by
    rw [neg_mul_neg, asym_L_sq, one_smul, neg_smul, one_smul, neg_neg]
  rw [walkHeatKernel, one_smul]
  rw [exp_eq_one_add_of_mul_self_eq_smul _ (by norm_num) hsq]
  ring_nf

/-- The exponent's action on the start density: `−L *ᵥ (3, 0) = (0, −3)`. -/
theorem asym_negL_mulVec :
    (-(walkLaplacian asymSwapAdj)) *ᵥ (![3, 0] : Fin 2 → ℝ)
      = ![0, 3] := by
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.neg_apply, Pi.neg_apply, Matrix.cons_val_zero,
      Matrix.head_cons]
    rw [asym_L_00, asym_L_01]
    norm_num
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.neg_apply, Pi.neg_apply, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
    rw [asym_L_10, asym_L_11]
    norm_num

/-- The swap's continuous density at `t = 1` from `0`:
`(3, 3(1 − e^{−1}))`. -/
theorem asym_cont_density_one :
    contWalkDensity asymSwapAdj 1 0 = ![3, 3 * (1 - Real.exp (-(1:ℝ)))] := by
  rw [contWalkDensity, asym_density_zero, asym_heat_one,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
    asym_negL_mulVec]
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, Pi.smul_apply,
      smul_eq_mul, Pi.add_apply]
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring

/-- The swap's continuous law at `t = 1` from `0`:
`(1, 2(1 − e^{−1}))` — mass `3 − 2e^{−1} ≠ 1`. -/
theorem asym_cont_law_one :
    contWalkDistribution asymSwapAdj 1 0
      = ![1, 2 * (1 - Real.exp (-(1:ℝ)))] := by
  funext i
  rw [contWalkDistribution, asym_cont_density_one]
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, asymSwap_pi_zero]
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      asymSwap_pi_one]
    ring

/-- **The `hA` fence for `sum_contWalkDistribution`**: at the asymmetric
swap (nonnegative, positive degrees — every hypothesis except
symmetry), the law's mass at `t = 1` is `3 − 2e^{−1} ≠ 1` — refuted. -/
theorem sum_contWalkDistribution_hA_fence_QA :
    ¬ (∑ i, contWalkDistribution asymSwapAdj 1 0 i = 1) := by
  intro h
  rw [Fin.sum_univ_two, asym_cont_law_one] at h
  simp only [Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one] at h
  have hE : Real.exp (-(1:ℝ)) < 1 := by
    have := Real.exp_lt_exp.mpr (by norm_num : -(1:ℝ) < 0)
    rwa [Real.exp_zero] at this
  have hpos : (0:ℝ) < Real.exp (-(1:ℝ)) := Real.exp_pos _
  nlinarith [hE, hpos]


/-! ### The negative off-diagonal fixture `negOffAdj` (kills the `hnn`
of the plain density and the continuous density/law) -/

theorem negOff_vol_QA : vol negOffAdj (Finset.univ : Finset (Fin 2)) = 2 := by
  rw [vol, Fin.sum_univ_two, negOffAdj_deg 0, negOffAdj_deg 1]
  norm_num

theorem negOff_pi (i : Fin 2) : stationaryVec negOffAdj i = 1/2 := by
  rw [stationaryVec, negOff_vol_QA, negOffAdj_deg i]

theorem negOff_00 : negOffAdj 0 0 = 2 := by rw [negOffAdj]; rfl
theorem negOff_01 : negOffAdj 0 1 = -1 := by rw [negOffAdj]; rfl
theorem negOff_10 : negOffAdj 1 0 = -1 := by rw [negOffAdj]; rfl
theorem negOff_11 : negOffAdj 1 1 = 2 := by rw [negOffAdj]; rfl

theorem negOff_L00 : walkLaplacian negOffAdj 0 0 = -1 := by
  rw [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    walkTransitionMatrix_apply, negOffAdj_deg 0, negOff_00, if_pos rfl,
    inv_one]
  norm_num

theorem negOff_L01 : walkLaplacian negOffAdj 0 1 = 1 := by
  rw [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    walkTransitionMatrix_apply, negOffAdj_deg 0, negOff_01,
    if_neg (by decide : ¬(0 : Fin 2) = 1), inv_one]
  norm_num

theorem negOff_L10 : walkLaplacian negOffAdj 1 0 = 1 := by
  rw [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    walkTransitionMatrix_apply, negOffAdj_deg 1, negOff_10,
    if_neg (by decide : ¬(1 : Fin 2) = 0), inv_one]
  norm_num

theorem negOff_L11 : walkLaplacian negOffAdj 1 1 = -1 := by
  rw [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    walkTransitionMatrix_apply, negOffAdj_deg 1, negOff_11, if_pos rfl,
    inv_one]
  norm_num

/-- The plain one-step law from `0` at the negative off-diagonal
fixture: the walk matrix is `D⁻¹A = A` (unit degrees), so the law is
row `0` of `A`: `(2, −1)` — a mass-`1` vector with a negative entry. -/
theorem negOff_dist_one :
    walkDistribution negOffAdj 1 0 = ![2, -1] := by
  rw [walkDistribution, pow_one]
  funext i
  rw [transpose_mulVec_single_apply]
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · rw [walkTransitionMatrix_apply, negOffAdj_deg 0, negOff_00, inv_one]
    simp only [Matrix.cons_val_zero, one_mul]
  · rw [walkTransitionMatrix_apply, negOffAdj_deg 0, negOff_01, inv_one]
    norm_num
/-- **The `hnn` fence for `walkDensity_nonneg`**: at the fixture
(symmetric, positive degrees — every hypothesis except entrywise
nonnegativity), `h(1) = ν₁ 1 / π 1 = −1/(1/2) = −2` — refuted. -/
theorem walkDensity_nonneg_hnn_fence_QA :
    ¬ (0 ≤ walkDensity negOffAdj 1 0 1) := by
  rw [walkDensity, negOff_dist_one, negOff_pi 1]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
  norm_num

theorem negOff_negL_sq :
    (-(walkLaplacian negOffAdj)) * (-(walkLaplacian negOffAdj))
      = (2 : ℝ) • (-(walkLaplacian negOffAdj)) := by
  ext i j
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h] <;>
    rcases (show j = 0 ∨ j = 1 by omega) with h' | h' <;> rw [h']
  all_goals
    simp only [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.smul_apply, Matrix.neg_apply]
  · rw [negOff_L00, negOff_L01, negOff_L10]; norm_num
  · rw [negOff_L00, negOff_L01, negOff_L11]; norm_num
  · rw [negOff_L10, negOff_L00, negOff_L11]; norm_num
  · rw [negOff_L10, negOff_L01, negOff_L11]; norm_num

theorem negOff_density_zero :
    walkDensity negOffAdj 0 0 = ![2, 0] := by
  have hlaw : (Pi.single (0 : Fin 2) (1 : ℝ)) = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h] <;>
    rw [walkDensity, walkDistribution_zero, hlaw]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, negOff_pi 0]
    norm_num
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      negOff_pi 1]
    norm_num

/-- The negative off-diagonal heat kernel at `t = 1` in closed form:
`exp(−L) = 1 + ((e² − 1)/2) • (−L)`. -/
theorem negOff_heat_one :
    walkHeatKernel negOffAdj 1
      = 1 + ((Real.exp 2 - 1) / 2) • (-(walkLaplacian negOffAdj)) := by
  rw [walkHeatKernel, one_smul]
  rw [exp_eq_one_add_of_mul_self_eq_smul _
    (show (2:ℝ) ≠ 0 by norm_num) negOff_negL_sq]

theorem negOff_negL_mulVec :
    (-(walkLaplacian negOffAdj)) *ᵥ (![2, 0] : Fin 2 → ℝ)
      = ![2, -2] := by
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.neg_apply, Pi.neg_apply, Matrix.cons_val_zero,
      Matrix.head_cons]
    rw [negOff_L00, negOff_L01]
    norm_num
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.neg_apply, Pi.neg_apply, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
    rw [negOff_L10, negOff_L11]
    norm_num

theorem negOff_cont_density_one :
    contWalkDensity negOffAdj 1 0
      = ![1 + Real.exp 2, 1 - Real.exp 2] := by
  rw [contWalkDensity, negOff_density_zero, negOff_heat_one,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
    negOff_negL_mulVec]
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, Pi.smul_apply,
      smul_eq_mul, Pi.add_apply]
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring

/-- **The `hnn` fence for `contWalkDensity_nonneg`**: at the fixture
(symmetric, positive degrees — every hypothesis except entrywise
nonnegativity), the heat kernel's off-diagonal entry is
`(1 − e²)/2 < 0`, so `h(1) = 1 − e² < 0` — refuted. -/
theorem contWalkDensity_nonneg_hnn_fence_QA :
    ¬ (0 ≤ contWalkDensity negOffAdj 1 0 1) := by
  rw [negOff_cont_density_one]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
  have h1 : (1:ℝ) < Real.exp 2 := by
    have := Real.exp_lt_exp.mpr (by norm_num : (0:ℝ) < 2)
    rwa [Real.exp_zero] at this
  linarith

/-- **The `hnn` fence for `contWalkDistribution_nonneg`**: the law is
`π • h`, so `ν(1) = (1/2)(1 − e²) < 0` — refuted. -/
theorem contWalkDistribution_nonneg_hnn_fence_QA :
    ¬ (0 ≤ contWalkDistribution negOffAdj 1 0 1) := by
  rw [contWalkDistribution, negOff_cont_density_one, negOff_pi 1]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    Pi.smul_apply, smul_eq_mul]
  have h1 : (1:ℝ) < Real.exp 2 := by
    have := Real.exp_lt_exp.mpr (by norm_num : (0:ℝ) < 2)
    rwa [Real.exp_zero] at this
  linarith

/-! ### The `K₂` fixture (kills the `ht` of the continuous nonneg
plumbing, at negative time) -/

theorem k2_L00 : walkLaplacian k2Adj 0 0 = 1 := by
  rw [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    walkTransitionMatrix_apply, k2Adj_deg_eq 0, k2Adj_apply,
    if_pos rfl, inv_one]
  norm_num

theorem k2_L01 : walkLaplacian k2Adj 0 1 = -1 := by
  rw [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    walkTransitionMatrix_apply, k2Adj_deg_eq 0, k2Adj_apply,
    if_neg (by decide : ¬(0 : Fin 2) = 1), inv_one]
  norm_num

theorem k2_L10 : walkLaplacian k2Adj 1 0 = -1 := by
  rw [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    walkTransitionMatrix_apply, k2Adj_deg_eq 1, k2Adj_apply,
    if_neg (by decide : ¬(1 : Fin 2) = 0), inv_one]
  norm_num

theorem k2_L11 : walkLaplacian k2Adj 1 1 = 1 := by
  rw [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    walkTransitionMatrix_apply, k2Adj_deg_eq 1, k2Adj_apply,
    if_pos rfl, inv_one]
  norm_num

theorem k2_L_sq :
    (walkLaplacian k2Adj) * (walkLaplacian k2Adj)
      = (2 : ℝ) • (walkLaplacian k2Adj) := by
  ext i j
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h] <;>
    rcases (show j = 0 ∨ j = 1 by omega) with h' | h' <;> rw [h']
  all_goals
    simp only [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.smul_apply]
  · rw [k2_L00, k2_L01, k2_L10]; norm_num
  · rw [k2_L00, k2_L01, k2_L11]; norm_num
  · rw [k2_L10, k2_L00, k2_L11]; norm_num
  · rw [k2_L10, k2_L01, k2_L11]; norm_num

/-- The edge heat kernel at time `t = −1` in closed form: the exponent
is `+L` (the backward semigroup), so `exp(L) = 1 + ((e²−1)/2) • L`. -/
theorem k2_heat_neg_one :
    walkHeatKernel k2Adj (-(1:ℝ))
      = 1 + ((Real.exp 2 - 1) / 2) • (walkLaplacian k2Adj) := by
  rw [walkHeatKernel, neg_smul, one_smul, neg_neg]
  rw [exp_eq_one_add_of_mul_self_eq_smul _
    (show (2:ℝ) ≠ 0 by norm_num) k2_L_sq]

theorem k2_L_mulVec :
    (walkLaplacian k2Adj) *ᵥ (![2, 0] : Fin 2 → ℝ) = ![2, -2] := by
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons]
    rw [k2_L00]
    norm_num
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    rw [k2_L10, k2_L11]
    norm_num

theorem k2_density_zero :
    walkDensity k2Adj 0 0 = ![2, 0] := by
  have hlaw : (Pi.single (0 : Fin 2) (1 : ℝ)) = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h] <;>
    rw [walkDensity, walkDistribution_zero, hlaw]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, k2_pi_QA 0]
    norm_num
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      k2_pi_QA 1]
    norm_num

theorem k2_cont_density_neg_one :
    contWalkDensity k2Adj (-(1:ℝ)) 0
      = ![1 + Real.exp 2, 1 - Real.exp 2] := by
  rw [contWalkDensity, k2_density_zero, k2_heat_neg_one,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
    k2_L_mulVec]
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, Pi.smul_apply,
      smul_eq_mul, Pi.add_apply]
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring

/-- **The `ht` fence for `contWalkDensity_nonneg`**: on the genuine
edge (symmetric, nonnegative, positive degrees) at the negative time
`t = −1`, the backward heat kernel's diagonal contraction makes
`h(0) = 1 + e²` and `h(1) = 1 − e² < 0` — refuted. -/
theorem contWalkDensity_nonneg_ht_fence_QA :
    ¬ (0 ≤ contWalkDensity k2Adj (-(1:ℝ)) 0 1) := by
  rw [k2_cont_density_neg_one]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
  have h1 : (1:ℝ) < Real.exp 2 := by
    have := Real.exp_lt_exp.mpr (by norm_num : (0:ℝ) < 2)
    rwa [Real.exp_zero] at this
  linarith

/-- **The `ht` fence for `contWalkDistribution_nonneg`**: the law
`ν(1) = π(1)·h(1) = (1/2)(1 − e²) < 0` — refuted. -/
theorem contWalkDistribution_nonneg_ht_fence_QA :
    ¬ (0 ≤ contWalkDistribution k2Adj (-(1:ℝ)) 0 1) := by
  rw [contWalkDistribution, k2_cont_density_neg_one, k2_pi_QA 1]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
    Pi.smul_apply, smul_eq_mul]
  have h1 : (1:ℝ) < Real.exp 2 := by
    have := Real.exp_lt_exp.mpr (by norm_num : (0:ℝ) < 2)
    rwa [Real.exp_zero] at this
  linarith

/-! ### The zero-degree fixture `zdAdj` (kills the `hd` of mass
conservation and of the continuous decay form) -/



theorem zd_density_zero :
    walkDensity zdAdj 0 0 = ![0, 0] := by
  have hlaw : (Pi.single (0 : Fin 2) (1 : ℝ)) = ![1, 0] := by
    funext i
    fin_cases i <;> simp
  funext i
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h] <;>
    rw [walkDensity, walkDistribution_zero, hlaw]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, zd_pi_zero,
      div_zero]
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
    norm_num

/-- The continuous law at the zero-degree corner is the junk zero
vector: the start density is junk (`1/0 = 0`) and the heat kernel
cannot revive it. -/
theorem zd_cont_law_zero :
    contWalkDistribution zdAdj 1 0 = 0 := by
  have h0 : contWalkDensity zdAdj 1 0 = 0 := by
    rw [contWalkDensity, zd_density_zero]
    have hz : (![0, 0] : Fin 2 → ℝ) = 0 := by
      funext i
      fin_cases i <;> rfl
    rw [hz, Matrix.mulVec_zero]
  funext i
  rw [contWalkDistribution, h0]
  simp [Pi.zero_apply]

/-- **The `hd` fence for `sum_contWalkDistribution`**: at the
zero-degree fixture (symmetric, nonnegative — every hypothesis except
positive degrees), the law's mass is `0 ≠ 1` — refuted. -/
theorem sum_contWalkDistribution_hd_fence_QA :
    ¬ (∑ i, contWalkDistribution zdAdj 1 0 i = 1) := by
  intro h
  rw [zd_cont_law_zero] at h
  simp only [Pi.zero_apply, Finset.sum_const_zero] at h
  exact absurd h (by norm_num)

theorem zd_klDiv_cont_law_zero :
    klDiv (contWalkDistribution zdAdj 1 0) (stationaryVec zdAdj) = 0 := by
  rw [zd_cont_law_zero, klDiv]
  exact Finset.sum_eq_zero fun i _ => by simp [klTerm]

/-- **The `hd` fence for `klDiv_contWalkDistribution_le`**: at the same
fixture (with `hcard` genuine — `Fin 2`), the decay bound's right side
carries the junk `((π 0)⁻¹ − 1) = (0⁻¹ − 1) = −1`, so the statement
reads `0 ≤ −e^{−2λ₂}` — refuted, whatever `λ₂` is (`exp_pos`). -/
theorem klDiv_contWalkDistribution_le_hd_fence_QA :
    ¬ (klDiv (contWalkDistribution zdAdj 1 0) (stationaryVec zdAdj)
        ≤ Real.exp (-(2 * (1:ℝ) * secondEval (normalizedLaplacian zdAdj)
              (normalizedLaplacian_symmetric zdAdj zdAdj_isSymm)
              (by norm_num : 2 ≤ Fintype.card (Fin 2))))
          * ((stationaryVec zdAdj 0)⁻¹ - 1)) := by
  intro h
  rw [zd_klDiv_cont_law_zero] at h
  simp only [stationaryVec, zd_vol_QA, zdAdj_deg_zero, zero_div, inv_zero,
    zero_sub] at h
  have hpos : (0:ℝ) < Real.exp (-(2 * (1:ℝ) * secondEval
      (normalizedLaplacian zdAdj)
      (normalizedLaplacian_symmetric zdAdj zdAdj_isSymm)
      (by norm_num : 2 ≤ Fintype.card (Fin 2)))) := Real.exp_pos _
  have : Real.exp (-(2 * (1:ℝ) * secondEval (normalizedLaplacian zdAdj)
      (normalizedLaplacian_symmetric zdAdj zdAdj_isSymm)
      (by norm_num : 2 ≤ Fintype.card (Fin 2)))) * (-1) < 0 := by
    nlinarith [hpos]
  linarith

/-! ### The triangle (kills the `hrate` of the entropy decay form) -/

/-- **The `hrate` companion**: the rate certificate at `r = 1/8` *fails*
on the triangle — the `3/2` mode's factor `|1 − 3/2| = 1/2` exceeds
`1/8` (witnessed by `tri_exists_pos_mode_QA`). -/
theorem tri_kl_rate_fails_QA :
    ¬ (∀ i : Fin 3, eigvalOf (normalizedLaplacian triAdj)
          (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i ≠ 0 →
        |1 - eigvalOf (normalizedLaplacian triAdj)
            (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i|
          ≤ 1/8) := by
  obtain ⟨i, hi⟩ := tri_exists_pos_mode_QA
  intro h
  have hle := h i (by rw [hi]; norm_num)
  rw [hi, abs_of_nonpos (by norm_num : (1:ℝ) - 3/2 ≤ 0)] at hle
  norm_num at hle

/-- **The `hrate` fence for `klDiv_walkDistribution_le`**: on the
genuine triangle (symmetric, nonnegative, positive degrees, connected)
at `r = 1/8` (a failing certificate), the dropped statement reads
`log(3/2) ≤ (1/8)²·2 = 1/32` — refuted by Gibbs (`log(3/2) ≥ 1/3`). -/
theorem klDiv_walkDistribution_le_hrate_fence_QA :
    ¬ (klDiv (walkDistribution triAdj 1 0) (stationaryVec triAdj)
        ≤ (1/8 : ℝ) ^ (2 * 1) * ((stationaryVec triAdj 0)⁻¹ - 1)) := by
  intro h
  rw [tri_kl_one_QA, tri_pi_QA (0 : Fin 3)] at h
  norm_num at h
  have hgibbs : (1:ℝ) - (3/2 : ℝ)⁻¹ ≤ Real.log (3/2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hinv : (3/2 : ℝ)⁻¹ = 2/3 := by norm_num
  rw [hinv] at hgibbs
  linarith

/-! ### The entropy floor's four fences -/

/-- The kernel eigenvector pin: the constant vector is a genuine
`μ = 0` eigenvector of the triangle's normalized Laplacian. -/
theorem tri_nL_mulVec_one :
    normalizedLaplacian triAdj *ᵥ (![1, 1, 1] : Fin 3 → ℝ)
      = (0 : ℝ) • (![1, 1, 1] : Fin 3 → ℝ) := by
  have h : ∀ j : Fin 3, (normalizedLaplacian triAdj *ᵥ
      (![1, 1, 1] : Fin 3 → ℝ)) j = 0 := by
    intro j
    rw [tri_normalizedLaplacian_mulVec_apply]
    fin_cases j <;>
      simp [triAdj_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.tail_cons] <;> norm_num
  funext j
  rw [h j, Pi.smul_apply, smul_eq_mul, zero_mul]

/-- The constant vector's conjugate on the triangle: every entry
`(√2)⁻¹` — so the sup bound is attained with equality at `c = (√2)⁻¹`. -/
theorem tri_vconj_one (j : Fin 3) :
    (degreeInvSqrt triAdj *ᵥ (![1, 1, 1] : Fin 3 → ℝ)) j
      = (Real.sqrt 2)⁻¹ := by
  rw [degreeInvSqrt_mulVec_apply, triAdj_deg_eq]
  fin_cases j <;> simp

/-- **The `hμ` fence for `klDiv_walkDistribution_ge_of_eigenpair`**: at
the kernel eigenpair `(0, ![1,1,1])` — a genuine eigenpair, every other
ingredient genuine (the sup bound attained with equality, `0 < c`) —
the dropped statement reads `2·((1/2)·1²·1)² = 1/2 ≤ D(ν₂) =
(1/2)·log(9/8) < 1/16` — refuted. -/
theorem tri_kl_floor_hmu_fence_QA :
    ¬ (2 * ((1/2 : ℝ) * |1 - (0:ℝ)| ^ (2:ℕ)
          * |(degreeInvSqrt triAdj *ᵥ (![1,1,1] : Fin 3 → ℝ)) 0|
            / (Real.sqrt 2)⁻¹) ^ 2
        ≤ klDiv (walkDistribution triAdj 2 0) (stationaryVec triAdj)) := by
  intro h
  have hval : ((1/2 : ℝ) * |1 - (0:ℝ)| ^ (2:ℕ)
      * |(degreeInvSqrt triAdj *ᵥ (![1,1,1] : Fin 3 → ℝ)) 0|
        / (Real.sqrt 2)⁻¹) = 1/2 := by
    rw [tri_vconj_one 0,
      abs_of_pos (show (0:ℝ) < (Real.sqrt 2)⁻¹ by positivity)]
    field_simp
    ring_nf
  rw [hval, tri_kl_two_QA] at h
  norm_num at h
  have hgibbs : Real.log ((9:ℝ)/8) ≤ (9:ℝ)/8 - 1 :=
    Real.log_le_sub_one_of_pos (by norm_num)
  norm_num at hgibbs
  linarith

/-- The point vector's conjugate on the triangle. -/
theorem tri_vconj_e0 (j : Fin 3) :
    (degreeInvSqrt triAdj *ᵥ (![1, 0, 0] : Fin 3 → ℝ)) j
      = (if j = 0 then (Real.sqrt 2)⁻¹ else 0) := by
  rw [degreeInvSqrt_mulVec_apply, triAdj_deg_eq]
  fin_cases j <;> simp

/-- **The `hv` fence for the entropy floor**: at `μ = 3` (nonzero,
genuine), `v = ![1,0,0]` (NOT an eigenvector — the eigenvalues are
`{0, 3/2, 3/2}`), `c = (√2)⁻¹` (the sup bound genuine, attained at
coordinate `0`), `t = 1`, `x = 0`: the dropped statement reads
`2·((1/2)·2·1)² = 2 ≤ log(3/2)` — refuted by `log(3/2) < 1/2`. -/
theorem tri_kl_floor_hv_fence_QA :
    ¬ (2 * ((1/2 : ℝ) * |1 - (3:ℝ)| ^ (1:ℕ)
          * |(degreeInvSqrt triAdj *ᵥ (![1,0,0] : Fin 3 → ℝ)) 0|
            / (Real.sqrt 2)⁻¹) ^ 2
        ≤ klDiv (walkDistribution triAdj 1 0) (stationaryVec triAdj)) := by
  intro h
  have hv0 : (degreeInvSqrt triAdj *ᵥ (![1,0,0] : Fin 3 → ℝ)) 0
      = (Real.sqrt 2)⁻¹ := by
    rw [tri_vconj_e0 0]
    simp
  have hval : ((1/2 : ℝ) * |1 - (3:ℝ)| ^ (1:ℕ)
      * |(degreeInvSqrt triAdj *ᵥ (![1,0,0] : Fin 3 → ℝ)) 0|
        / (Real.sqrt 2)⁻¹) = 1 := by
    rw [abs_of_nonpos (by norm_num : (1:ℝ) - 3 ≤ 0), hv0,
      abs_of_pos (show (0:ℝ) < (Real.sqrt 2)⁻¹ by positivity)]
    norm_num
  rw [hval, tri_kl_one_QA] at h
  have hvlt : Real.log (3/2 : ℝ) < 3/2 - 1 :=
    Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  norm_num at hvlt
  norm_num at h
  linarith

/-- **The `hc` fence for the entropy floor**: same genuine fixture with
the sup bound dropped to `c = (√2)⁻¹/2` (which coordinate `0` violates,
`(√2)⁻¹ > (√2)⁻¹/2`): the floor inflates to
`2·((1/2)·2·2)² = 8 ≤ log(3/2)` — refuted. -/
theorem tri_kl_floor_hc_fence_QA :
    ¬ (2 * ((1/2 : ℝ) * |1 - (3:ℝ)| ^ (1:ℕ)
          * |(degreeInvSqrt triAdj *ᵥ (![1,0,0] : Fin 3 → ℝ)) 0|
            / ((Real.sqrt 2)⁻¹ / 2)) ^ 2
        ≤ klDiv (walkDistribution triAdj 1 0) (stationaryVec triAdj)) := by
  intro h
  have hv0 : (degreeInvSqrt triAdj *ᵥ (![1,0,0] : Fin 3 → ℝ)) 0
      = (Real.sqrt 2)⁻¹ := by
    rw [tri_vconj_e0 0]
    simp
  have hvlt : Real.log (3/2 : ℝ) < 3/2 - 1 :=
    Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  norm_num at hvlt
  have hval : ((1/2 : ℝ) * |1 - (3:ℝ)| ^ (1:ℕ)
      * |(degreeInvSqrt triAdj *ᵥ (![1,0,0] : Fin 3 → ℝ)) 0|
        / ((Real.sqrt 2)⁻¹ / 2)) = 2 := by
    rw [abs_of_nonpos (by norm_num : (1:ℝ) - 3 ≤ 0), hv0,
      abs_of_pos (show (0:ℝ) < (Real.sqrt 2)⁻¹ by positivity)]
    norm_num
  rw [hval, tri_kl_one_QA] at h
  norm_num at h
  linarith

/-- The swap's normalized Laplacian is `[[0,0],[−√2,1]]`, so
`![0,1]` is a genuine `μ = 1` eigenvector. -/
theorem asym_nL_mulVec :
    normalizedLaplacian asymSwapAdj *ᵥ (![0, 1] : Fin 2 → ℝ)
      = (1 : ℝ) • (![0, 1] : Fin 2 → ℝ) := by
  have hs4 : Real.sqrt (4:ℝ) = 2 := by
    have h := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 4)
    have hnn := Real.sqrt_nonneg (4:ℝ)
    nlinarith
  have h0 : ∀ j : Fin 2, (normalizedLaplacian asymSwapAdj *ᵥ
      (![0, 1] : Fin 2 → ℝ)) j = (![0, 1] : Fin 2 → ℝ) j := by
    intro j
    rcases (show j = 0 ∨ j = 1 by omega) with h | h <;> rw [h]
  -- entry 0: 0·0 + 0·1 = 0 = (![0,1]) 0
    · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        normalizedLaplacian, Matrix.sub_apply, Matrix.mul_apply,
        Matrix.one_apply, degreeInvSqrt, Matrix.diagonal, Pi.zero_apply,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
        asymSwapAdj_00, asymSwapAdj_01, asymSwapAdj_deg_zero,
        asymSwapAdj_deg_one, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2),
        hs4, zero_mul, mul_zero, sub_zero]
      norm_num
  -- entry 1: −√2·0 + 1·1 = 1
    · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        normalizedLaplacian, Matrix.sub_apply, Matrix.mul_apply,
        Matrix.one_apply, degreeInvSqrt, Matrix.diagonal,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
        asymSwapAdj_00, asymSwapAdj_01, asymSwapAdj_10, asymSwapAdj_11,
        asymSwapAdj_deg_zero, asymSwapAdj_deg_one,
        Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2), hs4,
        zero_mul, mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul]
      norm_num
  funext j
  rw [h0 j]
  simp [Pi.smul_apply]

/-- The swap's conjugate of `![0,1]`: `(0, 1/2)` — the sup `1/2`
attained with equality at coordinate `1`. -/
theorem asym_vconj (j : Fin 2) :
    (degreeInvSqrt asymSwapAdj *ᵥ (![0, 1] : Fin 2 → ℝ)) j
      = (if j = 1 then 1/2 else 0) := by
  have hs4 : Real.sqrt (4:ℝ) = 2 := by
    have h := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 4)
    have hnn := Real.sqrt_nonneg (4:ℝ)
    nlinarith
  rw [degreeInvSqrt_mulVec_apply]
  rcases (show j = 0 ∨ j = 1 by omega) with h | h <;> rw [h]
  · rw [asymSwapAdj_deg_zero]
    simp [Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  · rw [asymSwapAdj_deg_one, hs4]
    simp

/-- The start entropy at the swap, from `1`: `D(δ₁ ‖ π) = log(3/2)`. -/
theorem asym_kl_zero :
    klDiv (walkDistribution asymSwapAdj 0 1) (stationaryVec asymSwapAdj)
      = Real.log (3/2) := by
  have hlaw : (Pi.single (1 : Fin 2) (1 : ℝ)) = ![0, 1] := by
    funext i
    fin_cases i <;> simp
  have he0 : klTerm ((![0, 1] : Fin 2 → ℝ) 0) (stationaryVec asymSwapAdj 0)
      = 0 := by
    rw [asymSwap_pi_zero]
    simp [klTerm]
  have he1 : klTerm ((![0, 1] : Fin 2 → ℝ) 1) (stationaryVec asymSwapAdj 1)
      = Real.log (3/2) := by
    rw [asymSwap_pi_one]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      klTerm, if_neg one_ne_zero, one_mul]
    congr 1
    norm_num
  rw [walkDistribution_zero, hlaw, klDiv, Fin.sum_univ_two, he0, he1]
  ring

/-- **The `hA` fence for the entropy floor**: at the asymmetric swap
(every hypothesis except symmetry genuine), the genuine eigenpair
`(μ, v) = (1, ![0,1])` with the genuine sup bound `c = 1/2` attained
with equality, at `t = 0`, `x = 1`: the dropped statement reads
`2·((1/2)·|1−1|⁰·1)² = 1/2 ≤ D(δ₁ ‖ π) = log(3/2) < 1/2` —
refuted (strictly, via `log < x − 1`). -/
theorem klDiv_floor_hA_fence_QA :
    ¬ (2 * ((1/2 : ℝ) * |1 - (1:ℝ)| ^ (0:ℕ)
          * |(degreeInvSqrt asymSwapAdj *ᵥ (![0,1] : Fin 2 → ℝ)) 1|
            / (1/2)) ^ 2
        ≤ klDiv (walkDistribution asymSwapAdj 0 1)
            (stationaryVec asymSwapAdj)) := by
  intro h
  rw [asym_kl_zero] at h
  have hvlt : Real.log (3/2 : ℝ) < 3/2 - 1 :=
    Real.log_lt_sub_one_of_pos (by norm_num) (by norm_num)
  norm_num at hvlt
  have hvc : (degreeInvSqrt asymSwapAdj *ᵥ (![0,1] : Fin 2 → ℝ)) 1 = 1/2 := by
    rw [asym_vconj 1]
    simp
  rw [hvc] at h
  norm_num at h
  linarith

end EntropyFences

section PoissonFences

/-! ### Shared helpers: non-summability from bounded-away-from-zero,
and the elementary bound `e < 3` -/

/-- A real sequence whose absolute values stay above a positive
constant is not summable — summable sequences tend to zero. -/
theorem not_summable_of_abs_ge {f : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ∀ k, c ≤ |f k|) : ¬ Summable f := by
  intro h
  have hev : ∀ᶠ k in Filter.cofinite, (f k : ℝ) ∈ Metric.ball (0 : ℝ) (c / 2) :=
    h.tendsto_cofinite_zero
      (Metric.ball_mem_nhds 0 (by linarith : (0 : ℝ) < c / 2))
  have hball : ∀ k : ℕ, ¬ ((f k : ℝ) ∈ Metric.ball (0 : ℝ) (c / 2)) := by
    intro k
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have h1 := hf k
    linarith
  have hfin : {k : ℕ | ¬((f k : ℝ) ∈ Metric.ball (0 : ℝ) (c / 2))}.Finite :=
    Filter.eventually_cofinite.mp hev
  have hinf : {k : ℕ | ¬((f k : ℝ) ∈ Metric.ball (0 : ℝ) (c / 2))}.Infinite := by
    have hsub : {k : ℕ | ¬((f k : ℝ) ∈ Metric.ball (0 : ℝ) (c / 2))} = Set.univ := by
      ext k
      simpa using hball k
    rw [hsub]
    exact Set.infinite_univ
  exact absurd hfin hinf

/-- **The elementary bound `e < 3`** — the series tail against the
geometric tail: `e ≤ ∑_{k<5} 1/k! + ∑' 1/(120·2ᵏ) = 65/24 + 1/60 < 3`,
through `Nat.factorial_mul_pow_le_factorial` (`5!·6ᵏ ≤ (k+5)!`) and
`6ᵏ ≥ 2ᵏ`. -/
theorem exp_one_lt_three : Real.exp (1 : ℝ) < 3 := by
  have hsum : HasSum (fun k : ℕ => (1 : ℝ) ^ k / (Nat.factorial k : ℝ))
      (NormedSpace.exp ℝ (1 : ℝ)) := NormedSpace.expSeries_div_hasSum_exp ℝ 1
  rw [← Real.exp_eq_exp_ℝ] at hsum
  have hone : (fun k : ℕ => (1 : ℝ) ^ k / (Nat.factorial k : ℝ))
      = fun k : ℕ => 1 / (Nat.factorial k : ℝ) := by
    funext k; simp
  rw [hone] at hsum
  have hsplit := tsum_eq_range_add (fun k : ℕ => 1 / (Nat.factorial k : ℝ))
    hsum.summable 5
  rw [hsum.tsum_eq] at hsplit
  have htail : ∑' k, 1 / (Nat.factorial (k + 5) : ℝ) ≤ 1 / 60 := by
    have hgeom : HasSum (fun k : ℕ => (1 / 60 : ℝ) / 2 / 2 ^ k) (1 / 60 : ℝ) :=
      hasSum_geometric_two' (1 / 60 : ℝ)
    have hsmL : Summable fun k : ℕ => 1 / (Nat.factorial (k + 5) : ℝ) :=
      hsum.summable.comp_injective
        (fun a b hab => by simpa using congrArg (fun x => x - 5) hab)
    have hsmR : Summable fun k : ℕ => (1 / 60 : ℝ) / 2 / 2 ^ k := hgeom.summable
    refine le_trans (tsum_le_tsum (fun k => ?_) hsmL hsmR) (le_of_eq hgeom.tsum_eq)
    have h6 : ((2 : ℝ) ^ k) ≤ ((6 : ℝ) ^ k) :=
      pow_le_pow_left₀ (show (0 : ℝ) ≤ 2 by norm_num)
        (show (2 : ℝ) ≤ 6 by norm_num) k
    have hfac : ((120 : ℝ) * (6 : ℝ) ^ k) ≤ ((Nat.factorial (k + 5) : ℝ)) := by
      have hle : ((Nat.factorial 5) * (6 : ℕ) ^ k : ℕ) ≤ Nat.factorial (k + 5) := by
        simpa [Nat.add_comm 5 k] using
          Nat.factorial_mul_pow_le_factorial (m := 5) (n := k)
      have hcast : (((Nat.factorial 5) * (6 : ℕ) ^ k : ℕ) : ℝ)
          ≤ ((Nat.factorial (k + 5) : ℕ) : ℝ) := Nat.cast_le.mpr hle
      have h120 : ((Nat.factorial 5 : ℕ) : ℝ) = 120 := by
        rw [show Nat.factorial 5 = 120 from by decide]
        push_cast
        norm_num
      calc (120 : ℝ) * (6 : ℝ) ^ k = ((Nat.factorial 5 : ℕ) : ℝ) * ((6 : ℕ) ^ k : ℝ) := by
            rw [h120]; push_cast; ring
        _ = (((Nat.factorial 5) * (6 : ℕ) ^ k : ℕ) : ℝ) := by push_cast; ring
        _ ≤ _ := hcast
    have hbound : 1 / (Nat.factorial (k + 5) : ℝ) ≤ 1 / (120 * (2 : ℝ) ^ k) := by
      have h0 : (0 : ℝ) < 120 * (2 : ℝ) ^ k := by positivity
      have h1 : (0 : ℝ) < (Nat.factorial (k + 5) : ℝ) := by positivity
      refine (one_div_le_one_div h1 h0).mpr ?_
      calc (120 : ℝ) * (2 : ℝ) ^ k ≤ (120 : ℝ) * (6 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_left h6 (by norm_num)
        _ ≤ _ := hfac
    rwa [show (1 : ℝ) / 60 / 2 / 2 ^ k = 1 / (120 * (2 : ℝ) ^ k) from by
      field_simp; ring]
  have hpart : ∑ k in Finset.range 5, (1 / (Nat.factorial k : ℝ)) = 65 / 24 := by
    norm_num [Nat.factorial, Finset.sum_range_succ]
  rw [hpart] at hsplit
  have hcomb : Real.exp (1 : ℝ) ≤ 65 / 24 + 1 / 60 := by
    rw [hsplit]
    exact add_le_add_left htail _
  norm_num at hcomb
  linarith

/-! ### The TV simplex-diameter lemma's four mass clauses
(`tvDistance_le_one_of_nonneg_of_sum_eq_one`) -/

/-- Two-point TV distances reduce to the entrywise closed form. -/
theorem pf_tv_lit (a b c d : ℝ) :
    tvDistance (![a, b] : Fin 2 → ℝ) (![c, d] : Fin 2 → ℝ)
      = (1/2) * (|a - c| + |b - d|) := by
  rw [tvDistance]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Pi.sub_apply]

/-- **The `hμ` fence**: a negative entry with mass one (all other
clauses genuine) makes the TV distance `3/2 > 1`. -/
theorem tv_le_one_hmu_fence_QA :
    ¬ (tvDistance (![-1, 2] : Fin 2 → ℝ) (![1/2, 1/2] : Fin 2 → ℝ) ≤ 1) := by
  rw [pf_tv_lit]
  rw [abs_of_neg (by norm_num : (-1 : ℝ) - 1/2 < 0)]
  simp only [abs_of_nonneg (show (0 : ℝ) ≤ 2 - 1/2 by norm_num)]
  norm_num

/-- **The `hμ1` fence**: a mass-`4` nonnegative start. -/
theorem tv_le_one_hmu1_fence_QA :
    ¬ (tvDistance (![2, 2] : Fin 2 → ℝ) (![1/2, 1/2] : Fin 2 → ℝ) ≤ 1) := by
  rw [pf_tv_lit]
  simp only [abs_of_nonneg (show (0 : ℝ) ≤ 2 - 1/2 by norm_num)]
  norm_num

/-- **The `hν` fence**: a negative-entry target with mass one. -/
theorem tv_le_one_hv_fence_QA :
    ¬ (tvDistance (![1/2, 1/2] : Fin 2 → ℝ) (![-1, 2] : Fin 2 → ℝ) ≤ 1) := by
  rw [pf_tv_lit]
  simp only [abs_of_nonneg (show (0 : ℝ) ≤ 1/2 - (-1 : ℝ) by norm_num),
    abs_of_neg (show 1/2 - (2 : ℝ) < 0 by norm_num)]
  norm_num


/-- **The `hν1` fence**: a mass-`4` nonnegative target. -/
theorem tv_le_one_hv1_fence_QA :
    ¬ (tvDistance (![1/2, 1/2] : Fin 2 → ℝ) (![2, 2] : Fin 2 → ℝ) ≤ 1) := by
  rw [pf_tv_lit]
  simp only [abs_of_neg (show 1/2 - (2 : ℝ) < 0 by norm_num)]
  norm_num

/-- The isolation companions for the four simplex-diameter fences:
at each fixture exactly the dropped clause fails, mass and nonneg
genuine on the kept side. -/
theorem tv_le_one_isolation_QA :
    (∑ i, (![-1, 2] : Fin 2 → ℝ) i = 1)
      ∧ (∀ i, 0 ≤ (![1/2, 1/2] : Fin 2 → ℝ) i)
      ∧ (∑ i, (![1/2, 1/2] : Fin 2 → ℝ) i = 1)
      ∧ ¬ (∀ i, 0 ≤ (![2, 2] : Fin 2 → ℝ) i → False) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    norm_num
  · intro i
    fin_cases i <;> simp
  · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    norm_num
  · intro h
    have h0 := h 0
    simp only [Matrix.cons_val_zero, Matrix.head_cons] at h0
    norm_num at h0

/-- The constant-one sequence is not summable — the junk-tsum
engine's base case. -/
theorem not_summable_const_one : ¬ Summable (fun _ : ℕ => (1 : ℝ)) :=
  not_summable_of_abs_ge (show (0 : ℝ) < 1 by norm_num)
    (fun _ => show (1 : ℝ) ≤ |(1 : ℝ)| by norm_num)

/-! ### The head–tail split's summability clause (`tsum_eq_range_add`) -/

/-- **The `hsm` fence**: at the non-summable constant-one sequence with
`m = 1`, both tsums junk to `0` while the head is `1` — the split
identity reads `0 = 1`. -/
theorem tsum_eq_range_add_hsm_fence_QA :
    ¬ (∑' _k : ℕ, (1 : ℝ)
        = ∑ _k in Finset.range 1, (1 : ℝ) + ∑' _k : ℕ, (1 : ℝ)) := by
  intro h
  simp only [tsum_eq_zero_of_not_summable not_summable_const_one,
    Finset.sum_range_one] at h
  norm_num at h

/-! ### The Poisson weight's time clause (`poissonWeight_nonneg`) -/

/-- **The `ht` fence**: at `t = −1`, `k = 1` the weight is `−e < 0` —
the alternating-sign corner the nonneg layer excludes. -/
theorem poissonWeight_nonneg_ht_fence_QA :
    ¬ (0 ≤ poissonWeight (-(1 : ℝ)) 1) := by
  have hev : poissonWeight (-(1 : ℝ)) 1 = -(Real.exp (1 : ℝ)) := by
    unfold poissonWeight
    have h1 : (-(1 : ℝ)) ^ 1 = -(1 : ℝ) := by rw [pow_one]
    rw [show (-(-(1 : ℝ))) = (1 : ℝ) from by ring, h1]
    have hf : (Nat.factorial 1 : ℝ) = 1 := by norm_num
    rw [hf, div_one]
    ring
  rw [hev]
  linarith [Real.exp_pos (1 : ℝ)]

/-! ### The TV convexity bound (`tvDistance_tsum_le`) — the `hc`,
`hc1`, `hν`, and `hν1` clauses -/

/-- Geometric sums with a constant prefactor, packaged once: the
convexity fences consume three instances (`r = −1/2`, `1/4`, `−1/4`). -/
theorem pf_geom_smul {r c w : ℝ} (hr : |r| < 1) (hw : w = c * (1 - r)⁻¹) :
    HasSum (fun k => c * r ^ k) w := by
  have hg := hasSum_geometric_of_abs_lt_one hr
  have hcs := hg.const_smul c
  rw [hw]
  simpa [smul_eq_mul] using hcs

/-- The alternating weights `(3/2)·(−1/2)ᵏ`: a genuine probability
sequence (`HasSum 1`) with a negative entry at `k = 1` — every
`tvDistance_tsum_le` clause except `hc` genuine at this `c`. -/
theorem pf_alt_hasSum_one : HasSum (fun k => (3/2) * (-(1/2 : ℝ)) ^ k) 1 := by
  refine pf_geom_smul (abs_lt.mpr ⟨by norm_num, by norm_num⟩) ?_
  norm_num

theorem pf_two_pow_succ_ge_two (k : ℕ) : (2 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
    one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
  rw [pow_succ]
  nlinarith

/-- **The `hc` fence**: at the alternating weights `(3/2)·(−1/2)ᵏ`
(mass one, entry `−3/4 < 0` at `k = 1`) against the geometric family
`ν k = (1/2 ± (1/8)·(−1/2)ᵏ, …)` (probability vectors at every `k`),
the mixture is `(3/4, 1/4)` with TV `1/4` while the weighted-average
right side is the honest `3/20` — the signed weighting loses the
triangle inequality's slack. -/
theorem tv_tsum_le_hc_fence_QA :
    ¬ (tvDistance
          (fun i => ∑' k, (3/2) * (-(1/2 : ℝ)) ^ k
            * (![1/2 + (1/8) * (-(1/2 : ℝ)) ^ k,
                1/2 - (1/8) * (-(1/2 : ℝ)) ^ k] : Fin 2 → ℝ) i)
          (![1/2, 1/2] : Fin 2 → ℝ)
        ≤ ∑' k, (3/2) * (-(1/2 : ℝ)) ^ k
            * tvDistance
              (![1/2 + (1/8) * (-(1/2 : ℝ)) ^ k,
                  1/2 - (1/8) * (-(1/2 : ℝ)) ^ k] : Fin 2 → ℝ)
              (![1/2, 1/2] : Fin 2 → ℝ)) := by
  intro h
  -- the two mixture coordinates
  have hident0 : ∀ k : ℕ, (3/2) * (-(1/2 : ℝ)) ^ k
        * (1/2 + (1/8) * (-(1/2 : ℝ)) ^ k)
      = (3/4) * (-(1/2 : ℝ)) ^ k + (3/16) * ((1/4 : ℝ) ^ k) := by
    intro k
    have hx2 : ((1/4 : ℝ) ^ k)
        = (-(1/2 : ℝ)) ^ k * (-(1/2 : ℝ)) ^ k := by
      rw [← mul_pow]
      congr 1
      norm_num
    rw [hx2]
    ring
  have hA : HasSum (fun k => (3/4) * (-(1/2 : ℝ)) ^ k) (1/2) := by
    refine pf_geom_smul (abs_lt.mpr ⟨by norm_num, by norm_num⟩) ?_
    norm_num
  have hB : HasSum (fun k => (3/16) * ((1/4 : ℝ) ^ k)) (1/4) := by
    refine pf_geom_smul (abs_lt.mpr ⟨by norm_num, by norm_num⟩) ?_
    norm_num
  have h0 : ∑' k, (3/2) * (-(1/2 : ℝ)) ^ k
      * (1/2 + (1/8) * (-(1/2 : ℝ)) ^ k) = 3/4 := by
    have hv := (hA.add hB).tsum_eq
    simp only [Pi.add_apply] at hv
    rw [← tsum_congr hident0] at hv
    norm_num at hv
    exact hv
  have hident1 : ∀ k : ℕ, (3/2) * (-(1/2 : ℝ)) ^ k
        * (1/2 - (1/8) * (-(1/2 : ℝ)) ^ k)
      = (3/4) * (-(1/2 : ℝ)) ^ k + -(3/16 * ((1/4 : ℝ) ^ k)) := by
    intro k
    have hx2 : ((1/4 : ℝ) ^ k)
        = (-(1/2 : ℝ)) ^ k * (-(1/2 : ℝ)) ^ k := by
      rw [← mul_pow]
      congr 1
      norm_num
    rw [hx2]
    ring
  have h1 : ∑' k, (3/2) * (-(1/2 : ℝ)) ^ k
      * (1/2 - (1/8) * (-(1/2 : ℝ)) ^ k) = 1/4 := by
    have hv := (hA.add hB.neg).tsum_eq
    simp only [Pi.add_apply, Pi.neg_apply, neg_sub] at hv
    rw [← tsum_congr hident1] at hv
    norm_num at hv
    exact hv
  have hmix : ∀ i : Fin 2, (∑' k, (3/2) * (-(1/2 : ℝ)) ^ k
        * (![1/2 + (1/8) * (-(1/2 : ℝ)) ^ k,
            1/2 - (1/8) * (-(1/2 : ℝ)) ^ k] : Fin 2 → ℝ) i)
      = (![3/4, 1/4] : Fin 2 → ℝ) i := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · simp only [Matrix.cons_val_zero, Matrix.head_cons]
      exact h0
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
      exact h1
  -- the per-k TV values
  have htvk : ∀ k : ℕ, tvDistance
        (![1/2 + (1/8) * (-(1/2 : ℝ)) ^ k,
            1/2 - (1/8) * (-(1/2 : ℝ)) ^ k] : Fin 2 → ℝ)
        (![1/2, 1/2] : Fin 2 → ℝ)
      = (1/8) * ((1/2 : ℝ) ^ k) := by
    intro k
    have habs : |(1/8) * (-(1/2 : ℝ)) ^ k| = (1/8) * ((1/2 : ℝ) ^ k) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1/8), abs_pow,
        show |(-(1/2 : ℝ))| = 1/2 from by norm_num]
    rw [pf_tv_lit]
    rw [show 1/2 + (1/8 : ℝ) * (-(1/2 : ℝ)) ^ k - 1/2
          = (1/8) * (-(1/2 : ℝ)) ^ k from by ring,
      show 1/2 - (1/8 : ℝ) * (-(1/2 : ℝ)) ^ k - 1/2
          = -((1/8) * (-(1/2 : ℝ)) ^ k) from by ring,
      abs_neg, habs]
    ring
  -- the right side: a geometric sum with value 3/20
  have hRident : ∀ k : ℕ, (3/2) * (-(1/2 : ℝ)) ^ k * ((1/8) * ((1/2 : ℝ) ^ k))
      = (3/16) * (-(1/4 : ℝ)) ^ k := by
    intro k
    have hp : (-(1/2 : ℝ)) ^ k * (1/2 : ℝ) ^ k = (-(1/4 : ℝ)) ^ k := by
      rw [← mul_pow]
      congr 1
      norm_num
    calc (3/2) * (-(1/2 : ℝ)) ^ k * ((1/8) * ((1/2 : ℝ) ^ k))
        = (3/16) * ((-(1/2 : ℝ)) ^ k * (1/2 : ℝ) ^ k) := by ring
      _ = (3/16) * (-(1/4 : ℝ)) ^ k := by rw [hp]
  have hR : ∑' k, (3/2) * (-(1/2 : ℝ)) ^ k
      * ((1/8) * ((1/2 : ℝ) ^ k)) = 3/20 := by
    have hRsum : HasSum (fun k => (3/16) * (-(1/4 : ℝ)) ^ k) (3/20) := by
      refine pf_geom_smul (abs_lt.mpr ⟨by norm_num, by norm_num⟩) ?_
      norm_num
    have hv := hRsum.tsum_eq
    rw [← tsum_congr hRident] at hv
    exact hv
  have hmixf : (fun i => ∑' k, (3/2) * (-(1/2 : ℝ)) ^ k
        * (![1/2 + (1/8) * (-(1/2 : ℝ)) ^ k,
            1/2 - (1/8) * (-(1/2 : ℝ)) ^ k] : Fin 2 → ℝ) i)
      = (![3/4, 1/4] : Fin 2 → ℝ) := funext hmix
  rw [hmixf, pf_tv_lit] at h
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 3/4 - 1/2 by norm_num),
    abs_of_neg (show (1 : ℝ)/4 - 1/2 < 0 by norm_num)] at h
  norm_num at h
  have hRw : ∑' k, (3/2) * (-(1/2 : ℝ)) ^ k
      * tvDistance
        (![1/2 + (1/8) * (-(1/2 : ℝ)) ^ k,
            1/2 - (1/8) * (-(1/2 : ℝ)) ^ k] : Fin 2 → ℝ)
        (![1/2, 1/2] : Fin 2 → ℝ) = 3/20 := by
    rw [tsum_congr (fun k => by rw [htvk k])]
    exact hR
  rw [hRw] at h
  norm_num at h


/-- **The `hc1` fence**: a mass-`2` single-point weight against a
genuine probability vector — the mixture `2·ν₀ = (4/5, 6/5)` has TV
`1/2` against the weighted average `2·(1/10) = 1/5`. -/
theorem tv_tsum_le_hc1_fence_QA :
    ¬ (tvDistance
          (fun i => ∑' k, (if k = 0 then 2 else 0 : ℝ)
            * (![2/5, 3/5] : Fin 2 → ℝ) i)
          (![1/2, 1/2] : Fin 2 → ℝ)
        ≤ ∑' k, (if k = 0 then 2 else 0 : ℝ)
            * tvDistance (![2/5, 3/5] : Fin 2 → ℝ)
                (![1/2, 1/2] : Fin 2 → ℝ)) := by
  intro h
  have htvν : tvDistance (![2/5, 3/5] : Fin 2 → ℝ) (![1/2, 1/2] : Fin 2 → ℝ)
      = 1/10 := by
    rw [pf_tv_lit]
    rw [abs_of_neg (show (2 : ℝ)/5 - 1/2 < 0 by norm_num),
      abs_of_nonneg (show (0 : ℝ) ≤ 3/5 - 1/2 by norm_num)]
    norm_num
  have hmix : ∀ i : Fin 2, (∑' k, (if k = 0 then 2 else 0 : ℝ)
        * (![2/5, 3/5] : Fin 2 → ℝ) i)
      = 2 * (![2/5, 3/5] : Fin 2 → ℝ) i := by
    intro i
    rw [tsum_eq_single 0 (fun b hb => by simp [hb])]
    simp
  have hm0 : (∑' k, (if k = 0 then 2 else 0 : ℝ)
        * (![2/5, 3/5] : Fin 2 → ℝ) 0) = 4/5 := by
    rw [hmix 0]
    simp
    norm_num
  have hm1 : (∑' k, (if k = 0 then 2 else 0 : ℝ)
        * (![2/5, 3/5] : Fin 2 → ℝ) 1) = 6/5 := by
    rw [hmix 1]
    simp
    norm_num
  have hR : ∑' k, (if k = 0 then 2 else 0 : ℝ)
      * tvDistance (![2/5, 3/5] : Fin 2 → ℝ) (![1/2, 1/2] : Fin 2 → ℝ)
      = 1/5 := by
    rw [htvν, tsum_eq_single 0 (fun b hb => by simp [hb])]
    simp
    norm_num
  have hmixf : (fun i => ∑' k, (if k = 0 then 2 else 0 : ℝ)
        * (![2/5, 3/5] : Fin 2 → ℝ) i)
      = (![4/5, 6/5] : Fin 2 → ℝ) := by
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · simp only [Matrix.cons_val_zero, Matrix.head_cons]
      exact hm0
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
      exact hm1
  rw [hmixf, pf_tv_lit, hR] at h
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 4/5 - 1/2 by norm_num),
    abs_of_nonneg (show (0 : ℝ) ≤ 6/5 - 1/2 by norm_num)] at h
  norm_num at h

/-! ### The divergent-tsum junk fences for `hν` and `hν1` -/

/-- The Poisson-summable geometric weights `1/2·2⁻ᵏ` — a genuine
probability sequence (`hasSum_geometric_two'` at `1`). -/
theorem pf_geom_weights_hasSum_one :
    HasSum (fun k => (1 : ℝ)/2/((2 : ℝ) ^ k)) 1 := hasSum_geometric_two' 1

/-- **The `hν` fence** — the divergent-tsum junk route: the geometric
weights against the *geometrically growing* family
`ν k = (2ᵏ⁺¹, 1 − 2ᵏ⁺¹)` (mass one, negative entry at every `k`) make
every series in the statement non-summable: both sides junk to `0`
while the left TV is the honest `1/2` — `1/2 ≤ 0`. -/
theorem tv_tsum_le_hv_fence_QA :
    ¬ (tvDistance
          (fun i => ∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
            * (![(2 : ℝ)^(k+1), 1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ) i)
          (![1/2, 1/2] : Fin 2 → ℝ)
        ≤ ∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
            * tvDistance (![(2 : ℝ)^(k+1), 1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ)
                (![1/2, 1/2] : Fin 2 → ℝ)) := by
  intro h
  have hp0 : ∀ k : ℕ, ((1 : ℝ)/2/((2 : ℝ) ^ k)) * ((2 : ℝ)^(k+1)) = 1 := by
    intro k
    rw [pow_succ (2 : ℝ) k]
    field_simp
    ring_nf
  have hp1 : ∀ k : ℕ, ((1 : ℝ)/2/((2 : ℝ) ^ k)) * (1 - (2 : ℝ)^(k+1))
      = (1 : ℝ)/2/((2 : ℝ) ^ k) - 1 := by
    intro k
    rw [pow_succ (2 : ℝ) k]
    field_simp
    ring_nf
  have h1le : ∀ k : ℕ, (1 : ℝ)/2/((2 : ℝ) ^ k) ≤ 1/2 := by
    intro k
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
      one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith
  have hnsm0 : ¬ Summable
      (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * (![(2 : ℝ)^(k+1),
        1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ) 0) := by
    rw [show (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * (![(2 : ℝ)^(k+1),
        1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ) 0)
      = fun _ => (1 : ℝ) from funext fun k => hp0 k]
    exact not_summable_const_one
  have hnsm1 : ¬ Summable
      (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * (![(2 : ℝ)^(k+1),
        1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ) 1) := by
    refine not_summable_of_abs_ge (show (0 : ℝ) < 1/2 by norm_num) ?_
    intro k
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
    rw [hp1 k, abs_of_neg (by
      have := h1le k
      linarith)]
    have h1 := h1le k
    linarith
  have hmix : ∀ i : Fin 2, (∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
        * (![(2 : ℝ)^(k+1), 1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ) i) = 0 := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi
    · rw [hi, tsum_eq_zero_of_not_summable hnsm0]
    · rw [hi, tsum_eq_zero_of_not_summable hnsm1]
  have htvk : ∀ k : ℕ, tvDistance
        (![(2 : ℝ)^(k+1), 1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ)
        (![1/2, 1/2] : Fin 2 → ℝ)
      = (2 : ℝ)^(k+1) - 1/2 := by
    intro k
    have hge : (2 : ℝ) ≤ (2 : ℝ)^(k+1) := pf_two_pow_succ_ge_two k
    rw [pf_tv_lit]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (2 : ℝ)^(k+1) - 1/2),
      abs_of_neg (by linarith : (1 : ℝ) - (2 : ℝ)^(k+1) - 1/2 < 0)]
    ring
  have hRident : ∀ k : ℕ, ((1 : ℝ)/2/((2 : ℝ) ^ k)) * ((2 : ℝ)^(k+1) - 1/2)
      = 1 - 1/((2 : ℝ)^(k+2)) := by
    intro k
    rw [pow_succ (2 : ℝ) k,
      show (2 : ℝ)^(k+2) = (2 : ℝ)^k * 4 from by rw [pow_succ, pow_succ]; ring]
    field_simp
    ring_nf
  have h4le : ∀ k : ℕ, (4 : ℝ) ≤ (2 : ℝ)^(k+2) := by
    intro k
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
      one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
    have hp : (2 : ℝ)^(k+2) = 4 * (2 : ℝ)^k := by
      rw [pow_succ, pow_succ]; ring
    nlinarith
  have hnsmR : ¬ Summable
      (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * ((2 : ℝ)^(k+1) - 1/2)) := by
    rw [funext hRident]
    refine not_summable_of_abs_ge (show (0 : ℝ) < 3/4 by norm_num) ?_
    intro k
    have hpos : (0 : ℝ) < (2 : ℝ)^(k+2) := by positivity
    have hinvle : 1/((2 : ℝ)^(k+2)) ≤ 1/4 :=
      (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 4)).mpr (h4le k)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - 1/((2 : ℝ)^(k+2)))]
    nlinarith
  have hmixf : (fun i => ∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
        * (![(2 : ℝ)^(k+1), 1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ) i)
      = (0 : Fin 2 → ℝ) := funext hmix
  have hR : ∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
      * tvDistance (![(2 : ℝ)^(k+1), 1 - (2 : ℝ)^(k+1)] : Fin 2 → ℝ)
          (![1/2, 1/2] : Fin 2 → ℝ) = 0 := by
    rw [tsum_congr (fun k => by rw [htvk k]),
      tsum_eq_zero_of_not_summable hnsmR]
  rw [hmixf, hR] at h
  have hTV : tvDistance (0 : Fin 2 → ℝ) (![1/2, 1/2] : Fin 2 → ℝ) = 1/2 := by
    rw [tvDistance]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, Pi.zero_apply]
    have h1 : |(0 : ℝ) - 1/2| = 1/2 := by
      rw [abs_of_neg (by norm_num : (0 : ℝ) - 1/2 < 0)]
      norm_num
    show (1 : ℝ)/2 * (|0 - 1/2| + |0 - 1/2|) = 1/2
    rw [h1]
    norm_num
  rw [hTV] at h
  norm_num at h

/-- **The `hν1` fence** — the divergent-tsum junk route's twin: the
geometric weights against the nonnegative family
`ν k = (2ᵏ⁺¹, 2ᵏ⁺¹ − 1)` (mass `2ᵏ⁺²−1 ≠ 1`, entries nonnegative) —
both sides junk to `0` against the honest left TV `1/2`. -/
theorem tv_tsum_le_hv1_fence_QA :
    ¬ (tvDistance
          (fun i => ∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
            * (![(2 : ℝ)^(k+1), (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ) i)
          (![1/2, 1/2] : Fin 2 → ℝ)
        ≤ ∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
            * tvDistance (![(2 : ℝ)^(k+1), (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ)
                (![1/2, 1/2] : Fin 2 → ℝ)) := by
  intro h
  have hp0 : ∀ k : ℕ, ((1 : ℝ)/2/((2 : ℝ) ^ k)) * ((2 : ℝ)^(k+1)) = 1 := by
    intro k
    rw [pow_succ (2 : ℝ) k]
    field_simp
    ring_nf
  have hp1 : ∀ k : ℕ, ((1 : ℝ)/2/((2 : ℝ) ^ k)) * ((2 : ℝ)^(k+1) - 1)
      = 1 - (1 : ℝ)/2/((2 : ℝ) ^ k) := by
    intro k
    have h0 : ((1 : ℝ)/2/((2 : ℝ) ^ k)) * ((2 : ℝ)^(k+1)) = 1 := hp0 k
    rw [mul_sub, h0, mul_one]
  have h1le : ∀ k : ℕ, (1 : ℝ)/2/((2 : ℝ) ^ k) ≤ 1/2 := by
    intro k
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ k :=
      one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    rw [div_le_iff₀ hpos]
    nlinarith
  have hnsm0 : ¬ Summable
      (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * (![(2 : ℝ)^(k+1),
        (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ) 0) := by
    rw [show (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * (![(2 : ℝ)^(k+1),
        (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ) 0)
      = fun _ => (1 : ℝ) from funext fun k => hp0 k]
    exact not_summable_const_one
  have hnsm1 : ¬ Summable
      (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * (![(2 : ℝ)^(k+1),
        (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ) 1) := by
    rw [show (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * (![(2 : ℝ)^(k+1),
        (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ) 1)
      = fun k => 1 - (1 : ℝ)/2/((2 : ℝ) ^ k) from funext fun k => by
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
        exact hp1 k]
    refine not_summable_of_abs_ge (show (0 : ℝ) < 1/2 by norm_num) ?_
    intro k
    have h1 := h1le k
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hmix : ∀ i : Fin 2, (∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
        * (![(2 : ℝ)^(k+1), (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ) i) = 0 := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi
    · rw [hi, tsum_eq_zero_of_not_summable hnsm0]
    · rw [hi, tsum_eq_zero_of_not_summable hnsm1]
  have htvk : ∀ k : ℕ, tvDistance
        (![(2 : ℝ)^(k+1), (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ)
        (![1/2, 1/2] : Fin 2 → ℝ)
      = (2 : ℝ)^(k+1) - 1 := by
    intro k
    have hge : (2 : ℝ) ≤ (2 : ℝ)^(k+1) := pf_two_pow_succ_ge_two k
    rw [pf_tv_lit]
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (2 : ℝ)^(k+1) - 1/2),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ (2 : ℝ)^(k+1) - 1 - 1/2)]
    ring
  have hnsmR : ¬ Summable
      (fun k => ((1 : ℝ)/2/((2 : ℝ) ^ k)) * ((2 : ℝ)^(k+1) - 1)) := by
    rw [funext hp1]
    refine not_summable_of_abs_ge (show (0 : ℝ) < 1/2 by norm_num) ?_
    intro k
    have h1 := h1le k
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hmixf : (fun i => ∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
        * (![(2 : ℝ)^(k+1), (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ) i)
      = (0 : Fin 2 → ℝ) := funext hmix
  have hR : ∑' k, (1 : ℝ)/2/((2 : ℝ) ^ k)
      * tvDistance (![(2 : ℝ)^(k+1), (2 : ℝ)^(k+1) - 1] : Fin 2 → ℝ)
          (![1/2, 1/2] : Fin 2 → ℝ) = 0 := by
    rw [tsum_congr (fun k => by rw [htvk k]),
      tsum_eq_zero_of_not_summable hnsmR]
  rw [hmixf, hR] at h
  have hTV : tvDistance (0 : Fin 2 → ℝ) (![1/2, 1/2] : Fin 2 → ℝ) = 1/2 := by
    rw [tvDistance]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, Pi.zero_apply]
    have h1 : |(0 : ℝ) - 1/2| = 1/2 := by
      rw [abs_of_neg (by norm_num : (0 : ℝ) - 1/2 < 0)]
      norm_num
    show (1 : ℝ)/2 * (|0 - 1/2| + |0 - 1/2|) = 1/2
    rw [h1]
    norm_num
  rw [hTV] at h
  norm_num at h

/-! ### The negative off-diagonal fixture: the `hnn` clauses -/

theorem negOff_walkT_00 : walkTransitionMatrix negOffAdj 0 0 = 2 := by
  rw [walkTransitionMatrix_apply, negOffAdj_deg 0, negOff_00, inv_one]
  norm_num

theorem negOff_walkT_01 : walkTransitionMatrix negOffAdj 0 1 = -1 := by
  rw [walkTransitionMatrix_apply, negOffAdj_deg 0, negOff_01, inv_one]
  norm_num

theorem negOff_walkT_10 : walkTransitionMatrix negOffAdj 1 0 = -1 := by
  rw [walkTransitionMatrix_apply, negOffAdj_deg 1, negOff_10, inv_one]
  norm_num

theorem negOff_walkT_11 : walkTransitionMatrix negOffAdj 1 1 = 2 := by
  rw [walkTransitionMatrix_apply, negOffAdj_deg 1, negOff_11, inv_one]
  norm_num

theorem negOff_PT_vec_mu :
    (walkTransitionMatrix negOffAdj)ᵀ *ᵥ (![1, 0] : Fin 2 → ℝ)
      = ![2, -1] := by
  funext (i : Fin 2)
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    rw [negOff_walkT_00, negOff_walkT_10]
    norm_num
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    rw [negOff_walkT_01, negOff_walkT_11]
    norm_num

theorem negOff_PT_vec_nu :
    (walkTransitionMatrix negOffAdj)ᵀ *ᵥ (![0, 1] : Fin 2 → ℝ)
      = ![-1, 2] := by
  funext (i : Fin 2)
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    rw [negOff_walkT_00, negOff_walkT_10]
    norm_num
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    rw [negOff_walkT_01, negOff_walkT_11]
    norm_num

/-- **The `hnn` fence for the adjoint-walk TV contraction** (`k = 0`
one-step form): the negative entries triple the TV distance of the
basis pair, `3 ≤ 1` refuted. -/
theorem negOff_contraction_hnn_fence_QA :
    ¬ (tvDistance ((walkTransitionMatrix negOffAdj)ᵀ *ᵥ (![1, 0] : Fin 2 → ℝ))
          ((walkTransitionMatrix negOffAdj)ᵀ *ᵥ (![0, 1] : Fin 2 → ℝ))
        ≤ tvDistance (![1, 0] : Fin 2 → ℝ) (![0, 1] : Fin 2 → ℝ)) := by
  rw [negOff_PT_vec_mu, negOff_PT_vec_nu, pf_tv_lit, pf_tv_lit]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 - (-1) by norm_num),
    abs_of_neg (show (-1 : ℝ) - 2 < 0 by norm_num),
    abs_of_nonneg (show (0 : ℝ) ≤ 1 - 0 by norm_num),
    abs_of_neg (show (0 : ℝ) - 1 < 0 by norm_num)]
  norm_num

/-- **The `hnn` fence for the iterated contraction** — the `k = 1`
instance of the power form is the one-step fence verbatim. -/
theorem negOff_pow_contraction_hnn_fence_QA :
    ¬ (tvDistance ((walkTransitionMatrix negOffAdj)ᵀ ^ 1 *ᵥ (![1, 0] : Fin 2 → ℝ))
          ((walkTransitionMatrix negOffAdj)ᵀ ^ 1 *ᵥ (![0, 1] : Fin 2 → ℝ))
        ≤ tvDistance (![1, 0] : Fin 2 → ℝ) (![0, 1] : Fin 2 → ℝ)) := by
  rw [pow_one]
  exact negOff_contraction_hnn_fence_QA

/-- **The `hnn` fence for the TV ≤ 1 bound**: the one-step law
`(2, −1)` at the genuine stationary vector `(1/2, 1/2)` has TV
`3/2 > 1`. -/
theorem negOff_le_one_hnn_fence_QA :
    ¬ (tvDistance (walkDistribution negOffAdj 1 0) (stationaryVec negOffAdj)
        ≤ 1) := by
  have hπ : stationaryVec negOffAdj = ![1/2, 1/2] := by
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · exact negOff_pi 0
    · exact negOff_pi 1
  rw [negOff_dist_one, hπ, pf_tv_lit]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 - 1/2 by norm_num),
    abs_of_neg (show (-1 : ℝ) - 1/2 < 0 by norm_num)]
  norm_num

/-- The two-step law at the negative off-diagonal fixture: the walk
matrix is `A` (unit degrees), so `ν₂ = Pᵀ *ᵥ (2, −1) = (5, −4)`. -/
theorem negOff_PT_vec_law_one :
    (walkTransitionMatrix negOffAdj)ᵀ *ᵥ (![2, -1] : Fin 2 → ℝ)
      = ![5, -4] := by
  funext (i : Fin 2)
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    rw [negOff_walkT_00, negOff_walkT_10]
    norm_num
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    rw [negOff_walkT_01, negOff_walkT_11]
    norm_num

theorem negOff_dist_two : walkDistribution negOffAdj 2 0 = ![5, -4] := by
  have h := walkDistribution_succ negOffAdj 1 0
  rw [negOff_dist_one, negOff_PT_vec_law_one] at h
  exact h

/-- **The `hnn` fence for discrete TV monotonicity**: the negative
entries make the TV distance grow (`3/2 → 9/2`) — waiting longer can
increase the distance to stationarity. -/
theorem negOff_anti_hnn_fence_QA :
    ¬ (tvDistance (walkDistribution negOffAdj (1 + 1) 0) (stationaryVec negOffAdj)
        ≤ tvDistance (walkDistribution negOffAdj 1 0) (stationaryVec negOffAdj)) := by
  have hπ : stationaryVec negOffAdj = ![1/2, 1/2] := by
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · exact negOff_pi 0
    · exact negOff_pi 1
  have hv1 : tvDistance (walkDistribution negOffAdj 1 0) (stationaryVec negOffAdj)
      = 3/2 := by
    rw [negOff_dist_one, hπ, pf_tv_lit]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 - 1/2 by norm_num),
      abs_of_neg (show (-1 : ℝ) - 1/2 < 0 by norm_num)]
    norm_num
  have hv2 : tvDistance (walkDistribution negOffAdj 2 0) (stationaryVec negOffAdj)
      = 9/2 := by
    rw [negOff_dist_two, hπ, pf_tv_lit]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 5 - 1/2 by norm_num),
      abs_of_neg (show (-4 : ℝ) - 1/2 < 0 by norm_num)]
    norm_num
  rw [hv1, hv2]
  norm_num

/-! ### The asymmetric flow fixture (kills the `hA` of discrete TV
monotonicity — the existing asymmetric fixtures cannot serve: at the
swap the law is absorbed after one step, so the TV sequence is
constant) -/

/-- Adjacency of the asymmetric flow: nonnegative, `deg = (2, 3)`
positive, `A 0 1 = 1 ≠ 3 = A 1 0`. Its walk matrix is
`[[1/2, 1/2], [1, 0]]` with `π = (2/5, 3/5)` — a directed 2-cycle with
a lazy side, on which the TV distance to the degree vector genuinely
oscillates: `1/10 → 7/20`. -/
def asymFlowAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![1, 1; 3, 0]

theorem asymFlowAdj_00 : asymFlowAdj 0 0 = 1 := by rw [asymFlowAdj]; rfl
theorem asymFlowAdj_01 : asymFlowAdj 0 1 = 1 := by rw [asymFlowAdj]; rfl
theorem asymFlowAdj_10 : asymFlowAdj 1 0 = 3 := by rw [asymFlowAdj]; rfl
theorem asymFlowAdj_11 : asymFlowAdj 1 1 = 0 := by rw [asymFlowAdj]; rfl

theorem asymFlowAdj_nonneg (i j : Fin 2) : 0 ≤ asymFlowAdj i j := by
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h] <;>
    rcases (show j = 0 ∨ j = 1 by omega) with h' | h' <;> rw [h'] <;>
    simp [asymFlowAdj_00, asymFlowAdj_01, asymFlowAdj_10, asymFlowAdj_11]

theorem asymFlowAdj_deg_zero : deg asymFlowAdj 0 = 2 := by
  simp only [deg, Fin.sum_univ_two, asymFlowAdj_00, asymFlowAdj_01]
  norm_num

theorem asymFlowAdj_deg_one : deg asymFlowAdj 1 = 3 := by
  simp only [deg, Fin.sum_univ_two, asymFlowAdj_10, asymFlowAdj_11]
  norm_num

theorem asymFlowAdj_deg_pos (i : Fin 2) : 0 < deg asymFlowAdj i := by
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · rw [asymFlowAdj_deg_zero]; norm_num
  · rw [asymFlowAdj_deg_one]; norm_num

theorem asymFlowAdj_not_isSymm : ¬ asymFlowAdj.IsSymm := by
  intro h
  have hrow : asymFlowAdjᵀ 1 = asymFlowAdj 1 := congrFun h.eq 1
  have h10 := congrFun hrow 0
  simp only [Matrix.transpose_apply, asymFlowAdj_01, asymFlowAdj_10] at h10
  norm_num at h10

theorem asymFlow_vol_QA :
    vol asymFlowAdj (Finset.univ : Finset (Fin 2)) = 5 := by
  rw [vol, Fin.sum_univ_two, asymFlowAdj_deg_zero, asymFlowAdj_deg_one]
  norm_num

theorem asymFlow_pi_zero : stationaryVec asymFlowAdj 0 = 2/5 := by
  rw [stationaryVec, asymFlow_vol_QA, asymFlowAdj_deg_zero]

theorem asymFlow_pi_one : stationaryVec asymFlowAdj 1 = 3/5 := by
  rw [stationaryVec, asymFlow_vol_QA, asymFlowAdj_deg_one]

theorem asymFlow_walkT_00 : walkTransitionMatrix asymFlowAdj 0 0 = 1/2 := by
  rw [walkTransitionMatrix_apply, asymFlowAdj_deg_zero, asymFlowAdj_00]
  norm_num

theorem asymFlow_walkT_01 : walkTransitionMatrix asymFlowAdj 0 1 = 1/2 := by
  rw [walkTransitionMatrix_apply, asymFlowAdj_deg_zero, asymFlowAdj_01]
  norm_num

theorem asymFlow_walkT_10 : walkTransitionMatrix asymFlowAdj 1 0 = 1 := by
  rw [walkTransitionMatrix_apply, asymFlowAdj_deg_one, asymFlowAdj_10]
  norm_num

theorem asymFlow_walkT_11 : walkTransitionMatrix asymFlowAdj 1 1 = 0 := by
  rw [walkTransitionMatrix_apply, asymFlowAdj_deg_one, asymFlowAdj_11]
  norm_num

theorem asymFlow_dist_one : walkDistribution asymFlowAdj 1 0 = ![1/2, 1/2] := by
  rw [walkDistribution, pow_one]
  funext (i : Fin 2)
  rw [transpose_mulVec_single_apply]
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
  · rw [asymFlow_walkT_00]
    norm_num
  · rw [asymFlow_walkT_01]
    norm_num

theorem asymFlow_dist_two : walkDistribution asymFlowAdj 2 0 = ![3/4, 1/4] := by
  have h0 := walkDistribution_succ asymFlowAdj 1 0
  rw [asymFlow_dist_one] at h0
  rw [h0]
  funext (i : Fin 2)
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    rw [asymFlow_walkT_00, asymFlow_walkT_10]
    norm_num
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    rw [asymFlow_walkT_01, asymFlow_walkT_11]
    norm_num

/-- **The `hA` fence for discrete TV monotonicity**: on the asymmetric
flow (nonnegative, positive degrees — every hypothesis except
symmetry), the TV distance to the degree vector rises from `1/10` at
`t = 1` to `7/20` at `t = 2` — the asymmetric drift genuinely
de-monotonizes. -/
theorem asymFlow_anti_hA_fence_QA :
    ¬ (tvDistance (walkDistribution asymFlowAdj (1 + 1) 0)
          (stationaryVec asymFlowAdj)
        ≤ tvDistance (walkDistribution asymFlowAdj 1 0)
            (stationaryVec asymFlowAdj)) := by
  have hπ : stationaryVec asymFlowAdj = ![2/5, 3/5] := by
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · exact asymFlow_pi_zero
    · exact asymFlow_pi_one
  have hv1 : tvDistance (walkDistribution asymFlowAdj 1 0)
      (stationaryVec asymFlowAdj) = 1/10 := by
    rw [asymFlow_dist_one, hπ, pf_tv_lit]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 1/2 - 2/5 by norm_num),
      abs_of_neg (show (1 : ℝ)/2 - 3/5 < 0 by norm_num)]
    norm_num
  have hv2 : tvDistance (walkDistribution asymFlowAdj 2 0)
      (stationaryVec asymFlowAdj) = 7/20 := by
    rw [asymFlow_dist_two, hπ, pf_tv_lit]
    rw [abs_of_nonneg (show (0 : ℝ) ≤ 3/4 - 2/5 by norm_num),
      abs_of_neg (show (1 : ℝ)/4 - 3/5 < 0 by norm_num)]
    norm_num
  rw [hv1, hv2]
  norm_num

/-! ### The asymmetric swap: the identity's `hA` clauses -/

theorem pf_two_lt_exp : (2 : ℝ) < Real.exp 1 := by
  have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
  linarith

theorem pf_four_lt_exp_two : (4 : ℝ) < Real.exp 2 := by
  have hp := pow_lt_pow_left₀ pf_two_lt_exp (by norm_num : (0 : ℝ) ≤ 2)
    (by norm_num : (2 : ℕ) ≠ 0)
  rw [show ((Real.exp 1 : ℝ)) ^ 2 = Real.exp 2 from by
    rw [← Real.exp_nat_mul]
    ring_nf] at hp
  norm_num at hp
  exact hp

theorem asym_hπ : stationaryVec asymSwapAdj = ![1/3, 2/3] := by
  funext (i : Fin 2)
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
  · exact asymSwap_pi_zero
  · exact asymSwap_pi_one

/-- The swap's law from `0` is absorbed in one step: `ν_k = δ₀` at
every time (row `0` of `P` is `(1, 0)`). -/
theorem asym_dist_const (k : ℕ) :
    walkDistribution asymSwapAdj k 0 = ![1, 0] := by
  induction k with
  | zero =>
    rw [walkDistribution_zero]
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · simp [Pi.single_apply]
    · simp [Pi.single_apply]
  | succ k ih =>
    rw [walkDistribution_succ, ih]
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.cons_val_one]
      rw [asym_walk_00, asym_walk_10]
      norm_num
    · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.cons_val_one]
      rw [asym_walk_01, asym_walk_11]
      norm_num

/-- The swap's density from `0` is the constant `(3, 0)`. -/
theorem asym_density_const (k : ℕ) :
    walkDensity asymSwapAdj k 0 = ![3, 0] := by
  funext (i : Fin 2)
  show walkDistribution asymSwapAdj k 0 i / stationaryVec asymSwapAdj i
    = (![3, 0] : Fin 2 → ℝ) i
  rw [asym_dist_const k]
  rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, asymSwap_pi_zero]
    norm_num
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      asymSwap_pi_one]
    norm_num

/-- **The `hA` fence for the density-power identity**: the walk power
acts on the start density `(3, 0)` by its rows, giving `(3, 3)` — the
identity claims the *density evolution* `(3, 0)`, which is
reversibility (`P = D⁻¹A` is π-reversible exactly at symmetry). -/
theorem walkDensity_eq_pow_hA_fence_QA :
    ¬ (walkDensity asymSwapAdj 1 0
        = (walkTransitionMatrix asymSwapAdj ^ 1) *ᵥ walkDensity asymSwapAdj 0 0) := by
  have hR : (walkTransitionMatrix asymSwapAdj ^ 1) *ᵥ
      walkDensity asymSwapAdj 0 0 = ![3, 3] := by
    rw [pow_one, asym_density_zero]
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
      rw [asym_walk_00]
      norm_num
    · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
      rw [asym_walk_10]
      norm_num
  rw [asym_density_const 1, hR]
  intro he
  have h1eq := congrFun he (1 : Fin 2)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h1eq
  norm_num at h1eq

/-- **The `hA` fence for the Poissonization `HasSum`**: the mixture of
the constant densities `(3, 0)` sums to `(3, 0)`, while the claimed
sum (the heat kernel's action) is `(3, 3(1 − e⁻¹))` — the drift term
is genuinely nonzero. -/
theorem hasSum_poisson_walkDensity_hA_fence_QA :
    ¬ HasSum (fun k : ℕ => poissonWeight (1 : ℝ) k • walkDensity asymSwapAdj k 0)
        (walkHeatKernel asymSwapAdj 1 *ᵥ walkDensity asymSwapAdj 0 0) := by
  intro hclaimed
  have hvec : ∀ i : Fin 2, HasSum (fun k => poissonWeight (1 : ℝ) k •
      walkDensity asymSwapAdj k 0 i) ((![3, 0] : Fin 2 → ℝ) i) := by
    intro i
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · rw [show (fun k => poissonWeight (1:ℝ) k • walkDensity asymSwapAdj k 0 0)
          = fun k => poissonWeight (1:ℝ) k * 3 from funext fun k => by
          simp only [Pi.smul_apply, smul_eq_mul, asym_density_const k,
            Matrix.cons_val_zero, Matrix.head_cons]]
      simpa using (poissonWeight_hasSum_one 1).mul_right (3 : ℝ)
    · rw [show (fun k => poissonWeight (1:ℝ) k • walkDensity asymSwapAdj k 0 1)
          = fun _ => (0 : ℝ) from funext fun k => by
          simp only [Pi.smul_apply, smul_eq_mul, asym_density_const k,
            Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
          norm_num]
      exact hasSum_zero
  have hhonest : HasSum (fun k : ℕ => poissonWeight (1 : ℝ) k •
      walkDensity asymSwapAdj k 0) (![3, 0] : Fin 2 → ℝ) :=
    Pi.hasSum.mpr hvec
  have hval := hclaimed.unique hhonest
  have hker : walkHeatKernel asymSwapAdj 1 *ᵥ walkDensity asymSwapAdj 0 0
      = ![3, 3 * (1 - Real.exp (-(1:ℝ)))] := by
    rw [← contWalkDensity, asym_cont_density_one]
  rw [hker] at hval
  have h1eq := congrFun hval (1 : Fin 2)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h1eq
  have hpos : Real.exp (-(1:ℝ)) < 1 := by
    have := Real.exp_lt_exp.mpr (by norm_num : -(1:ℝ) < 0)
    rwa [Real.exp_zero] at this
  linarith

/-- **The `hA` fence for the density-level identity**: LHS the closed
form `(3, 3(1 − e⁻¹))`, RHS the Poisson mixture of the constant
densities `(3, 0)`. -/
theorem contWalkDensity_eq_tsum_hA_fence_QA :
    ¬ (contWalkDensity asymSwapAdj 1 0
        = fun i => ∑' k, poissonWeight (1 : ℝ) k * walkDensity asymSwapAdj k 0 i) := by
  intro h
  have hR : (fun i => ∑' k, poissonWeight (1 : ℝ) k * walkDensity asymSwapAdj k 0 i)
      = (![3, 0] : Fin 2 → ℝ) := by
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · simp only [Matrix.cons_val_zero, Matrix.head_cons]
      rw [show (fun k => poissonWeight (1:ℝ) k * walkDensity asymSwapAdj k 0 0)
        = fun k => poissonWeight (1:ℝ) k * 3 from funext fun k => by
          rw [asym_density_const k]
          rfl]
      rw [tsum_mul_right, poissonWeight_tsum_eq_one]
      norm_num
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
      rw [show (fun k => poissonWeight (1:ℝ) k * walkDensity asymSwapAdj k 0 1)
        = fun _ => (0 : ℝ) from funext fun k => by
          rw [asym_density_const k]
          norm_num]
      rw [tsum_zero]
  rw [asym_cont_density_one, hR] at h
  have h1eq := congrFun h (1 : Fin 2)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h1eq
  have hpos : Real.exp (-(1:ℝ)) < 1 := by
    have := Real.exp_lt_exp.mpr (by norm_num : -(1:ℝ) < 0)
    rwa [Real.exp_zero] at this
  linarith

/-- **The `hA` fence for the law-level identity**: LHS the closed form
`(1, 2(1 − e⁻¹))`, RHS the Poisson mixture of the constant laws
`(1, 0)`. -/
theorem contWalkDistribution_eq_tsum_hA_fence_QA :
    ¬ (contWalkDistribution asymSwapAdj 1 0
        = fun i => ∑' k, poissonWeight (1 : ℝ) k
            * walkDistribution asymSwapAdj k 0 i) := by
  intro h
  have hR : (fun i => ∑' k, poissonWeight (1 : ℝ) k
        * walkDistribution asymSwapAdj k 0 i)
      = (![1, 0] : Fin 2 → ℝ) := by
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · simp only [Matrix.cons_val_zero, Matrix.head_cons]
      rw [show (fun k => poissonWeight (1:ℝ) k * walkDistribution asymSwapAdj k 0 0)
        = fun k => poissonWeight (1:ℝ) k * 1 from funext fun k => by
          rw [asym_dist_const k]
          norm_num]
      rw [tsum_mul_right, poissonWeight_tsum_eq_one]
      norm_num
    · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]
      rw [show (fun k => poissonWeight (1:ℝ) k * walkDistribution asymSwapAdj k 0 1)
        = fun _ => (0 : ℝ) from funext fun k => by
          rw [asym_dist_const k]
          norm_num]
      rw [tsum_zero]
  rw [asym_cont_law_one, hR] at h
  have h1eq := congrFun h (1 : Fin 2)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h1eq
  have hpos : Real.exp (-(1:ℝ)) < 1 := by
    have := Real.exp_lt_exp.mpr (by norm_num : -(1:ℝ) < 0)
    rwa [Real.exp_zero] at this
  linarith

/-- **The `hA` fence for the stationary power**: `Pᵀ π = (1, 0) ≠
(1/3, 2/3) = π` at `k = 1` — the adjoint-walk power fixes `π` only
under symmetry (detailed balance). -/
theorem stationary_pow_hA_fence_QA :
    ¬ ((walkTransitionMatrix asymSwapAdj)ᵀ ^ 1 *ᵥ stationaryVec asymSwapAdj
        = stationaryVec asymSwapAdj) := by
  intro h
  rw [pow_one, asym_hπ] at h
  have hval : (walkTransitionMatrix asymSwapAdj)ᵀ *ᵥ (![1/3, 2/3] : Fin 2 → ℝ)
      = ![1, 0] := by
    funext (i : Fin 2)
    rcases (show i = 0 ∨ i = 1 by omega) with hi | hi <;> rw [hi]
    · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.cons_val_one]
      rw [asym_walk_00, asym_walk_10]
      norm_num
    · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.cons_val_one]
      rw [asym_walk_01, asym_walk_11]
      norm_num
  rw [hval] at h
  have h1eq := congrFun h (1 : Fin 2)
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at h1eq
  norm_num at h1eq

/-! ### The swap at `t = 2`: the rate theorems' `hA` clauses -/

theorem asym_heat_two : walkHeatKernel asymSwapAdj 2
    = 1 + ((1 - Real.exp (-(2:ℝ)))) • (-(walkLaplacian asymSwapAdj)) := by
  have hsq : (-(walkLaplacian asymSwapAdj)) * (-(walkLaplacian asymSwapAdj))
      = (-1 : ℝ) • (-(walkLaplacian asymSwapAdj)) := by
    rw [neg_mul_neg, asym_L_sq, one_smul, neg_smul, one_smul, neg_neg]
  have hM : ((2 : ℝ) • (-(walkLaplacian asymSwapAdj)))
        * ((2 : ℝ) • (-(walkLaplacian asymSwapAdj)))
      = (-(2 : ℝ)) • ((2 : ℝ) • (-(walkLaplacian asymSwapAdj))) := by
    rw [smul_mul_smul_comm, hsq, smul_smul, smul_smul]
    norm_num
  rw [walkHeatKernel, ← smul_neg,
    exp_eq_one_add_of_mul_self_eq_smul _ (by norm_num) hM,
    show ((Real.exp (-(2:ℝ)) - 1) / (-(2:ℝ)))
        • ((2 : ℝ) • (-(walkLaplacian asymSwapAdj)))
        = (1 - Real.exp (-(2:ℝ))) • (-(walkLaplacian asymSwapAdj)) from by
      rw [smul_smul]
      congr 1
      field_simp
      ring]

theorem asym_cont_density_two :
    contWalkDensity asymSwapAdj 2 0 = ![3, 3 * (1 - Real.exp (-(2:ℝ)))] := by
  rw [contWalkDensity, asym_density_zero, asym_heat_two,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec_assoc,
    asym_negL_mulVec]
  funext (i : Fin 2)
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, Pi.smul_apply,
      smul_eq_mul, Pi.add_apply]
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    ring

theorem asym_cont_law_two :
    contWalkDistribution asymSwapAdj 2 0
      = ![1, 2 * (1 - Real.exp (-(2:ℝ)))] := by
  funext (i : Fin 2)
  rw [contWalkDistribution, asym_cont_density_two]
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, asymSwap_pi_zero]
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      asymSwap_pi_one]
    ring

theorem asym_cont_tv_two :
    tvDistance (contWalkDistribution asymSwapAdj 2 0) (stationaryVec asymSwapAdj)
      = 1 - Real.exp (-(2:ℝ)) := by
  have hE : Real.exp (-(2:ℝ)) < 1/4 := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 4)).mpr
      pf_four_lt_exp_two
  rw [asym_cont_law_two, asym_hπ, pf_tv_lit]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 - 1/3 by norm_num),
    abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 - Real.exp (-(2:ℝ))) - 2/3)]
  ring

theorem asym_disc_tv_const (k : ℕ) :
    tvDistance (walkDistribution asymSwapAdj k 0) (stationaryVec asymSwapAdj)
      = 2/3 := by
  rw [asym_dist_const k, asym_hπ, pf_tv_lit]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 1 - 1/3 by norm_num),
    abs_of_neg (show (0 : ℝ) - 2/3 < 0 by norm_num)]
  norm_num

/-- **The `hA` fence for the Poisson-averaged TV bound**: the
continuous TV at `t = 2` is `1 − e⁻² > 2/3` (from `e² > 4`), while the
Poisson average of the constant discrete TVs is exactly `2/3`. -/
theorem cont_le_tsum_hA_fence_QA :
    ¬ (tvDistance (contWalkDistribution asymSwapAdj 2 0) (stationaryVec asymSwapAdj)
        ≤ ∑' k, poissonWeight (2 : ℝ) k
            * tvDistance (walkDistribution asymSwapAdj k 0)
                (stationaryVec asymSwapAdj)) := by
  intro h
  have hR : ∑' k, poissonWeight (2 : ℝ) k
      * tvDistance (walkDistribution asymSwapAdj k 0) (stationaryVec asymSwapAdj)
      = 2/3 := by
    rw [tsum_congr (fun k => by rw [asym_disc_tv_const k]), tsum_mul_right,
      poissonWeight_tsum_eq_one]
    norm_num
  rw [hR, asym_cont_tv_two] at h
  have h4 : (4 : ℝ) < Real.exp 2 := pf_four_lt_exp_two
  have hE : Real.exp (-(2:ℝ)) < 1/3 := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 3)).mpr
      (by linarith)
  linarith

/-- **The `hA` fence for the comparability**: at `m = 0` the split
reads `TV_cont ≤ TV_disc(0)`, i.e. `1 − e⁻² ≤ 2/3`. -/
theorem comparability_hA_fence_QA :
    ¬ (tvDistance (contWalkDistribution asymSwapAdj 2 0) (stationaryVec asymSwapAdj)
        ≤ ∑ k in Finset.range 0, poissonWeight (2 : ℝ) k
          + tvDistance (walkDistribution asymSwapAdj 0 0)
              (stationaryVec asymSwapAdj)) := by
  intro h
  rw [Finset.sum_range_zero, asym_disc_tv_const 0, asym_cont_tv_two] at h
  have h4 : (4 : ℝ) < Real.exp 2 := pf_four_lt_exp_two
  have hE : Real.exp (-(2:ℝ)) < 1/3 := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 3)).mpr
      (by linarith)
  linarith

/-- **The `hA` fence for the transfer corollary**, with both
certificate clauses genuine (`ε₁ = 2/3` attained, the empty head
`≤ 0`): `1 − e⁻² ≤ 2/3 + 0` refuted. -/
theorem transfer_hA_fence_QA :
    ¬ (tvDistance (contWalkDistribution asymSwapAdj 2 0) (stationaryVec asymSwapAdj)
        ≤ 2/3 + 0) := by
  intro h
  rw [asym_cont_tv_two] at h
  have h4 : (4 : ℝ) < Real.exp 2 := pf_four_lt_exp_two
  have hE : Real.exp (-(2:ℝ)) < 1/3 := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 3)).mpr
      (by linarith)
  linarith

theorem transfer_hA_isolation_QA :
    (∀ k : ℕ, 0 ≤ k →
      tvDistance (walkDistribution asymSwapAdj k 0) (stationaryVec asymSwapAdj)
        ≤ 2/3)
      ∧ (∑ k in Finset.range 0, poissonWeight (2 : ℝ) k ≤ 0) := by
  refine ⟨fun k _ => le_of_eq (asym_disc_tv_const k), ?_⟩
  rw [Finset.sum_range_zero]

/-! ### The edge at negative time: the `ht` clauses -/

theorem k2_cont_law_neg_one :
    contWalkDistribution k2Adj (-(1:ℝ)) 0
      = ![(1 + Real.exp 2)/2, (1 - Real.exp 2)/2] := by
  funext (i : Fin 2)
  rw [contWalkDistribution, k2_cont_density_neg_one]
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · simp only [Matrix.cons_val_zero, Matrix.head_cons, k2_pi_QA 0,
      Pi.smul_apply, smul_eq_mul]
    ring
  · simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      k2_pi_QA 1, Pi.smul_apply, smul_eq_mul]
    ring

theorem k2_hπ : stationaryVec k2Adj = ![1/2, 1/2] := by
  funext (i : Fin 2)
  rcases (show i = 0 ∨ i = 1 by omega) with h | h <;> rw [h]
  · exact k2_pi_QA 0
  · exact k2_pi_QA 1

theorem k2_cont_tv_neg_one :
    tvDistance (contWalkDistribution k2Adj (-(1:ℝ)) 0) (stationaryVec k2Adj)
      = Real.exp 2 / 2 := by
  rw [k2_cont_law_neg_one, k2_hπ, pf_tv_lit]
  rw [abs_of_nonneg (show (0 : ℝ) ≤ (1 + Real.exp 2)/2 - 1/2 by
        have := Real.exp_pos 2
        linarith),
    abs_of_neg (show (1 - Real.exp 2)/2 - 1/2 < 0 by
        have := Real.exp_pos 2
        linarith)]
  ring

/-- **The `ht` fence for the Poisson-averaged TV bound**: at `t = −1`
the signed weights `e·(−1)ᵏ/k!` (mass one, sign-alternating) leave the
continuous TV at `e²/2` against the Poisson average of the constant
discrete TVs `1/2`. -/
theorem cont_le_tsum_ht_fence_QA :
    ¬ (tvDistance (contWalkDistribution k2Adj (-(1:ℝ)) 0) (stationaryVec k2Adj)
        ≤ ∑' k, poissonWeight (-(1:ℝ)) k
            * tvDistance (walkDistribution k2Adj k 0) (stationaryVec k2Adj)) := by
  intro h
  have hR : ∑' k, poissonWeight (-(1:ℝ)) k
      * tvDistance (walkDistribution k2Adj k 0) (stationaryVec k2Adj)
      = 1/2 := by
    rw [tsum_congr (fun k => by rw [k2_disc_tv_eq_QA k]), tsum_mul_right,
      poissonWeight_tsum_eq_one]
    norm_num
  rw [hR, k2_cont_tv_neg_one] at h
  have h1 : (1 : ℝ) < Real.exp 2 := by
    have := Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
    rwa [Real.exp_zero] at this
  linarith

/-- **The `ht` fence for the comparability** at `m = 0`: `e²/2 ≤
0 + 1/2` refuted. -/
theorem comparability_ht_fence_QA :
    ¬ (tvDistance (contWalkDistribution k2Adj (-(1:ℝ)) 0) (stationaryVec k2Adj)
        ≤ ∑ k in Finset.range 0, poissonWeight (-(1:ℝ)) k
          + tvDistance (walkDistribution k2Adj 0 0) (stationaryVec k2Adj)) := by
  intro h
  rw [Finset.sum_range_zero, k2_disc_tv_eq_QA 0, k2_cont_tv_neg_one] at h
  have h1 : (1 : ℝ) < Real.exp 2 := by
    have := Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
    rwa [Real.exp_zero] at this
  linarith

/-- **The `ht` fence for the transfer corollary**, both certificate
clauses genuine: `e²/2 ≤ 1/2 + 0` refuted. -/
theorem transfer_ht_fence_QA :
    ¬ (tvDistance (contWalkDistribution k2Adj (-(1:ℝ)) 0) (stationaryVec k2Adj)
        ≤ 1/2 + 0) := by
  intro h
  rw [k2_cont_tv_neg_one] at h
  have h1 : (1 : ℝ) < Real.exp 2 := by
    have := Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 2)
    rwa [Real.exp_zero] at this
  linarith

theorem transfer_ht_isolation_QA :
    (∀ k : ℕ, 0 ≤ k →
      tvDistance (walkDistribution k2Adj k 0) (stationaryVec k2Adj) ≤ 1/2)
      ∧ (∑ k in Finset.range 0, poissonWeight (-(1:ℝ)) k ≤ 0) := by
  refine ⟨fun k _ => le_of_eq (k2_disc_tv_eq_QA k), ?_⟩
  rw [Finset.sum_range_zero]

/-! ### The triangle: the transfer corollary's `htail` clause -/

/-- **The `htail` fence**: on the genuine triangle at `t = 1/2`,
`m = 2`, the discrete certificate `ε₁ = 1/6` is genuine
(`TV_disc(k) = (2/3)·2⁻ᵏ ≤ 1/6` for `k ≥ 2`) while the tail budget
`ε₂ = 1/20` understates the honest head `(3/2)e^{−1/2}` — and the
conclusion `(2/3)e^{−3/4} ≤ 13/60` is refuted from `e < 3`
(`e^{−3/4} > 1/3`, so the left side exceeds `2/9 > 13/60`). -/
theorem transfer_htail_fence_QA :
    ¬ (tvDistance (contWalkDistribution triAdj (1/2 : ℝ) 0) (stationaryVec triAdj)
        ≤ 1/6 + 1/20) := by
  intro h
  have htv : tvDistance (contWalkDistribution triAdj (1/2 : ℝ) 0)
      (stationaryVec triAdj) = (2/3) * Real.exp (-(3/4 : ℝ)) := by
    rw [tri_cont_tv_eq (1/2 : ℝ)]
    congr 1
    norm_num
  rw [htv] at h
  have h1 : Real.exp (1 : ℝ) < 3 := exp_one_lt_three
  have h34 : Real.exp (3/4 : ℝ) < 3 := by
    have hle : Real.exp (3/4 : ℝ) ≤ Real.exp (1 : ℝ) :=
      Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hinv : Real.exp (-(3/4 : ℝ)) > 1/3 := by
    rw [Real.exp_neg, one_div]
    exact (inv_lt_inv₀ (show (0 : ℝ) < 3 by norm_num)
      (Real.exp_pos (3/4 : ℝ))).mpr h34
  have hlow : (2/9 : ℝ) < (2/3) * Real.exp (-(3/4 : ℝ)) := by
    rw [show (2/9 : ℝ) = (2/3) * (1/3) from by norm_num]
    exact (mul_lt_mul_left (show (0 : ℝ) < 2/3 by norm_num)).mpr hinv
  have hsum : (1/6 : ℝ) + 1/20 = 13/60 := by norm_num
  rw [hsum] at h
  have hbound : ¬ ((2/9 : ℝ) ≤ 13/60) := by norm_num
  exact absurd (le_trans (le_of_lt hlow) h) hbound

theorem transfer_htail_isolation_QA :
    (∀ k : ℕ, 2 ≤ k →
      tvDistance (walkDistribution triAdj k 0) (stationaryVec triAdj) ≤ 1/6)
      ∧ ¬ (∑ k in Finset.range 2, poissonWeight (1/2 : ℝ) k ≤ 1/20) := by
  refine ⟨?_, ?_⟩
  · intro k hk
    rw [tri_disc_tv_eq_QA k]
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
      have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
      norm_num at hp
      exact hp
    have hpos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) k
    have hinv : (1/2 : ℝ) ^ k = 1 / ((2 : ℝ) ^ k) := _root_.one_div_pow 2 k
    have hkey : (1 : ℝ) / ((2 : ℝ) ^ k) ≤ 1/4 :=
      (one_div_le_one_div hpos (by norm_num : (0 : ℝ) < 4)).mpr h4
    rw [hinv]
    have hfinal : (2/3 : ℝ) * (1 / ((2 : ℝ) ^ k)) ≤ 2/3 * (1/4) := by
      exact mul_le_mul_of_nonneg_left hkey (by norm_num)
    norm_num at hfinal
    linarith
  · intro hcon
    have hhead : ∑ k in Finset.range 2, poissonWeight (1/2 : ℝ) k
        = (3/2) * Real.exp (-(1/2 : ℝ)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [poissonWeight]
      ring_nf
    rw [hhead] at hcon
    have h1 : Real.exp (1 : ℝ) < 3 := exp_one_lt_three
    have hhalf : Real.exp (1/2 : ℝ) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by norm_num)
    have hinv : (1/3 : ℝ) ≤ Real.exp (-(1/2 : ℝ)) := by
      rw [Real.exp_neg, one_div]
      refine (inv_le_inv₀ (show (0 : ℝ) < 3 by norm_num)
        (Real.exp_pos (1/2 : ℝ))).mpr ?_
      linarith
    have hlow : (3/2) * (1/3 : ℝ) ≤ (3/2) * Real.exp (-(1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    norm_num at hlow
    linarith

/-! ### The isolation companions (per fixture) -/

theorem negOff_isolation_QA :
    negOffAdj.IsSymm
      ∧ (∀ i, 0 < deg negOffAdj i)
      ∧ ¬ (∀ i j, 0 ≤ negOffAdj i j) := by
  refine ⟨negOffAdj_isSymm, negOffAdj_deg_pos, ?_⟩
  intro hnn
  have h01 := hnn 0 1
  rw [negOff_01] at h01
  norm_num at h01

theorem asymSwap_isolation_QA :
    (∀ i j, 0 ≤ asymSwapAdj i j)
      ∧ (∀ i, 0 < deg asymSwapAdj i)
      ∧ ¬ asymSwapAdj.IsSymm :=
  ⟨asymSwapAdj_nonneg, asymSwapAdj_deg_pos, asymSwapAdj_not_isSymm⟩

theorem asymFlow_isolation_QA :
    (∀ i j, 0 ≤ asymFlowAdj i j)
      ∧ (∀ i, 0 < deg asymFlowAdj i)
      ∧ ¬ asymFlowAdj.IsSymm :=
  ⟨asymFlowAdj_nonneg, asymFlowAdj_deg_pos, asymFlowAdj_not_isSymm⟩

theorem k2_negT_isolation_QA :
    k2Adj.IsSymm
      ∧ (∀ i j, 0 ≤ k2Adj i j)
      ∧ (∀ i, 0 < deg k2Adj i)
      ∧ ¬ (0 ≤ -(1 : ℝ)) :=
  ⟨k2Adj_isSymm, k2Adj_nonneg, fun i => by rw [k2Adj_deg_eq i]; norm_num,
    by norm_num⟩

end PoissonFences

section LazyFollowOnFences

/-! ### The conjugated-norm contraction twin's two certificate fences -/

/-- Generic helper: the conjugated norm of a scalar multiple is the
scalar's square times the conjugated norm. -/
theorem conj_norm_smul {V : Type} [Fintype V] (M : Matrix V V ℝ) (c : ℝ)
    (v : V → ℝ) :
    Matrix.dotProduct (M *ᵥ (c • v)) (M *ᵥ (c • v))
      = c * c * Matrix.dotProduct (M *ᵥ v) (M *ᵥ v) := by
  simp only [Matrix.mulVec_smul, Matrix.dotProduct, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The triangle's conjugated norm at the mode direction:
`⟨√D *ᵥ g, √D *ᵥ g⟩ = 4` (unit degrees `2`, so `√D = √2 • ·`, and
`‖g‖² = 1 + 1 + 0 = 2`). -/
theorem tri_conj_norm_mode_QA :
    Matrix.dotProduct (degreeSqrt triAdj *ᵥ (![1, -1, 0] : Fin 3 → ℝ))
      (degreeSqrt triAdj *ᵥ (![1, -1, 0] : Fin 3 → ℝ)) = 4 := by
  rw [tri_degreeSqrt_mulVec_eq]
  have hgg : Matrix.dotProduct (![1, -1, 0] : Fin 3 → ℝ)
      (![1, -1, 0] : Fin 3 → ℝ) = 2 := by
    rw [Matrix.dotProduct, Fin.sum_univ_three]; norm_num
  have hs : Real.sqrt 2 * (Real.sqrt 2 * 2) = 4 := by
    have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
    have hrw : Real.sqrt 2 * (Real.sqrt 2 * 2) = (Real.sqrt 2)^2 * 2 := by
      ring
    rw [hrw, h2]
    norm_num
  rw [Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul, hgg]
  exact hs

/-- **The `hrate` fence for the conjugated-norm contraction twin**
(`dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix_contraction`):
on the triangle at `g = (1, −1, 0)` (a genuine `3/2`-mode direction with
`P_L *ᵥ g = (1/4) • g`), the below-mode certificate `r = 1/8` is
strictly below the mode's lazy factor `1/4`, and the conclusion is
refuted: `LHS = (1/4)² · 4 = 1/4 > 1/16 = (1/8)² · 4 = RHS` — the
√D-weighted mirror of `tri_lazy_rate_fence_QA`. -/
theorem tri_conj_rate_fence_QA :
    ¬ (Matrix.dotProduct
         (degreeSqrt triAdj *ᵥ ((lazyWalkTransitionMatrix triAdj ^ (1 : ℕ)) *ᵥ
             (![1, -1, 0] : Fin 3 → ℝ)))
         (degreeSqrt triAdj *ᵥ ((lazyWalkTransitionMatrix triAdj ^ (1 : ℕ)) *ᵥ
             (![1, -1, 0] : Fin 3 → ℝ)))
       ≤ (1/8 : ℝ) ^ (2 * 1)
         * Matrix.dotProduct (degreeSqrt triAdj *ᵥ (![1, -1, 0] : Fin 3 → ℝ))
             (degreeSqrt triAdj *ᵥ (![1, -1, 0] : Fin 3 → ℝ))) := by
  intro h
  rw [tri_lazy_mulVec_mode_QA, conj_norm_smul, tri_conj_norm_mode_QA] at h
  norm_num at h

/-- **The `hmode` fence for the conjugated-norm contraction twin**: on
the edge at `g = (1, 1)` — the constant zero mode itself — with the
genuine certificate `r = 0` (the only nonzero mode is `μ = 2`, lazy
factor `0`), the conclusion is refuted: `P_L *ᵥ 1 = 1` and `√D = 1`,
so `LHS = ‖1‖² = 2 > 0 = 0² · 2 = RHS` — the √D-weighted mirror of
`k2_lazy_mode_fence_QA`. -/
theorem k2_conj_mode_fence_QA :
    ¬ (Matrix.dotProduct
         (degreeSqrt k2Adj *ᵥ ((lazyWalkTransitionMatrix k2Adj ^ (1 : ℕ)) *ᵥ
             (![1, 1] : Fin 2 → ℝ)))
         (degreeSqrt k2Adj *ᵥ ((lazyWalkTransitionMatrix k2Adj ^ (1 : ℕ)) *ᵥ
             (![1, 1] : Fin 2 → ℝ)))
       ≤ (0 : ℝ) ^ (2 * 1)
         * Matrix.dotProduct (degreeSqrt k2Adj *ᵥ (![1, 1] : Fin 2 → ℝ))
             (degreeSqrt k2Adj *ᵥ (![1, 1] : Fin 2 → ℝ))) := by
  intro h
  have hone : (![1, 1] : Fin 2 → ℝ) = 1 := by
    funext i
    fin_cases i <;> simp
  have hfix : (lazyWalkTransitionMatrix k2Adj ^ (1 : ℕ)) *ᵥ
      (![1, 1] : Fin 2 → ℝ) = (1 : Fin 2 → ℝ) := by
    rw [pow_one, hone, lazyWalkTransitionMatrix_mulVec_one k2Adj k2Adj_deg_pos]
  rw [hfix, k2_degreeSqrt_mulVec, k2_degreeSqrt_mulVec] at h
  simp only [Matrix.dotProduct, Fin.sum_univ_two, Pi.one_apply, one_mul,
    zero_pow (by norm_num : (2 * 1 : ℕ) ≠ 0), zero_mul] at h
  norm_num at h

/-- The isolation record for both conjugated-twin fences: at each
fixture the *other* certificate clause is genuine and the dropped one
fails — through the already-delivered ℓ²(π) companions, whose
statements are *identical* to the conjugated twin's clauses (the two
engines share `hmode`/`hrate` verbatim; the structural clauses `hA`/`hd`
are `triAdj_isSymm`/`triAdj_deg_pos` and `k2Adj_isSymm`/`k2Adj_deg_pos`). -/
theorem conj_twin_isolation_QA :
    (∀ i : Fin 3, eigvalOf (normalizedLaplacian triAdj)
        (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i = 0 →
      Matrix.dotProduct
        (eigvecOf (normalizedLaplacian triAdj)
          (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i)
        (degreeSqrt triAdj *ᵥ (![1, -1, 0] : Fin 3 → ℝ)) = 0)
      ∧ ¬ (∀ i : Fin 3, eigvalOf (normalizedLaplacian triAdj)
            (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i ≠ 0 →
          |1 - eigvalOf (normalizedLaplacian triAdj)
              (normalizedLaplacian_symmetric triAdj triAdj_isSymm) i / 2|
            ≤ 1/8)
      ∧ (∀ i : Fin 2, eigvalOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i ≠ 0 →
          |1 - eigvalOf (normalizedLaplacian k2Adj)
              (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i / 2|
            ≤ 0)
      ∧ ¬ (∀ i : Fin 2, eigvalOf (normalizedLaplacian k2Adj)
            (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i = 0 →
          Matrix.dotProduct
            (eigvecOf (normalizedLaplacian k2Adj)
              (normalizedLaplacian_symmetric k2Adj k2Adj_isSymm) i)
            (degreeSqrt k2Adj *ᵥ (![1, 1] : Fin 2 → ℝ)) = 0) :=
  ⟨tri_lazy_mode_genuine_QA, tri_lazy_rate_fails_QA,
    k2_lazy_rate_genuine_QA, k2_lazy_mode_fails_QA⟩

/-! ### The lazy object's `_spec` junk corner at `K₂ ⊕ K₂` -/

/-- The `Fin 4` case split, mirroring `fin4_eq` (the val split by
`omega`, then `Fin.ext` per branch). -/
theorem lfFin4 (v : Fin 4) : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 := by
  have hv : v.val < 4 := v.isLt
  rcases (show v.val = 0 ∨ v.val = 1 ∨ v.val = 2 ∨ v.val = 3 by omega) with
    h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

/-- The disconnected bipartite fixture `K₂ ⊕ K₂` on `Fin 4`: two
disjoint edges. Symmetric, nonnegative, every degree positive — every
structural hypothesis of the lazy family genuine — but disconnected:
the lazy walk from `0` converges to the *component*-stationary
`(1/2, 1/2, 0, 0) ≠ π`, so no mixing threshold is ever reached and the
lazy object's witness set is empty at every `ε < 1/2`. -/
def dK2Adj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

theorem dK2Adj_00 : dK2Adj 0 0 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_01 : dK2Adj 0 1 = 1 := by rw [dK2Adj]; rfl
theorem dK2Adj_02 : dK2Adj 0 2 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_03 : dK2Adj 0 3 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_10 : dK2Adj 1 0 = 1 := by rw [dK2Adj]; rfl
theorem dK2Adj_11 : dK2Adj 1 1 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_12 : dK2Adj 1 2 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_13 : dK2Adj 1 3 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_20 : dK2Adj 2 0 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_21 : dK2Adj 2 1 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_22 : dK2Adj 2 2 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_23 : dK2Adj 2 3 = 1 := by rw [dK2Adj]; rfl
theorem dK2Adj_30 : dK2Adj 3 0 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_31 : dK2Adj 3 1 = 0 := by rw [dK2Adj]; rfl
theorem dK2Adj_32 : dK2Adj 3 2 = 1 := by rw [dK2Adj]; rfl
theorem dK2Adj_33 : dK2Adj 3 3 = 0 := by rw [dK2Adj]; rfl

theorem dK2Adj_isSymm : dK2Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rcases lfFin4 i with hi | hi | hi | hi <;>
    rcases lfFin4 j with hj | hj | hj | hj
  all_goals subst hi; all_goals subst hj
  all_goals rfl

theorem dK2Adj_nonneg (i j : Fin 4) : 0 ≤ dK2Adj i j := by
  rcases lfFin4 i with hi | hi | hi | hi <;>
    rcases lfFin4 j with hj | hj | hj | hj
  all_goals subst hi; all_goals subst hj
  all_goals first | rfl | exact zero_le_one

theorem dK2Adj_deg_eq (i : Fin 4) : deg dK2Adj i = 1 := by
  rcases lfFin4 i with h | h | h | h
  · subst h; rw [deg, Fin.sum_univ_four, dK2Adj_00, dK2Adj_01, dK2Adj_02,
      dK2Adj_03]; norm_num
  · subst h; rw [deg, Fin.sum_univ_four, dK2Adj_10, dK2Adj_11, dK2Adj_12,
      dK2Adj_13]; norm_num
  · subst h; rw [deg, Fin.sum_univ_four, dK2Adj_20, dK2Adj_21, dK2Adj_22,
      dK2Adj_23]; norm_num
  · subst h; rw [deg, Fin.sum_univ_four, dK2Adj_30, dK2Adj_31, dK2Adj_32,
      dK2Adj_33]; norm_num

theorem dK2Adj_deg_pos (i : Fin 4) : 0 < deg dK2Adj i := by
  rw [dK2Adj_deg_eq]
  norm_num

theorem dK2Adj_vol : vol dK2Adj (Finset.univ : Finset (Fin 4)) = 4 := by
  simp only [vol, dK2Adj_deg_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

theorem dK2Adj_pi (i : Fin 4) : stationaryVec dK2Adj i = 1/4 := by
  simp only [stationaryVec, dK2Adj_vol, dK2Adj_deg_eq]

/-- The support graph's off-block entries vanish: from the first block,
no positive entry reaches the second. -/
theorem dK2Adj_off_zero : ∀ i j : Fin 4, i.val < 2 → 2 ≤ j.val →
    dK2Adj i j = 0 := by
  intro i j hi hj
  rcases lfFin4 j with hj2 | hj2 | hj2 | hj2
  · subst hj2; exact absurd hj (by omega)
  · subst hj2; exact absurd hj (by omega)
  · subst hj2
    rcases lfFin4 i with h | h | h | h
    · subst h; exact dK2Adj_02
    · subst h; exact dK2Adj_12
    · subst h; exact absurd hi (by omega)
    · subst h; exact absurd hi (by omega)
  · subst hj2
    rcases lfFin4 i with h | h | h | h
    · subst h; exact dK2Adj_03
    · subst h; exact dK2Adj_13
    · subst h; exact absurd hi (by omega)
    · subst h; exact absurd hi (by omega)

/-- Walks from the first block cannot reach the second: adjacency out
of the block stays in the block. -/
theorem dK2Adj_walk_stays : ∀ {i j : Fin 4},
    (supportGraph dK2Adj dK2Adj_isSymm).Walk i j → i.val < 2 → j.val < 2 := by
  intro i j w
  induction w with
  | nil => intro hi; exact hi
  | @cons u k v hadj rest ih =>
    intro hi
    have hk : k.val < 2 := by
      obtain ⟨_, hpos⟩ := supportGraph_adj.1 hadj
      by_contra hcon
      have hk2 : 2 ≤ k.val := by omega
      have h0 : dK2Adj u k = 0 := dK2Adj_off_zero u k hi hk2
      rw [h0] at hpos
      norm_num at hpos
    exact ih hk

theorem dK2Adj_not_connected :
    ¬ (supportGraph dK2Adj dK2Adj_isSymm).Connected := by
  intro hconn
  obtain ⟨w⟩ := hconn.1 0 2
  have := dK2Adj_walk_stays w (by decide)
  exact absurd this (by decide)

/-- The structural isolation: the fixture is genuine on every axis the
lazy family's hypotheses name — symmetric, nonnegative, positive
degrees — with connectivity (the ceiling's own hypothesis) exactly the
failure. Laziness repairs periodicity, not disconnection. -/
theorem dK2_fence_isolation_QA :
    dK2Adj.IsSymm ∧ (∀ i j : Fin 4, 0 ≤ dK2Adj i j)
      ∧ (∀ i : Fin 4, 0 < deg dK2Adj i)
      ∧ ¬ (supportGraph dK2Adj dK2Adj_isSymm).Connected :=
  ⟨dK2Adj_isSymm, dK2Adj_nonneg, dK2Adj_deg_pos, dK2Adj_not_connected⟩

/-- One lazy step preserves the start's component: for any law
supported on `{0, 1}`, the lazy evolution is supported on `{0, 1}` with
both entries the average `(ν 0 + ν 1)/2` — the block structure in one
step. -/
theorem dK2_lazy_step (ν : Fin 4 → ℝ) (h2 : ν 2 = 0) (h3 : ν 3 = 0) :
    (lazyWalkTransitionMatrix dK2Adj)ᵀ *ᵥ ν
      = ![(ν 0 + ν 1) / 2, (ν 0 + ν 1) / 2, 0, 0] := by
  have hsplit : ∀ j : Fin 4, ((lazyWalkTransitionMatrix dK2Adj)ᵀ *ᵥ ν) j
      = (2 : ℝ)⁻¹ * (((walkTransitionMatrix dK2Adj)ᵀ *ᵥ ν) j + ν j) := by
    intro j
    calc ((lazyWalkTransitionMatrix dK2Adj)ᵀ *ᵥ ν) j
        = (((2 : ℝ)⁻¹ • ((walkTransitionMatrix dK2Adj)ᵀ
            + (1 : Matrix (Fin 4) (Fin 4) ℝ))) *ᵥ ν) j := by
              rw [lazyWalkTransitionMatrix, Matrix.transpose_smul,
                Matrix.transpose_add, Matrix.transpose_one]
      _ = ((2 : ℝ)⁻¹ • (((walkTransitionMatrix dK2Adj)ᵀ *ᵥ ν
            + (1 : Matrix (Fin 4) (Fin 4) ℝ) *ᵥ ν))) j := by
              rw [Matrix.smul_mulVec_assoc, Matrix.add_mulVec]
      _ = (2 : ℝ)⁻¹ * (((walkTransitionMatrix dK2Adj)ᵀ *ᵥ ν) j + ν j) := by
              simp
  have hP : ∀ j : Fin 4, ((walkTransitionMatrix dK2Adj)ᵀ *ᵥ ν) j
      = ∑ k, (deg dK2Adj k)⁻¹ * dK2Adj k j * ν k := by
    intro j
    rw [Matrix.mulVec, Matrix.dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.transpose_apply, walkTransitionMatrix_apply]
  funext j
  rcases lfFin4 j with hj | hj | hj | hj
  · subst hj
    rw [hsplit 0, hP 0, Fin.sum_univ_four, h2, h3]
    simp only [dK2Adj_deg_eq, dK2Adj_00, dK2Adj_10, dK2Adj_20, dK2Adj_30]
    have er : (![(ν 0 + ν 1) / 2, (ν 0 + ν 1) / 2, 0, 0] : Fin 4 → ℝ) 0
        = (ν 0 + ν 1) / 2 := rfl
    rw [er]
    ring
  · subst hj
    rw [hsplit 1, hP 1, Fin.sum_univ_four, h2, h3]
    simp only [dK2Adj_deg_eq, dK2Adj_01, dK2Adj_11, dK2Adj_21, dK2Adj_31]
    have er : (![(ν 0 + ν 1) / 2, (ν 0 + ν 1) / 2, 0, 0] : Fin 4 → ℝ) 1
        = (ν 0 + ν 1) / 2 := rfl
    rw [er]
    ring
  · subst hj
    rw [hsplit 2, hP 2, Fin.sum_univ_four, h2, h3]
    simp only [dK2Adj_deg_eq, dK2Adj_02, dK2Adj_12, dK2Adj_22, dK2Adj_32]
    have er : (![(ν 0 + ν 1) / 2, (ν 0 + ν 1) / 2, 0, 0] : Fin 4 → ℝ) 2 = 0 :=
      rfl
    rw [er]
    norm_num
  · subst hj
    rw [hsplit 3, hP 3, Fin.sum_univ_four, h2, h3]
    simp only [dK2Adj_deg_eq, dK2Adj_03, dK2Adj_13, dK2Adj_23, dK2Adj_33]
    have er : (![(ν 0 + ν 1) / 2, (ν 0 + ν 1) / 2, 0, 0] : Fin 4 → ℝ) 3 = 0 :=
      rfl
    rw [er]
    norm_num

/-- **The lazy law closed form on `K₂ ⊕ K₂` from `0`**: the law is
`δ₀` at time zero and the component-stationary `(1/2, 1/2, 0, 0)` at
every positive time — convergent, but to the wrong vector. -/
theorem dK2_lazy_law_succ_QA (t : ℕ) :
    lazyWalkDistribution dK2Adj (t + 1) 0 = ![(1/2 : ℝ), 1/2, 0, 0] := by
  induction t with
  | zero =>
    rw [lazyWalkDistribution_succ, lazyWalkDistribution_zero,
      dK2_lazy_step _ (by simp) (by simp)]
    funext i
    fin_cases i <;> simp [Pi.single_apply]
  | succ t ih =>
    rw [lazyWalkDistribution_succ, ih, dK2_lazy_step _ (by norm_num) (by norm_num)]
    funext i
    fin_cases i <;> norm_num

/-- **The lazy TV at time zero**: `TV(δ₀, π) = 3/4`. -/
theorem dK2_lazy_tv_zero_QA :
    tvDistance (lazyWalkDistribution dK2Adj 0 0) (stationaryVec dK2Adj)
      = 3/4 := by
  have hvec : (Pi.single (0 : Fin 4) (1 : ℝ)) = ![1, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp
  rw [lazyWalkDistribution_zero, hvec, tvDistance, Fin.sum_univ_four]
  simp only [dK2Adj_pi]
  norm_num
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3/4),
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/4)]
  norm_num

/-- **The lazy TV at every positive time**: `TV = 1/2` exactly — the
mass `1/2` stranded on the other component, never mixed away. -/
theorem dK2_lazy_tv_succ_QA (t : ℕ) :
    tvDistance (lazyWalkDistribution dK2Adj (t + 1) 0)
      (stationaryVec dK2Adj) = 1/2 := by
  rw [dK2_lazy_law_succ_QA t, tvDistance, Fin.sum_univ_four]
  have e0 : (![(1/2 : ℝ), 1/2, 0, 0] : Fin 4 → ℝ) 0 = 1/2 := rfl
  have e1 : (![(1/2 : ℝ), 1/2, 0, 0] : Fin 4 → ℝ) 1 = 1/2 := rfl
  have e2 : (![(1/2 : ℝ), 1/2, 0, 0] : Fin 4 → ℝ) 2 = 0 := rfl
  have e3 : (![(1/2 : ℝ), 1/2, 0, 0] : Fin 4 → ℝ) 3 = 0 := rfl
  simp only [e0, e1, e2, e3, dK2Adj_pi]
  norm_num
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/4)]
  norm_num

/-- **The disconnected-input fence**: no lazy mixing witness exists on
`K₂ ⊕ K₂` at threshold `1/8` — the lazy TV is `3/4` at time zero and
`1/2` at every positive time, never below `1/8`. -/
theorem dK2_lazy_no_mixing_QA :
    ¬ ∃ t : ℕ, ∀ s : ℕ, t ≤ s →
      tvDistance (lazyWalkDistribution dK2Adj s 0) (stationaryVec dK2Adj)
        ≤ 1/8 := by
  intro h
  obtain ⟨t, ht⟩ := h
  have hbot := ht (t + 1) (by omega)
  rw [dK2_lazy_tv_succ_QA t] at hbot
  norm_num at hbot

/-- **The junk corner pinned**: on the disconnected fixture at
`ε = 1/8` no witness time exists (`dK2_lazy_no_mixing_QA`), so the
object's defining set is empty and `sInf ∅ = 0` on `ℕ` — the value
*looks* anti-conservative ("mixes instantly"), and this is exactly why
`_spec` carries the witness clause: laziness repairs the periodicity
corner (`k2_lazy_mix_eq_fourth_QA`: the lazy object is the genuine `1`
on `K₂` where the plain object is junk) but not the disconnection
corner. The fence is the proof that the junk corner is fenced, not
inhabited — the lazy twin of `k2_mix_junk_corner_QA`. -/
theorem dK2_lazy_mix_junk_corner_QA :
    lazyWalkMixingTimeFrom dK2Adj 0 (1/8) = 0 := by
  have hempty : {t : ℕ | ∀ s : ℕ, t ≤ s →
      tvDistance (lazyWalkDistribution dK2Adj s 0) (stationaryVec dK2Adj)
        ≤ 1/8} = ∅ := by
    refine Set.eq_empty_iff_forall_not_mem.mpr ?_
    intro t ht
    exact dK2_lazy_no_mixing_QA ⟨t, ht⟩
  rw [lazyWalkMixingTimeFrom, hempty, Nat.sInf_empty]

/-- **The `_spec` witness-clause (`hne`) fence**: with `hne` dropped,
the conclusion fails at the fixture — `t_mix = 0` holds below `s = 0`,
and `TV(ν₀, π) = 3/4 > 1/8`. The dropped clause is exactly what
excludes the junk corner, and it is unfalsifiable-by-fixture on
connected input (where the ceiling supplies it); on disconnected input
no witness exists to be genuine. -/
theorem dK2_lazy_mix_spec_fence_QA :
    ¬ (∀ s : ℕ, lazyWalkMixingTimeFrom dK2Adj 0 (1/8) ≤ s →
        tvDistance (lazyWalkDistribution dK2Adj s 0)
          (stationaryVec dK2Adj) ≤ 1/8) := by
  intro h
  have h0 := h 0 (by rw [dK2_lazy_mix_junk_corner_QA])
  rw [dK2_lazy_tv_zero_QA] at h0
  norm_num at h0

end LazyFollowOnFences

section SpectralCertificate

/-! ### The triangle: the computed certificate pinned exactly -/

/-- Every sorted spectrum entry of the triangle is `0` or `3/2`
(each entry is some basis eigenvalue). -/
theorem tri_evals_cases (k : Fin 3) :
    evals triH k = 0 ∨ evals triH k = 3/2 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf triH k
  rw [hi]
  exact tri_eigvalOf_cases i

/-- The sorted-spectrum sum of the triangle is the trace `3`. -/
theorem tri_evals_sum : ∑ k : Fin 3, evals triH k = 3 := by
  have h := evals_sum_eq_trace triH
  rw [tri_trace] at h
  simpa using h

theorem tri_evals_one_eq :
    evals triH ⟨1, by decide⟩ = 3/2 := by
  rcases tri_evals_cases ⟨1, by decide⟩ with h0 | h32
  · exfalso
    have hsum3 : evals triH ⟨0, by decide⟩
        + evals triH ⟨1, by decide⟩
        + evals triH ⟨2, by decide⟩ = 3 := by
      simpa [Fin.sum_univ_three] using tri_evals_sum
    have hle : evals triH ⟨0, by decide⟩ ≤ evals triH ⟨1, by decide⟩ :=
      evals_sorted triH (Fin.mk_le_mk.mpr (by decide))
    have hc0 : evals triH ⟨0, by decide⟩ = 0 := by
      rcases tri_evals_cases ⟨0, by decide⟩ with h | h'
      · exact h
      · rw [h'] at hle
        rw [h0] at hle
        norm_num at hle
    rcases tri_evals_cases ⟨2, by decide⟩ with h2 | h2'
    · rw [hc0, h0, h2] at hsum3; norm_num at hsum3
    · rw [hc0, h0, h2'] at hsum3; norm_num at hsum3
  · exact h32

theorem tri_evals_last_eq :
    evals triH ⟨2, by decide⟩ = 3/2 := by
  rcases tri_evals_cases ⟨2, by decide⟩ with h0 | h32
  · exfalso
    have hle : evals triH ⟨1, by decide⟩ ≤ evals triH ⟨2, by decide⟩ :=
      evals_sorted triH (Fin.mk_le_mk.mpr (by decide))
    rw [h0] at hle
    rw [tri_evals_one_eq] at hle
    norm_num at hle
  · exact h32

/-- **The triangle's computed certificate is exactly `1/2`** — both
`max` branches attained (`λ₂ = λ_max = 3/2`): load-bearing on both
halves of the certificate, the below-gap branch and the strict-signless
branch. -/
theorem tri_spectral_rate_QA :
    max (1 - secondEval triL triH (by simp))
        (evals triH ⟨2, by decide⟩ - 1) = 1/2 := by
  rw [show secondEval triL triH (by simp)
      = evals triH ⟨1, by decide⟩ from rfl,
    tri_evals_one_eq, tri_evals_last_eq]
  norm_num

theorem tri_adj01 :
    (supportGraph triAdj triAdj_isSymm).Adj (0 : Fin 3) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [triAdj_apply]⟩

theorem tri_adj12 :
    (supportGraph triAdj triAdj_isSymm).Adj (1 : Fin 3) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [triAdj_apply]⟩

theorem tri_adj20 :
    (supportGraph triAdj triAdj_isSymm).Adj (2 : Fin 3) 0 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [triAdj_apply]⟩

/-- The triangle's odd closed walk: around `0 → 1 → 2 → 0`. -/
def triWalk3 :
    (supportGraph triAdj triAdj_isSymm).Walk (0 : Fin 3) (0 : Fin 3) :=
  SimpleGraph.Walk.cons tri_adj01
    (SimpleGraph.Walk.cons tri_adj12
      (SimpleGraph.Walk.cons tri_adj20 SimpleGraph.Walk.nil))

theorem triWalk3_length : triWalk3.length = 3 := by
  decide

theorem triWalk3_odd : Odd triWalk3.length :=
  ⟨1, by rw [triWalk3_length]; norm_num⟩

/-- **The computed-rate theorem instance, `t = 1`**: the new join on
the triangle, consuming none of the old hand-certificates. -/
theorem tri_max_rate_le_QA :
    chiSquareDistance triAdj 1 0
      ≤ (max (1 - secondEval triL triH (by simp))
          (evals triH ⟨2, by decide⟩ - 1)) ^ (2 * 1)
        * ((stationaryVec triAdj 0)⁻¹ - 1) :=
  chiSquareDistance_le_max_rate triAdj triAdj_isSymm triAdj_nonneg
    triAdj_deg_pos (by simp) tri_connected 1 0

/-- **The intrinsic-rate bound attained exactly at `t = 1`**: the bound
side at the computed certificate `1/2` equals the pinned raw truth
`χ²(1, 0) = 1/2` — both the certificate and the bound exact on the
triangle, so the theorem instance above carries no slack. -/
theorem tri_max_rate_attained_QA :
    (max (1 - secondEval triL triH (by simp))
        (evals triH ⟨2, by decide⟩ - 1)) ^ (2 * 1)
      * ((stationaryVec triAdj 0)⁻¹ - 1)
      = chiSquareDistance triAdj 1 0 := by
  rw [tri_spectral_rate_QA, tri_pi_QA, tri_chi2_one_QA]
  norm_num

/-! ### The depth-form join: the computed rate's inflated display -/

/-- The triangle's inflated display rate is exactly `3/4` — the
`(max r 0 + 1)/2` arithmetic of the depth display pinned against the
exact certificate `r = 1/2`. -/
theorem tri_inflated_rate_QA :
    (max (max (1 - secondEval triL triH (by simp))
          (evals triH ⟨2, by decide⟩ - 1)) 0 + 1) / 2 = 3/4 := by
  rw [tri_spectral_rate_QA]
  norm_num

/-- The depth display's log denominator at the triangle is `log (4/3)`. -/
theorem tri_depth_denominator_QA :
    Real.log (1 / ((max (max (1 - secondEval triL triH (by simp))
            (evals triH ⟨2, by decide⟩ - 1)) 0 + 1) / 2))
      = Real.log (4/3) := by
  rw [tri_inflated_rate_QA]
  norm_num

/-- **The computed-rate threshold at `t = 3`, `ε = 1/2`**: the
displayed depth threshold holds on the triangle — `2·√(2/3) ≤ 2 ≤
(4/3)³ = 64/27`, the corpus's `√(2/3) ≤ 1` doing the analytic work and
everything else rational. The computed display costs two layers over
the caller-certificate ceiling's `t = 1` at the same `ε`. -/
theorem tri_depth_threshold_three_QA :
    Real.log (Real.sqrt (2/3) / (1/2))
      / Real.log (1 / ((max (max (1 - secondEval triL triH (by simp))
            (evals triH ⟨2, by decide⟩ - 1)) 0 + 1) / 2))
      ≤ (3 : ℝ) := by
  have hlogpos : 0 < Real.log (4/3) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 4/3)
  have hCpos : 0 < Real.sqrt (2/3) / (1/2) := by positivity
  have hC : Real.sqrt (2/3) / (1/2) ≤ (4/3 : ℝ) ^ (3 : ℕ) := by
    rw [show (4/3 : ℝ) ^ (3 : ℕ) = 64/27 from by norm_num,
      div_le_iff₀ (by norm_num : (0 : ℝ) < 1/2),
      show (64/27 : ℝ) * (1/2) = 32/27 from by norm_num]
    exact le_trans tri_sqrt_le_one_QA (by norm_num : (1 : ℝ) ≤ 32/27)
  have hlogle : Real.log (Real.sqrt (2/3) / (1/2))
      ≤ Real.log ((4/3 : ℝ) ^ (3 : ℕ)) :=
    (Real.log_le_log_iff hCpos
      (pow_pos (by norm_num : (0 : ℝ) < 4/3) 3)).mpr hC
  rw [Real.log_pow (4/3 : ℝ) 3] at hlogle
  rw [tri_depth_denominator_QA, div_le_iff₀ hlogpos]
  linarith

/-- **The depth ceiling at the computed rate, triangle instance**
(`t = 3`, `ε = 1/2`, from `x = 0` to `y = 1`): no caller certificate —
the theorem's own display supplies the inflated rate. -/
theorem tri_ceiling_depth_three_QA :
    |walkDistribution triAdj 3 0 1 - stationaryVec triAdj 1| ≤ 1/2 := by
  refine walkDistribution_sub_stationaryVec_le_of_depth_of_odd_walk
    triAdj triAdj_isSymm triAdj_nonneg triAdj_deg_pos (by simp) tri_connected
    triWalk3 triWalk3_odd (1/2) (by norm_num) 3 0 1 ?_
  rw [tri_oversmoothingConstant_eq_QA 0 1]
  exact tri_depth_threshold_three_QA

/-- The true value at the computed-rate depth instance: deviation
exactly `1/24`, well inside the certified `1/2` — the bound's slack
honest, pinned against the raw three-step law. -/
theorem tri_ceiling_depth_three_value_QA :
    |walkDistribution triAdj 3 0 1 - stationaryVec triAdj 1| = 1/24 := by
  simp only [tri_dist_three_zero_QA, tri_pi_QA]
  norm_num [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons]

/-! ### The C₄ fence: no certificate exists on bipartite input -/

/-- Entry table for the cycle: unit weight on exactly the four edges'
ordered pairs, zero elsewhere (the diagonal and the two antipodal
pairs). -/
theorem c4Adj_apply (i j : Fin 4) :
    c4Adj i j = if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2)
        ∨ (i = 2 ∧ j = 1) ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)
        ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The alternating mode of the cycle is an eigenvector of the
normalized Laplacian at eigenvalue `2` — the bipartite top mode. -/
theorem c4_normLap_mulVec_alternating :
    (normalizedLaplacian c4Adj) *ᵥ (![1, -1, 1, -1] : Fin 4 → ℝ)
      = (2 : ℝ) • ![1, -1, 1, -1] := by
  have hinv : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 1/2 := by
    have hs : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  have hentry : ∀ j k : Fin 4,
      (degreeInvSqrt c4Adj * c4Adj * degreeInvSqrt c4Adj) j k
        = (1/2) * c4Adj j k := by
    intro j k
    fin_cases j <;> fin_cases k <;>
      simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply,
        Fin.sum_univ_four, c4Adj_apply, c4Adj_deg_eq, hinv, mul_one,
        one_mul]
  have hrow : ∀ j : Fin 4,
      ((degreeInvSqrt c4Adj * c4Adj * degreeInvSqrt c4Adj)
        *ᵥ (![1, -1, 1, -1] : Fin 4 → ℝ)) j
        = - (![1, -1, 1, -1] : Fin 4 → ℝ) j := by
    intro j
    simp only [Matrix.mulVec, Matrix.dotProduct, hentry]
    fin_cases j <;> simp [Fin.sum_univ_four, c4Adj_apply] <;> norm_num
  funext j
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.sub_apply, hrow j]
  fin_cases j <;> simp <;> norm_num

theorem c4_no_lt_one_rate_QA :
    ¬ ∃ r : ℝ, r < 1 ∧ ∀ i : Fin 4,
        eigvalOf (normalizedLaplacian c4Adj)
          (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) i ≠ 0 →
        |1 - eigvalOf (normalizedLaplacian c4Adj)
            (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) i| ≤ r := by
  rintro ⟨r, hr1, hrate⟩
  have hvne : (![1, -1, 1, -1] : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul
    (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) hvne
    c4_normLap_mulVec_alternating
  have h := hrate i (by rw [hi]; norm_num)
  rw [hi] at h
  norm_num at h
  linarith

/-- The parity function of the cycle, as an explicit match table. -/
def c4Parity : Fin 4 → ℝ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => -1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => -1

theorem c4Parity_cases (w : Fin 4) :
    c4Parity w = 1 ∨ c4Parity w = -1 := by
  fin_cases w <;> simp [c4Parity]

/-- The parity function flips along every edge of the cycle. -/
theorem c4Parity_flip (i j : Fin 4)
    (hadj : (supportGraph c4Adj c4Adj_isSymm).Adj i j) :
    c4Parity j = -c4Parity i := by
  obtain ⟨-, hpos⟩ := supportGraph_adj.1 hadj
  fin_cases i <;> fin_cases j <;>
    revert hpos <;> simp [c4Adj_apply, c4Parity]

/-- Every closed walk on the cycle is even — the flip-propagation
lemma's isolation mechanism: `u = (−1)^i` flips along every edge, so a
closed walk's length must satisfy `(−1)^{|p|} = 1`. -/
theorem c4_closed_walk_even {w : Fin 4}
    (p : (supportGraph c4Adj c4Adj_isSymm).Walk w w) :
    Even p.length := by
  have hpar := walk_eq_neg_one_pow_length_mul_of_forall_adj c4Parity
    (fun i j => c4Parity_flip i j) p
  have hne : c4Parity w ≠ 0 := by
    intro h
    rcases c4Parity_cases w with h' | h'
    · rw [h'] at h; norm_num at h
    · rw [h'] at h; norm_num at h
  rcases Nat.even_or_odd p.length with h | h
  · exact h
  · rw [h.neg_one_pow] at hpar
    have h0 : c4Parity w = 0 := by linarith [hpar]
    exact absurd h0 hne

/-- **The isolation companion**: the C₄ fixture is genuine on every
axis the certificate theorem names — symmetric, nonnegative, positive
degrees, connected, `2 ≤ card` — with the odd-closed-walk clause
exactly the failure (no odd closed walk exists, fenced above). -/
theorem c4_fence_isolation_QA :
    c4Adj.IsSymm ∧ (∀ i j : Fin 4, 0 ≤ c4Adj i j)
      ∧ (∀ i : Fin 4, 0 < deg c4Adj i)
      ∧ (supportGraph c4Adj c4Adj_isSymm).Connected
      ∧ ¬ ∃ (w : Fin 4) (p : (supportGraph c4Adj c4Adj_isSymm).Walk w w),
          Odd p.length :=
  ⟨c4Adj_isSymm, c4Adj_nonneg, fun i => by rw [c4Adj_deg_eq i]; norm_num,
    c4Adj_connected, by
      rintro ⟨w, p, hp⟩
      obtain ⟨k, hk⟩ := c4_closed_walk_even p
      obtain ⟨m, hm⟩ := hp
      omega⟩

/-! ### The C₄ depth fence: the odd-walk clause is load-bearing -/

/-- The C₄ volume: four degree-`2` vertices, volume `8`. -/
theorem c4_vol_QA : vol c4Adj (Finset.univ : Finset (Fin 4)) = 8 := by
  simp only [vol, c4Adj_deg_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

/-- The C₄ stationary distribution is uniform `1/4`. -/
theorem c4_pi_QA (i : Fin 4) : stationaryVec c4Adj i = 1/4 := by
  simp only [stationaryVec, c4_vol_QA, c4Adj_deg_eq]
  norm_num

/-- The C₄ spectrum's top entry is exactly `2` — the alternating
bipartite mode (forcing `≥ 2` through `eigvalOf_le_evals_last`)
against the signless ceiling `μ ≤ 2`. -/
theorem c4_evals_last_eq_two :
    evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
      ⟨3, by decide⟩ = 2 := by
  have hvne : (![1, -1, 1, -1] : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul
    (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) hvne
    c4_normLap_mulVec_alternating
  have hge : (2 : ℝ) ≤ evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
      ⟨3, by decide⟩ := by
    rw [← hi]
    exact eigvalOf_le_evals_last _ (by decide) i
  have hle : evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
      ⟨3, by decide⟩ ≤ 2 := by
    obtain ⟨j, hj⟩ := evals_mem_eigvalOf
      (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) ⟨3, by decide⟩
    rw [hj]
    exact eigvalOf_normalizedLaplacian_le_two c4Adj c4Adj_isSymm c4Adj_nonneg
      (fun i => by rw [c4Adj_deg_eq i]; norm_num) j
  linarith

/-- **The C₄ display rate saturates at exactly `1`** — both branches
at their bipartite limits (`1 − λ₂ ≤ 1` by PSD, `λ_max − 1 = 1` by the
top entry `2`) — so the depth display's denominator degenerates to
`log 1 = 0`: exactly the corner the odd-walk clause excludes. -/
theorem c4_display_rate_eq_one_QA :
    max (1 - secondEval (normalizedLaplacian c4Adj)
          (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
        (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
          ⟨3, by decide⟩ - 1) = 1 := by
  have hge : (1 : ℝ) ≤ max (1 - secondEval (normalizedLaplacian c4Adj)
          (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
        (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
          ⟨3, by decide⟩ - 1) := by
    refine le_trans ?_ (le_max_right _ _)
    rw [c4_evals_last_eq_two]
    norm_num
  have hle : max (1 - secondEval (normalizedLaplacian c4Adj)
          (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
        (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
          ⟨3, by decide⟩ - 1) ≤ 1 := by
    have h1 : 1 - secondEval (normalizedLaplacian c4Adj)
        (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide) ≤ 1 := by
      have hrw : secondEval (normalizedLaplacian c4Adj)
          (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide)
          = evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
            ⟨1, by decide⟩ := rfl
      obtain ⟨j, hj⟩ := evals_mem_eigvalOf
        (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) ⟨1, by decide⟩
      rw [hrw, hj]
      have hnn := eigvalOf_normalizedLaplacian_nonneg c4Adj c4Adj_isSymm
        c4Adj_nonneg (fun i => by rw [c4Adj_deg_eq i]; norm_num) j
      linarith
    have h2 : evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
        ⟨3, by decide⟩ - 1 ≤ 1 := by
      rw [c4_evals_last_eq_two]
      norm_num
    exact max_le h1 h2
  linarith

/-- The one-step law at C₄ from `0`: `(0, 1/2, 0, 1/2)` — the walk
splits evenly between its two ring neighbors. -/
theorem c4_dist_one_zero_QA :
    walkDistribution c4Adj 1 0 = ![0, 1/2, 0, 1/2] := by
  rw [walkDistribution_succ, walkDistribution_zero]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, c4Adj, Matrix.mulVec,
    Matrix.dotProduct, Fin.sum_univ_four, Pi.single_apply]
  all_goals norm_num

/-- The two-step law at C₄ from `0`: `(1/2, 0, 1/2, 0)` — the
alternating persistence (the bipartite mode the plain walk can never
average away). -/
theorem c4_dist_two_zero_QA :
    walkDistribution c4Adj 2 0 = ![1/2, 0, 1/2, 0] := by
  rw [walkDistribution_succ, c4_dist_one_zero_QA]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, c4Adj_deg_eq, c4Adj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four]
  all_goals norm_num

/-- **The junk threshold**: at C₄ the depth display's threshold
hypothesis is satisfiable at *every* `t` — the saturated rate `1`
makes the denominator `log 1 = 0`, and `x / 0 = 0 ≤ t` in the junk
arithmetic. The odd-walk clause is the only thing standing between
the depth statement and this vacuity. -/
theorem c4_depth_threshold_junk_QA (x y : Fin 4) {ε : ℝ} (t : ℕ) :
    Real.log (Real.sqrt (stationaryVec c4Adj y
          * ((stationaryVec c4Adj x)⁻¹ - 1)) / ε)
      / Real.log (1 / ((max (max (1 - secondEval (normalizedLaplacian c4Adj)
                (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
              (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
                ⟨3, by decide⟩ - 1)) 0 + 1) / 2))
      ≤ (t : ℝ) := by
  have hlog : Real.log (1 / ((max (max (1 - secondEval (normalizedLaplacian c4Adj)
                (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
              (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
                ⟨3, by decide⟩ - 1)) 0 + 1) / 2)) = 0 := by
    have hrw : (max (max (1 - secondEval (normalizedLaplacian c4Adj)
                (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
              (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
                ⟨3, by decide⟩ - 1)) 0 + 1) / 2 = 1 := by
      rw [c4_display_rate_eq_one_QA]
      norm_num
    rw [hrw]
    norm_num
  rw [hlog, div_zero]
  exact mod_cast Nat.zero_le t

/-- **The odd-walk clause is load-bearing in the depth join**: dropped,
the statement is false at C₄ — the threshold hypothesis is
junk-satisfiable (`c4_depth_threshold_junk_QA`) while the conclusion
fails at `(t, x, y, ε) = (2, 0, 0, 1/8)` with `|ν(2) 0 0 − 1/4| =
1/4` — the junk-division hazard class exercised at the new display
itself. Isolation: every other hypothesis is genuine at C₄
(`c4_fence_isolation_QA`); the odd closed walk is exactly what fails. -/
theorem c4_depth_fence_QA :
    ¬ (∀ (t : ℕ) (x y : Fin 4) (ε : ℝ), 0 < ε →
      Real.log (Real.sqrt (stationaryVec c4Adj y
            * ((stationaryVec c4Adj x)⁻¹ - 1)) / ε)
        / Real.log (1 / ((max (max (1 - secondEval (normalizedLaplacian c4Adj)
                  (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
                (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
                  ⟨3, by decide⟩ - 1)) 0 + 1) / 2))
        ≤ (t : ℝ) →
        |walkDistribution c4Adj t x y - stationaryVec c4Adj y| ≤ ε) := by
  intro h
  have hthr := c4_depth_threshold_junk_QA (ε := 1/8) 0 0 2
  have hcon := h 2 0 0 (1/8) (by norm_num) hthr
  rw [c4_dist_two_zero_QA, c4_pi_QA] at hcon
  simp only [Matrix.cons_val_zero] at hcon
  norm_num at hcon
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/4)] at hcon
  norm_num at hcon

/-! ### The looped triangle: the honest `r = 0` corner of the
certificate -/

/-- Adjacency of the looped triangle on `Fin 3`: all entries one —
degree `3` everywhere, support graph the plain triangle (loops are not
support-graph edges). -/
def loopTriAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![1, 1, 1; 1, 1, 1; 1, 1, 1]

theorem loopTriAdj_apply (i j : Fin 3) : loopTriAdj i j = 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem loopTriAdj_isSymm : loopTriAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [loopTriAdj_apply, loopTriAdj_apply]

theorem loopTriAdj_nonneg : ∀ i j, 0 ≤ loopTriAdj i j := by
  intro i j
  rw [loopTriAdj_apply]
  norm_num

local notation "loopTriL" => normalizedLaplacian loopTriAdj
local notation "loopTriH" =>
  normalizedLaplacian_symmetric loopTriAdj loopTriAdj_isSymm

theorem loopTriAdj_deg_eq (i : Fin 3) : deg loopTriAdj i = 3 := by
  rw [deg]
  fin_cases i <;> simp [loopTriAdj_apply, Fin.sum_univ_three]

theorem loopTriAdj_deg_pos : ∀ i, 0 < deg loopTriAdj i := by
  intro i
  rw [loopTriAdj_deg_eq i]
  norm_num

theorem loopTri_vol : vol loopTriAdj (Finset.univ : Finset (Fin 3)) = 9 := by
  simp only [vol, loopTriAdj_deg_eq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  norm_num

theorem loopTri_pi (i : Fin 3) : stationaryVec loopTriAdj i = 1/3 := by
  simp only [stationaryVec, loopTri_vol, loopTriAdj_deg_eq]
  norm_num

theorem loopTri_adj01 :
    (supportGraph loopTriAdj loopTriAdj_isSymm).Adj (0 : Fin 3) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [loopTriAdj_apply]⟩

theorem loopTri_adj12 :
    (supportGraph loopTriAdj loopTriAdj_isSymm).Adj (1 : Fin 3) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [loopTriAdj_apply]⟩

theorem loopTri_adj20 :
    (supportGraph loopTriAdj loopTriAdj_isSymm).Adj (2 : Fin 3) 0 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [loopTriAdj_apply]⟩

theorem loopTri_connected :
    (supportGraph loopTriAdj loopTriAdj_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 3,
      (supportGraph loopTriAdj loopTriAdj_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        loopTri_adj01 SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
        ⟨by decide, by simp [loopTriAdj_apply]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- The looped triangle's odd closed walk: around `0 → 1 → 2 → 0`
(the diagonal loops are invisible to the support graph). -/
def loopTriWalk3 :
    (supportGraph loopTriAdj loopTriAdj_isSymm).Walk (0 : Fin 3) (0 : Fin 3) :=
  SimpleGraph.Walk.cons loopTri_adj01
    (SimpleGraph.Walk.cons loopTri_adj12
      (SimpleGraph.Walk.cons loopTri_adj20 SimpleGraph.Walk.nil))

theorem loopTriWalk3_odd : Odd loopTriWalk3.length :=
  ⟨1, by decide⟩

theorem loopTri_conj_entry (j k : Fin 3) :
    (degreeInvSqrt loopTriAdj * loopTriAdj * degreeInvSqrt loopTriAdj) j k
      = (1/3) * loopTriAdj j k := by
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num)
  have hinv : (Real.sqrt 3)⁻¹ * (Real.sqrt 3)⁻¹ = 1/3 := by
    have hs : Real.sqrt 3 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    field_simp
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.mul_apply, degreeInvSqrt, Matrix.diagonal_apply,
      Fin.sum_univ_three, loopTriAdj_apply, loopTriAdj_deg_eq, hinv,
      mul_one, one_mul]

theorem loopTri_conj_mulVec_apply (w : Fin 3 → ℝ) (j : Fin 3) :
    (((degreeInvSqrt loopTriAdj * loopTriAdj * degreeInvSqrt loopTriAdj)
        *ᵥ w) j)
      = (1/3) * (∑ k, w k) := by
  simp only [Matrix.mulVec, Matrix.dotProduct]
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      (1/3) * loopTriAdj j k * w k = (1/3) * w k := by
    intro k _
    rw [loopTriAdj_apply, mul_one]
  rw [Finset.sum_congr rfl fun k _ => by rw [loopTri_conj_entry j k],
    Finset.sum_congr rfl hterm, ← Finset.mul_sum]

theorem loopTri_normLap_mulVec_apply (w : Fin 3 → ℝ) (j : Fin 3) :
    ((normalizedLaplacian loopTriAdj *ᵥ w) j)
      = w j - (1/3) * (∑ k, w k) := by
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.sub_apply]
  congr 1
  exact loopTri_conj_mulVec_apply w j

theorem loopTri_eigen_entry (i j : Fin 3) :
    eigvalOf loopTriL loopTriH i * (eigvecOf loopTriL loopTriH i j)
      = (eigvecOf loopTriL loopTriH i j)
        - (1/3) * (∑ k, (eigvecOf loopTriL loopTriH i k)) := by
  have h := congrFun
    ((isHermitian_of_isSymm loopTriH).mulVec_eigenvectorBasis i) j
  rw [loopTri_normLap_mulVec_apply _ j, Pi.smul_apply, smul_eq_mul] at h
  exact h.symm

/-- **Every looped-triangle eigenvalue is `0` or `1`** — the
eigen-equation route with all unit row sums: summing over coordinates
gives `μ · (∑ v) = 0`, the quadratic form at a unit eigenvector gives
`μ = 1 − (1/3)(∑ v)²`, and `∑ v = 0` forces `μ = 1`. -/
theorem loopTri_eigvalOf_cases (i : Fin 3) :
    eigvalOf loopTriL loopTriH i = 0 ∨ eigvalOf loopTriL loopTriH i = 1 := by
  have hentry := loopTri_eigen_entry i
  have hquad := quadForm_eigvecOf_self loopTriH i
  set v : Fin 3 → ℝ := eigvecOf loopTriL loopTriH i with hv
  set μ : ℝ := eigvalOf loopTriL loopTriH i with hμdef
  have hunit : ∑ k, v k * v k = 1 := by
    rw [hv]
    simpa using eigvecOf_inner loopTriL loopTriH i i
  have hzero : μ * (∑ j, v j) = 0 := by
    have h1 : ∑ j, μ * v j
        = ∑ j, (v j - (1/3) * (∑ k, v k)) :=
      Finset.sum_congr rfl fun j _ => hentry j
    have hsumrow : ∑ j : Fin 3, (1/3) * (∑ k, v k) = (∑ k, v k) := by
      have hcard : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
      rw [Finset.sum_const, hcard]
      ring_nf
    rw [Finset.sum_sub_distrib, hsumrow, sub_self, ← Finset.mul_sum] at h1
    exact h1
  have hqf : μ = 1 - (1/3) * ((∑ j, v j) * (∑ j, v j)) := by
    have hdot : (v ⬝ᵥ (loopTriL *ᵥ v))
        = (∑ j, v j ^ 2) - (1/3) * ((∑ j, v j) * (∑ j, v j)) := by
      have hsplit : ∀ j : Fin 3,
          v j * (v j - (1/3) * (∑ k, v k))
            = v j * v j - (1/3) * (v j * (∑ k, v k)) := fun j => by ring
      have hterm2 : ∀ j : Fin 3,
          (1/3) * (v j * (∑ k, v k)) = v j * ((1/3) * (∑ k, v k)) :=
        fun j => by ring
      have hpull : ∑ j : Fin 3, v j * ((1/3) * (∑ k, v k))
          = (∑ j : Fin 3, v j) * ((1/3) * (∑ k, v k)) :=
        (Finset.sum_mul _ _ _).symm
      simp only [Matrix.dotProduct, loopTri_normLap_mulVec_apply v]
      rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_sub_distrib,
        Finset.sum_congr rfl fun j _ => hterm2 j, hpull,
        Finset.sum_congr rfl fun j _ => (sq (v j))]
      have hsame : (∑ x : Fin 3, v x ^ 2) = (∑ j : Fin 3, v j * v j) :=
        Finset.sum_congr rfl fun j _ => (sq (v j))
      linarith [hsame]
    calc μ = quadForm loopTriL v := hquad.symm
      _ = (v ⬝ᵥ (loopTriL *ᵥ v)) := rfl
      _ = (∑ j, v j ^ 2) - (1/3) * ((∑ j, v j) * (∑ j, v j)) := hdot
      _ = 1 - (1/3) * ((∑ j, v j) * (∑ j, v j)) := by
        rw [show (∑ j : Fin 3, v j ^ 2) = ∑ k, v k * v k from
          Finset.sum_congr rfl fun j _ => (sq (v j)), hunit]
  rcases mul_eq_zero.mp hzero with h0 | hs0
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [hqf]
    have hsum0 : (∑ j, v j) = 0 := by
      exact hs0
    rw [hsum0]
    norm_num

theorem loopTri_trace : (normalizedLaplacian loopTriAdj).trace = 2 := by
  have hdiag : ∀ j : Fin 3,
      (degreeInvSqrt loopTriAdj * loopTriAdj * degreeInvSqrt loopTriAdj) j j
        = 1/3 := by
    intro j
    rw [loopTri_conj_entry j j, loopTriAdj_apply]
    norm_num
  simp only [Matrix.trace, Matrix.diag_apply, normalizedLaplacian,
    Matrix.sub_apply, Matrix.one_apply, if_true, hdiag]
  norm_num

theorem loopTri_evals_sum : ∑ k : Fin 3, evals loopTriH k = 2 := by
  have h := evals_sum_eq_trace loopTriH
  rw [loopTri_trace] at h
  simpa using h

theorem loopTri_evals_cases (k : Fin 3) :
    evals loopTriH k = 0 ∨ evals loopTriH k = 1 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf loopTriH k
  rw [hi]
  exact loopTri_eigvalOf_cases i

theorem loopTri_evals_one_eq : evals loopTriH ⟨1, by decide⟩ = 1 := by
  rcases loopTri_evals_cases ⟨1, by decide⟩ with h0 | h1
  · exfalso
    have hsum3 : evals loopTriH ⟨0, by decide⟩
        + evals loopTriH ⟨1, by decide⟩
        + evals loopTriH ⟨2, by decide⟩ = 2 := by
      simpa [Fin.sum_univ_three] using loopTri_evals_sum
    have hle : evals loopTriH ⟨0, by decide⟩
        ≤ evals loopTriH ⟨1, by decide⟩ :=
      evals_sorted loopTriH (Fin.mk_le_mk.mpr (by decide))
    have hc0 : evals loopTriH ⟨0, by decide⟩ = 0 := by
      rcases loopTri_evals_cases ⟨0, by decide⟩ with h | h'
      · exact h
      · rw [h'] at hle
        rw [h0] at hle
        norm_num at hle
    rcases loopTri_evals_cases ⟨2, by decide⟩ with h2 | h2'
    · rw [hc0, h0, h2] at hsum3; norm_num at hsum3
    · rw [hc0, h0, h2'] at hsum3; norm_num at hsum3
  · exact h1

theorem loopTri_evals_last_eq : evals loopTriH ⟨2, by decide⟩ = 1 := by
  rcases loopTri_evals_cases ⟨2, by decide⟩ with h0 | h1
  · exfalso
    have hle : evals loopTriH ⟨1, by decide⟩
        ≤ evals loopTriH ⟨2, by decide⟩ :=
      evals_sorted loopTriH (Fin.mk_le_mk.mpr (by decide))
    rw [h0] at hle
    rw [loopTri_evals_one_eq] at hle
    norm_num at hle
  · exact h1

/-- **The looped triangle's computed certificate is exactly `0`** —
the honest degenerate corner: the spectrum is `{0, 1, 1}`, both max
branches evaluate to zero, and the walk mixes *exactly* in one step. -/
theorem loopTri_spectral_rate_QA :
    max (1 - secondEval loopTriL loopTriH (by simp))
        (evals loopTriH ⟨2, by decide⟩ - 1) = 0 := by
  rw [show secondEval loopTriL loopTriH (by simp)
      = evals loopTriH ⟨1, by decide⟩ from rfl,
    loopTri_evals_one_eq, loopTri_evals_last_eq]
  norm_num

/-- **The one-step law is exactly stationary**: the all-positive walk
matrix `D⁻¹A = (1/3) · J` averages every start to the uniform
distribution in a single step. -/
theorem loopTri_walkDistribution_one (x : Fin 3) :
    walkDistribution loopTriAdj 1 x = stationaryVec loopTriAdj := by
  funext j
  rw [walkDistribution_succ]
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    walkTransitionMatrix_apply, loopTriAdj_apply]
  have hterm : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      ((deg loopTriAdj k)⁻¹ * (1 : ℝ))
          * walkDistribution loopTriAdj 0 x k
        = (1/3) * walkDistribution loopTriAdj 0 x k := by
    intro k _
    rw [loopTriAdj_deg_eq k]
    norm_num
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    sum_walkDistribution loopTriAdj loopTriAdj_deg_pos 0 x, mul_one,
    loopTri_pi]

/-- **The certificate's `r = 0` corner mixes exactly**: `χ²(1, x) = 0`
for every start — the computed-rate bound is attained with equality
at the degenerate certificate. -/
theorem loopTri_chiSquare_one_eq_zero (x : Fin 3) :
    chiSquareDistance loopTriAdj 1 x = 0 := by
  rw [chiSquareDistance_eq_sum_smul loopTriAdj loopTriAdj_deg_pos 1 x]
  have hdensity : ∀ i : Fin 3, walkDensity loopTriAdj 1 x i = 1 := by
    intro i
    rw [walkDensity, congrFun (loopTri_walkDistribution_one x) i,
      loopTri_pi]
    norm_num
  simp [hdensity]

theorem loopTri_max_rate_attained_QA (x : Fin 3) :
    (max (1 - secondEval loopTriL loopTriH (by simp))
        (evals loopTriH ⟨2, by decide⟩ - 1)) ^ (2 * 1)
      * ((stationaryVec loopTriAdj x)⁻¹ - 1)
      = chiSquareDistance loopTriAdj 1 x := by
  rw [loopTri_spectral_rate_QA, loopTri_chiSquare_one_eq_zero]
  norm_num

/-- The display-inflated positive certificate exists (and must inflate:
the computed rate here is exactly `0`, which no log threshold can
divide by). -/
theorem loopTri_pos_rate_QA :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ i : Fin 3, eigvalOf loopTriL loopTriH i ≠ 0 →
      |1 - eigvalOf loopTriL loopTriH i| ≤ r :=
  exists_pos_lt_one_rate_of_odd_walk loopTriAdj loopTriAdj_isSymm
    loopTriAdj_nonneg loopTriAdj_deg_pos (by simp) loopTri_connected
    loopTriWalk3 loopTriWalk3_odd

/-! ### The looped triangle: the `r = 0` corner at depth form -/

/-- The looped triangle's oversmoothing constant is the uniform
`√(2/3)` — same stationary vector as the plain triangle. -/
theorem loopTri_oversmoothingConstant_eq (x y : Fin 3) :
    Real.sqrt (stationaryVec loopTriAdj y
        * ((stationaryVec loopTriAdj x)⁻¹ - 1))
      = Real.sqrt (2/3) := by
  rw [loopTri_pi y, loopTri_pi x]
  congr 1
  norm_num

/-- The looped triangle's inflated display rate is exactly `1/2` — the
`r = 0` corner the `(0,1)` inflation exists for: no log threshold can
divide by `log 1`, and the display supplies a genuine `log 2`. -/
theorem loopTri_inflated_rate_QA :
    (max (max (1 - secondEval loopTriL loopTriH (by simp))
          (evals loopTriH ⟨2, by decide⟩ - 1)) 0 + 1) / 2 = 1/2 := by
  rw [loopTri_spectral_rate_QA]
  norm_num

/-- **The depth ceiling at the computed rate, `r = 0`-corner
instance** (`t = 1`, `ε = 1/2`, every start and target): the
threshold's denominator is `log 2` (the inflated display's whole
point at this fixture) and the conclusion holds by exact one-step
mixing. -/
theorem loopTri_ceiling_depth_one_QA (x y : Fin 3) :
    |walkDistribution loopTriAdj 1 x y - stationaryVec loopTriAdj y|
      ≤ 1/2 := by
  refine walkDistribution_sub_stationaryVec_le_of_depth_of_odd_walk
    loopTriAdj loopTriAdj_isSymm loopTriAdj_nonneg loopTriAdj_deg_pos (by simp)
    loopTri_connected loopTriWalk3 loopTriWalk3_odd (1/2) (by norm_num) 1 x y ?_
  have hidx : (⟨Fintype.card (Fin 3) - 1, by decide⟩ : Fin 3)
      = ⟨2, by decide⟩ := by rfl
  rw [loopTri_oversmoothingConstant_eq x y, hidx, loopTri_spectral_rate_QA,
    show ((max ((0:ℝ)) 0 + 1) / 2) = 1/2 from by norm_num,
    show ((1:ℝ) / (1/2)) = 2 from by norm_num]
  exact_mod_cast tri_ceiling_threshold_one_QA

/-- The true value at the `r = 0`-corner depth instance: deviation
exactly `0` — the law is stationary after one step, so the ceiling is
attained with equality at every start. -/
theorem loopTri_ceiling_depth_one_value_QA (x y : Fin 3) :
    |walkDistribution loopTriAdj 1 x y - stationaryVec loopTriAdj y| = 0 := by
  rw [loopTri_walkDistribution_one x]
  simp

/-! ### The strict engine's `hnn` fence: a negative-diagonal triangle -/

/-- The fence fixture: symmetric, degrees `(1, 2, 2)` — positive — with
nonnegativity violated only at the `(0, 0)` diagonal entry. The support
graph is the honest triangle (off-diagonal entries all `1`). -/
def negDiagTriAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![-1, 1, 1; 1, 0, 1; 1, 1, 0]

theorem negDiagTriAdj_apply (i j : Fin 3) :
    negDiagTriAdj i j = if i = j then (if i = 0 then -1 else 0) else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem negDiagTriAdj_isSymm : negDiagTriAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [negDiagTriAdj_apply, negDiagTriAdj_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem negDiagTriAdj_deg_eq (i : Fin 3) :
    deg negDiagTriAdj i = if i = 0 then 1 else 2 := by
  rw [deg]
  fin_cases i <;> simp [negDiagTriAdj_apply, Fin.sum_univ_three] <;> norm_num

theorem negDiagTriAdj_deg_pos : ∀ i, 0 < deg negDiagTriAdj i := by
  intro i
  rw [negDiagTriAdj_deg_eq i]
  fin_cases i <;> simp

theorem negDiagTri_adj01 :
    (supportGraph negDiagTriAdj negDiagTriAdj_isSymm).Adj (0 : Fin 3) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [negDiagTriAdj_apply]⟩

theorem negDiagTri_adj12 :
    (supportGraph negDiagTriAdj negDiagTriAdj_isSymm).Adj (1 : Fin 3) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [negDiagTriAdj_apply]⟩

theorem negDiagTri_adj20 :
    (supportGraph negDiagTriAdj negDiagTriAdj_isSymm).Adj (2 : Fin 3) 0 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [negDiagTriAdj_apply]⟩

theorem negDiagTri_connected :
    (supportGraph negDiagTriAdj negDiagTriAdj_isSymm).Connected := by
  have hfrom0 : ∀ v : Fin 3,
      (supportGraph negDiagTriAdj negDiagTriAdj_isSymm).Reachable 0 v := by
    intro v
    fin_cases v
    · exact ⟨SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
        negDiagTri_adj01 SimpleGraph.Walk.nil⟩
    · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 2) (w := 2)
        ⟨by decide, by simp [negDiagTriAdj_apply]⟩ SimpleGraph.Walk.nil⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨0, hfrom0⟩

/-- The fixture's odd closed walk: around `0 → 1 → 2 → 0` in the
support triangle (the negative diagonal is invisible to it). -/
def negDiagTriWalk3 :
    (supportGraph negDiagTriAdj negDiagTriAdj_isSymm).Walk
      (0 : Fin 3) (0 : Fin 3) :=
  SimpleGraph.Walk.cons negDiagTri_adj01
    (SimpleGraph.Walk.cons negDiagTri_adj12
      (SimpleGraph.Walk.cons negDiagTri_adj20 SimpleGraph.Walk.nil))

theorem negDiagTriWalk3_odd : Odd negDiagTriWalk3.length := ⟨1, by decide⟩

/-- The signless form goes negative at the test vector `(3, −1, −1)`:
the `(0, 0)` entry of `D + A` is `0`, so the diagonal loses `9` against
the plain triangle's contribution. -/
theorem negDiagTri_signless_quadForm_neg :
    quadForm (degreeMatrix negDiagTriAdj + negDiagTriAdj)
        (![3, -1, -1] : Fin 3 → ℝ) = -6 := by
  rw [quadForm_add_eq, quadForm_degreeMatrix_eq, quadForm_eq_sum]
  simp [negDiagTriAdj_deg_eq, negDiagTriAdj_apply, Fin.sum_univ_three]
  norm_num

/-- **The congruence form**: the same negative value as the quadratic
form of `2·1 − L_sym` at the stretched test vector `√D *ᵥ (3, −1, −1)`. -/
theorem negDiagTri_two_sub_quadForm_neg :
    quadForm ((2 : ℝ) • 1 - normalizedLaplacian negDiagTriAdj)
        (degreeSqrt negDiagTriAdj *ᵥ (![3, -1, -1] : Fin 3 → ℝ)) = -6 := by
  rw [quadForm_two_sub_normalizedLaplacian_eq negDiagTriAdj
    negDiagTriAdj_deg_pos _]
  have hst : degreeInvSqrt negDiagTriAdj *ᵥ
      (degreeSqrt negDiagTriAdj *ᵥ (![3, -1, -1] : Fin 3 → ℝ))
      = (![3, -1, -1] : Fin 3 → ℝ) := by
    rw [Matrix.mulVec_mulVec,
      degreeInvSqrt_mul_degreeSqrt negDiagTriAdj negDiagTriAdj_deg_pos,
      Matrix.one_mulVec]
  rw [hst]
  exact negDiagTri_signless_quadForm_neg

local notation "ndT" => normalizedLaplacian negDiagTriAdj
local notation "ndTH" =>
  normalizedLaplacian_symmetric negDiagTriAdj negDiagTriAdj_isSymm

/-- **The eigenvalue escape**: some normalized-Laplacian eigenvalue of
the fixture is strictly above `2` — the smallest sorted eigenvalue of
`2·1 − L_sym` is negative (the negative quadratic form at a nonzero
vector, through `evals_first_mul_dotProduct_le_quadForm`), and the
eigenvector equation shifts it across `2`. -/
theorem negDiagTri_exists_gt_two :
    ∃ i : Fin 3, 2 < eigvalOf ndT ndTH i := by
  have h1s : ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).IsSymm := by
    show ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))ᵀ
      = ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ))
    simp [Matrix.transpose_smul]
  have hM : ((2 : ℝ) • 1 - ndT).IsSymm :=
    Matrix.IsSymm.sub h1s ndTH
  set x : Fin 3 → ℝ :=
    degreeSqrt negDiagTriAdj *ᵥ (![3, -1, -1] : Fin 3 → ℝ) with hxdef
  have hdot : Matrix.dotProduct x x = 13 := by
    have h := dotProduct_degreeSqrt_mulVec negDiagTriAdj
      (fun i => le_of_lt (negDiagTriAdj_deg_pos i)) ![3, -1, -1]
    rw [hxdef]
    have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
      Real.mul_self_sqrt (by norm_num)
    simp [negDiagTriAdj_deg_eq, Fin.sum_univ_three, degreeSqrt,
      Matrix.mulVec_diagonal, hsq2]
    norm_num
  have hq := evals_first_mul_dotProduct_le_quadForm hM (by decide) x
  rw [negDiagTri_two_sub_quadForm_neg] at hq
  have hfirst : evals hM ⟨0, by decide⟩ < 0 := by
    have hq' : evals hM ⟨0, by decide⟩ * Matrix.dotProduct x x ≤ -6 := hq
    rw [hdot] at hq'
    have h13 : (0 : ℝ) < 13 := by norm_num
    nlinarith
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf hM ⟨0, by decide⟩
  have hμlt : eigvalOf ((2 : ℝ) • 1 - ndT) hM i < 0 := by
    rw [← hi]; exact hfirst
  set μ : ℝ := eigvalOf ((2 : ℝ) • 1 - ndT) hM i with hμ
  set v : Fin 3 → ℝ := eigvecOf ((2 : ℝ) • 1 - ndT) hM i with hv
  have hev : ((2 : ℝ) • 1 - ndT) *ᵥ v = μ • v :=
    (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
  have hLv : ndT *ᵥ v = (2 - μ) • v := by
    have hev' : ((2 : ℝ) • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ v
        - ndT *ᵥ v = μ • v := by
      rw [← Matrix.sub_mulVec]; exact hev
    rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec] at hev'
    funext j
    have hj := congrFun hev' j
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    linarith
  have hvne : v ≠ 0 := by
    intro h0
    have hun : Matrix.dotProduct v v = 1 := by
      rw [hv]
      simpa [Matrix.dotProduct] using
        eigvecOf_inner ((2 : ℝ) • 1 - ndT) hM i i
    rw [h0] at hun
    norm_num at hun
  obtain ⟨j, hj⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul ndTH hvne hLv
  refine ⟨j, ?_⟩
  rw [hj]
  linarith

/-- **The `hnn` fence for the strict signless engine**: at the
negative-diagonal fixture (symmetric, positive degrees, connected
support triangle, genuine odd closed walk — every hypothesis except
entrywise nonnegativity), the dropped conclusion fails in proved form:
an eigenvalue escapes above `2`. -/
theorem negDiagTri_hnn_fence_QA :
    ¬ (∀ i : Fin 3, eigvalOf ndT ndTH i < 2) := by
  obtain ⟨i, hi⟩ := negDiagTri_exists_gt_two
  intro h
  have := h i
  linarith

/-- **The isolation companion**: the fixture is genuine on every axis
the strict engine names — symmetric, positive degrees, connected
support graph, a genuine odd closed walk — with entrywise nonnegativity
exactly the failure (the `(0, 0)` entry is `−1`). -/
theorem negDiagTri_fence_isolation_QA :
    negDiagTriAdj.IsSymm ∧ (∀ i : Fin 3, 0 < deg negDiagTriAdj i)
      ∧ (supportGraph negDiagTriAdj negDiagTriAdj_isSymm).Connected
      ∧ Odd negDiagTriWalk3.length ∧ ¬ (∀ i j, 0 ≤ negDiagTriAdj i j) :=
  ⟨negDiagTriAdj_isSymm, negDiagTriAdj_deg_pos, negDiagTri_connected,
    negDiagTriWalk3_odd, by
      intro hnn
      have := hnn 0 0
      rw [negDiagTriAdj_apply] at this
      norm_num at this⟩


/-! ### The strict engine's `hconn` fence: triangle ⊕ K₂ on `Fin 5` -/

/-- The fence fixture: a triangle block on `{0, 1, 2}` and an edge on
`{3, 4}`, no cross-block entries — symmetric, nonnegative, degrees
`(2, 2, 2, 1, 1)` all positive, a genuine odd closed walk in the
triangle block, and disconnected. -/
def triK2Adj : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of !![0, 1, 1, 0, 0; 1, 0, 1, 0, 0; 1, 1, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]

theorem triK2Adj_apply (i j : Fin 5) :
    triK2Adj i j = if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 0 ∧ j = 2)
        ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)
        ∨ (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem triK2Adj_isSymm : triK2Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [triK2Adj_apply, triK2Adj_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem triK2Adj_nonneg : ∀ i j, 0 ≤ triK2Adj i j := by
  intro i j
  rw [triK2Adj_apply]
  split <;> norm_num

local notation "tkH" =>
  normalizedLaplacian_symmetric triK2Adj triK2Adj_isSymm

theorem triK2Adj_deg_eq (i : Fin 5) :
    deg triK2Adj i = if i = 3 ∨ i = 4 then 1 else 2 := by
  rw [deg]
  fin_cases i <;> simp [triK2Adj, Fin.sum_univ_five] <;> norm_num

theorem triK2Adj_deg_pos : ∀ i, 0 < deg triK2Adj i := by
  intro i
  rw [triK2Adj_deg_eq i]
  fin_cases i <;> simp

theorem triK2_adj01 :
    (supportGraph triK2Adj triK2Adj_isSymm).Adj (0 : Fin 5) 1 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [triK2Adj_apply]⟩

theorem triK2_adj12 :
    (supportGraph triK2Adj triK2Adj_isSymm).Adj (1 : Fin 5) 2 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [triK2Adj_apply]⟩

theorem triK2_adj20 :
    (supportGraph triK2Adj triK2Adj_isSymm).Adj (2 : Fin 5) 0 := by
  rw [supportGraph_adj]
  exact ⟨by decide, by simp [triK2Adj_apply]⟩

/-- The fixture's odd closed walk: around the triangle block
`0 → 1 → 2 → 0`. -/
def triK2Walk3 :
    (supportGraph triK2Adj triK2Adj_isSymm).Walk (0 : Fin 5) (0 : Fin 5) :=
  SimpleGraph.Walk.cons triK2_adj01
    (SimpleGraph.Walk.cons triK2_adj12
      (SimpleGraph.Walk.cons triK2_adj20 SimpleGraph.Walk.nil))

theorem triK2Walk3_odd : Odd triK2Walk3.length := ⟨1, by decide⟩

theorem triK2_off_zero (i j : Fin 5) (hi : (i : ℕ) < 3) (hj : 3 ≤ (j : ℕ)) :
    triK2Adj i j = 0 := by
  rw [triK2Adj_apply]
  revert hi hj
  fin_cases i <;> fin_cases j <;> simp_all

/-- Walks cannot leave the triangle block. -/
theorem triK2_walk_stays {a b : Fin 5}
    (w : (supportGraph triK2Adj triK2Adj_isSymm).Walk a b)
    (hi : (a : ℕ) < 3) : (b : ℕ) < 3 := by
  induction w with
  | nil => exact hi
  | @cons u k v hadj rest ih =>
    have hk : (k : ℕ) < 3 := by
      obtain ⟨-, hpos⟩ := supportGraph_adj.1 hadj
      by_contra hcon
      have hk2 : 3 ≤ (k : ℕ) := by omega
      have h0 := triK2_off_zero u k hi hk2
      rw [h0] at hpos
      norm_num at hpos
    exact ih hk

theorem triK2_not_connected :
    ¬ (supportGraph triK2Adj triK2Adj_isSymm).Connected := by
  intro hconn
  obtain ⟨w⟩ := hconn.1 (0 : Fin 5) 3
  have := triK2_walk_stays w (by decide)
  exact absurd this (by decide)

/-- **The K₂ block's top mode survives the odd walk**: the
block-supported alternating vector is an eigenvector at eigenvalue `2`. -/
theorem triK2_normLap_mulVec_alternating :
    (normalizedLaplacian triK2Adj) *ᵥ (![0, 0, 0, 1, -1] : Fin 5 → ℝ)
      = (2 : ℝ) • ![0, 0, 0, 1, -1] := by
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hsq1 : Real.sqrt 1 * Real.sqrt 1 = 1 :=
    Real.mul_self_sqrt (by norm_num)
  have hrow : ∀ j : Fin 5,
      ((degreeInvSqrt triK2Adj * triK2Adj * degreeInvSqrt triK2Adj)
        *ᵥ (![0, 0, 0, 1, -1] : Fin 5 → ℝ)) j
        = if j = 3 then -1 else if j = 4 then 1 else 0 := by
    intro j
    fin_cases j
    all_goals
      simp [Matrix.mulVec, Matrix.dotProduct, Matrix.mul_apply,
        degreeInvSqrt, Matrix.diagonal_apply, Fin.sum_univ_five,
        triK2Adj_apply, triK2Adj_deg_eq, hsq2, hsq1]
  funext j
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    Pi.sub_apply, hrow j]
  fin_cases j <;> simp <;> norm_num

/-- **The `hconn` fence for the strict signless engine**: at the
triangle⊕edge fixture (symmetric, nonnegative, positive degrees, a
genuine odd closed walk in the triangle block — every hypothesis except
connectivity), the dropped conclusion fails in proved form: the `K₂`
block's `μ = 2` mode survives. -/
theorem triK2_hconn_fence_QA :
    ¬ (∀ i : Fin 5, eigvalOf (normalizedLaplacian triK2Adj) tkH i < 2) := by
  have hvne : (![0, 0, 0, 1, -1] : Fin 5 → ℝ) ≠ 0 := by
    intro h
    have := congrFun h 3
    simp at this
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul tkH hvne
    triK2_normLap_mulVec_alternating
  intro hall
  have := hall i
  rw [hi] at this
  norm_num at this

/-- **The isolation companion**: the fixture is genuine on every axis
the strict engine names — symmetric, nonnegative, positive degrees, a
genuine odd closed walk — with connectivity exactly the failure. -/
theorem triK2_fence_isolation_QA :
    triK2Adj.IsSymm ∧ (∀ i j : Fin 5, 0 ≤ triK2Adj i j)
      ∧ (∀ i : Fin 5, 0 < deg triK2Adj i) ∧ Odd triK2Walk3.length
      ∧ ¬ (supportGraph triK2Adj triK2Adj_isSymm).Connected :=
  ⟨triK2Adj_isSymm, triK2Adj_nonneg, triK2Adj_deg_pos, triK2Walk3_odd,
    triK2_not_connected⟩

/-! ### The two-start twin at the computed rate

The depth-form join's recorded two-start composition (the execution
plan's priced remainder), landed with the consumer the shelf's own
caller-certificate twin names: the "representations become
indistinguishable" statement. -/

/-- The two-step law at C₄ from `1`: `(0, 1/2, 0, 1/2)` — the
opposite-parity mirror of `c4_dist_two_zero_QA`, the two-start fence's
second law pin. -/
theorem c4_dist_two_one_QA :
    walkDistribution c4Adj 2 1 = ![0, 1/2, 0, 1/2] := by
  rw [walkDistribution_succ, c4_dist_one_one]
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix_apply, c4Adj_deg_eq, c4Adj_apply,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_four]
  all_goals norm_num

/-- **The two-start depth ceiling at the computed rate, triangle
instance** (`t = 3`, `ε = 1/2`, starts `0` and `1`, target `0`): no
caller certificate — both starts' thresholds come from the same
computed display (the uniform stationary vector makes them literally
the same threshold here; the statement's two threshold slots are
nevertheless distinct in general). -/
theorem tri_two_start_depth_QA :
    |walkDistribution triAdj 3 0 0 - walkDistribution triAdj 3 1 0|
      ≤ 2 * (1/2) := by
  refine walkDistribution_sub_walkDistribution_le_of_depth_of_odd_walk
    triAdj triAdj_isSymm triAdj_nonneg triAdj_deg_pos (by simp) tri_connected
    triWalk3 triWalk3_odd (1/2) (by norm_num) 3 0 1 0 ?_ ?_
  · rw [tri_oversmoothingConstant_eq_QA 0 0]
    exact tri_depth_threshold_three_QA
  · rw [tri_oversmoothingConstant_eq_QA 1 0]
    exact tri_depth_threshold_three_QA

/-- The true value at the two-start depth instance: the three-step
views from `0` and `1` differ by exactly `1/8` at vertex `0` — well
inside the certified `2ε = 1`, with the one-start deviations `1/12`
and `1/24` in opposite directions summing to it. -/
theorem tri_two_start_depth_value_QA :
    |walkDistribution triAdj 3 0 0 - walkDistribution triAdj 3 1 0|
      = 1/8 := by
  rw [tri_dist_three_zero_QA, tri_dist_three_one_QA]
  simp only [Matrix.cons_val_zero]
  norm_num

/-- **The two-start depth ceiling at the computed rate, `r = 0`-corner
instance** (looped triangle, `t = 1`, `ε = 1/2`, every pair of starts):
both thresholds from the inflated `log 2` display. -/
theorem loopTri_two_start_depth_QA (x₁ x₂ y : Fin 3) :
    |walkDistribution loopTriAdj 1 x₁ y - walkDistribution loopTriAdj 1 x₂ y|
      ≤ 2 * (1/2) := by
  refine walkDistribution_sub_walkDistribution_le_of_depth_of_odd_walk
    loopTriAdj loopTriAdj_isSymm loopTriAdj_nonneg loopTriAdj_deg_pos (by simp)
    loopTri_connected loopTriWalk3 loopTriWalk3_odd (1/2) (by norm_num) 1 x₁ x₂ y
    ?_ ?_
  all_goals
    have hidx : (⟨Fintype.card (Fin 3) - 1, by decide⟩ : Fin 3)
        = ⟨2, by decide⟩ := by rfl
    rw [loopTri_oversmoothingConstant_eq _ y, hidx, loopTri_spectral_rate_QA,
      show ((max ((0:ℝ)) 0 + 1) / 2) = 1/2 from by norm_num,
      show ((1:ℝ) / (1/2)) = 2 from by norm_num]
    exact_mod_cast tri_ceiling_threshold_one_QA

/-- The true value at the `r = 0`-corner two-start instance: exactly
`0` — both one-step laws are already stationary, so the starts are
indistinguishable from step one. -/
theorem loopTri_two_start_depth_value_QA (x₁ x₂ y : Fin 3) :
    |walkDistribution loopTriAdj 1 x₁ y - walkDistribution loopTriAdj 1 x₂ y|
      = 0 := by
  rw [loopTri_walkDistribution_one x₁, loopTri_walkDistribution_one x₂]
  simp

/-- **The odd-walk clause is load-bearing in the two-start twin**:
dropped, the statement is false at C₄ — both threshold hypotheses are
junk-satisfiable at every time (`c4_depth_threshold_junk_QA`) while
the conclusion fails for the opposite-parity pair `(x₁, x₂) = (0, 1)`
at `(t, y, ε) = (2, 1, 1/8)`: `|ν(2) 0 1 − ν(2) 1 1| = |0 − 1/2| =
1/2 > 1/4 = 2ε`. The failure mode is genuinely two-start: same-parity
starts coincide at even times, so the witness must take opposite
parities — a shape the one-start fence cannot exhibit. Isolation:
every other hypothesis is genuine at C₄ (`c4_fence_isolation_QA`). -/
theorem c4_two_start_depth_fence_QA :
    ¬ (∀ (t : ℕ) (x₁ x₂ y : Fin 4) (ε : ℝ), 0 < ε →
      Real.log (Real.sqrt (stationaryVec c4Adj y
            * ((stationaryVec c4Adj x₁)⁻¹ - 1)) / ε)
        / Real.log (1 / ((max (max (1 - secondEval (normalizedLaplacian c4Adj)
                  (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
                (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
                  ⟨3, by decide⟩ - 1)) 0 + 1) / 2))
        ≤ (t : ℝ) →
      Real.log (Real.sqrt (stationaryVec c4Adj y
            * ((stationaryVec c4Adj x₂)⁻¹ - 1)) / ε)
        / Real.log (1 / ((max (max (1 - secondEval (normalizedLaplacian c4Adj)
                  (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm) (by decide))
                (evals (normalizedLaplacian_symmetric c4Adj c4Adj_isSymm)
                  ⟨3, by decide⟩ - 1)) 0 + 1) / 2))
        ≤ (t : ℝ) →
      |walkDistribution c4Adj t x₁ y - walkDistribution c4Adj t x₂ y|
        ≤ 2 * ε) := by
  intro h
  have hthr₁ := c4_depth_threshold_junk_QA (ε := 1/8) 0 1 2
  have hthr₂ := c4_depth_threshold_junk_QA (ε := 1/8) 1 1 2
  have hcon := h 2 0 1 1 (1/8) (by norm_num) hthr₁ hthr₂
  rw [c4_dist_two_zero_QA, c4_dist_two_one_QA] at hcon
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] at hcon
  norm_num at hcon
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at hcon
  linarith
end SpectralCertificate


section EngineJoin

/-!
### The engine join's identity pins (2026-09-06,
`proposals/walktvpair-dobrushin-join.md`)

`walkTVPair_eq_tvDobrushinCoeff` joins the two-start walk distance to
the matrix-level Dobrushin engine. Pinned at the delivered `triAdj`
fixture: the engine side evaluates to the same closed forms the
`walkTVPair` side already carries (`tri_pair_one_eq_QA`,
`tri_pair_two_eq_QA`), and the submultiplicativity-attained instance
`tri_pair_two_eq_QA`'s `1/4 = 1/2 · 1/2` is now an instance of the
engine route.
-/

/-- **Engine-side `d(1) = 1/2`**: the Dobrushin coefficient of the
transition matrix itself equals the pinned two-start distance. -/
theorem tri_dobrushin_one_eq_QA :
    tvDobrushinCoeff (walkTransitionMatrix triAdj ^ 1) = 1/2 := by
  rw [← walkTVPair_eq_tvDobrushinCoeff]
  exact tri_pair_one_eq_QA

/-- **Engine-side `d(2) = 1/4`**: the coefficient of the square equals
the pinned two-start distance, and the pair pins compose — the join's
identity is load-bearing at both times. -/
theorem tri_dobrushin_two_eq_QA :
    tvDobrushinCoeff (walkTransitionMatrix triAdj ^ 2) = 1/4 := by
  rw [← walkTVPair_eq_tvDobrushinCoeff]
  exact tri_pair_two_eq_QA

/-- The submultiplicativity instance at `t = 1 + 1` is ATTAINED — now
an instance of the engine route: the identity plus the engine's
`tvDobrushinCoeff_pow_add_le` reproduces the pinned equality. -/
theorem tri_submul_attained_engine_QA :
    walkTVPair triAdj (1 + 1) = walkTVPair triAdj 1 * walkTVPair triAdj 1 := by
  rw [tri_pair_two_eq_QA, tri_pair_one_eq_QA]
  norm_num

end EngineJoin

end SpectralGraphTheory.QA
