/-
  Normalized_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Normalized`: the general
  (irregular) normalized Laplacian and its diagonal square-root
  scaffolding, instantiated at a concrete three-vertex path graph — a
  genuinely irregular graph with degrees (1, 2, 1) — and at the regular
  two-vertex edge.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  (including the symbolic `√2` entries) is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Normalized
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## A concrete irregular graph: the three-vertex path `0 — 1 — 2`
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1). -/
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

/-- All degrees of the path are positive: the interface hypothesis of
the normalized-Laplacian theorems holds. Computed directly per vertex. -/
theorem pathAdj_deg_pos (i : Fin 3) : 0 < deg pathAdj i := by
  fin_cases i <;>
    simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num

/-- Normalized-Laplacian diagonal of the path: the center entry is `1`
(the path has no self-loops, so the diagonal of `L_sym` is `1 - 0`). -/
theorem path_normalizedLaplacian_diag_QA :
    normalizedLaplacian pathAdj 1 1 = 1 := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    degreeInvSqrt, pathAdj, Real.sqrt_one, inv_one, one_mul,
    Matrix.of_apply, Fin.isValue]
  norm_num

/-- Normalized-Laplacian adjacent entry: `(L_sym) 0 1 = -1/√2` — the
degree-2 center scales the edge by `1/√(1·2)`. -/
theorem path_normalizedLaplacian_offdiag_QA :
    normalizedLaplacian pathAdj 0 1 = -(Real.sqrt 2)⁻¹ := by
  have hp01 : pathAdj 0 1 = 1 := by norm_num [pathAdj]
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    degreeInvSqrt, Real.sqrt_one, inv_one, one_mul, zero_sub,
    pathAdj_deg_zero, pathAdj_deg_one]
  rw [hp01]
  norm_num

/-- Normalized-Laplacian non-adjacent entry: `(L_sym) 0 2 = 0`. -/
theorem path_normalizedLaplacian_far_QA :
    normalizedLaplacian pathAdj 0 2 = 0 := by
  have hp02 : pathAdj 0 2 = 0 := by norm_num [pathAdj]
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    degreeInvSqrt, Real.sqrt_one, inv_one, one_mul,
    pathAdj_deg_zero, pathAdj_deg_two]
  rw [hp02]
  have hne : ¬(0 : ℕ) = 2 := by decide
  simp [hne]

/-- The congruence bridge computes at the path: the `(0,1)` entry of
`√D L_sym √D` is `-1`, the combinatorial-Laplacian entry — the square
roots cancel. -/
theorem path_congruence_entry_QA :
    (degreeSqrt pathAdj * normalizedLaplacian pathAdj
      * degreeSqrt pathAdj) 0 1 = -1 := by
  have h := congrFun (congrFun
    (degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt pathAdj
      pathAdj_deg_pos) 0) 1
  have hval : laplacian pathAdj 0 1 = -1 := by
    simp only [laplacian, degreeMatrix, Matrix.sub_apply, pathAdj,
      Matrix.of_apply, Fin.isValue, pathAdj_deg_zero]
    norm_num
  rw [hval] at h
  exact h

/-!
## Agreement with the regular cone at the two-vertex edge
-/

/-- The adjacency matrix of the single edge on `Fin 2` (symmetric,
1-regular). -/
def edgeAdj2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; 1, 0]

theorem edgeAdj2_deg (i : Fin 2) : deg edgeAdj2 i = 1 := by
  fin_cases i <;>
    simp only [deg, edgeAdj2, Matrix.of_apply, Fin.sum_univ_two] <;>
    norm_num

/-- On the regular edge, the general normalized Laplacian agrees with
the Cheeger-bridge `regularNormalizedLaplacian` — the two normalizations
coincide on the regular cone. -/
theorem edge_normalized_agrees_regular_QA :
    normalizedLaplacian edgeAdj2 = regularNormalizedLaplacian edgeAdj2 1 :=
  normalizedLaplacian_eq_regularNormalizedLaplacian edgeAdj2 1
    edgeAdj2_deg one_pos

/-!
## The walk form at the path
-/

/-- Every row of the walk transition matrix of the path sums to one:
row-stochasticity on a genuinely irregular graph. -/
theorem path_walk_row_sum_QA (i : Fin 3) :
    ∑ j, walkTransitionMatrix pathAdj i j = 1 :=
  walkTransitionMatrix_row_sum pathAdj pathAdj_deg_pos i

/-- Walk entries of the path compute: the center row places `1/2` on
each neighbor (`P 1 0 = 1/2`), the leaf rows place all mass on the
center (`P 0 1 = 1`). -/
theorem path_walk_entries_QA :
    walkTransitionMatrix pathAdj 1 0 = 1 / 2
      ∧ walkTransitionMatrix pathAdj 0 1 = 1 := by
  have h10 : pathAdj 1 0 = 1 := by norm_num [pathAdj]
  have h01 : pathAdj 0 1 = 1 := by norm_num [pathAdj]
  constructor
  · simp only [walkTransitionMatrix, Matrix.diagonal_mul, pathAdj_deg_one]
    rw [h10]
    norm_num
  · simp only [walkTransitionMatrix, Matrix.diagonal_mul, pathAdj_deg_zero]
    rw [h01]
    norm_num

/-- The similarity identity instantiated and checked entrywise at the
path: the `(1,2)` entry of `√D · L_walk · (1/√D)` equals the `(1,2)`
entry of `L_sym`, both `-1/√2` — the walk form is similar to the
symmetric normalized Laplacian. -/
theorem path_similarity_entry_QA :
    (degreeSqrt pathAdj * walkLaplacian pathAdj * degreeInvSqrt pathAdj) 1 2
      = normalizedLaplacian pathAdj 1 2 :=
  congrFun (congrFun
    (degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt pathAdj pathAdj_deg_pos)
    1) 2

/-!
## Eigenpair transfer through the similarity (mixing-time Step 1)

The path `0 — 1 — 2` has normalized spectrum `{0, 1, 2}` with hand
eigenvectors `(1, √2, 1)`, `(1, 0, -1)`, `(1, -√2, 1)`. Each eigenpair
is transferred to the *walk* world two ways — through the transfer
theorems and by raw arithmetic on the conjugated vectors (which are
`(1,1,1)`, `(1,0,-1)`, `(1,-1,1)`) — and two guards witness that the
conjugation and the `1 - μ` reflection are load-bearing.
-/

/-- Normalization bridge: `deg` unfolds to literal sums, and the
center degree lands as `1 + 1`; rewriting it to `2` puts the surviving
`√(1 + 1)` atoms into the canonical `√2` form the pinned arithmetic
facts below use. -/
theorem path_one_add_one_QA : (1 : ℝ) + 1 = 2 := by norm_num

/-- The `√2`-arithmetic used throughout: `√2 · √2 = 2`, `(1/√2) · √2 = 1`,
and `2/√2 = √2`. -/
theorem path_sqrt2_arith_QA :
    Real.sqrt 2 * Real.sqrt 2 = 2
      ∧ (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1
      ∧ 2 * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
  have ht : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  refine ⟨h2, inv_mul_cancel₀ ht, ?_⟩
  nth_rewrite 1 [← h2]
  rw [mul_assoc, mul_inv_cancel₀ ht, mul_one]

/-- The hand eigenpair at eigenvalue `0`: `(1, √2, 1)` is in the kernel
of the path's normalized Laplacian (raw computation, independent of the
transfer machinery). -/
theorem path_Lsym_eigen_zero_QA :
    normalizedLaplacian pathAdj *ᵥ ![1, Real.sqrt 2, 1]
      = (0 : ℝ) • ![1, Real.sqrt 2, 1] := by
  have hinv := path_sqrt2_arith_QA.2.1
  have htwo := path_sqrt2_arith_QA.2.2
  funext i
  fin_cases i
  all_goals simp [normalizedLaplacian, degreeInvSqrt, deg,
    path_one_add_one_QA, pathAdj, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_three]
  all_goals nlinarith [hinv, htwo]

/-- The conjugated kernel vector is the all-ones vector: the degree
square roots cancel the eigenvector's entries (raw computation). -/
theorem path_degreeInvSqrt_mulVec_kervec_QA :
    degreeInvSqrt pathAdj *ᵥ ![1, Real.sqrt 2, 1] = ![1, 1, 1] := by
  funext i
  fin_cases i <;>
    simp [degreeInvSqrt, deg, path_one_add_one_QA, pathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three]

/-- Forward transfer at eigenvalue `0`, through the theorem: the kernel
pair of `L_sym` conjugates to a kernel pair of the walk Laplacian. -/
theorem path_walkLaplacian_transfer_zero_QA :
    walkLaplacian pathAdj *ᵥ (degreeInvSqrt pathAdj *ᵥ ![1, Real.sqrt 2, 1])
      = (0 : ℝ) • (degreeInvSqrt pathAdj *ᵥ ![1, Real.sqrt 2, 1]) :=
  walkLaplacian_mulVec_degreeInvSqrt pathAdj pathAdj_deg_pos
    path_Lsym_eigen_zero_QA

/-- Raw cross-check of the transferred kernel pair: the walk Laplacian
annihilates the all-ones vector (computed directly from `P = D⁻¹A`'s
entries, independent of the transfer theorem and of `Stationary`). -/
theorem path_walkLaplacian_ones_raw_QA :
    walkLaplacian pathAdj *ᵥ ![1, 1, 1] = 0 := by
  funext i
  fin_cases i
  all_goals simp [walkLaplacian, walkTransitionMatrix, deg,
    path_one_add_one_QA, pathAdj, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_three]
  all_goals nlinarith [path_sqrt2_arith_QA.2.1]

/-- The hand eigenpair at eigenvalue `1`: `(1, 0, -1)`. -/
theorem path_Lsym_eigen_one_QA :
    normalizedLaplacian pathAdj *ᵥ ![1, 0, -1]
      = (1 : ℝ) • ![1, 0, -1] := by
  funext i
  fin_cases i <;>
    simp [normalizedLaplacian, degreeInvSqrt, deg, path_one_add_one_QA,
      pathAdj, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]

/-- Transition transfer at eigenvalue `1`: the `1`-eigenpair of `L_sym`
gives a `0`-eigenpair of the walk transition matrix, through the
theorem. -/
theorem path_walkTransition_transfer_one_QA :
    walkTransitionMatrix pathAdj *ᵥ (degreeInvSqrt pathAdj *ᵥ ![1, 0, -1])
      = (1 - 1 : ℝ) • (degreeInvSqrt pathAdj *ᵥ ![1, 0, -1]) :=
  walkTransitionMatrix_mulVec_degreeInvSqrt pathAdj pathAdj_deg_pos
    path_Lsym_eigen_one_QA

/-- Raw cross-check: the transition matrix annihilates `(1, 0, -1)`
(the leaf rows move the difference to the center, where it cancels). -/
theorem path_walkTransition_middle_raw_QA :
    walkTransitionMatrix pathAdj *ᵥ ![1, 0, -1] = 0 := by
  funext i
  fin_cases i <;>
    simp [walkTransitionMatrix, deg, path_one_add_one_QA, pathAdj,
      Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]

/-- The hand eigenpair at eigenvalue `2`: `(1, -√2, 1)`. -/
theorem path_Lsym_eigen_two_QA :
    normalizedLaplacian pathAdj *ᵥ ![1, -Real.sqrt 2, 1]
      = (2 : ℝ) • ![1, -Real.sqrt 2, 1] := by
  have hinv := path_sqrt2_arith_QA.2.1
  have htwo := path_sqrt2_arith_QA.2.2
  funext i
  fin_cases i
  all_goals simp [normalizedLaplacian, degreeInvSqrt, deg,
    path_one_add_one_QA, pathAdj, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_three]
  all_goals nlinarith [hinv, htwo]

/-- The conjugate of `(1, -√2, 1)` is `(1, -1, 1)` (raw computation). -/
theorem path_degreeInvSqrt_mulVec_alt_QA :
    degreeInvSqrt pathAdj *ᵥ ![1, -Real.sqrt 2, 1] = ![1, -1, 1] := by
  funext i
  fin_cases i <;>
    simp [degreeInvSqrt, deg, path_one_add_one_QA, pathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three]

/-- Transition transfer at eigenvalue `2`: the `2`-eigenpair of `L_sym`
gives a `(1 - 2)`-eigenpair of the transition matrix, through the
theorem. -/
theorem path_walkTransition_transfer_two_QA :
    walkTransitionMatrix pathAdj *ᵥ
      (degreeInvSqrt pathAdj *ᵥ ![1, -Real.sqrt 2, 1])
      = (1 - 2 : ℝ) • (degreeInvSqrt pathAdj *ᵥ ![1, -Real.sqrt 2, 1]) :=
  walkTransitionMatrix_mulVec_degreeInvSqrt pathAdj pathAdj_deg_pos
    path_Lsym_eigen_two_QA

/-- Raw cross-check: the transition matrix acts on `(1, -1, 1)` as
multiplication by `-1` — the alternating (period-2) mode of the path
walk. -/
theorem path_walkTransition_alt_raw_QA :
    walkTransitionMatrix pathAdj *ᵥ ![1, -1, 1]
      = (-1 : ℝ) • ![1, -1, 1] := by
  funext i
  fin_cases i
  all_goals simp [walkTransitionMatrix, deg, path_one_add_one_QA, pathAdj,
    Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three]
  all_goals norm_num

/-- The walk-Laplacian eigenpair at `(1, -1, 1)`: eigenvalue `2`, by raw
arithmetic (`L_walk = 1 - P`, `P *ᵥ w = -w`). -/
theorem path_walkLaplacian_alt_raw_QA :
    walkLaplacian pathAdj *ᵥ ![1, -1, 1] = (2 : ℝ) • ![1, -1, 1] := by
  funext i
  fin_cases i
  all_goals simp [walkLaplacian, walkTransitionMatrix, deg,
    path_one_add_one_QA, pathAdj, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_three]
  all_goals nlinarith [path_sqrt2_arith_QA.2.1]

/-- Backward transfer, through the theorem: the raw walk eigenpair
`(1, -1, 1)` at eigenvalue `2` conjugates back to a `2`-eigenpair of
`L_sym`. -/
theorem path_backward_transfer_QA :
    normalizedLaplacian pathAdj *ᵥ (degreeSqrt pathAdj *ᵥ ![1, -1, 1])
      = (2 : ℝ) • (degreeSqrt pathAdj *ᵥ ![1, -1, 1]) :=
  normalizedLaplacian_mulVec_degreeSqrt pathAdj pathAdj_deg_pos
    path_walkLaplacian_alt_raw_QA

/-- The backward-conjugated witness is the hand eigenvector `(1, -√2, 1)`
— the two routes produce the same vector. -/
theorem path_degreeSqrt_mulVec_alt_QA :
    degreeSqrt pathAdj *ᵥ ![1, -1, 1] = ![1, -Real.sqrt 2, 1] := by
  funext i
  fin_cases i <;>
    simp [degreeSqrt, deg, path_one_add_one_QA, pathAdj, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_three]

/-- Every entry of the transferred walk spectrum is a genuine eigenvalue
of the transition matrix with a nonzero witness — the existential
interface instantiated at each of the path's three spectral indices. -/
theorem path_exists_walk_eigenvector_QA (k : Fin 3) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      walkTransitionMatrix pathAdj *ᵥ w
        = walkEvals pathAdj pathAdj_isSymm k • w :=
  exists_eigenvector_walkTransitionMatrix_eq_walkEvals pathAdj
    pathAdj_isSymm pathAdj_deg_pos k

/-- The transferred family spans, on the fixture: the three conjugated
eigenvectors reconstruct `(1, 2, 3)` with hand-solved coefficients
`2, -1, 0` (independent of the theorem — a linear solve). -/
theorem path_transferred_span_QA :
    (2 : ℝ) • ![1, 1, 1] + (-1 : ℝ) • ![1, 0, -1] + (0 : ℝ) • ![1, -1, 1]
      = (![1, 2, 3] : Fin 3 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      smul_eq_mul] <;>
    norm_num

/-- **Guard:** the conjugation is load-bearing. The walk eigenvector
`(1, -1, 1)` (eigenvalue `2` of `L_walk`) is *not* an eigenvector of
`L_sym` at the reflected eigenvalue `-1`: skipping the `√D`
conjugation is refutable. -/
theorem path_no_skip_conjugation_QA :
    ¬ (normalizedLaplacian pathAdj *ᵥ ![1, -1, 1]
        = (-1 : ℝ) • ![1, -1, 1]) := by
  have htwo := path_sqrt2_arith_QA.2.2
  have hnn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  intro h
  have e1 := congrFun h 1
  simp [normalizedLaplacian, degreeInvSqrt, deg, path_one_add_one_QA,
    pathAdj, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
    Pi.smul_apply, smul_eq_mul] at e1
  nlinarith [htwo, hnn]

/-- **Guard:** the `1 - μ` reflection is load-bearing. The transition
matrix does *not* act on `(1, -1, 1)` as multiplication by `2` (the
unreflected normalized eigenvalue): the raw action is by `-1`. -/
theorem path_transition_not_unreflected_QA :
    ¬ (walkTransitionMatrix pathAdj *ᵥ ![1, -1, 1]
        = (2 : ℝ) • ![1, -1, 1]) := by
  rw [path_walkTransition_alt_raw_QA]
  intro h
  have h0 := congrFun h 0
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.head_cons] at h0
  norm_num at h0

end SpectralGraphTheory.QA
