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

  Since 2026-09-04 this file also carries the family's adversarial
  fence audit (`AdversarialFences`): hypothesis-form negative witnesses
  plus isolation companions for every load-bearing clause of
  `Normalized.lean`'s theorem surface
  (`proposals/adversarial-fences-normalized-family.md`).

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

/-!
## The adversarial fence audit (`proposals/adversarial-fences-normalized-family.md`)

Hypothesis-form fences for the load-bearing clauses of
`Scaffold.Mathlib.GraphTheory.Normalized`'s theorem surface — the audit
method's fourteenth application, over the library's most-consumed
unaudited shelf (20 transitive non-QA consumers). Every fence refutes a
*theorem* instantiation; nothing admitted is consumed.

The fixtures:
- `nfNegEdge` — symmetric `Fin 2` `!![-2, 1; 1, 0]]`, degrees (-1, 1):
  the negative-degree corner, the headline fixture.
  `degreeSqrt = degreeInvSqrt = diag(0, 1)`, `L_sym` degenerates to the
  identity, `P = !![2, -1; 1, 0]]`, `L_walk = !![-1, 1; -1, 1]]` — the
  genuine negative row is what breaks the congruence, similarity,
  commutation, and transfer families (at *symmetric zero-degree*
  fixtures those dropped statements are provable: the junk kills both
  sides identically — the P4 finding recorded in the proposal).
- `nfIso` — symmetric `Fin 3` `K₂ ⊕ isolated`, degrees (1, 1, 0): the
  zero-degree corner, where the junk row of `P` and the junk identity
  entry of `L_sym` genuinely separate.
- `nfNegI` — symmetric `Fin 2` `diag(-1, -1)`, degrees (-1, -1).
- `nfAsymAdj` — asymmetric `Fin 2` `!![0, 2; 1, 0]]`, degrees (2, 1):
  the family's only signature-free symmetry clause dies here.
- the delivered `edgeAdj2` (K₂), reused.
-/

/-- The negative-degree fixture: symmetric, degrees (-1, 1). -/
def nfNegEdge : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![-2, 1; 1, 0]

/-- The zero-degree fixture: symmetric `K₂ ⊕ isolated vertex`,
degrees (1, 1, 0). -/
def nfIso : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 0; 0, 0, 0]

/-- The all-negative fixture: symmetric, degrees (-1, -1). -/
def nfNegI : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![-1, 0; 0, -1]

/-- The asymmetric fixture with positive degrees (2, 1). -/
def nfAsymAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 2; 1, 0]

/-!
### Index disjunction (the robust route around the eta-wrapped
`fin_cases` literal trap, recorded by the kernel-bridge audit)
-/

theorem nfFin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

theorem nfFin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  fin_cases i <;> simp

theorem nf_sqrt_neg_one : Real.sqrt (-1 : ℝ) = 0 :=
  Real.sqrt_eq_zero_of_nonpos (by norm_num)

/-!
### The fixtures' structural pins
-/

theorem nfNegEdge_isSymm : nfNegEdge.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply, nfNegEdge]

theorem nfIso_isSymm : nfIso.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply, nfIso]

theorem nfNegI_isSymm : nfNegI.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.transpose_apply, nfNegI]

theorem nfNegEdge_deg_zero : deg nfNegEdge 0 = -1 := by
  simp only [deg, nfNegEdge, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

theorem nfNegEdge_deg_one : deg nfNegEdge 1 = 1 := by
  simp only [deg, nfNegEdge, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

theorem nfIso_deg_zero : deg nfIso 0 = 1 := by
  simp only [deg, nfIso, Matrix.of_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

theorem nfIso_deg_one : deg nfIso 1 = 1 := by
  simp only [deg, nfIso, Matrix.of_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

theorem nfIso_deg_two : deg nfIso 2 = 0 := by
  simp only [deg, nfIso, Matrix.of_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.tail_cons, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

theorem nfNegI_deg (i : Fin 2) : deg nfNegI i = -1 := by
  rcases nfFin2_cases i with rfl | rfl
  · simp only [deg, nfNegI, Matrix.of_apply, Fin.sum_univ_two]
    norm_num
  · simp only [deg, nfNegI, Matrix.of_apply, Fin.sum_univ_two]
    norm_num

theorem nfAsym_deg_zero : deg nfAsymAdj 0 = 2 := by
  simp only [deg, nfAsymAdj, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

theorem nfAsym_deg_one : deg nfAsymAdj 1 = 1 := by
  simp only [deg, nfAsymAdj, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

/-!
### The pinned matrices at the negative-degree fixture
-/

theorem nfNegEdge_degreeSqrt :
    degreeSqrt nfNegEdge = Matrix.diagonal ![0, 1] := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [degreeSqrt, Matrix.diagonal_apply, deg, nfNegEdge,
      Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Fin.isValue, reduceIte]
  all_goals norm_num
  all_goals simp only [nf_sqrt_neg_one, Real.sqrt_one, Real.sqrt_zero]

theorem nfNegEdge_degreeInvSqrt :
    degreeInvSqrt nfNegEdge = Matrix.diagonal ![0, 1] := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [degreeInvSqrt, Matrix.diagonal_apply, deg, nfNegEdge,
      Matrix.of_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Fin.isValue, reduceIte]
  all_goals norm_num
  all_goals
    simp only [nf_sqrt_neg_one, Real.sqrt_one, Real.sqrt_zero,
      inv_zero, inv_one]

/-- The normalized Laplacian of the negative-degree fixture is the
*identity*: the reciprocal factor `1/√(-1) = 0` kills the congruence
entirely. -/
theorem nfNegEdge_Lsym : normalizedLaplacian nfNegEdge = 1 := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, nfNegEdge, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte]
  all_goals norm_num
  all_goals
    simp only [nf_sqrt_neg_one, Real.sqrt_one, Real.sqrt_zero,
      inv_zero, inv_one, zero_mul, mul_zero, one_mul]

theorem nfNegI_Lsym : normalizedLaplacian nfNegI = 1 := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, nfNegI, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte]
  all_goals norm_num
  all_goals
    simp only [nf_sqrt_neg_one, Real.sqrt_one, Real.sqrt_zero,
      inv_zero, inv_one, zero_mul, mul_zero, one_mul]

/-- The walk transition matrix of the negative-degree fixture, pinned:
the negative row is scaled by the *genuine* `(-1)⁻¹ = -1`. -/
theorem nfNegEdge_P : walkTransitionMatrix nfNegEdge = !![2, -1; 1, 0] := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [walkTransitionMatrix_apply, deg, nfNegEdge,
      Matrix.of_apply, Fin.isValue, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  all_goals norm_num

theorem nfNegEdge_walkLap : walkLaplacian nfNegEdge = !![-1, 1; -1, 1] := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
      nfNegEdge_P, Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, neg_sub, reduceIte]
  all_goals norm_num

theorem nfNegEdge_lap : laplacian nfNegEdge = !![1, -1; -1, 1] := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [laplacian, degreeMatrix, Matrix.sub_apply, deg, nfNegEdge,
      Matrix.of_apply, Fin.isValue, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      reduceIte]
  all_goals norm_num

/-!
### The action pins
-/

theorem nfNegEdge_dis_mulVec (x : Fin 2 → ℝ) :
    degreeInvSqrt nfNegEdge *ᵥ x = ![0, x 1] := by
  funext i
  rcases nfFin2_cases i with rfl | rfl
  · rw [degreeInvSqrt_mulVec_apply, nfNegEdge_deg_zero, nf_sqrt_neg_one]
    simp
  · rw [degreeInvSqrt_mulVec_apply, nfNegEdge_deg_one]
    simp

theorem nfNegEdge_ds_mulVec (x : Fin 2 → ℝ) :
    degreeSqrt nfNegEdge *ᵥ x = ![0, x 1] := by
  funext i
  rcases nfFin2_cases i with rfl | rfl
  · rw [degreeSqrt_mulVec_apply, nfNegEdge_deg_zero, nf_sqrt_neg_one]
    simp
  · rw [degreeSqrt_mulVec_apply, nfNegEdge_deg_one]
    simp

theorem nfNegEdge_walkLap_mulVec (x : Fin 2 → ℝ) :
    walkLaplacian nfNegEdge *ᵥ x = ![x 1 - x 0, x 1 - x 0] := by
  rw [nfNegEdge_walkLap]
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    simp only [Matrix.of_apply, Fin.isValue, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
  all_goals ring

theorem nfNegEdge_P_mulVec (x : Fin 2 → ℝ) :
    walkTransitionMatrix nfNegEdge *ᵥ x = ![2 * x 0 - x 1, x 0] := by
  rw [nfNegEdge_P]
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    simp only [Matrix.of_apply, Fin.isValue, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
  all_goals ring

/-!
### The K₂ action pins (the delivered `edgeAdj2`, degrees (1, 1))
-/

theorem edgeAdj2_dis_mulVec (x : Fin 2 → ℝ) :
    degreeInvSqrt edgeAdj2 *ᵥ x = x := by
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    rw [degreeInvSqrt_mulVec_apply, edgeAdj2_deg, Real.sqrt_one]
  all_goals simp

theorem edgeAdj2_ds_mulVec (x : Fin 2 → ℝ) :
    degreeSqrt edgeAdj2 *ᵥ x = x := by
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    rw [degreeSqrt_mulVec_apply, edgeAdj2_deg, Real.sqrt_one]
  all_goals simp

theorem edgeAdj2_walkLap_mulVec (x : Fin 2 → ℝ) :
    walkLaplacian edgeAdj2 *ᵥ x = ![x 0 - x 1, x 1 - x 0] := by
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    simp only [walkLaplacian, Matrix.sub_apply, Matrix.one_apply,
      walkTransitionMatrix_apply, deg, edgeAdj2, Matrix.of_apply,
      Fin.isValue, Fin.sum_univ_two, inv_one, one_mul, Matrix.mulVec,
      Matrix.dotProduct, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, neg_sub, reduceIte]
  all_goals norm_num
  all_goals (try ring)

theorem edgeAdj2_Lsym_mulVec (x : Fin 2 → ℝ) :
    normalizedLaplacian edgeAdj2 *ᵥ x = ![x 0 - x 1, x 1 - x 0] := by
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, edgeAdj2, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Real.sqrt_one, inv_one, one_mul, Matrix.mulVec,
      Matrix.dotProduct, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, neg_sub, reduceIte]
  all_goals norm_num
  all_goals (try ring)

theorem edgeAdj2_P_mulVec (x : Fin 2 → ℝ) :
    walkTransitionMatrix edgeAdj2 *ᵥ x = ![x 1, x 0] := by
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    simp only [walkTransitionMatrix_apply, deg, edgeAdj2,
      Matrix.of_apply, Fin.isValue, Fin.sum_univ_two, inv_one, one_mul,
      Matrix.mulVec, Matrix.dotProduct, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, reduceIte]
  all_goals norm_num

/-!
## The A section: the diagonal layer
-/

/-- **A1 — `degreeSqrt_mul_degreeSqrt`'s `hdeg` clause is
load-bearing.** At the all-negative fixture `√(-1) = 0`, so the product
is the zero matrix, while the degree matrix is `diag(-1, -1)`. -/
theorem nf_sqrt_mul_sqrt_hdeg_fence :
    ¬ (degreeSqrt nfNegI * degreeSqrt nfNegI = degreeMatrix nfNegI) := by
  intro h
  have e00 := congrFun (congrFun h 0) 0
  simp only [degreeSqrt, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply,
    degreeMatrix, nfNegI_deg, if_pos rfl, nf_sqrt_neg_one, zero_mul] at e00
  norm_num at e00

/-- A1 isolation: the dropped `hdeg` genuinely fails (degree `-1`),
and the failure is the square-root corner, not a junk degeneracy of the
whole fixture. -/
theorem nf_sqrt_mul_sqrt_hdeg_isolation :
    nfNegI.IsSymm ∧ deg nfNegI 0 < 0 := by
  refine ⟨nfNegI_isSymm, ?_⟩
  rw [nfNegI_deg]
  norm_num

/-- **A2 — `degreeSqrt_mul_degreeInvSqrt`'s `hd` clause is
load-bearing.** At the zero-degree vertex the product entry is
`√0 · (1/√0) = 0 ≠ 1`. -/
theorem nf_sqrt_mul_invsqrt_hd_fence :
    ¬ (degreeSqrt nfIso * degreeInvSqrt nfIso = 1) := by
  intro h
  have e22 := congrFun (congrFun h 2) 2
  simp only [degreeSqrt, degreeInvSqrt, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Matrix.one_apply, nfIso_deg_two,
    Real.sqrt_zero, inv_zero, zero_mul] at e22
  norm_num at e22

/-- **A3 — `degreeInvSqrt_mul_degreeSqrt`'s `hd` clause is
load-bearing** (the mirror of A2 at the same entry). -/
theorem nf_invsqrt_mul_sqrt_hd_fence :
    ¬ (degreeInvSqrt nfIso * degreeSqrt nfIso = 1) := by
  intro h
  have e22 := congrFun (congrFun h 2) 2
  simp only [degreeSqrt, degreeInvSqrt, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_apply, Matrix.one_apply, nfIso_deg_two,
    Real.sqrt_zero, inv_zero, zero_mul] at e22
  norm_num at e22

/-- A2/A3 isolation: the dropped `hd` genuinely fails at vertex 2**
(degree `0`), on a symmetric fixture — the zero-degree corner, not a
global degeneracy. -/
theorem nf_sqrt_invsqrt_hd_isolation :
    nfIso.IsSymm ∧ deg nfIso 2 = 0 :=
  ⟨nfIso_isSymm, nfIso_deg_two⟩

/-- **A4 — `degreeInvSqrt_mulVec_ne_zero`'s `hd` clause is
load-bearing.** The kept clause `hv` is genuine: `e₂ ≠ 0`; but the
conjugation annihilates it (`1/√0 = 0`). -/
theorem nf_dis_mulVec_ne_zero_hd_fence :
    degreeInvSqrt nfIso *ᵥ ![0, 0, 1] = 0 := by
  funext i
  rcases nfFin3_cases i with rfl | rfl | rfl
  · rw [degreeInvSqrt_mulVec_apply, nfIso_deg_zero, Real.sqrt_one]
    simp
  · rw [degreeInvSqrt_mulVec_apply, nfIso_deg_one, Real.sqrt_one]
    simp
  · rw [degreeInvSqrt_mulVec_apply, nfIso_deg_two, Real.sqrt_zero]
    simp

theorem nf_dis_mulVec_ne_zero_hd_isolation :
    (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have e2 := congrFun h 2
  simp at e2

/-- **A5 — `degreeInvSqrt_mulVec_ne_zero`'s `hv` clause is
load-bearing.** At `v = 0` the image is `0`, so the dropped statement
`image ≠ 0` is refuted outright; the kept `hd` is genuine on `K₂`. -/
theorem nf_dis_mulVec_ne_zero_hv_fence :
    degreeInvSqrt edgeAdj2 *ᵥ 0 = 0 :=
  Matrix.mulVec_zero _

theorem nf_dis_mulVec_ne_zero_hv_isolation :
    ∀ i, 0 < deg edgeAdj2 i := by
  intro i
  rw [edgeAdj2_deg i]
  norm_num

/-!
## The B section: the normalized layer
-/

/-- **B1 — `normalizedLaplacian_symmetric`'s `hA` clause is
load-bearing** — the family's only signature-free symmetry clause.
The asymmetric fixture has positive degrees (no junk anywhere), and the
congruence sees the asymmetric entries: `L_sym 0 1 = -√2 ≠ -1/√2 =
L_sym 1 0`. -/
theorem nf_Lsym_hA_fence : ¬ (normalizedLaplacian nfAsymAdj).IsSymm := by
  intro h
  have hT : (normalizedLaplacian nfAsymAdj)ᵀ = normalizedLaplacian nfAsymAdj :=
    h
  have e01 := congrFun (congrFun hT 0) 1
  rw [Matrix.transpose_apply] at e01
  have h01 : normalizedLaplacian nfAsymAdj 0 1 = -(Real.sqrt 2) := by
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, nfAsymAdj, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte]
    norm_num
    rw [mul_comm ((Real.sqrt 2 : ℝ)⁻¹) 2, path_sqrt2_arith_QA.2.2]
  have h10 : normalizedLaplacian nfAsymAdj 1 0 = -(Real.sqrt 2)⁻¹ := by
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, nfAsymAdj, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte]
    norm_num
  rw [h01, h10] at e01
  have hsq : (Real.sqrt 2 : ℝ) * (Real.sqrt 2 : ℝ) = 2 :=
    path_sqrt2_arith_QA.1
  have hin : (Real.sqrt 2 : ℝ)⁻¹ * Real.sqrt 2 = 1 :=
    path_sqrt2_arith_QA.2.1
  have heq : (Real.sqrt 2 : ℝ)⁻¹ = Real.sqrt 2 := by linarith
  rw [heq] at hin
  linarith

/-- B1 isolation: the asymmetric fixture's degrees are both positive —
the symmetry clause is the only failing structure. -/
theorem nf_Lsym_hA_isolation : ∀ i, 0 < deg nfAsymAdj i := by
  intro i
  rcases nfFin2_cases i with rfl | rfl
  · rw [nfAsym_deg_zero]; norm_num
  · rw [nfAsym_deg_one]; norm_num

/-- **B2 — the congruence bridge's `hd` clause is load-bearing.** At
the negative-degree fixture the bridge reads
`diag(0,1) · 1 · diag(0,1) = diag(0,1)` against the combinatorial
`L = !![1, -1; -1, 1]]` — mismatched at entry `(0, 0)`. -/
theorem nf_congruence_hd_fence :
    ¬ (degreeSqrt nfNegEdge * normalizedLaplacian nfNegEdge * degreeSqrt nfNegEdge
      = laplacian nfNegEdge) := by
  intro h
  rw [nfNegEdge_Lsym, Matrix.mul_one, nfNegEdge_degreeSqrt,
    Matrix.diagonal_mul_diagonal, nfNegEdge_lap] at h
  have e00 := congrFun (congrFun h 0) 0
  simp only [Matrix.diagonal_apply, if_pos rfl, Matrix.of_apply,
    Fin.isValue, Matrix.cons_val_zero, Matrix.head_cons] at e00
  norm_num at e00

/-- **B3 — the left-multiplied congruence's `hd` clause is
load-bearing.** At entry `(1, 0)`: `L_sym √D` carries the zero column
factor (`√(deg 0) = 0`), while `(1/√D) L` scales row 1 genuinely:
`-1`. -/
theorem nf_left_congruence_hd_fence :
    ¬ (normalizedLaplacian nfNegEdge * degreeSqrt nfNegEdge
      = degreeInvSqrt nfNegEdge * laplacian nfNegEdge) := by
  intro h
  rw [nfNegEdge_Lsym, Matrix.one_mul, nfNegEdge_degreeSqrt,
    nfNegEdge_degreeInvSqrt, nfNegEdge_lap] at h
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero] at e10
  norm_num at e10

/-- **B4 — the kernel-vector theorem's `hd` clause is load-bearing.**
The stretched constant is `√D *ᵥ 1 = ![0, 1]`, and the degenerate
identity `L_sym` maps it to `![0, 1] ≠ 0`. -/
theorem nf_kernel_vec_hd_fence :
    ¬ (normalizedLaplacian nfNegEdge *ᵥ (degreeSqrt nfNegEdge *ᵥ onesVec) = 0) := by
  intro h
  rw [nfNegEdge_ds_mulVec, nfNegEdge_Lsym, Matrix.one_mulVec] at h
  have e1 := congrFun h 1
  simp only [onesVec, Matrix.cons_val_one, Matrix.head_cons,
    Pi.zero_apply] at e1
  norm_num at e1

/-- **B5 — the identity-degeneration theorem's `hdeg` clause is
load-bearing.** On `K₂` (every degree positive, so `hdeg` genuinely
fails) the normalized Laplacian is `1 - A ≠ 1`. -/
theorem nf_eq_one_hdeg_fence :
    ¬ (normalizedLaplacian edgeAdj2 = 1) := by
  intro h
  have e01 := congrFun (congrFun h 0) 1
  have hL : normalizedLaplacian edgeAdj2 0 1 = -1 := by
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, edgeAdj2, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte]
    norm_num
  rw [hL] at e01
  norm_num at e01

/-- B5 isolation: the dropped `hdeg` fails from positivity (degree `1`
at every vertex) — the fixture is a genuine graph. -/
theorem nf_eq_one_hdeg_isolation :
    ∀ i, 0 < deg edgeAdj2 i := nf_dis_mulVec_ne_zero_hv_isolation

/-- **B6 — the regular-agreement theorem's `hd` clause is
load-bearing.** Claiming the wrong degree `d = 2` on `K₂` (degrees `1`,
so `hd` fails and `hdpos : 0 < 2` is genuine) compares `1 - A` against
`1 - ½A`. -/
theorem nf_regular_hd_fence :
    ¬ (normalizedLaplacian edgeAdj2
      = regularNormalizedLaplacian edgeAdj2 2) := by
  intro h
  have e01 := congrFun (congrFun h 0) 1
  have hL : normalizedLaplacian edgeAdj2 0 1 = -1 := by
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, edgeAdj2, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte]
    norm_num
  have hR : regularNormalizedLaplacian edgeAdj2 2 0 1 = -(1/2) := by
    simp only [regularNormalizedLaplacian, Matrix.sub_apply,
      Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, edgeAdj2,
      Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one]
    norm_num
  rw [hL, hR] at e01
  norm_num at e01

/-- B6 isolation: `hdpos` is genuine at `d = 2`. -/
theorem nf_regular_hd_isolation : (0 : ℝ) < 2 := by norm_num

/-- **B7 — the regular-agreement theorem's `hdpos` clause is
load-bearing.** At `d = -1` with `hd` genuine (every degree `-1`): the
normalized side degenerates to the junk identity `1`, while
`1 - (-1)⁻¹ • A = 1 + A = 0`. -/
theorem nf_regular_hdpos_fence :
    ¬ (normalizedLaplacian nfNegI = regularNormalizedLaplacian nfNegI (-1)) := by
  intro h
  have e00 := congrFun (congrFun h 0) 0
  have hL : normalizedLaplacian nfNegI 0 0 = 1 := by
    rw [nfNegI_Lsym]; simp
  have hR : regularNormalizedLaplacian nfNegI (-1) 0 0 = 0 := by
    simp only [regularNormalizedLaplacian, Matrix.sub_apply,
      Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, nfNegI,
      Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.head_cons]
    norm_num
  rw [hL, hR] at e00
  norm_num at e00

/-- B7 isolation: `hd` is genuine at `d = -1`. -/
theorem nf_regular_hdpos_isolation : ∀ i, deg nfNegI i = -1 := nfNegI_deg

/-!
## The C section: the walk layer
-/

/-- **C1 — `walkTransitionMatrix_row_sum`'s `hd` clause is
load-bearing.** The zero-degree vertex's row is junk: every entry
`0⁻¹ · A 2 j = 0`, so the row sum is `0 ≠ 1`. -/
theorem nf_row_sum_hd_fence : ¬ (∑ j, walkTransitionMatrix nfIso 2 j = 1) := by
  intro h
  have hz : ∀ j, walkTransitionMatrix nfIso 2 j = 0 := by
    intro j
    rw [walkTransitionMatrix_apply, nfIso_deg_two, inv_zero, zero_mul]
  rw [Finset.sum_eq_zero (fun j _ => hz j)] at h
  norm_num at h

/-- **C2 — `walkTransitionMatrix_mulVec_one`'s `hd` clause is
load-bearing.** At the zero-degree vertex: `(P *ᵥ 1) 2 = 0 ≠ 1`. -/
theorem nf_mulVec_one_hd_fence :
    ¬ (walkTransitionMatrix nfIso *ᵥ (1 : Fin 3 → ℝ) = 1) := by
  intro h
  have e2 := congrFun h 2
  have hz : ∀ j, walkTransitionMatrix nfIso 2 j = 0 := by
    intro j
    rw [walkTransitionMatrix_apply, nfIso_deg_two, inv_zero, zero_mul]
  simp only [Matrix.mulVec, Matrix.dotProduct, Pi.one_apply, mul_one,
    Finset.sum_eq_zero (fun j _ => hz j), Pi.zero_apply] at e2
  norm_num at e2

/-- **C3 — the similarity identity's `hd` clause is load-bearing.** The
conjugation `√D L_walk (1/√D)` carries the zero row/column factors and
collapses to `diag(0, 1)`, while `L_sym` is the identity — mismatched
at entry `(0, 0)`. -/
theorem nf_similarity_hd_fence :
    ¬ (degreeSqrt nfNegEdge * walkLaplacian nfNegEdge * degreeInvSqrt nfNegEdge
      = normalizedLaplacian nfNegEdge) := by
  intro h
  rw [nfNegEdge_degreeSqrt, nfNegEdge_degreeInvSqrt, nfNegEdge_Lsym] at h
  have e00 := congrFun (congrFun h 0) 0
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply, if_pos rfl, Matrix.one_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.head_cons, nfNegEdge_walkLap,
    Matrix.of_apply, mul_zero, sub_self] at e00
  norm_num at e00

/-- The negative-degree fixture's packaged isolation: symmetric, the
dropped `hd` fails at exactly the negative vertex, and the
eigen-hypotheses used by the transfer fences are genuine at the pinned
matrices. -/
theorem nf_transfer_hd_isolation :
    nfNegEdge.IsSymm ∧ deg nfNegEdge 0 < 0
      ∧ normalizedLaplacian nfNegEdge *ᵥ ![0, 1] = (1 : ℝ) • ![0, 1]
      ∧ walkLaplacian nfNegEdge *ᵥ ![1, 1] = 0 := by
  refine ⟨nfNegEdge_isSymm, ?_, ?_, ?_⟩
  · rw [nfNegEdge_deg_zero]; norm_num
  · rw [nfNegEdge_Lsym]
    simp [Matrix.one_mulVec]
  · rw [nfNegEdge_walkLap_mulVec]
    funext i
    rcases nfFin2_cases i with rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.cons_val_one, Pi.zero_apply] <;>
    norm_num

/-- **C4 — the forward transfer's `hd` clause is load-bearing.** At the
negative-degree fixture the `L_sym` side degenerates to the identity
(the eigen-hypothesis `L_sym *ᵥ ![0,1] = 1 • ![0,1]` is genuine), but
the walk row `(deg 0)⁻¹ = (-1)⁻¹` is genuine and moves mass:
`L_walk *ᵥ ![0,1] = ![1,1] ≠ ![0,1]`. -/
theorem nf_forward_transfer_hd_fence :
    ¬ (walkLaplacian nfNegEdge *ᵥ (degreeInvSqrt nfNegEdge *ᵥ ![0, 1])
      = (1 : ℝ) • (degreeInvSqrt nfNegEdge *ᵥ ![0, 1])) := by
  intro h
  rw [nfNegEdge_dis_mulVec, nfNegEdge_walkLap_mulVec] at h
  have e0 := congrFun h 0
  simp only [Matrix.cons_val_zero, Matrix.head_cons, smul_eq_mul,
    mul_zero] at e0
  norm_num at e0

/-- **C5 — the forward transfer's `h` clause is load-bearing.** On
`K₂` (`hd` genuine) the non-eigenvector `v = e₀` at `μ = 0`:
`L_walk *ᵥ e₀ = ![1, -1] ≠ 0`. -/
theorem nf_forward_transfer_h_fence :
    ¬ (walkLaplacian edgeAdj2 *ᵥ (degreeInvSqrt edgeAdj2 *ᵥ ![1, 0])
      = (0 : ℝ) • (degreeInvSqrt edgeAdj2 *ᵥ ![1, 0])) := by
  intro h
  rw [edgeAdj2_dis_mulVec, edgeAdj2_walkLap_mulVec] at h
  have e0 := congrFun h 0
  simp only [Matrix.cons_val_zero, Matrix.head_cons, smul_eq_mul,
    zero_mul, sub_zero] at e0
  norm_num at e0

/-- **C6 — the backward transfer's `hd` clause is load-bearing.** The
walk side genuinely annihilates `w = ![1,1]` (`L_walk *ᵥ ![1,1] = 0`,
so `h` holds at `μ = 0`), but the conjugate `√D *ᵥ ![1,1] = ![0,1]`
hits the identity `L_sym` and survives: `![0,1] ≠ 0`. -/
theorem nf_backward_transfer_hd_fence :
    ¬ (normalizedLaplacian nfNegEdge *ᵥ (degreeSqrt nfNegEdge *ᵥ ![1, 1])
      = (0 : ℝ) • (degreeSqrt nfNegEdge *ᵥ ![1, 1])) := by
  intro h
  rw [nfNegEdge_ds_mulVec, nfNegEdge_Lsym, Matrix.one_mulVec, zero_smul] at h
  have e1 := congrFun h 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at e1
  norm_num at e1

/-- **C7 — the backward transfer's `h` clause is load-bearing.** On
`K₂`, the non-eigenvector `w = e₀` at `μ = 0`: `L_sym *ᵥ e₀ =
![1, -1] ≠ 0`. -/
theorem nf_backward_transfer_h_fence :
    ¬ (normalizedLaplacian edgeAdj2 *ᵥ (degreeSqrt edgeAdj2 *ᵥ ![1, 0])
      = (0 : ℝ) • (degreeSqrt edgeAdj2 *ᵥ ![1, 0])) := by
  intro h
  rw [edgeAdj2_ds_mulVec, edgeAdj2_Lsym_mulVec] at h
  have e0 := congrFun h 0
  simp only [Matrix.cons_val_zero, Matrix.head_cons, smul_eq_mul,
    zero_mul, sub_zero] at e0
  norm_num at e0

/-- **C8 — the transition transfer's `hd` clause is load-bearing.** The
same genuine `L_sym`-eigenpair as C4 (`μ = 1`), but `P *ᵥ ![0,1] =
![-1, 0]` against the reflected coefficient `(1 - 1) • ![0,1] = 0`. -/
theorem nf_transition_transfer_hd_fence :
    ¬ (walkTransitionMatrix nfNegEdge *ᵥ (degreeInvSqrt nfNegEdge *ᵥ ![0, 1])
      = (1 - 1 : ℝ) • (degreeInvSqrt nfNegEdge *ᵥ ![0, 1])) := by
  intro h
  rw [nfNegEdge_dis_mulVec, nfNegEdge_P_mulVec] at h
  have e0 := congrFun h 0
  simp only [Matrix.cons_val_zero, Matrix.head_cons, smul_eq_mul,
    mul_zero, sub_self, sub_zero] at e0
  norm_num at e0

/-- **C9 — the transition transfer's `h` clause is load-bearing.** On
`K₂`, the non-eigenvector `v = e₀` at `μ = 0`: `P *ᵥ e₀ = ![0,1] ≠
![1,0] = (1 - 0) • e₀`. -/
theorem nf_transition_transfer_h_fence :
    ¬ (walkTransitionMatrix edgeAdj2 *ᵥ (degreeInvSqrt edgeAdj2 *ᵥ ![1, 0])
      = (1 - 0 : ℝ) • (degreeInvSqrt edgeAdj2 *ᵥ ![1, 0])) := by
  intro h
  rw [edgeAdj2_dis_mulVec, edgeAdj2_P_mulVec] at h
  have e0 := congrFun h 0
  simp only [Matrix.cons_val_zero, Matrix.head_cons, smul_eq_mul,
    mul_one, sub_zero] at e0
  norm_num at e0

/-- C5/C7/C9 isolation: `hd` is genuine on `K₂` (degrees `1`). -/
theorem nf_transfer_h_isolation :
    ∀ i, 0 < deg edgeAdj2 i := nf_dis_mulVec_ne_zero_hv_isolation

/-!
## The D section: the eigenbasis layer

The `hA` clauses here are signature-entangled (the displays carry
`eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA)`
and `walkEvals A hA`); the `hd` clauses are fenced below.
-/

/-- The `L_sym` symmetry proof for the negative-degree fixture's
eigenbasis displays. -/
theorem nfLsym : (normalizedLaplacian nfNegEdge).IsSymm :=
  normalizedLaplacian_symmetric nfNegEdge nfNegEdge_isSymm

/-- Some eigenbasis vector of the degenerate identity `L_sym` has a
nonvanishing second coordinate — otherwise both basis vectors would be
multiples of `e₀` and could not be orthonormal (`eigvecOf_inner`). -/
theorem nf_basis_second :
    ∃ i : Fin 2, eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i 1 ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have h00 : ∑ k, eigvecOf (normalizedLaplacian nfNegEdge) nfLsym 0 k
      * eigvecOf (normalizedLaplacian nfNegEdge) nfLsym 0 k = 1 := by
    simpa using eigvecOf_inner _ nfLsym 0 0
  have h11 : ∑ k, eigvecOf (normalizedLaplacian nfNegEdge) nfLsym 1 k
      * eigvecOf (normalizedLaplacian nfNegEdge) nfLsym 1 k = 1 := by
    simpa using eigvecOf_inner _ nfLsym 1 1
  have h01 : ∑ k, eigvecOf (normalizedLaplacian nfNegEdge) nfLsym 0 k
      * eigvecOf (normalizedLaplacian nfNegEdge) nfLsym 1 k = 0 := by
    simpa using eigvecOf_inner _ nfLsym 0 1
  simp only [Fin.sum_univ_two, hcon 0, hcon 1, mul_zero, add_zero] at h00 h11 h01
  have a0 : eigvecOf (normalizedLaplacian nfNegEdge) nfLsym 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at h00
    norm_num at h00
  have b0 : eigvecOf (normalizedLaplacian nfNegEdge) nfLsym 1 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at h11
    norm_num at h11
  rcases mul_eq_zero.1 h01 with h' | h'
  · exact a0 h'
  · exact b0 h'

/-- **D1 — `walkLaplacian_mulVec_eigvecOf`'s `hd` clause is
load-bearing.** At the witness index `i` of `nf_basis_second`: the
conjugated eigenvector is `![0, u 1]` with `u 1 ≠ 0`, and
`L_walk *ᵥ ![0, u 1] = ![u 1, u 1]` — its zeroth coordinate `u 1 ≠ 0`
while the eigenvalue-scaled right side's zeroth coordinate is
`λ · 0 = 0`. No eigenvalue pin is needed. -/
theorem nf_wl_eigvecOf_hd_fence :
    ∃ i : Fin 2, ¬ (walkLaplacian nfNegEdge *ᵥ
        (degreeInvSqrt nfNegEdge *ᵥ
          eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i)
      = eigvalOf (normalizedLaplacian nfNegEdge) nfLsym i •
        (degreeInvSqrt nfNegEdge *ᵥ
          eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i)) := by
  obtain ⟨i, hi⟩ := nf_basis_second
  refine ⟨i, ?_⟩
  intro hcon
  rw [nfNegEdge_dis_mulVec, nfNegEdge_walkLap_mulVec] at hcon
  have e0 := congrFun hcon 0
  simp only [Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul, mul_zero,
    sub_zero] at e0
  have hzero : eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i 1 = 0 := by
    linarith
  exact hi hzero

/-- **D2 — `walkTransitionMatrix_mulVec_eigvecOf`'s `hd` clause is
load-bearing.** Same witness: `P *ᵥ ![0, u 1] = ![2·0 - u 1, 0]` — its
zeroth coordinate is `-u 1 ≠ 0` against the right side's
`(1 - λ) · 0 = 0`. -/
theorem nf_wt_eigvecOf_hd_fence :
    ∃ i : Fin 2, ¬ (walkTransitionMatrix nfNegEdge *ᵥ
        (degreeInvSqrt nfNegEdge *ᵥ
          eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i)
      = (1 - eigvalOf (normalizedLaplacian nfNegEdge) nfLsym i) •
        (degreeInvSqrt nfNegEdge *ᵥ
          eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i)) := by
  obtain ⟨i, hi⟩ := nf_basis_second
  refine ⟨i, ?_⟩
  intro hcon
  rw [nfNegEdge_dis_mulVec, nfNegEdge_P_mulVec] at hcon
  have e0 := congrFun hcon 0
  simp only [Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul, mul_zero, sub_mul,
    one_mul, zero_sub, neg_eq_zero] at e0
  have hzero : eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i 1 = 0 := by
    linarith
  exact hi hzero

/-- **D3 — `walk_eigvec_expansion`'s `hd` clause is load-bearing.** At
`w = e₀`: the coefficient vector is `√D *ᵥ e₀ = ![√(-1) · 1, √1 · 0] =
0`, so every coefficient is `u i ⬝ᵥ 0 = 0` and the whole expansion
collapses to `0 ≠ e₀`. -/
theorem nf_expansion_hd_fence :
    ¬ (∑ i, Matrix.dotProduct
        (eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i)
        (degreeSqrt nfNegEdge *ᵥ ![1, 0])
      • (degreeInvSqrt nfNegEdge *ᵥ
          eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i)
      = (![1, 0] : Fin 2 → ℝ)) := by
  intro h
  have hz : degreeSqrt nfNegEdge *ᵥ ![1, 0] = 0 := by
    rw [nfNegEdge_ds_mulVec]
    funext i
    rcases nfFin2_cases i with rfl | rfl <;>
      simp only [Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.cons_val_one, Pi.zero_apply]
  have hsum : (∑ i, Matrix.dotProduct
      (eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i)
      (degreeSqrt nfNegEdge *ᵥ ![1, 0])
    • (degreeInvSqrt nfNegEdge *ᵥ
        eigvecOf (normalizedLaplacian nfNegEdge) nfLsym i)) = 0 := by
    rw [hz]
    exact Finset.sum_eq_zero fun i _ => by
      rw [Matrix.dotProduct_zero, zero_smul]
  rw [hsum] at h
  have e0 := congrFun h 0
  simp at e0

theorem nfNegEdge_walkEvals_zero (k : Fin (Fintype.card (Fin 2))) :
    walkEvals nfNegEdge nfNegEdge_isSymm k = 0 := by
  simp only [walkEvals]
  have h1 : evals (normalizedLaplacian_symmetric nfNegEdge nfNegEdge_isSymm) k
      = 1 := by
    rw [evals_congr
      (normalizedLaplacian_symmetric nfNegEdge nfNegEdge_isSymm)
      (show (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm by
        simp [Matrix.IsSymm])
      nfNegEdge_Lsym]
    exact evals_one _ k
  rw [h1]
  norm_num

/-- **D4 — `exists_eigenvector_walkTransitionMatrix_eq_walkEvals`'s
`hd` clause is load-bearing.** The transferred spectrum is
`walkEvals = 1 - 1 = 0` (the `L_sym` side is the identity, transported
by `evals_congr` through `evals_one`), so the claim reads `∃ w ≠ 0, P *ᵥ w = 0`
— refuted by the row equations of the pinned `P` (`2 w₀ = w₁`,
`w₀ = 0`). -/
theorem nf_exists_walkEvals_hd_fence :
    ¬ (∃ w : Fin 2 → ℝ, w ≠ 0 ∧
        walkTransitionMatrix nfNegEdge *ᵥ w
          = walkEvals nfNegEdge nfNegEdge_isSymm ⟨0, by simp⟩ • w) := by
  rintro ⟨w, hw0, hw⟩
  rw [nfNegEdge_walkEvals_zero ⟨0, by simp⟩] at hw
  simp only [sub_self, zero_smul] at hw
  rw [nfNegEdge_P_mulVec] at hw
  have e1 := congrFun hw 1
  have e0 := congrFun hw 0
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
    Pi.zero_apply] at e1 e0
  have hw0' : w 0 = 0 := e1
  have hw1' : w 1 = 0 := by
    rw [hw0'] at e0
    linarith
  apply hw0
  funext i
  rcases nfFin2_cases i with rfl | rfl
  · exact hw0'
  · exact hw1'

/-- D-layer isolation: the kept `hA` is genuine (the fixture is
symmetric) — packaged with `nf_transfer_hd_isolation`. -/
theorem nf_eigbasis_hA_isolation : nfNegEdge.IsSymm := nfNegEdge_isSymm

/-!
## The E section: the power layer
-/

/-- **E1 — the commutation form's `hd` clause is load-bearing.** At
entry `(1, 0)`: the left side is `√1 · P 1 0 = 1`, while the right side
carries the zero column factor `√(deg 0) = 0` and an identically-zero
`1 - L_sym`. -/
theorem nf_commutation_hd_fence :
    ¬ (degreeSqrt nfNegEdge * walkTransitionMatrix nfNegEdge
      = (1 - normalizedLaplacian nfNegEdge) * degreeSqrt nfNegEdge) := by
  intro h
  rw [nfNegEdge_Lsym, sub_self, Matrix.zero_mul,
    nfNegEdge_degreeSqrt, nfNegEdge_P] at h
  have e10 := congrFun (congrFun h 1) 0
  simp only [Matrix.diagonal_mul, Matrix.diagonal_apply,
    if_neg (by decide : ¬(1 : Fin 2) = 0), Matrix.of_apply, Fin.isValue,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.zero_apply, zero_mul] at e10
  norm_num at e10

/-- **E2 — the conjugated-power transfer's `hd` clause is
load-bearing.** At `t = 1`, `g = e₀`: the left side is
`√D *ᵥ (P *ᵥ e₀) = √D *ᵥ ![2, 1] = ![0, 1]`, while the right side acts
by the zero matrix `1 - L_sym`. -/
theorem nf_power_transfer_hd_fence :
    ¬ (degreeSqrt nfNegEdge *ᵥ ((walkTransitionMatrix nfNegEdge ^ 1) *ᵥ ![1, 0])
      = ((1 - normalizedLaplacian nfNegEdge) ^ 1) *ᵥ
        (degreeSqrt nfNegEdge *ᵥ ![1, 0])) := by
  intro h
  rw [pow_one, pow_one, nfNegEdge_Lsym, sub_self, Matrix.zero_mulVec,
    nfNegEdge_P_mulVec, nfNegEdge_ds_mulVec] at h
  have e1 := congrFun h 1
  simp only [Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_zero, Pi.zero_apply] at e1
  norm_num at e1

/-!
## The eigenbasis-transfer pins (`proposals/band-normalized-pairs-pins.md`)

The first genuine consumption of the two opaque-`eigvecOf` transfer
theorems (`walkLaplacian_mulVec_eigvecOf`, `walk_eigvec_expansion`).
Mathlib's `eigenvalues`/`eigenvectorBasis` are built from the direct sum
of eigenspaces with no sorting guarantee (an explicit upstream TODO), so
neither the eigenvalue at an index nor the eigenvector's sign is
syntactically resolvable. Two instruments resolve this without unfolding:

- the **eigenvalue-witness bridge** (`eigvalOf_of_eigenpair`): a hand
  eigenpair locates an *index* carrying its eigenvalue —
  `dotProduct_eigvecOf_mulVec` moves the symmetric operator across the
  dot product, the eigenvalue-mismatch factor kills every expansion
  coefficient, and `eigvecOf_expansion_apply` collapses the vector;
- **sign-robust forms**: facts homogeneous in the eigenvector (the
  eigen-equation itself, entry antisymmetry) or quadratic per mode (the
  expansion's aggregate join), for which the unresolved sign cancels.

The mode-`1` eigenspace at the path is one-dimensional along
`(1, 0, -1)` (two row equations), so the transferred walk eigenvector
is `c • (1, 0, -1)` at an unknown nonzero `c` — its antisymmetry and
eigen-equation are `c`-robust. The expansion pin evaluates the
transferred expansion's quadratic aggregate at the degree-`2` center,
where the value `(√2)⁻¹ = 1/√(deg 1)` carries the graph's genuine
irregularity, through two independent engines.
-/

/-- **The eigenvalue-witness bridge.** Every eigenvector of a symmetric
matrix (with any eigenvalue, hand-supplied) matches some spectral-theorem
basis index's eigenvalue: if no `eigvalOf` equaled `μ`, then every
expansion coefficient `vᵢ ⬝ᵥ x` would vanish
(`dotProduct_eigvecOf_mulVec` moves `M` across the dot product and the
mismatch factor kills the coefficient), forcing `x = 0` by
`eigvecOf_expansion_apply`. This is the sign-free instrument that
instantiates the opaque-basis transfer theorems at hand eigenpairs. -/
theorem eigvalOf_of_eigenpair {V : Type} [Fintype V] [DecidableEq V]
    {M : Matrix V V ℝ} (hM : M.IsSymm) {x : V → ℝ} (hx : x ≠ 0)
    {μ : ℝ} (h : M *ᵥ x = μ • x) :
    ∃ i : V, eigvalOf M hM i = μ := by
  by_contra hcon
  push_neg at hcon
  apply hx
  funext a
  have hzero : ∀ i, Matrix.dotProduct (eigvecOf M hM i) x = 0 := by
    intro i
    have h1 : Matrix.dotProduct (eigvecOf M hM i) (M *ᵥ x)
        = μ * Matrix.dotProduct (eigvecOf M hM i) x := by
      rw [h, Matrix.dotProduct_smul, smul_eq_mul]
    rw [dotProduct_eigvecOf_mulVec hM i x] at h1
    have h2 : (eigvalOf M hM i - μ)
        * Matrix.dotProduct (eigvecOf M hM i) x = 0 := by
      rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.1 h2 with h' | h'
    · exact absurd (eq_of_sub_eq_zero h') (hcon i)
    · exact h'
  have hexp := eigvecOf_expansion_apply hM x a
  simp only [hzero, zero_mul, Finset.sum_const_zero, Pi.zero_apply] at hexp
  exact hexp.symm

/-- The hand mode-`1` eigenvector is nonzero (entry read). -/
theorem path_eigvec_one_hand_ne_zero : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have e := congrFun h 0
  simp at e

/-- Normalized-Laplacian corner diagonal entry: `(L_sym) 0 0 = 1` (no
self-loops, degree-`1` vertex) — completing the entry pins the
eigenspace row-solve needs. -/
theorem path_normalizedLaplacian_00_QA :
    normalizedLaplacian pathAdj 0 0 = 1 := by
  have hp00 : pathAdj 0 0 = 0 := by norm_num [pathAdj]
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    degreeInvSqrt, Real.sqrt_one, inv_one, one_mul, zero_sub,
    pathAdj_deg_zero]
  rw [hp00]
  norm_num

/-- Normalized-Laplacian second off-diagonal: `(L_sym) 1 2 = -1/√2` —
the degree-`(2, 1)` edge scaled by `1/√(2·1)`. -/
theorem path_normalizedLaplacian_12_QA :
    normalizedLaplacian pathAdj 1 2 = -(Real.sqrt 2)⁻¹ := by
  have hp12 : pathAdj 1 2 = 1 := by norm_num [pathAdj]
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    degreeInvSqrt, Real.sqrt_one, inv_one, one_mul, zero_sub,
    pathAdj_deg_one, pathAdj_deg_two]
  rw [hp12]
  have hne : ¬(1 : ℕ) = 2 := by decide
  simp [hne]

/-- **The mode-`1` eigenspace shape at the opaque basis**: an
eigenvalue-`1` basis vector has middle entry `0` and antisymmetric
ends (`v 2 = -v 0`), by the two row equations of
`L_sym - 1` — the sign (and scale) of the basis vector stays
unresolved, exactly the degree of freedom the transfer pins below never
consume. -/
theorem path_eigvecOf_one_shape {i : Fin 3}
    (hi : eigvalOf (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i = 1) :
    eigvecOf (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1 = 0 ∧
      eigvecOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 2
        = -eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 0 := by
  have hev : normalizedLaplacian pathAdj *ᵥ
      eigvecOf (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i
      = eigvalOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i •
          eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i :=
    (isHermitian_of_isSymm
      (normalizedLaplacian_symmetric pathAdj
        pathAdj_isSymm)).mulVec_eigenvectorBasis i
  rw [hi] at hev
  have e0 := congrFun hev 0
  have e1 := congrFun hev 1
  have h10 : normalizedLaplacian pathAdj 1 0 = -(Real.sqrt 2)⁻¹ := by
    rw [show normalizedLaplacian pathAdj 1 0
        = normalizedLaplacian pathAdj 0 1 from
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm).apply 0 1,
      path_normalizedLaplacian_offdiag_QA]
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
    Pi.smul_apply, smul_eq_mul, mul_one,
    path_normalizedLaplacian_00_QA,
    path_normalizedLaplacian_offdiag_QA,
    path_normalizedLaplacian_far_QA] at e0
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
    Pi.smul_apply, smul_eq_mul, mul_one,
    path_normalizedLaplacian_diag_QA, h10,
    path_normalizedLaplacian_12_QA] at e1
  have hin : ((Real.sqrt 2 : ℝ)⁻¹)
      * eigvecOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1 = 0 := by
    have hpos : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [e0]
  have hv1 : eigvecOf (normalizedLaplacian pathAdj)
      (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1 = 0 := by
    rcases mul_eq_zero.1 hin with h' | h'
    · exact absurd h' (inv_ne_zero
        (Real.sqrt_ne_zero'.mpr (by norm_num)))
    · exact h'
  refine ⟨hv1, ?_⟩
  have hsum : ((Real.sqrt 2 : ℝ)⁻¹)
      * (eigvecOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 0
        + eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 2) = 0 := by
    nlinarith [e1, hv1]
  have hkey : eigvecOf (normalizedLaplacian pathAdj)
      (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 0
      + eigvecOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 2 = 0 := by
    rcases mul_eq_zero.1 hsum with h' | h'
    · exact absurd h' (inv_ne_zero
        (Real.sqrt_ne_zero'.mpr (by norm_num)))
    · exact h'
  linarith

/-- **The eigenbasis transfer consumed, eigen-equation form**: the
bridge locates the eigenvalue-`1` index from the hand eigenpair
`path_Lsym_eigen_one_QA`, and `walkLaplacian_mulVec_eigvecOf` transfers
that basis vector to a fixed point of the walk Laplacian — the
opaque-index instantiation of the forward transfer at eigenvalue `1`. -/
theorem path_walkLaplacian_eigvecOf_transfer_pin :
    ∃ i : Fin 3,
      eigvalOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i = 1 ∧
      walkLaplacian pathAdj *ᵥ (degreeInvSqrt pathAdj *ᵥ
          eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
        = degreeInvSqrt pathAdj *ᵥ
            eigvecOf (normalizedLaplacian pathAdj)
              (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i := by
  obtain ⟨i, hi⟩ := eigvalOf_of_eigenpair
    (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
    path_eigvec_one_hand_ne_zero path_Lsym_eigen_one_QA
  refine ⟨i, hi, ?_⟩
  have h := walkLaplacian_mulVec_eigvecOf pathAdj pathAdj_isSymm
    pathAdj_deg_pos i
  rwa [hi, one_smul] at h

/-- **The same transfer in sign-robust entry form**: the transferred
walk eigenvector has middle entry `0`, antisymmetric ends, and is
nonzero — properties invariant under the unresolved sign/scale of the
basis vector (the eigenspace shape composed with the degree
conjugation; the endpoints have degree `1`, so only the middle entry
scales). A wrong conjugation or a wrong eigenvalue would break the
antisymmetry or the nonvanishing. -/
theorem path_walkLaplacian_eigvecOf_transfer_shape :
    ∃ i : Fin 3,
      eigvalOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i = 1 ∧
      (degreeInvSqrt pathAdj *ᵥ
          eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) 1 = 0 ∧
      (degreeInvSqrt pathAdj *ᵥ
          eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) 0
        = -((degreeInvSqrt pathAdj *ᵥ
              eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) 2) ∧
      (degreeInvSqrt pathAdj *ᵥ
          eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) ≠ 0 := by
  obtain ⟨i, hi⟩ := eigvalOf_of_eigenpair
    (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
    path_eigvec_one_hand_ne_zero path_Lsym_eigen_one_QA
  obtain ⟨hv1, hv2⟩ := path_eigvecOf_one_shape hi
  have w0 : (degreeInvSqrt pathAdj *ᵥ
      eigvecOf (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) 0
      = eigvecOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 0 := by
    rw [degreeInvSqrt_mulVec_apply, pathAdj_deg_zero, Real.sqrt_one,
      inv_one, one_mul]
  have w1 : (degreeInvSqrt pathAdj *ᵥ
      eigvecOf (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) 1 = 0 := by
    rw [degreeInvSqrt_mulVec_apply, pathAdj_deg_one, hv1]
    simp
  have w2 : (degreeInvSqrt pathAdj *ᵥ
      eigvecOf (normalizedLaplacian pathAdj)
        (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) 2
      = eigvecOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 2 := by
    rw [degreeInvSqrt_mulVec_apply, pathAdj_deg_two, Real.sqrt_one,
      inv_one, one_mul]
  exact ⟨i, hi, w1, by rw [w0, w2, hv2, neg_neg],
    degreeInvSqrt_mulVec_ne_zero pathAdj pathAdj_deg_pos
      (eigvecOf_ne_zero _ _ i)⟩

/-- Raw route: the hand eigenpair `(1, 0, -1)` is a walk-Laplacian fixed
point by direct row arithmetic on `P = D⁻¹A` (the delivered
`path_walkTransition_middle_raw_QA` annihilates it under `P`, and
`L_walk = 1 - P`) — the numeric companion of the transfer pin, no
eigenbasis involved. -/
theorem path_walkLaplacian_one_mode_raw :
    walkLaplacian pathAdj *ᵥ (![1, 0, -1] : Fin 3 → ℝ)
      = (![1, 0, -1] : Fin 3 → ℝ) := by
  rw [walkLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    path_walkTransition_middle_raw_QA, sub_zero]

/-- The degree-square-root action at the center vertex:
`√D *ᵥ e₁ = √2 • e₁` (the degree-`2` center). -/
theorem path_degreeSqrt_mulVec_center :
    degreeSqrt pathAdj *ᵥ (![0, 1, 0] : Fin 3 → ℝ)
      = ![0, Real.sqrt 2, 0] := by
  funext i
  rcases nfFin3_cases i with rfl | rfl | rfl
  · rw [degreeSqrt_mulVec_apply, pathAdj_deg_zero, Real.sqrt_one]
    simp
  · rw [degreeSqrt_mulVec_apply, pathAdj_deg_one]
    simp
  · rw [degreeSqrt_mulVec_apply, pathAdj_deg_two, Real.sqrt_one]
    simp

/-- The reciprocal action at the center vertex:
`(1/√D) *ᵥ e₁ = (1/√2) • e₁`. -/
theorem path_degreeInvSqrt_mulVec_center :
    degreeInvSqrt pathAdj *ᵥ (![0, 1, 0] : Fin 3 → ℝ)
      = ![0, (Real.sqrt 2)⁻¹, 0] := by
  funext i
  rcases nfFin3_cases i with rfl | rfl | rfl
  · rw [degreeInvSqrt_mulVec_apply, pathAdj_deg_zero, Real.sqrt_one]
    simp
  · rw [degreeInvSqrt_mulVec_apply, pathAdj_deg_one]
    simp
  · rw [degreeInvSqrt_mulVec_apply, pathAdj_deg_two, Real.sqrt_one]
    simp

/-- **Column completeness at the center**: the basis vectors' center
entries square-sum to one — `eigvecOf_expansion_apply` at `e₁` read at
entry `1` (the unconjugated expansion engine, consumed here as the
independent route of the transferred-expansion join). -/
theorem path_eigvecOf_column_norm :
    ∑ i, eigvecOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1
        * eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1
      = 1 := by
  have hexp := eigvecOf_expansion_apply
    (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm)
    (![0, 1, 0] : Fin 3 → ℝ) 1
  simpa [Matrix.dotProduct, Fin.sum_univ_three] using hexp

/-- **The transferred expansion consumed, aggregate-quadratic form.**
Dotting the transferred expansion of `e₁`
(`walk_eigvec_expansion`) with the conjugated test vector
`(1/√D) *ᵥ e₁ = ![0, 1/√2, 0]` evaluates the whole quadratic sum
through the theorem: the value is `1/√2 = 1/√(deg 1)`, carrying the
graph's genuine irregularity (on a regular graph it would be `1`). Each
summand is quadratic in its basis vector, so the unresolved signs
cancel — no identification of the basis is needed. -/
theorem path_walk_eigvec_expansion_center_join :
    (∑ i, Matrix.dotProduct
          (eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
          (degreeSqrt pathAdj *ᵥ (![0, 1, 0] : Fin 3 → ℝ))
        * Matrix.dotProduct
            (degreeInvSqrt pathAdj *ᵥ
              eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
            (![0, (Real.sqrt 2)⁻¹, 0] : Fin 3 → ℝ))
      = (Real.sqrt 2)⁻¹ := by
  have hexp := walk_eigvec_expansion pathAdj pathAdj_isSymm
    pathAdj_deg_pos (![0, 1, 0] : Fin 3 → ℝ)
  have hsplit : ∀ (c : Fin 3 → ℝ) (y : Fin 3 → (Fin 3 → ℝ))
      (u : Fin 3 → ℝ),
      (∑ i, c i • y i) ⬝ᵥ u = ∑ i, c i * (y i ⬝ᵥ u) := by
    intro c y u
    simp only [Matrix.dotProduct, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    calc ∑ a, (∑ i, c i * y i a) * u a
        = ∑ a, ∑ i, (c i * y i a) * u a := by
          exact Finset.sum_congr rfl fun a _ => Finset.sum_mul _ _ _
      _ = ∑ i, ∑ a, (c i * y i a) * u a := Finset.sum_comm
      _ = ∑ i, c i * ∑ a, y i a * u a := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun a _ => by ring
  have hdot := congrArg
    (fun s => Matrix.dotProduct s (![0, (Real.sqrt 2)⁻¹, 0] : Fin 3 → ℝ)) hexp
  simp only [hsplit] at hdot
  have hval : Matrix.dotProduct (![0, 1, 0] : Fin 3 → ℝ)
      (![0, (Real.sqrt 2)⁻¹, 0] : Fin 3 → ℝ) = (Real.sqrt 2)⁻¹ := by
    simp [Matrix.dotProduct, Fin.sum_univ_three]
  rw [hval] at hdot
  exact hdot

/-- The same value through the independent engine: each summand
rewrites by the pinned diagonal actions (`√2` and `1/√2` at the
center) to `(1/√2) · (vᵢ 1)²`, and the column-completeness pin sums the
squares to one — no transferred-expansion theorem involved. Two routes,
one value. -/
theorem path_walk_eigvec_expansion_center_join_raw :
    (∑ i, Matrix.dotProduct
          (eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
          (degreeSqrt pathAdj *ᵥ (![0, 1, 0] : Fin 3 → ℝ))
        * Matrix.dotProduct
            (degreeInvSqrt pathAdj *ᵥ
              eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
            (![0, (Real.sqrt 2)⁻¹, 0] : Fin 3 → ℝ))
      = (Real.sqrt 2)⁻¹ := by
  have hin : (Real.sqrt 2 : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hc : ∀ i : Fin 3,
      Matrix.dotProduct
          (eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
          (degreeSqrt pathAdj *ᵥ (![0, 1, 0] : Fin 3 → ℝ))
        = Real.sqrt 2 * eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1 := by
    intro i
    rw [path_degreeSqrt_mulVec_center]
    simp only [Matrix.dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, mul_zero, zero_add, add_zero,
      mul_one]
    ring
  have hwapp : ∀ i : Fin 3,
      (degreeInvSqrt pathAdj *ᵥ
          eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i) 1
        = (Real.sqrt 2)⁻¹ * eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1 := by
    intro i
    rw [degreeInvSqrt_mulVec_apply, pathAdj_deg_one]
  have hw : ∀ i : Fin 3,
      Matrix.dotProduct
          (degreeInvSqrt pathAdj *ᵥ
            eigvecOf (normalizedLaplacian pathAdj)
              (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
          (![0, (Real.sqrt 2)⁻¹, 0] : Fin 3 → ℝ)
        = (Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹
            * eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1) := by
    intro i
    simp only [Matrix.dotProduct, Fin.sum_univ_three, hwapp i,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.tail_cons, mul_zero, zero_add, add_zero]
    ring
  have hterm : ∀ i : Fin 3,
      (Real.sqrt 2 * eigvecOf (normalizedLaplacian pathAdj)
          (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1)
        * ((Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹
            * eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1))
      = (Real.sqrt 2)⁻¹ * (eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1
          * eigvecOf (normalizedLaplacian pathAdj)
              (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1) := by
    intro i
    have key : (Real.sqrt 2 : ℝ) * (Real.sqrt 2)⁻¹ = 1 :=
      mul_inv_cancel₀ hin
    calc (Real.sqrt 2 * eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1)
        * ((Real.sqrt 2)⁻¹ * ((Real.sqrt 2)⁻¹
            * eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1))
        = ((Real.sqrt 2 : ℝ) * (Real.sqrt 2)⁻¹)
            * ((Real.sqrt 2)⁻¹
              * (eigvecOf (normalizedLaplacian pathAdj)
                  (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1
                * eigvecOf (normalizedLaplacian pathAdj)
                    (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1)) := by
          ring
      _ = (Real.sqrt 2)⁻¹ * (eigvecOf (normalizedLaplacian pathAdj)
              (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1
            * eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1) := by
          rw [key, one_mul]
  have hsum : (∑ i : Fin 3, (Real.sqrt 2)⁻¹
      * (eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1
          * eigvecOf (normalizedLaplacian pathAdj)
              (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1))
      = (Real.sqrt 2)⁻¹ := by
    rw [← Finset.mul_sum, path_eigvecOf_column_norm, mul_one]
  calc (∑ i : Fin 3, Matrix.dotProduct
          (eigvecOf (normalizedLaplacian pathAdj)
            (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
          (degreeSqrt pathAdj *ᵥ (![0, 1, 0] : Fin 3 → ℝ))
        * Matrix.dotProduct
            (degreeInvSqrt pathAdj *ᵥ
              eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i)
            (![0, (Real.sqrt 2)⁻¹, 0] : Fin 3 → ℝ))
      = ∑ i : Fin 3, (Real.sqrt 2)⁻¹
          * (eigvecOf (normalizedLaplacian pathAdj)
                (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1
              * eigvecOf (normalizedLaplacian pathAdj)
                  (normalizedLaplacian_symmetric pathAdj pathAdj_isSymm) i 1) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hc i, hw i]
        exact hterm i
    _ = (Real.sqrt 2)⁻¹ := hsum

end SpectralGraphTheory.QA
