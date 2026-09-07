/-
  RandomWalk_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.RandomWalk`: the transition
  matrix and walk Laplacian interfaces, instantiated at a concrete
  two-vertex graph (the edge `0 — 1`) where every quantity computes.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces at a point where the
  arithmetic is fully evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.RandomWalk

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## A concrete two-vertex graph: the single edge `0 — 1`
-/

/-- The adjacency matrix of the single edge on `Fin 2` (symmetric,
1-regular, nonnegative). -/
def rwEdgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem rwEdgeAdj_isSymm : rwEdgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [rwEdgeAdj]

theorem rwEdgeAdj_deg (i : Fin 2) : deg rwEdgeAdj i = 1 := by
  fin_cases i <;>
    simp only [deg, rwEdgeAdj, Matrix.of_apply, Fin.sum_univ_two] <;>
    simp

/-- Row-stochasticity computes at the edge: both rows of the transition
  matrix are the distribution placing all mass on the neighbor. -/
theorem edge_row_sum_QA (i : Fin 2) :
    ∑ j, transitionMatrix rwEdgeAdj 1 i j = 1 :=
  transitionMatrix_row_sum rwEdgeAdj 1 rwEdgeAdj_deg one_pos i

/-- The transition matrix of the edge computes entrywise: it is the
  anti-diagonal (swapping) matrix. -/
theorem edge_transitionMatrix_entries_QA :
    transitionMatrix rwEdgeAdj 1
      = Matrix.of fun (i j : Fin 2) => if i = j then 0 else 1 := by
  simp only [transitionMatrix, inv_one, one_smul, rwEdgeAdj]

/-- The scaling bridge computes at the edge: the walk Laplacian is the
  combinatorial Laplacian itself (degree `d = 1`). -/
theorem edge_randomWalkLaplacian_eq_laplacian_QA :
    randomWalkLaplacian rwEdgeAdj 1 = laplacian rwEdgeAdj := by
  rw [randomWalkLaplacian_eq_smul_laplacian rwEdgeAdj 1 rwEdgeAdj_deg one_pos,
    inv_one, one_smul]

/-- Interop with the Cheeger bridge computes at the edge: the walk
  Laplacian is the normalized Laplacian used by the Cheeger axioms. -/
theorem edge_randomWalkLaplacian_eq_normalized_QA :
    randomWalkLaplacian rwEdgeAdj 1 = regularNormalizedLaplacian rwEdgeAdj 1 :=
  randomWalkLaplacian_eq_regularNormalizedLaplacian rwEdgeAdj 1

/-- The combinatorial Laplacian of the edge computes: it is `1 - A`, the
  standard two-vertex Laplacian with eigenvalues `0` and `2`. -/
theorem edge_laplacian_entries_QA :
    laplacian rwEdgeAdj
      = Matrix.of fun (i j : Fin 2) => if i = j then 1 else -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, rwEdgeAdj, deg]

/-! ### AdversarialFences: the adversarial fence audit
(`proposals/adversarial-fences-random-walk-family.md`, 2026-09-05)

The audit method's nineteenth application: a hypothesis-necessity pass
over the random-walk family — 5 transitive non-QA consumers via
`Stationary` (this run's reverse-import walk), whose 76-line QA was
fully pre-discipline (one nonnegative fixture, zero negative
witnesses). Six hypothesis-form fences; the shelf is all-proved, so
these are theorem-instantiation fences (no `-- @refutes` tags, nothing
admitted consumed):

- **`hA`** (both symmetry statements) at `rwAsymAdj = !![0, 2; 1, 0]]`,
  killed at `d = 1` where `1⁻¹ • A = A` (`2 ≠ 1` resp. `-2 ≠ -1`); the
  `d = 0` junk-rescue corner pinned alongside (the scalar `0⁻¹ = 0`
  symmetrizes every matrix, so the dropped statements fail exactly
  when `d ≠ 0` ∧ asymmetric).
- **`hd`** (row-stochasticity and the scaling bridge) at the delivered
  `rwEdgeAdj` with the wrong claimed degree `d = 2` — row sum `1/2 ≠ 1`
  and a `2×` diagonal separation `1 ≠ 1/2`, no junk anywhere.
- **`hdpos`** (row-stochasticity and the scaling bridge) at
  `rwZeroAdj = 0`, genuinely `0`-regular: the junk `0⁻¹ = 0` corner
  where the transition matrix collapses to the zero matrix (row sum
  `0 ≠ 1`; the bridge's sides separate `1 ≠ 0`). Pricing finding: this
  is the *only* failure corner — at every genuinely `d`-regular
  fixture with `d ≠ 0` (negative degrees included) both dropped
  statements are true by `d⁻¹ * d = 1`, recorded by the proved
  strengthening companions `_of_ne_zero`.

Non-fenceable: `randomWalkLaplacian_eq_regularNormalizedLaplacian`
carries no mathematical hypotheses at all (it is the `rfl` identity of
the two normalizations) — nothing to drop. -/

section AdversarialFences

/-! #### Fixture 1: `rwAsymAdj = !![0, 2; 1, 0]]` — the `hA` breaker -/

/-- The `hA` breaker: asymmetric with both off-diagonal entries
nonzero, killed at `d = 1` where the transition matrix is the adjacency
itself. -/
def rwAsymAdj : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 1, 0]

theorem rwAsymAdj_00 : rwAsymAdj 0 0 = 0 := rfl
theorem rwAsymAdj_01 : rwAsymAdj 0 1 = 2 := rfl
theorem rwAsymAdj_10 : rwAsymAdj 1 0 = 1 := rfl
theorem rwAsymAdj_11 : rwAsymAdj 1 1 = 0 := rfl

/-- Isolation: the dropped clause genuinely fails (`2 ≠ 1`). -/
theorem rwAsymAdj_not_isSymm : ¬ rwAsymAdj.IsSymm := fun h =>
  absurd (h.apply 0 1) (by rw [rwAsymAdj_10, rwAsymAdj_01]; norm_num)

/-- Normalization pin: at `d = 1` the transition matrix is the
adjacency matrix itself. -/
theorem rwAsymAdj_transitionMatrix_one_apply (i j : Fin 2) :
    transitionMatrix rwAsymAdj 1 i j = rwAsymAdj i j := by
  simp only [transitionMatrix, Matrix.smul_apply, smul_eq_mul, inv_one,
    one_mul]

theorem rwAsymAdj_transitionMatrix_one_01 :
    transitionMatrix rwAsymAdj 1 0 1 = 2 := by
  rw [rwAsymAdj_transitionMatrix_one_apply, rwAsymAdj_01]

theorem rwAsymAdj_transitionMatrix_one_10 :
    transitionMatrix rwAsymAdj 1 1 0 = 1 := by
  rw [rwAsymAdj_transitionMatrix_one_apply, rwAsymAdj_10]

/-- **Fence (`hA` clause of `transitionMatrix_symmetric`).** Dropping
symmetry is refuted at `rwAsymAdj`, `d = 1`: the transition matrix is
the adjacency itself and `(0,1) = 2 ≠ 1 = (1,0)`. -/
theorem transitionMatrix_symmetric_hA_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ),
        (transitionMatrix A d).IsSymm) := by
  intro h
  have h1 := h rwAsymAdj 1
  have h01 := h1.apply 0 1
  rw [rwAsymAdj_transitionMatrix_one_10, rwAsymAdj_transitionMatrix_one_01]
    at h01
  norm_num at h01

/-- **Fence (`hA` clause of `randomWalkLaplacian_symmetric`).** Same
fixture, different conclusion: `L_rw = 1 - P` inherits the asymmetry
through the subtraction (`(0,1)` entry `0 - 2 = -2 ≠ -1 = 0 - 1`). -/
theorem randomWalkLaplacian_symmetric_hA_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ),
        (randomWalkLaplacian A d).IsSymm) := by
  intro h
  have h1 := h rwAsymAdj 1
  have h01 := h1.apply 0 1
  rw [randomWalkLaplacian] at h01
  simp only [Matrix.sub_apply] at h01
  rw [Matrix.one_apply] at h01
  simp only [if_neg (show (0 : Fin 2) ≠ 1 by decide), if_neg (show (1 : Fin 2) ≠ 0 by decide),
    transitionMatrix, Matrix.smul_apply, smul_eq_mul, inv_one, one_mul] at h01
  rw [rwAsymAdj_10, rwAsymAdj_01] at h01
  norm_num at h01

/-- **The `d = 0` junk-rescue corner.** At `d = 0` the junk scalar
`0⁻¹ = 0` collapses the transition matrix to the zero matrix —
symmetric for *every* adjacency. This is where junk rescues the two
dropped symmetry statements rather than refuting them: they fail
exactly when `d ≠ 0` ∧ asymmetric. -/
theorem rwAsymAdj_transitionMatrix_zero_eq_zero :
    transitionMatrix rwAsymAdj 0 = 0 := by
  simp [transitionMatrix]

theorem rwAsymAdj_transitionMatrix_zero_isSymm :
    (transitionMatrix rwAsymAdj 0).IsSymm := by
  rw [rwAsymAdj_transitionMatrix_zero_eq_zero]
  simp

theorem rwAsymAdj_randomWalkLaplacian_zero_isSymm :
    (randomWalkLaplacian rwAsymAdj 0).IsSymm := by
  rw [randomWalkLaplacian, rwAsymAdj_transitionMatrix_zero_eq_zero, sub_zero]
  exact Matrix.isSymm_one

/-! #### Fixture 2: `rwZeroAdj = 0` — the `hdpos` breaker -/

/-- The `hdpos` breaker: the zero matrix on `Fin 2`, genuinely
`0`-regular (`deg 0 i = ∑ j, 0 = 0`). The junk `0⁻¹ = 0` corner where
both `hdpos`-dropped statements fail — and, by the strengthening
companions below, the *only* corner where they fail. -/
def rwZeroAdj : Matrix (Fin 2) (Fin 2) ℝ := 0

/-- Isolation: the kept `hd` clause is genuine — the zero matrix is
genuinely `0`-regular. -/
theorem rwZeroAdj_deg (i : Fin 2) : deg rwZeroAdj i = 0 := by
  simp [deg, rwZeroAdj]

/-- The definitional junk pin: the transition matrix of the `0`-regular
graph is the **zero matrix** (`0⁻¹ = 0`), not a stochastic matrix — the
row-sum interface a Markov consumer needs exists only off this corner. -/
theorem rwZeroAdj_transitionMatrix_zero_eq_zero :
    transitionMatrix rwZeroAdj 0 = 0 := by
  simp [transitionMatrix]

theorem rwZeroAdj_transitionMatrix_row_sum_zero (i : Fin 2) :
    ∑ j, transitionMatrix rwZeroAdj 0 i j = 0 := by
  rw [rwZeroAdj_transitionMatrix_zero_eq_zero]
  simp

/-- **Fence (`hdpos` clause of `transitionMatrix_row_sum`).** Dropping
`0 < d` is refuted at the genuinely `0`-regular zero matrix: the kept
`hd` holds (`deg = 0`) while the junk `0⁻¹ = 0` collapses every row sum
to `0 ≠ 1`. -/
theorem transitionMatrix_row_sum_hdpos_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ), (∀ i, deg A i = d) →
        ∀ i, ∑ j, transitionMatrix A d i j = 1) := by
  intro h
  have h0 := h rwZeroAdj 0 rwZeroAdj_deg 0
  rw [rwZeroAdj_transitionMatrix_row_sum_zero 0] at h0
  norm_num at h0

/-- The bridge's two sides separate maximally at the same corner:
`L_rw = 1 - 0 = 1` against `0⁻¹ • laplacian 0 = 0`. -/
theorem rwZeroAdj_laplacian_apply (i j : Fin 2) :
    laplacian rwZeroAdj i j = 0 := by
  simp [laplacian, degreeMatrix, deg, rwZeroAdj]

/-- **Fence (`hdpos` clause of `randomWalkLaplacian_eq_smul_laplacian`).**
Dropping `0 < d` is refuted at the same fixture: the kept `hd` holds
while the identity's two sides separate at `(0,0)` — `1 - 0⁻¹ * 0 = 1`
against `0⁻¹ * 0 = 0`. -/
theorem randomWalkLaplacian_eq_smul_laplacian_hdpos_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ), (∀ i, deg A i = d) →
        randomWalkLaplacian A d = d⁻¹ • laplacian A) := by
  intro h
  have h0 := h rwZeroAdj 0 rwZeroAdj_deg
  have e00 := congrFun (congrFun h0 0) 0
  simp only [randomWalkLaplacian, Matrix.sub_apply, Matrix.one_apply,
    transitionMatrix, Matrix.smul_apply, smul_eq_mul, rwZeroAdj_laplacian_apply,
    inv_zero, zero_mul, Matrix.zero_apply, Pi.one_apply] at e00
  norm_num at e00

/-! #### Fixture 3: the delivered `rwEdgeAdj` at the wrong claimed degree
`d = 2` — the `hd` breaker -/

/-- Isolation: the dropped clause genuinely fails — `rwEdgeAdj` is
genuinely `1`-regular, so it is not `2`-regular. -/
theorem rwEdgeAdj_not_two_regular : ¬ (∀ i, deg rwEdgeAdj i = 2) := by
  intro h
  have h0 := h 0
  rw [rwEdgeAdj_deg] at h0
  norm_num at h0

/-- The kill pin: at the wrong claimed degree `d = 2` every row of the
transition matrix sums to `1/2`, not `1` — pure wrong-constant
arithmetic, no junk anywhere. -/
theorem rwEdgeAdj_transitionMatrix_row_sum_two (i : Fin 2) :
    ∑ j, transitionMatrix rwEdgeAdj 2 i j = 1 / 2 := by
  simp only [transitionMatrix, Matrix.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]
  rw [← deg, rwEdgeAdj_deg i, inv_eq_one_div]
  norm_num

/-- **Fence (`hd` clause of `transitionMatrix_row_sum`).** Dropping
regularity is refuted at `rwEdgeAdj` with the claimed degree `d = 2`: the
kept `0 < d` is genuine while the row sums are `1/2 ≠ 1`. -/
theorem transitionMatrix_row_sum_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ), 0 < d →
        ∀ i, ∑ j, transitionMatrix A d i j = 1) := by
  intro h
  have h0 := h rwEdgeAdj 2 two_pos 0
  rw [rwEdgeAdj_transitionMatrix_row_sum_two 0] at h0
  norm_num at h0

/-- The bridge's separation pin at the same fixture: the walk
Laplacian's diagonal is `1 - 2⁻¹ * 0 = 1` while the scaled
combinatorial Laplacian's is `2⁻¹ * 1 = 1/2`. -/
theorem rwEdgeAdj_randomWalkLaplacian_two_00 :
    randomWalkLaplacian rwEdgeAdj 2 0 0 = 1 := by
  simp only [randomWalkLaplacian, Matrix.sub_apply, transitionMatrix,
    Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, rwEdgeAdj]
  norm_num

theorem rwEdgeAdj_smul_laplacian_two_00 :
    ((2:ℝ)⁻¹ • laplacian rwEdgeAdj) 0 0 = 1 / 2 := by
  have e : laplacian rwEdgeAdj 0 0 = 1 := by
    rw [edge_laplacian_entries_QA]; simp
  simp only [Matrix.smul_apply, smul_eq_mul, e]
  rw [inv_eq_one_div]
  norm_num

/-- **Fence (`hd` clause of `randomWalkLaplacian_eq_smul_laplacian`).**
Dropping regularity is refuted at `rwEdgeAdj` with the claimed degree
`d = 2`: the kept `0 < d` is genuine while the two sides separate `2×`
at the diagonal (`1 ≠ 1/2`). -/
theorem randomWalkLaplacian_eq_smul_laplacian_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ), 0 < d →
        randomWalkLaplacian A d = d⁻¹ • laplacian A) := by
  intro h
  have h0 := h rwEdgeAdj 2 two_pos
  have e00 := congrFun (congrFun h0 0) 0
  rw [rwEdgeAdj_randomWalkLaplacian_two_00, rwEdgeAdj_smul_laplacian_two_00]
    at e00
  norm_num at e00

/-! #### The strengthening companions: `d = 0` is the only failure
corner

At every genuinely `d`-regular fixture with `d ≠ 0` — negative degrees
included — both `hdpos`-dropped statements are *true*, by the same
routes the shelf proofs use. Together with the two fences above this is
an exact characterization: `0 < d` is needed only as `d ≠ 0`, and only
the junk corner `d = 0` separates them. -/

/-- **Strengthening companion (row sums).** The shelf theorem's proof
route closes verbatim with `0 < d` weakened to `d ≠ 0`. -/
theorem transitionMatrix_row_sum_of_ne_zero {V : Type} [Fintype V]
    [DecidableEq V] (A : WAdj (V := V)) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdz : d ≠ 0) (i : V) :
    ∑ j, transitionMatrix A d i j = 1 := by
  simp only [transitionMatrix, Matrix.smul_apply, smul_eq_mul,
    ← Finset.mul_sum]
  rw [← deg, hd i, inv_mul_cancel₀ hdz]

/-- **Strengthening companion (the scaling bridge).** The shelf
theorem's proof route closes with `0 < d` weakened to `d ≠ 0`
(`field_simp` clears the inverse through `hdz`). -/
theorem randomWalkLaplacian_eq_smul_laplacian_of_ne_zero {V : Type}
    [Fintype V] [DecidableEq V] (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdz : d ≠ 0) :
    randomWalkLaplacian A d = d⁻¹ • laplacian A := by
  ext i j
  simp only [randomWalkLaplacian, transitionMatrix, Matrix.sub_apply,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, Pi.one_apply,
    laplacian, degreeMatrix]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, dif_pos rfl, hd i]
    field_simp
  · simp [h]

end AdversarialFences

/-! ## Singles pins: the walk-Laplacian symmetry

The first genuine consumption of `randomWalkLaplacian_symmetric`, at
`d = 2` — a choice off the fixture's degree, so the entries carry the
genuine `1/2` scaling and the symmetry statement is not degenerate.
-/

section SinglesPins

/-- Symmetry through the theorem at `d = 2`. -/
theorem rwp_walkLaplacian_sym :
    (randomWalkLaplacian rwEdgeAdj 2).IsSymm :=
  randomWalkLaplacian_symmetric rwEdgeAdj rwEdgeAdj_isSymm 2

/-- The entry equality derived through the theorem (the transpose
route), plus the raw value `−1/2` of the off-diagonal entries — the
`(1, 0)` entry read from the `(0, 1)` entry through symmetry, exactly
what a transposed convention would break. -/
theorem rwp_walkLaplacian_entry :
    (randomWalkLaplacian rwEdgeAdj 2) 0 1 = (randomWalkLaplacian rwEdgeAdj 2) 1 0
      ∧ (randomWalkLaplacian rwEdgeAdj 2) 0 1 = -(1 / 2) := by
  constructor
  · have h := randomWalkLaplacian_symmetric rwEdgeAdj rwEdgeAdj_isSymm 2
    calc (randomWalkLaplacian rwEdgeAdj 2) 0 1
        = (randomWalkLaplacian rwEdgeAdj 2)ᵀ 1 0 :=
          (Matrix.transpose_apply _ _ _).symm
      _ = (randomWalkLaplacian rwEdgeAdj 2) 1 0 := by rw [h.eq]
  · simp only [randomWalkLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.smul_apply, smul_eq_mul, transitionMatrix, rwEdgeAdj]
    norm_num

end SinglesPins

end SpectralGraphTheory.QA
