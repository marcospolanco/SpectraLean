/-
  Directed_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Directed` (the directed
  degree layer, `proposals/directed-graph-operators.md` Step 1) and —
  its load-bearing core — the certification that the pre-existing
  undirected-shelf walk operators (`walkTransitionMatrix`,
  `walkLaplacian`) genuinely apply to asymmetric, genuinely directed
  input, at the fixture `dirA` (arcs 0→1 of weight 3, 0→2 of weight 1,
  1→0 and 2→0 of weight 1).

  Step 2 QA (the directed normalized Laplacian, same proposal; see the
  Step 2 section below for the witness list): every entry of
  `L_dir dirA` computed from the entry form, symmetry instantiated
  hypothesis-free on asymmetric input, the symmetric-cone agreement on
  `symA`, the square-root-free conjugate instantiated with both sides
  computed raw, the undirected-reuse negative witness
  (`L_dir ≠ normalizedLaplacian` on directed input), and the
  calibration negative witness — `L_dir` is symmetric but **not PSD**
  on directed input (`quadForm` refuted at `dirB`). Pin-specific
  technique added: `Real.sqrt` of a numeral needs
  `Real.sqrt_eq_iff_eq_sq` on this pin (`norm_num` alone does not
  evaluate it); `Real.sqrt_one` for `1`.

  Witnesses, per the proposal's QA plan:

  - positive: `outDeg = (4, 1, 1)` and `inDeg = (2, 3, 1)` on `dirA`,
    pinned through the `rfl` entry table; the directed handshaking
    `∑ outDeg = ∑ inDeg = 6` by theorem and by raw sums;
  - agreement: on the symmetric edge, `inDeg = outDeg = deg` at every
    vertex, through the theorems and raw;
  - negative: `outDeg dirA 0 ≠ inDeg dirA 0` (`4 ≠ 2`) — the directed
    case is genuinely not free — and `walkTransitionMatrix dirA` is
    provably *not* symmetric (`P 0 1 = 3/4 ≠ 1 = P 1 0`): there is no
    symmetric operator to restrict to, the calibration fact this axis
    turns on;
  - row-stochasticity and mass conservation instantiated on `dirA`
    through the shelf's own hypothesis-free (symmetry-free) theorems.

  Evaluation note (pin-specific): entry sums are pinned by `show`
  (kernel defeq through `Finset.sum` on `Fin 3`) plus a nine-entry
  `rfl` table for `dirA` — `simp only [outDeg, dirA, ...]` unfolds of
  the *new* degree defs leave `Matrix.vecHead (Matrix.vecTail …)`
  residue on this snapshot, while the same list through `deg` behaves;
  the kernel route is deterministic either way.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Directed
import Scaffold.Mathlib.GraphTheory.Stationary
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The directed fixture and its entry table
-/

/-- Adjacency of a genuinely directed 3-vertex network: arcs `0→1`
(weight 3), `0→2` (weight 1), `1→0` (weight 1), `2→0` (weight 1).
Nonnegative (every entry is pinned to `0`, `1`, or `3` by the table
below), positive out-degrees, not symmetric; `outDeg = (4, 1, 1)`
against `inDeg = (2, 3, 1)`. -/
def dirA : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 3, 1; 1, 0, 0; 1, 0, 0]

/-- The entry table, proved by kernel evaluation (`rfl`). Every entry
is a nonneg numeral, which is the fixture's nonnegativity witness. -/
theorem dirA_00 : dirA 0 0 = 0 := rfl
theorem dirA_01 : dirA 0 1 = 3 := rfl
theorem dirA_02 : dirA 0 2 = 1 := rfl
theorem dirA_10 : dirA 1 0 = 1 := rfl
theorem dirA_11 : dirA 1 1 = 0 := rfl
theorem dirA_12 : dirA 1 2 = 0 := rfl
theorem dirA_20 : dirA 2 0 = 1 := rfl
theorem dirA_21 : dirA 2 1 = 0 := rfl
theorem dirA_22 : dirA 2 2 = 0 := rfl

/-- The fixture is genuinely asymmetric: `dirA 0 1 = 3 ≠ 1 = dirA 1 0`. -/
theorem dirA_not_isSymm : ¬ dirA.IsSymm := by
  intro h
  have h01 := h.apply 0 1
  rw [dirA_01, dirA_10] at h01
  norm_num at h01

/-!
## The two degree functions, pinned raw
-/

/-- Out-degree of vertex 0: `0 + 3 + 1 = 4`. -/
theorem dirA_outDeg_zero : outDeg dirA 0 = 4 := by
  simp only [outDeg, Fin.sum_univ_three]
  rw [dirA_00, dirA_01, dirA_02]; norm_num

/-- Out-degree of vertex 1: `1 + 0 + 0 = 1`. -/
theorem dirA_outDeg_one : outDeg dirA 1 = 1 := by
  simp only [outDeg, Fin.sum_univ_three]
  rw [dirA_10, dirA_11, dirA_12]; norm_num

/-- Out-degree of vertex 2: `1 + 0 + 0 = 1`. -/
theorem dirA_outDeg_two : outDeg dirA 2 = 1 := by
  simp only [outDeg, Fin.sum_univ_three]
  rw [dirA_20, dirA_21, dirA_22]; norm_num

/-- In-degree of vertex 0: column 0 is `0 + 1 + 1 = 2`. -/
theorem dirA_inDeg_zero : inDeg dirA 0 = 2 := by
  simp only [inDeg, Fin.sum_univ_three]
  rw [dirA_00, dirA_10, dirA_20]; norm_num

/-- In-degree of vertex 1: column 1 is `3 + 0 + 0 = 3`. -/
theorem dirA_inDeg_one : inDeg dirA 1 = 3 := by
  simp only [inDeg, Fin.sum_univ_three]
  rw [dirA_01, dirA_11, dirA_21]; norm_num

/-- In-degree of vertex 2: column 2 is `1 + 0 + 0 = 1`. -/
theorem dirA_inDeg_two : inDeg dirA 2 = 1 := by
  simp only [inDeg, Fin.sum_univ_three]
  rw [dirA_02, dirA_12, dirA_22]; norm_num

/-- **Negative witness** (the proposal's "directed case is genuinely
not free"): out- and in-degree differ at vertex 0, `4 ≠ 2`. Any lemma
phrased for the undirected shelf as if `outDeg = inDeg` were free
produces a wrong answer here. -/
theorem dirA_outDeg_ne_inDeg : outDeg dirA 0 ≠ inDeg dirA 0 := by
  rw [dirA_outDeg_zero, dirA_inDeg_zero]
  norm_num

/-- The out-degree of the fixture *is* the shelf's `deg` — the
definitional identity instantiated where the arithmetic is evaluated. -/
theorem dirA_outDeg_eq_deg_QA : outDeg dirA 0 = deg dirA 0 :=
  outDeg_eq_deg dirA 0

/-- The transpose identity instantiated with content: `inDeg dirA 1`
is `deg` of the reversed network, checked against the entry table. -/
theorem dirA_inDeg_transpose_QA :
    inDeg dirA 1 = deg dirAᵀ 1 :=
  inDeg_eq_deg_transpose dirA 1

/-- Raw check of the reversed-network degree: column 1 of `dirA` is
`3 + 0 + 0 = 3`. -/
theorem dirA_degTranspose_one : deg dirAᵀ 1 = 3 := by
  simp only [deg, Fin.sum_univ_three, Matrix.transpose_apply]
  rw [dirA_01, dirA_11, dirA_21]; norm_num

/-- The shelf degrees of the fixture: `(4, 1, 1)`. -/
theorem dirA_deg_zero : deg dirA 0 = 4 := dirA_outDeg_zero
theorem dirA_deg_one : deg dirA 1 = 1 := dirA_outDeg_one
theorem dirA_deg_two : deg dirA 2 = 1 := dirA_outDeg_two

/-- Positive out-degrees at every vertex — the hypothesis shape the
walk-operator interface consumes (`deg` route: this snapshot's `simp`
idiom is reliable through `deg`). -/
theorem dirA_deg_pos (i : Fin 3) : 0 < deg dirA i := by
  fin_cases i <;>
    simp only [deg, dirA, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num

/-!
## Directed handshaking
-/

/-- **Directed handshaking**, theorem route: total out-weight equals
total in-weight, no symmetry or nonnegativity anywhere in the
statement. -/
theorem dirA_handshake_QA :
    ∑ i, outDeg dirA i = ∑ i, inDeg dirA i :=
  sum_outDeg_eq_sum_inDeg dirA

/-- **Directed handshaking**, raw route: both totals computed
independently as `6` — rows `4 + 1 + 1`, columns `2 + 3 + 1`. -/
theorem dirA_handshake_outDeg_raw_QA : ∑ i, outDeg dirA i = 6 := by
  rw [Fin.sum_univ_three]
  rw [dirA_outDeg_zero, dirA_outDeg_one, dirA_outDeg_two]; norm_num

theorem dirA_handshake_inDeg_raw_QA : ∑ i, inDeg dirA i = 6 := by
  rw [Fin.sum_univ_three]
  rw [dirA_inDeg_zero, dirA_inDeg_one, dirA_inDeg_two]; norm_num

/-!
## The pre-existing walk operators on asymmetric input
-/

/-- **The load-bearing certification:** the undirected shelf's
row-stochasticity theorem, stated without any symmetry hypothesis,
instantiated on the asymmetric fixture — every row of
`P = D_out⁻¹ A` sums to one. Had `walkTransitionMatrix` secretly been
defined through the symmetrized adjacency, or `deg` through a
symmetric sum, this instantiation would not elaborate or would be
false. -/
theorem dirA_walk_row_sum_QA (i : Fin 3) :
    ∑ j, walkTransitionMatrix dirA i j = 1 :=
  walkTransitionMatrix_row_sum dirA dirA_deg_pos i

/-- Raw cross-check of row 0: `(1/4)·0 + (1/4)·3 + (1/4)·1 = 1`. -/
theorem dirA_walk_row_sum_raw_QA :
    ∑ j, walkTransitionMatrix dirA 0 j = 1 := by
  simp only [Fin.sum_univ_three, walkTransitionMatrix_apply,
    dirA_deg_zero]
  rw [dirA_00, dirA_01, dirA_02]; norm_num

/-- Mass conservation on asymmetric input: the walk Laplacian kills
the constant vector. -/
theorem dirA_walkLaplacian_conserves_QA :
    walkLaplacian dirA *ᵥ (fun _ => (1 : ℝ)) = 0 :=
  walkLaplacian_mulVec_one_eq_zero dirA dirA_deg_pos

/-- Entry of the walk matrix: `P 0 1 = 3/4` (out of vertex 0, three
quarters of the weight goes to 1). -/
theorem dirA_walkP01 : walkTransitionMatrix dirA 0 1 = 3 / 4 := by
  rw [walkTransitionMatrix_apply, dirA_deg_zero, dirA_01]
  norm_num

/-- Entry of the walk matrix: `P 1 0 = 1` (all of vertex 1's weight
goes to 0). -/
theorem dirA_walkP10 : walkTransitionMatrix dirA 1 0 = 1 := by
  rw [walkTransitionMatrix_apply, dirA_deg_one, dirA_10]
  norm_num

/-- **Negative witness, calibration:** the directed walk matrix is
provably *not* symmetric — `P 0 1 = 3/4 ≠ 1 = P 1 0`. There is no
symmetric operator to restrict to; the `evals`/`eigvecOf` toolkit
does not reach here (this axis needs Perron–Frobenius instead). -/
theorem dirA_walk_not_isSymm : ¬ (walkTransitionMatrix dirA).IsSymm := by
  intro h
  have h01 := h.apply 0 1
  rw [dirA_walkP10, dirA_walkP01] at h01
  norm_num at h01

/-- Entry of the walk Laplacian: `L_walk 0 1 = 0 − 3/4`, computed from
`I − P` entrywise. -/
theorem dirA_walkLaplacian_zero_one : walkLaplacian dirA 0 1 = -(3 / 4) := by
  simp only [walkLaplacian, Matrix.sub_apply]
  rw [Matrix.one_apply_ne (by decide), dirA_walkP01]
  ring

/-!
## Agreement on the symmetric cone
-/

/-- Adjacency of the single edge on `Fin 2` (symmetric, 1-regular). -/
def symA : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; 1, 0]

theorem symA_isSymm : symA.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [symA]

/-- Agreement theorem route: on the symmetric edge, `inDeg = outDeg`
at every vertex. -/
theorem symA_inDeg_eq_outDeg (i : Fin 2) :
    inDeg symA i = outDeg symA i :=
  inDeg_eq_outDeg_of_isSymm symA symA_isSymm i

/-- Agreement theorem route: on the symmetric edge, `inDeg = deg`. -/
theorem symA_inDeg_eq_deg (i : Fin 2) :
    inDeg symA i = deg symA i :=
  inDeg_eq_deg_of_isSymm symA symA_isSymm i

/-- Raw cross-check: the edge's out-degree and in-degree at vertex 0
are both `1`, computed independently from row and column. -/
theorem symA_outDeg_zero : outDeg symA 0 = 1 := by
  simp only [outDeg, Fin.sum_univ_two]
  have e00 : symA 0 0 = 0 := rfl
  have e01 : symA 0 1 = 1 := rfl
  rw [e00, e01]; norm_num

theorem symA_inDeg_zero : inDeg symA 0 = 1 := by
  simp only [inDeg, Fin.sum_univ_two]
  have e00 : symA 0 0 = 0 := rfl
  have e10 : symA 1 0 = 1 := rfl
  rw [e00, e10]; norm_num

theorem symA_deg_zero : deg symA 0 = 1 := by
  simp only [deg, Fin.sum_univ_two]
  have e00 : symA 0 0 = 0 := rfl
  have e01 : symA 0 1 = 1 := rfl
  rw [e00, e01]; norm_num

/-- Agreement instantiated at vertex 0 through the theorems, all three
degree readings pinned to `1` by the raw computations above. -/
theorem symA_agreement_QA :
    inDeg symA 0 = 1 ∧ outDeg symA 0 = 1 ∧ deg symA 0 = 1 :=
  ⟨symA_inDeg_zero, symA_outDeg_zero, symA_deg_zero⟩

/-!
## The directed normalized Laplacian (Step 2)

The fixture is `dirA` again — degrees `(4, 1, 1)`, all squares, so
`√D = diag(2, 1, 1)` is rational and every entry of `L_dir` is exact.
Expected operator (from the entry form):
`[[1, −1, −1/2], [−1, 1, 0], [−1/2, 0, 1]]`.
-/

/-- The fixture's degree square roots, rational: `√(deg dirA 0) = 2`
(via `Real.sqrt_eq_iff_eq_sq` — `norm_num` does not evaluate `Real.sqrt`
of numerals on this pin) and `√(deg dirA 1) = √(deg dirA 2) = 1`. -/
theorem dirA_sqrt_deg_zero : Real.sqrt (deg dirA 0) = 2 := by
  rw [dirA_deg_zero]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

theorem dirA_sqrt_deg_one : Real.sqrt (deg dirA 1) = 1 := by
  rw [dirA_deg_one]
  exact Real.sqrt_one

theorem dirA_sqrt_deg_two : Real.sqrt (deg dirA 2) = 1 := by
  rw [dirA_deg_two]
  exact Real.sqrt_one

/-- Diagonal entry: `L_dir 0 0 = 1 − ½·(1/2)·(0 + 0)·(1/2) = 1`. The
entry form's `if 0 = 0` is discharged by `if_pos rfl`. -/
theorem dirA_Ldir_zero_zero :
    directedNormalizedLaplacian dirA 0 0 = 1 := by
  rw [directedNormalizedLaplacian_apply, if_pos rfl,
    dirA_sqrt_deg_zero, dirA_00]
  norm_num

/-- Off-diagonal entry: `L_dir 0 1 = −½·(1/2)·(3 + 1)·1 = −1` — the
`0→1` arc of weight 3 and the `1→0` arc of weight 1 enter
symmetrically. -/
theorem dirA_Ldir_zero_one :
    directedNormalizedLaplacian dirA 0 1 = -1 := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    dirA_sqrt_deg_zero, dirA_sqrt_deg_one, dirA_01, dirA_10]
  norm_num

/-- Off-diagonal entry: `L_dir 0 2 = −½·(1/2)·(1 + 1)·1 = −1/2`. -/
theorem dirA_Ldir_zero_two :
    directedNormalizedLaplacian dirA 0 2 = -(1 / 2) := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    dirA_sqrt_deg_zero, dirA_sqrt_deg_two, dirA_02, dirA_20]
  norm_num

/-- Off-diagonal entry: `L_dir 1 0 = −1` (the transpose reading of the
same two arcs as `dirA_Ldir_zero_one`). -/
theorem dirA_Ldir_one_zero :
    directedNormalizedLaplacian dirA 1 0 = -1 := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    dirA_sqrt_deg_one, dirA_sqrt_deg_zero, dirA_10, dirA_01]
  norm_num

/-- Diagonal entry: `L_dir 1 1 = 1` (no loop). -/
theorem dirA_Ldir_one_one :
    directedNormalizedLaplacian dirA 1 1 = 1 := by
  rw [directedNormalizedLaplacian_apply, if_pos rfl,
    dirA_sqrt_deg_one, dirA_11]
  norm_num

/-- Off-diagonal entry: `L_dir 1 2 = 0` (no arcs either way between 1
and 2). -/
theorem dirA_Ldir_one_two :
    directedNormalizedLaplacian dirA 1 2 = 0 := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    dirA_sqrt_deg_one, dirA_sqrt_deg_two, dirA_12, dirA_21]
  norm_num

/-- Off-diagonal entry: `L_dir 2 0 = −1/2`. -/
theorem dirA_Ldir_two_zero :
    directedNormalizedLaplacian dirA 2 0 = -(1 / 2) := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    dirA_sqrt_deg_two, dirA_sqrt_deg_zero, dirA_20, dirA_02]
  norm_num

/-- Off-diagonal entry: `L_dir 2 1 = 0`. -/
theorem dirA_Ldir_two_one :
    directedNormalizedLaplacian dirA 2 1 = 0 := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    dirA_sqrt_deg_two, dirA_sqrt_deg_one, dirA_21, dirA_12]
  norm_num

/-- Diagonal entry: `L_dir 2 2 = 1`. -/
theorem dirA_Ldir_two_two :
    directedNormalizedLaplacian dirA 2 2 = 1 := by
  rw [directedNormalizedLaplacian_apply, if_pos rfl,
    dirA_sqrt_deg_two, dirA_22]
  norm_num

/-- **The load-bearing certification:** the hypothesis-free symmetry
theorem, instantiated on *asymmetric* input. Had the definition
secretly needed `IsSymm` (or the symmetrization been plumbed through a
symmetric-only shelf object), this instantiation would not elaborate. -/
theorem dirA_Ldir_isSymm_QA :
    (directedNormalizedLaplacian dirA).IsSymm :=
  directedNormalizedLaplacian_isSymm dirA

/-- Raw symmetry cross-check at the asymmetric pair: the `(0,1)` and
`(1,0)` entries are both `-1`, pinned independently above. -/
theorem dirA_Ldir_symm_raw_QA :
    directedNormalizedLaplacian dirA 0 1
      = directedNormalizedLaplacian dirA 1 0 := by
  rw [dirA_Ldir_zero_one, dirA_Ldir_one_zero]

/-- **Negative witness, undirected reuse:** the shelf's
`normalizedLaplacian` on the same directed input is a *different*
operator — its `(0,1)` entry is `−3/2` (the unsymmetrized
`(1/2)·3·1`), against `L_dir`'s `−1`. Feeding directed input to the
undirected operator silently loses the symmetrization. -/
theorem dirA_normL_zero_one :
    normalizedLaplacian dirA 0 1 = -(3 / 2) := by
  simp only [normalizedLaplacian, Matrix.sub_apply, degreeInvSqrt,
    Matrix.diagonal_mul, Matrix.mul_diagonal, dirA_sqrt_deg_zero,
    dirA_sqrt_deg_one, dirA_01]
  rw [Matrix.one_apply_ne (by decide : (0 : Fin 3) ≠ 1)]
  norm_num

theorem dirA_Ldir_ne_normalizedLaplacian :
    directedNormalizedLaplacian dirA ≠ normalizedLaplacian dirA := by
  intro h
  have h01 : directedNormalizedLaplacian dirA 0 1
      = normalizedLaplacian dirA 0 1 := by rw [h]
  rw [dirA_Ldir_zero_one, dirA_normL_zero_one] at h01
  norm_num at h01

/-- The square-root-free conjugate, theorem route, on the directed
fixture (positive out-degrees from `dirA_deg_pos`). -/
theorem dirA_conj_QA :
    degreeSqrt dirA * directedNormalizedLaplacian dirA * degreeSqrt dirA
      = degreeMatrix dirA - (1 / 2 : ℝ) • (dirA + dirAᵀ) :=
  degreeSqrt_mul_directedNormalizedLaplacian_mul_degreeSqrt dirA
    dirA_deg_pos

/-- Raw cross-check, right side: the `(0,1)` entry of
`D − ½(A + Aᵀ)` is `0 − ½(3 + 1) = −2`. -/
theorem dirA_conjRHS_zero_one :
    (degreeMatrix dirA - (1 / 2 : ℝ) • (dirA + dirAᵀ)) 0 1 = -2 := by
  have hD : degreeMatrix dirA 0 1 = 0 := by
    simp [degreeMatrix]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.add_apply, Matrix.transpose_apply, hD, dirA_01, dirA_10]
  norm_num

/-- Raw cross-check, left side: the `(0,1)` entry of
`√D L_dir √D` is `√4 · (−1) · √1 = −2`, computed from the pinned
entries through the double sum (the diagonal `if`s resolve by
decidability since all indices are concrete). -/
theorem dirA_conjLHS_zero_one :
    (degreeSqrt dirA * directedNormalizedLaplacian dirA
      * degreeSqrt dirA) 0 1 = -2 := by
  have hDiag0 : ∀ k : Fin 3, degreeSqrt dirA 0 k
      = if (0 : Fin 3) = k then (2 : ℝ) else 0 := by
    intro k
    fin_cases k <;>
      simp [degreeSqrt, Matrix.diagonal_apply, dirA_sqrt_deg_zero]
  have hDiag1 : ∀ k : Fin 3, degreeSqrt dirA k 1
      = if k = (1 : Fin 3) then (1 : ℝ) else 0 := by
    intro k
    fin_cases k <;>
      simp [degreeSqrt, Matrix.diagonal_apply, dirA_sqrt_deg_one]
  simp only [Matrix.mul_apply, Fin.sum_univ_three, hDiag0, hDiag1,
    dirA_Ldir_zero_zero, dirA_Ldir_zero_one, dirA_Ldir_zero_two,
    dirA_Ldir_one_zero, dirA_Ldir_one_one, dirA_Ldir_one_two,
    dirA_Ldir_two_zero, dirA_Ldir_two_one, dirA_Ldir_two_two]
  simp

/-- **Agreement, theorem route (the Step-3 acceptance brick):** on the
symmetric edge, `L_dir = normalizedLaplacian`. -/
theorem symA_Ldir_eq_normalizedLaplacian_QA :
    directedNormalizedLaplacian symA = normalizedLaplacian symA :=
  directedNormalizedLaplacian_eq_normalizedLaplacian symA symA_isSymm

theorem symA_deg_zero' : deg symA 0 = 1 := symA_deg_zero
theorem symA_deg_one : deg symA 1 = 1 := by
  simp only [deg, Fin.sum_univ_two]
  have e10 : symA 1 0 = 1 := rfl
  have e11 : symA 1 1 = 0 := rfl
  rw [e10, e11]; norm_num

theorem symA_01 : symA 0 1 = 1 := rfl
theorem symA_10 : symA 1 0 = 1 := rfl
theorem symA_00 : symA 0 0 = 0 := rfl
theorem symA_11 : symA 1 1 = 0 := rfl

/-- Raw cross-check of the agreement, left side: `L_dir symA 0 1 = −1`
(degrees `(1,1)`, so the normalizers are `1`). -/
theorem symA_Ldir_zero_one : directedNormalizedLaplacian symA 0 1 = -1 := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    symA_deg_zero', symA_deg_one, Real.sqrt_one, inv_one, symA_01, symA_10]
  norm_num

theorem symA_Ldir_one_zero : directedNormalizedLaplacian symA 1 0 = -1 := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    symA_deg_one, symA_deg_zero', Real.sqrt_one, inv_one, symA_10, symA_01]
  norm_num

/-- Raw cross-check of the agreement, right side:
`normalizedLaplacian symA 0 1 = −1`. -/
theorem symA_normL_zero_one : normalizedLaplacian symA 0 1 = -1 := by
  simp only [normalizedLaplacian, Matrix.sub_apply, degreeInvSqrt,
    Matrix.diagonal_mul, Matrix.mul_diagonal, symA_deg_zero', symA_deg_one,
    Real.sqrt_one, inv_one, symA_01]
  rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
  norm_num

/-- Raw cross-check of the agreement on the diagonal:
`L_dir symA 0 0 = 1`. -/
theorem symA_Ldir_zero_zero :
    directedNormalizedLaplacian symA 0 0 = 1 := by
  rw [directedNormalizedLaplacian_apply, if_pos rfl,
    symA_deg_zero', Real.sqrt_one, inv_one, symA_00]
  norm_num

theorem symA_normL_zero_zero : normalizedLaplacian symA 0 0 = 1 := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply_eq,
    degreeInvSqrt, Matrix.diagonal_mul, Matrix.mul_diagonal,
    symA_deg_zero', symA_deg_one, Real.sqrt_one, inv_one, symA_00]
  norm_num

/-!
## Calibration negative witness: symmetric but not PSD

`dirB` (arcs `0→1` weight 4, `1→0` weight 1): out-degrees `(4, 1)`
(both squares), nonnegative, genuinely directed. The symmetrized
adjacency `½(A + Aᵀ)` carries weight `5/2` against the out-degree
normalization `√4·√1 = 2`, so `L_dir 0 1 = −5/4` — past `−1`, and the
quadratic form at `(1, 1)` dips to `−1/2`.
-/

/-- Adjacency of a genuinely directed 2-vertex network: arc `0→1` of
weight 4, arc `1→0` of weight 1. Nonnegative, positive out-degrees,
not symmetric. -/
def dirB : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 4; 1, 0]

theorem dirB_00 : dirB 0 0 = 0 := rfl
theorem dirB_01 : dirB 0 1 = 4 := rfl
theorem dirB_10 : dirB 1 0 = 1 := rfl
theorem dirB_11 : dirB 1 1 = 0 := rfl

theorem dirB_deg_zero : deg dirB 0 = 4 := by
  simp only [deg, Fin.sum_univ_two]
  rw [dirB_00, dirB_01]; norm_num

theorem dirB_deg_one : deg dirB 1 = 1 := by
  simp only [deg, Fin.sum_univ_two]
  rw [dirB_10, dirB_11]; norm_num

theorem dirB_sqrt_deg_zero : Real.sqrt (deg dirB 0) = 2 := by
  rw [dirB_deg_zero]
  exact (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)

theorem dirB_sqrt_deg_one : Real.sqrt (deg dirB 1) = 1 := by
  rw [dirB_deg_one]
  exact Real.sqrt_one

theorem dirB_deg_pos (i : Fin 2) : 0 < deg dirB i := by
  fin_cases i <;>
    simp only [deg, dirB, Matrix.of_apply, Fin.sum_univ_two] <;>
    norm_num

/-- **Symmetry holds on `dirB`** — hypothesis-free theorem route; the
refutation below is therefore about PSD-ness alone, not symmetry. -/
theorem dirB_Ldir_isSymm_QA :
    (directedNormalizedLaplacian dirB).IsSymm :=
  directedNormalizedLaplacian_isSymm dirB

/-- The decisive entry: `L_dir dirB 0 1 = −½·(1/2)·(4 + 1)·1 = −5/4`,
past `−1`. -/
theorem dirB_Ldir_zero_one :
    directedNormalizedLaplacian dirB 0 1 = -(5 / 4) := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    dirB_sqrt_deg_zero, dirB_sqrt_deg_one, dirB_01, dirB_10]
  norm_num

theorem dirB_Ldir_one_zero :
    directedNormalizedLaplacian dirB 1 0 = -(5 / 4) := by
  rw [directedNormalizedLaplacian_apply, if_neg (by decide),
    dirB_sqrt_deg_one, dirB_sqrt_deg_zero, dirB_10, dirB_01]
  norm_num

theorem dirB_Ldir_zero_zero :
    directedNormalizedLaplacian dirB 0 0 = 1 := by
  rw [directedNormalizedLaplacian_apply, if_pos rfl,
    dirB_sqrt_deg_zero, dirB_00]
  norm_num

theorem dirB_Ldir_one_one :
    directedNormalizedLaplacian dirB 1 1 = 1 := by
  rw [directedNormalizedLaplacian_apply, if_pos rfl,
    dirB_sqrt_deg_one, dirB_11]
  norm_num

/-- **The calibration negative witness:** the quadratic form of
`L_dir dirB` at the constant vector is `−1/2`, computed from the
pinned entries. -/
theorem dirB_quadForm :
    quadForm (directedNormalizedLaplacian dirB) (fun _ => (1 : ℝ))
      = -(1 / 2) := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  rw [dirB_Ldir_zero_zero, dirB_Ldir_zero_one,
    dirB_Ldir_one_zero, dirB_Ldir_one_one]
  norm_num

/-- **PSD-ness refuted:** `0 ≤ quadForm` fails on this nonnegative,
positive-out-degree, symmetric-`L_dir` directed fixture. The
positivity layer of the undirected toolkit (PSD-ness, variational
eigenvalue bounds) does not transfer to the directed axis — the exact
boundary the proposal's Calibration section draws; the directed
spectral theory needs Perron–Frobenius instead. -/
theorem dirB_not_quadForm_nonneg :
    ¬ (0 ≤ quadForm (directedNormalizedLaplacian dirB)
        (fun _ => (1 : ℝ))) := by
  rw [dirB_quadForm]
  norm_num

end SpectralGraphTheory.QA
