/-
  Expander_QA.lean

  Purpose
  -------
  QA for `Scaffold.Mathlib.GraphTheory.Expander` — step 1 of
  `proposals/decidable-spectral-certificates.md` (the edge-weight and
  discrepancy core of the Expander Mixing Lemma).

  Style follows the falsification convention of the sibling QA files:

  - *Computation from the definitions.* Every edge weight, centered
    indicator entry, and centered cross term is unfolded on a concrete
    fixture and evaluated; the general theorems under test are not
    invoked on the path from definition to value. A mis-defined
    `edgeWeight` or `centeredIndicator` self-consistent with its own
    theorem family would be caught by a wrong value.
  - *Positive witnesses.* The `d`-regular decomposition is instantiated
    on both an adjacent cut (cross term `+1/2`) and an opposite cut
    (cross term `-1/2`), each cross term computed independently from
    the raw definitions, and the matrix form of the cut weight is
    computed raw and cross-checked against the theorem.
  - *Negative witnesses.* Dropping the centered cross term from the
    decomposition is refuted numerically on the opposite cut (`0 ≠
    1/2`); the main term's degree is pinned by regularity (a wrong `d`
    is refuted, `1 ≠ 3/4`); and cut-weight symmetry genuinely fails on
    an asymmetric weight matrix (`2 ≠ 1`), so the symmetry hypothesis
    is load-bearing.

  Fixtures are declared under fresh names rather than imported from
  sibling QA modules: QA modules are built independently and must not
  import each other (they share the `SpectralGraphTheory.QA`
  namespace).

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks interfaces; it does not prove any
  axiom's truth.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Expander
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The four-cycle fixture `0 — 1 — 2 — 3 — 0`
-/

/-- Adjacency of the cycle `C₄` on `Fin 4`: symmetric, unit weights,
all degrees `2` (2-regular — the decomposition's hypothesis). -/
def expCycleAdj4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of !![0, 1, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 1, 0, 1, 0]

theorem expCycleAdj4_isSymm : expCycleAdj4.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [expCycleAdj4]

theorem expCycleAdj4_deg (i : Fin 4) : deg expCycleAdj4 i = 2 := by
  fin_cases i
  · simp only [deg, expCycleAdj4, Matrix.of_apply, Fin.sum_univ_four]
    norm_num
  · simp only [deg, expCycleAdj4, Matrix.of_apply, Fin.sum_univ_four]
    norm_num
  · simp only [deg, expCycleAdj4, Matrix.of_apply, Fin.sum_univ_four]
    norm_num
  · simp only [deg, expCycleAdj4, Matrix.of_apply, Fin.sum_univ_four]
    norm_num

/-!
## Cut weights, computed from the raw definition
-/

/-- Adjacent singletons: one unit edge. -/
theorem exp_ew_adjacent_QA :
    edgeWeight expCycleAdj4 {0} {1} = 1 := by
  simp [edgeWeight, expCycleAdj4]

/-- Opposite singletons: no edge — the cut weight is zero even though
both sets are nonempty. -/
theorem exp_ew_opposite_QA :
    edgeWeight expCycleAdj4 {0} {2} = 0 := by
  simp [edgeWeight, expCycleAdj4]

/-- Half-and-half cut: the two crossing edges. -/
theorem exp_ew_01_23_QA :
    edgeWeight expCycleAdj4 ({0, 1} : Finset (Fin 4)) {2, 3} = 2 := by
  simp [edgeWeight, expCycleAdj4]
  norm_num

/-- The total weight: every row sums to `2`, four rows. -/
theorem exp_ew_univ_QA :
    edgeWeight expCycleAdj4 Finset.univ Finset.univ = 8 := by
  simp only [edgeWeight, Matrix.dotProduct, Matrix.mulVec, expCycleAdj4,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.vecTail,
    Matrix.vecHead]
  norm_num

/-- Row-degree form: the cut against `univ` is the degree sum over the
source set. -/
theorem exp_ew_univ_right_QA :
    edgeWeight expCycleAdj4 ({0, 1} : Finset (Fin 4)) Finset.univ = 4 := by
  simp only [edgeWeight, Matrix.dotProduct, Matrix.mulVec, expCycleAdj4,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.vecTail,
    Matrix.vecHead,
    Finset.sum_insert, Finset.sum_singleton]
  norm_num

/-- The matrix form computed raw from `dotProduct`/`mulVec`,
independently of `edgeWeight_eq_dotProduct`. -/
theorem exp_ew_matrix_raw_QA :
    indicatorVec ({0, 1} : Finset (Fin 4)) ⬝ᵥ
      (expCycleAdj4 *ᵥ indicatorVec ({2, 3} : Finset (Fin 4))) = 2 := by
  have hI01 : indicatorVec ({0, 1} : Finset (Fin 4)) =
      ![1, 1, 0, 0] := by
    funext i
    fin_cases i <;> simp [indicatorVec]
  have hI23 : indicatorVec ({2, 3} : Finset (Fin 4)) =
      ![0, 0, 1, 1] := by
    funext i
    fin_cases i <;> simp [indicatorVec]
  rw [hI01, hI23]
  simp only [Matrix.dotProduct, Matrix.mulVec, expCycleAdj4,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.vecTail,
    Matrix.vecHead]
  norm_num

/-- The raw value agrees with the theorem's matrix form (both sides of
`edgeWeight_eq_dotProduct` are pinned independently above). -/
theorem exp_ew_dotProduct_agrees_QA :
    edgeWeight expCycleAdj4 ({0, 1} : Finset (Fin 4)) {2, 3} =
      indicatorVec ({0, 1} : Finset (Fin 4)) ⬝ᵥ
        (expCycleAdj4 *ᵥ indicatorVec ({2, 3} : Finset (Fin 4))) := by
  rw [exp_ew_01_23_QA, exp_ew_matrix_raw_QA]

/-- Symmetry of the cut weight instantiated on the half-and-half cut. -/
theorem exp_ew_symm_QA :
    edgeWeight expCycleAdj4 ({0, 1} : Finset (Fin 4)) {2, 3} =
      edgeWeight expCycleAdj4 {2, 3} ({0, 1} : Finset (Fin 4)) := by
  rw [edgeWeight_symm expCycleAdj4 expCycleAdj4_isSymm]

/-!
## Centered indicators, computed entrywise
-/

/-- The centered indicator of the half-set: entries `±1/2`. -/
theorem exp_centered_pair_QA :
    centeredIndicator ({0, 1} : Finset (Fin 4)) =
      ![1 / 2, 1 / 2, -1 / 2, -1 / 2] := by
  funext i
  fin_cases i <;>
    simp [centeredIndicator, indicatorVec, Fintype.card_fin] <;>
    norm_num

/-- The centered indicator of a singleton: `3/4` at the member,
`-1/4` elsewhere. -/
theorem exp_centered_single_QA :
    centeredIndicator ({0} : Finset (Fin 4)) =
      ![3 / 4, -1 / 4, -1 / 4, -1 / 4] := by
  funext i
  fin_cases i <;>
    simp [centeredIndicator, indicatorVec, Fintype.card_fin] <;>
    norm_num

/-- Orthogonality to `onesVec`, computed from the raw dot product of
the pinned entries (not through the general theorem). -/
theorem exp_centered_orthogonal_QA :
    centeredIndicator ({0, 1} : Finset (Fin 4)) ⬝ᵥ onesVec = 0 := by
  rw [exp_centered_pair_QA]
  simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.vecTail, Matrix.vecHead]
  norm_num

/-!
## The centered cross terms, computed from the raw definitions
-/

set_option linter.unnecessarySeqFocus false in
/-- Cross term of the adjacent cut: `+1/2`. -/
theorem exp_cross_adjacent_QA :
    centeredIndicator ({0} : Finset (Fin 4)) ⬝ᵥ
      (expCycleAdj4 *ᵥ centeredIndicator ({1} : Finset (Fin 4))) = 1 / 2 := by
  have hC1 : centeredIndicator ({1} : Finset (Fin 4)) =
      ![-(1 / 4), 3 / 4, -(1 / 4), -(1 / 4)] := by
    funext i
    fin_cases i <;>
      simp [centeredIndicator, indicatorVec, Fintype.card_fin] <;>
      norm_num
  rw [exp_centered_single_QA, hC1]
  simp only [Matrix.dotProduct, Matrix.mulVec, expCycleAdj4,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.vecTail,
    Matrix.vecHead]
  norm_num

set_option linter.unnecessarySeqFocus false in
/-- Cross term of the opposite cut: `-1/2`. -/
theorem exp_cross_opposite_QA :
    centeredIndicator ({0} : Finset (Fin 4)) ⬝ᵥ
      (expCycleAdj4 *ᵥ centeredIndicator ({2} : Finset (Fin 4))) = -(1 / 2) := by
  have hC2 : centeredIndicator ({2} : Finset (Fin 4)) =
      ![-(1 / 4), -(1 / 4), 3 / 4, -(1 / 4)] := by
    funext i
    fin_cases i <;>
      simp [centeredIndicator, indicatorVec, Fintype.card_fin] <;>
      norm_num
  rw [exp_centered_single_QA, hC2]
  simp only [Matrix.dotProduct, Matrix.mulVec, expCycleAdj4,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.vecTail,
    Matrix.vecHead]
  norm_num

/-!
## The decomposition instantiated, and what it refutes
-/

/-- Adjacent cut: `1 = 2·1·1/4 + 1/2` — the theorem instantiated, with
both the cut weight and the cross term pinned independently above. -/
theorem exp_decomp_adjacent_QA :
    edgeWeight expCycleAdj4 ({0} : Finset (Fin 4)) {1} =
      2 * 1 * 1 / (Fintype.card (Fin 4) : ℝ) + 1 / 2 := by
  rw [edgeWeight_eq_regular_add_centered expCycleAdj4
    expCycleAdj4_isSymm 2 expCycleAdj4_deg, exp_cross_adjacent_QA]
  norm_num [Fintype.card_fin, Finset.card_singleton]

/-- Opposite cut: `0 = 2·1·1/4 - 1/2` — the cross term cancels the
main term exactly. -/
theorem exp_decomp_opposite_QA :
    edgeWeight expCycleAdj4 ({0} : Finset (Fin 4)) {2} =
      2 * 1 * 1 / (Fintype.card (Fin 4) : ℝ) - 1 / 2 := by
  rw [edgeWeight_eq_regular_add_centered expCycleAdj4
    expCycleAdj4_isSymm 2 expCycleAdj4_deg, exp_cross_opposite_QA]
  norm_num [Fintype.card_fin, Finset.card_singleton]

/-- **Negative witness (cross term load-bearing).** A statement keeping
only the population main term is refuted on the opposite cut:
`edgeWeight = 0` while the main term is `1/2`. -/
theorem exp_main_term_only_refuted_QA :
    edgeWeight expCycleAdj4 ({0} : Finset (Fin 4)) {2} ≠
      2 * 1 * 1 / (Fintype.card (Fin 4) : ℝ) := by
  rw [exp_ew_opposite_QA]
  norm_num [Fintype.card_fin]

/-- **Negative witness (degree pinned by regularity).** The main term's
`d` is forced: with the wrong degree `3` the main term is `3/4 ≠ 1` =
the adjacent cut weight. -/
theorem exp_wrong_degree_refuted_QA :
    edgeWeight expCycleAdj4 ({0} : Finset (Fin 4)) {1} ≠
      3 * 1 * 1 / (Fintype.card (Fin 4) : ℝ) := by
  rw [exp_ew_adjacent_QA]
  norm_num [Fintype.card_fin]

/-!
## Asymmetry witness: cut-weight symmetry genuinely fails
-/

/-- An asymmetric two-vertex weight matrix: `A 0 1 = 2 ≠ 1 = A 1 0`. -/
def expAsymAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 2; 1, 0]

theorem exp_ew_asym_QA : edgeWeight expAsymAdj {0} {1} = 2 := by
  simp [edgeWeight, expAsymAdj]

theorem exp_ew_asym_swapped_QA : edgeWeight expAsymAdj {1} {0} = 1 := by
  simp [edgeWeight, expAsymAdj]

/-- **Negative witness (symmetry load-bearing).** The asymmetric weight
has `edgeWeight {0} {1} = 2 ≠ 1 = edgeWeight {1} {0}`, so
`edgeWeight_symm`'s hypothesis is not vacuous. -/
theorem exp_ew_asym_ne_QA :
    edgeWeight expAsymAdj {0} {1} ≠ edgeWeight expAsymAdj {1} {0} := by
  rw [exp_ew_asym_QA, exp_ew_asym_swapped_QA]
  norm_num

end SpectralGraphTheory.QA
