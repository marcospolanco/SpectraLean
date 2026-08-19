/-
  Expander_QA.lean

  Purpose
  -------
  QA for `Scaffold.Mathlib.GraphTheory.Expander` — steps 1 and 2 of
  `proposals/decidable-spectral-certificates.md`: the edge-weight and
  discrepancy core, and the Expander Mixing Lemma itself.

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
  - *Step 2: the mixing lemma with a derived, tight `μ`.* The spectral
    hypothesis `max |2−λ₂| |2−λ_max| ≤ 2` is proved on `C₄` (test
    vector for `λ₂`, sum-of-squares for `λ_max`, PSD for both lower
    bounds) rather than assumed; the lemma is instantiated on two cuts;
    and the opposite cut *attains the bound exactly* (both sides
    independently compute to `2`), as does the alternating vector in
    the operator bound (`|xᵀAx| = 8 = 2‖x‖²`) — the theorem is not
    vacuous and the derived `μ` is tight.

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

/-!
## The Expander Mixing Lemma on `C₄` (Step 2)

The spectral hypothesis is *derived*, not assumed: `μ = 2` is pinned by
bounding `λ₂` from above with a test vector (`secondEval_le_rayleigh`
at `![1, 0, -1, 0]`), bounding `λ_max` with a direct
sum-of-squares estimate `xᵀ L x ≤ 4 xᵀx` routed to the last sorted
eigenvalue through `quadForm_eigvecOf_self`, and bounding both from
below by 0 through Laplacian positive semidefiniteness. The bound is
then instantiated on two cuts — and the opposite cut *attains equality*,
witnessing that the derived `μ` is tight on this fixture.
-/

theorem expC4_nonneg_QA : ∀ i j, 0 ≤ expCycleAdj4 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [expCycleAdj4]

/-- Every Laplacian eigenvalue of `C₄` is nonnegative (PSD, through a
unit eigenvector's quadratic form). -/
theorem expC4_eigvalOf_nonneg_QA (i : Fin 4) :
    0 ≤ eigvalOf (laplacian expCycleAdj4)
        (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm) i := by
  rw [← quadForm_eigvecOf_self]
  exact laplacian_psd expCycleAdj4 expCycleAdj4_isSymm expC4_nonneg_QA
    (eigvecOf _ _ i)

theorem expC4_lambda2_nonneg_QA :
    0 ≤ lambda2 expCycleAdj4 expCycleAdj4_isSymm (by decide) := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm) ⟨1, by decide⟩
  show 0 ≤ evals (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
    ⟨1, by decide⟩
  rw [hi]
  exact expC4_eigvalOf_nonneg_QA i

theorem expC4_evals_last_nonneg_QA :
    0 ≤ evals (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
        ⟨Fintype.card (Fin 4) - 1, by decide⟩ := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
    ⟨Fintype.card (Fin 4) - 1, by decide⟩
  rw [hi]
  exact expC4_eigvalOf_nonneg_QA i

theorem expC4_quadForm_10m10_QA :
    quadForm (laplacian expCycleAdj4) ![1, 0, -1, 0] = 4 := by
  rw [laplacian_quadForm expCycleAdj4 expCycleAdj4_isSymm]
  simp only [expCycleAdj4, Matrix.of_apply, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons]
  norm_num [sub_sq]

theorem expC4_dot_10m10_QA :
    Matrix.dotProduct (![1, 0, -1, 0] : Fin 4 → ℝ) ![1, 0, -1, 0] = 2 := by
  simp only [Matrix.dotProduct, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.vecTail, Matrix.vecHead]
  norm_num

/-- **`λ₂` pinned from above by a test vector.** The alternating cut
vector `![1, 0, -1, 0]` has Rayleigh quotient `4 / 2 = 2`, so
`λ₂(L(C₄)) ≤ 2`. -/
theorem expC4_lambda2_le_two_QA :
    lambda2 expCycleAdj4 expCycleAdj4_isSymm (by decide) ≤ 2 := by
  have hx0 : (![1, 0, -1, 0] : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, 0, -1, 0] : Fin 4 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have hxorth : Matrix.dotProduct (![1, 0, -1, 0] : Fin 4 → ℝ)
      onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.vecTail, Matrix.vecHead]
    norm_num
  have h := secondEval_le_rayleigh
    (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
    (laplacian_psd expCycleAdj4 expCycleAdj4_isSymm expC4_nonneg_QA)
    (laplacian_ones_in_kernel expCycleAdj4) (by decide) hx0 hxorth
  unfold rayleigh at h
  rw [if_neg hx0, expC4_quadForm_10m10_QA, expC4_dot_10m10_QA] at h
  rw [lambda2_eq_secondEval]
  linarith

set_option linter.unnecessarySeqFocus false in
/-- **The direct sum-of-squares estimate.** For every vector, the
`C₄` Laplacian energy is at most four times the squared norm — each
edge term `(a − b)²` against `(a + b)² ≥ 0`. -/
theorem expC4_quadForm_le_four_QA (x : Fin 4 → ℝ) :
    quadForm (laplacian expCycleAdj4) x ≤ 4 * (x ⬝ᵥ x) := by
  have hedges : (∑ i, ∑ j, expCycleAdj4 i j * (x i - x j) ^ 2)
      = 2 * ((x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2
        + (x 2 - x 3) ^ 2 + (x 3 - x 0) ^ 2) := by
    simp only [expCycleAdj4, Matrix.of_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons]
    norm_num [sub_sq]
    ring
  have hnorm : x ⬝ᵥ x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons]
  have e1 : (0:ℝ) ≤ (x 0 + x 1) ^ 2 := sq_nonneg _
  have e2 : (0:ℝ) ≤ (x 1 + x 2) ^ 2 := sq_nonneg _
  have e3 : (0:ℝ) ≤ (x 2 + x 3) ^ 2 := sq_nonneg _
  have e4 : (0:ℝ) ≤ (x 3 + x 0) ^ 2 := sq_nonneg _
  rw [laplacian_quadForm expCycleAdj4 expCycleAdj4_isSymm, hedges, hnorm]
  nlinarith [e1, e2, e3, e4]

theorem expC4_evals_last_le_four_QA :
    evals (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
        ⟨Fintype.card (Fin 4) - 1, by decide⟩ ≤ 4 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
    ⟨Fintype.card (Fin 4) - 1, by decide⟩
  rw [hi, ← quadForm_eigvecOf_self]
  have hunit : Matrix.dotProduct
      (eigvecOf (laplacian expCycleAdj4)
        (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm) i)
      (eigvecOf (laplacian expCycleAdj4)
        (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm) i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner
      (laplacian expCycleAdj4)
      (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm) i i
  have hle := expC4_quadForm_le_four_QA
    (eigvecOf (laplacian expCycleAdj4)
      (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm) i)
  rw [hunit] at hle
  linarith

/-- **The derived spectral hypothesis.** `max |2 − λ₂| |2 − λ_max| ≤ 2`
on `C₄` — assembled from the three bounds above, not assumed. -/
theorem expC4_mu_le_two_QA :
    max |2 - lambda2 expCycleAdj4 expCycleAdj4_isSymm (by norm_num)|
        |2 - evals (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
            ⟨Fintype.card (Fin 4) - 1, by decide⟩| ≤ 2 := by
  have h2 := expC4_lambda2_le_two_QA
  have h2n := expC4_lambda2_nonneg_QA
  have hmax := expC4_evals_last_le_four_QA
  have hmaxn := expC4_evals_last_nonneg_QA
  exact max_le (abs_le.2 ⟨by linarith, by linarith⟩)
    (abs_le.2 ⟨by linarith, by linarith⟩)

/-- **The mixing lemma instantiated: opposite cut.** With the derived
`μ = 2`, the deviation bound on the cut `({0,2}, {0,2})`. -/
theorem exp_eml_opposite_QA :
    |edgeWeight expCycleAdj4 ({0, 2} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4))
      - 2 * 2 * 2 / (4:ℝ)| ≤
      2 * Real.sqrt ((2:ℝ) * 2 * ((4:ℝ) - 2) * ((4:ℝ) - 2)) / 4 := by
  have hcard : ({0, 2} : Finset (Fin 4)).card = 2 := by decide
  have h := expander_mixing_lemma expCycleAdj4 expCycleAdj4_isSymm
    expC4_nonneg_QA 2 expCycleAdj4_deg (by decide) 2 expC4_mu_le_two_QA
    {0, 2} {0, 2}
  rw [hcard, Fintype.card_fin] at h
  simpa using h

/-- The opposite cut's raw cut weight: no edges cross, everything
inside. -/
theorem exp_ew_02_02_QA :
    edgeWeight expCycleAdj4 ({0, 2} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4)) = 0 := by
  simp [edgeWeight, expCycleAdj4]

/-- **Sharpness witness: the bound is attained on the opposite cut.**
Both sides of the mixing bound compute, independently of the theorem,
to `2`: the deviation `|0 − 2|` and the geometric factor
`2 • √16 / 4`. The derived `μ = 2` is tight on this fixture — the
theorem is not vacuous. -/
theorem exp_eml_opposite_sharp_QA :
    |edgeWeight expCycleAdj4 ({0, 2} : Finset (Fin 4)) ({0, 2} : Finset (Fin 4))
      - 2 * 2 * 2 / (4:ℝ)| =
      2 * Real.sqrt ((2:ℝ) * 2 * ((4:ℝ) - 2) * ((4:ℝ) - 2)) / 4 := by
  have hs : Real.sqrt ((2:ℝ) * 2 * ((4:ℝ) - 2) * ((4:ℝ) - 2)) = 4 := by
    have h : (2:ℝ) * 2 * ((4:ℝ) - 2) * ((4:ℝ) - 2) = 4 * 4 := by norm_num
    rw [h, Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 4)]
  rw [exp_ew_02_02_QA, hs]
  norm_num

/-- **The mixing lemma instantiated: half cut.** On `({0,1}, {0,1})`
the cut weight meets the main term exactly, deviation `0`. -/
theorem exp_eml_adjacent_QA :
    |edgeWeight expCycleAdj4 ({0, 1} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4))
      - 2 * 2 * 2 / (4:ℝ)| ≤
      2 * Real.sqrt ((2:ℝ) * 2 * ((4:ℝ) - 2) * ((4:ℝ) - 2)) / 4 := by
  have hcard : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  have h := expander_mixing_lemma expCycleAdj4 expCycleAdj4_isSymm
    expC4_nonneg_QA 2 expCycleAdj4_deg (by decide) 2 expC4_mu_le_two_QA
    {0, 1} {0, 1}
  rw [hcard, Fintype.card_fin] at h
  simpa using h

theorem exp_ew_01_01_QA :
    edgeWeight expCycleAdj4 ({0, 1} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4)) = 2 := by
  simp [edgeWeight, expCycleAdj4]
  norm_num

/-- The half cut's deviation computes to zero — the population main
term is exact on this cut (computed independently of the lemma). -/
theorem exp_eml_adjacent_deviation_QA :
    |edgeWeight expCycleAdj4 ({0, 1} : Finset (Fin 4)) ({0, 1} : Finset (Fin 4))
      - 2 * 2 * 2 / (4:ℝ)| = 0 := by
  rw [exp_ew_01_01_QA]
  norm_num

/-- **Bridge sharpness witness.** The alternating vector attains
equality in the operator bound on `1⊥`: `|xᵀAx| = 8 = 2 ‖x‖²` —
the `λ_max` direction of the sandwich is tight. Computed from the raw
definitions. -/
theorem exp_bridge_alternating_sharp_QA :
    |quadForm expCycleAdj4 ![1, -1, 1, -1]| =
      2 * Matrix.dotProduct (![1, -1, 1, -1] : Fin 4 → ℝ) ![1, -1, 1, -1] := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, expCycleAdj4,
    Matrix.of_apply, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.vecTail, Matrix.vecHead]
  norm_num

/-- **Norm fact instantiated.** The centered indicator of the half cut
has squared norm `1` — computed from the pinned entries `±1/2`, and
equal to `|S|(n−|S|)/n = 2·2/4` as `dotProduct_centeredIndicator_self`
states. -/
theorem exp_centered_norm_half_QA :
    centeredIndicator ({0, 1} : Finset (Fin 4)) ⬝ᵥ
      centeredIndicator ({0, 1} : Finset (Fin 4)) = 1 := by
  rw [exp_centered_pair_QA]
  simp only [Matrix.dotProduct, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.vecTail, Matrix.vecHead]
  norm_num

theorem exp_centered_norm_eq_variance_QA :
    centeredIndicator ({0, 1} : Finset (Fin 4)) ⬝ᵥ
      centeredIndicator ({0, 1} : Finset (Fin 4)) =
      (2:ℝ) * ((4:ℝ) - 2) / 4 := by
  rw [exp_centered_norm_half_QA]
  norm_num

end SpectralGraphTheory.QA
