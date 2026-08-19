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
  - *Step 4: exact spectrum pins and the Ramanujan fixture family.*
    The bounds become equalities: a Poincaré inequality on `C₄`
    (`2‖x‖² ≤ xᵀLx` for `x ⊥ 1`, by the identity
    `E = 2Σx² + 2(x₀+x₂)²` under `Σx = 0`) pins `λ₂(C₄) = 2` through
    the *lower* half of `lambda2_variational` (`le_csInf` — the
    constraint set is universally bounded below), and the alternating
    eigenvector pins `λ_max(C₄) = 4`, so `μ(C₄) = 2` *exactly* — the
    Ramanujan bound `2√(d−1)` is attained with equality. The complete
    graph `K₃` carries an *identity* `xᵀLx = 3‖x‖² − (Σx)²` (both the
    Poincaré inequality and its converse scaling at once), pinning
    `λ₂ = λ_max = 3`, `μ(K₃) = 1` — strictly Ramanujan — with the EML
    *attained exactly* on two cuts. The six-cycle `C₆` gets its EML
    instance with a derived `μ ≤ 2` (test vector, per-edge estimate,
    PSD), attained with equality on the alternating cut
    `({0,2,4}, {0,2,4})`.

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

/-!
## Step 4: exact spectrum pins on `C₄` — Poincaré, `λ₂ = 2`,
`λ_max = 4`, `μ = 2` at Ramanujan equality

The derived spectral hypothesis above used bounds. The pins below make
`μ(C₄)` itself exact, and the Ramanujan bound `μ ≤ 2√(d−1)` (with
`d = 2`) is *attained with equality* — `C₄` is an exactly-Ramanujan
fixture, checkable against `lambda2` and `evals` directly rather than
through bounds.
-/


/-- **The `C₄` Poincaré inequality** (exact lower half of the
spectrum): every vector orthogonal to `onesVec` has Laplacian energy at
least twice its squared norm. Proof: the Dirichlet sum evaluates to
`E = 2Σx² + 2(x₀+x₂)²` under `Σx = 0` (the cross term
`(x₀+x₂)(x₁+x₃)` collapses to `−(x₀+x₂)²`), so the excess is a
square. This is the `n = 4` instance of the discrete Wirtinger
inequality, the named absent item of radar axis 3 — proved here on a
fixture, not in general. -/
theorem expC4_poincare_QA (x : Fin 4 → ℝ)
    (hxorth : Matrix.dotProduct x onesVec = 0) :
    2 * (x ⬝ᵥ x) ≤ quadForm (laplacian expCycleAdj4) x := by
  have hsum : x 0 + x 1 + x 2 + x 3 = 0 := by
    have h := hxorth
    simp only [Matrix.dotProduct, onesVec, Fin.sum_univ_four, mul_one] at h
    exact h
  have hnorm : x ⬝ᵥ x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_four]
  have hedges : (∑ i, ∑ j, expCycleAdj4 i j * (x i - x j) ^ 2)
      = 2 * ((x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 2 - x 3) ^ 2
        + (x 3 - x 0) ^ 2) := by
    simp only [expCycleAdj4, Matrix.of_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
    ring
  have hkey : (x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 2 - x 3) ^ 2
      + (x 3 - x 0) ^ 2
      = 2 * (x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3)
        + 2 * (x 0 + x 2) ^ 2 := by
    linear_combination (-(2:ℝ) * (x 0 + x 2)) * hsum
  rw [laplacian_quadForm expCycleAdj4 expCycleAdj4_isSymm, hedges, hkey, hnorm]
  linarith [sq_nonneg (x 0 + x 2)]

/-- **`λ₂(C₄)` pinned from below** through the *lower* half of
`lambda2_variational`: every constraint-set member has Rayleigh
quotient ≥ 2 (Poincaré), and the set is nonempty — so the infimum is
≥ 2. This is the first QA consumer of the variational characterization
in the `≥` direction. -/
theorem expC4_lambda2_ge_two_QA :
    2 ≤ lambda2 expCycleAdj4 expCycleAdj4_isSymm (by decide) := by
  have hx0 : (![1, 0, -1, 0] : Fin 4 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, 0, -1, 0] : Fin 4 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have hxorth : Matrix.dotProduct (![1, 0, -1, 0] : Fin 4 → ℝ) onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.vecTail, Matrix.vecHead]
    norm_num
  have hray : rayleigh (laplacian expCycleAdj4) (![1, 0, -1, 0] : Fin 4 → ℝ)
      = 2 := by
    rw [rayleigh, if_neg hx0, expC4_quadForm_10m10_QA, expC4_dot_10m10_QA]
    norm_num
  rw [lambda2_variational expCycleAdj4 expCycleAdj4_isSymm
    expC4_nonneg_QA (by decide)]
  refine le_csInf ⟨(2:ℝ), ![1, 0, -1, 0], hx0, hxorth, hray⟩ ?_
  rintro r ⟨y, hy0, hyorth, hyr⟩
  rw [← hyr, rayleigh, if_neg hy0]
  exact (le_div_iff₀ (dotProduct_self_pos hy0)).2 (expC4_poincare_QA y hyorth)

/-- **The exact pin: `λ₂(C₄) = 2`.** Upper bound from the test vector
(above), lower bound from Poincaré — the value the certificate QA
certifies is the true algebraic connectivity, not just an upper bound. -/
theorem expC4_lambda2_eq_two_QA :
    lambda2 expCycleAdj4 expCycleAdj4_isSymm (by decide) = 2 :=
  le_antisymm expC4_lambda2_le_two_QA expC4_lambda2_ge_two_QA

theorem expC4_quadForm_alt_QA :
    quadForm (laplacian expCycleAdj4) ![1, -1, 1, -1] = 16 := by
  rw [laplacian_quadForm expCycleAdj4 expCycleAdj4_isSymm]
  simp only [expCycleAdj4, Matrix.of_apply, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  norm_num [sub_sq]

theorem expC4_dot_alt_QA :
    Matrix.dotProduct (![1, -1, 1, -1] : Fin 4 → ℝ) ![1, -1, 1, -1] = 4 := by
  simp only [Matrix.dotProduct, Fin.sum_univ_four,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  norm_num

/-- **`λ_max(C₄)` pinned from below**: the alternating vector has
Rayleigh quotient `16/4 = 4`, and the generic top domination
`quadForm_le_evals_last` forces `λ_max ≥ 4`. -/
theorem expC4_evals_last_ge_four_QA :
    4 ≤ evals (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
        ⟨Fintype.card (Fin 4) - 1, by decide⟩ := by
  have h := quadForm_le_evals_last
    (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
    (by decide) (![1, -1, 1, -1] : Fin 4 → ℝ)
  rw [expC4_quadForm_alt_QA, expC4_dot_alt_QA] at h
  linarith

/-- **The exact pin: `λ_max(C₄) = 4`** — the sum-of-squares upper bound
above, the alternating-vector lower bound here. -/
theorem expC4_evals_last_eq_four_QA :
    evals (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
        ⟨Fintype.card (Fin 4) - 1, by decide⟩ = 4 :=
  le_antisymm expC4_evals_last_le_four_QA expC4_evals_last_ge_four_QA

/-- **`μ(C₄) = 2` exactly** (not merely ≤ 2 as the derived hypothesis
above needed): the Laplacian endpoints are `λ₂ = 2`, `λ_max = 4`, so
`max |2−2| |2−4| = 2`. -/
theorem expC4_mu_eq_two_QA :
    max |2 - lambda2 expCycleAdj4 expCycleAdj4_isSymm (by norm_num)|
        |2 - evals (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
            ⟨Fintype.card (Fin 4) - 1, by decide⟩| = 2 := by
  rw [expC4_lambda2_eq_two_QA, expC4_evals_last_eq_four_QA]
  norm_num

/-- **`C₄` is exactly Ramanujan:** `μ(C₄) = 2 = 2√(d−1)` with
`d = 2` — the Ramanujan bound is *attained*, at both endpoints of the
admissible range (`K₃` below sits strictly inside it). -/
theorem expC4_ramanujan_eq_QA :
    max |2 - lambda2 expCycleAdj4 expCycleAdj4_isSymm (by norm_num)|
        |2 - evals (laplacian_symmetric expCycleAdj4 expCycleAdj4_isSymm)
            ⟨Fintype.card (Fin 4) - 1, by decide⟩|
      = 2 * Real.sqrt ((2:ℝ) - 1) := by
  have hone : ((2:ℝ) - 1) = 1 := by norm_num
  rw [expC4_mu_eq_two_QA, hone, Real.sqrt_one]
  norm_num

/-!
## Step 4: the complete graph `K₃` — an identity for the energy,
`λ₂ = λ_max = 3`, `μ = 1`, and the EML attained on two cuts
-/


/-- Adjacency of the complete graph `K₃` on `Fin 3`: symmetric, unit
weights off the diagonal, all degrees `2` (`d`-regular; `K₃` is also
the triangle cycle `C₃`). -/
def expK3Adj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 1; 1, 0, 1; 1, 1, 0]

/-- Entry table for the clique: `0` on the diagonal, `1` off it. The
`fin_cases`-grounded statement avoids matrix-literal evaluation issues
at higher indices (entries are `rfl`). -/
theorem expK3Adj_apply (i j : Fin 3) :
    expK3Adj i j = if i = j then 0 else 1 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem expK3Adj_isSymm : expK3Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [expK3Adj_apply, expK3Adj_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem expK3Adj_nonneg_QA : ∀ i j, 0 ≤ expK3Adj i j := by
  intro i j
  rw [expK3Adj_apply]
  split <;> norm_num

theorem expK3Adj_deg (i : Fin 3) : deg expK3Adj i = 2 := by
  rw [deg]
  fin_cases i <;> simp [expK3Adj_apply, Fin.sum_univ_three] <;> norm_num

/-- **The `K₃` energy identity**: the Laplacian quadratic form is
exactly `3‖x‖² − (Σx)²` — the `n = 3` instance of the general identity
`xᵀL(Kₙ)x = n‖x‖² − (Σx)²`. This single identity carries both the
Poincaré inequality (drop the square at `Σx = 0`) and the top bound
(the square is nonnegative) — the whole spectrum of `K₃` follows. -/
theorem expK3_quadForm_identity_QA (x : Fin 3 → ℝ) :
    quadForm (laplacian expK3Adj) x
      = 3 * (x ⬝ᵥ x) - (x 0 + x 1 + x 2) ^ 2 := by
  have hedges : (∑ i, ∑ j, expK3Adj i j * (x i - x j) ^ 2)
      = 2 * ((x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 2 - x 0) ^ 2) := by
    simp only [expK3Adj, Matrix.of_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hnorm : x ⬝ᵥ x = x 0 * x 0 + x 1 * x 1 + x 2 * x 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_three]
  rw [laplacian_quadForm expK3Adj expK3Adj_isSymm, hedges, hnorm]
  ring

/-- **The `K₃` Poincaré inequality is an equality**: for `x ⊥ 1` the
energy is exactly `3‖x‖²` — no slack in either direction. -/
theorem expK3_quadForm_of_ortho_QA (x : Fin 3 → ℝ)
    (hxorth : Matrix.dotProduct x onesVec = 0) :
    quadForm (laplacian expK3Adj) x = 3 * (x ⬝ᵥ x) := by
  have hsum : x 0 + x 1 + x 2 = 0 := by
    have h := hxorth
    simp only [Matrix.dotProduct, onesVec, Fin.sum_univ_three, mul_one] at h
    exact h
  rw [expK3_quadForm_identity_QA, hsum]
  ring

/-- The unconditional top bound (drop the square from the identity). -/
theorem expK3_quadForm_le_three_QA (x : Fin 3 → ℝ) :
    quadForm (laplacian expK3Adj) x ≤ 3 * (x ⬝ᵥ x) := by
  rw [expK3_quadForm_identity_QA]
  nlinarith [sq_nonneg (x 0 + x 1 + x 2)]

/-- The test vector's Rayleigh quotient computes to `3` — the exact
spectrum value, from the orthogonality identity. -/
theorem expK3_rayleigh_testvec_QA :
    rayleigh (laplacian expK3Adj) (![1, -1, 0] : Fin 3 → ℝ) = 3 := by
  have hx0 : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, -1, 0] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have hxorth : Matrix.dotProduct (![1, -1, 0] : Fin 3 → ℝ) onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.vecTail, Matrix.vecHead]
    norm_num
  have hdot : Matrix.dotProduct (![1, -1, 0] : Fin 3 → ℝ) ![1, -1, 0] = 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.vecTail, Matrix.vecHead]
    norm_num
  rw [rayleigh, if_neg hx0, expK3_quadForm_of_ortho_QA _ hxorth, hdot]
  norm_num

/-- **The exact pin: `λ₂(K₃) = 3`.** Upper bound from the test vector's
quotient, lower bound from the Poincaré equality through
`lambda2_variational`'s `le_csInf` direction. -/
theorem expK3_lambda2_eq_three_QA :
    lambda2 expK3Adj expK3Adj_isSymm (by decide) = 3 := by
  have hx0 : (![1, -1, 0] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, -1, 0] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have hxorth : Matrix.dotProduct (![1, -1, 0] : Fin 3 → ℝ) onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.vecTail, Matrix.vecHead]
    norm_num
  refine le_antisymm ?_ ?_
  · have h := secondEval_le_rayleigh
      (laplacian_symmetric expK3Adj expK3Adj_isSymm)
      (laplacian_psd expK3Adj expK3Adj_isSymm expK3Adj_nonneg_QA)
      (laplacian_ones_in_kernel expK3Adj) (by decide) hx0 hxorth
    rw [lambda2_eq_secondEval]
    rw [expK3_rayleigh_testvec_QA] at h
    exact h
  · rw [lambda2_variational expK3Adj expK3Adj_isSymm
      expK3Adj_nonneg_QA (by decide)]
    refine le_csInf ⟨(3:ℝ), ![1, -1, 0], hx0, hxorth,
      expK3_rayleigh_testvec_QA⟩ ?_
    rintro r ⟨y, hy0, hyorth, hyr⟩
    rw [← hyr, rayleigh, if_neg hy0]
    exact (le_div_iff₀ (dotProduct_self_pos hy0)).2
      (expK3_quadForm_of_ortho_QA y hyorth).symm.le

theorem expK3_evals_last_le_three_QA :
    evals (laplacian_symmetric expK3Adj expK3Adj_isSymm)
        ⟨Fintype.card (Fin 3) - 1, by decide⟩ ≤ 3 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric expK3Adj expK3Adj_isSymm)
    ⟨Fintype.card (Fin 3) - 1, by decide⟩
  rw [hi, ← quadForm_eigvecOf_self]
  have hunit : Matrix.dotProduct
      (eigvecOf (laplacian expK3Adj)
        (laplacian_symmetric expK3Adj expK3Adj_isSymm) i)
      (eigvecOf (laplacian expK3Adj)
        (laplacian_symmetric expK3Adj expK3Adj_isSymm) i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner
      (laplacian expK3Adj)
      (laplacian_symmetric expK3Adj expK3Adj_isSymm) i i
  have hle := expK3_quadForm_le_three_QA
    (eigvecOf (laplacian expK3Adj)
      (laplacian_symmetric expK3Adj expK3Adj_isSymm) i)
  rw [hunit] at hle
  linarith

/-- **The exact pin: `λ_max(K₃) = 3`** — sortedness against
`λ₂ = 3` from below, the estimate above from above. -/
theorem expK3_evals_last_eq_three_QA :
    evals (laplacian_symmetric expK3Adj expK3Adj_isSymm)
        ⟨Fintype.card (Fin 3) - 1, by decide⟩ = 3 := by
  refine le_antisymm expK3_evals_last_le_three_QA ?_
  have hle : (⟨1, by decide⟩ : Fin 3)
      ≤ ⟨Fintype.card (Fin 3) - 1, by decide⟩ := by decide
  have h := evals_sorted (laplacian_symmetric expK3Adj expK3Adj_isSymm) hle
  have h2 : (3:ℝ) = lambda2 expK3Adj expK3Adj_isSymm (by decide) :=
    expK3_lambda2_eq_three_QA.symm
  rw [h2]
  exact h

/-- **`μ(K₃) = 1` exactly**: both Laplacian endpoints sit at `3`, so
`max |2−3| |2−3| = 1` — the classical `μ(Kₙ) = 1` at `n = 3`. -/
theorem expK3_mu_eq_one_QA :
    max |2 - lambda2 expK3Adj expK3Adj_isSymm (by norm_num)|
        |2 - evals (laplacian_symmetric expK3Adj expK3Adj_isSymm)
            ⟨Fintype.card (Fin 3) - 1, by decide⟩| = 1 := by
  rw [expK3_lambda2_eq_three_QA, expK3_evals_last_eq_three_QA]
  norm_num

/-- **`K₃` is Ramanujan, strictly:** `μ(K₃) = 1 < 2 = 2√(d−1)` with
`d = 2` — the complete graphs' classical Ramanujan property at `n = 3`,
with slack. -/
theorem expK3_ramanujan_QA :
    max |2 - lambda2 expK3Adj expK3Adj_isSymm (by norm_num)|
        |2 - evals (laplacian_symmetric expK3Adj expK3Adj_isSymm)
            ⟨Fintype.card (Fin 3) - 1, by decide⟩|
      ≤ 2 * Real.sqrt ((2:ℝ) - 1) := by
  have hone : ((2:ℝ) - 1) = 1 := by norm_num
  rw [hone, Real.sqrt_one, expK3_mu_eq_one_QA]
  norm_num

theorem expK3_mu_le_one_QA :
    max |2 - lambda2 expK3Adj expK3Adj_isSymm (by norm_num)|
        |2 - evals (laplacian_symmetric expK3Adj expK3Adj_isSymm)
            ⟨Fintype.card (Fin 3) - 1, by decide⟩| ≤ 1 :=
  le_of_eq expK3_mu_eq_one_QA

/-- **The mixing lemma instantiated on `K₃`: singleton cut.** With the
exact `μ = 1`, the deviation bound on `({0}, {0})`. -/
theorem expK3_eml_singleton_QA :
    |edgeWeight expK3Adj ({0} : Finset (Fin 3)) ({0} : Finset (Fin 3))
      - 2 * 1 * 1 / (3:ℝ)| ≤
      1 * Real.sqrt ((1:ℝ) * 1 * ((3:ℝ) - 1) * ((3:ℝ) - 1)) / 3 := by
  have hcard : ({0} : Finset (Fin 3)).card = 1 := by decide
  have h := expander_mixing_lemma expK3Adj expK3Adj_isSymm
    expK3Adj_nonneg_QA 2 expK3Adj_deg (by decide) 1 expK3_mu_le_one_QA {0} {0}
  rw [hcard, Fintype.card_fin] at h
  simpa using h

/-- The singleton cut's raw cut weight: the diagonal is zero — no
self-edges. -/
theorem expK3_ew_singleton_QA :
    edgeWeight expK3Adj ({0} : Finset (Fin 3)) ({0} : Finset (Fin 3)) = 0 := by
  simp [edgeWeight, expK3Adj]

/-- **Sharpness witness: the bound is attained on the singleton cut.**
Both sides independently compute to `2/3`: the deviation
`|0 − 2/3|` and the geometric factor `1 • √4 / 3`. -/
theorem expK3_eml_singleton_sharp_QA :
    |edgeWeight expK3Adj ({0} : Finset (Fin 3)) ({0} : Finset (Fin 3))
      - 2 * 1 * 1 / (3:ℝ)| =
      1 * Real.sqrt ((1:ℝ) * 1 * ((3:ℝ) - 1) * ((3:ℝ) - 1)) / 3 := by
  have hs : Real.sqrt ((1:ℝ) * 1 * ((3:ℝ) - 1) * ((3:ℝ) - 1)) = 2 := by
    have h : (1:ℝ) * 1 * ((3:ℝ) - 1) * ((3:ℝ) - 1) = 2 * 2 := by norm_num
    rw [h, Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
  rw [expK3_ew_singleton_QA, hs]
  norm_num

/-- **The mixing lemma instantiated on `K₃`: the edge cut.** On
`({0,1}, {0,1})` the cut weight `2` meets the main term `8/3` — the
deviation is `2/3`. -/
theorem expK3_eml_edge_QA :
    |edgeWeight expK3Adj ({0, 1} : Finset (Fin 3)) ({0, 1} : Finset (Fin 3))
      - 2 * 2 * 2 / (3:ℝ)| ≤
      1 * Real.sqrt ((2:ℝ) * 2 * ((3:ℝ) - 2) * ((3:ℝ) - 2)) / 3 := by
  have hcard : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have h := expander_mixing_lemma expK3Adj expK3Adj_isSymm
    expK3Adj_nonneg_QA 2 expK3Adj_deg (by decide) 1 expK3_mu_le_one_QA
    ({0, 1} : Finset (Fin 3)) {0, 1}
  rw [hcard, Fintype.card_fin] at h
  simpa using h

theorem expK3_ew_edge_QA :
    edgeWeight expK3Adj ({0, 1} : Finset (Fin 3)) ({0, 1} : Finset (Fin 3))
      = 2 := by
  simp [edgeWeight, expK3Adj]
  norm_num

/-- **Sharpness witness: the bound is attained on the edge cut too** —
both sides compute to `2/3`. On `K₃` *every* nontrivial cut attains the
EML bound exactly. -/
theorem expK3_eml_edge_sharp_QA :
    |edgeWeight expK3Adj ({0, 1} : Finset (Fin 3)) ({0, 1} : Finset (Fin 3))
      - 2 * 2 * 2 / (3:ℝ)| =
      1 * Real.sqrt ((2:ℝ) * 2 * ((3:ℝ) - 2) * ((3:ℝ) - 2)) / 3 := by
  have hs : Real.sqrt ((2:ℝ) * 2 * ((3:ℝ) - 2) * ((3:ℝ) - 2)) = 2 := by
    have h : (2:ℝ) * 2 * ((3:ℝ) - 2) * ((3:ℝ) - 2) = 2 * 2 := by norm_num
    rw [h, Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
  rw [expK3_ew_edge_QA, hs]
  norm_num

/-!
## Step 4: the six-cycle `C₆` — EML with derived `μ ≤ 2`, attained on
the alternating cut

The exact `C₄`-style pins are not available here (the `C₆` Poincaré
constant is the genuinely nonlinear Wirtinger inequality), but the EML
hypothesis `μ ≤ 2` needs only bounds: `λ₂ ≤ 1` from the certificate
test vector, both endpoints in `[0, 4]` from PSD and a per-edge
estimate. The Ramanujan inequality `μ ≤ 2√(d−1)` then holds (not at
equality — that would need the exact pins).
-/

/-- Matrix-literal entry evaluation at index `5` of a `Fin 6` vector:
the `cons_val` simp family stops at four, and this step is
`rfl`-reducible but not syntactically matched by `simp only`. -/
private theorem vecCons_val_five {α : Type} (x : α) (u : Fin 5 → α) :
    Matrix.vecCons x u (5 : Fin 6) = u (4 : Fin 5) := rfl


/-- Adjacency of the cycle `C₆` on `Fin 6`: symmetric, unit weights,
all degrees `2`. -/
def expCycleAdj6 : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of !![0, 1, 0, 0, 0, 1; 1, 0, 1, 0, 0, 0; 0, 1, 0, 1, 0, 0;
               0, 0, 1, 0, 1, 0; 0, 0, 0, 1, 0, 1; 1, 0, 0, 0, 1, 0]

/-- Entry table for the cycle: unit weight exactly on the cyclically
adjacent pairs. `fin_cases`-grounded (entries and the decidable
condition are `rfl`). -/
theorem expCycleAdj6_apply (i j : Fin 6) :
    expCycleAdj6 i j =
      if ((i.val + 1) % 6 = j.val ∨ (j.val + 1) % 6 = i.val) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> rfl

theorem expCycleAdj6_isSymm : expCycleAdj6.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [expCycleAdj6_apply, expCycleAdj6_apply]
  simp [or_comm]

theorem expCycleAdj6_nonneg_QA : ∀ i j, 0 ≤ expCycleAdj6 i j := by
  intro i j
  rw [expCycleAdj6_apply]
  split <;> norm_num

theorem expCycleAdj6_deg (i : Fin 6) : deg expCycleAdj6 i = 2 := by
  rw [deg]
  fin_cases i
  · show ∑ j, (![0, 1, 0, 0, 0, 1] : Fin 6 → ℝ) j = 2
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, vecCons_val_five]
    norm_num
  · show ∑ j, (![1, 0, 1, 0, 0, 0] : Fin 6 → ℝ) j = 2
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, vecCons_val_five]
    norm_num
  · show ∑ j, (![0, 1, 0, 1, 0, 0] : Fin 6 → ℝ) j = 2
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, vecCons_val_five]
    norm_num
  · show ∑ j, (![0, 0, 1, 0, 1, 0] : Fin 6 → ℝ) j = 2
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, vecCons_val_five]
    norm_num
  · show ∑ j, (![0, 0, 0, 1, 0, 1] : Fin 6 → ℝ) j = 2
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, vecCons_val_five]
    norm_num
  · show ∑ j, (![1, 0, 0, 0, 1, 0] : Fin 6 → ℝ) j = 2
    simp only [Fin.sum_univ_six, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, vecCons_val_five]
    norm_num

theorem expC6_quadForm_testvec_QA :
    quadForm (laplacian expCycleAdj6) ![1, 1, 0, -1, -1, 0] = 4 := by
  rw [laplacian_quadForm expCycleAdj6 expCycleAdj6_isSymm]
  simp only [expCycleAdj6, Matrix.of_apply, Fin.sum_univ_six,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, vecCons_val_five, sub_sq]
  norm_num

theorem expC6_dot_testvec_QA :
    Matrix.dotProduct (![1, 1, 0, -1, -1, 0] : Fin 6 → ℝ)
      ![1, 1, 0, -1, -1, 0] = 4 := by
  simp only [Matrix.dotProduct, Fin.sum_univ_six,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, vecCons_val_five]
  norm_num

/-- **`λ₂(C₆) ≤ 1` from the certificate test vector** — the same
`![1, 1, 0, −1, −1, 0]` whose integer twin the certificate QA
kernel-decides. -/
theorem expC6_lambda2_le_one_QA :
    lambda2 expCycleAdj6 expCycleAdj6_isSymm (by decide) ≤ 1 := by
  have hx0 : (![1, 1, 0, -1, -1, 0] : Fin 6 → ℝ) ≠ 0 := by
    intro h
    have h0 : (![1, 1, 0, -1, -1, 0] : Fin 6 → ℝ) 0 = 0 := congrFun h 0
    simp at h0
  have hxorth : Matrix.dotProduct (![1, 1, 0, -1, -1, 0] : Fin 6 → ℝ)
      onesVec = 0 := by
    simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, vecCons_val_five]
    norm_num
  have h := secondEval_le_rayleigh
    (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm)
    (laplacian_psd expCycleAdj6 expCycleAdj6_isSymm expCycleAdj6_nonneg_QA)
    (laplacian_ones_in_kernel expCycleAdj6) (by decide) hx0 hxorth
  rw [lambda2_eq_secondEval]
  unfold rayleigh at h
  rw [if_neg hx0, expC6_quadForm_testvec_QA, expC6_dot_testvec_QA] at h
  linarith

theorem expC6_eigvalOf_nonneg_QA (i : Fin 6) :
    0 ≤ eigvalOf (laplacian expCycleAdj6)
        (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm) i := by
  rw [← quadForm_eigvecOf_self]
  exact laplacian_psd expCycleAdj6 expCycleAdj6_isSymm
    expCycleAdj6_nonneg_QA (eigvecOf _ _ i)

theorem expC6_lambda2_nonneg_QA :
    0 ≤ lambda2 expCycleAdj6 expCycleAdj6_isSymm (by decide) := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm) ⟨1, by decide⟩
  show 0 ≤ evals (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm)
    ⟨1, by decide⟩
  rw [hi]
  exact expC6_eigvalOf_nonneg_QA i

theorem expC6_evals_last_nonneg_QA :
    0 ≤ evals (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm)
        ⟨Fintype.card (Fin 6) - 1, by decide⟩ := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm)
    ⟨Fintype.card (Fin 6) - 1, by decide⟩
  rw [hi]
  exact expC6_eigvalOf_nonneg_QA i

/-- **The `C₆` energy identity**: the Dirichlet energy is exactly
`4‖x‖² − Σ_edges (xᵢ + xᵢ₊₁)²` — the six `(a+b)²` terms carry the
entire deviation from the top bound. -/
theorem expC6_quadForm_eq_four_sub_QA (x : Fin 6 → ℝ) :
    quadForm (laplacian expCycleAdj6) x
      = 4 * (x ⬝ᵥ x) - ((x 0 + x 1) ^ 2 + (x 1 + x 2) ^ 2
        + (x 2 + x 3) ^ 2 + (x 3 + x 4) ^ 2 + (x 4 + x 5) ^ 2
        + (x 5 + x 0) ^ 2) := by
  have hedges : (∑ i, ∑ j, expCycleAdj6 i j * (x i - x j) ^ 2)
      = 2 * ((x 0 - x 1) ^ 2 + (x 1 - x 2) ^ 2 + (x 2 - x 3) ^ 2
        + (x 3 - x 4) ^ 2 + (x 4 - x 5) ^ 2 + (x 5 - x 0) ^ 2) := by
    simp only [expCycleAdj6, Matrix.of_apply, Fin.sum_univ_six,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
      Matrix.tail_cons, vecCons_val_five]
    ring
  have hnorm : x ⬝ᵥ x = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 + x 4 ^ 2
      + x 5 ^ 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_six, pow_two]
  rw [laplacian_quadForm expCycleAdj6 expCycleAdj6_isSymm, hedges, hnorm]
  ring

theorem expC6_quadForm_le_four_QA (x : Fin 6 → ℝ) :
    quadForm (laplacian expCycleAdj6) x ≤ 4 * (x ⬝ᵥ x) := by
  have h1 : (0:ℝ) ≤ (x 0 + x 1) ^ 2 := sq_nonneg _
  have h2 : (0:ℝ) ≤ (x 1 + x 2) ^ 2 := sq_nonneg _
  have h3 : (0:ℝ) ≤ (x 2 + x 3) ^ 2 := sq_nonneg _
  have h4 : (0:ℝ) ≤ (x 3 + x 4) ^ 2 := sq_nonneg _
  have h5 : (0:ℝ) ≤ (x 4 + x 5) ^ 2 := sq_nonneg _
  have h6 : (0:ℝ) ≤ (x 5 + x 0) ^ 2 := sq_nonneg _
  rw [expC6_quadForm_eq_four_sub_QA]
  linarith

theorem expC6_evals_last_le_four_QA :
    evals (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm)
        ⟨Fintype.card (Fin 6) - 1, by decide⟩ ≤ 4 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm)
    ⟨Fintype.card (Fin 6) - 1, by decide⟩
  rw [hi, ← quadForm_eigvecOf_self]
  have hunit : Matrix.dotProduct
      (eigvecOf (laplacian expCycleAdj6)
        (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm) i)
      (eigvecOf (laplacian expCycleAdj6)
        (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm) i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner
      (laplacian expCycleAdj6)
      (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm) i i
  have hle := expC6_quadForm_le_four_QA
    (eigvecOf (laplacian expCycleAdj6)
      (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm) i)
  rw [hunit] at hle
  linarith

/-- **The derived spectral hypothesis on `C₆`: `μ ≤ 2`** — assembled
from the test-vector bound, PSD, and the per-edge estimate (no exact
pins needed for the EML). -/
theorem expC6_mu_le_two_QA :
    max |2 - lambda2 expCycleAdj6 expCycleAdj6_isSymm (by norm_num)|
        |2 - evals (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm)
            ⟨Fintype.card (Fin 6) - 1, by decide⟩| ≤ 2 := by
  have h2 := expC6_lambda2_le_one_QA
  have h2n := expC6_lambda2_nonneg_QA
  have hmax := expC6_evals_last_le_four_QA
  have hmaxn := expC6_evals_last_nonneg_QA
  exact max_le (abs_le.2 ⟨by linarith, by linarith⟩)
    (abs_le.2 ⟨by linarith, by linarith⟩)

/-- **`C₆` is Ramanujan:** `μ(C₆) ≤ 2 = 2√(d−1)` with `d = 2` (bounds
only; the exact equality `μ = 2` would need the `C₆` Wirtinger pins). -/
theorem expC6_ramanujan_QA :
    max |2 - lambda2 expCycleAdj6 expCycleAdj6_isSymm (by norm_num)|
        |2 - evals (laplacian_symmetric expCycleAdj6 expCycleAdj6_isSymm)
            ⟨Fintype.card (Fin 6) - 1, by decide⟩|
      ≤ 2 * Real.sqrt ((2:ℝ) - 1) := by
  have hone : ((2:ℝ) - 1) = 1 := by norm_num
  rw [hone, Real.sqrt_one]
  simpa using expC6_mu_le_two_QA

/-- **The mixing lemma instantiated on `C₆`: alternating cut.** With
the derived `μ ≤ 2`, the deviation bound on `({0,2,4}, {0,2,4})`. -/
theorem expC6_eml_alternating_QA :
    |edgeWeight expCycleAdj6 ({0, 2, 4} : Finset (Fin 6))
        ({0, 2, 4} : Finset (Fin 6)) - 2 * 3 * 3 / (6:ℝ)| ≤
      2 * Real.sqrt ((3:ℝ) * 3 * ((6:ℝ) - 3) * ((6:ℝ) - 3)) / 6 := by
  have hcard : ({0, 2, 4} : Finset (Fin 6)).card = 3 := by decide
  have h := expander_mixing_lemma expCycleAdj6 expCycleAdj6_isSymm
    expCycleAdj6_nonneg_QA 2 expCycleAdj6_deg (by decide) 2 expC6_mu_le_two_QA
    ({0, 2, 4} : Finset (Fin 6)) {0, 2, 4}
  rw [hcard, Fintype.card_fin] at h
  simpa using h

/-- The alternating cut's raw cut weight: every pair in
`{0,2,4} × {0,2,4}` is non-adjacent on the cycle. -/
theorem expC6_ew_alternating_QA :
    edgeWeight expCycleAdj6 ({0, 2, 4} : Finset (Fin 6))
        ({0, 2, 4} : Finset (Fin 6)) = 0 := by
  simp [edgeWeight, expCycleAdj6]

/-- **Sharpness witness: the bound is attained on the alternating
cut.** Both sides independently compute to `3`: the deviation
`|0 − 3|` and the geometric factor `2 • √81 / 6`. -/
theorem expC6_eml_alternating_sharp_QA :
    |edgeWeight expCycleAdj6 ({0, 2, 4} : Finset (Fin 6))
        ({0, 2, 4} : Finset (Fin 6)) - 2 * 3 * 3 / (6:ℝ)| =
      2 * Real.sqrt ((3:ℝ) * 3 * ((6:ℝ) - 3) * ((6:ℝ) - 3)) / 6 := by
  have hs : Real.sqrt ((3:ℝ) * 3 * ((6:ℝ) - 3) * ((6:ℝ) - 3)) = 9 := by
    have h : (3:ℝ) * 3 * ((6:ℝ) - 3) * ((6:ℝ) - 3) = 9 * 9 := by norm_num
    rw [h, Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 9)]
  rw [expC6_ew_alternating_QA, hs]
  norm_num

end SpectralGraphTheory.QA
