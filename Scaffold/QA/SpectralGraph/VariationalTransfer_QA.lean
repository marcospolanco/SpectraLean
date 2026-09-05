/-
  VariationalTransfer_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.VariationalTransfer`, the
  second consuming module of the `Normalized`/`Spectral` interfaces:
  quadratic-form and Rayleigh-quotient transfer through the congruence
  bridge, and PSD transfer, instantiated at the three-vertex path
  (degrees 1, 2, 1).

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated. QA does not prove any axiom's truth.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.QA.SpectralGraph.Normalized_QA
import Scaffold.QA.SpectralGraph.KernelBridge_QA
import Scaffold.QA.SpectralGraph.DegreeSandwich_QA
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The three-vertex path `0 — 1 — 2` (reused fixture)
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1). -/
def vtPathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem vtPathAdj_isSymm : vtPathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [vtPathAdj]

theorem vtPathAdj_deg_zero : deg vtPathAdj 0 = 1 := by
  simp only [deg, vtPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem vtPathAdj_deg_one : deg vtPathAdj 1 = 2 := by
  simp only [deg, vtPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem vtPathAdj_deg_two : deg vtPathAdj 2 = 1 := by
  simp only [deg, vtPathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem vtPathAdj_deg_pos (i : Fin 3) : 0 < deg vtPathAdj i := by
  fin_cases i <;>
    simp only [deg, vtPathAdj, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num

/-- Nonnegative weights of the path (unit, off-diagonal only). -/
theorem vtPathAdj_nonneg (i j : Fin 3) : 0 ≤ vtPathAdj i j := by
  fin_cases i <;> fin_cases j <;> simp [vtPathAdj]

/-- The alternating test vector `(1, -1, 1)`. -/
def vtAltVec : Fin 3 → ℝ :=
  ![1, -1, 1]

theorem vtAltVec_ne_zero : vtAltVec ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [vtAltVec] at h0

/-!
## Entrywise stretch and the degree-weighted denominator
-/

/-- The degree stretch computes entrywise at the path:
`√D y = (1, -√2, 1)` at the alternating vector. -/
theorem vt_degreeSqrt_mulVec_alt_QA :
    (degreeSqrt vtPathAdj *ᵥ vtAltVec) 1 = -(Real.sqrt 2) := by
  rw [degreeSqrt_mulVec, vtPathAdj_deg_one]
  norm_num [vtAltVec]

/-- The degree-weighted denominator computes to the total volume `4`:
`∑ deg i · y i² = 1 + 2 + 1`, evaluated through the transfer theorem
on one side and as a bare sum on the other. -/
theorem vt_degreeWeighted_denominator_QA :
    Matrix.dotProduct (degreeSqrt vtPathAdj *ᵥ vtAltVec)
        (degreeSqrt vtPathAdj *ᵥ vtAltVec) = 4 := by
  rw [dotProduct_degreeSqrt_mulVec vtPathAdj
    (fun i => le_of_lt (vtPathAdj_deg_pos i))]
  simp only [vtAltVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.sum_univ_three, vtPathAdj_deg_zero,
    vtPathAdj_deg_one, vtPathAdj_deg_two]
  norm_num

/-- The bare weighted sum also computes directly to `4` — the
denominator lemma's value agrees with the hand computation. -/
theorem vt_degreeWeighted_sum_direct_QA :
    ∑ i, deg vtPathAdj i * vtAltVec i * vtAltVec i = 4 := by
  simp only [vtAltVec, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Fin.sum_univ_three, vtPathAdj_deg_zero,
    vtPathAdj_deg_one, vtPathAdj_deg_two]
  norm_num

/-!
## The transferred Rayleigh quotient: the classical value `2`
-/

/-- The combinatorial numerator computes to `8` via the proved
Dirichlet identity: four directed edges each contributing
`(1-(-1))² = 4`, halved, doubled by the degree weighting — the exact
statement is the fully evaluated sum. -/
theorem vt_quadForm_laplacian_alt :
    quadForm (laplacian vtPathAdj) vtAltVec = 8 := by
  rw [laplacian_quadForm vtPathAdj vtPathAdj_isSymm vtAltVec]
  simp only [vtPathAdj, vtAltVec, Matrix.of_apply, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- **The headline transfer instantiates to the classical value.** At
the path, the normalized Rayleigh quotient of the stretched
alternating vector is `2` — the largest eigenvalue of the normalized
path Laplacian, computed here as `8 / 4` (transferred numerator over
degree-weighted denominator), not by any spectral theorem. A defect in
the congruence bridge, the stretch, or the denominator lemma would
move this value. -/
theorem vt_rayleigh_transfer_alt_QA :
    rayleigh (normalizedLaplacian vtPathAdj)
      (degreeSqrt vtPathAdj *ᵥ vtAltVec) = 2 := by
  rw [rayleigh_normalizedLaplacian_degreeSqrt vtPathAdj
    vtPathAdj_deg_pos vtAltVec_ne_zero, vt_quadForm_laplacian_alt,
    vt_degreeWeighted_sum_direct_QA]
  norm_num

/-- The transfer theorem recomposes: the combinatorial quadratic form
of the alternating vector equals the normalized quadratic form of the
stretched vector (both `8` when the latter is evaluated through the
congruence). -/
theorem vt_quadForm_transfer_QA :
    quadForm (laplacian vtPathAdj) vtAltVec
      = quadForm (normalizedLaplacian vtPathAdj)
          (degreeSqrt vtPathAdj *ᵥ vtAltVec) :=
  quadForm_laplacian_eq_quadForm_normalizedLaplacian vtPathAdj
    vtPathAdj_deg_pos vtAltVec

/-!
## PSD transfer
-/

/-- PSD transfer instantiates at two concrete vectors: the stretched
alternating vector and the first unit vector both have nonnegative
normalized quadratic form. -/
theorem vt_normalizedLaplacian_psd_QA :
    0 ≤ quadForm (normalizedLaplacian vtPathAdj)
        (degreeSqrt vtPathAdj *ᵥ vtAltVec)
      ∧ 0 ≤ quadForm (normalizedLaplacian vtPathAdj)
          (vtAltVec + ![0, 1, 0]) := by
  have hpsd : ∀ x : Fin 3 → ℝ,
      0 ≤ quadForm (normalizedLaplacian vtPathAdj) x :=
    normalizedLaplacian_psd vtPathAdj vtPathAdj_isSymm vtPathAdj_nonneg
      vtPathAdj_deg_pos
  exact ⟨hpsd _, hpsd _⟩

/-- PSD gives nonnegative Rayleigh quotients at nonzero vectors: at
the stretched alternating vector the quotient is exactly the positive
value `2`. -/
theorem vt_rayleigh_nonneg_QA :
    0 ≤ rayleigh (normalizedLaplacian vtPathAdj)
        (degreeSqrt vtPathAdj *ᵥ vtAltVec) := by
  rw [vt_rayleigh_transfer_alt_QA]
  norm_num

section TransferFences

/-! ### Shared numeric helpers and local fixtures -/

theorem vtf_sq_sqrt_two : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

theorem vtf_sqrt_two_ne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity

/-- `1/√2 = √2/2`, the rewriting that makes every `√2` entry
polynomial. -/
theorem vtf_inv_sqrt_two : ((Real.sqrt 2 : ℝ)⁻¹) = Real.sqrt 2 / 2 := by
  field_simp

/-- `√4 = 2` through the `sqrt_mul_self` route (norm_num's sqrt
extension does not fire under the stretch products). -/
theorem vtf_sqrt_four : Real.sqrt 4 = 2 := by
  rw [show (4 : ℝ) = 2 * 2 from by norm_num,
    Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)]

/-- The alternating mode is nonzero. -/
theorem vtf_alt_ne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

/-- The signed genuinely-`d = 2`-regular fixture: symmetric, degrees
`2 = 3 - 1 > 0`, one negative entry. -/
def vtSigAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![3, -1; -1, 3]

/-- The all-zero adjacency on `Fin 2`: symmetric, nonnegative, both
degrees `0`. -/
def vtZeroAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 0; 0, 0]

/-- The connected negative-cut fixture: symmetric, degrees
`(1, 2, 1)`, one negative entry, support the path `0—1—2`. -/
def vtNegCutAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![3, 1, -3; 1, 0, 1; -3, 1, 3]

theorem vtSigAdj_isSymm : vtSigAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem vtSigAdj_deg (i : Fin 2) : deg vtSigAdj i = 2 := by
  rcases nfFin2_cases i with rfl | rfl <;>
    simp only [deg, vtSigAdj, Matrix.of_apply, Fin.sum_univ_two]
  all_goals norm_num

theorem vtSigAdj_deg_pos (i : Fin 2) : 0 < deg vtSigAdj i := by
  rw [vtSigAdj_deg]; norm_num

theorem vtSigAdj_not_nonneg : ¬ (∀ i j : Fin 2, 0 ≤ vtSigAdj i j) := by
  intro h
  have h01 := h 0 1
  simp only [vtSigAdj, Matrix.of_apply] at h01
  norm_num at h01

/-- The signed regular fixture's normalized Laplacian, pinned. -/
theorem vtSigAdj_Lsym :
    normalizedLaplacian vtSigAdj = !![-1/2, 1/2; 1/2, -1/2] := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, vtSigAdj, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte]
  all_goals norm_num
  all_goals simp only [vtf_inv_sqrt_two, vtf_inv_sqrt_two]
  · linear_combination (-(3 : ℝ) / 4) * vtf_sq_sqrt_two
  · linear_combination (1 / 4 : ℝ) * vtf_sq_sqrt_two
  · linear_combination (1 / 4 : ℝ) * vtf_sq_sqrt_two
  · linear_combination (-(3 : ℝ) / 4) * vtf_sq_sqrt_two

/-- The alternating mode is an eigenvector at `-1`. -/
theorem vtSigAdj_Lsym_mulVec :
    normalizedLaplacian vtSigAdj *ᵥ (![1, -1] : Fin 2 → ℝ)
      = (-1 : ℝ) • ![1, -1] := by
  rw [vtSigAdj_Lsym]
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
  all_goals norm_num

theorem vtZeroAdj_isSymm : vtZeroAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem vtZeroAdj_nonneg (i j : Fin 2) : 0 ≤ vtZeroAdj i j := by
  fin_cases i <;> fin_cases j <;> simp [vtZeroAdj]

theorem vtZeroAdj_deg (i : Fin 2) : deg vtZeroAdj i = 0 := by
  rcases nfFin2_cases i with rfl | rfl <;>
    simp only [deg, vtZeroAdj, Matrix.of_apply, Fin.sum_univ_two]
  all_goals norm_num

theorem vtZeroAdj_not_pos_deg : ¬ (∀ i : Fin 2, 0 < deg vtZeroAdj i) := by
  intro h
  have h0 := h 0
  rw [vtZeroAdj_deg] at h0
  norm_num at h0

/-- The zero adjacency's degree square root vanishes identically. -/
theorem vtZeroAdj_degreeSqrt : degreeSqrt vtZeroAdj = 0 := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [degreeSqrt, Matrix.diagonal_apply, deg, vtZeroAdj,
      Matrix.of_apply, Fin.isValue, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Real.sqrt_zero, Matrix.zero_apply, add_zero]
  all_goals simp

/-- The zero adjacency's normalized Laplacian is the identity. -/
theorem vtZeroAdj_Lsym : normalizedLaplacian vtZeroAdj = 1 := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, vtZeroAdj, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte, Real.sqrt_zero, inv_zero,
      zero_mul, mul_zero, one_mul, sub_zero]

/-! ### The negative-cut fixture's pins -/

theorem vtNC_00 : vtNegCutAdj 0 0 = 3 := rfl
theorem vtNC_01 : vtNegCutAdj 0 1 = 1 := rfl
theorem vtNC_02 : vtNegCutAdj 0 2 = -3 := rfl
theorem vtNC_10 : vtNegCutAdj 1 0 = 1 := rfl
theorem vtNC_11 : vtNegCutAdj 1 1 = 0 := rfl
theorem vtNC_12 : vtNegCutAdj 1 2 = 1 := rfl
theorem vtNC_20 : vtNegCutAdj 2 0 = -3 := rfl
theorem vtNC_21 : vtNegCutAdj 2 1 = 1 := rfl
theorem vtNC_22 : vtNegCutAdj 2 2 = 3 := rfl

theorem vtNegCutAdj_isSymm : vtNegCutAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> rfl

theorem vtNC_deg0 : deg vtNegCutAdj 0 = 1 := by
  simp only [deg, vtNegCutAdj, Matrix.of_apply, Fin.sum_univ_three,
    vtNC_00, vtNC_01, vtNC_02]
  norm_num

theorem vtNC_deg1 : deg vtNegCutAdj 1 = 2 := by
  simp only [deg, vtNegCutAdj, Matrix.of_apply, Fin.sum_univ_three,
    vtNC_10, vtNC_11, vtNC_12]
  norm_num

theorem vtNC_deg2 : deg vtNegCutAdj 2 = 1 := by
  simp only [deg, vtNegCutAdj, Matrix.of_apply, Fin.sum_univ_three,
    vtNC_20, vtNC_21, vtNC_22]
  norm_num

theorem vtNegCutAdj_deg_pos (i : Fin 3) : 0 < deg vtNegCutAdj i := by
  fin_cases i
  · show (0 : ℝ) < deg vtNegCutAdj 0
    simp [vtNC_deg0]
  · show (0 : ℝ) < deg vtNegCutAdj 1
    simp [vtNC_deg1]
  · show (0 : ℝ) < deg vtNegCutAdj 2
    simp [vtNC_deg2]

theorem vtNegCutAdj_not_nonneg : ¬ (∀ i j : Fin 3, 0 ≤ vtNegCutAdj i j) := by
  intro h
  have h02 := h 0 2
  rw [vtNC_02] at h02
  norm_num at h02

theorem vtNegCutAdj_degMin (i : Fin 3) : (1 : ℝ) ≤ deg vtNegCutAdj i := by
  fin_cases i
  · show (1 : ℝ) ≤ deg vtNegCutAdj 0
    simp [vtNC_deg0]
  · show (1 : ℝ) ≤ deg vtNegCutAdj 1
    simp [vtNC_deg1]
  · show (1 : ℝ) ≤ deg vtNegCutAdj 2
    simp [vtNC_deg2]

theorem vtNegCutAdj_degMax (i : Fin 3) : deg vtNegCutAdj i ≤ (2 : ℝ) := by
  fin_cases i
  · show deg vtNegCutAdj 0 ≤ (2 : ℝ)
    simp [vtNC_deg0]
  · show deg vtNegCutAdj 1 ≤ (2 : ℝ)
    simp [vtNC_deg1]
  · show deg vtNegCutAdj 2 ≤ (2 : ℝ)
    simp [vtNC_deg2]

theorem vtNC_L00 : laplacian vtNegCutAdj 0 0 = -2 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, vtNC_deg0,
    vtNC_00]
  try norm_num
theorem vtNC_L01 : laplacian vtNegCutAdj 0 1 = -1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ (by decide),
    vtNC_01]
  try norm_num
theorem vtNC_L02 : laplacian vtNegCutAdj 0 2 = 3 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ (by decide),
    vtNC_02]
  try norm_num
theorem vtNC_L10 : laplacian vtNegCutAdj 1 0 = -1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ (by decide),
    vtNC_10]
  try norm_num
theorem vtNC_L11 : laplacian vtNegCutAdj 1 1 = 2 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, vtNC_deg1,
    vtNC_11]
  try norm_num
theorem vtNC_L12 : laplacian vtNegCutAdj 1 2 = -1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ (by decide),
    vtNC_12]
  try norm_num
theorem vtNC_L20 : laplacian vtNegCutAdj 2 0 = 3 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ (by decide),
    vtNC_20]
  try norm_num
theorem vtNC_L21 : laplacian vtNegCutAdj 2 1 = -1 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ (by decide),
    vtNC_21]
  try norm_num
theorem vtNC_L22 : laplacian vtNegCutAdj 2 2 = -2 := by
  rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, vtNC_deg2,
    vtNC_22]
  try norm_num

/-- The negative-cut fixture's combinatorial form at the fence witness
`(1, 1, 0)`: negative, the value the bracket flips on. -/
theorem vtNegCutAdj_quadForm :
    quadForm (laplacian vtNegCutAdj) (![1, 1, 0] : Fin 3 → ℝ) = -2 := by
  rw [quadForm]
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
    Matrix.cons_val_two, one_mul, zero_mul, vtNC_L00, vtNC_L01,
    vtNC_L10, vtNC_L11, vtNC_L20, vtNC_L21, vtNC_L02, vtNC_L12]
  norm_num

/-! ### The negative-degree fixture's volume pins -/

theorem vtf_neg_vol_zero : vol nfNegEdge ({0} : Finset (Fin 2)) = -1 := by
  simp only [vol, Finset.sum_singleton, nfNegEdge_deg_zero]

theorem vtf_neg_vol_compl :
    vol nfNegEdge ({0} : Finset (Fin 2))ᶜ = 1 := by
  have hcompl : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  rw [hcompl]
  simp only [vol, Finset.sum_singleton, nfNegEdge_deg_one]

theorem vtf_neg_vol_univ :
    vol nfNegEdge (Finset.univ : Finset (Fin 2)) = 0 := by
  simp only [vol, Fin.sum_univ_two, nfNegEdge_deg_zero,
    nfNegEdge_deg_one]
  norm_num

theorem vtf_neg_boundary : boundary nfNegEdge ({0} : Finset (Fin 2)) = 1 := by
  have hcompl : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  simp only [boundary, Finset.sum_singleton, hcompl, nfNegEdge,
    Matrix.of_apply]
  norm_num

/-- The cut test vector of the negative-degree fixture at `S = {0}`:
`(vol Sᶜ, -vol S) = (1, 1)`. -/
theorem vtf_neg_cutVec :
    cutTestVector nfNegEdge ({0} : Finset (Fin 2)) = ![1, 1] := by
  funext i
  rcases nfFin2_cases i with rfl | rfl <;>
    rw [cutTestVector_apply, vtf_neg_vol_compl, vtf_neg_vol_zero] <;>
    simp

/-! ### The congruence lemma's `hP` -/

/-- **Fence (`quadForm_congr`, `hP`)**: the generic congruence engine is
genuinely symmetric-only. At the asymmetric `P = !![1, 1; 0, 1]]` with
`M = 1` and `y = (0, 1)`, the dropped statement reads
`quadForm (P²) y = quadForm 1 (P *ᵥ y)`, i.e. `1 = 2`. -/
theorem vtf_congr_hP_fence_QA :
    ¬ (quadForm (!![1, 1; 0, 1] * (1 : Matrix (Fin 2) (Fin 2) ℝ)
          * !![1, 1; 0, 1]) (![0, 1] : Fin 2 → ℝ)
        = quadForm (1 : Matrix (Fin 2) (Fin 2) ℝ)
            (!![1, 1; 0, 1] *ᵥ (![0, 1] : Fin 2 → ℝ))) := by
  intro h
  have h1 : quadForm (!![1, 1; 0, 1] * (1 : Matrix (Fin 2) (Fin 2) ℝ)
          * !![1, 1; 0, 1]) (![0, 1] : Fin 2 → ℝ) = 1 := by
    simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Matrix.mul_one,
      Matrix.mul_apply, Matrix.of_apply, Fin.isValue, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  have h2 : quadForm (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (!![1, 1; 0, 1] *ᵥ (![0, 1] : Fin 2 → ℝ)) = 2 := by
    simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Matrix.mul_one,
      Matrix.mul_apply, Matrix.of_apply, Fin.isValue, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Matrix.one_apply]
    norm_num
  rw [h1, h2] at h
  norm_num at h

theorem vtf_congr_hP_isolation_QA :
    ¬ (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsSymm := by
  intro h
  have hT : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)ᵀ
      = !![1, 1; 0, 1] := h
  have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hT
  simp only [Matrix.transpose_apply, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at e
  norm_num at e

/-! ### The degree clauses of the transfer engine (negative-degree row) -/

theorem vtf_neg_stretch_e0 :
    degreeSqrt nfNegEdge *ᵥ (![1, 0] : Fin 2 → ℝ) = 0 := by
  rw [nfNegEdge_ds_mulVec]
  simp

/-- **Fence (Dirichlet-form transfer, `hd`)**: at the negative-degree
fixture the stretched vector loses its zeroth coordinate entirely:
`quadForm L e₀ = 1` against `quadForm L_sym (√D e₀) = quadForm 1 0 = 0`. -/
theorem vtf_quadForm_transfer_hd_fence_QA :
    ¬ (quadForm (laplacian nfNegEdge) (![1, 0] : Fin 2 → ℝ)
        = quadForm (normalizedLaplacian nfNegEdge)
            (degreeSqrt nfNegEdge *ᵥ (![1, 0] : Fin 2 → ℝ))) := by
  intro h
  have h1 : quadForm (laplacian nfNegEdge) (![1, 0] : Fin 2 → ℝ) = 1 := by
    rw [nfNegEdge_lap, quadForm]
    simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply,
      Fin.isValue, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  rw [vtf_neg_stretch_e0, nfNegEdge_Lsym, h1] at h
  simp only [quadForm, Matrix.mulVec, Matrix.one_mulVec,
    Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one, Matrix.one_apply,
    Matrix.zero_apply, zero_mul, Matrix.one_apply] at h
  norm_num at h

/-- **Isolation**: the fixture is symmetric; the degree clause `hd` is
exactly the failure (degree `0` is `-1`). -/
theorem vtf_quadForm_transfer_hd_isolation_QA :
    nfNegEdge.IsSymm ∧ ¬ (∀ i : Fin 2, 0 < deg nfNegEdge i) :=
  ⟨nfNegEdge_isSymm, by
    intro hdeg
    have h0 := hdeg 0
    rw [nfNegEdge_deg_zero] at h0
    norm_num at h0⟩

/-- **Fence (degree-weighted denominator, `hdeg`)**: the junk
`√(-1) = 0` kills the stretched vector, so the dot product reads `0`
while the weighted sum reads `-1`. -/
theorem vtf_dot_hdeg_fence_QA :
    ¬ (Matrix.dotProduct (degreeSqrt nfNegEdge *ᵥ (![1, 0] : Fin 2 → ℝ))
          (degreeSqrt nfNegEdge *ᵥ (![1, 0] : Fin 2 → ℝ))
        = ∑ i, deg nfNegEdge i * (![1, 0] : Fin 2 → ℝ) i
            * (![1, 0] : Fin 2 → ℝ) i) := by
  intro h
  have hsum : ∑ i, deg nfNegEdge i * (![1, 0] : Fin 2 → ℝ) i
      * (![1, 0] : Fin 2 → ℝ) i = -1 := by
    simp only [Fin.sum_univ_two, nfNegEdge_deg_zero, nfNegEdge_deg_one,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  rw [vtf_neg_stretch_e0, Matrix.zero_dotProduct, hsum] at h
  norm_num at h

theorem vtf_dot_hdeg_isolation_QA :
    nfNegEdge.IsSymm ∧ ¬ (∀ i : Fin 2, 0 ≤ deg nfNegEdge i) :=
  ⟨nfNegEdge_isSymm, by
    intro hdeg
    have h0 := hdeg 0
    rw [nfNegEdge_deg_zero] at h0
    norm_num at h0⟩

/-- **Fence (onesVec pairing, `hdeg`)**: pairing against the stretched
constants is killed identically — `0 ≠ ∑ deg y = -1`. -/
theorem vtf_dot_onesVec_hdeg_fence_QA :
    ¬ (Matrix.dotProduct (degreeSqrt nfNegEdge *ᵥ (![1, 0] : Fin 2 → ℝ))
          (degreeSqrt nfNegEdge *ᵥ (onesVec : Fin 2 → ℝ))
        = ∑ i, deg nfNegEdge i * (![1, 0] : Fin 2 → ℝ) i) := by
  intro h
  have hsum : ∑ i, deg nfNegEdge i * (![1, 0] : Fin 2 → ℝ) i = -1 := by
    simp only [Fin.sum_univ_two, nfNegEdge_deg_zero, nfNegEdge_deg_one,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  rw [vtf_neg_stretch_e0, Matrix.zero_dotProduct, hsum] at h
  norm_num at h

/-- **Fence (nonzero preservation, `hd`)**: the conclusion itself fails
at the negative-degree row — the stretch of `e₀` is the zero vector. -/
theorem vtf_stretch_ne_zero_hd_fence_QA :
    degreeSqrt nfNegEdge *ᵥ (![1, 0] : Fin 2 → ℝ) = 0 :=
  vtf_neg_stretch_e0

theorem vtf_stretch_ne_zero_hd_isolation_QA :
    (![1, 0] : Fin 2 → ℝ) ≠ 0 ∧ nfNegEdge.IsSymm
      ∧ ¬ (∀ i : Fin 2, 0 < deg nfNegEdge i) :=
  ⟨by
      intro h
      have h0 := congrFun h 0
      simp at h0,
    nfNegEdge_isSymm, by
      intro hdeg
      have h0 := hdeg 0
      rw [nfNegEdge_deg_zero] at h0
      norm_num at h0⟩

/-- **Fence (Rayleigh transfer, `hd`)**: the definitional junk branch of
`rayleigh` at the collapsed stretched vector reads `0` against the
honest `-1` on the right. -/
theorem vtf_rayleigh_hd_fence_QA :
    ¬ (rayleigh (normalizedLaplacian nfNegEdge)
          (degreeSqrt nfNegEdge *ᵥ (![1, 0] : Fin 2 → ℝ))
        = quadForm (laplacian nfNegEdge) (![1, 0] : Fin 2 → ℝ)
            / ∑ i, deg nfNegEdge i * (![1, 0] : Fin 2 → ℝ) i
              * (![1, 0] : Fin 2 → ℝ) i) := by
  intro h
  have hq : quadForm (laplacian nfNegEdge) (![1, 0] : Fin 2 → ℝ) = 1 := by
    rw [nfNegEdge_lap, quadForm]
    simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply,
      Fin.isValue, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  have hsum : ∑ i, deg nfNegEdge i * (![1, 0] : Fin 2 → ℝ) i
      * (![1, 0] : Fin 2 → ℝ) i = -1 := by
    simp only [Fin.sum_univ_two, nfNegEdge_deg_zero, nfNegEdge_deg_one,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    norm_num
  rw [vtf_neg_stretch_e0, rayleigh, if_pos rfl, hq, hsum] at h
  norm_num at h

/-- **Fence (left-multiplied congruence, `hd`)**: entry `(0, 1)` reads
`0` (the junk `√(-1)` kills the left factor) against the genuine
`L 0 1 * 1 = -1`. -/
theorem vtf_leftCongr_hd_fence_QA :
    ¬ (degreeSqrt nfNegEdge * normalizedLaplacian nfNegEdge
        = laplacian nfNegEdge * degreeInvSqrt nfNegEdge) := by
  intro h
  have eL : (degreeSqrt nfNegEdge * normalizedLaplacian nfNegEdge) 0 1
      = 0 := by
    rw [nfNegEdge_Lsym, Matrix.mul_one, nfNegEdge_degreeSqrt]
    simp only [Matrix.diagonal_apply, Fin.isValue,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Matrix.zero_apply]
    simp
  have eR : (laplacian nfNegEdge * degreeInvSqrt nfNegEdge) 0 1 = -1 := by
    rw [nfNegEdge_lap, nfNegEdge_degreeInvSqrt, Matrix.mul_diagonal]
    simp only [Matrix.of_apply, Fin.isValue, Matrix.cons_val_one,
      Matrix.head_cons]
    norm_num
  have e := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h
  simp only at e
  rw [eL, eR] at e
  norm_num at e

/-- **Fence (kernel-cone lift, `hd`)**: `y = (1, 1)` is genuinely in the
combinatorial kernel, but the stretch `√D y = (0, 1)` is not in the
normalized kernel — `L_sym *ᵥ (0, 1) = (0, 1) ≠ 0`. -/
theorem vtf_coneLift_hd_fence_QA :
    ¬ (normalizedLaplacian nfNegEdge *ᵥ
          (degreeSqrt nfNegEdge *ᵥ (![1, 1] : Fin 2 → ℝ)) = 0) := by
  intro h
  rw [nfNegEdge_ds_mulVec, nfNegEdge_Lsym, Matrix.one_mulVec] at h
  have h1 := congrFun h 1
  simp only [Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply] at h1
  norm_num at h1

theorem vtf_coneLift_hd_isolation_QA :
    laplacian nfNegEdge *ᵥ (![1, 1] : Fin 2 → ℝ) = 0
      ∧ nfNegEdge.IsSymm ∧ ¬ (∀ i : Fin 2, 0 < deg nfNegEdge i) :=
  ⟨by
      rw [nfNegEdge_lap]
      funext i
      rcases nfFin2_cases i with rfl | rfl <;>
        simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply,
          Fin.isValue, Fin.sum_univ_two, Matrix.cons_val_zero,
          Matrix.head_cons, Matrix.cons_val_one, Pi.zero_apply]
      all_goals norm_num,
    nfNegEdge_isSymm, by
      intro hdeg
      have h0 := hdeg 0
      rw [nfNegEdge_deg_zero] at h0
      norm_num at h0⟩

/-! ### The cut-test-vector layer's degree clauses -/

/-- **Fence (cut-vector orthogonality, `hdeg`)**: the volume identity
`vol S · vol Sᶜ - vol Sᶜ · vol S = 0` is not what the left side
computes to — both stretched vectors are `(0, 1)`, dot `1`. -/
theorem vtf_cutVec_orth_hdeg_fence_QA :
    ¬ (Matrix.dotProduct (degreeSqrt nfNegEdge
            *ᵥ cutTestVector nfNegEdge ({0} : Finset (Fin 2)))
          (degreeSqrt nfNegEdge *ᵥ (onesVec : Fin 2 → ℝ))
        = 0) := by
  intro h
  rw [vtf_neg_cutVec, nfNegEdge_ds_mulVec, nfNegEdge_ds_mulVec,
    onesVec] at h
  simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
    one_mul, Matrix.dotProduct, Fin.sum_univ_two, Matrix.zero_mul] at h
  norm_num at h

/-- **Fence (cut-vector self norm, `hdeg`)**: the stretched norm reads
`1` against the junk product `vol S · vol Sᶜ · vol V = (-1) · 1 · 0`. -/
theorem vtf_cutVec_self_hdeg_fence_QA :
    ¬ (Matrix.dotProduct (degreeSqrt nfNegEdge
            *ᵥ cutTestVector nfNegEdge ({0} : Finset (Fin 2)))
          (degreeSqrt nfNegEdge
            *ᵥ cutTestVector nfNegEdge ({0} : Finset (Fin 2)))
        = vol nfNegEdge ({0} : Finset (Fin 2))
            * vol nfNegEdge ({0} : Finset (Fin 2))ᶜ
            * vol nfNegEdge (Finset.univ : Finset (Fin 2))) := by
  intro h
  rw [vtf_neg_cutVec, nfNegEdge_ds_mulVec, vtf_neg_vol_zero,
    vtf_neg_vol_compl, vtf_neg_vol_univ] at h
  simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.dotProduct,
    Fin.sum_univ_two, Matrix.zero_mul, Matrix.cons_val_zero] at h
  norm_num at h

/-- **Fence (cut-vector nonvanishing, `hd`)**: at the all-zero adjacency
every volume is junk-zero, the cut vector is stretched to `0` — the
conclusion itself fails while `hS`/`hSc` are genuine. -/
theorem vtf_cutVec_ne_zero_hd_fence_QA :
    degreeSqrt vtZeroAdj *ᵥ cutTestVector vtZeroAdj ({0} : Finset (Fin 2))
      = 0 := by
  rw [vtZeroAdj_degreeSqrt, Matrix.zero_mulVec]

theorem vtf_cutVec_ne_zero_hd_isolation_QA :
    ({0} : Finset (Fin 2)).Nonempty
      ∧ ({0} : Finset (Fin 2))ᶜ.Nonempty
      ∧ vtZeroAdj.IsSymm ∧ (∀ i j : Fin 2, 0 ≤ vtZeroAdj i j)
      ∧ ¬ (∀ i : Fin 2, 0 < deg vtZeroAdj i) :=
  ⟨Finset.singleton_nonempty 0, ⟨1, by decide⟩, vtZeroAdj_isSymm,
    vtZeroAdj_nonneg, vtZeroAdj_not_pos_deg⟩

/-- **Fence (cut-vector Rayleigh quotient, `hd`)**: the left side
computes to `rayleigh 1 (0, 1) = 1` while the right side is
`boundary · vol V / (vol S · vol Sᶜ) = 1 · 0 / (-1) = 0`. -/
theorem vtf_cutVec_rayleigh_hd_fence_QA :
    ¬ (rayleigh (normalizedLaplacian nfNegEdge)
          (degreeSqrt nfNegEdge
            *ᵥ cutTestVector nfNegEdge ({0} : Finset (Fin 2)))
        = boundary nfNegEdge ({0} : Finset (Fin 2))
            * vol nfNegEdge (Finset.univ : Finset (Fin 2))
            / (vol nfNegEdge ({0} : Finset (Fin 2))
              * vol nfNegEdge ({0} : Finset (Fin 2))ᶜ)) := by
  intro h
  rw [vtf_neg_cutVec, nfNegEdge_ds_mulVec, nfNegEdge_Lsym,
    vtf_neg_boundary, vtf_neg_vol_univ, vtf_neg_vol_zero,
    vtf_neg_vol_compl] at h
  rw [rayleigh, if_neg (by
      intro hz
      have h1 := congrFun hz 1
      simp at h1)] at h
  simp only [quadForm, Matrix.mulVec, Matrix.one_mulVec,
    Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one, Matrix.one_apply,
    Matrix.zero_apply, zero_mul, one_mul] at h
  norm_num at h

/-! ### PSD transfer -/

/-- The asymmetric fixture's normalized Laplacian, pinned: the
congruence sees the asymmetric adjacency directly. -/
theorem vtAsymAdj_Lsym :
    normalizedLaplacian nfAsymAdj
      = !![1, -(Real.sqrt 2); -((Real.sqrt 2 : ℝ)⁻¹), 1] := by
  ext i j
  rcases nfFin2_cases i with rfl | rfl <;>
    rcases nfFin2_cases j with rfl | rfl <;>
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, deg, nfAsymAdj, Matrix.of_apply, Fin.isValue,
      Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, reduceIte, Real.sqrt_one, inv_one]
  all_goals norm_num
  all_goals simp only [vtf_inv_sqrt_two]
  all_goals ring

/-- **Fence (PSD transfer, `hA`)**: at the asymmetric positive-degree
fixture the quadratic form sees the symmetrized action —
`quadForm L_sym (1, 1) = 2 - (3/2)√2 < 0` (since `4 < 3√2`, i.e.
`16 < 18`). -/
theorem vtf_psd_hA_fence_QA :
    ¬ (∀ x : Fin 2 → ℝ, 0 ≤ quadForm (normalizedLaplacian nfAsymAdj) x) := by
  intro h
  have hkey : (4 : ℝ) < 3 * Real.sqrt 2 := by
    have hnn : (0 : ℝ) ≤ Real.sqrt 2 := by positivity
    nlinarith [vtf_sq_sqrt_two]
  have h1 := h ![1, 1]
  rw [vtAsymAdj_Lsym] at h1
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h1
  rw [vtf_inv_sqrt_two] at h1
  linarith

theorem vtf_psd_hA_isolation_QA :
    (∀ i j : Fin 2, 0 ≤ nfAsymAdj i j) ∧ (∀ i : Fin 2, 0 < deg nfAsymAdj i)
      ∧ ¬ nfAsymAdj.IsSymm :=
  ⟨by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [nfAsymAdj],
    by
      intro i
      rcases nfFin2_cases i with rfl | rfl <;>
        simp [nfAsym_deg_zero, nfAsym_deg_one],
    by
      intro h
      have hT : (nfAsymAdj : Matrix (Fin 2) (Fin 2) ℝ)ᵀ = nfAsymAdj := h
      have e := congrArg
        (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) hT
      simp only [Matrix.transpose_apply, nfAsymAdj, Matrix.of_apply,
        Fin.isValue, Matrix.cons_val_zero, Matrix.head_cons,
        Matrix.cons_val_one] at e
      norm_num at e⟩

/-- **Fence (PSD transfer, `hnn`)**: the signed regular fixture's
alternating mode is an eigenvector at `-1`, so the form reads `-2 < 0`. -/
theorem vtf_psd_hnn_fence_QA :
    ¬ (∀ x : Fin 2 → ℝ, 0 ≤ quadForm (normalizedLaplacian vtSigAdj) x) := by
  intro h
  have h1 := h ![1, -1]
  rw [vtSigAdj_Lsym] at h1
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct,
    Fin.sum_univ_two, Matrix.of_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h1
  norm_num at h1

theorem vtf_psd_hnn_isolation_QA :
    vtSigAdj.IsSymm ∧ (∀ i : Fin 2, 0 < deg vtSigAdj i)
      ∧ ¬ (∀ i j : Fin 2, 0 ≤ vtSigAdj i j) :=
  ⟨vtSigAdj_isSymm, vtSigAdj_deg_pos, vtSigAdj_not_nonneg⟩

/-! ### The connectivity-transfer layer -/

/-- **Fence (bottom eigenvalue zero, `hnn`)**: the signed regular
fixture's bottom normalized eigenvalue is at most `-1` (the alternating
mode is an eigenpair at `-1`, and the bottom entry of the sorted
spectrum is below every basis eigenvalue) — against the claimed `= 0`. -/
theorem vtf_evalsZero_hnn_fence_QA :
    evals (normalizedLaplacian_symmetric vtSigAdj vtSigAdj_isSymm)
        (⟨0, by decide⟩ : Fin (Fintype.card (Fin 2)))
      ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul
    (normalizedLaplacian_symmetric vtSigAdj vtSigAdj_isSymm)
    vtf_alt_ne vtSigAdj_Lsym_mulVec
  have hle := evals_first_le_eigvalOf
    (normalizedLaplacian_symmetric vtSigAdj vtSigAdj_isSymm)
    (by decide) i
  rw [hi, h] at hle
  norm_num at hle

/-- **Fence (bottom eigenvalue zero, `hd`)**: at the all-zero adjacency
the normalized Laplacian is the identity, so the bottom eigenvalue is
`1 ≠ 0` through `evals_one`. -/
theorem vtf_evalsZero_hd_fence_QA :
    evals (normalizedLaplacian_symmetric vtZeroAdj vtZeroAdj_isSymm)
        (⟨0, by decide⟩ : Fin (Fintype.card (Fin 2)))
      ≠ 0 := by
  intro h
  have h1 : evals (normalizedLaplacian_symmetric vtZeroAdj
      vtZeroAdj_isSymm)
      (⟨0, by decide⟩ : Fin (Fintype.card (Fin 2)))
      = evals (show (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm from by simp)
          (⟨0, by decide⟩ : Fin (Fintype.card (Fin 2))) :=
    evals_congr _ _ vtZeroAdj_Lsym _
  rw [h1, evals_one] at h
  norm_num at h

theorem vtf_evalsZero_hd_isolation_QA :
    vtZeroAdj.IsSymm ∧ (∀ i j : Fin 2, 0 ≤ vtZeroAdj i j)
      ∧ (0 < Fintype.card (Fin 2))
      ∧ ¬ (∀ i : Fin 2, 0 < deg vtZeroAdj i) :=
  ⟨vtZeroAdj_isSymm, vtZeroAdj_nonneg, by decide, vtZeroAdj_not_pos_deg⟩

/-! ### The signed-path kernel (the algebraic-connectivity `hnn` fence) -/

theorem vtsp_stretch_ones :
    degreeSqrt kbfSgnPath3Adj *ᵥ (onesVec : Fin 3 → ℝ) = ![1, 2, 1] := by
  funext i
  rw [degreeSqrt_mulVec_apply]
  fin_cases i <;>
    simp only [deg, kbfSgnPath3Adj, Matrix.of_apply, Fin.sum_univ_three,
      kbfSgn3_00, kbfSgn3_01, kbfSgn3_02, kbfSgn3_10, kbfSgn3_11,
      kbfSgn3_12, kbfSgn3_20, kbfSgn3_21, kbfSgn3_22, Fin.isValue]
  all_goals norm_num
  all_goals (try rw [vtf_sqrt_four])
  all_goals norm_num
  all_goals (try simp [onesVec])

/-- The stretched kernel vector: `√D · (1, 2, 3) = (1, 4, 3)`. -/
theorem vtsp_stretch_kernel :
    degreeSqrt kbfSgnPath3Adj *ᵥ (![1, 2, 3] : Fin 3 → ℝ) = ![1, 4, 3] := by
  funext i
  rw [degreeSqrt_mulVec_apply]
  fin_cases i <;>
    simp only [deg, kbfSgnPath3Adj, Matrix.of_apply, Fin.sum_univ_three,
      kbfSgn3_00, kbfSgn3_01, kbfSgn3_02, kbfSgn3_10, kbfSgn3_11,
      kbfSgn3_12, kbfSgn3_20, kbfSgn3_21, kbfSgn3_22, Fin.isValue]
  all_goals norm_num
  all_goals (try rw [vtf_sqrt_four])
  all_goals norm_num

theorem vtsp_deg_pos (i : Fin 3) : 0 < deg kbfSgnPath3Adj i := by
  fin_cases i
  · show (0 : ℝ) < deg kbfSgnPath3Adj 0
    simp only [deg, kbfSgnPath3Adj, Matrix.of_apply, Fin.sum_univ_three,
      kbfSgn3_00, kbfSgn3_01, kbfSgn3_02]
    norm_num
  · show (0 : ℝ) < deg kbfSgnPath3Adj 1
    simp only [deg, kbfSgnPath3Adj, Matrix.of_apply, Fin.sum_univ_three,
      kbfSgn3_10, kbfSgn3_11, kbfSgn3_12]
    norm_num
  · show (0 : ℝ) < deg kbfSgnPath3Adj 2
    simp only [deg, kbfSgnPath3Adj, Matrix.of_apply, Fin.sum_univ_three,
      kbfSgn3_20, kbfSgn3_21, kbfSgn3_22]
    norm_num

theorem vtsp_stretch_ones_in_kernel :
    normalizedLaplacian kbfSgnPath3Adj *ᵥ ![1, 2, 1] = 0 := by
  rw [← vtsp_stretch_ones]
  exact normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero
    kbfSgnPath3Adj vtsp_deg_pos kbfSgn3_ones_in_kernel

theorem vtsp_stretch_kernel_in_kernel :
    normalizedLaplacian kbfSgnPath3Adj *ᵥ ![1, 4, 3] = 0 := by
  rw [← vtsp_stretch_kernel]
  exact normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero
    kbfSgnPath3Adj vtsp_deg_pos kbfSgn3_kernel_vec

theorem vtsp_linearIndependent :
    LinearIndependent (R := ℝ) (M := Fin 3 → ℝ)
      (![![1, 2, 1], ![1, 4, 3]]) := by
  rw [LinearIndependent.pair_iff' (by
      intro h
      have h0 := congrFun h 0
      simp at h0)]
  intro a ha
  have h1 := congrFun ha 0
  have h2 := congrFun ha 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h1 h2
  linarith

/-- The stretched kernel's span lands in the normalized kernel. -/
theorem vtsp_span_le_ker :
    Submodule.span ℝ (Set.range (![![1, 2, 1], ![1, 4, 3]]))
      ≤ LinearMap.ker (Matrix.mulVecLin (normalizedLaplacian
        kbfSgnPath3Adj)) := by
  rw [Submodule.span_le]
  rintro x hx
  obtain ⟨i, rfl⟩ := hx
  fin_cases i
  · show Matrix.mulVecLin (normalizedLaplacian kbfSgnPath3Adj)
        (![1, 2, 1] : Fin 3 → ℝ) = 0
    rw [Matrix.mulVecLin_apply]
    exact vtsp_stretch_ones_in_kernel
  · show Matrix.mulVecLin (normalizedLaplacian kbfSgnPath3Adj)
        (![1, 4, 3] : Fin 3 → ℝ) = 0
    rw [Matrix.mulVecLin_apply]
    exact vtsp_stretch_kernel_in_kernel

/-- **Fence (algebraic connectivity, `hnn`)**: on the signed path —
symmetric, positive degrees, genuinely *connected* support — the
combinatorial kernel is two-dimensional (`1` and `(1, 2, 3)` are both
delivered kernel pins), both kernel vectors stretch into the normalized
kernel (the cone lift at genuine positive degrees), so the second
eigenvalue is bounded above by a zero Rayleigh quotient through the
subspace competitor engine: `λ₂ ≤ 0`, refuting `0 < λ₂`. -/
theorem vtf_pos_of_connected_hnn_fence_QA :
    ¬ (0 < secondEval (normalizedLaplacian kbfSgnPath3Adj)
          (normalizedLaplacian_symmetric kbfSgnPath3Adj
            kbfSgnPath3Adj_isSymm)
          (by norm_num)) := by
  intro hpos
  obtain ⟨x, hxW, hx0, hge⟩ :=
    exists_ne_mem_rayleigh_ge_of_finrank_eq
      (normalizedLaplacian_symmetric kbfSgnPath3Adj kbfSgnPath3Adj_isSymm)
      (⟨1, by decide⟩ : Fin (Fintype.card (Fin 3)))
      (Submodule.span ℝ (Set.range (![![1, 2, 1], ![1, 4, 3]])))
      (by rw [finrank_span_eq_card vtsp_linearIndependent]; decide)
  have hxker : normalizedLaplacian kbfSgnPath3Adj *ᵥ x = 0 :=
    vtsp_span_le_ker hxW
  have hray : rayleigh (normalizedLaplacian kbfSgnPath3Adj) x = 0 := by
    rw [rayleigh, if_neg hx0, quadForm, hxker, Matrix.dotProduct_zero,
      zero_div]
  rw [hray] at hge
  have hdef : secondEval (normalizedLaplacian kbfSgnPath3Adj)
      (normalizedLaplacian_symmetric kbfSgnPath3Adj
        kbfSgnPath3Adj_isSymm) (by norm_num)
      = evals (normalizedLaplacian_symmetric kbfSgnPath3Adj
          kbfSgnPath3Adj_isSymm)
          (⟨1, by decide⟩ : Fin (Fintype.card (Fin 3))) := rfl
  rw [hdef] at hpos
  linarith

theorem vtf_pos_of_connected_hnn_isolation_QA :
    kbfSgnPath3Adj.IsSymm ∧ (∀ i : Fin 3, 0 < deg kbfSgnPath3Adj i)
      ∧ (2 ≤ Fintype.card (Fin 3))
      ∧ (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Connected
      ∧ ¬ (∀ i j : Fin 3, 0 ≤ kbfSgnPath3Adj i j) :=
  ⟨kbfSgnPath3Adj_isSymm, vtsp_deg_pos, by norm_num,
    kbfSgnPath3_supportGraph_connected, kbfSgn3_not_nonneg⟩

/-- **Fence (the iff form, `hnn`)**: the same witness — the left side is
`false` (the fence above), the right side `true` (the delivered
connectivity pin). -/
theorem vtf_pos_iff_hnn_fence_QA :
    ¬ (0 < secondEval (normalizedLaplacian kbfSgnPath3Adj)
          (normalizedLaplacian_symmetric kbfSgnPath3Adj
            kbfSgnPath3Adj_isSymm)
          (by norm_num)
        ↔ (supportGraph kbfSgnPath3Adj kbfSgnPath3Adj_isSymm).Connected) := by
  intro h
  exact vtf_pos_of_connected_hnn_fence_QA
    (h.2 kbfSgnPath3_supportGraph_connected)

/-! ### The degree-sandwich layer's pointwise engines -/

/-- **Fence (linear-equiv bijectivity, `hd`)**: at the all-zero adjacency
the stretch map is literally zero, so injectivity fails. -/
theorem vtf_equiv_hd_fence_QA :
    ¬ Function.Injective (Matrix.mulVecLin (degreeSqrt vtZeroAdj)) := by
  intro hinj
  have h0 : ∀ x : Fin 2 → ℝ,
      Matrix.mulVecLin (degreeSqrt vtZeroAdj) x = 0 := by
    intro x
    rw [Matrix.mulVecLin_apply, vtZeroAdj_degreeSqrt, Matrix.zero_mulVec]
  have h10 : Matrix.mulVecLin (degreeSqrt vtZeroAdj) 1
      = Matrix.mulVecLin (degreeSqrt vtZeroAdj) 0 := by
    rw [h0 1, h0 0]
  exact one_ne_zero (hinj h10)

/-- **Fence (denominator floor, `hdmin`)**: an overstated floor cannot
bound the weighted norm — `5 · ‖e₀‖² = 5 ≤ 1 = deg · e₀²` is false. -/
theorem vtf_sum_ge_hdmin_fence_QA :
    ¬ ((5 : ℝ) * Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
          (![1, 0] : Fin 2 → ℝ)
        ≤ ∑ i, deg edgeAdj i * (![1, 0] : Fin 2 → ℝ) i
            * (![1, 0] : Fin 2 → ℝ) i) := by
  simp only [Matrix.dotProduct, Fin.sum_univ_two, edgeAdj_regular,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  norm_num

/-- **Fence (denominator ceiling, `hdmax`)**: an understated ceiling
cannot dominate the weighted norm — `1 ≤ (1/2) · 1` is false. -/
theorem vtf_sum_le_hdmax_fence_QA :
    ¬ (∑ i, deg edgeAdj i * (![1, 0] : Fin 2 → ℝ) i
            * (![1, 0] : Fin 2 → ℝ) i
        ≤ (1 / 2 : ℝ) * Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
            (![1, 0] : Fin 2 → ℝ)) := by
  simp only [Matrix.dotProduct, Fin.sum_univ_two, edgeAdj_regular,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  norm_num

/-! ### The quotient bracket on the connected negative cut -/

theorem vtf_negCut_stretch_ne :
    degreeSqrt vtNegCutAdj *ᵥ (![1, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro hz
  have h0 := congrFun hz 0
  rw [degreeSqrt_mulVec_apply, vtNC_deg0, Real.sqrt_one, one_mul] at h0
  simp only [Matrix.cons_val_zero, Matrix.head_cons, Pi.zero_apply] at h0
  norm_num at h0

theorem vtf_negCut_W :
    Matrix.dotProduct (degreeSqrt vtNegCutAdj *ᵥ (![1, 1, 0] : Fin 3 → ℝ))
      (degreeSqrt vtNegCutAdj *ᵥ (![1, 1, 0] : Fin 3 → ℝ)) = 3 := by
  rw [dotProduct_degreeSqrt_mulVec vtNegCutAdj
    (fun i => le_of_lt (vtNegCutAdj_deg_pos i))]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.cons_val_two, vtNC_deg0, vtNC_deg1,
    vtNC_deg2]
  norm_num

theorem vtf_negCut_num :
    quadForm (normalizedLaplacian vtNegCutAdj)
      (degreeSqrt vtNegCutAdj *ᵥ (![1, 1, 0] : Fin 3 → ℝ)) = -2 := by
  rw [← quadForm_laplacian_eq_quadForm_normalizedLaplacian vtNegCutAdj
    vtNegCutAdj_deg_pos]
  exact vtNegCutAdj_quadForm

theorem vtf_negCut_rayleigh_norm :
    rayleigh (normalizedLaplacian vtNegCutAdj)
      (degreeSqrt vtNegCutAdj *ᵥ (![1, 1, 0] : Fin 3 → ℝ)) = -2 / 3 := by
  rw [rayleigh, if_neg vtf_negCut_stretch_ne, vtf_negCut_num,
    vtf_negCut_W]

theorem vtf_negCut_rayleigh_lap :
    rayleigh (laplacian vtNegCutAdj) (![1, 1, 0] : Fin 3 → ℝ) = -1 := by
  rw [rayleigh, if_neg (by
      intro hz
      have h0 := congrFun hz 0
      simp at h0), vtNegCutAdj_quadForm]
  simp only [Matrix.dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
    Matrix.cons_val_two]
  norm_num

/-- **Fence (quotient bracket upper, `hnn` — the headline)**: on the
connected negative-cut fixture the combinatorial form at `(1, 1, 0)` is
`-2`, so the degree-weighted denominator `3` divides it to `-2/3` while
the plain-norm quotient lands at `-1 = -2/2`: the division flips on
signed input exactly as the docstring warns, `-2/3 ≤ -1` is false, with
`hA`, `hd`, `hdmin`, `hpos`, `hx0` all genuine. -/
theorem vtf_rayleigh_le_div_hnn_fence_QA :
    ¬ (rayleigh (normalizedLaplacian vtNegCutAdj)
          (degreeSqrt vtNegCutAdj *ᵥ (![1, 1, 0] : Fin 3 → ℝ))
        ≤ rayleigh (laplacian vtNegCutAdj) (![1, 1, 0] : Fin 3 → ℝ)
            / (1 : ℝ)) := by
  intro h
  rw [vtf_negCut_rayleigh_norm, vtf_negCut_rayleigh_lap] at h
  norm_num at h

/-- **Fence (quotient bracket lower, `hnn`)**: the same witness at
`dmax = 2` — `-1 ≤ 2 · (-2/3) = -4/3` is false. -/
theorem vtf_rayleigh_mul_hnn_fence_QA :
    ¬ (rayleigh (laplacian vtNegCutAdj) (![1, 1, 0] : Fin 3 → ℝ)
        ≤ (2 : ℝ) * rayleigh (normalizedLaplacian vtNegCutAdj)
            (degreeSqrt vtNegCutAdj *ᵥ (![1, 1, 0] : Fin 3 → ℝ))) := by
  intro h
  rw [vtf_negCut_rayleigh_lap, vtf_negCut_rayleigh_norm] at h
  norm_num at h

theorem vtf_rayleigh_hnn_isolation_QA :
    vtNegCutAdj.IsSymm ∧ (∀ i : Fin 3, 0 < deg vtNegCutAdj i)
      ∧ (∀ i : Fin 3, (1 : ℝ) ≤ deg vtNegCutAdj i)
      ∧ (∀ i : Fin 3, deg vtNegCutAdj i ≤ (2 : ℝ))
      ∧ (![1, 1, 0] : Fin 3 → ℝ) ≠ 0
      ∧ ¬ (∀ i j : Fin 3, 0 ≤ vtNegCutAdj i j) :=
  ⟨vtNegCutAdj_isSymm, vtNegCutAdj_deg_pos, vtNegCutAdj_degMin,
    vtNegCutAdj_degMax, by
      intro hz
      have h0 := congrFun hz 0
      simp at h0, vtNegCutAdj_not_nonneg⟩

/-! ### Wrong-constant fences on K₂ -/

/-- The K₂ stretch pin: `√D = 1` on `K₂`. -/
theorem vtK2_ds (x : Fin 2 → ℝ) : degreeSqrt edgeAdj *ᵥ x = x := by
  funext i
  rw [degreeSqrt_mulVec_apply, edgeAdj_regular i, Real.sqrt_one, one_mul]

theorem vtK2_pos_deg (i : Fin 2) : 0 < deg edgeAdj i := by
  rw [edgeAdj_regular i]; norm_num

/-- The K₂ alternating mode's combinatorial form: `4`. -/
theorem vtK2_quadForm :
    quadForm (laplacian edgeAdj) (![1, -1] : Fin 2 → ℝ) = 4 := by
  rw [quadForm]
  simp only [Matrix.mulVec, Matrix.dotProduct, laplacian,
    Matrix.sub_apply, degreeMatrix, edgeAdj, Matrix.of_apply,
    Fin.isValue, deg, Fin.sum_univ_two, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
    reduceIte, Matrix.one_apply]
  norm_num

theorem vtK2_quadForm_norm :
    quadForm (normalizedLaplacian edgeAdj) (![1, -1] : Fin 2 → ℝ) = 4 := by
  rw [← vtK2_ds (![1, -1] : Fin 2 → ℝ),
    ← quadForm_laplacian_eq_quadForm_normalizedLaplacian edgeAdj
      vtK2_pos_deg]
  exact vtK2_quadForm

theorem vtK2_dot :
    Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) (![1, -1] : Fin 2 → ℝ) = 2 := by
  simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one]
  norm_num

theorem vtK2_rayleigh_norm :
    rayleigh (normalizedLaplacian edgeAdj) (![1, -1] : Fin 2 → ℝ) = 2 := by
  rw [rayleigh, if_neg vtf_alt_ne, vtK2_quadForm_norm, vtK2_dot]
  norm_num

theorem vtK2_rayleigh_lap :
    rayleigh (laplacian edgeAdj) (![1, -1] : Fin 2 → ℝ) = 2 := by
  rw [rayleigh, if_neg vtf_alt_ne, vtK2_quadForm, vtK2_dot]
  norm_num

/-- **Fence (quotient bracket upper, wrong `hdmin`)**: at `dmin = 5` on
K₂ the dropped statement reads `2 ≤ 2/5`. -/
theorem vtf_rayleigh_le_div_hdmin_fence_QA :
    ¬ (rayleigh (normalizedLaplacian edgeAdj)
          (degreeSqrt edgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))
        ≤ rayleigh (laplacian edgeAdj) (![1, -1] : Fin 2 → ℝ)
            / (5 : ℝ)) := by
  intro h
  rw [vtK2_ds, vtK2_rayleigh_norm, vtK2_rayleigh_lap] at h
  norm_num at h

/-- **Fence (quotient bracket lower, wrong `hdmax`)**: at `dmax = 1/2`
on K₂ the dropped statement reads `2 ≤ (1/2) · 2 = 1`. -/
theorem vtf_rayleigh_mul_hdmax_fence_QA :
    ¬ (rayleigh (laplacian edgeAdj) (![1, -1] : Fin 2 → ℝ)
        ≤ (1 / 2 : ℝ) * rayleigh (normalizedLaplacian edgeAdj)
            (degreeSqrt edgeAdj *ᵥ (![1, -1] : Fin 2 → ℝ))) := by
  intro h
  rw [vtK2_rayleigh_lap, vtK2_ds, vtK2_rayleigh_norm] at h
  norm_num at h

/-- **Fence (the div-form interface, wrong `hdmax`)**: at `dmax = 1/2`
on K₂ the dropped statement reads `lambda2 / (1/2) = 4 ≤ 2`. (The mul
form is fenced by `icf_sandwich_hdmax`; this is the div form's own
statement.) -/
theorem vtf_div_secondEval_hdmax_fence_QA :
    ¬ (lambda2 edgeAdj edgeAdj_symmetric (le_refl 2) / (1 / 2 : ℝ)
        ≤ secondEval (normalizedLaplacian edgeAdj)
            (normalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric)
            (le_refl 2)) := by
  intro h
  rw [dsK2_lambda2_eq_two, icEdge_normLap_secondEval] at h
  norm_num at h

/-! ### The `0 < dmin` guard at the pointwise engine (zero-degree corner) -/

theorem vtf_iso_ds_e0 :
    degreeSqrt nfIso *ᵥ (![1, 0, 0] : Fin 3 → ℝ) = ![1, 0, 0] := by
  funext i
  rw [degreeSqrt_mulVec_apply]
  fin_cases i <;>
    simp only [deg, nfIso, Matrix.of_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
      Matrix.cons_val_two, Fin.isValue]
  all_goals norm_num

theorem vtI_00 : nfIso 0 0 = 0 := rfl
theorem vtI_01 : nfIso 0 1 = 1 := rfl
theorem vtI_02 : nfIso 0 2 = 0 := rfl
theorem vtI_10 : nfIso 1 0 = 1 := rfl
theorem vtI_11 : nfIso 1 1 = 0 := rfl
theorem vtI_12 : nfIso 1 2 = 0 := rfl
theorem vtI_20 : nfIso 2 0 = 0 := rfl
theorem vtI_21 : nfIso 2 1 = 0 := rfl
theorem vtI_22 : nfIso 2 2 = 0 := rfl

theorem vtf_iso_Lsym :
    normalizedLaplacian nfIso = !![1, -1, 0; -1, 1, 0; 0, 0, 1] := by
  ext i j
  rcases nfFin3_cases i with rfl | rfl | rfl <;>
    rcases nfFin3_cases j with rfl | rfl | rfl <;>
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
      degreeInvSqrt, nfIso_deg_zero, nfIso_deg_one, nfIso_deg_two,
      vtI_00, vtI_01, vtI_02, vtI_10, vtI_11, vtI_12, vtI_20, vtI_21,
      vtI_22, Fin.isValue, Real.sqrt_one, Real.sqrt_zero, inv_one,
      inv_zero, zero_mul, mul_zero, one_mul, sub_zero]
  all_goals simp

theorem vtf_iso_e0_ne : (![1, 0, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp at h0

theorem vtf_iso_quadForm_norm :
    quadForm (normalizedLaplacian nfIso) (![1, 0, 0] : Fin 3 → ℝ) = 1 := by
  rw [vtf_iso_Lsym, quadForm]
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
    Matrix.of_apply, Fin.isValue, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

theorem vtf_iso_quadForm_lap :
    quadForm (laplacian nfIso) (![1, 0, 0] : Fin 3 → ℝ) = 1 := by
  rw [quadForm]
  simp only [Matrix.mulVec, Matrix.dotProduct, laplacian,
    Matrix.sub_apply, degreeMatrix, nfIso, Matrix.of_apply,
    Fin.isValue, deg, Fin.sum_univ_three, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
    Matrix.cons_val_two, reduceIte]
  norm_num

theorem vtf_iso_dot :
    Matrix.dotProduct (![1, 0, 0] : Fin 3 → ℝ) (![1, 0, 0] : Fin 3 → ℝ)
      = 1 := by
  simp only [Matrix.dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
    Matrix.cons_val_two]
  norm_num

/-- **Fence (the `0 < dmin` guard at the pointwise engine)**: on the
zero-degree fixture `dmin = 0` satisfies the degree-floor clause
(`0 ≤ deg`), yet the right side is `rayleigh L e₀ / 0 = 1/0 = 0` while
the left side computes to `1`. -/
theorem vtf_rayleigh_le_div_hpos_fence_QA :
    ¬ (rayleigh (normalizedLaplacian nfIso)
          (degreeSqrt nfIso *ᵥ (![1, 0, 0] : Fin 3 → ℝ))
        ≤ rayleigh (laplacian nfIso) (![1, 0, 0] : Fin 3 → ℝ)
            / (0 : ℝ)) := by
  intro h
  have hnorm : rayleigh (normalizedLaplacian nfIso)
      (degreeSqrt nfIso *ᵥ (![1, 0, 0] : Fin 3 → ℝ)) = 1 := by
    rw [vtf_iso_ds_e0, rayleigh, if_neg vtf_iso_e0_ne,
      vtf_iso_quadForm_norm, vtf_iso_dot]
    norm_num
  have hlap : rayleigh (laplacian nfIso) (![1, 0, 0] : Fin 3 → ℝ) = 1 := by
    rw [rayleigh, if_neg vtf_iso_e0_ne, vtf_iso_quadForm_lap,
      vtf_iso_dot]
    norm_num
  rw [hnorm, hlap, div_zero] at h
  norm_num at h

theorem vtf_rayleigh_le_div_hpos_isolation_QA :
    nfIso.IsSymm ∧ (∀ i j : Fin 3, 0 ≤ nfIso i j)
      ∧ (∀ i : Fin 3, (0 : ℝ) ≤ deg nfIso i)
      ∧ (![1, 0, 0] : Fin 3 → ℝ) ≠ 0
      ∧ ¬ (0 < (0 : ℝ)) :=
  ⟨nfIso_isSymm, by
      intro i j
      rcases nfFin3_cases i with rfl | rfl | rfl <;>
        rcases nfFin3_cases j with rfl | rfl | rfl <;>
        simp [vtI_00, vtI_01, vtI_02, vtI_10, vtI_11, vtI_12,
          vtI_20, vtI_21, vtI_22],
    by
      intro i
      rcases nfFin3_cases i with rfl | rfl | rfl <;>
        simp [nfIso_deg_zero, nfIso_deg_one, nfIso_deg_two],
    vtf_iso_e0_ne, not_lt.mpr (le_refl (0 : ℝ))⟩

end TransferFences

end SpectralGraphTheory.QA
