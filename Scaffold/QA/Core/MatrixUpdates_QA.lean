/-
  MatrixUpdates_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Core.MatrixUpdates`, whose Woodbury
  identity became a proved theorem on 2026-08-18 after its former
  admitted shape was found false:

  * a refutation of the retired statement at the scalar counterexample
    `A = 1, U = V = 1, C = 0` — stated at the retired axiom's own shape
    for `n = k = Fin 1`, `𝕜 = ℚ`, without consuming any axiom, together
    with proofs that the retired hypotheses *held* there (so the old
    axiom genuinely applied and was false, not vacuous);
  * evidence that the corrected hypothesis `IsUnit C.det` excludes
    exactly that counterexample;
  * positive instances of the corrected theorem: nonzero scalars, and a
    non-scalar rank-one update whose both sides compute to the true
    inverse `!![3/8, -1/8; -1/8, 3/8]`.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA checks the
  interface and its numerical consequences; it does not validate the
  neighboring `sherman_morrison` axiom.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Core.MatrixUpdates

open scoped Matrix

namespace Scaffold.Mathlib.Core.QA

/-!
## Computational helpers
-/

/-- Inverse of an invertible 1×1 scalar matrix, by the proved
nonsingular-inverse cancellation (`Matrix.inv_eq_left_inv`), not kernel
junk evaluation. -/
private theorem inv_fin_one (a : ℚ) (ha : a ≠ 0) :
    (!![a] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = !![a⁻¹] := by
  refine Matrix.inv_eq_left_inv (A := !![a]) (B := !![a⁻¹]) ?_
  ext i j
  fin_cases i
  fin_cases j
  simp [Matrix.mul_apply, Fin.sum_univ_one]
  exact inv_mul_cancel₀ ha

/-- Inverse of a 2×2 matrix with nonzero determinant, via the adjugate
formula; the `Ring.inverse` factor is discharged through the proved
`Ring.inverse_eq_inv`. -/
private theorem inv_fin_two_of (a b c d : ℚ) (h : a * d - b * c ≠ 0) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℚ)⁻¹
      = !![d / (a * d - b * c), -b / (a * d - b * c);
            -c / (a * d - b * c), a / (a * d - b * c)] := by
  rw [Matrix.inv_def, Matrix.det_fin_two_of, Matrix.adjugate_fin_two_of]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ring.inverse_eq_inv]
  all_goals field_simp

/-- Reduce a 1×1 matrix identity to its single entry. -/
private lemma eq_of_entry {M N : Matrix (Fin 1) (Fin 1) ℚ} (h : M 0 0 = N 0 0) :
    M = N := by
  ext i j
  fin_cases i
  fin_cases j
  exact h

/-!
## The retired statement, refuted at the scalar counterexample

The counterexample is `n = k = Fin 1`, `𝕜 = ℚ`, `A = U = V = !![1]`,
`C = !![0]`. Every hypothesis of the retired axiom holds, and the two
sides evaluate to `1` and `0`.
-/

/-- The retired axiom's middle-factor hypothesis held at the
counterexample: `(C + V A⁻¹ U).det = 1`, a unit. -/
theorem old_woodbury_middle_hyp_holds_QA :
    IsUnit (((!![0] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![1])⁻¹ * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ)).det := by
  have hmid : ((!![0] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![1])⁻¹ * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ) = !![1] := by
    rewrite [inv_fin_one 1 (by norm_num)]
    refine eq_of_entry ?_
    simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_one]
  rw [hmid, Matrix.det_fin_one_of]
  norm_num

/-- The retired axiom's sum hypothesis also held at the
counterexample: `(A + U C V).det = 1`, a unit (and `A.det = 1` is
immediate). The refutation below is therefore of a genuinely applicable,
false statement. -/
theorem old_woodbury_sum_hyp_holds_QA :
    IsUnit (((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![0]) * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ)).det := by
  have hsum : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![0]) * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ) = !![1] := by
    refine eq_of_entry ?_
    simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_one]
  rw [hsum, Matrix.det_fin_one_of]
  norm_num

/-- The retired `woodbury_identity` axiom, restated at its own shape for
`n = k = Fin 1` over `ℚ` and negated: at `A = U = V = 1`, `C = 0` the
left side is the true inverse `1` while the right side evaluates to
`1 - (0 + 1·1·1)⁻¹ = 0`. This consumes no axiom — the false statement is
refuted, not instantiated. -/
theorem old_woodbury_identity_refuted_QA :
    ¬ ∀ (A U C V : Matrix (Fin 1) (Fin 1) ℚ),
      IsUnit A.det → IsUnit (C + V * A⁻¹ * U).det → IsUnit (A + U * C * V).det →
      (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  intro h
  have hA : IsUnit (!![1] : Matrix (Fin 1) (Fin 1) ℚ).det := by
    rw [Matrix.det_fin_one_of]; norm_num
  have hins := h (!![1]) (!![1]) (!![0]) (!![1]) hA
    old_woodbury_middle_hyp_holds_QA old_woodbury_sum_hyp_holds_QA
  -- left side: the sum is `![1]`, so its inverse is `![1]`
  have hLHS : (((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![0]) * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ))⁻¹ = !![1] := by
    have hsum : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![0]) * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ) = !![1] := by
      refine eq_of_entry ?_
      simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_one]
    rw [hsum, inv_fin_one 1 (by norm_num)]
    refine eq_of_entry ?_
    norm_num
  -- right side: `1 - 1 · (0 + 1)⁻¹ · 1 = 0`
  have hRHS : (((!![1] : Matrix (Fin 1) (Fin 1) ℚ))⁻¹
      - (!![1])⁻¹ * (!![1]) * ((!![0] + (!![1]) * (!![1])⁻¹ * (!![1]))⁻¹)
        * (!![1]) * (!![1])⁻¹) = !![0] := by
    have hmid : ((!![0] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![1])⁻¹ * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ) = !![1] := by
      rewrite [inv_fin_one 1 (by norm_num)]
      refine eq_of_entry ?_
      simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_one]
    rewrite [hmid, inv_fin_one 1 (by norm_num)]
    refine eq_of_entry ?_
    simp [Matrix.mul_apply, Matrix.add_apply, Matrix.sub_apply, Fin.sum_univ_one]
  rw [hLHS, hRHS] at hins
  exact absurd hins (by decide)

/-- The corrected theorem's new hypothesis `IsUnit C.det` excludes the
counterexample: `C = 0` is singular. The repaired statement cannot be
instantiated where the retired one was false. -/
theorem corrected_C_hyp_excludes_counterexample_QA :
    ¬ IsUnit ((!![0] : Matrix (Fin 1) (Fin 1) ℚ)).det := by
  rw [Matrix.det_fin_one_of]
  norm_num

/-!
## Positive instances of the corrected theorem
-/

/-- Scalar positive instance, left side: at `A = 2`, `U = V = 1`,
`C = 3` the updated matrix is `5` and its true inverse is `1/5`,
computed directly from the definition. -/
theorem woodbury_scalar_sum_inv_QA :
    (((!![2] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![3]) * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ))⁻¹ = !![1 / 5] := by
  have hsum : ((!![2] + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![3]) * (!![1])) :
      Matrix (Fin 1) (Fin 1) ℚ) = !![5] := by
    refine eq_of_entry ?_
    simp only [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_one]
    norm_num
  rw [hsum, inv_fin_one 5 (by norm_num)]
  refine eq_of_entry ?_
  norm_num

/-- Scalar positive instance, right side: the corrected theorem's
right-hand side at the same fixture computes to the same `1/5` — pinned
by *consuming* `woodbury_identity` and then using the independent
left-side computation above. -/
theorem woodbury_scalar_rhs_QA :
    (((!![2] : Matrix (Fin 1) (Fin 1) ℚ))⁻¹
      - (!![2])⁻¹ * (!![1]) * ((!![3])⁻¹ + (!![1]) * (!![2])⁻¹ * (!![1]))⁻¹
        * (!![1]) * (!![2])⁻¹) = !![1 / 5] := by
  have hA : IsUnit (!![2] : Matrix (Fin 1) (Fin 1) ℚ).det := by
    rw [Matrix.det_fin_one_of]; norm_num
  have hC : IsUnit (!![3] : Matrix (Fin 1) (Fin 1) ℚ).det := by
    rw [Matrix.det_fin_one_of]; norm_num
  have hM : IsUnit (((!![3])⁻¹ + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![2])⁻¹ * (!![1]) :
      Matrix (Fin 1) (Fin 1) ℚ)).det := by
    have hmid : (((!![3])⁻¹ + (!![1] : Matrix (Fin 1) (Fin 1) ℚ) * (!![2])⁻¹ * (!![1])) :
        Matrix (Fin 1) (Fin 1) ℚ) = !![3⁻¹ + 2⁻¹] := by
      rewrite [inv_fin_one 3 (by norm_num), inv_fin_one 2 (by norm_num)]
      refine eq_of_entry ?_
      simp [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_one]
    rw [hmid, Matrix.det_fin_one_of]
    norm_num
  rewrite [← woodbury_identity (!![2]) (!![1]) (!![3]) (!![1]) hA hC hM]
  exact woodbury_scalar_sum_inv_QA

/-- The rank-one-update fixture: `A = diag 2 2` (`Fin 2 × Fin 2`). -/
private def A2 : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 2]

/-- The rank-one-update fixture: the all-ones column (`Fin 2 × Fin 1`). -/
private def U2 : Matrix (Fin 2) (Fin 1) ℚ := !![1; 1]

/-- The rank-one-update fixture: the scalar coupling `C = 1`. -/
private def C1 : Matrix (Fin 1) (Fin 1) ℚ := !![1]

/-- The rank-one-update fixture: the all-ones row (`Fin 1 × Fin 2`). -/
private def V2 : Matrix (Fin 1) (Fin 2) ℚ := !![1, 1]

/-- Non-scalar rank-one-update instance, left side: updating
`A = diag 2 2` by the all-ones rank-one term gives `!![3, 1; 1, 3]`,
whose true inverse `!![3/8, -1/8; -1/8, 3/8]` is computed directly from
the adjugate formula. -/
theorem woodbury_rank_one_sum_inv_QA :
    (A2 + U2 * C1 * V2)⁻¹ = !![3/8, -1/8; -1/8, 3/8] := by
  have hsum : (A2 + U2 * C1 * V2 : Matrix (Fin 2) (Fin 2) ℚ) = !![3, 1; 1, 3] := by
    simp only [A2, U2, C1, V2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_one, Fin.sum_univ_two] <;>
      norm_num
  rw [hsum, inv_fin_two_of 3 1 1 3 (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The fixture's inverse of `A`, computed from the adjugate formula:
`diag 2 2` inverts to `diag (1/2) (1/2)`. -/
private theorem A2_inv : A2⁻¹ = !![1/2, 0; 0, 1/2] := by
  simp only [A2]
  rw [inv_fin_two_of 2 0 0 2 (by norm_num)]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num

/-- The fixture's middle factor, computed: `C⁻¹ + V A⁻¹ U = 1 + 1 = 2`,
a unit — the corrected theorem's new middle hypothesis at this
instance. -/
private theorem middle1 : (C1⁻¹ + V2 * A2⁻¹ * U2 : Matrix (Fin 1) (Fin 1) ℚ) = !![2] := by
  rw [A2_inv]
  simp only [U2, C1, V2]
  refine eq_of_entry ?_
  simp only [Matrix.mul_apply, Matrix.add_apply, Fin.sum_univ_one, Fin.sum_univ_two]
  norm_num

/-- The fixture's middle factor inverts to `1/2`:
`(C⁻¹ + V A⁻¹ U)⁻¹ = (![1] + ![1])⁻¹ = 1/2`, computed. -/
private theorem middle1_inv : (C1⁻¹ + V2 * A2⁻¹ * U2)⁻¹ = !![1/2] := by
  rw [middle1, inv_fin_one 2 (by norm_num)]
  refine eq_of_entry ?_
  norm_num

/-- Non-scalar rank-one-update instance, right side: the corrected
theorem's right-hand side at the same fixture — with the nontrivial
middle factor `(C⁻¹ + V A⁻¹ U)⁻¹ = (![1] + ![1])⁻¹ = 1/2` — computes to
the same `!![3/8, -1/8; -1/8, 3/8]`, again by consuming
`woodbury_identity` and finishing with the independent left side. -/
theorem woodbury_identity_rank_one_QA :
    A2⁻¹ - A2⁻¹ * U2 * (C1⁻¹ + V2 * A2⁻¹ * U2)⁻¹ * V2 * A2⁻¹
      = !![3/8, -1/8; -1/8, 3/8] := by
  have hA : IsUnit A2.det := by
    simp only [A2, Matrix.det_fin_two_of]; norm_num
  have hC : IsUnit C1.det := by
    simp only [C1, Matrix.det_fin_one_of]; norm_num
  have hM : IsUnit (C1⁻¹ + V2 * A2⁻¹ * U2).det := by
    rw [middle1, Matrix.det_fin_one_of]; norm_num
  rw [← woodbury_identity A2 U2 C1 V2 hA hC hM]
  exact woodbury_rank_one_sum_inv_QA

end Scaffold.Mathlib.Core.QA
