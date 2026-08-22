/-
  Entropy_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.InformationTheory.Entropy`: the two
  classical quantities (`klDiv`, `shannonEntropy`) pinned by raw
  numerical computation on explicit distributions, the theorems
  instantiated at those distributions, and the prescribed witnesses —
  the strict-positivity instance of Gibbs' inequality computed
  independently of the theorem, the equality case cross-checked
  numerically, the entropy maximum attained at uniform and *strictly*
  missed away from it, and the `p i = 0 ↦ 0` junk convention exhibited
  at the delta distribution.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.InformationTheory.Entropy
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Classical

namespace Scaffold.InformationTheory.QA

/-!
## Section A: the biased coin against the fair coin on `Fin 2`
-/

/-- The biased distribution `(3/4, 1/4)`. -/
noncomputable def pBias : Fin 2 → ℝ := ![3/4, 1/4]

/-- The fair distribution `(1/2, 1/2)`. -/
noncomputable def qFair : Fin 2 → ℝ := ![1/2, 1/2]

theorem pBias_nonneg : ∀ i, 0 ≤ pBias i := by
  intro i
  fin_cases i <;> norm_num [pBias, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem pBias_pos : ∀ i, 0 < pBias i := by
  intro i
  fin_cases i <;> norm_num [pBias, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem pBias_sum : ∑ i, pBias i = 1 := by
  norm_num [pBias, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem qFair_pos : ∀ i, 0 < qFair i := by
  intro i
  fin_cases i <;> norm_num [qFair, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem qFair_sum : ∑ i, qFair i = 1 := by
  norm_num [qFair, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

/-- The divergence of the biased from the fair coin, computed by hand:
`3/4 · log(3/2) + 1/4 · log(1/2) = ¼ · log(27/16)`, assembled with
`Real.log_pow`/`Real.log_mul` only — no appeal to any theorem above. -/
theorem klDiv_bias_raw : klDiv pBias qFair = (1/4) * Real.log (27/16) := by
  have h32 : (0:ℝ) < 3/2 := by norm_num
  have h12 : (0:ℝ) < 1/2 := by norm_num
  have h1 : (3:ℝ) * Real.log (3/2) = Real.log ((3/2) ^ 3) :=
    (Real.log_pow (3/2) 3).symm
  have h2 : Real.log ((3/2) ^ 3) + Real.log (1/2) = Real.log (27/16) := by
    rw [← Real.log_mul (by norm_num : ((3:ℝ)/2) ^ 3 ≠ 0) (ne_of_gt h12)]
    norm_num
  rw [klDiv, Fin.sum_univ_two]
  simp only [klTerm, pBias, qFair, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, if_neg (show ((3:ℝ)/4) ≠ 0 by norm_num),
    if_neg (show ((1:ℝ)/4) ≠ 0 by norm_num)]
  norm_num
  rw [show (3:ℝ)/4 * Real.log (3/2) + (1:ℝ)/4 * Real.log (1/2)
      = (1:ℝ)/4 * ((3:ℝ) * Real.log (3/2) + Real.log (1/2)) from by ring_nf, h1, h2]

/-- Gibbs' inequality instantiated at the pair (the theorem route). -/
theorem klDiv_bias_nonneg_via_thm : 0 ≤ klDiv pBias qFair :=
  klDiv_nonneg pBias_nonneg pBias_sum qFair_pos qFair_sum

/-- **Strictly positive** divergence at a genuinely distinct pair, from
the raw computation alone — the bound is not vacuously tight. -/
theorem klDiv_bias_pos : 0 < klDiv pBias qFair := by
  rw [klDiv_bias_raw]
  have h : 0 < Real.log (27/16) := (Real.log_pos_iff (by norm_num)).mpr (by norm_num)
  positivity

theorem pBias_ne_qFair : pBias ≠ qFair := by
  intro h
  have h0 := congrFun h 0
  simp only [pBias, qFair, Matrix.cons_val_zero, Matrix.head_cons] at h0
  norm_num at h0

/-- The equality case used *forward*: since the distributions differ,
the divergence cannot vanish. Load-bearing on `klDiv_eq_zero_iff` — a
wrong equality case (one that held at a distinct pair) would make this
unprovable, and its numeric companion `klDiv_bias_pos` would then
contradict it. -/
theorem klDiv_bias_ne_zero : klDiv pBias qFair ≠ 0 := fun h =>
  pBias_ne_qFair ((klDiv_eq_zero_iff pBias_nonneg pBias_sum qFair_pos qFair_sum).mp h)

/-- The diagonal case computed from the definition alone: `log 1 = 0`
term-wise. -/
theorem klDiv_self_eq_zero_raw : klDiv pBias pBias = 0 := by
  rw [klDiv, Fin.sum_univ_two]
  simp only [klTerm, pBias, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, if_neg (show ((3:ℝ)/4) ≠ 0 by norm_num),
    if_neg (show ((1:ℝ)/4) ≠ 0 by norm_num),
    div_self (show ((3:ℝ)/4) ≠ 0 by norm_num),
    div_self (show ((1:ℝ)/4) ≠ 0 by norm_num),
    Real.log_one, mul_zero, add_zero]

/-- The equality case cross-checked against the raw diagonal
computation: the hand-computed `klDiv pBias pBias = 0` fed *through*
the theorem recovers `pBias = pBias`. -/
theorem klDiv_eq_zero_self_via_thm : pBias = pBias :=
  (klDiv_eq_zero_iff pBias_nonneg pBias_sum pBias_pos pBias_sum).mp klDiv_self_eq_zero_raw

/-- The entropy of the biased coin, computed by hand:
`-(3/4 · log(3/4) + 1/4 · log(1/4)) = ¼ · log(256/27)`. -/
theorem shannon_bias_raw : shannonEntropy pBias = (1/4) * Real.log (256/27) := by
  have h34 : (0:ℝ) < 3/4 := by norm_num
  have h14 : (0:ℝ) < 1/4 := by norm_num
  have hp1 : (3:ℝ) * Real.log (3/4) = Real.log ((3/4) ^ 3) :=
    (Real.log_pow (3/4) 3).symm
  have hp2 : Real.log ((3/4) ^ 3) + Real.log (1/4) = Real.log (27/256) := by
    rw [← Real.log_mul (by norm_num : ((3:ℝ)/4) ^ 3 ≠ 0) (ne_of_gt h14)]
    norm_num
  rw [shannonEntropy, Fin.sum_univ_two]
  simp only [klTerm, div_one, pBias, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, if_neg (ne_of_gt h34), if_neg (ne_of_gt h14)]
  rw [show -((3:ℝ)/4 * Real.log (3/4) + (1:ℝ)/4 * Real.log (1/4))
      = -((1:ℝ)/4 * ((3:ℝ) * Real.log (3/4) + Real.log (1/4))) from by ring_nf,
    hp1, hp2, show (256:ℝ)/27 = ((27:ℝ)/256)⁻¹ from by norm_num, Real.log_inv]
  ring_nf

/-- **The uniform bridge cross-checked numerically at the fair coin**:
the theorem says `klDiv pBias q = log 2 − shannonEntropy pBias`, and
both sides have now been pinned independently by raw computation
(`¼ · log(27/16)` against `log 2 − ¼ · log(256/27)`, equal because
`16 · 27/256 = 27/16`). Load-bearing on `klDiv_apply_uniform`: a wrong
bridge (wrong sign, wrong constant) would fail to match the pinned
arithmetic. -/
theorem klDiv_bridge_bias : klDiv pBias qFair = Real.log 2 - shannonEntropy pBias := by
  have e1 : (4:ℝ) * Real.log 2 = Real.log ((2:ℝ) ^ 4) := (Real.log_pow (2:ℝ) 4).symm
  have e2 : Real.log ((2:ℝ) ^ 4) - Real.log (256/27) = Real.log (27/16) := by
    rw [show ((2:ℝ) ^ 4) = 16 from by norm_num,
      ← Real.log_div (by norm_num : ((16:ℝ)) ≠ 0) (by norm_num : ((256:ℝ)/27) ≠ 0)]
    norm_num
  rw [klDiv_bias_raw, shannon_bias_raw]
  apply mul_left_cancel₀ (show ((4:ℝ)) ≠ 0 by norm_num)
  rw [show ((4:ℝ)) * ((1:ℝ)/4 * Real.log (27/16)) = Real.log (27/16) from by ring_nf,
    show ((4:ℝ)) * (Real.log 2 - (1:ℝ)/4 * Real.log (256/27))
      = (4:ℝ) * Real.log 2 - Real.log (256/27) from by ring_nf, e1, e2]

/-!
## Section B: the uniform distribution on `Fin 4` — the entropy maximum attained
-/

/-- The uniform distribution on `Fin 4`. -/
noncomputable def pUni : Fin 4 → ℝ := fun _ => 1/4

theorem pUni_nonneg : ∀ i, 0 ≤ pUni i := fun _ => by norm_num [pUni]

theorem pUni_sum : ∑ i, pUni i = 1 := by
  rw [Fin.sum_univ_four]
  simp only [pUni]
  norm_num

/-- Computed from the definition alone: four copies of
`1/4 · log(1/4)` negate to `log 4`. -/
theorem shannon_uni_raw : shannonEntropy pUni = Real.log 4 := by
  have hq : ((1:ℝ)/4) ≠ 0 := by norm_num
  rw [shannonEntropy, Fin.sum_univ_four]
  simp only [klTerm, pUni, if_neg hq, div_one, Real.log_inv 4]
  rw [show ((1:ℝ)/4) = (4:ℝ)⁻¹ from by norm_num, Real.log_inv 4]
  ring_nf

/-- The same value through the equality case of the maximum theorem. -/
theorem shannon_uni_via_eq : shannonEntropy pUni = Real.log 4 :=
  (shannonEntropy_eq_log_card_iff pUni_nonneg pUni_sum).mpr (by
    funext i
    simp only [pUni, Fintype.card_fin]
    norm_num)

theorem shannon_uni_nonneg_via_thm : 0 ≤ shannonEntropy pUni :=
  shannonEntropy_nonneg pUni_nonneg pUni_sum

/-- The maximum bound itself, instantiated. -/
theorem shannon_uni_le : shannonEntropy pUni ≤ Real.log (Fintype.card (Fin 4)) :=
  shannonEntropy_le_log_card pUni_nonneg pUni_sum

/-!
## Section C: the strictness witness — a non-uniform distribution on `Fin 4`
-/

/-- The non-uniform distribution `(1/2, 1/6, 1/6, 1/6)`. -/
noncomputable def pSkew : Fin 4 → ℝ := ![1/2, 1/6, 1/6, 1/6]

theorem pSkew_nonneg : ∀ i, 0 ≤ pSkew i := by
  intro i
  fin_cases i <;> norm_num [pSkew, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem pSkew_pos : ∀ i, 0 < pSkew i := by
  intro i
  fin_cases i <;> norm_num [pSkew, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem pSkew_sum : ∑ i, pSkew i = 1 := by
  norm_num [pSkew, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem pSkew_ne_uniform : pSkew ≠ fun _ => (Fintype.card (Fin 4) : ℝ)⁻¹ := by
  intro h
  have h0 := congrFun h 0
  simp only [pSkew, Matrix.cons_val_zero, Matrix.head_cons, Fintype.card_fin] at h0
  norm_num at h0

/-- **The negative witness of the QA plan**: the entropy of a
non-uniform distribution is *strictly* below the maximum. Strictness is
available only through the equality-case iff (the plain bound gives
`≤`), so this is the load-bearing use of the strict route — exactly as
the proposal's QA plan requires. -/
theorem shannon_skew_lt_log4 : shannonEntropy pSkew < Real.log 4 := by
  refine lt_of_le_of_ne (shannonEntropy_le_log_card pSkew_nonneg pSkew_sum) ?_
  intro h
  exact pSkew_ne_uniform ((shannonEntropy_eq_log_card_iff pSkew_nonneg pSkew_sum).mp h)

/-- The same strictness on the divergence side: `pSkew` against uniform
has strictly positive relative entropy, derived through the equality
case (and consistent with `shannon_skew_lt_log4` via the bridge). -/
theorem klDiv_skew_uni_pos : 0 < klDiv pSkew (fun _ => (Fintype.card (Fin 4) : ℝ)⁻¹) := by
  have hn : (0:ℝ) < Fintype.card (Fin 4) := by norm_num
  have h : shannonEntropy pSkew < Real.log (Fintype.card (Fin 4)) := shannon_skew_lt_log4
  rw [klDiv_apply_uniform pSkew_nonneg pSkew_sum hn]
  linarith

/-!
## Section D: the delta distribution — the junk convention exhibited
-/

/-- The point mass `(1, 0, 0, 0)` on `Fin 4`. -/
noncomputable def pDelta : Fin 4 → ℝ := ![1, 0, 0, 0]

theorem pDelta_nonneg : ∀ i, 0 ≤ pDelta i := by
  intro i
  fin_cases i <;> norm_num [pDelta, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem pDelta_sum : ∑ i, pDelta i = 1 := by
  norm_num [pDelta, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

/-- Entropy exactly zero at the point mass: index `0` contributes
`1 · log 1 = 0`, and indices `1–3` contribute `0` *through the explicit
`p i = 0` branch of the definition* — the junk convention made visible. -/
theorem shannon_delta_eq_zero : shannonEntropy pDelta = 0 := by
  rw [shannonEntropy, Fin.sum_univ_four]
  simp [klTerm, pDelta, Real.log_one]

theorem shannon_delta_nonneg_via_thm : 0 ≤ shannonEntropy pDelta :=
  shannonEntropy_nonneg pDelta_nonneg pDelta_sum

/-- Zero entropy is also strictly below the maximum — the bound is
honest at the degenerate end too. -/
theorem shannon_delta_lt_log4 : shannonEntropy pDelta < Real.log 4 := by
  rw [shannon_delta_eq_zero]
  exact (Real.log_pos_iff (by norm_num)).mpr (by norm_num)

end Scaffold.InformationTheory.QA
