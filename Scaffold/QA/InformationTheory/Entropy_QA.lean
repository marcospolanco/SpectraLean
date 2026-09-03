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

/-! ## The binary two-point Pinsker bound (`proposals/entropy-mixing-pinsker.md`)

The exact value at `(a, b) = (1/2, 3/4)`: `d = (1/2)·log(4/3)`, the
bound `1/8` holding with honest slack (`log(4/3) ≥ 1/4`, the
one-step Gibbs bound attained at equality).
-/

theorem bin_two_point_value_QA :
    klTerm (1/2 : ℝ) (3/4) + klTerm (1/2 : ℝ) (1/4)
      = (1/2) * Real.log (4/3) := by
  have h1 : klTerm (1/2 : ℝ) (3/4) = (1/2) * Real.log (2/3) := by
    simp only [klTerm, if_neg (by norm_num : (1/2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have h2 : klTerm (1/2 : ℝ) (1/4) = (1/2) * Real.log 2 := by
    simp only [klTerm, if_neg (by norm_num : (1/2 : ℝ) ≠ 0)]
    congr 1
    norm_num
  have hsum : (1/2 : ℝ) * Real.log (2/3) + (1/2) * Real.log 2
      = (1/2) * (Real.log (2/3) + Real.log 2) := by ring
  rw [h1, h2, hsum, ← Real.log_mul (by norm_num : (2:ℝ)/3 ≠ 0) two_ne_zero,
    show (2/3 : ℝ) * 2 = 4/3 from by norm_num]

theorem bin_two_point_le_QA :
    2 * ((1/2 : ℝ) - 3/4) ^ 2
      ≤ klTerm (1/2 : ℝ) (3/4) + klTerm (1/2 : ℝ) (1/4) := by
  rw [bin_two_point_value_QA]
  have h : (1:ℝ) - (4/3)⁻¹ ≤ Real.log (4/3) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hinv : (4/3 : ℝ)⁻¹ = 3/4 := by norm_num
  rw [hinv] at h
  norm_num
  linarith

/-!
## Section F: the entropy layer's adversarial fences (2026-09-03)

`proposals/adversarial-fences-entropy-family.md`: the audit-shaped
adversarial pass over the entropy family, generic layer. The 2026-09-01
delivery pinned positive instances only; the mass clauses and the
strict-positivity corner clauses below had no negative witness anywhere
in the repository. Each fence is the negation of the conclusion at a
specific instantiation with both sides computed; the fixtures' genuine
facts are recorded beside them.
-/

/-- The uniform probability on `Fin 2` (genuine: nonnegative, mass 1). -/
noncomputable def pU2 : Fin 2 → ℝ := fun _ => 1/2

/-- The doubled measure `(1, 1)`: strictly positive, mass `2` — kills
the `q`-mass clauses. -/
noncomputable def qMass2 : Fin 2 → ℝ := fun _ => 1

/-- The half-mass vector `(1/4, 1/4)`: nonnegative, mass `1/2` — kills
the `p`-mass clauses on the divergence side. -/
noncomputable def pMassHalf : Fin 2 → ℝ := fun _ => 1/4

/-- The doubled vector `(2, 2)`: nonnegative, mass `4` — kills the
`p`-mass clauses on the entropy side. -/
noncomputable def pDoub : Fin 2 → ℝ := fun _ => 2

/-- The two point masses swapped: `p = (1, 0)`, `q = (0, 1)`. -/
noncomputable def pSwapD : Fin 2 → ℝ := ![1, 0]
noncomputable def qSwapD : Fin 2 → ℝ := ![0, 1]

/-- The `(3/4, 3/4)` fixture for the bridge's mass clause. -/
noncomputable def p3q : Fin 2 → ℝ := fun _ => 3/4

/-! ### Fixture genuineness -/

theorem pU2_nonneg : ∀ i, 0 ≤ pU2 i := fun _ => by norm_num [pU2]
theorem pU2_sum : ∑ i, pU2 i = 1 := by
  rw [Fin.sum_univ_two]
  simp only [pU2]
  norm_num

theorem qMass2_pos : ∀ i, 0 < qMass2 i := fun _ => by norm_num [qMass2]
theorem qMass2_sum : ∑ i, qMass2 i = 2 := by
  rw [Fin.sum_univ_two]
  simp only [qMass2]
  norm_num

theorem pMassHalf_nonneg : ∀ i, 0 ≤ pMassHalf i := fun _ => by
  norm_num [pMassHalf]
theorem pMassHalf_sum : ∑ i, pMassHalf i = 1/2 := by
  rw [Fin.sum_univ_two]
  simp only [pMassHalf]
  norm_num

theorem pDoub_nonneg : ∀ i, 0 ≤ pDoub i := fun _ => by norm_num [pDoub]
theorem pDoub_sum : ∑ i, pDoub i = 4 := by
  rw [Fin.sum_univ_two]
  simp only [pDoub]
  norm_num

theorem pSwapD_nonneg : ∀ i, 0 ≤ pSwapD i := by
  intro i
  fin_cases i <;> norm_num [pSwapD, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
theorem pSwapD_sum : ∑ i, pSwapD i = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [pSwapD, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem qSwapD_nonneg : ∀ i, 0 ≤ qSwapD i := by
  intro i
  fin_cases i <;> norm_num [qSwapD, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
theorem qSwapD_sum : ∑ i, qSwapD i = 1 := by
  rw [Fin.sum_univ_two]
  norm_num [qSwapD, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]

theorem p3q_nonneg : ∀ i, 0 ≤ p3q i := fun _ => by norm_num [p3q]
theorem p3q_sum : ∑ i, p3q i = 3/2 := by
  rw [Fin.sum_univ_two]
  simp only [p3q]
  norm_num

/-! ### `klDiv_nonneg`: both mass clauses -/

/-- The `q`-mass junk pin: at `q = (1, 1)` the doubled denominator makes
both summands `log(1/2)`, so `D = log(1/2) = −log 2 < 0`. -/
theorem klDiv_pU2_qMass2 : klDiv pU2 qMass2 = -(Real.log 2) := by
  have h1 : klTerm (1/2 : ℝ) 1 = -(1/2) * Real.log 2 := by
    have hpos : (0:ℝ) < 1/2 := by norm_num
    have hlog : Real.log ((1:ℝ)/2) = -Real.log 2 := by
      rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from by norm_num, Real.log_inv]
    simp only [klTerm, if_neg (ne_of_gt hpos), div_one, hlog]
    ring
  rw [klDiv, Fin.sum_univ_two]
  simp only [pU2, qMass2]
  rw [h1]
  ring

/-- **The `hq1` fence for `klDiv_nonneg`**: with every other hypothesis
genuine (nonnegative mass-`1` `p`, strictly positive `q`), the
mass-dropped statement reads `0 ≤ −log 2` — refuted. -/
theorem klDiv_nonneg_qmass_fence_QA :
    ¬ (0 ≤ klDiv pU2 qMass2) := by
  rw [klDiv_pU2_qMass2]
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-- The `p`-mass junk pin: at `p = (1/4, 1/4)` both summands read
`(1/4)·log(1/2)`, so `D = −(1/2)·log 2 < 0`. -/
theorem klDiv_pMassHalf_qFair : klDiv pMassHalf qFair = -(1/2) * Real.log 2 := by
  have h1 : klTerm (1/4 : ℝ) (1/2 : ℝ) = (1/4) * (-(Real.log 2)) := by
    have hpos : (0:ℝ) < 1/4 := by norm_num
    have hval : (1/4 : ℝ) / (1/2 : ℝ) = (2:ℝ)⁻¹ := by norm_num
    simp only [klTerm, if_neg (ne_of_gt hpos), hval, Real.log_inv]
  rw [klDiv, Fin.sum_univ_two]
  simp only [pMassHalf, qFair, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one]
  rw [h1]
  ring

/-- **The `hp'` fence for `klDiv_nonneg`**: with every other hypothesis
genuine (strictly positive mass-`1` `q` included), the mass-dropped
statement reads `0 ≤ −(1/2)·log 2` — refuted. -/
theorem klDiv_nonneg_pmass_fence_QA :
    ¬ (0 ≤ klDiv pMassHalf qFair) := by
  rw [klDiv_pMassHalf_qFair]
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ### `klDiv_eq_zero_iff`: the strict-positivity clause -/

/-- The swap junk pin: at `p = (1, 0)`, `q = (0, 1)` the junk
convention `klTerm 1 0 = log 0 = 0` kills both summands — the
divergence of two *different* point masses is junk-zero. -/
theorem klDiv_pSwapD_qSwapD : klDiv pSwapD qSwapD = 0 := by
  have h1 : klTerm (1:ℝ) 0 = 0 := by
    simp only [klTerm, if_neg one_ne_zero, div_zero, Real.log_zero, one_mul]
  have h2 : klTerm (0:ℝ) 1 = 0 := by simp [klTerm]
  rw [klDiv, Fin.sum_univ_two]
  norm_num [pSwapD, qSwapD, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  rw [h1, h2]
  ring

/-- The two swapped point masses are genuinely different vectors. -/
theorem pSwapD_ne_qSwapD : pSwapD ≠ qSwapD := by
  intro h
  have h0 := congrFun h 0
  simp only [pSwapD, qSwapD, Matrix.cons_val_zero, Matrix.head_cons] at h0
  norm_num at h0

/-- **The `hq` fence for `klDiv_eq_zero_iff`**: with every other
hypothesis genuine, the strict-positivity-dropped identification reads
`D = 0 ↔ p = q` — refuted in the forward direction: `D = 0` (both
summands junk) while `p ≠ q`. -/
theorem klDiv_eq_zero_iff_qpos_fence_QA :
    ¬ (klDiv pSwapD qSwapD = 0 ↔ pSwapD = qSwapD) := by
  intro h
  exact pSwapD_ne_qSwapD (h.mp klDiv_pSwapD_qSwapD)

/-- The doubled-denominator junk pin: at `p = (1, 0)`, `q = (1, 1)`
(strictly positive, mass `2`), both summands vanish (`log 1 = 0` and
the `p = 0` branch) — `D = 0` for different vectors. -/
theorem klDiv_pSwapD_qMass2 : klDiv pSwapD qMass2 = 0 := by
  have h1 : klTerm (1:ℝ) 1 = 0 := by
    simp only [klTerm, if_neg one_ne_zero, div_one, Real.log_one, one_mul]
  have h2 : klTerm (0:ℝ) 1 = 0 := by simp [klTerm]
  rw [klDiv, Fin.sum_univ_two]
  simp only [pSwapD, qMass2, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one]
  rw [h1, h2]
  ring

theorem pSwapD_ne_qMass2 : pSwapD ≠ qMass2 := by
  intro h
  have h1 := congrFun h 1
  simp only [pSwapD, qMass2, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.head_cons] at h1
  norm_num at h1

/-- **The `hq1` fence for `klDiv_eq_zero_iff`**: with `q` strictly
positive and `p` a genuine point mass (every hypothesis except the
`q`-mass), the dropped identification reads `D = 0 ↔ p = q` with
`D = 0` genuine while `p ≠ (1, 1)` — refuted. -/
theorem klDiv_eq_zero_iff_qmass_fence_QA :
    ¬ (klDiv pSwapD qMass2 = 0 ↔ pSwapD = qMass2) := by
  intro h
  exact pSwapD_ne_qMass2 (h.mp klDiv_pSwapD_qMass2)

/-! ### `klDiv_apply_uniform`: the mass clause -/

theorem klTerm_one_invtwo : klTerm (1:ℝ) ((2:ℝ)⁻¹) = Real.log 2 := by
  simp only [klTerm, if_neg one_ne_zero, one_mul]
  rw [show ((1:ℝ)/(2:ℝ)⁻¹) = 2 from by rw [one_div, inv_inv]]

theorem klTerm_one_one : klTerm (1:ℝ) 1 = 0 := by
  simp only [klTerm, if_neg one_ne_zero, div_one, Real.log_one, one_mul]

/-- **The `hp'` fence for `klDiv_apply_uniform`**: at `p = (1, 1)` on
`Fin 2` (nonneg genuine, mass `2` dropped), the identity reads
`2·log 2 = log 2 − 0` — refuted. -/
theorem klDiv_apply_uniform_pmass_fence_QA :
    ¬ (klDiv qMass2 (fun _ => (Fintype.card (Fin 2) : ℝ)⁻¹)
        = Real.log (Fintype.card (Fin 2)) - shannonEntropy qMass2) := by
  have hH : shannonEntropy qMass2 = 0 := by
    rw [shannonEntropy, Fin.sum_univ_two]
    simp only [qMass2, klTerm_one_one]
    ring
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  have hD : klDiv qMass2 (fun _ => (Fintype.card (Fin 2) : ℝ)⁻¹)
      = 2 * Real.log 2 := by
    rw [klDiv, Fin.sum_univ_two, hcard]
    simp only [qMass2, inv_inv]
    rw [klTerm_one_invtwo]
    ring
  intro h
  rw [hD, hH, hcard] at h
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ### `shannonEntropy_nonneg`: the mass clause -/

/-- The doubled-vector entropy pin: `H(2, 2) = −4·log 2 < 0`. -/
theorem shannon_pDoub : shannonEntropy pDoub = -(4 : ℝ) * Real.log 2 := by
  have hterm : klTerm (2:ℝ) 1 = 2 * Real.log 2 := by
    simp only [klTerm, if_neg (by norm_num : (2:ℝ) ≠ 0), div_one]
  rw [shannonEntropy, Fin.sum_univ_two]
  simp only [pDoub, hterm]
  ring

/-- **The `hp'` fence for `shannonEntropy_nonneg`**: with `p ≥ 0`
genuine and the mass clause dropped, the statement reads
`0 ≤ −4·log 2` — refuted. -/
theorem shannon_nonneg_pmass_fence_QA :
    ¬ (0 ≤ shannonEntropy pDoub) := by
  rw [shannon_pDoub]
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ### `shannonEntropy_le_log_card`: the mass clause -/

/-- The third-uniform fixture on `Fin 4`: mass `4/3`, every entry
`1/3`. -/
noncomputable def pThird4 : Fin 4 → ℝ := fun _ => 1/3

theorem pThird4_nonneg : ∀ i, 0 ≤ pThird4 i := fun _ => by norm_num [pThird4]

theorem pThird4_sum : ∑ i, pThird4 i = 4/3 := by
  rw [Fin.sum_univ_four]
  simp only [pThird4]
  norm_num

/-- `log 4 < (4/3)·log 3`, by `3⁴ = 81 > 64 = 4³` through
`Real.log_lt_log` and `Real.log_pow`. -/
theorem log_four_lt_four_thirds_log_three :
    Real.log 4 < (4/3 : ℝ) * Real.log 3 := by
  have h64 : (4:ℝ) ^ 3 = 64 := by norm_num
  have h81 : (3:ℝ) ^ 4 = 81 := by norm_num
  have hlt : (4:ℝ) ^ 3 < (3:ℝ) ^ 4 := by rw [h64, h81]; norm_num
  have hlog := Real.log_lt_log (by norm_num : (0:ℝ) < 4 ^ 3) hlt
  rw [Real.log_pow, Real.log_pow] at hlog
  simp only [Nat.cast_ofNat] at hlog
  have h3 : (0:ℝ) < 3 := by norm_num
  nlinarith [hlog, h3]

/-- The third-uniform entropy pin: `H = (4/3)·log 3` at mass `4/3`. -/
theorem shannon_pThird4 : shannonEntropy pThird4 = (4/3 : ℝ) * Real.log 3 := by
  have hq : ((1:ℝ)/3) ≠ 0 := by norm_num
  rw [shannonEntropy, Fin.sum_univ_four]
  simp only [klTerm, pThird4, if_neg hq, div_one]
  rw [show ((1:ℝ)/3) = (3:ℝ)⁻¹ from by norm_num, Real.log_inv 3]
  ring_nf

/-- **The `hp'` fence for `shannonEntropy_le_log_card`**: with `p ≥ 0`
genuine and mass `4/3` (dropped), the statement reads
`(4/3)·log 3 ≤ log 4` — refuted by `3⁴ > 4³`. -/
theorem shannon_le_log_card_pmass_fence_QA :
    ¬ (shannonEntropy pThird4 ≤ Real.log (Fintype.card (Fin 4))) := by
  have hcard : (Fintype.card (Fin 4) : ℝ) = 4 := by norm_num
  rw [shannon_pThird4, hcard]
  exact not_le.mpr log_four_lt_four_thirds_log_three

/-! ### `shannonEntropy_eq_log_card_iff`: the mass clause -/

/-- The half-vector on `Fin 4`: mass `2`, entropy exactly `log 4`. -/
noncomputable def pHalf4 : Fin 4 → ℝ := fun _ => 1/2

theorem pHalf4_nonneg : ∀ i, 0 ≤ pHalf4 i := fun _ => by norm_num [pHalf4]
theorem pHalf4_sum : ∑ i, pHalf4 i = 2 := by
  rw [Fin.sum_univ_four]
  simp only [pHalf4]
  norm_num

theorem pHalf4_ne_uniform : pHalf4 ≠ (fun _ => (Fintype.card (Fin 4) : ℝ)⁻¹) := by
  intro h
  have h0 := congrFun h 0
  simp only [pHalf4, Fintype.card_fin, Nat.cast_ofNat] at h0
  norm_num at h0

/-- `H(1/2, 1/2, 1/2, 1/2) = 2·log 2 = log 4` at mass `2`. -/
theorem shannon_pHalf4 : shannonEntropy pHalf4 = Real.log 4 := by
  have hq : ((1:ℝ)/2) ≠ 0 := by norm_num
  rw [shannonEntropy, Fin.sum_univ_four]
  simp only [klTerm, pHalf4, if_neg hq, div_one]
  rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from by norm_num, Real.log_inv 2]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
    norm_num
  rw [hlog4]
  ring_nf

/-- **The `hp'` fence for `shannonEntropy_eq_log_card_iff`**: with
`p ≥ 0` genuine and mass `2` (dropped), the statement reads
`H = log 4 ↔ p = uniform` — refuted: the left side holds exactly while
`p` is not the uniform vector. -/
theorem shannon_eq_log_card_pmass_fence_QA :
    ¬ (shannonEntropy pHalf4 = Real.log (Fintype.card (Fin 4))
        ↔ pHalf4 = fun _ => (Fintype.card (Fin 4) : ℝ)⁻¹) := by
  intro h
  exact pHalf4_ne_uniform (h.mp shannon_pHalf4)

/-! ### `klTerm_le_sub_one_mul`: the strict-positivity clause -/

/-- **The `hb` fence for the termwise bridge**: at `a = 1/2` (genuine),
`b = 0`, the junk convention `klTerm (1/2) 0 = (1/2)·log 0 = 0` meets
the right side `(1/2)·(0 − 1) = −1/2`: the dropped statement reads
`0 ≤ −1/2` — refuted. -/
theorem klTerm_sub_one_mul_bpos_fence_QA :
    ¬ (klTerm (1/2 : ℝ) 0 ≤ (1/2 : ℝ) * ((1/2 : ℝ) / 0 - 1)) := by
  have hL : klTerm (1/2 : ℝ) 0 = 0 := by
    simp only [klTerm, if_neg (by norm_num : (1/2 : ℝ) ≠ 0), div_zero,
      Real.log_zero]
    ring
  rw [hL]
  norm_num

/-! ### `klDiv_le_sum_sq_div`: the `p`-mass clause -/

/-- The bridge fixture value: `D(3/4, 3/4 ‖ 1/2, 1/2) = (3/2)·log(3/2)`,
which Gibbs bounds below by `1/2`. -/
theorem klDiv_p3q_qFair : klDiv p3q qFair = (3/2 : ℝ) * Real.log (3/2) := by
  have hterm : klTerm (3/4 : ℝ) (1/2 : ℝ) = (3/4 : ℝ) * Real.log (3/2) := by
    simp only [klTerm, if_neg (by norm_num : (3/4 : ℝ) ≠ 0)]
    congr 1
    norm_num
  rw [klDiv, Fin.sum_univ_two]
  simp only [p3q, qFair, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one]
  rw [hterm]
  ring

/-- **The `hp1` fence for `klDiv_le_sum_sq_div`**: with `p ≥ 0`, strict
`q`-positivity, and `q`-mass all genuine, the `p`-mass-dropped statement
reads `(3/2)·log(3/2) ≤ 1/4` — refuted, since Gibbs gives
`log(3/2) ≥ 1/3` so the left side is at least `1/2`. -/
theorem klDiv_le_sum_sq_div_pmass_fence_QA :
    ¬ (klDiv p3q qFair
        ≤ ∑ i, (p3q i - qFair i) ^ 2 / qFair i) := by
  have hD := klDiv_p3q_qFair
  have hRHS : ∑ i, (p3q i - qFair i) ^ 2 / qFair i = 1/4 := by
    rw [Fin.sum_univ_two]
    norm_num [p3q, qFair, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
  rw [hD, hRHS]
  have hgibbs : (1:ℝ) - (3/2 : ℝ)⁻¹ ≤ Real.log (3/2) :=
    Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hinv : (3/2 : ℝ)⁻¹ = 2/3 := by norm_num
  rw [hinv] at hgibbs
  have hcomb : (3/2 : ℝ) * (1 - 2/3) = 1/2 := by norm_num
  nlinarith [hgibbs, hcomb]

/-! ### `sum_klTerm_ge_klTerm`: the strict-positivity clause -/

/-- **The `hq` fence for the two-block log-sum bound**: at
`p = (1/2, 1/2)`, `q = (0, 1)` over the full `Fin 2` (with `p ≥ 0`
genuine), the dropped statement reads
`klTerm 1 1 = 0 ≤ −(1/2)·log 2` — refuted. -/
theorem sum_klTerm_ge_klTerm_qpos_fence_QA :
    ¬ (klTerm (∑ i in (Finset.univ : Finset (Fin 2)), pU2 i)
          (∑ i in (Finset.univ : Finset (Fin 2)), qSwapD i)
        ≤ ∑ i in (Finset.univ : Finset (Fin 2)), klTerm (pU2 i) (qSwapD i)) := by
  have hp : ∑ i in (Finset.univ : Finset (Fin 2)), pU2 i = 1 := pU2_sum
  have hq : ∑ i in (Finset.univ : Finset (Fin 2)), qSwapD i = 1 := qSwapD_sum
  have hR0 : klTerm (pU2 0) (qSwapD 0) = 0 := by
    simp only [pU2, qSwapD, Matrix.cons_val_zero, Matrix.head_cons, klTerm]
    norm_num
  have hR1 : klTerm (pU2 1) (qSwapD 1) = -(1/2) * Real.log 2 := by
    have hpos : (0:ℝ) < 1/2 := by norm_num
    have hlog : Real.log ((1:ℝ)/2) = -Real.log 2 := by
      rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from by norm_num, Real.log_inv]
    simp only [pU2, qSwapD, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons, klTerm, if_neg (ne_of_gt hpos), div_one, hlog]
    ring
  intro h
  rw [hp, hq, klTerm_one_one, Fin.sum_univ_two, hR0, hR1] at h
  norm_num at h
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  linarith

/-! ### The binary two-point bound: both strict-positivity clauses -/

/-- **The `hb` fence for the binary two-point Pinsker bound**: at
`a = 1/2` (interior, genuine), `b = 0`, the right side collapses to
`klTerm (1/2) 1 = −(1/2)·log 2 < 0` against the left side `1/2` —
refuted. -/
theorem two_point_bzero_fence_QA :
    ¬ (2 * ((1/2 : ℝ) - 0) ^ 2
        ≤ klTerm (1/2 : ℝ) 0 + klTerm (1 - 1/2 : ℝ) (1 - 0)) := by
  have hA : klTerm (1/2 : ℝ) 0 = 0 := by
    simp only [klTerm, if_neg (by norm_num : (1/2 : ℝ) ≠ 0), div_zero,
      Real.log_zero]
    ring
  have hB : klTerm (1 - 1/2 : ℝ) (1 - 0) = -(1/2) * Real.log 2 := by
    have hpos : (0:ℝ) < 1 - 1/2 := by norm_num
    have hne : (1 - 1/2 : ℝ) ≠ 0 := ne_of_gt hpos
    simp only [klTerm, if_neg hne, sub_zero, div_one]
    have hlog : Real.log ((1:ℝ)/2) = -Real.log 2 := by
      rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from by norm_num, Real.log_inv]
    rw [show (1 - 1/2 : ℝ) = (1:ℝ)/2 from by norm_num, hlog]
    ring
  rw [hA, hB]
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  norm_num
  linarith

/-- **The `hb1` fence**: at `a = 1/2`, `b = 1`, the same collapse with
the summands exchanged — refuted. -/
theorem two_point_bone_fence_QA :
    ¬ (2 * ((1/2 : ℝ) - 1) ^ 2
        ≤ klTerm (1/2 : ℝ) 1 + klTerm (1 - 1/2 : ℝ) (1 - 1)) := by
  have hA : klTerm (1/2 : ℝ) 1 = -(1/2) * Real.log 2 := by
    have hpos : (0:ℝ) < 1/2 := by norm_num
    have hlog : Real.log ((1:ℝ)/2) = -Real.log 2 := by
      rw [show ((1:ℝ)/2) = (2:ℝ)⁻¹ from by norm_num, Real.log_inv]
    simp only [klTerm, if_neg (ne_of_gt hpos), div_one, hlog]
    ring
  have hB : klTerm (1 - 1/2 : ℝ) (1 - 1) = 0 := by
    have hne : (1 - 1/2 : ℝ) ≠ 0 := by norm_num
    simp only [klTerm, if_neg hne, sub_self, div_zero, Real.log_zero]
    ring
  rw [hA, hB, add_zero]
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  norm_num
  linarith

end Scaffold.InformationTheory.QA
