/-
  BandDavisKahanDiff_QA.lean

  Purpose
  -------
  QA lemmas for the difference (sin-Theta) form of the band Davis-Kahan
  theorem in `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.
  BandDavisKahan` (`proposals/band-davis-kahan-difference.md`): the
  subspace-distance bound

      ‖P_A(a1,b1] - P_B(a2,b2]‖ ≤ ‖A - B‖ / δ

for equal-rank band projectors under one-sided eigenvalue separation —
the equal-rank gap identity's first consumer, witnessed at every level
the strategy's falsifiability test names.

  Four sections, on the fixtures reused by QA-to-QA import (`diag13`
  from `Band_QA`, the rotated `bdkB = !![1, 3/4; 3/4, 3]` from
  `BandDavisKahan_QA` with its pinned spectrum `{3/4, 13/4}`,
  eigen-direction constraints, and perturbation bound
  `‖diag13 - bdkB‖ ≤ 3/4`):

  1. **The rotated positive witness** — equal windows `(-1, 2]` on
     both matrices, δ = 3/4 (B's out-of-window eigenvalue 13/4 sits
     `b1 + δ = 11/4 ≤ 13/4` away; the low side is vacuous). The rank
     equality is *supplied through the new rank supplier*
     (`rank_bandProjector_eq_card`: count 1 on each side, from the
     pinned spectra). The theorem bounds the distance by 1; the raw
     route pins it from below by `√(1/10)` completely independently:
     `(P - Q) *ᵥ e0 = ![1/10, 3/10]` with `Q *ᵥ e0 = ![9/10, -3/10]`
     resolved through B's eigenbasis (the `(3,-1)` direction, the
     sign-independent coordinate squares 9/10 and 1/10 — no
     `eigvecOf` value assumed). Plus the identity-coherence witness:
     `((1 - Q) * P) *ᵥ e0` pinned equal to `(P - Q) *ᵥ e0` by an
     independent raw route — the equal-rank identity's content
     exhibited numerically.

  2. **The ε = 0 attainment** — A = B = diag13 with identical windows
     `(-1, 2]` at δ = 1/2 (separation genuinely holds: the
     out-of-window eigenvalue 3 satisfies `2 + 1/2 ≤ 3`): the theorem
     reads `‖P - Q‖ ≤ 0`, so the distance is exactly 0 — attained —
     and the difference is independently pinned zero through the
     imported projector pin.

  3. **The margin-corollary instance** — B's window `(-2, 3]`
     (captures 3/4 only) at δ = 1 through
     `l2OpNorm_bandProjector_sub_bandProjector_le_of_mem`: margins
     `-2 + 1 ≤ -1` and `2 + 1 ≤ 3`; bound `≤ 3/4`, raw lower
     `√(1/10)` by the same eigenbasis route at the new window.

  4. **The fence — the rank hypothesis load-bearing, refuted in
     proved form** — A = B = diag13 with A's window `(3/2, 5/2]`
     (captures no eigenvalue: rank 0) against B's window `(5/2, 7/2]`
     (captures 3: rank 1): every *other* hypothesis verified at δ =
     1/2 (`hlo`: eigenvalue 1 satisfies `1 ≤ 5/2 → 1 ≤ 3/2 - 1/2`;
     `hhi` vacuous), the hypothesis-free conclusion
     `‖P - Q‖ = ‖diag(0,1)‖ = 1 ≤ 0` refuted, and the rank
     difference proved through the rank supplier — exactly `hrank`
     isolated.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan
import Scaffold.QA.Perturbation.BandDavisKahan_QA

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open SpectralGraphTheory
open SpectralGraphTheory.QA

/-!
## Fixture helpers: the bottom-mode index of `bdkB`, and window counts
-/

/-- The `3/4` mode has an index. -/
theorem bdkB_exists_bot : ∃ i : Fin 2, eigvalOf bdkB bdkB_symm i = 3 / 4 := by
  rcases bdkB_eigvalOf_mem 0 with h | h
  · exact ⟨0, h⟩
  · refine ⟨1, ?_⟩
    rcases bdkB_eigvalOf_mem 1 with h' | h'
    · exact h'
    · exfalso
      have hsum := bdkB_sum
      rw [h, h'] at hsum
      norm_num at hsum

/-- The `3/4` mode has exactly one index (two would force the product
`9/16` against the pinned `39/16`). -/
theorem bdkB_unique_bot : ∀ i j : Fin 2,
    eigvalOf bdkB bdkB_symm i = 3 / 4 →
    eigvalOf bdkB bdkB_symm j = 3 / 4 → i = j := by
  intro i j hi hj
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    have hp := bdkB_prod
    rw [show eigvalOf bdkB bdkB_symm 0 = 3 / 4 from hi,
        show eigvalOf bdkB bdkB_symm 1 = 3 / 4 from hj] at hp
    norm_num at hp
  · exfalso
    have hp := bdkB_prod
    rw [show eigvalOf bdkB bdkB_symm 0 = 3 / 4 from hj,
        show eigvalOf bdkB bdkB_symm 1 = 3 / 4 from hi] at hp
    norm_num at hp
  · rfl

/-- Any window of `bdkB` containing `3/4` but not `13/4` selects
exactly one mode. -/
theorem bdkB_card_band_of_mem (a b : ℝ) (ha : a < 3 / 4) (hb : 3 / 4 ≤ b)
    (htop : ¬ (a < 13 / 4 ∧ 13 / 4 ≤ b)) :
    (Finset.univ.filter fun i =>
      a < eigvalOf bdkB bdkB_symm i
        ∧ eigvalOf bdkB bdkB_symm i ≤ b).card = 1 := by
  obtain ⟨jb, hjb⟩ := bdkB_exists_bot
  have hfilter : (Finset.univ.filter fun i =>
      a < eigvalOf bdkB bdkB_symm i
        ∧ eigvalOf bdkB bdkB_symm i ≤ b) = {jb} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hwin
      rcases bdkB_eigvalOf_mem i with h | h
      · exact bdkB_unique_bot i jb h hjb
      · rw [h] at hwin
        exact absurd hwin htop
    · intro h
      rw [h, hjb]
      exact ⟨ha, hb⟩
  rw [hfilter, Finset.card_singleton]

/-- The `(-1, 2]` window of `diag13` selects exactly the eigenvalue-1
mode. -/
theorem diag13_card_band_low :
    (Finset.univ.filter fun i =>
      (-1 : ℝ) < eigvalOf diag13 diag13_symm i
        ∧ eigvalOf diag13 diag13_symm i ≤ 2).card = 1 := by
  obtain ⟨i1, hi1⟩ := diag13_exists_one
  have hfilter : (Finset.univ.filter fun i =>
      (-1 : ℝ) < eigvalOf diag13 diag13_symm i
        ∧ eigvalOf diag13 diag13_symm i ≤ 2) = {i1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hwin
      rcases diag13_eigvalOf_mem i with h | h
      · exact diag13_unique_one i i1 h hi1
      · rw [h] at hwin
        norm_num at hwin
    · intro h
      rw [h, hi1]
      norm_num
  rw [hfilter, Finset.card_singleton]

/-!
## The window-parametric filtered action of `bdkB` at `e0`

`Q *ᵥ e0 = ![9/10, -3/10]` for any window selecting the `3/4` mode
alone — the `(3, -1)` eigen-direction with the sign-independent
coordinate squares `9/10` (first) and `1/10` (second).
-/

theorem bdkd_Qe0_of_mem (a b : ℝ) (hab : a ≤ b) (ha : a < 3 / 4)
    (hb : 3 / 4 ≤ b) (htop : ¬ (a < 13 / 4 ∧ 13 / 4 ≤ b)) :
    bandProjector bdkB bdkB_symm a b *ᵥ (![1, 0] : Fin 2 → ℝ)
      = ![9 / 10, -(3 / 10)] := by
  funext k
  rw [(eigvecOf_expansion_apply bdkB_symm
    (bandProjector bdkB bdkB_symm a b *ᵥ (![1, 0] : Fin 2 → ℝ)) k).symm]
  have hcomp : ∀ j : Fin 2,
      Matrix.dotProduct (eigvecOf bdkB bdkB_symm j)
        (bandProjector bdkB bdkB_symm a b *ᵥ (![1, 0] : Fin 2 → ℝ))
      = (if a < eigvalOf bdkB bdkB_symm j
            ∧ eigvalOf bdkB bdkB_symm j ≤ b then (1 : ℝ) else 0)
        * eigvecOf bdkB bdkB_symm j 0 := by
    intro j
    rw [eigvecOf_dotProduct_bandProjector_mulVec bdkB_symm a b hab j
      (![1, 0] : Fin 2 → ℝ)]
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [Fin.sum_univ_two, hcomp 0, hcomp 1]
  rcases bdkB_eigvalOf_mem 0 with h0e | h0e
  · have h1e : eigvalOf bdkB bdkB_symm 1 = 13 / 4 := by
      rcases bdkB_eigvalOf_mem 1 with h | h
      · exfalso
        have hsum := bdkB_sum
        rw [h0e, h] at hsum
        norm_num at hsum
      · exact h
    rw [h0e, h1e]
    have hc0 : a < 3 / 4 ∧ 3 / 4 ≤ b := ⟨ha, hb⟩
    simp only [if_pos hc0, if_neg htop, one_mul, zero_mul, add_zero]
    fin_cases k
    · show eigvecOf bdkB bdkB_symm 0 0 * eigvecOf bdkB bdkB_symm 0 0
          = 9 / 10
      have hd := bdkB_eigvec_bot_dir 0 h0e
      have hs := bdkB_eigvec_bot_sq 0 h0e
      have hsq : (-(3 * eigvecOf bdkB bdkB_symm 0 1))
          * (-(3 * eigvecOf bdkB bdkB_symm 0 1))
          = 9 * (eigvecOf bdkB bdkB_symm 0 1
            * eigvecOf bdkB bdkB_symm 0 1) := by ring
      rw [hd, hsq, hs]
      norm_num
    · show eigvecOf bdkB bdkB_symm 0 0 * eigvecOf bdkB bdkB_symm 0 1
          = -(3 / 10)
      have hd := bdkB_eigvec_bot_dir 0 h0e
      have hs := bdkB_eigvec_bot_sq 0 h0e
      have hsq : (-(3 * eigvecOf bdkB bdkB_symm 0 1))
          * eigvecOf bdkB bdkB_symm 0 1
          = -3 * (eigvecOf bdkB bdkB_symm 0 1
            * eigvecOf bdkB bdkB_symm 0 1) := by ring
      rw [hd, hsq, hs]
      norm_num
  · have h1e : eigvalOf bdkB bdkB_symm 1 = 3 / 4 := by
      rcases bdkB_eigvalOf_mem 1 with h | h
      · exact h
      · exfalso
        have hsum := bdkB_sum
        rw [h0e, h] at hsum
        norm_num at hsum
    rw [h0e, h1e]
    have hc1 : a < 3 / 4 ∧ 3 / 4 ≤ b := ⟨ha, hb⟩
    simp only [if_neg htop, if_pos hc1, one_mul, zero_mul, zero_add]
    fin_cases k
    · show eigvecOf bdkB bdkB_symm 1 0 * eigvecOf bdkB bdkB_symm 1 0
          = 9 / 10
      have hd := bdkB_eigvec_bot_dir 1 h1e
      have hs := bdkB_eigvec_bot_sq 1 h1e
      have hsq : (-(3 * eigvecOf bdkB bdkB_symm 1 1))
          * (-(3 * eigvecOf bdkB bdkB_symm 1 1))
          = 9 * (eigvecOf bdkB bdkB_symm 1 1
            * eigvecOf bdkB bdkB_symm 1 1) := by ring
      rw [hd, hsq, hs]
      norm_num
    · show eigvecOf bdkB bdkB_symm 1 0 * eigvecOf bdkB bdkB_symm 1 1
          = -(3 / 10)
      have hd := bdkB_eigvec_bot_dir 1 h1e
      have hs := bdkB_eigvec_bot_sq 1 h1e
      have hsq : (-(3 * eigvecOf bdkB bdkB_symm 1 1))
          * eigvecOf bdkB bdkB_symm 1 1
          = -3 * (eigvecOf bdkB bdkB_symm 1 1
            * eigvecOf bdkB bdkB_symm 1 1) := by ring
      rw [hd, hsq, hs]
      norm_num

/-- The `diag13` low-band action at `e0` (the imported pin). -/
theorem band_diag13_low_e0 :
    bandProjector diag13 diag13_symm (-1) 2 *ᵥ (![1, 0] : Fin 2 → ℝ)
      = ![1, 0] := by
  rw [band_diag13_low]
  funext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]

/-!
## Section 1: the rotated positive witness (two routes)
-/

/-- The difference action at `e0`: `![1/10, 3/10]`, both parts
computed raw (the `diag13` pin and the eigenbasis route). -/
theorem bdkd_diff_e0_of_mem (a b : ℝ) (hab : a ≤ b) (ha : a < 3 / 4)
    (hb : 3 / 4 ≤ b) (htop : ¬ (a < 13 / 4 ∧ 13 / 4 ≤ b)) :
    (bandProjector diag13 diag13_symm (-1) 2
      - bandProjector bdkB bdkB_symm a b) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = ![1 / 10, 3 / 10] := by
  rw [Matrix.sub_mulVec, band_diag13_low_e0,
    bdkd_Qe0_of_mem a b hab ha hb htop]
  funext i
  fin_cases i
  · show (1 : ℝ) - 9 / 10 = 1 / 10
    norm_num
  · show (0 : ℝ) - -(3 / 10) = 3 / 10
    norm_num

/-- The squared length of the difference action at `e0` is `1/10`
(the raw route's numeric content). -/
theorem bdkd_diff_e0_dot_of_mem (a b : ℝ) (hab : a ≤ b) (ha : a < 3 / 4)
    (hb : 3 / 4 ≤ b) (htop : ¬ (a < 13 / 4 ∧ 13 / 4 ≤ b)) :
    Matrix.dotProduct
      ((bandProjector diag13 diag13_symm (-1) 2
        - bandProjector bdkB bdkB_symm a b) *ᵥ (![1, 0] : Fin 2 → ℝ))
      ((bandProjector diag13 diag13_symm (-1) 2
        - bandProjector bdkB bdkB_symm a b) *ᵥ (![1, 0] : Fin 2 → ℝ))
      = 1 / 10 := by
  rw [bdkd_diff_e0_of_mem a b hab ha hb htop]
  norm_num [Matrix.dotProduct, Fin.sum_univ_two, Pi.sub_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- The rank equality for the equal-window fixture, supplied through
the new rank supplier (count 1 each side). -/
theorem bdkd_rank_eq :
    (bandProjector diag13 diag13_symm (-1) 2).rank
      = (bandProjector bdkB bdkB_symm (-1) 2).rank := by
  rw [rank_bandProjector_eq_card diag13_symm (-1) 2 (by norm_num),
    rank_bandProjector_eq_card bdkB_symm (-1) 2 (by norm_num),
    diag13_card_band_low,
    bdkB_card_band_of_mem (-1) 2 (by norm_num) (by norm_num)
      (by norm_num)]

/-- **The two-route positive witness.** The raw eigenbasis route
bounds the distance from below by `√(1/10)`, the theorem (at δ = 3/4,
with the perturbation bounded by `3/4`) bounds it from above by `1`,
and `1/10 < 1` — the two routes leave a proved nonempty gap, so a
misstatement on either side breaks the conjunction. -/
theorem bdkd_rotated_QA :
    Real.sqrt (1 / 10)
      ≤ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2‖
      ∧ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2‖
        ≤ 1 := by
  refine ⟨?_, ?_⟩
  · have hact := l2OpNorm_mulVec_le
      (bandProjector diag13 diag13_symm (-1) 2
        - bandProjector bdkB bdkB_symm (-1) 2) (![1, 0] : Fin 2 → ℝ)
    rw [norm_euclidean_eq_sqrt,
      bdkd_diff_e0_dot_of_mem (-1) 2 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num),
      norm_euclidean_eq_sqrt] at hact
    have he0 : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [he0, Real.sqrt_one, mul_one] at hact
    exact hact
  · have hthm := l2OpNorm_bandProjector_sub_bandProjector_le
      diag13_symm bdkB_symm (-1) 2 (-1) 2 (by norm_num) (by norm_num)
      (δ := (3 / 4 : ℝ)) (by norm_num) bdkd_rank_eq ?_ ?_
    · calc ‖bandProjector diag13 diag13_symm (-1) 2
            - bandProjector bdkB bdkB_symm (-1) 2‖
          ≤ ‖diag13 - bdkB‖ / (3 / 4 : ℝ) := hthm
        _ ≤ (3 / 4 : ℝ) / (3 / 4 : ℝ) :=
            div_le_div₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) bdkE_norm_le
              (by norm_num : (0 : ℝ) < 3 / 4) (le_refl _)
        _ = 1 := by field_simp
    · intro j hj
      rcases bdkB_eigvalOf_mem j with h | h <;> rw [h] at hj <;>
        norm_num at hj
    · intro j hj
      rcases bdkB_eigvalOf_mem j with h | h
      · rw [h] at hj
        norm_num at hj
      · rw [h]
        norm_num

/-- **The identity-coherence witness.** The equal-rank identity says
`‖P - Q‖ = ‖(1 - Q) * P‖`; at the fixture the two *actions* at `e0`
are pinned equal by an independent raw route (each side computed
separately: `P *ᵥ e0 = e0`, then `Q *ᵥ e0 = ![9/10, -3/10]`). -/
theorem bdkd_coherence :
    ((1 - bandProjector bdkB bdkB_symm (-1) 2)
        * bandProjector diag13 diag13_symm (-1) 2)
        *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2) *ᵥ (![1, 0] : Fin 2 → ℝ) := by
  rw [← Matrix.mulVec_mulVec, band_diag13_low_e0, Matrix.sub_mulVec,
    Matrix.one_mulVec,
    bdkd_Qe0_of_mem (-1) 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num),
    bdkd_diff_e0_of_mem (-1) 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
  funext i
  fin_cases i
  · show (1 : ℝ) - 9 / 10 = 1 / 10
    norm_num
  · show (0 : ℝ) - -(3 / 10) = 3 / 10
    norm_num

/-!
## Section 2: the ε = 0 attainment (A = B, identical windows)
-/

/-- At zero perturbation with identical windows the bound is
*attained*: the theorem reads `‖P - Q‖ ≤ 0` (the separation holds at
δ = 1/2 — the out-of-window eigenvalue 3 satisfies `5/2 ≤ 3`), so the
distance is exactly 0. -/
theorem bdkd_zeroE_attained :
    ‖bandProjector diag13 diag13_symm (-1) 2
      - bandProjector diag13 diag13_symm (-1) 2‖ = 0 := by
  have hthm := l2OpNorm_bandProjector_sub_bandProjector_le
    diag13_symm diag13_symm (-1) 2 (-1) 2 (by norm_num) (by norm_num)
    (δ := (1 / 2 : ℝ)) (by norm_num) rfl ?_ ?_
  · have h0 : diag13 - diag13 = 0 := by
      ext i j; simp
    rw [h0, norm_zero, zero_div] at hthm
    exact le_antisymm hthm (norm_nonneg _)
  · intro j hj
    rcases diag13_eigvalOf_mem j with h | h <;> rw [h] at hj <;>
      norm_num at hj
  · intro j hj
    rcases diag13_eigvalOf_mem j with h | h
    · rw [h] at hj
      norm_num at hj
    · rw [h] at hj ⊢
      norm_num at hj ⊢

/-- The independent raw route: both projectors are the pinned
`diag(1,0)`, so the difference is the zero matrix. -/
theorem bdkd_zeroE_raw :
    bandProjector diag13 diag13_symm (-1) 2
      - bandProjector diag13 diag13_symm (-1) 2 = 0 := by
  rw [band_diag13_low, sub_self]

/-!
## Section 3: the margin-corollary instance
-/

/-- The margin corollary at B's window `(-2, 3]` (captures the `3/4`
mode alone), δ = 1: bound `≤ 3/4`, raw lower `√(1/10)` by the same
eigenbasis route at the new window. -/
theorem bdkd_margin_QA :
    Real.sqrt (1 / 10)
      ≤ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-2) 3‖
      ∧ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-2) 3‖
        ≤ 3 / 4 := by
  have hrank : (bandProjector diag13 diag13_symm (-1) 2).rank
      = (bandProjector bdkB bdkB_symm (-2) 3).rank := by
    rw [rank_bandProjector_eq_card diag13_symm (-1) 2 (by norm_num),
      rank_bandProjector_eq_card bdkB_symm (-2) 3 (by norm_num),
      diag13_card_band_low,
      bdkB_card_band_of_mem (-2) 3 (by norm_num) (by norm_num)
        (by norm_num)]
  refine ⟨?_, ?_⟩
  · have hact := l2OpNorm_mulVec_le
      (bandProjector diag13 diag13_symm (-1) 2
        - bandProjector bdkB bdkB_symm (-2) 3) (![1, 0] : Fin 2 → ℝ)
    rw [norm_euclidean_eq_sqrt,
      bdkd_diff_e0_dot_of_mem (-2) 3 (by norm_num) (by norm_num)
        (by norm_num) (by norm_num),
      norm_euclidean_eq_sqrt] at hact
    have he0 : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [he0, Real.sqrt_one, mul_one] at hact
    exact hact
  · have hthm := l2OpNorm_bandProjector_sub_bandProjector_le_of_mem
      diag13_symm bdkB_symm (-1) 2 (-2) 3 (by norm_num) (by norm_num)
      (δ := (1 : ℝ)) (by norm_num) hrank (by norm_num) (by norm_num)
    rw [div_one] at hthm
    exact le_trans hthm bdkE_norm_le

/-!
## Section 4: the fence — the rank hypothesis load-bearing
-/

/-- A's fence window `(3/2, 5/2]` captures no eigenvalue of
`diag13` (both 1 and 3 fail the window conditions). -/
theorem bdkd_fence_lowcard :
    (Finset.univ.filter fun i =>
      (3 / 2 : ℝ) < eigvalOf diag13 diag13_symm i
        ∧ eigvalOf diag13 diag13_symm i ≤ 5 / 2).card = 0 := by
  have hfilter : (Finset.univ.filter fun i =>
      (3 / 2 : ℝ) < eigvalOf diag13 diag13_symm i
        ∧ eigvalOf diag13 diag13_symm i ≤ 5 / 2) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.not_mem_empty, not_false_iff]
    rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num
  rw [hfilter, Finset.card_empty]

/-- B's fence window `(5/2, 7/2]` captures exactly the eigenvalue-3
mode. -/
theorem bdkd_fence_highcard :
    (Finset.univ.filter fun i =>
      (5 / 2 : ℝ) < eigvalOf diag13 diag13_symm i
        ∧ eigvalOf diag13 diag13_symm i ≤ 7 / 2).card = 1 := by
  obtain ⟨j3, hj3⟩ := diag13_exists_three
  have hunique : ∀ i : Fin 2, eigvalOf diag13 diag13_symm i = 3 → i = j3 := by
    intro i hi
    by_contra hne
    have hsum := diag13_sum
    fin_cases i <;> fin_cases j3
    · exact absurd rfl hne
    · have ha : eigvalOf diag13 diag13_symm 0 = 3 := hi
      have hb : eigvalOf diag13 diag13_symm 1 = 3 := hj3
      rw [ha, hb] at hsum
      norm_num at hsum
    · have ha : eigvalOf diag13 diag13_symm 1 = 3 := hi
      have hb : eigvalOf diag13 diag13_symm 0 = 3 := hj3
      rw [ha, hb] at hsum
      norm_num at hsum
    · exact absurd rfl hne
  have hfilter : (Finset.univ.filter fun i =>
      (5 / 2 : ℝ) < eigvalOf diag13 diag13_symm i
        ∧ eigvalOf diag13 diag13_symm i ≤ 7 / 2) = {j3} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hwin
      rcases diag13_eigvalOf_mem i with h | h
      · rw [h] at hwin
        norm_num at hwin
      · rw [h] at hwin
        norm_num at hwin
        exact hunique i h
    · intro h
      rw [h, hj3]
      norm_num
  rw [hfilter, Finset.card_singleton]

/-- The fence's A-projector is zero (empty window: both threshold
projectors are the pinned `diag(1,0)`). -/
theorem bdkd_fence_P :
    bandProjector diag13 diag13_symm (3 / 2) (5 / 2) = 0 := by
  rw [bandProjector,
    spectralProjector_diag13_eq (5 / 2) (by norm_num) (by norm_num),
    spectralProjector_diag13_eq (3 / 2) (by norm_num) (by norm_num),
    sub_self]

/-- The fence's B-projector is the second-axis projector. -/
theorem bdkd_fence_Q :
    bandProjector diag13 diag13_symm (5 / 2) (7 / 2)
      = (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [bandProjector,
    spectralProjector_eq_one diag13 diag13_symm (7 / 2)
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    spectralProjector_diag13_eq (5 / 2) (by norm_num) (by norm_num)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]

/-- The fence's rank difference, through the rank supplier: 0 vs 1. -/
theorem bdkd_fence_ranks :
    (bandProjector diag13 diag13_symm (3 / 2) (5 / 2)).rank = 0
      ∧ (bandProjector diag13 diag13_symm (5 / 2) (7 / 2)).rank = 1 := by
  refine ⟨?_, ?_⟩
  · rw [rank_bandProjector_eq_card diag13_symm (3 / 2) (5 / 2)
      (by norm_num), bdkd_fence_lowcard]
  · rw [rank_bandProjector_eq_card diag13_symm (5 / 2) (7 / 2)
      (by norm_num), bdkd_fence_highcard]

/-- **The fence refuted in proved form.** With every hypothesis of the
difference theorem verified *except* the rank equality (windows
`(3/2, 5/2]` empty for A, `(5/2, 7/2]` occupied for B, at A = B and
δ = 1/2), the hypothesis-free conclusion reads `‖0 - diag(0,1)‖ ≤ 0` —
false, since the norm is at least `1` through the action bound at
`e1`. Exactly `hrank` is the violated hypothesis. -/
theorem bdkd_rank_fence :
    ¬ (‖bandProjector diag13 diag13_symm (3 / 2) (5 / 2)
          - bandProjector diag13 diag13_symm (5 / 2) (7 / 2)‖
        ≤ ‖diag13 - diag13‖ / (1 / 2 : ℝ)) := by
  intro hcon
  have h0 : diag13 - diag13 = 0 := by
    ext i j; simp
  rw [h0, norm_zero, zero_div] at hcon
  have hM : bandProjector diag13 diag13_symm (3 / 2) (5 / 2)
      - bandProjector diag13 diag13_symm (5 / 2) (7 / 2)
      = -(!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [bdkd_fence_P, bdkd_fence_Q, zero_sub]
  rw [hM] at hcon
  have hact := l2OpNorm_mulVec_le
    (-(!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ))
    (![0, 1] : Fin 2 → ℝ)
  have hz : (-(!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ
      (![0, 1] : Fin 2 → ℝ) = ![0, -1] := by
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  rw [hz, norm_euclidean_eq_sqrt] at hact
  rw [norm_euclidean_eq_sqrt] at hact
  have he1 : (![0, 1] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  have he1' : (![0, -1] : Fin 2 → ℝ) ⬝ᵥ ![0, -1] = 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [he1', he1, Real.sqrt_one, mul_one] at hact
  linarith

/-- Every `hrank`-shaped hypothesis of the theorem's other
assumptions holds at the fence — the rank equality is the *only*
failing one. -/
theorem bdkd_fence_only_rank_fails :
    ¬ ((bandProjector diag13 diag13_symm (3 / 2) (5 / 2)).rank
        = (bandProjector diag13 diag13_symm (5 / 2) (7 / 2)).rank)
      ∧ (∀ j, eigvalOf diag13 diag13_symm j ≤ (5 / 2 : ℝ) →
          eigvalOf diag13 diag13_symm j ≤ 3 / 2 - 1 / 2)
      ∧ (∀ j, (7 / 2 : ℝ) < eigvalOf diag13 diag13_symm j →
          5 / 2 + 1 / 2 ≤ eigvalOf diag13 diag13_symm j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    obtain ⟨h1, h2⟩ := bdkd_fence_ranks
    rw [heq] at h1
    omega
  · intro j hj
    rcases diag13_eigvalOf_mem j with h | h
    · rw [h] at hj ⊢
      norm_num at hj ⊢
    · rw [h] at hj
      norm_num at hj
  · intro j hj
    rcases diag13_eigvalOf_mem j with h | h <;> rw [h] at hj <;>
      norm_num at hj

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
