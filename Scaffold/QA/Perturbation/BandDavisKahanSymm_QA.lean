/-
  BandDavisKahanSymm_QA.lean

  Purpose
  -------
  QA lemmas for the two-sided (symmetric-separation) constant-2 form
  of the band Davis–Kahan difference theorem in
  `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
  (`proposals/band-davis-kahan-symmetric.md`):

      ‖P_A(a1,b1] - P_B(a2,b2]‖ ≤ 2 * ‖A - B‖ / δ

  under separation on *both* out-of-window flanks (B's out-of-window
  spectrum δ-away from A's in-window spectrum, and A's out-of-window
  spectrum δ-away from B's in-window spectrum), with **no rank
  hypothesis** — unequal ranks force `δ ≤ ‖A - B‖`, the trivial
  regime; on equal-rank inputs the delivered pairwise theorem gives
  the strictly better constant 1.

  Four sections:

  1. **The rank-free unequal-rank witness — the selling point** —
     `A = clusterA = diag(0, 5, 11)` window `(-1, 6]` (cluster
     `{0, 5}`, rank 2) against `B = clusterB = diag(1, 2, 4)` window
     `(3/2, 3]` (cluster `{2}`, rank 1) at δ = 1/2: both separations
     discharged on the pinned spectra, the ranks pinned **2 ≠ 1**
     through the delivered supplier — the delivered difference
     family's rank hypothesis exhibited failing on the very fixture
     the new theorem covers — the norm lower-bounded by `1` raw at
     `e0` (B's 1-mode is out-of-window, so the band action on `e0`
     vanishes by the component action + the eigen-equation support
     pin), and the theorem bound evaluated `≤ 2 * 7/(1/2) = 28`.
     Plus the **constant comparison** on the equal-rank rotated
     fixture (`diag13` vs `bdkB`, equal windows `(-1, 2]`,
     δ = 3/4): delivered bound `≤ 1` vs new bound `≤ 2` against the
     imported raw lower `√(1/10)` — the constant-2 cost visible.

  2. **The ε = 0 attainment** — A = B = diag13, genuinely distinct
     windows `(-1, 2]` vs `(-1/2, 5/2]` selecting the same cluster at
     δ = 1/2: the theorem reads `‖P - Q‖ ≤ 2 * 0 / δ = 0`, attained
     (cross-checked by the imported raw zero pin).

  3. **The fence — `hsepAB` load-bearing, refuted in proved form** —
     A = B = diag13, windows `(-1, 2]` vs `(-1, 4]`: B's window
     selects everything, so `hsepBA` is *vacuous* and provably
     holds; A's out-of-window 3-mode sits at distance 0 from B's
     in-window 3-mode, so `hsepAB` fails; the hypothesis-free
     conclusion `‖P - Q‖ ≤ 2 * 0 / δ = 0` is refuted with
     `‖P - Q‖ ≥ 1` at `e1` (`Q = 1` through `bandProjector_eq_one`).
     The mirror of the cluster QA's `hsep` fence: between the two QA
     files, both separation sides of the difference family are
     isolated.

  4. **The decomposition-coherence witness** (the `bdkd_coherence`
     precedent) — the consumed ring identity
     `P - Q = (I - Q) * P - Q * (I - P)` exhibited at the action
     level on the rotated fixture at `e0`: the difference action
     `![1/10, 3/10]` pinned by the imported raw route, and the two
     composite parts computed independently (`(I - Q) P *ᵥ e0 =
     ![1/10, 3/10]`, `Q (I - P) *ᵥ e0 = 0`).

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan
import Scaffold.QA.Perturbation.BandDavisKahanCluster_QA

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open SpectralGraphTheory
open SpectralGraphTheory.QA

/-!
## Section 1 support: the clusterB eigen-equation support pin

The eigen-equation of a diagonal matrix at the 2-mode forces the
eigenvector's off-2 coordinates to vanish (the cluster QA's private
technique, re-derived here at the one index needed — that layer is
private to its file).
-/

section SupportPins

/-- The eigen-equation of `clusterB = diag(1, 2, 4)` at coordinate
`l`: `d l * v l = λ * v l`. -/
private theorem bdks_eig_eq (j l : Fin 3) :
    (![1, 2, 4] : Fin 3 → ℝ) l * eigvecOf clusterB clusterB_symm j l
      = eigvalOf clusterB clusterB_symm j
        * eigvecOf clusterB clusterB_symm j l := by
  have h0 : clusterB *ᵥ eigvecOf clusterB clusterB_symm j
      = eigvalOf clusterB clusterB_symm j
        • eigvecOf clusterB clusterB_symm j :=
    (isHermitian_of_isSymm clusterB_symm).mulVec_eigenvectorBasis j
  have := congrFun h0 l
  simpa [clusterB, Matrix.mulVec, Matrix.dotProduct,
    Matrix.diagonal_apply] using this

/-- An eigenvector of `clusterB` at the eigenvalue 2 vanishes off
the middle coordinate. -/
theorem bdks_eigvec_two_off (j : Fin 3)
    (hj : eigvalOf clusterB clusterB_symm j = 2) :
    eigvecOf clusterB clusterB_symm j 0 = 0
      ∧ eigvecOf clusterB clusterB_symm j 2 = 0 := by
  constructor
  · have h := bdks_eig_eq j 0
    rw [Matrix.cons_val_zero, hj] at h
    have he : (1 : ℝ) * eigvecOf clusterB clusterB_symm j 0
        - 2 * eigvecOf clusterB clusterB_symm j 0 = 0 := by linarith
    linarith
  · have h := bdks_eig_eq j 2
    have he : (![1, 2, 4] : Fin 3 → ℝ) 2 = 4 := by
      simp [Matrix.cons_val_succ, Matrix.cons_val_zero]
    rw [he, hj] at h
    have hz : (4 : ℝ) * eigvecOf clusterB clusterB_symm j 2
        - 2 * eigvecOf clusterB clusterB_symm j 2 = 0 := by linarith
    linarith

/-- The B-window `(3/2, 3]` selects exactly the 2-mode: the card
pin. -/
theorem bdks_cardB_mid :
    (Finset.univ.filter fun j =>
      (3 / 2 : ℝ) < eigvalOf clusterB clusterB_symm j
        ∧ eigvalOf clusterB clusterB_symm j ≤ 3).card = 1 := by
  obtain ⟨j₂, hj₂⟩ := clusterB_exists_two
  have hset : (Finset.univ.filter fun j =>
      (3 / 2 : ℝ) < eigvalOf clusterB clusterB_symm j
        ∧ eigvalOf clusterB clusterB_symm j ≤ 3) = {j₂} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases clusterB_mem j with h' | h' | h'
      · rw [h'] at h; norm_num at h
      · exact clusterB_inj j j₂ (h'.trans hj₂.symm)
      · rw [h'] at h; norm_num at h
    · intro h
      rw [h, hj₂]
      norm_num
  rw [hset, Finset.card_singleton]

/-- The rank pins: 2 on A's window, 1 on B's — through the delivered
supplier. -/
theorem bdks_rankA_eq_two :
    (bandProjector clusterA clusterA_symm (-1) 6).rank = 2 := by
  rw [rank_bandProjector_eq_card clusterA_symm (-1) 6 (by norm_num),
    clusterA_card_band]

theorem bdks_rankB_eq_one :
    (bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3).rank = 1 := by
  rw [rank_bandProjector_eq_card clusterB_symm (3 / 2 : ℝ) 3
    (by norm_num), bdks_cardB_mid]

/-- The band action of B's `(3/2, 3]` window on `e0` vanishes: the
only eigenbasis vector pairing with `e0` is the 1-mode (support pin),
and it is out-of-window. -/
theorem bdks_Qe0_zero :
    bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3
      *ᵥ (![1, 0, 0] : Fin 3 → ℝ) = 0 := by
  have hpair : ∀ j : Fin 3,
      Matrix.dotProduct (eigvecOf clusterB clusterB_symm j)
        (bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3
          *ᵥ (![1, 0, 0] : Fin 3 → ℝ)) = 0 := by
    intro j
    rw [eigvecOf_dotProduct_bandProjector_mulVec clusterB_symm
      (3 / 2 : ℝ) 3 (by norm_num) j (![1, 0, 0] : Fin 3 → ℝ)]
    by_cases hmem : (3 / 2 : ℝ) < eigvalOf clusterB clusterB_symm j
        ∧ eigvalOf clusterB clusterB_symm j ≤ 3
    · have h2 : eigvalOf clusterB clusterB_symm j = 2 := by
        rcases clusterB_mem j with h | h | h
        · rw [h] at hmem; norm_num at hmem
        · exact h
        · rw [h] at hmem; norm_num at hmem
      have hoff := (bdks_eigvec_two_off j h2).1
      have hp : Matrix.dotProduct (eigvecOf clusterB clusterB_symm j)
          (![1, 0, 0] : Fin 3 → ℝ)
          = eigvecOf clusterB clusterB_symm j 0 := by
        simp [Matrix.dotProduct, Fin.sum_univ_three]
      rw [if_pos hmem, hp, hoff]; norm_num
    · rw [if_neg hmem]; norm_num
  funext k
  rw [(eigvecOf_expansion_apply clusterB_symm
    (bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3
      *ᵥ (![1, 0, 0] : Fin 3 → ℝ)) k).symm]
  exact Finset.sum_eq_zero fun j _ => by rw [hpair j, zero_mul]

end SupportPins

/-!
## Section 1: the rank-free unequal-rank witness
-/

/-- **The unequal-rank witness.** On the cluster fixtures with
windows selecting 2 and 1 eigenvalues respectively, the ranks are
provably different (the delivered difference family's hypothesis
fails), the raw norm is at least `1`, and the new theorem's bound
holds at `2 * 7 / (1/2) = 28` — rank-free coverage the delivered
family cannot reach. -/
theorem bdks_unequal_rank_QA :
    (bandProjector clusterA clusterA_symm (-1) 6).rank
      ≠ (bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3).rank
    ∧ 1 ≤ ‖bandProjector clusterA clusterA_symm (-1) 6
        - bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3‖
    ∧ ‖bandProjector clusterA clusterA_symm (-1) 6
        - bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3‖
      ≤ 2 * 7 / (1 / 2 : ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [bdks_rankA_eq_two, bdks_rankB_eq_one]
    norm_num
  · -- the raw lower bound: (P - Q) *ᵥ e0 = e0
    have hP : bandProjector clusterA clusterA_symm (-1) 6
        *ᵥ (![1, 0, 0] : Fin 3 → ℝ) = ![1, 0, 0] := by
      rw [bandClusterA_eq]
      funext k
      fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct,
        Matrix.diagonal_apply, Fin.sum_univ_three]
    have hact := l2OpNorm_mulVec_le
      (bandProjector clusterA clusterA_symm (-1) 6
        - bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3)
      (![1, 0, 0] : Fin 3 → ℝ)
    rw [Matrix.sub_mulVec, hP, bdks_Qe0_zero, sub_zero,
      norm_euclidean_eq_sqrt] at hact
    have he0 : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ (![1, 0, 0] : Fin 3 → ℝ)
        = 1 := by
      simp [Matrix.dotProduct, Fin.sum_univ_three]
    rw [he0, Real.sqrt_one] at hact
    simpa using hact
  · -- the theorem's upper bound at δ = 1/2
    have hthm := l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm
      clusterA_symm clusterB_symm (-1) 6 (3 / 2 : ℝ) 3
      (by norm_num) (by norm_num) (δ := (1 / 2 : ℝ)) (by norm_num)
      ?_ ?_
    · calc ‖bandProjector clusterA clusterA_symm (-1) 6
            - bandProjector clusterB clusterB_symm (3 / 2 : ℝ) 3‖
          ≤ 2 * ‖clusterA - clusterB‖ / (1 / 2 : ℝ) := hthm
        _ ≤ 2 * 7 / (1 / 2 : ℝ) :=
            (div_le_div_iff_of_pos_right
              (by norm_num : (0 : ℝ) < 1 / 2)).2
              (mul_le_mul_of_nonneg_left clusterDiff_norm_le
                (by norm_num : (0 : ℝ) ≤ 2))
    · -- hsepAB: A's out-of-window {11} vs B's in-window {2}
      intro i hiout j jin
      have hi : eigvalOf clusterA clusterA_symm i = 11 := by
        rcases clusterA_mem i with h | h | h
        · exact absurd (And.intro (by rw [h]; norm_num)
            (by rw [h]; norm_num)) hiout
        · exact absurd (And.intro (by rw [h]; norm_num)
            (by rw [h]; norm_num)) hiout
        · exact h
      have hj : eigvalOf clusterB clusterB_symm j = 2 := by
        rcases clusterB_mem j with h | h | h
        · linarith [h, jin.1]
        · exact h
        · linarith [h, jin.2]
      rw [hi, hj]
      norm_num
    · -- hsepBA: B's out-of-window {1, 4} vs A's in-window {0, 5}
      intro j hjout i hiin1 hiin2
      have hA : eigvalOf clusterA clusterA_symm i = 0
          ∨ eigvalOf clusterA clusterA_symm i = 5 := by
        rcases clusterA_mem i with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · linarith [h, hiin2]
      have hB : eigvalOf clusterB clusterB_symm j = 1
          ∨ eigvalOf clusterB clusterB_symm j = 4 := by
        rcases clusterB_mem j with h | h | h
        · exact Or.inl h
        · exact absurd (And.intro (by rw [h]; norm_num)
            (by rw [h]; norm_num)) hjout
        · exact Or.inr h
      rcases hA with ha | ha <;> rcases hB with hb | hb <;>
        rw [hb, ha] <;> norm_num

/-- **The constant comparison.** On the equal-rank rotated fixture
the delivered pairwise theorem (constant 1) and the new symmetric
theorem (constant 2) both apply; their bounds `≤ 1` and `≤ 2` are
pinned against the imported raw lower `√(1/10)` — the constant-2
cost visible numerically. -/
theorem bdks_rotated_two_QA :
    Real.sqrt (1 / 10)
      ≤ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2‖
    ∧ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2‖ ≤ 1
    ∧ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2‖ ≤ 2 := by
  refine ⟨bdkd_rotated_QA.1, bdkd_rotated_QA.2, ?_⟩
  have hthm := l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm
    diag13_symm bdkB_symm (-1) 2 (-1) 2 (by norm_num) (by norm_num)
    (δ := (3 / 4 : ℝ)) (by norm_num) ?_ ?_
  · calc ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2‖
        ≤ 2 * ‖diag13 - bdkB‖ / (3 / 4 : ℝ) := hthm
      _ ≤ 2 * (3 / 4 : ℝ) / (3 / 4 : ℝ) :=
          (div_le_div_iff_of_pos_right
            (by norm_num : (0 : ℝ) < 3 / 4)).2
            (mul_le_mul_of_nonneg_left bdkE_norm_le
              (by norm_num : (0 : ℝ) ≤ 2))
      _ = 2 := by field_simp
  · -- hsepAB: A's out-of-window {3} vs B's in-window {3/4}
    intro i hiout j jin
    have hi : eigvalOf diag13 diag13_symm i = 3 := by
      rcases diag13_eigvalOf_mem i with h | h
      · exact absurd (And.intro (by rw [h]; norm_num)
          (by rw [h]; norm_num)) hiout
      · exact h
    have hj : eigvalOf bdkB bdkB_symm j = 3 / 4 := by
      rcases bdkB_eigvalOf_mem j with h | h
      · exact h
      · linarith [h, jin.2]
    rw [hi, hj]
    rw [abs_of_nonneg (by norm_num)]
    norm_num
  · -- hsepBA: B's out-of-window {13/4} vs A's in-window {1}
    intro j hjout i iin1 iin2
    have hj : eigvalOf bdkB bdkB_symm j = 13 / 4 := by
      rcases bdkB_eigvalOf_mem j with h | h
      · exact absurd (And.intro (by rw [h]; norm_num)
          (by rw [h]; norm_num)) hjout
      · exact h
    have hi : eigvalOf diag13 diag13_symm i = 1 := by
      rcases diag13_eigvalOf_mem i with h | h
      · exact h
      · linarith [h, iin2]
    rw [hj, hi]
    rw [abs_of_nonneg (by norm_num)]
    norm_num

/-!
## Section 2: the ε = 0 attainment at genuinely distinct windows
-/

/-- **The ε = 0 attainment.** Through the theorem at genuinely
distinct windows selecting the same cluster (both separations at
distance 2 ≥ δ = 1/2): `‖P - Q‖ ≤ 2 * ‖A - A‖ / δ = 0`, attained —
cross-checked by the imported raw zero pin. -/
theorem bdks_zeroE_attained :
    ‖bandProjector diag13 diag13_symm (-1) 2
        - bandProjector diag13 diag13_symm (-1 / 2) (5 / 2)‖
      ≤ 2 * ‖diag13 - diag13‖ / (1 / 2 : ℝ)
    ∧ ‖bandProjector diag13 diag13_symm (-1) 2
        - bandProjector diag13 diag13_symm (-1 / 2) (5 / 2)‖ = 0 := by
  refine ⟨?_, bdkc_zeroE_raw⟩
  have hthm := l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm
    diag13_symm diag13_symm (-1) 2 (-1 / 2) (5 / 2) (by norm_num)
    (by norm_num) (δ := (1 / 2 : ℝ)) (by norm_num) ?_ ?_
  · rw [sub_self, norm_zero, mul_zero, zero_div] at hthm ⊢
    exact hthm
  · -- hsepAB: A's out-of-window {3} vs B's in-window {1}
    intro i hiout j jin
    have hi : eigvalOf diag13 diag13_symm i = 3 := by
      rcases diag13_eigvalOf_mem i with h | h
      · exact absurd (And.intro (by rw [h]; norm_num)
          (by rw [h]; norm_num)) hiout
      · exact h
    have hj : eigvalOf diag13 diag13_symm j = 1 := by
      rcases diag13_eigvalOf_mem j with h | h
      · exact h
      · linarith [h, jin.2]
    rw [hi, hj]
    norm_num
  · -- hsepBA: B's out-of-window {3} vs A's in-window {1}
    intro j hjout i iin1 iin2
    have hj : eigvalOf diag13 diag13_symm j = 3 := by
      rcases diag13_eigvalOf_mem j with h | h
      · exact absurd (And.intro (by rw [h]; norm_num)
          (by rw [h]; norm_num)) hjout
      · exact h
    have hi : eigvalOf diag13 diag13_symm i = 1 := by
      rcases diag13_eigvalOf_mem i with h | h
      · exact h
      · linarith [h, iin2]
    rw [hj, hi]
    norm_num

/-!
## Section 3: the fence — `hsepAB` isolated, the mirror of the
cluster QA's `hsep` fence
-/

/-- B's window `(-1, 4]` selects every eigenvalue of `diag13`, so the
band projector is the identity. -/
theorem bdks_fence_Qeq :
    bandProjector diag13 diag13_symm (-1) (4 : ℝ) = 1 :=
  bandProjector_eq_one diag13 diag13_symm (-1) 4
    (fun i => by
      rcases diag13_eigvalOf_mem i with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num)
    (fun i => by
      rcases diag13_eigvalOf_mem i with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num)

/-- The raw norm lower bound: `(P - 1) *ᵥ e1 = -e1`, so
`‖P - Q‖ ≥ 1`. -/
theorem bdks_fence_lower :
    1 ≤ ‖bandProjector diag13 diag13_symm (-1) 2
        - (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
  have hP : bandProjector diag13 diag13_symm (-1) 2
      *ᵥ (![0, 1] : Fin 2 → ℝ) = ![0, 0] := by
    rw [band_diag13_low]
    funext k
    fin_cases k <;> simp [Matrix.mulVec, Matrix.dotProduct,
      Matrix.diagonal_apply, Fin.sum_univ_two]
  have hz : (![0, 0] : Fin 2 → ℝ) - ![0, 1] = -![0, 1] := by
    funext k
    fin_cases k <;> simp
  have hdot : Matrix.dotProduct (-![0, 1] : Fin 2 → ℝ)
      (-![0, 1] : Fin 2 → ℝ) = 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  have he1 : Matrix.dotProduct (![0, 1] : Fin 2 → ℝ)
      (![0, 1] : Fin 2 → ℝ) = 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  have hact := l2OpNorm_mulVec_le
    (bandProjector diag13 diag13_symm (-1) 2
      - (1 : Matrix (Fin 2) (Fin 2) ℝ)) (![0, 1] : Fin 2 → ℝ)
  rw [Matrix.sub_mulVec, hP, Matrix.one_mulVec, hz,
    norm_euclidean_eq_sqrt, norm_euclidean_eq_sqrt] at hact
  rw [hdot, he1, Real.sqrt_one] at hact
  simpa using hact

/-- The hypothesis-free conclusion refuted in proved form: with
A = B (so the RHS is `0`) and `Q = 1`, the norm is at least `1`. -/
theorem bdks_sep_fence :
    ¬ (‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector diag13 diag13_symm (-1) (4 : ℝ)‖
      ≤ 2 * ‖diag13 - diag13‖ / (1 / 2 : ℝ)) := by
  intro h
  rw [bdks_fence_Qeq, sub_self, norm_zero, mul_zero, zero_div] at h
  exact absurd (le_trans bdks_fence_lower h) (by norm_num)

/-- `hsepBA` holds on the fence fixture — vacuously (B's window
selects everything). -/
theorem bdks_fence_sepBA_holds :
    ∀ j, ¬((-1 : ℝ) < eigvalOf diag13 diag13_symm j
        ∧ eigvalOf diag13 diag13_symm j ≤ 4) →
    ∀ i, (-1 : ℝ) < eigvalOf diag13 diag13_symm i
      ∧ eigvalOf diag13 diag13_symm i ≤ 2 →
    (1 / 2 : ℝ) ≤ |eigvalOf diag13 diag13_symm j
      - eigvalOf diag13 diag13_symm i| := by
  intro j hj i hi
  have hmem : (-1 : ℝ) < eigvalOf diag13 diag13_symm j
      ∧ eigvalOf diag13 diag13_symm j ≤ 4 := by
    rcases diag13_eigvalOf_mem j with h | h
    · exact ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩
    · exact ⟨by rw [h]; norm_num, by rw [h]; norm_num⟩
  exact absurd hmem hj

/-- `hsepAB` fails on the fence fixture: A's out-of-window 3-mode is
at distance 0 from B's in-window 3-mode. -/
theorem bdks_fence_sepAB_fails :
    ¬ (∀ i, ¬((-1 : ℝ) < eigvalOf diag13 diag13_symm i
          ∧ eigvalOf diag13 diag13_symm i ≤ 2) →
        ∀ j, (-1 : ℝ) < eigvalOf diag13 diag13_symm j
          ∧ eigvalOf diag13 diag13_symm j ≤ 4 →
        (1 / 2 : ℝ) ≤ |eigvalOf diag13 diag13_symm i
          - eigvalOf diag13 diag13_symm j|) := by
  obtain ⟨i₃, hi₃⟩ := diag13_exists_three
  intro h
  have hout : ¬((-1 : ℝ) < eigvalOf diag13 diag13_symm i₃
      ∧ eigvalOf diag13 diag13_symm i₃ ≤ 2) := by
    intro hcon
    have h2 : eigvalOf diag13 diag13_symm i₃ ≤ 2 := hcon.2
    rw [hi₃] at h2
    exact absurd h2 (by norm_num)
  have hin : (-1 : ℝ) < eigvalOf diag13 diag13_symm i₃
      ∧ eigvalOf diag13 diag13_symm i₃ ≤ 4 :=
    ⟨by rw [hi₃]; norm_num, by rw [hi₃]; norm_num⟩
  have hbad := h i₃ hout i₃ hin
  rw [hi₃, sub_self, abs_zero] at hbad
  exact absurd hbad (by norm_num)

/-- The isolation: every guard verified, `hsepBA` holds, `hsepAB`
fails — exactly the new hypothesis isolated (there is no rank
hypothesis to check; that is the point). -/
theorem bdks_fence_only_sepAB_fails :
    (0 : ℝ) < 1 / 2
    ∧ ((-1 : ℝ) ≤ 2 ∧ (-1 : ℝ) ≤ (4 : ℝ))
    ∧ (∀ j, ¬((-1 : ℝ) < eigvalOf diag13 diag13_symm j
          ∧ eigvalOf diag13 diag13_symm j ≤ 4) →
        ∀ i, (-1 : ℝ) < eigvalOf diag13 diag13_symm i
          ∧ eigvalOf diag13 diag13_symm i ≤ 2 →
        (1 / 2 : ℝ) ≤ |eigvalOf diag13 diag13_symm j
          - eigvalOf diag13 diag13_symm i|)
    ∧ ¬ (∀ i, ¬((-1 : ℝ) < eigvalOf diag13 diag13_symm i
          ∧ eigvalOf diag13 diag13_symm i ≤ 2) →
        ∀ j, (-1 : ℝ) < eigvalOf diag13 diag13_symm j
          ∧ eigvalOf diag13 diag13_symm j ≤ 4 →
        (1 / 2 : ℝ) ≤ |eigvalOf diag13 diag13_symm i
          - eigvalOf diag13 diag13_symm j|)
    ∧ ¬ (‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector diag13 diag13_symm (-1) (4 : ℝ)‖
      ≤ 2 * ‖diag13 - diag13‖ / (1 / 2 : ℝ)) :=
  ⟨by norm_num, ⟨by norm_num, by norm_num⟩, bdks_fence_sepBA_holds,
    bdks_fence_sepAB_fails, bdks_sep_fence⟩

/-!
## Section 4: the decomposition-coherence witness

The consumed ring identity `P - Q = (I - Q) * P - Q * (I - P)`
exhibited at the action level on the rotated fixture: both composite
parts computed independently from the imported action pins.
-/

/-- The first composite part: `(I - Q) P *ᵥ e0 = ![1/10, 3/10]`,
raw from the imported pins (`P *ᵥ e0 = e0`, `Q *ᵥ e0 =
![9/10, -3/10]`). -/
theorem bdks_decomp_part1 :
    ((1 - bandProjector bdkB bdkB_symm (-1) 2)
        * bandProjector diag13 diag13_symm (-1) 2)
      *ᵥ (![1, 0] : Fin 2 → ℝ) = ![1 / 10, 3 / 10] := by
  rw [← Matrix.mulVec_mulVec, band_diag13_low_e0, Matrix.sub_mulVec,
    Matrix.one_mulVec,
    bdkd_Qe0_of_mem (-1) 2 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)]
  funext k
  fin_cases k <;> norm_num

/-- The second composite part: `Q (I - P) *ᵥ e0 = 0` — `P` fixes
`e0`, so the complement kills it. -/
theorem bdks_decomp_part2 :
    (bandProjector bdkB bdkB_symm (-1) 2
        * (1 - bandProjector diag13 diag13_symm (-1) 2))
      *ᵥ (![1, 0] : Fin 2 → ℝ) = 0 := by
  rw [← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    band_diag13_low_e0, sub_self, Matrix.mulVec_zero]

/-- **The decomposition-coherence witness.** The difference action at
`e0` (pinned `![1/10, 3/10]` by the imported raw route) equals the
first composite part minus the second — both parts computed
independently of the module's private identity. -/
theorem bdks_decomp_coherence :
    (bandProjector diag13 diag13_symm (-1) 2
        - bandProjector bdkB bdkB_symm (-1) 2) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = ((1 - bandProjector bdkB bdkB_symm (-1) 2)
          * bandProjector diag13 diag13_symm (-1) 2)
          *ᵥ (![1, 0] : Fin 2 → ℝ)
        - (bandProjector bdkB bdkB_symm (-1) 2
            * (1 - bandProjector diag13 diag13_symm (-1) 2))
            *ᵥ (![1, 0] : Fin 2 → ℝ)
    ∧ (bandProjector diag13 diag13_symm (-1) 2
        - bandProjector bdkB bdkB_symm (-1) 2)
        *ᵥ (![1, 0] : Fin 2 → ℝ) = ![1 / 10, 3 / 10] := by
  refine ⟨?_, bdkd_diff_e0_of_mem (-1) 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)⟩
  rw [bdks_decomp_part1, bdks_decomp_part2, sub_zero,
    bdkd_diff_e0_of_mem (-1) 2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
