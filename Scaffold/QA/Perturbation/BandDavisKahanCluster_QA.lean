/-
  BandDavisKahanCluster_QA.lean

  Purpose
  -------
  QA lemmas for the eigenvalue-cluster-separated (pairwise, YWS-literal)
  difference form of the band Davis–Kahan theorem in
  `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
  (`proposals/band-davis-kahan-cluster.md`):

      ‖P_A(a1,b1] - P_B(a2,b2]‖ ≤ ‖A - B‖ / δ

  under *pairwise* separation — every eigenvalue of `B` outside its
  window δ-away from every eigenvalue of `A` inside its window, the
  literal Yu–Wang–Samworth Theorem 1 δ at constant 1 — a strictly
  weaker hypothesis than the delivered closure separation.

  Four sections:

  1. **The interior witness — new coverage** — `A = diag(0, 5, 11)`
     window `(-1, 6]` (cluster `{0, 5}` with the internal gap
     `(0, 5)`), `B = diag(1, 2, 4)` window `(0, 3]` (cluster `{1, 2}`):
     B's out-of-window eigenvalue `4` sits strictly inside A's cluster
     range at pairwise distance `min(4, 1) = 1 = δ` from both cluster
     eigenvalues. The *delivered* theorem's closure-separation shape is
     refuted in proved form at the same data (`b1 + δ = 7 ≤ 4` is
     false at the 4-mode), so this configuration is unreachable by the
     closure form and covered by the pairwise one. Both band projectors
     are pinned entrywise to `diag(1, 1, 0)` (through the new
     zero/one threshold lemmas plus the two-mode entrywise sum), so the
     difference is exactly `0`, joined with the theorem bound
     `≤ ‖A - B‖ ≤ 7`.

  2. **The rotated non-trivial witness** — the sibling's fixture
     (`bdkB` vs `diag13`, equal windows `(-1, 2]`, δ = 3/4) through
     the new theorem: bound `≤ 1` against the imported raw lower
     `√(1/10)` — the two-route pattern at the new hypothesis shape.

  3. **The ε = 0 attainment** — A = B = diag13, *different* windows
     `(-1, 2]` vs `(-1/2, 5/2]` selecting the same cluster: the new
     capture-equality lemma pins the projectors equal, the theorem
     reads `‖P - Q‖ ≤ ‖A - A‖/δ = 0`, attained by genuinely distinct
     windows.

  4. **The fence — `hsep` load-bearing, refuted in proved form** —
     A = B = diag13, windows `(-1, 2]` vs `(2, 4]` (equal ranks 1 =
     1, guards verified): B's out-of-window eigenvalue 1 is at
     distance 0 from A's in-window eigenvalue 1, so the pairwise
     hypothesis fails and the hypothesis-free conclusion `‖P - Q‖ ≤ 0`
     is refuted with the norm at least `1` at `e0` — the mirror of the
     sibling's rank fence, isolating the new hypothesis.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan
import Scaffold.QA.Perturbation.BandDavisKahanDiff_QA

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open SpectralGraphTheory
open SpectralGraphTheory.QA

/-!
## Fin 3 generic diagonal helpers

The eigen-equation of a diagonal matrix forces each eigenvalue onto
the entry set and each eigenvector onto the coordinate of its
eigenvalue; with distinct entries, orthonormality then forces each
eigenvalue class to be a singleton.
-/

section Fin3Diagonal

variable {d : Fin 3 → ℝ}

private theorem eigvalOf_diagonal_eq_entry
    (hM : (Matrix.diagonal d).IsSymm) (i : Fin 3) :
    ∃ k : Fin 3, eigvalOf (Matrix.diagonal d) hM i = d k := by
  have hev : ∀ l : Fin 3, d l * eigvecOf (Matrix.diagonal d) hM i l
      = eigvalOf (Matrix.diagonal d) hM i
        * eigvecOf (Matrix.diagonal d) hM i l := by
    intro l
    have h0 : (Matrix.diagonal d) *ᵥ (eigvecOf (Matrix.diagonal d) hM i)
        = eigvalOf (Matrix.diagonal d) hM i
          • eigvecOf (Matrix.diagonal d) hM i :=
      (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
    have := congrFun h0 l
    simpa [Matrix.mulVec, Matrix.dotProduct, Matrix.diagonal_apply] using this
  have hv0 : eigvecOf (Matrix.diagonal d) hM i ≠ 0 := by
    intro h
    have hnn := eigvecOf_inner (Matrix.diagonal d) hM i i
    rw [h, if_pos rfl] at hnn
    simp at hnn
  obtain ⟨k, hk⟩ : ∃ k : Fin 3, eigvecOf (Matrix.diagonal d) hM i k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hv0 (funext hcon)
  refine ⟨k, ?_⟩
  exact (mul_right_cancel₀ hk (hev k)).symm

/-- Off-coordinate support: an eigenvector of a diagonal matrix
vanishes at every coordinate whose entry differs from its
eigenvalue. -/
private theorem eigvecOf_diagonal_apply_eq_zero
    (hM : (Matrix.diagonal d).IsSymm) (i l : Fin 3)
    (h : d l ≠ eigvalOf (Matrix.diagonal d) hM i) :
    eigvecOf (Matrix.diagonal d) hM i l = 0 := by
  have hev : d l * eigvecOf (Matrix.diagonal d) hM i l
      = eigvalOf (Matrix.diagonal d) hM i
        * eigvecOf (Matrix.diagonal d) hM i l := by
    have h0 : (Matrix.diagonal d) *ᵥ (eigvecOf (Matrix.diagonal d) hM i)
        = eigvalOf (Matrix.diagonal d) hM i
          • eigvecOf (Matrix.diagonal d) hM i :=
      (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
    have := congrFun h0 l
    simpa [Matrix.mulVec, Matrix.dotProduct, Matrix.diagonal_apply] using this
  have hsub : d l * eigvecOf (Matrix.diagonal d) hM i l
      - eigvalOf (Matrix.diagonal d) hM i
        * eigvecOf (Matrix.diagonal d) hM i l = 0 := by linarith
  rw [← sub_mul] at hsub
  rcases mul_eq_zero.1 hsub with h' | h'
  · exact absurd (sub_eq_zero.mp h') h
  · exact h'

/-- Eigenvalue classes of a distinct-entry diagonal are singletons:
two eigenvectors at a common eigenvalue are both supported on the
same coordinate, so their inner product is a product of nonzero
entries — contradicting orthonormality. -/
private theorem eigvalOf_diagonal_inj
    (hM : (Matrix.diagonal d).IsSymm)
    (hd : ∀ a b : Fin 3, d a = d b → a = b) (i j : Fin 3)
    (h : eigvalOf (Matrix.diagonal d) hM i
      = eigvalOf (Matrix.diagonal d) hM j) : i = j := by
  by_contra hij
  obtain ⟨k, hk⟩ := eigvalOf_diagonal_eq_entry hM i
  have hsupp : ∀ l : Fin 3, l ≠ k →
      eigvecOf (Matrix.diagonal d) hM i l = 0 ∧
      eigvecOf (Matrix.diagonal d) hM j l = 0 := by
    intro l hl
    have hdi : d l ≠ eigvalOf (Matrix.diagonal d) hM i := by
      rw [hk]
      intro hcon
      exact hl (hd l k hcon)
    have hdj : d l ≠ eigvalOf (Matrix.diagonal d) hM j := by
      intro hcon
      exact hdi (hcon.trans h.symm)
    exact ⟨eigvecOf_diagonal_apply_eq_zero hM i l hdi,
      eigvecOf_diagonal_apply_eq_zero hM j l hdj⟩
  have hvik : eigvecOf (Matrix.diagonal d) hM i k ≠ 0 := by
    intro hz
    have hzall : eigvecOf (Matrix.diagonal d) hM i = 0 := by
      funext l
      by_cases hl : l = k
      · rw [hl, hz, Pi.zero_apply]
      · exact (hsupp l hl).1
    have hnn := eigvecOf_inner (Matrix.diagonal d) hM i i
    rw [hzall, if_pos rfl] at hnn
    simp at hnn
  have hvjk : eigvecOf (Matrix.diagonal d) hM j k ≠ 0 := by
    intro hz
    have hzall : eigvecOf (Matrix.diagonal d) hM j = 0 := by
      funext l
      by_cases hl : l = k
      · rw [hl, hz, Pi.zero_apply]
      · exact (hsupp l hl).2
    have hnn := eigvecOf_inner (Matrix.diagonal d) hM j j
    rw [hzall, if_pos rfl] at hnn
    simp at hnn
  have hinner := eigvecOf_inner (Matrix.diagonal d) hM i j
  rw [if_neg (fun hcon => hij hcon)] at hinner
  have hexpand : ∑ l : Fin 3, eigvecOf (Matrix.diagonal d) hM i l
        * eigvecOf (Matrix.diagonal d) hM j l
      = eigvecOf (Matrix.diagonal d) hM i k
        * eigvecOf (Matrix.diagonal d) hM j k := by
    rw [Finset.sum_eq_single k]
    · intro b _ hb
      rw [(hsupp b hb).1, (hsupp b hb).2, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ k) h
  rw [hexpand] at hinner
  exact absurd hinner (mul_ne_zero hvik hvjk)

/-- Full support pin: an eigenvector at eigenvalue `d k` vanishes off
the `k`-th coordinate and has unit square on it. -/
private theorem eigvecOf_diagonal_at_entry
    (hM : (Matrix.diagonal d).IsSymm) (i k : Fin 3)
    (hval : eigvalOf (Matrix.diagonal d) hM i = d k)
    (hne : ∀ l : Fin 3, l ≠ k → d l ≠ d k) :
    (∀ l : Fin 3, l ≠ k → eigvecOf (Matrix.diagonal d) hM i l = 0)
      ∧ eigvecOf (Matrix.diagonal d) hM i k
        * eigvecOf (Matrix.diagonal d) hM i k = 1 := by
  have h1 : ∀ l : Fin 3, l ≠ k → eigvecOf (Matrix.diagonal d) hM i l = 0 := by
    intro l hl
    refine eigvecOf_diagonal_apply_eq_zero hM i l ?_
    rw [hval]
    exact hne l hl
  refine ⟨h1, ?_⟩
  have hnorm := eigvecOf_inner (Matrix.diagonal d) hM i i
  rw [if_pos rfl] at hnorm
  simp only [Matrix.dotProduct, Fin.sum_univ_three] at hnorm
  fin_cases k
  · rw [h1 1 (by decide), h1 2 (by decide)] at hnorm
    simpa using hnorm
  · rw [h1 0 (by decide), h1 2 (by decide)] at hnorm
    simpa using hnorm
  · rw [h1 0 (by decide), h1 1 (by decide)] at hnorm
    simpa using hnorm

end Fin3Diagonal

/-!
## The fixtures
-/

def clusterA : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![0, 5, 11]
def clusterB : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 2, 4]

theorem clusterA_symm : clusterA.IsSymm := by
  show clusterAᵀ = clusterA
  rw [clusterA, Matrix.diagonal_transpose]

theorem clusterB_symm : clusterB.IsSymm := by
  show clusterBᵀ = clusterB
  rw [clusterB, Matrix.diagonal_transpose]

theorem clusterA_sum :
    ∑ i, eigvalOf clusterA clusterA_symm i = 16 := by
  have h := eigvalOf_sum_eq_trace clusterA clusterA_symm
  rw [h]
  norm_num [clusterA, Matrix.trace_diagonal, Fin.sum_univ_three]

theorem clusterB_sum :
    ∑ i, eigvalOf clusterB clusterB_symm i = 7 := by
  have h := eigvalOf_sum_eq_trace clusterB clusterB_symm
  rw [h]
  norm_num [clusterB, Matrix.trace_diagonal, Fin.sum_univ_three]

theorem clusterA_mem (i : Fin 3) :
    eigvalOf clusterA clusterA_symm i = 0
      ∨ eigvalOf clusterA clusterA_symm i = 5
      ∨ eigvalOf clusterA clusterA_symm i = 11 := by
  have hk : ∃ k : Fin 3, eigvalOf clusterA clusterA_symm i
      = (![0, 5, 11] : Fin 3 → ℝ) k :=
    eigvalOf_diagonal_eq_entry clusterA_symm i
  obtain ⟨k, hk⟩ := hk
  fin_cases k <;> rw [hk] <;> simp

theorem clusterB_mem (i : Fin 3) :
    eigvalOf clusterB clusterB_symm i = 1
      ∨ eigvalOf clusterB clusterB_symm i = 2
      ∨ eigvalOf clusterB clusterB_symm i = 4 := by
  have hk : ∃ k : Fin 3, eigvalOf clusterB clusterB_symm i
      = (![1, 2, 4] : Fin 3 → ℝ) k :=
    eigvalOf_diagonal_eq_entry clusterB_symm i
  obtain ⟨k, hk⟩ := hk
  fin_cases k <;> rw [hk] <;> simp

private theorem clusterA_entries_inj (a b : Fin 3)
    (h : (![0, 5, 11] : Fin 3 → ℝ) a = (![0, 5, 11] : Fin 3 → ℝ) b) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all

private theorem clusterB_entries_inj (a b : Fin 3)
    (h : (![1, 2, 4] : Fin 3 → ℝ) a = (![1, 2, 4] : Fin 3 → ℝ) b) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all

theorem clusterA_inj (i j : Fin 3)
    (h : eigvalOf clusterA clusterA_symm i
      = eigvalOf clusterA clusterA_symm j) : i = j :=
  eigvalOf_diagonal_inj clusterA_symm clusterA_entries_inj i j h

theorem clusterB_inj (i j : Fin 3)
    (h : eigvalOf clusterB clusterB_symm i
      = eigvalOf clusterB clusterB_symm j) : i = j :=
  eigvalOf_diagonal_inj clusterB_symm clusterB_entries_inj i j h

/-- The top mode exists: without it every eigenvalue is at most `5`,
forcing the sum below the pinned trace. -/
theorem clusterA_exists_eleven :
    ∃ i : Fin 3, eigvalOf clusterA clusterA_symm i = 11 := by
  by_contra hcon
  push_neg at hcon
  have hle : ∀ i, eigvalOf clusterA clusterA_symm i ≤ 5 := by
    intro i
    rcases clusterA_mem i with h | h | h
    · rw [h]; norm_num
    · exact le_of_eq h
    · exact absurd h (hcon i)
  have hsumle : ∑ i, eigvalOf clusterA clusterA_symm i ≤ 15 := by
    have h1 : ∑ i, eigvalOf clusterA clusterA_symm i ≤ ∑ _ : Fin 3, (5 : ℝ) :=
      Finset.sum_le_sum fun i _ => hle i
    have h2 : ∑ _ : Fin 3, (5 : ℝ) = 15 := by norm_num
    linarith
  rw [clusterA_sum] at hsumle
  norm_num at hsumle

theorem clusterB_exists_four :
    ∃ i : Fin 3, eigvalOf clusterB clusterB_symm i = 4 := by
  by_contra hcon
  push_neg at hcon
  have hle : ∀ i, eigvalOf clusterB clusterB_symm i ≤ 2 := by
    intro i
    rcases clusterB_mem i with h | h | h
    · rw [h]; norm_num
    · exact le_of_eq h
    · exact absurd h (hcon i)
  have hsumle : ∑ i, eigvalOf clusterB clusterB_symm i ≤ 6 := by
    have h1 : ∑ i, eigvalOf clusterB clusterB_symm i ≤ ∑ _ : Fin 3, (2 : ℝ) :=
      Finset.sum_le_sum fun i _ => hle i
    have h2 : ∑ _ : Fin 3, (2 : ℝ) = 6 := by norm_num
    linarith
  rw [clusterB_sum] at hsumle
  norm_num at hsumle

/-- Three indices carrying values from a two-element set force two
equal values — contradicting class-injectivity. -/
private theorem exists_eigvalOf_two_values {M : Matrix (Fin 3) (Fin 3) ℝ}
    {hM : M.IsSymm} (x y : ℝ)
    (hval : ∀ i, eigvalOf M hM i = x ∨ eigvalOf M hM i = y)
    (hinj : ∀ i j : Fin 3, eigvalOf M hM i = eigvalOf M hM j → i = j) :
    False := by
  have h0 := hval 0
  have h1 := hval 1
  have h2 := hval 2
  rcases h0 with e0 | e0 <;> rcases h1 with e1 | e1 <;>
    rcases h2 with e2 | e2
  all_goals first
    | exact absurd (hinj 0 1 (e0.trans e1.symm)) (by decide)
    | exact absurd (hinj 0 2 (e0.trans e2.symm)) (by decide)
    | exact absurd (hinj 1 2 (e1.trans e2.symm)) (by decide)

theorem clusterA_exists_zero :
    ∃ i : Fin 3, eigvalOf clusterA clusterA_symm i = 0 := by
  by_contra hcon
  push_neg at hcon
  exact exists_eigvalOf_two_values (x := 5) (y := 11)
    (fun i => by
      rcases clusterA_mem i with h | h | h
      · exact absurd h (hcon i)
      · exact Or.inl h
      · exact Or.inr h) clusterA_inj

theorem clusterA_exists_five :
    ∃ i : Fin 3, eigvalOf clusterA clusterA_symm i = 5 := by
  by_contra hcon
  push_neg at hcon
  exact exists_eigvalOf_two_values (x := 0) (y := 11)
    (fun i => by
      rcases clusterA_mem i with h | h | h
      · exact Or.inl h
      · exact absurd h (hcon i)
      · exact Or.inr h) clusterA_inj

theorem clusterB_exists_one :
    ∃ i : Fin 3, eigvalOf clusterB clusterB_symm i = 1 := by
  by_contra hcon
  push_neg at hcon
  exact exists_eigvalOf_two_values (x := 2) (y := 4)
    (fun i => by
      rcases clusterB_mem i with h | h | h
      · exact absurd h (hcon i)
      · exact Or.inl h
      · exact Or.inr h) clusterB_inj

theorem clusterB_exists_two :
    ∃ i : Fin 3, eigvalOf clusterB clusterB_symm i = 2 := by
  by_contra hcon
  push_neg at hcon
  exact exists_eigvalOf_two_values (x := 1) (y := 4)
    (fun i => by
      rcases clusterB_mem i with h | h | h
      · exact Or.inl h
      · exact absurd h (hcon i)
      · exact Or.inr h) clusterB_inj

/-!
## The projector pins
-/

/-- The threshold projector at `6` selects the two cluster modes of
`A`, each supported on its own coordinate with unit square — the
entrywise sum is `diag(1, 1, 0)`. -/
theorem spClusterA_eq :
    spectralProjector clusterA clusterA_symm 6
      = Matrix.diagonal ![1, 1, 0] := by
  obtain ⟨i₀, hi₀⟩ := clusterA_exists_zero
  obtain ⟨i₅, hi₅⟩ := clusterA_exists_five
  have hfilter : (Finset.univ.filter
      fun i => eigvalOf clusterA clusterA_symm i ≤ 6) = insert i₀ {i₅} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hle
      rcases clusterA_mem i with h | h | h
      · exact Or.inl (clusterA_inj i i₀ (h.trans hi₀.symm))
      · exact Or.inr (clusterA_inj i i₅ (h.trans hi₅.symm))
      · rw [h] at hle; norm_num at hle
    · intro h
      rcases h with h | h
      · rw [h, hi₀]; norm_num
      · rw [h, hi₅]; norm_num
  obtain ⟨hs₀, hq₀⟩ :
      (∀ l : Fin 3, l ≠ 0 → eigvecOf clusterA clusterA_symm i₀ l = 0)
        ∧ eigvecOf clusterA clusterA_symm i₀ 0
          * eigvecOf clusterA clusterA_symm i₀ 0 = 1 :=
    eigvecOf_diagonal_at_entry clusterA_symm i₀ 0 hi₀
      (by intro l hl; fin_cases l <;>
        first | exact absurd rfl hl | norm_num [clusterA])
  obtain ⟨hs₅, hq₅⟩ :
      (∀ l : Fin 3, l ≠ 1 → eigvecOf clusterA clusterA_symm i₅ l = 0)
        ∧ eigvecOf clusterA clusterA_symm i₅ 1
          * eigvecOf clusterA clusterA_symm i₅ 1 = 1 :=
    eigvecOf_diagonal_at_entry clusterA_symm i₅ 1 hi₅
      (by intro l hl; fin_cases l <;>
        first | exact absurd rfl hl | norm_num [clusterA])
  have hne : i₀ ≠ i₅ := by
    intro h
    rw [h] at hi₀
    rw [hi₀] at hi₅
    norm_num at hi₅
  rw [spectralProjector, hfilter]
  ext a b
  simp only [Matrix.of_apply]
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  fin_cases a <;> fin_cases b <;>
    simp [hs₀, hs₅, hq₀, hq₅]

/-- The A-cluster band projector, through the new zero lemma for the
empty low threshold band. -/
theorem bandClusterA_eq :
    bandProjector clusterA clusterA_symm (-1) 6
      = Matrix.diagonal ![1, 1, 0] := by
  rw [bandProjector, spClusterA_eq,
    spectralProjector_eq_zero clusterA clusterA_symm (-1) (fun i => by
      rcases clusterA_mem i with h | h | h <;> rw [h] <;> norm_num),
    sub_zero]

theorem spClusterB_eq :
    spectralProjector clusterB clusterB_symm 3
      = Matrix.diagonal ![1, 1, 0] := by
  obtain ⟨i₁, hi₁⟩ := clusterB_exists_one
  obtain ⟨i₂, hi₂⟩ := clusterB_exists_two
  have hfilter : (Finset.univ.filter
      fun i => eigvalOf clusterB clusterB_symm i ≤ 3) = insert i₁ {i₂} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hle
      rcases clusterB_mem i with h | h | h
      · exact Or.inl (clusterB_inj i i₁ (h.trans hi₁.symm))
      · exact Or.inr (clusterB_inj i i₂ (h.trans hi₂.symm))
      · rw [h] at hle; norm_num at hle
    · intro h
      rcases h with h | h
      · rw [h, hi₁]; norm_num
      · rw [h, hi₂]; norm_num
  obtain ⟨hs₁, hq₁⟩ :
      (∀ l : Fin 3, l ≠ 0 → eigvecOf clusterB clusterB_symm i₁ l = 0)
        ∧ eigvecOf clusterB clusterB_symm i₁ 0
          * eigvecOf clusterB clusterB_symm i₁ 0 = 1 :=
    eigvecOf_diagonal_at_entry clusterB_symm i₁ 0 hi₁
      (by intro l hl; fin_cases l <;>
        first | exact absurd rfl hl | norm_num [clusterB])
  obtain ⟨hs₂, hq₂⟩ :
      (∀ l : Fin 3, l ≠ 1 → eigvecOf clusterB clusterB_symm i₂ l = 0)
        ∧ eigvecOf clusterB clusterB_symm i₂ 1
          * eigvecOf clusterB clusterB_symm i₂ 1 = 1 :=
    eigvecOf_diagonal_at_entry clusterB_symm i₂ 1 hi₂
      (by intro l hl; fin_cases l <;>
        first | exact absurd rfl hl | norm_num [clusterB])
  have hne : i₁ ≠ i₂ := by
    intro h
    rw [h] at hi₁
    rw [hi₁] at hi₂
    norm_num at hi₂
  rw [spectralProjector, hfilter]
  ext a b
  simp only [Matrix.of_apply]
  rw [Finset.sum_insert (by simp [hne]), Finset.sum_singleton]
  fin_cases a <;> fin_cases b <;>
    simp [hs₁, hs₂, hq₁, hq₂]

theorem bandClusterB_eq :
    bandProjector clusterB clusterB_symm 0 3
      = Matrix.diagonal ![1, 1, 0] := by
  rw [bandProjector, spClusterB_eq,
    spectralProjector_eq_zero clusterB clusterB_symm 0 (fun i => by
      rcases clusterB_mem i with h | h | h <;> rw [h] <;> norm_num),
    sub_zero]

/-- The window counts, through the trace lemma and the pinned
projector values. -/
theorem clusterA_card_band :
    (Finset.univ.filter fun i =>
      (-1 : ℝ) < eigvalOf clusterA clusterA_symm i
        ∧ eigvalOf clusterA clusterA_symm i ≤ 6).card = 2 := by
  have h := trace_bandProjector_eq_card clusterA_symm (-1) 6 (by norm_num)
  rw [bandClusterA_eq] at h
  have h2 : (Matrix.diagonal (![1, 1, 0] : Fin 3 → ℝ)).trace = (2 : ℝ) := by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_three]
  have h3 : ((Finset.univ.filter fun i =>
      (-1 : ℝ) < eigvalOf clusterA clusterA_symm i
        ∧ eigvalOf clusterA clusterA_symm i ≤ 6).card : ℝ) = 2 := by
    linarith
  exact_mod_cast h3

theorem clusterB_card_band :
    (Finset.univ.filter fun i =>
      (0 : ℝ) < eigvalOf clusterB clusterB_symm i
        ∧ eigvalOf clusterB clusterB_symm i ≤ 3).card = 2 := by
  have h := trace_bandProjector_eq_card clusterB_symm 0 3 (by norm_num)
  rw [bandClusterB_eq] at h
  have h2 : (Matrix.diagonal (![1, 1, 0] : Fin 3 → ℝ)).trace = (2 : ℝ) := by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_three]
  have h3 : ((Finset.univ.filter fun i =>
      (0 : ℝ) < eigvalOf clusterB clusterB_symm i
        ∧ eigvalOf clusterB clusterB_symm i ≤ 3).card : ℝ) = 2 := by
    linarith
  exact_mod_cast h3

theorem bdkc_rank_eq :
    (bandProjector clusterA clusterA_symm (-1) 6).rank
      = (bandProjector clusterB clusterB_symm 0 3).rank := by
  rw [rank_bandProjector_eq_card clusterA_symm (-1) 6 (by norm_num),
    rank_bandProjector_eq_card clusterB_symm 0 3 (by norm_num),
    clusterA_card_band, clusterB_card_band]

/-- The perturbation norm bound for the interior fixture. -/
theorem clusterDiff_norm_le : ‖clusterA - clusterB‖ ≤ 7 := by
  have hdef : clusterA - clusterB
      = Matrix.diagonal ![-1, 3, 7] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [clusterA, clusterB, Matrix.sub_apply, Matrix.diagonal_apply] <;>
      norm_num
  have hsymm : (Matrix.diagonal ![-1, 3, 7] : Matrix (Fin 3) (Fin 3) ℝ).IsSymm := by
    show _ᵀ = _
    rw [Matrix.diagonal_transpose]
  have hmem : ∀ i, eigvalOf (Matrix.diagonal ![-1, 3, 7]) hsymm i = -1
      ∨ eigvalOf (Matrix.diagonal ![-1, 3, 7]) hsymm i = 3
      ∨ eigvalOf (Matrix.diagonal ![-1, 3, 7]) hsymm i = 7 := by
    intro i
    have hk : ∃ k : Fin 3, eigvalOf (Matrix.diagonal ![-1, 3, 7]) hsymm i
        = (![-1, 3, 7] : Fin 3 → ℝ) k :=
      eigvalOf_diagonal_eq_entry hsymm i
    obtain ⟨k, hk⟩ := hk
    fin_cases k <;> rw [hk] <;> simp
  rw [hdef, Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_eq_max_abs_evals hsymm (by norm_num)]
  have h0 : |evals hsymm ⟨0, by norm_num⟩| ≤ 7 := by
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf hsymm ⟨0, by norm_num⟩
    rw [hi]
    rcases hmem i with h | h | h <;> rw [h] <;> norm_num
  have h2 : |evals hsymm ⟨2, by norm_num⟩| ≤ 7 := by
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf hsymm ⟨2, by norm_num⟩
    rw [hi]
    rcases hmem i with h | h | h <;> rw [h] <;> norm_num
  exact max_le h0 h2

/-!
## Section 1: the interior witness — new coverage, closure
separation provably failing
-/

/-- The pairwise hypothesis at the interior fixture: B's out-of-window
eigenvalue is `4` (values `1, 2` are in-window), and both of A's
in-window eigenvalues `0, 5` are at distance at least `1` from it. -/
theorem bdkc_interior_hsep :
    ∀ j, ¬((0 : ℝ) < eigvalOf clusterB clusterB_symm j
        ∧ eigvalOf clusterB clusterB_symm j ≤ 3) →
      ∀ i, (-1 : ℝ) < eigvalOf clusterA clusterA_symm i
        → eigvalOf clusterA clusterA_symm i ≤ 6 →
        (1 : ℝ) ≤ |eigvalOf clusterB clusterB_symm j
          - eigvalOf clusterA clusterA_symm i| := by
  intro j hjout i hinA hloA
  have hμ : eigvalOf clusterB clusterB_symm j = 4 := by
    rcases clusterB_mem j with h | h | h
    · exact absurd (by rw [h]; norm_num) hjout
    · exact absurd (by rw [h]; norm_num) hjout
    · exact h
  have hlA : eigvalOf clusterA clusterA_symm i = 0
      ∨ eigvalOf clusterA clusterA_symm i = 5 := by
    rcases clusterA_mem i with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · rw [h] at hloA; norm_num at hloA
  rcases hlA with h | h <;> rw [hμ, h] <;> norm_num

/-- **The interior witness.** The closure-separation shape of the
delivered theorem is refuted at this fixture: the high-side clause
would read `6 ≤ eigvalOf` at the 4-mode — false. -/
theorem bdkc_interior_not_closure :
    ¬ (∀ j, (3 : ℝ) < eigvalOf clusterB clusterB_symm j →
        (6 : ℝ) ≤ eigvalOf clusterB clusterB_symm j) := by
  intro h
  obtain ⟨i₄, hi₄⟩ := clusterB_exists_four
  have hlt : (3 : ℝ) < eigvalOf clusterB clusterB_symm i₄ := by
    rw [hi₄]; norm_num
  have := h i₄ hlt
  rw [hi₄] at this
  norm_num at this

/-- **The interior witness, both routes.** The raw route pins both
band projectors to `diag(1, 1, 0)` entrywise, so the distance is
exactly `0`; the theorem (through the pairwise hypothesis the closure
form cannot consume here) bounds it by `‖A - B‖ ≤ 7`. -/
theorem bdkc_interior_QA :
    ‖bandProjector clusterA clusterA_symm (-1) 6
        - bandProjector clusterB clusterB_symm 0 3‖ = 0
      ∧ ‖bandProjector clusterA clusterA_symm (-1) 6
          - bandProjector clusterB clusterB_symm 0 3‖ ≤ 7 := by
  refine ⟨?_, ?_⟩
  · rw [bandClusterA_eq, bandClusterB_eq, sub_self, norm_zero]
  · have hthm := l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise
      clusterA_symm clusterB_symm (-1) 6 0 3 (by norm_num) (by norm_num)
      (δ := (1 : ℝ)) (by norm_num) bdkc_rank_eq bdkc_interior_hsep
    calc ‖bandProjector clusterA clusterA_symm (-1) 6
          - bandProjector clusterB clusterB_symm 0 3‖
        ≤ ‖clusterA - clusterB‖ / (1 : ℝ) := hthm
      _ = ‖clusterA - clusterB‖ := div_one _
      _ ≤ 7 := clusterDiff_norm_le

/-!
## Section 2: the rotated non-trivial witness
-/

theorem bdkc_rotated_QA :
    Real.sqrt (1 / 10)
      ≤ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2‖
      ∧ ‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector bdkB bdkB_symm (-1) 2‖
        ≤ 1 := by
  refine ⟨bdkd_rotated_QA.1, ?_⟩
  have hsep : ∀ j, ¬((-1 : ℝ) < eigvalOf bdkB bdkB_symm j
        ∧ eigvalOf bdkB bdkB_symm j ≤ 2) →
      ∀ i, (-1 : ℝ) < eigvalOf diag13 diag13_symm i
        → eigvalOf diag13 diag13_symm i ≤ 2 →
        (3 / 4 : ℝ) ≤ |eigvalOf bdkB bdkB_symm j
          - eigvalOf diag13 diag13_symm i| := by
    intro j hjout i hinA hloA
    have hμ : eigvalOf bdkB bdkB_symm j = 13 / 4 := by
      rcases bdkB_eigvalOf_mem j with h | h
      · exact absurd (by rw [h]; norm_num) hjout
      · exact h
    have hlA : eigvalOf diag13 diag13_symm i = 1 := by
      rcases diag13_eigvalOf_mem i with h | h
      · exact h
      · rw [h] at hloA; norm_num at hloA
    rw [hμ, hlA, abs_of_nonneg (by norm_num)]
    norm_num
  have hthm := l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise
    diag13_symm bdkB_symm (-1) 2 (-1) 2 (by norm_num) (by norm_num)
    (δ := (3 / 4 : ℝ)) (by norm_num) bdkd_rank_eq hsep
  calc ‖bandProjector diag13 diag13_symm (-1) 2
        - bandProjector bdkB bdkB_symm (-1) 2‖
      ≤ ‖diag13 - bdkB‖ / (3 / 4 : ℝ) := hthm
    _ ≤ (3 / 4 : ℝ) / (3 / 4 : ℝ) :=
        div_le_div₀ (by norm_num : (0 : ℝ) ≤ 3 / 4) bdkE_norm_le
          (by norm_num : (0 : ℝ) < 3 / 4) (le_refl _)
    _ = 1 := by field_simp

/-!
## Section 3: the ε = 0 attainment through the capture-equality lemma
-/

/-- The two windows `(-1, 2]` and `(-1/2, 5/2]` select the same
cluster of `diag13` — the new capture-equality lemma pins the band
projectors equal. -/
theorem bdkc_capture_QA :
    bandProjector diag13 diag13_symm (-1 / 2) (5 / 2)
      = bandProjector diag13 diag13_symm (-1) 2 := by
  refine bandProjector_eq_of_forall_mem_iff diag13_symm _ _ _ _
    (by norm_num) (by norm_num) ?_
  intro i
  rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num

/-- The raw route: the difference of the two equal projectors is
zero. -/
theorem bdkc_zeroE_raw :
    ‖bandProjector diag13 diag13_symm (-1) 2
        - bandProjector diag13 diag13_symm (-1 / 2) (5 / 2)‖ = 0 := by
  rw [bdkc_capture_QA, sub_self, norm_zero]

/-- **The ε = 0 attainment.** Through the theorem at genuinely
distinct windows (rank equality transported by the capture lemma,
pairwise separation `|3 - 1| = 2 ≥ 1/2` at the out-of-window 3-mode):
`‖P - Q‖ ≤ ‖A - A‖/δ = 0`, attained. -/
theorem bdkc_zeroE_attained :
    ‖bandProjector diag13 diag13_symm (-1) 2
        - bandProjector diag13 diag13_symm (-1 / 2) (5 / 2)‖
      ≤ ‖diag13 - diag13‖ / (1 / 2 : ℝ) := by
  have hsep : ∀ j, ¬((-1 / 2 : ℝ) < eigvalOf diag13 diag13_symm j
        ∧ eigvalOf diag13 diag13_symm j ≤ 5 / 2) →
      ∀ i, (-1 : ℝ) < eigvalOf diag13 diag13_symm i
        → eigvalOf diag13 diag13_symm i ≤ 2 →
        (1 / 2 : ℝ) ≤ |eigvalOf diag13 diag13_symm j
          - eigvalOf diag13 diag13_symm i| := by
    intro j hjout i hinA hloA
    have hμ : eigvalOf diag13 diag13_symm j = 3 := by
      rcases diag13_eigvalOf_mem j with h | h
      · exact absurd (by rw [h]; norm_num) hjout
      · exact h
    have hlA : eigvalOf diag13 diag13_symm i = 1 := by
      rcases diag13_eigvalOf_mem i with h | h
      · exact h
      · rw [h] at hloA; norm_num at hloA
    rw [hμ, hlA]; norm_num
  have hrank : (bandProjector diag13 diag13_symm (-1) 2).rank
      = (bandProjector diag13 diag13_symm (-1 / 2) (5 / 2)).rank := by
    rw [bdkc_capture_QA]
  exact l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise
    diag13_symm diag13_symm (-1) 2 (-1 / 2) (5 / 2) (by norm_num)
    (by norm_num) (δ := (1 / 2 : ℝ)) (by norm_num) hrank hsep

/-- The attainment instance evaluated: the bound is exactly `0`. -/
theorem bdkc_zeroE_evaluated :
    ‖bandProjector diag13 diag13_symm (-1) 2
        - bandProjector diag13 diag13_symm (-1 / 2) (5 / 2)‖
      ≤ (0 : ℝ) := by
  have h := bdkc_zeroE_attained
  have h0 : ‖diag13 - diag13‖ = 0 := by rw [sub_self, norm_zero]
  rw [h0, zero_div] at h
  exact h

/-!
## Section 4: the fence — the pairwise hypothesis load-bearing
-/

theorem bdkc_diag13_unique_three (i j : Fin 2)
    (hi : eigvalOf diag13 diag13_symm i = 3)
    (hj : eigvalOf diag13 diag13_symm j = 3) : i = j := by
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso
    have hsum := diag13_sum
    rw [show eigvalOf diag13 diag13_symm 0 = 3 from hi,
        show eigvalOf diag13 diag13_symm 1 = 3 from hj] at hsum
    norm_num at hsum
  · exfalso
    have hsum := diag13_sum
    rw [show eigvalOf diag13 diag13_symm 1 = 3 from hi,
        show eigvalOf diag13 diag13_symm 0 = 3 from hj] at hsum
    norm_num at hsum
  · rfl

theorem bdkc_diag13_card_band_high :
    (Finset.univ.filter fun i =>
      (2 : ℝ) < eigvalOf diag13 diag13_symm i
        ∧ eigvalOf diag13 diag13_symm i ≤ 4).card = 1 := by
  obtain ⟨j3, hj3⟩ := diag13_exists_three
  have hfilter : (Finset.univ.filter fun i =>
      (2 : ℝ) < eigvalOf diag13 diag13_symm i
        ∧ eigvalOf diag13 diag13_symm i ≤ 4) = {j3} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hwin
      rcases diag13_eigvalOf_mem i with h | h
      · rw [h] at hwin; norm_num at hwin
      · exact bdkc_diag13_unique_three i j3 h hj3
    · intro h
      rw [h, hj3]
      norm_num
  rw [hfilter, Finset.card_singleton]

theorem bdkc_rank_eq_high :
    (bandProjector diag13 diag13_symm (-1) 2).rank
      = (bandProjector diag13 diag13_symm 2 4).rank := by
  rw [rank_bandProjector_eq_card diag13_symm (-1) 2 (by norm_num),
    rank_bandProjector_eq_card diag13_symm 2 4 (by norm_num),
    diag13_card_band_low, bdkc_diag13_card_band_high]

/-- **The fence refuted in proved form.** With every hypothesis of the
pairwise theorem verified *except* the separation itself (windows
`(-1, 2]` and `(2, 4]` on A = B, equal ranks 1 = 1, δ = 1/2), the
hypothesis-free conclusion reads `‖P - Q‖ ≤ ‖A - A‖/δ = 0` — false,
since the difference is `diag(1, -1)` with norm at least `1` through
the action bound at `e0`. Exactly the pairwise hypothesis is the
violated one. -/
theorem bdkc_sep_fence :
    ¬ (‖bandProjector diag13 diag13_symm (-1) 2
          - bandProjector diag13 diag13_symm 2 4‖
        ≤ ‖diag13 - diag13‖ / (1 / 2 : ℝ)) := by
  intro hcon
  have h0 : diag13 - diag13 = 0 := by
    ext i j; simp
  rw [h0, norm_zero, zero_div] at hcon
  have hM : bandProjector diag13 diag13_symm (-1) 2
      - bandProjector diag13 diag13_symm 2 4
      = (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [band_diag13_low, band_diag13_high]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]
  rw [hM] at hcon
  have hact := l2OpNorm_mulVec_le
    (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ)
    (![1, 0] : Fin 2 → ℝ)
  have hz : (!![1, 0; 0, -1] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
      (![1, 0] : Fin 2 → ℝ) = ![1, 0] := by
    funext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  rw [hz, norm_euclidean_eq_sqrt] at hact
  have he0 : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [he0, Real.sqrt_one, mul_one] at hact
  linarith

/-- Every `hsep`-shaped hypothesis of the theorem's other assumptions
holds at the fence — the pairwise separation is the *only* failing
one (the out-of-window 1-mode of B is at distance exactly `0` from
the in-window 1-mode of A, against δ = 1/2). -/
theorem bdkc_fence_only_sep_fails :
    ¬ (∀ j, ¬((2 : ℝ) < eigvalOf diag13 diag13_symm j
          ∧ eigvalOf diag13 diag13_symm j ≤ 4) →
        ∀ i, (-1 : ℝ) < eigvalOf diag13 diag13_symm i
          → eigvalOf diag13 diag13_symm i ≤ 2 →
          (1 / 2 : ℝ) ≤ |eigvalOf diag13 diag13_symm j
            - eigvalOf diag13 diag13_symm i|)
      ∧ (bandProjector diag13 diag13_symm (-1) 2).rank
          = (bandProjector diag13 diag13_symm 2 4).rank := by
  refine ⟨?_, bdkc_rank_eq_high⟩
  intro h
  obtain ⟨i₁, hi₁⟩ := diag13_exists_one
  have hjout : ¬((2 : ℝ) < eigvalOf diag13 diag13_symm i₁
      ∧ eigvalOf diag13 diag13_symm i₁ ≤ 4) := by
    rw [hi₁]; norm_num
  have hin : (-1 : ℝ) < eigvalOf diag13 diag13_symm i₁
      ∧ eigvalOf diag13 diag13_symm i₁ ≤ 2 := by
    rw [hi₁]; norm_num
  have hval := h i₁ hjout i₁ hin.1 hin.2
  rw [hi₁, sub_self, abs_zero] at hval
  norm_num at hval

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
