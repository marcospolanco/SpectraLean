/-
  ClusterProjector_QA.lean

  Purpose
  -------
  QA lemmas for the set-valued spectral projector
  (`Scaffold.Mathlib.GraphTheory.ClusterProjector`) and its Davis–Kahan
  pair (`proposals/cluster-projector.md`, the SetForm sections of
  `Perturbation/BandDavisKahan.lean`):

      ‖P_B(T) * P_A(S)‖ ≤ ‖A - B‖ / δ        (product form)
      ‖P_A(S) - P_B(T)‖ ≤ ‖A - B‖ / δ        (difference form, equal rank)

  under center/radius membership separation — every in-`S` eigenvalue of
  `A` within `r` of `c`, every in-`T` (product) / out-of-`T`
  (difference) eigenvalue of `B` at distance at least `r + δ` from `c`.

  Four sections:

  1. **The non-interval witness** — on the imported fixture
     `clusterA = diag(0, 5, 11)`, the cluster projector of the
     non-interval set `{0, 11}` is pinned entrywise to `diag(1, 0, 1)`
     — a subspace NO window expresses — through a four-lemma composition
     (capture at sets, the complement law, the band agreement, and the
     imported threshold-projector pin), plus the idempotence/action/
     complement/disjointness interface witnesses and the rank counts.

  2. **The non-interval difference instance** — `A = diag(0, 5, 11)` at
     `S = {0, 11}` vs `B = diag(-1, 5, 11)` at `T = {5, 11}`, at the
     exact-fit data `c = 11/2`, `r = 11/2`, `δ = 1` (A's in-`S`
     eigenvalues at distance exactly `r` from `c`; B's out-of-`T`
     eigenvalue `-1` at distance exactly `r + δ`): the theorem's bound
     `≤ ‖A - B‖ ≤ 1` joined with the raw lower bound `1 ≤ ‖P - Q‖` at
     `e₀` (the difference pinned entrywise to `diag(1, -1, 0)`, both
     projectors diagonal, the two-route pattern).

  3. **The ε = 0 attainment** — `A = B` at `S = T = {5}` (singleton
     clusters, `c = 5`, `r = 0`, δ = 1/2 with the out-of-`T` separation
     genuinely discharged): the conclusion reads `‖P - P‖ ≤ 0`,
     attained.

  4. **The fence — `hfar` load-bearing, refuted in proved form** — on
     the interior-gap configuration the proposal's recorded obstruction
     names: `A = B = diag(0, 5, 11)`, `S = {0, 11}`, `T = {5, 11}`.
     Ranks are equal (`2 = 2` through the counts), `hnear` holds, but
     the out-of-`T` eigenvalue `0` sits at range-interior distance
     `11/2 < 11/2 + δ` — `hfar` fails exactly there, and the
     hypothesis-free conclusion `‖P - Q‖ ≤ 0` is refuted with the norm
     lower-bounded by `1` at `e₀`.

  The adversarial fence audit of the shelf's own clause surface
  (proposal `adversarial-fences-band-projector-family.md`, 2026-09-04)
  is the fifth section: seven hypothesis-form fences over
  `ClusterProjector.lean`'s mode-selection, corner, disjointness,
  capture, and band-agreement statements at the same fixtures.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan
import Scaffold.QA.Perturbation.BandDavisKahanCluster_QA

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open SpectralGraphTheory

/-!
  ## Private Fin 3 diagonal helpers

  The eigen-equation of a diagonal matrix forces each eigenvalue onto
  the entry set and each eigenvector onto the coordinate of its
  eigenvalue. Copies of the cluster QA's private layer (that file's
  public fixture lemmas — `clusterA_mem`, `clusterA_inj`,
  `clusterA_exists_*`, `spClusterA_eq` — are imported and reused; only
  the generic helpers are private there).
-/

section Fin3Diagonal

variable {d : Fin 3 → ℝ}

private theorem eigvalOf_diagonal_eq_entry'
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

private theorem eigvecOf_diagonal_apply_eq_zero'
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

private theorem eigvecOf_diagonal_at_entry'
    (hM : (Matrix.diagonal d).IsSymm) (i k : Fin 3)
    (hval : eigvalOf (Matrix.diagonal d) hM i = d k)
    (hne : ∀ l : Fin 3, l ≠ k → d l ≠ d k) :
    (∀ l : Fin 3, l ≠ k → eigvecOf (Matrix.diagonal d) hM i l = 0)
      ∧ eigvecOf (Matrix.diagonal d) hM i k
        * eigvecOf (Matrix.diagonal d) hM i k = 1 := by
  have h1 : ∀ l : Fin 3, l ≠ k →
      eigvecOf (Matrix.diagonal d) hM i l = 0 := by
    intro l hl
    refine eigvecOf_diagonal_apply_eq_zero' hM i l ?_
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

/-- Eigenvalue classes of a distinct-entry diagonal are singletons
(the cluster QA's generic route, copied for this file's private
layer). -/
private theorem eigvalOf_diagonal_inj'
    (hM : (Matrix.diagonal d).IsSymm)
    (hd : ∀ a b : Fin 3, d a = d b → a = b) (i j : Fin 3)
    (h : eigvalOf (Matrix.diagonal d) hM i
      = eigvalOf (Matrix.diagonal d) hM j) : i = j := by
  by_contra hij
  obtain ⟨k, hk⟩ := eigvalOf_diagonal_eq_entry' hM i
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
    exact ⟨eigvecOf_diagonal_apply_eq_zero' hM i l hdi,
      eigvecOf_diagonal_apply_eq_zero' hM j l hdj⟩
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

end Fin3Diagonal

/-!
  ## The second fixture: `bm = diag(-1, 5, 11)`

  `B`'s out-of-`T` eigenvalue `-1` sits `δ`-below A's cluster range
  `[0, 11]` — the exact-fit difference configuration.
-/

def bm : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 5, 11]

theorem bm_symm : bm.IsSymm := by
  show bmᵀ = bm
  rw [bm, Matrix.diagonal_transpose]

theorem bm_mem (i : Fin 3) :
    eigvalOf bm bm_symm i = -1
      ∨ eigvalOf bm bm_symm i = 5
      ∨ eigvalOf bm bm_symm i = 11 := by
  have hk : ∃ k : Fin 3, eigvalOf bm bm_symm i
      = (![-1, 5, 11] : Fin 3 → ℝ) k :=
    eigvalOf_diagonal_eq_entry' bm_symm i
  obtain ⟨k, hk⟩ := hk
  fin_cases k <;> rw [hk] <;> simp

theorem bm_sum :
    ∑ i, eigvalOf bm bm_symm i = 15 := by
  have h := eigvalOf_sum_eq_trace bm bm_symm
  rw [h]
  norm_num [bm, Matrix.trace_diagonal, Fin.sum_univ_three]

private theorem bm_entries_inj (a b : Fin 3)
    (h : (![-1, 5, 11] : Fin 3 → ℝ) a
      = (![-1, 5, 11] : Fin 3 → ℝ) b) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all <;> linarith

theorem bm_inj (i j : Fin 3)
    (h : eigvalOf bm bm_symm i = eigvalOf bm bm_symm j) : i = j :=
  eigvalOf_diagonal_inj' bm_symm bm_entries_inj i j h

private theorem exists_eigvalOf_two_values' {M : Matrix (Fin 3) (Fin 3) ℝ}
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

theorem bm_exists_neg :
    ∃ i : Fin 3, eigvalOf bm bm_symm i = -1 := by
  by_contra hcon
  push_neg at hcon
  exact exists_eigvalOf_two_values' (x := 5) (y := 11)
    (fun i => by
      rcases bm_mem i with h | h | h
      · exact absurd h (hcon i)
      · exact Or.inl h
      · exact Or.inr h) bm_inj

/-!
  ## Section 1: the non-interval witness and the interface
-/

/-- The below-threshold projector selecting only the `0`-mode of
`clusterA` (the single-mode pin the imported cluster QA leaves
implicit). -/
theorem spA_four :
    spectralProjector clusterA clusterA_symm 4
      = Matrix.diagonal ![1, 0, 0] := by
  obtain ⟨i₀, hi₀⟩ := clusterA_exists_zero
  have hfilter : (Finset.univ.filter
      fun i => eigvalOf clusterA clusterA_symm i ≤ 4) = {i₀} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hle
      rcases clusterA_mem i with h | h | h
      · exact clusterA_inj i i₀ (h.trans hi₀.symm)
      · rw [h] at hle; norm_num at hle
      · rw [h] at hle; norm_num at hle
    · intro h
      rw [h, hi₀]; norm_num
  obtain ⟨hs₀, hq₀⟩ :
      (∀ l : Fin 3, l ≠ 0 → eigvecOf clusterA clusterA_symm i₀ l = 0)
        ∧ eigvecOf clusterA clusterA_symm i₀ 0
          * eigvecOf clusterA clusterA_symm i₀ 0 = 1 :=
    eigvecOf_diagonal_at_entry' clusterA_symm i₀ 0 hi₀
      (by intro l hl; fin_cases l <;>
        first | exact absurd rfl hl | norm_num [clusterA])
  rw [spectralProjector, hfilter]
  ext a b
  simp only [Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp [hs₀, hq₀]

/-- **The singleton cluster pin:** `P_{{5}} = diag(0, 1, 0)` — capture
at sets to the window `(4, 6]`, the band agreement to the threshold
difference, both threshold projectors pinned. -/
theorem cpA_five :
    clusterProjector clusterA clusterA_symm ({5} : Set ℝ)
      = Matrix.diagonal ![0, 1, 0] := by
  have hcap : clusterProjector clusterA clusterA_symm ({5} : Set ℝ)
      = clusterProjector clusterA clusterA_symm (Set.Ioc 4 6) := by
    refine clusterProjector_eq_of_forall_mem_iff clusterA_symm _ _ ?_
    intro i
    constructor
    · intro hin
      rcases clusterA_mem i with h | h | h
      · rw [h] at hin; simp at hin
      · rw [h]; exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩
      · rw [h] at hin; simp at hin
    · intro hioc
      have ⟨hlo, hhi⟩ := Set.mem_Ioc.mp hioc
      rcases clusterA_mem i with h | h | h
      · rw [h] at hlo; norm_num at hlo
      · exact h
      · rw [h] at hhi; norm_num at hhi
  rw [hcap, clusterProjector_eq_bandProjector clusterA_symm 4 6
    (by norm_num), bandProjector, spClusterA_eq, spA_four]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.sub_apply, Matrix.diagonal_apply]

/-- **The non-interval pin:** `P_{{0, 11}} = diag(1, 0, 1)` — the
partition of the identity at `{0, 11}` with the complement captured to
`{5}`, where the singleton pin applies. A subspace no window expresses:
the two surviving modes straddle the killed middle mode. -/
theorem cpA_zeroEleven :
    clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      = Matrix.diagonal ![1, 0, 1] := by
  have hcompl : clusterProjector clusterA clusterA_symm
      (({0, 11} : Set ℝ)ᶜ)
      = clusterProjector clusterA clusterA_symm ({5} : Set ℝ) := by
    refine clusterProjector_eq_of_forall_mem_iff clusterA_symm _ _ ?_
    intro i
    constructor
    · intro hc
      rcases clusterA_mem i with h | h | h
      · rw [h] at hc; simp at hc
      · exact h
      · rw [h] at hc; simp at hc
    · intro h
      refine (Set.mem_compl_iff _ _).mpr ?_
      intro hin
      rcases clusterA_mem i with h' | h' | h'
      · rw [h'] at h; simp at h
      · rw [h'] at hin; simp at hin
      · rw [h'] at h; simp at h
  have hpart := clusterProjector_add_clusterProjector_compl
    clusterA_symm ({0, 11} : Set ℝ)
  rw [hcompl, cpA_five] at hpart
  rw [eq_sub_of_add_eq hpart]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]

/-- The upper cluster pin: `P_{{5, 11}} = diag(0, 1, 1)` (the fence's
B-side and the difference instance's `T`-side shape on `A`). -/
theorem cpA_fiveEleven :
    clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)
      = Matrix.diagonal ![0, 1, 1] := by
  have hcap : clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)
      = clusterProjector clusterA clusterA_symm (Set.Ioc 4 12) := by
    refine clusterProjector_eq_of_forall_mem_iff clusterA_symm _ _ ?_
    intro i
    constructor
    · intro hin
      rcases clusterA_mem i with h | h | h
      · rw [h] at hin; simp at hin
      · rw [h]; exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩
      · rw [h]; exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩
    · intro hioc
      have ⟨hlo, hhi⟩ := Set.mem_Ioc.mp hioc
      rcases clusterA_mem i with h | h | h
      · rw [h] at hlo; norm_num at hlo
      · exact Or.inl h
      · exact Or.inr h
  have hone : spectralProjector clusterA clusterA_symm 12 = 1 :=
    spectralProjector_eq_one clusterA clusterA_symm 12 (fun i => by
      rcases clusterA_mem i with h | h | h <;> rw [h] <;> norm_num)
  rw [hcap, clusterProjector_eq_bandProjector clusterA_symm 4 12
    (by norm_num), bandProjector, hone, spA_four]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]

/-- `B`'s cluster pin: `P_bm({5, 11}) = diag(0, 1, 1)` — the same
capture/agreement route at the second fixture. -/
theorem cpBm_T :
    clusterProjector bm bm_symm ({5, 11} : Set ℝ)
      = Matrix.diagonal ![0, 1, 1] := by
  have hcap : clusterProjector bm bm_symm ({5, 11} : Set ℝ)
      = clusterProjector bm bm_symm (Set.Ioc 4 12) := by
    refine clusterProjector_eq_of_forall_mem_iff bm_symm _ _ ?_
    intro i
    constructor
    · intro hin
      rcases bm_mem i with h | h | h
      · rw [h] at hin
        norm_num [Set.mem_insert, Set.mem_singleton] at hin
      · rw [h]; exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩
      · rw [h]; exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩
    · intro hioc
      have ⟨hlo, hhi⟩ := Set.mem_Ioc.mp hioc
      rcases bm_mem i with h | h | h
      · rw [h] at hlo; norm_num at hlo
      · exact Or.inl h
      · exact Or.inr h
  have hspfour : spectralProjector bm bm_symm 4
      = Matrix.diagonal ![1, 0, 0] := by
    obtain ⟨i₀, hi₀⟩ := bm_exists_neg
    have hfilter : (Finset.univ.filter
        fun i => eigvalOf bm bm_symm i ≤ 4) = {i₀} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro hle
        rcases bm_mem i with h | h | h
        · exact bm_inj i i₀ (h.trans hi₀.symm)
        · rw [h] at hle; norm_num at hle
        · rw [h] at hle; norm_num at hle
      · intro h
        rw [h, hi₀]; norm_num
    obtain ⟨hs₀, hq₀⟩ :
        (∀ l : Fin 3, l ≠ 0 → eigvecOf bm bm_symm i₀ l = 0)
          ∧ eigvecOf bm bm_symm i₀ 0
            * eigvecOf bm bm_symm i₀ 0 = 1 :=
      eigvecOf_diagonal_at_entry' bm_symm i₀ 0 hi₀
        (by intro l hl; fin_cases l <;>
          first | exact absurd rfl hl | norm_num [bm])
    rw [spectralProjector, hfilter]
    ext a b
    simp only [Matrix.of_apply]
    fin_cases a <;> fin_cases b <;> simp [hs₀, hq₀]
  have hone : spectralProjector bm bm_symm 12 = 1 :=
    spectralProjector_eq_one bm bm_symm 12 (fun i => by
      rcases bm_mem i with h | h | h <;> rw [h] <;> norm_num)
  rw [hcap, clusterProjector_eq_bandProjector bm_symm 4 12
    (by norm_num), bandProjector, hone, hspfour]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.sub_apply, Matrix.one_apply, Matrix.diagonal_apply]

/-! ### Interface witnesses on the pinned values -/

/-- Idempotence instantiated and pinned: `diag(1, 0, 1)² =
diag(1, 0, 1)`, computed through the delivered law and the entrywise
pin. -/
theorem cpA_zeroEleven_idem_QA :
    clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        * clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      = clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ) := by
  rw [clusterProjector_idempotent]

/-- In-cluster mode fixed: the theorem-level action at the `0`-mode's
own eigenvector. -/
theorem cpA_action_mem_QA :
    ∃ i : Fin 3, eigvalOf clusterA clusterA_symm i ∈ ({0, 11} : Set ℝ)
      ∧ clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
          *ᵥ eigvecOf clusterA clusterA_symm i
        = eigvecOf clusterA clusterA_symm i := by
  obtain ⟨i₀, hi₀⟩ := clusterA_exists_zero
  have hmem : eigvalOf clusterA clusterA_symm i₀ ∈ ({0, 11} : Set ℝ) := by
    rw [hi₀]; simp
  exact ⟨i₀, hmem,
    clusterProjector_mulVec_eigvecOf_self clusterA clusterA_symm
      ({0, 11} : Set ℝ) i₀ hmem⟩

/-- Out-of-cluster mode annihilated: the `5`-mode's eigenvector is
killed by the `{0, 11}` projector. -/
theorem cpA_action_not_mem_QA :
    ∃ i : Fin 3, eigvalOf clusterA clusterA_symm i ∉ ({0, 11} : Set ℝ)
      ∧ clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
          *ᵥ eigvecOf clusterA clusterA_symm i = 0 := by
  obtain ⟨i₅, hi₅⟩ := clusterA_exists_five
  refine ⟨i₅, ?_,
    clusterProjector_mulVec_eigvecOf_eq_zero clusterA clusterA_symm
      ({0, 11} : Set ℝ) i₅ ?_⟩
  · intro hin
    rw [hi₅] at hin; simp at hin
  · intro hin
    rw [hi₅] at hin; simp at hin

/-- The disjoint-set product law, numerically: `diag(0, 1, 0) *
diag(1, 0, 1) = 0` through the delivered law at the disjoint sets
`{5}` and `{0, 11}`. -/
theorem cpA_disjoint_QA :
    clusterProjector clusterA clusterA_symm ({5} : Set ℝ)
        * clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      = 0 := by
  rw [clusterProjector_mul_clusterProjector_eq_zero_of_disjoint
    clusterA clusterA_symm _ _
    (Set.disjoint_iff.mpr (by simp))]

/-- The rank counts (the trace route at the pinned values): rank 2, 2,
2, 1 — the checkable form of the theorem's equal-rank hypothesis. -/
theorem cpA_rank_zeroEleven :
    (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)).rank
      = 2 := by
  have h := trace_clusterProjector_eq_card clusterA_symm
    ({0, 11} : Set ℝ)
  rw [cpA_zeroEleven] at h
  rw [show (Matrix.diagonal (![1, 0, 1] : Fin 3 → ℝ)).trace = (2 : ℝ) by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_three]] at h
  rw [rank_clusterProjector_eq_card clusterA_symm _]
  exact_mod_cast h.symm

theorem cpA_rank_five :
    (clusterProjector clusterA clusterA_symm ({5} : Set ℝ)).rank = 1 := by
  have h := trace_clusterProjector_eq_card clusterA_symm ({5} : Set ℝ)
  rw [cpA_five] at h
  rw [show (Matrix.diagonal (![0, 1, 0] : Fin 3 → ℝ)).trace = (1 : ℝ) by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_three]] at h
  rw [rank_clusterProjector_eq_card clusterA_symm _]
  exact_mod_cast h.symm

theorem cpA_rank_fiveEleven :
    (clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)).rank
      = 2 := by
  have h := trace_clusterProjector_eq_card clusterA_symm
    ({5, 11} : Set ℝ)
  rw [cpA_fiveEleven] at h
  rw [show (Matrix.diagonal (![0, 1, 1] : Fin 3 → ℝ)).trace = (2 : ℝ) by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_three]] at h
  rw [rank_clusterProjector_eq_card clusterA_symm _]
  exact_mod_cast h.symm

theorem cpBm_rank_T :
    (clusterProjector bm bm_symm ({5, 11} : Set ℝ)).rank = 2 := by
  have h := trace_clusterProjector_eq_card bm_symm ({5, 11} : Set ℝ)
  rw [cpBm_T] at h
  rw [show (Matrix.diagonal (![0, 1, 1] : Fin 3 → ℝ)).trace = (2 : ℝ) by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_three]] at h
  rw [rank_clusterProjector_eq_card bm_symm _]
  exact_mod_cast h.symm

/-!
  ## Section 2: the non-interval difference instance

  `A = diag(0, 5, 11)` at `S = {0, 11}` vs `B = diag(-1, 5, 11)` at
  `T = {5, 11}`, at the exact-fit data `c = 11/2`, `r = 11/2`, `δ = 1`:
  both in-`S` eigenvalues at distance exactly `r` from `c`; the single
  out-of-`T` eigenvalue `-1` at distance exactly `r + δ`.
-/

/-- The perturbation norm: `A - B = diag(1, 0, 0)` has norm exactly
`≤ 1` (the max-abs-eigenvalue bridge at the diagonal difference). -/
theorem normABm_le : ‖clusterA - bm‖ ≤ 1 := by
  have hdef : clusterA - bm = Matrix.diagonal ![1, 0, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [clusterA, bm, Matrix.sub_apply, Matrix.diagonal_apply]
  have hsymm : (Matrix.diagonal (![1, 0, 0] : Fin 3 → ℝ)).IsSymm := by
    show _ᵀ = _
    rw [Matrix.diagonal_transpose]
  have hmem : ∀ i, eigvalOf (Matrix.diagonal ![1, 0, 0]) hsymm i = 1
      ∨ eigvalOf (Matrix.diagonal ![1, 0, 0]) hsymm i = 0 := by
    intro i
    have hk : ∃ k : Fin 3, eigvalOf (Matrix.diagonal ![1, 0, 0]) hsymm i
        = (![1, 0, 0] : Fin 3 → ℝ) k :=
      eigvalOf_diagonal_eq_entry' hsymm i
    obtain ⟨k, hk⟩ := hk
    fin_cases k <;> rw [hk] <;> simp
  rw [hdef, Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_eq_max_abs_evals
    hsymm (by norm_num)]
  have h0 : |evals hsymm ⟨0, by norm_num⟩| ≤ 1 := by
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf hsymm ⟨0, by norm_num⟩
    rw [hi]
    rcases hmem i with h | h <;> rw [h] <;> norm_num
  have h2 : |evals hsymm ⟨2, by norm_num⟩| ≤ 1 := by
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf hsymm ⟨2, by norm_num⟩
    rw [hi]
    rcases hmem i with h | h <;> rw [h] <;> norm_num
  exact max_le h0 h2

/-- **The non-interval difference instance, theorem route.** Both
separation families discharge at the exact-fit data; the bound reads
`≤ ‖A - B‖ / 1 ≤ 1`. -/
theorem cpQA_difference :
    ‖clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        - clusterProjector bm bm_symm ({5, 11} : Set ℝ)‖
      ≤ ‖clusterA - bm‖ / 1 := by
  refine l2OpNorm_clusterProjector_sub_clusterProjector_le
    clusterA_symm bm_symm _ _ (11 / 2) (11 / 2) 1
    (by norm_num) (by norm_num) ?_ ?_ ?_
  · rw [cpA_rank_zeroEleven, cpBm_rank_T]
  · intro i hin
    rcases clusterA_mem i with h | h | h
    · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
    · rw [h] at hin; simp at hin
    · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
  · intro j hjout
    rcases bm_mem j with h | h | h
    · rw [h]; exact le_abs.mpr (Or.inr (by norm_num))
    · rw [h] at hjout; simp at hjout
    · rw [h] at hjout; simp at hjout

/-- **The evaluated bound:** `≤ 1`. -/
theorem cpQA_difference_evaluated :
    ‖clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        - clusterProjector bm bm_symm ({5, 11} : Set ℝ)‖ ≤ 1 := by
  have h := cpQA_difference
  rw [div_one] at h
  exact h.trans normABm_le

/-- **The raw lower bound:** the difference is `diag(1, -1, 0)`
entrywise, and its action on `e₀` is `e₀` itself, so the norm is at
least `1` — computed completely independently of the theorem. -/
theorem cpQA_diff_raw :
    1 ≤ ‖clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        - clusterProjector bm bm_symm ({5, 11} : Set ℝ)‖ := by
  have hdiff : clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      - clusterProjector bm bm_symm ({5, 11} : Set ℝ)
      = Matrix.diagonal ![1, -1, 0] := by
    rw [cpA_zeroEleven, cpBm_T]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.sub_apply, Matrix.diagonal_apply]
  have hact : (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      - clusterProjector bm bm_symm ({5, 11} : Set ℝ)) *ᵥ
      (![1, 0, 0] : Fin 3 → ℝ) = ![1, 0, 0] := by
    rw [hdiff]
    funext a
    fin_cases a <;>
      norm_num [Matrix.mulVec, Matrix.dotProduct, Matrix.diagonal_apply]
  have h := l2OpNorm_mulVec_le
    (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      - clusterProjector bm bm_symm ({5, 11} : Set ℝ)) ![1, 0, 0]
  rw [hact] at h
  have hnorm : ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm
      (![1, 0, 0] : Fin 3 → ℝ)‖ = 1 := by
    rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
    have hdot : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ (![1, 0, 0] : Fin 3 → ℝ) = 1 := by
      simp [Matrix.dotProduct, Fin.sum_univ_three]
    rw [hdot, Real.sqrt_one]
  rw [hnorm] at h
  linarith

/-!
  ## Section 3: the ε = 0 attainment

  `A = B` at the singleton clusters `S = T = {5}`, `c = 5`, `r = 0`,
  `δ = 1/2` — the out-of-`T` separation genuinely discharged (the
  `0`- and `11`-modes at distances `5` and `6`).
-/

theorem cpQA_zeroE :
    ‖clusterProjector clusterA clusterA_symm ({5} : Set ℝ)
        - clusterProjector clusterA clusterA_symm ({5} : Set ℝ)‖
      ≤ ‖clusterA - clusterA‖ / (1 / 2) := by
  refine l2OpNorm_clusterProjector_sub_clusterProjector_le
    clusterA_symm clusterA_symm _ _ 5 0 (1 / 2)
    (by norm_num) (by norm_num) ?_ ?_ ?_
  · rw [cpA_rank_five]
  · intro i hin
    have h : eigvalOf clusterA clusterA_symm i = 5 := by
      rcases clusterA_mem i with h | h | h
      · rw [h] at hin; simp at hin
      · exact h
      · rw [h] at hin; simp at hin
    rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
  · intro j hjout
    rcases clusterA_mem j with h | h | h
    · rw [h]; exact le_abs.mpr (Or.inr (by norm_num))
    · rw [h] at hjout; simp at hjout
    · rw [h]; exact le_abs.mpr (Or.inl (by norm_num))

/-- The attainment: the conclusion reads `‖P - P‖ ≤ 0`, attained. -/
theorem cpQA_zeroE_attained :
    ‖clusterProjector clusterA clusterA_symm ({5} : Set ℝ)
        - clusterProjector clusterA clusterA_symm ({5} : Set ℝ)‖ = 0 := by
  rw [sub_self, norm_zero]

/-!
  ## Section 4: the fence — `hfar` isolated on the interior-gap
  configuration

  `A = B = diag(0, 5, 11)`, `S = {0, 11}`, `T = {5, 11}`, `c = 11/2`,
  `r = 11/2`, `δ = 1/2`: the out-of-`T` eigenvalue `0` sits *inside*
  A's cluster range at distance `11/2 < 11/2 + 1/2` from `c` — the
  configuration the proposal's recorded obstruction names, exercised
  as a hypothesis fence.
-/

/-- The raw lower bound on the fence's difference: same diagonal shape
as the difference instance, norm at least `1` at `e₀`. -/
theorem cpQA_fence_lower :
    1 ≤ ‖clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        - clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)‖ := by
  have hdiff : clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      - clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)
      = Matrix.diagonal ![1, -1, 0] := by
    rw [cpA_zeroEleven, cpA_fiveEleven]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.sub_apply, Matrix.diagonal_apply]
  have hact : (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      - clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)) *ᵥ
      (![1, 0, 0] : Fin 3 → ℝ) = ![1, 0, 0] := by
    rw [hdiff]
    funext a
    fin_cases a <;>
      norm_num [Matrix.mulVec, Matrix.dotProduct, Matrix.diagonal_apply]
  have h := l2OpNorm_mulVec_le
    (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      - clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ))
    ![1, 0, 0]
  rw [hact] at h
  have hnorm : ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm
      (![1, 0, 0] : Fin 3 → ℝ)‖ = 1 := by
    rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
    have hdot : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ (![1, 0, 0] : Fin 3 → ℝ) = 1 := by
      simp [Matrix.dotProduct, Fin.sum_univ_three]
    rw [hdot, Real.sqrt_one]
  rw [hnorm] at h
  linarith

/-- **The fence:** with `A = B` the hypothesis-free conclusion would
read `‖P - Q‖ ≤ 0`, refuted by the raw lower bound. -/
theorem cpQA_fence :
    ¬ (‖clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        - clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)‖
      ≤ ‖clusterA - clusterA‖ / (1 / 2)) := by
  intro hcon
  rw [sub_self, norm_zero, zero_div] at hcon
  have h := cpQA_fence_lower
  linarith

/-- `hfar` fails exactly at the interior-gap `0`-mode: its distance to
`c = 11/2` is `11/2`, strictly below `r + δ = 6`. -/
theorem cpQA_fence_hfar_fails :
    ¬ (∀ j, eigvalOf clusterA clusterA_symm j ∉ ({5, 11} : Set ℝ) →
        11 / 2 + 1 / 2 ≤ |eigvalOf clusterA clusterA_symm j - 11 / 2|) := by
  intro hcon
  obtain ⟨i₀, hi₀⟩ := clusterA_exists_zero
  have hout : eigvalOf clusterA clusterA_symm i₀ ∉ ({5, 11} : Set ℝ) := by
    intro hin
    rw [hi₀] at hin; simp at hin
  have h := hcon i₀ hout
  rw [hi₀] at h
  rw [show |(0 : ℝ) - 11 / 2| = 11 / 2 from by
      rw [abs_sub_comm]; norm_num] at h
  norm_num at h

/-- **`hfar` is the only failing hypothesis:** ranks equal (`2 = 2`
through the counts), `hnear` holds at the same data, `δ > 0`, and the
hypothesis-free conclusion is refuted — the separation exercised as a
fence, not decoration. -/
theorem cpQA_fence_only_hfar_fails :
    (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)).rank
        = (clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)).rank
      ∧ (∀ i, eigvalOf clusterA clusterA_symm i ∈ ({0, 11} : Set ℝ) →
          |eigvalOf clusterA clusterA_symm i - 11 / 2| ≤ 11 / 2)
      ∧ (0 < (1 / 2 : ℝ))
      ∧ ¬ (∀ j, eigvalOf clusterA clusterA_symm j ∉ ({5, 11} : Set ℝ) →
          11 / 2 + 1 / 2 ≤ |eigvalOf clusterA clusterA_symm j - 11 / 2|)
      ∧ ¬ (‖clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
          - clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)‖
        ≤ ‖clusterA - clusterA‖ / (1 / 2)) := by
  refine ⟨?_, ?_, by norm_num, cpQA_fence_hfar_fails, cpQA_fence⟩
  · rw [cpA_rank_zeroEleven, cpA_rank_fiveEleven]
  · intro i hin
    rcases clusterA_mem i with h | h | h
    · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
    · rw [h] at hin; simp at hin
    · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩

/-!
  ## Section 5: the two-sided (both-separations) rank-free form

  The set twin of the window symmetric theorem
  (`l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm`,
  `proposals/cluster-projector-symmetric.md`): constant 2, **no rank
  hypothesis anywhere**. The headline witness is *unequal-rank* —
  `S = {0, 5}` on `clusterA` (rank 2) vs `T = {5}` on `bm` (rank 1),
  the delivered equal-rank family's hypothesis exhibited failing — with
  the flank data `cS = 5/2`, `rS = 5/2`, `cT = 5`, `rT = 0`, `δ = 1/2`
  (the two-pair statement shape at work: the out-of-`S` eigenvalue
  `11` sits `6` from `cT` while `bm`'s out-of-`T` eigenvalues sit `7/2`
  and `17/2` from `cS` — no single center covers both flanks).
-/

/-- The two new threshold pins on `bm`, extracted for the singleton
cluster pin below: the `-1`-mode selection at `4`, and the two-mode
selection `{-1, 5}` at `6` (the `spClusterA_eq` pattern at the second
fixture). -/
theorem spBm_four :
    spectralProjector bm bm_symm 4
      = Matrix.diagonal ![1, 0, 0] := by
  obtain ⟨i₀, hi₀⟩ := bm_exists_neg
  have hfilter : (Finset.univ.filter
      fun i => eigvalOf bm bm_symm i ≤ 4) = {i₀} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · intro hle
      rcases bm_mem i with h | h | h
      · exact bm_inj i i₀ (h.trans hi₀.symm)
      · rw [h] at hle; norm_num at hle
      · rw [h] at hle; norm_num at hle
    · intro h
      rw [h, hi₀]; norm_num
  obtain ⟨hs₀, hq₀⟩ :
      (∀ l : Fin 3, l ≠ 0 → eigvecOf bm bm_symm i₀ l = 0)
        ∧ eigvecOf bm bm_symm i₀ 0
          * eigvecOf bm bm_symm i₀ 0 = 1 :=
    eigvecOf_diagonal_at_entry' bm_symm i₀ 0 hi₀
      (by intro l hl; fin_cases l <;>
        first | exact absurd rfl hl | norm_num [bm])
  rw [spectralProjector, hfilter]
  ext a b
  simp only [Matrix.of_apply]
  fin_cases a <;> fin_cases b <;> simp [hs₀, hq₀]

theorem bm_exists_five : ∃ i : Fin 3, eigvalOf bm bm_symm i = 5 := by
  by_contra hcon
  push_neg at hcon
  exact exists_eigvalOf_two_values' (x := -1) (y := 11)
    (fun i => by
      rcases bm_mem i with h | h | h
      · exact Or.inl h
      · exact absurd h (hcon i)
      · exact Or.inr h) bm_inj

theorem spBm_six :
    spectralProjector bm bm_symm 6
      = Matrix.diagonal ![1, 1, 0] := by
  obtain ⟨i₀, hi₀⟩ := bm_exists_neg
  obtain ⟨i₅, hi₅⟩ := bm_exists_five
  have hfilter : (Finset.univ.filter
      fun i => eigvalOf bm bm_symm i ≤ 6) = insert i₀ {i₅} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hle
      rcases bm_mem i with h | h | h
      · exact Or.inl (bm_inj i i₀ (h.trans hi₀.symm))
      · exact Or.inr (bm_inj i i₅ (h.trans hi₅.symm))
      · rw [h] at hle; norm_num at hle
    · intro h
      rcases h with h | h
      · rw [h, hi₀]; norm_num
      · rw [h, hi₅]; norm_num
  obtain ⟨hs₀, hq₀⟩ :
      (∀ l : Fin 3, l ≠ 0 → eigvecOf bm bm_symm i₀ l = 0)
        ∧ eigvecOf bm bm_symm i₀ 0
          * eigvecOf bm bm_symm i₀ 0 = 1 :=
    eigvecOf_diagonal_at_entry' bm_symm i₀ 0 hi₀
      (by intro l hl; fin_cases l <;>
        first | exact absurd rfl hl | norm_num [bm])
  obtain ⟨hs₅, hq₅⟩ :
      (∀ l : Fin 3, l ≠ 1 → eigvecOf bm bm_symm i₅ l = 0)
        ∧ eigvecOf bm bm_symm i₅ 1
          * eigvecOf bm bm_symm i₅ 1 = 1 :=
    eigvecOf_diagonal_at_entry' bm_symm i₅ 1 hi₅
      (by intro l hl; fin_cases l <;>
        first | exact absurd rfl hl | norm_num [bm])
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

/-- The lower two-mode cluster pin on `clusterA`:
`P_{ {0, 5} } = diag(1, 1, 0)` — capture to the window `(-1, 6]`, the
band agreement, and the already-exported `bandClusterA_eq`. A second
subspace no *single* window at a shared center could pair with `bm`'s
`{5}`-cluster under one center — the two-pair statement shape's
witness. -/
theorem cpA_zeroFive :
    clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
      = Matrix.diagonal ![1, 1, 0] := by
  have hcap : clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
      = clusterProjector clusterA clusterA_symm (Set.Ioc (-1) 6) := by
    refine clusterProjector_eq_of_forall_mem_iff clusterA_symm _ _ ?_
    intro i
    constructor
    · intro hin
      rcases clusterA_mem i with h | h | h
      · rw [h]; exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩
      · rw [h]; exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩
      · rw [h] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
    · intro hioc
      have ⟨hlo, hhi⟩ := Set.mem_Ioc.mp hioc
      rcases clusterA_mem i with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · rw [h] at hhi; norm_num at hhi
  rw [hcap, clusterProjector_eq_bandProjector clusterA_symm (-1) 6
    (by norm_num), bandClusterA_eq]

/-- The `bm` singleton cluster pin: `P_bm({5}) = diag(0, 1, 0)` —
capture to `(4, 6]`, the band agreement, and the two threshold pins
above. -/
theorem cpBm_five :
    clusterProjector bm bm_symm ({5} : Set ℝ)
      = Matrix.diagonal ![0, 1, 0] := by
  have hcap : clusterProjector bm bm_symm ({5} : Set ℝ)
      = clusterProjector bm bm_symm (Set.Ioc 4 6) := by
    refine clusterProjector_eq_of_forall_mem_iff bm_symm _ _ ?_
    intro i
    constructor
    · intro hin
      rcases bm_mem i with h | h | h
      · rw [h] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
      · rw [h]; exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩
      · rw [h] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
    · intro hioc
      have ⟨hlo, hhi⟩ := Set.mem_Ioc.mp hioc
      rcases bm_mem i with h | h | h
      · rw [h] at hlo; norm_num at hlo
      · exact h
      · rw [h] at hhi; norm_num at hhi
  rw [hcap, clusterProjector_eq_bandProjector bm_symm 4 6
    (by norm_num), bandProjector, spBm_six, spBm_four]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.sub_apply, Matrix.diagonal_apply]

/-- The witness's rank counts: `2` and `1` — the delivered equal-rank
difference family's hypothesis exhibited failing on the very fixture
the new rank-free theorem covers. -/
theorem cpA_rank_zeroFive :
    (clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)).rank
      = 2 := by
  have h := trace_clusterProjector_eq_card clusterA_symm
    ({0, 5} : Set ℝ)
  rw [cpA_zeroFive] at h
  rw [show (Matrix.diagonal (![1, 1, 0] : Fin 3 → ℝ)).trace = (2 : ℝ) by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_three]] at h
  rw [rank_clusterProjector_eq_card clusterA_symm _]
  exact_mod_cast h.symm

theorem cpBm_rank_five :
    (clusterProjector bm bm_symm ({5} : Set ℝ)).rank = 1 := by
  have h := trace_clusterProjector_eq_card bm_symm ({5} : Set ℝ)
  rw [cpBm_five] at h
  rw [show (Matrix.diagonal (![0, 1, 0] : Fin 3 → ℝ)).trace = (1 : ℝ) by
    norm_num [Matrix.trace_diagonal, Fin.sum_univ_three]] at h
  rw [rank_clusterProjector_eq_card bm_symm _]
  exact_mod_cast h.symm

theorem cpsQA_ranks_ne :
    (clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)).rank
      ≠ (clusterProjector bm bm_symm ({5} : Set ℝ)).rank := by
  rw [cpA_rank_zeroFive, cpBm_rank_five]
  norm_num

/-- **The unequal-rank witness, theorem route.** Both flank
separations discharged at the two-pair data `cS = 5/2`, `rS = 5/2`,
`cT = 5`, `rT = 0`, `δ = 1/2`: A's in-`S` eigenvalues `0`, `5` at
distance exactly `rS` from `cS`; `bm`'s out-of-`T` eigenvalues `-1`,
`11` at distances `7/2`, `17/2` from `cS`; `bm`'s in-`T` eigenvalue `5`
at distance exactly `rT` from `cT`; A's out-of-`S` eigenvalue `11` at
distance `6` from `cT`. -/
theorem cpsQA_two_sided :
    ‖clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
        - clusterProjector bm bm_symm ({5} : Set ℝ)‖
      ≤ 2 * ‖clusterA - bm‖ / (1 / 2) := by
  refine l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm
    clusterA_symm bm_symm _ _ (5 / 2) (5 / 2) 5 0 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · intro i hin
    rcases clusterA_mem i with h | h | h
    · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
    · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
    · rw [h] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
  · intro j hjout
    rcases bm_mem j with h | h | h
    · rw [h]; exact le_abs.mpr (Or.inr (by norm_num))
    · rw [h] at hjout; norm_num [Set.mem_insert, Set.mem_singleton] at hjout
    · rw [h]; exact le_abs.mpr (Or.inl (by norm_num))
  · intro j hin
    have h5 : eigvalOf bm bm_symm j = 5 := by
      rcases bm_mem j with h | h | h
      · rw [h] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
      · exact h
      · rw [h] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
    rw [h5]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
  · intro i hiout
    rcases clusterA_mem i with h | h | h
    · rw [h] at hiout; norm_num [Set.mem_insert, Set.mem_singleton] at hiout
    · rw [h] at hiout; norm_num [Set.mem_insert, Set.mem_singleton] at hiout
    · rw [h]; exact le_abs.mpr (Or.inl (by norm_num))

/-- **The evaluated bound:** `≤ 4`, through the imported
`normABm_le : ‖clusterA - bm‖ ≤ 1`. -/
theorem cpsQA_two_sided_evaluated :
    ‖clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
        - clusterProjector bm bm_symm ({5} : Set ℝ)‖ ≤ 4 := by
  have h := cpsQA_two_sided
  rw [show (2 : ℝ) * ‖clusterA - bm‖ / (1 / 2)
      = 2 * (2 * ‖clusterA - bm‖) by ring] at h
  have h2 := mul_le_mul_of_nonneg_left normABm_le
    (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- **The raw lower bound:** the difference is `diag(1, 0, 0)`
entrywise, its action on `e₀` is `e₀`, so the norm is at least `1` —
computed completely independently of the theorem. -/
theorem cpsQA_witness_raw :
    1 ≤ ‖clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
        - clusterProjector bm bm_symm ({5} : Set ℝ)‖ := by
  have hdiff : clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
      - clusterProjector bm bm_symm ({5} : Set ℝ)
      = Matrix.diagonal ![1, 0, 0] := by
    rw [cpA_zeroFive, cpBm_five]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.sub_apply, Matrix.diagonal_apply]
  have hact : (clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
      - clusterProjector bm bm_symm ({5} : Set ℝ)) *ᵥ
      (![1, 0, 0] : Fin 3 → ℝ) = ![1, 0, 0] := by
    rw [hdiff]
    funext a
    fin_cases a <;>
      norm_num [Matrix.mulVec, Matrix.dotProduct, Matrix.diagonal_apply]
  have h := l2OpNorm_mulVec_le
    (clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
      - clusterProjector bm bm_symm ({5} : Set ℝ)) ![1, 0, 0]
  rw [hact] at h
  have hnorm : ‖(WithLp.equiv 2 (Fin 3 → ℝ)).symm
      (![1, 0, 0] : Fin 3 → ℝ)‖ = 1 := by
    rw [Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.norm_euclidean_eq_sqrt]
    have hdot : (![1, 0, 0] : Fin 3 → ℝ) ⬝ᵥ (![1, 0, 0] : Fin 3 → ℝ) = 1 := by
      simp [Matrix.dotProduct, Fin.sum_univ_three]
    rw [hdot, Real.sqrt_one]
  rw [hnorm] at h
  linarith

/-- **The ε = 0 attainment through the new theorem:** at `S = T = {5}`
on `clusterA`, both flank separations genuinely discharged (the
out-of-cluster eigenvalues `0`, `11` at distances `5`, `6` from the
common center `5`, `δ = 1/2`), the conclusion reads
`≤ 2 * 0 / (1/2) = 0`. -/
theorem cpsQA_zeroE :
    ‖clusterProjector clusterA clusterA_symm ({5} : Set ℝ)
        - clusterProjector clusterA clusterA_symm ({5} : Set ℝ)‖
      ≤ 2 * ‖clusterA - clusterA‖ / (1 / 2) := by
  refine l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm
    clusterA_symm clusterA_symm _ _ 5 0 5 0 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) ?_ ?_ ?_ ?_
  · intro i hin
    have h5 : eigvalOf clusterA clusterA_symm i = 5 := by
      rcases clusterA_mem i with h | h | h
      · rw [h] at hin; simp at hin
      · exact h
      · rw [h] at hin; simp at hin
    rw [h5]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
  · intro j hjout
    rcases clusterA_mem j with h | h | h
    · rw [h]; exact le_abs.mpr (Or.inr (by norm_num))
    · rw [h] at hjout; simp at hjout
    · rw [h]; exact le_abs.mpr (Or.inl (by norm_num))
  · intro j hin
    have h5 : eigvalOf clusterA clusterA_symm j = 5 := by
      rcases clusterA_mem j with h | h | h
      · rw [h] at hin; simp at hin
      · exact h
      · rw [h] at hin; simp at hin
    rw [h5]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
  · intro i hiout
    rcases clusterA_mem i with h | h | h
    · rw [h]; exact le_abs.mpr (Or.inr (by norm_num))
    · rw [h] at hiout; simp at hiout
    · rw [h]; exact le_abs.mpr (Or.inl (by norm_num))

/-- The attainment: the conclusion reads `‖P - P‖ ≤ 0`, attained. -/
theorem cpsQA_zeroE_attained :
    ‖clusterProjector clusterA clusterA_symm ({5} : Set ℝ)
        - clusterProjector clusterA clusterA_symm ({5} : Set ℝ)‖ = 0 := by
  rw [sub_self, norm_zero]

/-!
  ### The two-sided fence — each separation flank isolated

  `A = B = diag(0, 5, 11)`, `S = {0, 11}`, `T = {5, 11}`, `cS = 11/2`,
  `rS = 11/2`, `cT = 8`, `rT = 3`, `δ = 1/2`: both `hnear` sides hold,
  and *each* `hfar` side fails at its own interior eigenvalue — the
  out-of-`T` eigenvalue `0` inside A's cluster range (the recorded
  obstruction configuration), and the out-of-`S` eigenvalue `5` inside
  B's cluster range. The two-sidedness itself is exercised: neither
  separation is decoration.
-/

theorem cpsQA_fence_hnearT :
    ∀ j, eigvalOf clusterA clusterA_symm j ∈ ({5, 11} : Set ℝ) →
      |eigvalOf clusterA clusterA_symm j - 8| ≤ 3 := by
  intro j hin
  rcases clusterA_mem j with h | h | h
  · rw [h] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
  · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
  · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩

/-- `hfarS` fails at the interior-gap `5`-mode: its distance to
`cT = 8` is `3`, strictly below `rT + δ = 7/2`. -/
theorem cpsQA_fence_hfarS_fails :
    ¬ (∀ i, eigvalOf clusterA clusterA_symm i ∉ ({0, 11} : Set ℝ) →
        3 + 1 / 2 ≤ |eigvalOf clusterA clusterA_symm i - 8|) := by
  intro hcon
  obtain ⟨i₅, hi₅⟩ := clusterA_exists_five
  have hout : eigvalOf clusterA clusterA_symm i₅ ∉ ({0, 11} : Set ℝ) := by
    intro hin
    rw [hi₅] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
  have h := hcon i₅ hout
  rw [hi₅] at h
  rw [show |(5 : ℝ) - 8| = 3 from by rw [abs_sub_comm]; norm_num] at h
  norm_num at h

/-- **The fence:** with `A = B` the hypothesis-free conclusion would
read `≤ 0`, refuted by the imported raw lower bound (norm at least
`1` at `e₀`). -/
theorem cpsQA_fence :
    ¬ (‖clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        - clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)‖
      ≤ 2 * ‖clusterA - clusterA‖ / (1 / 2)) := by
  intro hcon
  have h0 : ‖clusterA - clusterA‖ = 0 := by
    rw [sub_self, norm_zero]
  rw [h0] at hcon
  have hrhs : (2 : ℝ) * 0 / (1 / 2) = 0 := by norm_num
  rw [hrhs] at hcon
  have h := cpQA_fence_lower
  linarith

/-- **Both `hnear` sides hold and both `hfar` sides fail** — the
isolation: the two separation flanks are the only failing hypotheses,
and the hypothesis-free conclusion is refuted with them verified. -/
theorem cpsQA_fence_both_hfars_fail :
    (∀ i, eigvalOf clusterA clusterA_symm i ∈ ({0, 11} : Set ℝ) →
        |eigvalOf clusterA clusterA_symm i - 11 / 2| ≤ 11 / 2)
      ∧ (∀ j, eigvalOf clusterA clusterA_symm j ∈ ({5, 11} : Set ℝ) →
          |eigvalOf clusterA clusterA_symm j - 8| ≤ 3)
      ∧ (0 < (1 / 2 : ℝ))
      ∧ ¬ (∀ j, eigvalOf clusterA clusterA_symm j ∉ ({5, 11} : Set ℝ) →
          11 / 2 + 1 / 2
            ≤ |eigvalOf clusterA clusterA_symm j - 11 / 2|)
      ∧ ¬ (∀ i, eigvalOf clusterA clusterA_symm i ∉ ({0, 11} : Set ℝ) →
          3 + 1 / 2 ≤ |eigvalOf clusterA clusterA_symm i - 8|)
      ∧ ¬ (‖clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
          - clusterProjector clusterA clusterA_symm ({5, 11} : Set ℝ)‖
        ≤ 2 * ‖clusterA - clusterA‖ / (1 / 2)) := by
  refine ⟨?_, cpsQA_fence_hnearT, by norm_num, cpQA_fence_hfar_fails,
    cpsQA_fence_hfarS_fails, cpsQA_fence⟩
  intro i hin
  rcases clusterA_mem i with h | h | h
  · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩
  · rw [h] at hin; norm_num [Set.mem_insert, Set.mem_singleton] at hin
  · rw [h]; exact abs_le.mpr ⟨by norm_num, by norm_num⟩

/-- **The ring-identity coherence witness:** on the pinned witness
projectors, `(1 - Q) * P - Q * (1 - P) = P - Q` entrywise — the
composition's identity exhibited numerically, independent of the
module's private lemma. Both one-sided products are computed from the
pins: `(1 - Q) * P = diag(1, 0, 0)` and `Q * (1 - P) = 0`. -/
theorem cpsQA_ring_QA :
    (1 - clusterProjector bm bm_symm ({5} : Set ℝ))
        * clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
        - clusterProjector bm bm_symm ({5} : Set ℝ)
          * (1 - clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ))
      = clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ)
        - clusterProjector bm bm_symm ({5} : Set ℝ) := by
  rw [cpA_zeroFive, cpBm_five]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, Fin.sum_univ_three]

/-! ## ClusterFences: the adversarial fence audit (proposal
`adversarial-fences-band-projector-family.md`, 2026-09-04)

Every load-bearing hypothesis clause of `ClusterProjector.lean`'s
theorem surface with no negative witness anywhere in the repository,
fenced in hypothesis form at the pinned fixture `clusterA =
diag(0,5,11)`. QA-only, no axiom contact. -/

section ClusterFences

/-- No eigenvector of the fixture is the zero vector (unit norm) — the
companion every action fence routes through. -/
theorem cfF_eigvec_ne_zero (i : Fin 3) :
    eigvecOf clusterA clusterA_symm i ≠ 0 := by
  intro hz
  have hnorm := eigvecOf_inner clusterA clusterA_symm i i
  rw [if_pos rfl, hz] at hnorm
  simp at hnorm

/-- **Fence (`clusterProjector_mulVec_eigvecOf_self`, `h : λ i ∈ S`)**:
at `S = {0, 11}` the eigenvalue-`5` mode is annihilated, not fixed. -/
theorem cfF_self_h_fence :
    ¬ (∀ i : Fin 3, clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        *ᵥ eigvecOf clusterA clusterA_symm i
          = eigvecOf clusterA clusterA_symm i) := by
  intro h
  obtain ⟨i₅, hi₅⟩ := clusterA_exists_five
  have hkill : clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      *ᵥ eigvecOf clusterA clusterA_symm i₅ = 0 :=
    clusterProjector_mulVec_eigvecOf_eq_zero clusterA clusterA_symm _ i₅
      (by intro hin
          rw [hi₅] at hin
          simp at hin)
  have hfix := h i₅
  rw [hkill] at hfix
  exact cfF_eigvec_ne_zero i₅ hfix.symm

/-- **Fence (`clusterProjector_mulVec_eigvecOf_eq_zero`,
`h : λ i ∉ S`)**: at `S = {0, 11}` the eigenvalue-`0` mode is fixed,
not annihilated. -/
theorem cfF_zero_h_fence :
    ¬ (∀ i : Fin 3, clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        *ᵥ eigvecOf clusterA clusterA_symm i = 0) := by
  intro h
  obtain ⟨i₀, hi₀⟩ := clusterA_exists_zero
  have hfix : clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
      *ᵥ eigvecOf clusterA clusterA_symm i₀
        = eigvecOf clusterA clusterA_symm i₀ :=
    clusterProjector_mulVec_eigvecOf_self clusterA clusterA_symm _ i₀
      (by rw [hi₀]; simp)
  have hkill := h i₀
  rw [hfix] at hkill
  exact cfF_eigvec_ne_zero i₀ hkill

/-- **Fence (`clusterProjector_eq_zero_of_forall_not_mem`, `h`)**: a
set genuinely selecting eigenvalues gives a nonzero projector — the
pinned `diag(1,0,1)` (entry `(0,0)` is `1 ≠ 0`). -/
theorem cfF_eqZeroNotMem_h_fence :
    ¬ (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ) = 0) := by
  rw [cpA_zeroEleven]
  intro h
  have e := congrFun (congrFun h 0) 0
  simp at e

/-- **Fence (`clusterProjector_eq_one_of_forall_mem`, `h`)**: a set
missing an eigenvalue is not the identity — the pinned `diag(1,1,0)`
(entry `(2,2)` is `0 ≠ 1`). -/
theorem cfF_eqOneMem_h_fence :
    ¬ (clusterProjector clusterA clusterA_symm ({0, 5} : Set ℝ) = 1) := by
  rw [cpA_zeroFive]
  intro h
  have e := congrFun (congrFun h 2) 2
  simp at e

/-- **Fence (`clusterProjector_mul_clusterProjector_eq_zero_of_disjoint`,
`hST`)**: identical clusters are as far from disjoint as possible, and
`P² = P = diag(1,0,1) ≠ 0`. -/
theorem cfF_disjoint_hST_fence :
    ¬ (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        * clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ) = 0) := by
  rw [clusterProjector_idempotent, cpA_zeroEleven]
  intro h
  have e := congrFun (congrFun h 0) 0
  simp at e

/-- **Fence (`clusterProjector_eq_of_forall_mem_iff`, `hiff`)**: sets
selecting different eigenvalue classes give different projectors —
`diag(1,0,1)` (missing the `5` mode) against the covering selection's
identity (entry `(1,1)`: `0 ≠ 1`). -/
theorem cfF_iff_hiff_fence :
    ¬ (clusterProjector clusterA clusterA_symm ({0, 11} : Set ℝ)
        = clusterProjector clusterA clusterA_symm (Set.Ioc (-1) 12)) := by
  rw [cpA_zeroEleven,
    clusterProjector_eq_one_of_forall_mem clusterA_symm _
      (fun i => by
        rcases clusterA_mem i with h | h | h <;> rw [h] <;>
          exact Set.mem_Ioc.mpr ⟨by norm_num, by norm_num⟩)]
  intro h
  have e := congrFun (congrFun h 1) 1
  simp at e

/-- **Isolation (the band-agreement `hab` fence):** the dropped clause
genuinely fails — `6 ≤ −1` is false. -/
theorem cfF_bandAgree_hab_isolation : ¬ ((6 : ℝ) ≤ (-1 : ℝ)) := by norm_num

/-- **Fence (`clusterProjector_eq_bandProjector`, `hab : a ≤ b`)**: the
docstring's own corner, realized — `Set.Ioc 6 (−1)` is empty so the
cluster side is `0`, while the negated band is
`P_{−1} − P_6 = −diag(1,1,0) ≠ 0` (both threshold pins delivered). -/
theorem cfF_bandAgree_hab_fence :
    ¬ (clusterProjector clusterA clusterA_symm (Set.Ioc 6 (-1))
        = bandProjector clusterA clusterA_symm 6 (-1)) := by
  have hempty : ∀ i : Fin 3,
      eigvalOf clusterA clusterA_symm i ∉ Set.Ioc 6 (-1) := by
    intro i hmem
    rw [Set.mem_Ioc] at hmem
    linarith
  have hband : bandProjector clusterA clusterA_symm 6 (-1)
      = -(Matrix.diagonal ![1, 1, 0]) := by
    rw [bandProjector, spClusterA_eq,
      spectralProjector_eq_zero clusterA clusterA_symm (-1)
        (fun i => by
          rcases clusterA_mem i with h | h | h
          · norm_num [h]
          · norm_num [h]
          · norm_num [h]),
      zero_sub]
  rw [clusterProjector_eq_zero_of_forall_not_mem clusterA_symm _ hempty,
    hband]
  intro h
  have e := congrFun (congrFun h 0) 0
  simp at e

end ClusterFences

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
