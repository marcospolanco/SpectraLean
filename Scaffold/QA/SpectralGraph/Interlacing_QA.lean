/-
  Interlacing_QA.lean

  Purpose
  -------
  QA lemmas for the interlacing interface of
  `Scaffold.Mathlib.GraphTheory.Spectral`: principal submatrix
  extraction and symmetry, and perturbation-matrix structure in the
  ℓ² operator norm.

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Analysis.CStarAlgebra.Matrix

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Principal submatrices
-/

/-- Entries of the principal submatrix are entries of the ambient
matrix. -/
theorem principal_submatrix_entries_QA (M : Matrix V V ℝ)
    (S : Finset V) (a b : ↥S) :
    M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V)) a b
      = M (a : V) (b : V) := by
  rfl

/-- The principal submatrix of a symmetric matrix is symmetric. -/
theorem principal_submatrix_preserves_symmetry_QA (M : Matrix V V ℝ)
    (hM : M.IsSymm) (S : Finset V) :
    (M.submatrix (fun i : ↥S => (i : V)) (fun i : ↥S => (i : V))).IsSymm :=
  principalSubmatrix_symmetric M hM S

/-!
## Perturbation structure
-/

/-- The difference of symmetric matrices is symmetric. -/
theorem symmetric_difference_is_symmetric_QA (M N : Matrix V V ℝ)
    (hM : M.IsSymm) (hN : N.IsSymm) :
    (M - N).IsSymm :=
  hM.sub hN

/-- Zero perturbation has zero operator norm. -/
theorem zero_perturbation_zero_norm_QA (M : Matrix V V ℝ) :
    ‖M - M‖ = 0 := by
  rw [sub_self, norm_zero]

/-- The operator norm satisfies the triangle inequality. -/
theorem norm_triangle_QA (M N P : Matrix V V ℝ) :
    ‖M - P‖ ≤ ‖M - N‖ + ‖N - P‖ := by
  have h : M - P = (M - N) + (N - P) := by
    ext a b
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  rw [h]
  exact norm_add_le _ _

/-!
## The interlacing window, pinned to its values on `K₂`

The two-vertex Laplacian `L = [[1, -1], [-1, 1]]` has spectrum `[0, 2]`,
pinned from trace and determinant exactly as in `Cheeger_QA`.lean
(`eigvalOf_sum_eq_trace`, `det_eq_prod_eigenvalues`, sortedness — no
spectral-theorem computation). Its principal submatrix on the singleton
`{0}` is the `1 × 1` matrix `[1]` with spectrum `[1]`. Interlacing
therefore instantiates to the strict window `0 ≤ 1 ≤ 2`, and the
collapsed one-sided bounds are refuted in proved form: the window is
genuinely two-sided.
-/

section EdgeWindow

private def edgeLap : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

private theorem edgeLap_symm : edgeLap.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [Matrix.transpose_apply, edgeLap]
  fin_cases i <;> fin_cases j <;> rfl

private theorem edgeLap_trace : edgeLap.trace = 2 := by
  norm_num [Matrix.trace, edgeLap]

private theorem edgeLap_det : edgeLap.det = 0 := by
  rw [show edgeLap = !![1, -1; -1, 1] from rfl, Matrix.det_fin_two]
  norm_num

/-- A length-two list is the list of its two entries. -/
private theorem list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- Two-point spectrum pinning for the `K₂` Laplacian: a sorted
length-two list with sum `2` and product `0` is `[0, 2]`. -/
private theorem two_point_pin_edge {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = 2)
    (hprod : l.prod = 0) :
    l.get ⟨0, by omega⟩ = 0 ∧ l.get ⟨1, by omega⟩ = 2 := by
  obtain ⟨g₀, g₁, hg⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, list_two_eq h2⟩
  subst hg
  have hlt : (0 : Fin 2) < (1 : Fin 2) := by decide
  have hmono : g₀ ≤ g₁ := hs.rel_get_of_lt hlt
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with h0 | h1
  · refine ⟨h0, ?_⟩
    show g₁ = 2
    linarith
  · exfalso
    rw [h1] at hsum
    linarith

/-- A length-one list's single entry is its sum. -/
private theorem one_point_pin {l : List ℝ} (h1 : l.length = 1) :
    l.get ⟨0, by rw [h1]; omega⟩ = l.sum := by
  obtain ⟨a, rfl⟩ : ∃ a : ℝ, l = [a] := by
    cases l with
    | nil => simp at h1
    | cons x xs =>
      cases xs with
      | nil => exact ⟨x, rfl⟩
      | cons y ys => simp at h1
  rw [List.sum_cons, List.sum_nil, add_zero]
  rfl

/-- The sorted spectrum of the `K₂` Laplacian is `[0, 2]`, computed from
trace and determinant only. -/
theorem edgeLap_evals :
    evals edgeLap_symm ⟨0, by simp⟩ = 0 ∧
      evals edgeLap_symm ⟨1, by simp⟩ = 2 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm edgeLap_symm).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm edgeLap_symm).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm edgeLap_symm).eigenvalues))).sum = 2 := by
    have htr : ∑ i : Fin 2, eigvalOf edgeLap edgeLap_symm i = 2 := by
      rw [eigvalOf_sum_eq_trace, edgeLap_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm edgeLap_symm).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2,
        ((isHermitian_of_isSymm edgeLap_symm).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm edgeLap_symm).det_eq_prod_eigenvalues
      rw [edgeLap_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact two_point_pin_edge hlen hsorted hsum hprod

/-- The vertex subset carrying the principal submatrix: the singleton
`{0}`. -/
private def S0 : Finset (Fin 2) := {0}

private theorem card_S0 : Fintype.card ↥S0 = 1 := by
  rw [Fintype.card_coe]; simp [S0]

/-- Every element of `↥S0` is the vertex `0`. -/
private theorem S0_eq_zero (i : ↥S0) : (i : Fin 2) = 0 :=
  Finset.mem_singleton.1 i.2

/-- The spectrum of the `1 × 1` principal submatrix `[1]`: a length-one
sorted list equals its sum, which is the trace, which is the single
diagonal entry `L 0 0 = 1`. -/
theorem edgeLap_sub_evals_eq_one :
    evals (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)
      ⟨0, by simp [S0]⟩ = 1 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset ↥S0).val.map
        ((isHermitian_of_isSymm
          (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)).eigenvalues))).length = 1 := by
    rw [Multiset.length_sort, Multiset.card_map]
    simp [S0]
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset ↥S0).val.map
        ((isHermitian_of_isSymm
          (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)).eigenvalues))).sum = 1 := by
    have htr : ∑ i : ↥S0, eigvalOf _
        (principalSubmatrix_symmetric edgeLap edgeLap_symm S0) i = 1 := by
      rw [eigvalOf_sum_eq_trace]
      simp only [Matrix.trace, Matrix.diag]
      rw [Fintype.sum_eq_single (⟨0, by simp [S0]⟩ : ↥S0)]
      · rfl
      · intro b hb
        exact absurd (Subtype.ext (S0_eq_zero b)) hb
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  exact (one_point_pin hlen).trans hsum

/-- **Interlacing instantiated to its values on `K₂`**: the theorem's
window is `0 ≤ 1 ≤ 2`, with all three spectral values computed
independently of the theorem (trace/determinant pinning). A mis-stated
spectral side cannot pass this check. -/
theorem interlacing_edge_window_QA :
    (0 : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ 2 := by
  obtain ⟨hlo, hhi⟩ := eigen_interlacing_principal_submatrix edgeLap
    edgeLap_symm S0 ⟨0, by simp [S0]⟩
      (by simp only [card_S0, Fintype.card_fin]; omega)
  obtain ⟨he0, he2⟩ := edgeLap_evals
  have hsub := edgeLap_sub_evals_eq_one
  refine ⟨?_, ?_⟩
  · calc (0 : ℝ) = evals edgeLap_symm ⟨0, by simp⟩ := he0.symm
      _ ≤ evals (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)
            ⟨0, by simp [S0]⟩ := hlo
      _ = 1 := hsub
  · calc (1 : ℝ) = evals (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)
            ⟨0, by simp [S0]⟩ := hsub.symm
      _ ≤ evals edgeLap_symm ⟨1, by simp⟩ := hhi
      _ = 2 := he2

/-- The window is genuinely two-sided at this fixture: the collapsed
bounds `μ₀ ≤ λ₀` and `λ₁ ≤ μ₀` are both false in proved form (the
submatrix eigenvalue `1` sits strictly inside `[0, 2]`). This is the
negative witness for the window shape itself. -/
theorem interlacing_edge_window_strict_QA :
    ¬ (evals (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)
          ⟨0, by simp [S0]⟩ ≤
        evals edgeLap_symm ⟨0, by simp⟩) ∧
    ¬ (evals edgeLap_symm ⟨1, by simp⟩ ≤
        evals (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)
          ⟨0, by simp [S0]⟩) := by
  obtain ⟨he0, he2⟩ := edgeLap_evals
  have hsub := edgeLap_sub_evals_eq_one
  constructor
  · intro h
    have h10 : (1 : ℝ) ≤ 0 :=
      calc (1 : ℝ) = evals (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)
              ⟨0, by simp [S0]⟩ := hsub.symm
        _ ≤ evals edgeLap_symm ⟨0, by simp⟩ := h
        _ = 0 := he0
    norm_num at h10
  · intro h
    have h21 : (2 : ℝ) ≤ 1 :=
      calc (2 : ℝ) = evals edgeLap_symm ⟨1, by simp⟩ := he2.symm
        _ ≤ evals (principalSubmatrix_symmetric edgeLap edgeLap_symm S0)
              ⟨0, by simp [S0]⟩ := h
        _ = 1 := hsub
    norm_num at h21

end EdgeWindow

end SpectralGraphTheory.QA
