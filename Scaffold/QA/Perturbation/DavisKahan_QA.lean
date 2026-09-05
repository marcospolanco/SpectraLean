/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan
import Scaffold.QA.Perturbation.Weyl_QA

/-!
# QA for the Davis–Kahan interface

Zero-perturbation instance of `davis_kahan_sin_theta`: with `E = 0` the
projector bound collapses to `‖P - P‖ ≤ 0`, checking the projector
indexing, separation direction, and ℓ² operator norm of the interface.
These are real Lean proofs deriving consequences from the theorem (now
proved, retired from axiom 2026-08-21); they are interface witnesses,
not proofs of the statement.

The **strict non-vacuity witness** (`davis_kahan_rotation_bound_QA`,
`davis_kahan_rotation_strict_QA`): a genuinely rotated projector at a
nonzero perturbation, `A = diag(0, 2)` perturbed by
`E = [[0, 3/4], [3/4, 0]]`, with `Ã = A + E` having the pinned spectrum
`[-1/4, 9/4]` (trace/determinant/sortedness), separation `δ = 9/4`, and
`‖E‖ = 3/4` (pinned spectrum through the proved operator-norm bridge).
The bound instance then reads `‖Q - P‖ ≤ 1/3` while the exact distance
is pinned to `1/√10 < 1/3` — the fixture exercises the theorem's no-tie
(the Duhamel) branch, and both sides are computed from the raw fixture,
independent of the theorem under test.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Zero perturbation: with an explicitly separated spectrum, the
projector bound collapses to `‖P_{A+0} - P_A‖ ≤ 0 / δ = 0`. Exercises
the theorem's projector indexing, separation direction, and ℓ² operator
norm at `E = 0`; the pairwise separation hypothesis is reduced to the
binding single-pair form through `evals_sorted`. -/
theorem davis_kahan_zero_perturbation_QA (A : Matrix V V ℝ) (hA : A.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin (Fintype.card V), (i : ℕ) ≤ (k : ℕ) → (k : ℕ) < (j : ℕ) →
      δ ≤ evals hA j - evals hA i) :
    ‖initialProjector (A + 0) (show (A + 0).IsSymm by rw [add_zero]; exact hA) k
        - initialProjector A hA k‖
      ≤ ‖(0 : Matrix V V ℝ)‖ / δ := by
  have hAE : (A + 0).IsSymm := by rw [add_zero]; exact hA
  have hevals : ∀ i, evals hAE i = evals hA i := fun i => by
    have h := weyl_inequality A 0 hA zero_isSymm_QA i
    rw [norm_zero] at h
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
  refine davis_kahan_sin_theta A 0 hA hAE k hk δ hδ ?_
  rw [hevals ⟨(k : ℕ) + 1, hk⟩]
  exact hsep ⟨(k : ℕ), k.isLt⟩ ⟨(k : ℕ) + 1, hk⟩ (le_refl _) (Nat.lt_succ_self _)

/-!
## The rotation fixture

`dkA = diag(0, 2)` (spectrum `[0, 2]`), `dkE = [[0, 3/4], [3/4, 0]]`
(spectrum `[-3/4, 3/4]`, norm `3/4`), so `dkA + dkE` has spectrum
`[-1/4, 9/4]`. Every value is pinned from trace, determinant, and
sortedness, independent of the theorem under test. The eigenvector
*directions* are computed from the eigen equations (one-dimensional
eigenspaces), so no control over Mathlib's classical choice of basis is
needed — the outer products are choice-independent.
-/

section RotationFixture

private theorem list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- Two-point spectrum pinning at target roots: a sorted length-two
list with sum `lo + hi` and product `lo * hi` is `[lo, hi]` whenever
`lo ≤ hi`. -/
private theorem two_point_pin_of_sum_prod {l : List ℝ} {lo hi : ℝ}
    (hlo : lo ≤ hi) (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b))
    (hsum : l.sum = lo + hi) (hprod : l.prod = lo * hi) :
    l.get ⟨0, by omega⟩ = lo ∧ l.get ⟨1, by omega⟩ = hi := by
  obtain ⟨g₀, g₁, hg⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, list_two_eq h2⟩
  subst hg
  have hmono : g₀ ≤ g₁ := by
    have h := hs.rel_get_of_lt (show (0 : Fin 2) < 1 by decide)
    simpa using h
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  have hsq : (g₁ - g₀) ^ 2 = (hi - lo) ^ 2 := by
    have e1 : (g₁ - g₀) ^ 2 = (g₀ + g₁) ^ 2 - 4 * (g₀ * g₁) := by ring
    have e2 : (hi - lo) ^ 2 = (lo + hi) ^ 2 - 4 * (lo * hi) := by ring
    rw [hsum, hprod] at e1
    rw [e1, e2]
  have hd : g₁ - g₀ = hi - lo := by
    have hexp : (g₁ - g₀ - (hi - lo)) * (g₁ - g₀ + (hi - lo)) = 0 := by
      have hfac : (g₁ - g₀ - (hi - lo)) * (g₁ - g₀ + (hi - lo))
          = (g₁ - g₀) ^ 2 - (hi - lo) ^ 2 := by ring
      rw [hfac, hsq]
      ring
    rcases mul_eq_zero.1 hexp with h' | h'
    · linarith
    · have hA : 0 ≤ g₁ - g₀ := by linarith
      have hB : 0 ≤ hi - lo := by linarith
      nlinarith
  show g₀ = lo ∧ g₁ = hi
  exact ⟨by linarith, by linarith⟩

/-- The unperturbed fixture `diag(0, 2)`. -/
def dkA : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 2]

theorem dkA_symmetric : dkA.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, dkA]

theorem dkA_trace : dkA.trace = 2 := by
  simp [Matrix.trace, dkA]

theorem dkA_det : dkA.det = 0 := by
  have h00 : dkA 0 0 = 0 := by simp [dkA]
  have h11 : dkA 1 1 = 2 := by simp [dkA]
  have h01 : dkA 0 1 = 0 := by simp [dkA]
  have h10 : dkA 1 0 = 0 := by simp [dkA]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

/-- The sorted spectrum of `dkA` is exactly `[0, 2]`. -/
theorem dkA_evals_pin :
    evals dkA_symmetric ⟨0, by simp⟩ = 0 ∧
      evals dkA_symmetric ⟨1, by simp⟩ = 2 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkA_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkA_symmetric).eigenvalues))).Sorted
      (fun a b => a ≤ b) := Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkA_symmetric).eigenvalues))).sum = 0 + 2 := by
    have htr : ∑ i : Fin 2, eigvalOf dkA dkA_symmetric i = 0 + 2 := by
      rw [eigvalOf_sum_eq_trace, dkA_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkA_symmetric).eigenvalues))).prod = 0 * 2 := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm dkA_symmetric).eigenvalues i) = 0 := by
      have h := (isHermitian_of_isSymm dkA_symmetric).det_eq_prod_eigenvalues
      rw [dkA_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := 0) (hi := 2) (by norm_num)
    hlen hsorted hsum hprod

/-- The perturbation fixture. -/
noncomputable def dkE : Matrix (Fin 2) (Fin 2) ℝ := !![0, 3/4; 3/4, 0]

theorem dkE_symmetric : dkE.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, dkE]

theorem dkE_trace : dkE.trace = 0 := by
  simp [Matrix.trace, dkE]

theorem dkE_det : dkE.det = -9/16 := by
  have h00 : dkE 0 0 = 0 := by simp [dkE]
  have h11 : dkE 1 1 = 0 := by simp [dkE]
  have h01 : dkE 0 1 = 3/4 := by simp [dkE]
  have h10 : dkE 1 0 = 3/4 := by simp [dkE]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

/-- The sorted spectrum of `dkE` is exactly `[-3/4, 3/4]`. -/
theorem dkE_evals_pin :
    evals dkE_symmetric ⟨0, by simp⟩ = -3/4 ∧
      evals dkE_symmetric ⟨1, by simp⟩ = 3/4 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkE_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkE_symmetric).eigenvalues))).Sorted
      (fun a b => a ≤ b) := Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkE_symmetric).eigenvalues))).sum
      = -3/4 + 3/4 := by
    have htr : ∑ i : Fin 2, eigvalOf dkE dkE_symmetric i = -3/4 + 3/4 := by
      rw [eigvalOf_sum_eq_trace, dkE_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkE_symmetric).eigenvalues))).prod
      = -3/4 * (3/4) := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm dkE_symmetric).eigenvalues i) = -9/16 := by
      have h := (isHermitian_of_isSymm dkE_symmetric).det_eq_prod_eigenvalues
      rw [dkE_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := -3/4) (hi := 3/4) (by norm_num)
    hlen hsorted hsum hprod

/-- The perturbation norm `‖dkE‖ = 3/4` — the top of the pinned
spectrum, through the proved operator-norm bridge. -/
theorem dkE_norm : ‖dkE‖ = 3/4 := by
  rw [Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_eq_max_abs_evals
    dkE_symmetric (by norm_num)]
  have h0 : evals dkE_symmetric ⟨0, by simp⟩ = -3/4 := dkE_evals_pin.1
  have hlast : evals dkE_symmetric ⟨Fintype.card (Fin 2) - 1, by simp⟩ = 3/4 := by
    show evals dkE_symmetric ⟨1, by simp⟩ = 3/4
    exact dkE_evals_pin.2
  rw [h0, hlast]
  norm_num

theorem dkAE_symmetric : (dkA + dkE).IsSymm :=
  dkA_symmetric.add dkE_symmetric

theorem dkAE_trace : (dkA + dkE).trace = 2 := by
  simp [Matrix.trace, dkA, dkE]

theorem dkAE_det : (dkA + dkE).det = -9/16 := by
  have h00 : (dkA + dkE) 0 0 = 0 := by
    simp only [Matrix.add_apply, dkA, dkE]; norm_num
  have h11 : (dkA + dkE) 1 1 = 2 := by
    simp only [Matrix.add_apply, dkA, dkE]; norm_num
  have h01 : (dkA + dkE) 0 1 = 3/4 := by
    simp only [Matrix.add_apply, dkA, dkE]; norm_num
  have h10 : (dkA + dkE) 1 0 = 3/4 := by
    simp only [Matrix.add_apply, dkA, dkE]; norm_num
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

/-- The sorted spectrum of the perturbed fixture is exactly
`[-1/4, 9/4]`, pinned independently. -/
theorem dkAE_evals_pin :
    evals dkAE_symmetric ⟨0, by simp⟩ = -1/4 ∧
      evals dkAE_symmetric ⟨1, by simp⟩ = 9/4 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues))).Sorted
      (fun a b => a ≤ b) := Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues))).sum
      = -1/4 + 9/4 := by
    have htr : ∑ i : Fin 2,
        eigvalOf (dkA + dkE) dkAE_symmetric i = -1/4 + 9/4 := by
      rw [eigvalOf_sum_eq_trace, dkAE_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues))).prod
      = -1/4 * (9/4) := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues i) = -9/16 := by
      have h := (isHermitian_of_isSymm dkAE_symmetric).det_eq_prod_eigenvalues
      rw [dkAE_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := -1/4) (hi := 9/4) (by norm_num)
    hlen hsorted hsum hprod

/-!
### Eigenvector directions and the projector pins

The eigenspaces are one-dimensional, so the eigen equations pin the
outer products making up the spectral projectors — no control over
Mathlib's classical eigenbasis choice is needed.
-/

/-- The sorted eigenvalue list of the perturbed fixture is the literal
list `[-1/4, 9/4]` (from the index-wise pin and the length). -/
theorem dkAE_sort_eq : (Multiset.sort (fun a b => a ≤ b)
    ((Finset.univ : Finset (Fin 2)).val.map
      ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues))) = [-1/4, 9/4] := by
  have h0 : evals dkAE_symmetric ⟨0, by simp⟩ = -1/4 := dkAE_evals_pin.1
  have h1 : evals dkAE_symmetric ⟨1, by simp⟩ = 9/4 := dkAE_evals_pin.2
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hget : ∀ j : Fin 2, (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues))).get
      ⟨(j : ℕ), by rw [hlen]; simp⟩ = evals dkAE_symmetric j :=
    fun j => rfl
  rw [list_two_eq hlen, hget ⟨0, by simp⟩, hget ⟨1, by simp⟩, h0, h1]

/-- Every eigenbasis eigenvalue of the perturbed fixture is one of the
two pinned values. -/
theorem dkAE_eigvalOf_mem (i : Fin 2) :
    eigvalOf (dkA + dkE) dkAE_symmetric i = -1/4 ∨
      eigvalOf (dkA + dkE) dkAE_symmetric i = 9/4 := by
  have hmem : eigvalOf (dkA + dkE) dkAE_symmetric i ∈ (Multiset.sort
      (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkAE_symmetric).eigenvalues))) := by
    rw [Multiset.mem_sort]
    exact Multiset.mem_map.2 ⟨i, Finset.mem_univ _, rfl⟩
  rw [dkAE_sort_eq] at hmem
  rcases List.mem_cons.1 hmem with h | h
  · exact Or.inl h
  rcases List.mem_cons.1 h with h' | h''
  · exact Or.inr h'
  · simp at h''

/-- The eigenbasis vectors at eigenvalue `-1/4` (a one-dimensional
eigenspace) have direction `v 0 = -3 * v 1` and unit norm — computed
from the eigen equations, independent of the basis choice. -/
theorem dkAE_low_eigvec_direction {i : Fin 2}
    (hle : eigvalOf (dkA + dkE) dkAE_symmetric i ≤ -1/4) :
    eigvecOf (dkA + dkE) dkAE_symmetric i 0
      = -3 * eigvecOf (dkA + dkE) dkAE_symmetric i 1 ∧
    ∑ a, (eigvecOf (dkA + dkE) dkAE_symmetric i a
      * eigvecOf (dkA + dkE) dkAE_symmetric i a) = 1 := by
  have hμ : eigvalOf (dkA + dkE) dkAE_symmetric i = -1/4 := by
    rcases dkAE_eigvalOf_mem i with h | h
    · exact h
    · exact absurd hle (by rw [h]; norm_num)
  have hveq : (dkA + dkE) *ᵥ (eigvecOf (dkA + dkE) dkAE_symmetric i)
      = (eigvalOf (dkA + dkE) dkAE_symmetric i)
        • (eigvecOf (dkA + dkE) dkAE_symmetric i) :=
    (isHermitian_of_isSymm dkAE_symmetric).mulVec_eigenvectorBasis i
  have hunit : ∑ a, (eigvecOf (dkA + dkE) dkAE_symmetric i a
      * eigvecOf (dkA + dkE) dkAE_symmetric i a) = 1 := by
    have h := eigvecOf_inner (dkA + dkE) dkAE_symmetric i i
    simpa using h
  -- the first row of the eigen equation pins the direction
  have hrow : ((dkA + dkE) *ᵥ (eigvecOf (dkA + dkE) dkAE_symmetric i)) 0
      = eigvalOf (dkA + dkE) dkAE_symmetric i
        * (eigvecOf (dkA + dkE) dkAE_symmetric i) 0 := by
    have h1 := congrFun hveq 0
    simp at h1
    exact h1
  have hraw : ((dkA + dkE) *ᵥ (eigvecOf (dkA + dkE) dkAE_symmetric i)) 0
      = (3/4) * (eigvecOf (dkA + dkE) dkAE_symmetric i) 1 := by
    simp only [Matrix.mulVec, Matrix.dotProduct]
    have e0 : (dkA + dkE) 0 0 = 0 := by
      simp only [Matrix.add_apply, dkA, dkE]; norm_num
    have e1 : (dkA + dkE) 0 1 = 3/4 := by
      simp only [Matrix.add_apply, dkA, dkE]; norm_num
    simp only [e0, e1, Fin.sum_univ_two]
    ring
  rw [hrow, hμ] at hraw
  have hd : eigvecOf (dkA + dkE) dkAE_symmetric i 0
      = -3 * eigvecOf (dkA + dkE) dkAE_symmetric i 1 := by
    linarith
  exact ⟨hd, hunit⟩

/-- The single-membership pin of the low filter: the eigenbasis indices
with eigenvalue at most the low threshold form a singleton. -/
theorem dkAE_low_filter_singleton :
    ∃ i₀ : Fin 2, (Finset.univ.filter fun i =>
      eigvalOf (dkA + dkE) dkAE_symmetric i ≤ -1/4) = {i₀} := by
  have hge : (1 : ℕ) ≤ (Finset.univ.filter fun i =>
      eigvalOf (dkA + dkE) dkAE_symmetric i ≤ -1/4).card := by
    have h := succ_le_card_filter_eigvalOf_le dkAE_symmetric ⟨0, by simp⟩
    rw [dkAE_evals_pin.1] at h
    exact h
  have hle : (Finset.univ.filter fun i =>
      eigvalOf (dkA + dkE) dkAE_symmetric i ≤ -1/4).card ≤ 1 := by
    have hsub : (Finset.univ.filter fun i =>
        eigvalOf (dkA + dkE) dkAE_symmetric i ≤ -1/4) ⊆
        Finset.univ.filter fun i =>
        eigvalOf (dkA + dkE) dkAE_symmetric i < 9/4 := by
      intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ i,
        lt_of_le_of_lt (Finset.mem_filter.1 hi).2 (by norm_num)⟩
    have h2 := card_filter_eigvalOf_lt_evals_le dkAE_symmetric ⟨1, by simp⟩
    rw [dkAE_evals_pin.2] at h2
    exact (Finset.card_le_card hsub).trans h2
  exact Finset.card_eq_one.1 (le_antisymm hle hge)

/-- **The perturbed projector pinned**: `Q` (the spectral projector of
`dkA + dkE` at its low threshold) is the rank-one outer product
`(1/10)·!![9, -3; -3, 1]` — the projection onto the line of the
eigenvector `(3, -1)/√10`. -/
theorem dkAE_projector_pin :
    spectralProjector (dkA + dkE) dkAE_symmetric
        (evals dkAE_symmetric ⟨0, by simp⟩)
      = !![9/10, -3/10; -3/10, 1/10] := by
  rw [dkAE_evals_pin.1]
  obtain ⟨i₀, hF⟩ := dkAE_low_filter_singleton
  have hi₀ : i₀ ∈ Finset.univ.filter fun i =>
      eigvalOf (dkA + dkE) dkAE_symmetric i ≤ -1/4 := by
    rw [hF]; exact Finset.mem_singleton_self i₀
  obtain ⟨hdir, hunit⟩ := dkAE_low_eigvec_direction (Finset.mem_filter.1 hi₀).2
  set v := eigvecOf (dkA + dkE) dkAE_symmetric i₀ with hvdef
  have hv1sq : (v 1) * (v 1) = 1/10 := by
    have hsum : v 0 * v 0 + v 1 * v 1 = 1 := by
      simpa [Fin.sum_univ_two] using hunit
    rw [hdir] at hsum
    nlinarith [hsum]
  have hv0sq : (v 0) * (v 0) = 9/10 := by
    rw [hdir]
    nlinarith [hv1sq]
  have hvcross : (v 0) * (v 1) = -3/10 := by
    rw [hdir]
    nlinarith [hv1sq]
  have h00 : spectralProjector (dkA + dkE) dkAE_symmetric (-1/4) 0 0
      = 9/10 := by
    simp only [spectralProjector, Matrix.of_apply, hF, Finset.sum_singleton,
      hvdef]
    exact hv0sq
  have h01 : spectralProjector (dkA + dkE) dkAE_symmetric (-1/4) 0 1
      = -3/10 := by
    simp only [spectralProjector, Matrix.of_apply, hF, Finset.sum_singleton,
      hvdef]
    exact hvcross
  have h10 : spectralProjector (dkA + dkE) dkAE_symmetric (-1/4) 1 0
      = -3/10 := by
    simp only [spectralProjector, Matrix.of_apply, hF, Finset.sum_singleton,
      hvdef]
    rw [mul_comm]
    exact hvcross
  have h11 : spectralProjector (dkA + dkE) dkAE_symmetric (-1/4) 1 1
      = 1/10 := by
    simp only [spectralProjector, Matrix.of_apply, hF, Finset.sum_singleton,
      hvdef]
    exact hv1sq
  ext a b
  fin_cases a <;> fin_cases b
  all_goals first
    | exact h00
    | exact h01
    | exact h10
    | exact h11

/-- **The unperturbed projector pinned**: `P` (the spectral projector
of `dkA` at its low threshold `0`) is the coordinate projection
`diag(1, 0)`. -/
theorem dkA_projector_pin :
    spectralProjector dkA dkA_symmetric (evals dkA_symmetric ⟨0, by simp⟩)
      = !![1, 0; 0, 0] := by
  rw [dkA_evals_pin.1]
  -- the filter at 0 is a singleton
  have hge : (1 : ℕ) ≤ (Finset.univ.filter fun i =>
      eigvalOf dkA dkA_symmetric i ≤ 0).card := by
    have h := succ_le_card_filter_eigvalOf_le dkA_symmetric ⟨0, by simp⟩
    rw [dkA_evals_pin.1] at h
    exact h
  have hle : (Finset.univ.filter fun i =>
      eigvalOf dkA dkA_symmetric i ≤ 0).card ≤ 1 := by
    have hsub : (Finset.univ.filter fun i =>
        eigvalOf dkA dkA_symmetric i ≤ 0) ⊆
        Finset.univ.filter fun i =>
        eigvalOf dkA dkA_symmetric i < 2 := by
      intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ i,
        lt_of_le_of_lt (Finset.mem_filter.1 hi).2 (by norm_num)⟩
    have h2 := card_filter_eigvalOf_lt_evals_le dkA_symmetric ⟨1, by simp⟩
    rw [dkA_evals_pin.2] at h2
    exact (Finset.card_le_card hsub).trans h2
  obtain ⟨i₀, hF⟩ := Finset.card_eq_one.1 (le_antisymm hle hge)
  have hi₀ : i₀ ∈ Finset.univ.filter fun i =>
      eigvalOf dkA dkA_symmetric i ≤ 0 := by
    rw [hF]; exact Finset.mem_singleton_self i₀
  -- the eigenvector at 0 lies on the first coordinate axis
  set v := eigvecOf dkA dkA_symmetric i₀ with hvdef
  have hμ : eigvalOf dkA dkA_symmetric i₀ = 0 := by
    have hmem : eigvalOf dkA dkA_symmetric i₀ ∈ (Multiset.sort
        (fun a b => a ≤ b)
        ((Finset.univ : Finset (Fin 2)).val.map
          ((isHermitian_of_isSymm dkA_symmetric).eigenvalues))) := by
      rw [Multiset.mem_sort]
      exact Multiset.mem_map.2 ⟨i₀, Finset.mem_univ _, rfl⟩
    have hsort : (Multiset.sort (fun a b => a ≤ b)
        ((Finset.univ : Finset (Fin 2)).val.map
          ((isHermitian_of_isSymm dkA_symmetric).eigenvalues))) = [0, 2] := by
      have h0 : evals dkA_symmetric ⟨0, by simp⟩ = 0 := dkA_evals_pin.1
      have h1 : evals dkA_symmetric ⟨1, by simp⟩ = 2 := dkA_evals_pin.2
      have hlen : (Multiset.sort (fun a b => a ≤ b)
          ((Finset.univ : Finset (Fin 2)).val.map
            ((isHermitian_of_isSymm dkA_symmetric).eigenvalues))).length = 2 := by
        rw [Multiset.length_sort, Multiset.card_map]; simp
      have hget : ∀ j : Fin 2, (Multiset.sort (fun a b => a ≤ b)
          ((Finset.univ : Finset (Fin 2)).val.map
            ((isHermitian_of_isSymm dkA_symmetric).eigenvalues))).get
          ⟨(j : ℕ), by rw [hlen]; simp⟩ = evals dkA_symmetric j :=
        fun j => rfl
      rw [list_two_eq hlen, hget ⟨0, by simp⟩, hget ⟨1, by simp⟩, h0, h1]
    rw [hsort] at hmem
    rcases List.mem_cons.1 hmem with h | h
    · exact h
    · rcases List.mem_cons.1 h with h' | h''
      · exact absurd (Finset.mem_filter.1 hi₀).2 (by rw [h']; norm_num)
      · simp at h''
  have hveq : dkA *ᵥ v = (eigvalOf dkA dkA_symmetric i₀) • v :=
    (isHermitian_of_isSymm dkA_symmetric).mulVec_eigenvectorBasis i₀
  have hunit : v 0 * v 0 + v 1 * v 1 = 1 := by
    have h := eigvecOf_inner dkA dkA_symmetric i₀ i₀
    simpa [Fin.sum_univ_two] using h
  have hrow : (dkA *ᵥ v) 1 = 0 := by
    have h := congrFun hveq 1
    rw [hμ] at h
    simp only [zero_smul, Pi.zero_apply] at h
    exact h
  have hraw : (dkA *ᵥ v) 1 = 2 * v 1 := by
    simp only [Matrix.mulVec, Matrix.dotProduct]
    have e0 : dkA 1 0 = 0 := by simp [dkA]
    have e1 : dkA 1 1 = 2 := by simp [dkA]
    simp only [e0, e1, Fin.sum_univ_two]
    ring
  have hz : (dkA *ᵥ v) 1 = 0 := by
    have h := congrFun hveq 1
    rw [hμ] at h
    simp only [zero_smul, Pi.zero_apply] at h
    exact h
  have hv1 : v 1 = 0 := by linarith
  have hv0sq : (v 0) * (v 0) = 1 := by nlinarith [hunit]
  have hvcross : (v 0) * (v 1) = 0 := by rw [hv1]; ring
  have hvcross' : (v 1) * (v 0) = 0 := by rw [hv1]; ring
  have hv1sq : (v 1) * (v 1) = 0 := by rw [hv1]; ring
  have h00 : spectralProjector dkA dkA_symmetric 0 0 0 = 1 := by
    simp only [spectralProjector, Matrix.of_apply, hF, Finset.sum_singleton,
      hvdef]
    exact hv0sq
  have h01 : spectralProjector dkA dkA_symmetric 0 0 1 = 0 := by
    simp only [spectralProjector, Matrix.of_apply, hF, Finset.sum_singleton,
      hvdef]
    exact hvcross
  have h10 : spectralProjector dkA dkA_symmetric 0 1 0 = 0 := by
    simp only [spectralProjector, Matrix.of_apply, hF, Finset.sum_singleton,
      hvdef]
    exact hvcross'
  have h11 : spectralProjector dkA dkA_symmetric 0 1 1 = 0 := by
    simp only [spectralProjector, Matrix.of_apply, hF, Finset.sum_singleton,
      hvdef]
    exact hv1sq
  ext a b
  fin_cases a <;> fin_cases b
  all_goals first
    | exact h00
    | exact h01
    | exact h10
    | exact h11

/-- **The strict non-vacuity instance**: at the rotation fixture the
bound reads `‖Q − P‖ ≤ ‖dkE‖ / (9/4) = 1/3`, with both spectra and the
perturbation norm pinned independently of the theorem. -/
theorem davis_kahan_rotation_bound_QA :
    ‖initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩‖ ≤ 1/3 := by
  have hin := davis_kahan_sin_theta dkA dkE dkA_symmetric dkAE_symmetric
    ⟨0, by simp⟩ (by decide) (9/4) (by norm_num) (by
      rw [dkAE_evals_pin.2, dkA_evals_pin.1]
      norm_num)
  rw [dkE_norm] at hin
  norm_num at hin
  exact hin

/-- The difference `Q − P` of the pinned projectors, entrywise. -/
theorem dkQP_apply (a b : Fin 2) :
    (initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩) a b
      = !![-1/10, -3/10; -3/10, 1/10] a b := by
  have h1 : spectralProjector (dkA + dkE) dkAE_symmetric
      (evals dkAE_symmetric ⟨0, by simp⟩) a b
      = !![9/10, -3/10; -3/10, 1/10] a b :=
    congrFun (congrFun dkAE_projector_pin a) b
  have h2 : spectralProjector dkA dkA_symmetric
      (evals dkA_symmetric ⟨0, by simp⟩) a b
      = !![1, 0; 0, 0] a b :=
    congrFun (congrFun dkA_projector_pin a) b
  show spectralProjector (dkA + dkE) dkAE_symmetric
      (evals dkAE_symmetric ⟨0, by simp⟩) a b
    - spectralProjector dkA dkA_symmetric (evals dkA_symmetric ⟨0, by simp⟩) a b = _
  rw [h1, h2]
  fin_cases a <;> fin_cases b <;> simp
  all_goals norm_num

theorem dkQP_symmetric :
    (initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩).IsSymm := by
  refine Matrix.IsSymm.ext fun a b => ?_
  rw [dkQP_apply b a, dkQP_apply a b]
  fin_cases a <;> fin_cases b <;> simp [Matrix.of_apply]

theorem dkQP_trace :
    (initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩).trace = 0 := by
  show (spectralProjector (dkA + dkE) dkAE_symmetric
      (evals dkAE_symmetric ⟨0, by simp⟩)
    - spectralProjector dkA dkA_symmetric (evals dkA_symmetric ⟨0, by simp⟩)).trace = 0
  rw [Matrix.trace_sub, dkAE_projector_pin, dkA_projector_pin]
  simp only [Matrix.trace, Matrix.of_apply]
  norm_num

theorem dkQP_det :
    (initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩).det = -1/10 := by
  have h00 : (initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩) 0 0 = -1/10 :=
    dkQP_apply 0 0
  have h11 : (initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩) 1 1 = 1/10 :=
    dkQP_apply 1 1
  have h01 : (initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩) 0 1 = -3/10 :=
    dkQP_apply 0 1
  have h10 : (initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩) 1 0 = -3/10 :=
    dkQP_apply 1 0
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

/-- The sorted spectrum of the pinned difference is
`[-√(1/10), √(1/10)]` (trace `0`, determinant `-1/10`). -/
theorem dkQP_evals_pin :
    evals dkQP_symmetric ⟨0, by simp⟩ = -(Real.sqrt (1/10)) ∧
      evals dkQP_symmetric ⟨1, by simp⟩ = Real.sqrt (1/10) := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkQP_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkQP_symmetric).eigenvalues))).Sorted
      (fun a b => a ≤ b) := Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkQP_symmetric).eigenvalues))).sum
      = -(Real.sqrt (1/10)) + Real.sqrt (1/10) := by
    have htr : ∑ i : Fin 2,
        eigvalOf _ dkQP_symmetric i
        = -(Real.sqrt (1/10)) + Real.sqrt (1/10) := by
      rw [eigvalOf_sum_eq_trace, dkQP_trace]
      ring
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm dkQP_symmetric).eigenvalues))).prod
      = -(Real.sqrt (1/10)) * Real.sqrt (1/10) := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm dkQP_symmetric).eigenvalues i) = -1/10 := by
      have h := (isHermitian_of_isSymm dkQP_symmetric).det_eq_prod_eigenvalues
      rw [dkQP_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    have hr : Real.sqrt (1/10) * Real.sqrt (1/10) = 1/10 :=
      Real.mul_self_sqrt (by norm_num)
    linarith
  exact two_point_pin_of_sum_prod (lo := -(Real.sqrt (1/10)))
    (hi := Real.sqrt (1/10))
    (by linarith [Real.sqrt_nonneg (1/10)]) hlen hsorted hsum hprod

/-- **The exact distance is `1/√10`, strictly below the `1/3` bound**:
the bound is not vacuous and not attained at this fixture. -/
theorem davis_kahan_rotation_strict_QA :
    ‖initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
      - initialProjector dkA dkA_symmetric ⟨0, by simp⟩‖ = Real.sqrt (1/10)
    ∧ Real.sqrt (1/10) < 1/3 := by
  have hlast : evals dkQP_symmetric ⟨Fintype.card (Fin 2) - 1, by simp⟩
      = Real.sqrt (1/10) := by
    show evals dkQP_symmetric ⟨1, by simp⟩ = Real.sqrt (1/10)
    exact dkQP_evals_pin.2
  rw [Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_eq_max_abs_evals
    dkQP_symmetric (by norm_num), dkQP_evals_pin.1, hlast]
  have hmax : max |-(Real.sqrt (1/10))| |Real.sqrt (1/10)|
      = Real.sqrt (1/10) := by
    rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact max_eq_right (le_refl _)
  refine ⟨hmax, ?_⟩
  have h1 : Real.sqrt (1/10) * Real.sqrt (1/10) = 1/10 :=
    Real.mul_self_sqrt (by norm_num)
  have h2 : (1/3 : ℝ) * (1/3) = 1/9 := by norm_num
  nlinarith

end RotationFixture

/-!
## The adversarial fence audit (`proposals/adversarial-fences-davis-kahan-core-family.md`)

Hypothesis-form fences (negative witnesses) and packaged isolation
companions for the Davis–Kahan core perturbation family's load-bearing
clauses: `davis_kahan_sin_theta`'s `hδ`/`hsep`, the Duhamel bound's
`hab`/`hcl`, the rank pin's no-tie clause, the trivial endpoint's four
projector-structure clauses, and the sorted-step lemma's eigenvalue
clause — the audit method's thirteenth application. Every fence refutes
a *theorem* instantiation (the family is proved hard crust); nothing
admitted is consumed.
-/

/-- **The D1 fence: `hδ : 0 < δ` is load-bearing.** At the rotation
fixture with `δ = -1/2` (every other hypothesis genuine, including the
separation), the bound's right side is the negative `‖dkE‖ / (-1/2) =
-3/2` while the left side is a norm — the dropped statement cannot
hold. -/
theorem dkf_dk_hdelta_fence :
    ¬ (‖initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
          - initialProjector dkA dkA_symmetric ⟨0, by simp⟩‖
        ≤ ‖dkE‖ / (-(1/2) : ℝ)) := by
  intro hcon
  have h0 := le_trans (norm_nonneg _) hcon
  rw [dkE_norm] at h0
  norm_num at h0

/-- **D1 isolation:** the separation clause is genuine at `δ = -1/2`
(the pinned gap `9/4 - 0` dominates it), so `hδ` is the only failing
hypothesis at this fixture. -/
theorem dkf_dk_hdelta_isolation :
    (-(1/2) : ℝ) ≤ evals dkAE_symmetric ⟨1, by simp⟩
      - evals dkA_symmetric ⟨0, by simp⟩ := by
  rw [dkAE_evals_pin.2, dkA_evals_pin.1]
  norm_num

/-- **The D2 fence: `hsep` is load-bearing.** With the separation
dropped, take `δ = 100` (`hδ` genuine): the bound would read
`‖Q - P‖ ≤ ‖dkE‖ / 100 = 3/400`, but the exact distance is pinned at
`√(1/10) > 3/400`. -/
theorem dkf_dk_hsep_fence :
    ¬ (‖initialProjector (dkA + dkE) dkAE_symmetric ⟨0, by simp⟩
          - initialProjector dkA dkA_symmetric ⟨0, by simp⟩‖
        ≤ ‖dkE‖ / (100 : ℝ)) := by
  intro hcon
  rw [dkE_norm] at hcon
  rw [(davis_kahan_rotation_strict_QA).1] at hcon
  have hsq : Real.sqrt ((1:ℝ)/10) * Real.sqrt ((1:ℝ)/10) = 1/10 :=
    Real.mul_self_sqrt (by norm_num)
  have hnn := Real.sqrt_nonneg ((1:ℝ)/10)
  have hc0 : (0:ℝ) ≤ 3/400 := by norm_num
  nlinarith

/-- **D2 isolation:** `hδ` is genuine at `δ = 100`. -/
theorem dkf_dk_hsep_isolation : (0:ℝ) < 100 := by norm_num

/-!

## The Duhamel bound's two clauses (H1, H2)
-/

/-- **The H1 fence: `hab : a < b` is load-bearing.** At `a = 1`,
`b = 0` (with `hcl` genuine: its premise-implication is trivially true
at `b = 0`, `c' = 0`, since `0 < λ → 0 ≤ λ`), the bound's right side is
`‖dkE‖ / (0 - 1) = -3/4` — below every norm. -/
theorem dkf_duhamel_hab_fence :
    ¬ (‖(1 - spectralProjector (dkA + dkE) dkAE_symmetric 0)
          * spectralProjector dkA dkA_symmetric 1‖
        ≤ ‖dkE‖ / (0 - 1)) := by
  intro hcon
  have h0 := le_trans (norm_nonneg _) hcon
  rw [dkE_norm] at h0
  norm_num at h0

/-- **H1 isolation:** the eigenvalue-window clause `hcl` is genuine at
the fence's `b = 0`, `c' = 0`. -/
theorem dkf_duhamel_hab_isolation : ∀ i : Fin 2,
    (0:ℝ) < eigvalOf (dkA + dkE) dkAE_symmetric i →
      (0:ℝ) ≤ eigvalOf (dkA + dkE) dkAE_symmetric i := by
  intro i hi
  exact le_of_lt hi


/-!
## The H2 layer: the threshold-`1` projector pin (the Duhamel `hcl`
fence's fixture) — the window `(-∞, 1]` captures exactly the `-1/4`
eigenspace, so the projector is the delivered pin's own matrix.
-/

/-- The window filter at threshold `1` coincides with the low filter at
`-1/4`: the only eigenvalue in `(-∞, 1]` is `-1/4` (`9/4` sits above
the window, by the delivered eigenvalue-membership pin). -/
theorem dkAE_filter_one_eq_low :
    (Finset.univ.filter fun i => eigvalOf (dkA + dkE) dkAE_symmetric i ≤ 1)
      = (Finset.univ.filter fun i =>
        eigvalOf (dkA + dkE) dkAE_symmetric i ≤ -1/4) := by
  apply Finset.ext
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases dkAE_eigvalOf_mem i with h' | h'
    · exact h'.le
    · exact absurd (h' ▸ h) (by norm_num)
  · intro h
    exact le_trans h (by norm_num)

/-- **The perturbed projector pinned at the H2 window**: `Q` at
threshold `1` is the same rank-one outer product
`(1/10)·!![9, -3; -3, 1]` as at its bottom eigenvalue. -/
theorem dkAE_projector_one_pin :
    spectralProjector (dkA + dkE) dkAE_symmetric 1
      = !![9/10, -3/10; -3/10, 1/10] := by
  have hEq : spectralProjector (dkA + dkE) dkAE_symmetric 1
      = spectralProjector (dkA + dkE) dkAE_symmetric (-1/4) := by
    conv_lhs => unfold spectralProjector
    rw [dkAE_filter_one_eq_low]
    rfl
  have hpin := dkAE_projector_pin
  rw [dkAE_evals_pin.1] at hpin
  rw [hEq]
  exact hpin

/-- The unperturbed projector at the H2 threshold `0` — the delivered
pin's own matrix (its threshold is the pinned bottom eigenvalue `0`). -/
theorem dkA_projector_zero :
    spectralProjector dkA dkA_symmetric 0 = !![1, 0; 0, 0] := by
  have h := dkA_projector_pin
  rw [dkA_evals_pin.1] at h
  exact h

/-- **The H2 fence: `hcl` (the eigenvalue window above `c'`) is
load-bearing.** At `a = 0`, `c' = 1` (both projectors pinned), `b = 100`
(`hab` genuine), the bound would read `‖(1 - Q) * P‖ ≤ ‖dkE‖ / 100 =
3/400`; but `(1 - Q) * P *ᵥ e₀ = ![1/10, 3/10]` pins the left side's
square at `≥ 1/10 > (3/400)²`. -/
theorem dkf_duhamel_hcl_fence :
    ¬ (‖(1 - spectralProjector (dkA + dkE) dkAE_symmetric 1)
          * spectralProjector dkA dkA_symmetric 0‖
        ≤ ‖dkE‖ / (100 - 0)) := by
  intro hcon
  have hRval : ‖dkE‖ / (100 - 0) = 3/400 := by
    rw [dkE_norm]
    norm_num
  rw [hRval] at hcon
  have hM : (1 - spectralProjector (dkA + dkE) dkAE_symmetric 1)
      * spectralProjector dkA dkA_symmetric 0
      = !![1/10, 0; 3/10, 0] := by
    rw [dkAE_projector_one_pin, dkA_projector_zero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.one_apply, Matrix.sub_apply]
    all_goals norm_num
  rw [hM] at hcon
  have hw := dotProduct_mulVec_norm2_le_l2OpNorm_sq
    (!![1/10, 0; 3/10, 0] : Matrix (Fin 2) (Fin 2) ℝ) (![1, 0] : Fin 2 → ℝ)
  have hmv : (!![1/10, 0; 3/10, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
      (![1, 0] : Fin 2 → ℝ) = ![1/10, 3/10] := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have hd : (![1/10, 3/10] : Fin 2 → ℝ) ⬝ᵥ ![1/10, 3/10] = 1/10 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    norm_num
  have he : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [hmv, hd, he] at hw
  have hnn : (0:ℝ) ≤ ‖(!![1/10, 0; 3/10, 0] : Matrix (Fin 2) (Fin 2) ℝ)‖ :=
    norm_nonneg _
  nlinarith [hcon, hnn]

/-- **H2 isolation:** `hab` is genuine at `b = 100`, and the dropped
`hcl` fails at exactly the `9/4` eigenvalue index. -/
theorem dkf_duhamel_hcl_isolation :
    ((0:ℝ) < 100) ∧ ∃ i : Fin 2,
      (1:ℝ) < eigvalOf (dkA + dkE) dkAE_symmetric i ∧
      ¬ ((100:ℝ) ≤ eigvalOf (dkA + dkE) dkAE_symmetric i) := by
  refine ⟨by norm_num, ?_⟩
  have hsum : ∑ i : Fin 2, eigvalOf (dkA + dkE) dkAE_symmetric i
      = (-1/4) + 9/4 := by
    rw [eigvalOf_sum_eq_trace, dkAE_trace]
    norm_num
  by_contra hcon'
  have hall : ∀ i, eigvalOf (dkA + dkE) dkAE_symmetric i = -1/4 := fun i => by
    rcases dkAE_eigvalOf_mem i with h | h
    · exact h
    · exact (hcon' ⟨i, by rw [h]; norm_num,
        fun hle => by rw [h] at hle; norm_num at hle⟩).elim
  simp only [hall] at hsum
  norm_num at hsum

/-!
## The H3 layer: the rank pin's no-tie clause, at the zero matrix
-/

private theorem dkf_zero_eigvalOf (i : Fin 2) :
    eigvalOf (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i = 0 := by
  have hveq : (0 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
      (eigvecOf (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i)
      = eigvalOf (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i
        • eigvecOf (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i :=
    (isHermitian_of_isSymm zero_isSymm_QA).mulVec_eigenvectorBasis i
  rw [zero_mulVec] at hveq
  rcases smul_eq_zero.1 hveq.symm with h | h
  · exact h
  · exfalso
    have hu : ∑ a, (eigvecOf (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i a
        * eigvecOf (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i a) = 1 := by
      have h := eigvecOf_inner (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i i
      simpa using h
    rw [h] at hu
    simp at hu

theorem dkf_zero_evals_pin :
    evals (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm) ⟨0, by simp⟩ = 0 ∧
      evals (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm) ⟨1, by simp⟩
        = 0 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm
          (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm
          (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm
          (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues))).sum
        = 0 + 0 := by
    have htr : ∑ i : Fin 2,
        eigvalOf (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i = 0 + 0 := by
      rw [eigvalOf_sum_eq_trace]
      simp
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm
          (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues))).prod
        = 0 * 0 := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm
          (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).eigenvalues i) = 0 := by
      have h := (isHermitian_of_isSymm
        (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)).det_eq_prod_eigenvalues
      have hz : (0 : Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
        simp [Matrix.det_fin_two]
      rw [hz] at h
      exact h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := 0) (hi := 0) (by norm_num)
    hlen hsorted hsum hprod

/-- **The H3 fence: the no-tie clause of the rank pin is
load-bearing.** At the zero matrix the sorted spectrum is tied (`0, 0`),
so the dropped statement would read
`rank (spectralProjector 0 hM 0) = 1`; but every eigenvalue is `0`, the
projector is the identity, and its rank is `2`. -/
theorem dkf_rank_hnn_tie_fence :
    ¬ ((spectralProjector (0 : Matrix (Fin 2) (Fin 2) ℝ)
          (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)
          (evals (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)
            ⟨0, by simp⟩)).rank
        = (0:ℕ) + 1) := by
  intro hcon
  have hproj : spectralProjector (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)
      (evals (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)
        ⟨0, by simp⟩) = 1 :=
    spectralProjector_eq_one _ _ _ (fun i => by
      show eigvalOf (0 : Matrix (Fin 2) (Fin 2) ℝ) zero_isSymm_QA i
        ≤ evals (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)
          ⟨0, by simp⟩
      rw [dkf_zero_evals_pin.1]
      exact le_of_eq (dkf_zero_eigvalOf i))
  rw [hproj, Matrix.rank_one] at hcon
  simp at hcon

/-- **H3 isolation:** the dropped no-tie hypothesis fails — the zero
matrix's pinned spectrum is tied at `0`. -/
theorem dkf_rank_hnn_tie_isolation :
    ¬ (evals (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm) ⟨0, by simp⟩
        < evals (zero_isSymm_QA : (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm)
          ⟨1, by simp⟩) := by
  rw [dkf_zero_evals_pin.1, dkf_zero_evals_pin.2]
  norm_num

/-!
## The H4–H7 layer: the trivial endpoint's four projector-structure
clauses, at two trivial fixtures
-/

/-- The asymmetric idempotent `!![1,2;0,0]]` — the H4/H6 fixture. -/
def dkfAsym2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 0, 0]

theorem dkfAsym2_mul_self : dkfAsym2 * dkfAsym2 = dkfAsym2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two, dkfAsym2]

theorem dkfAsym2_not_isSymm : ¬ dkfAsym2.IsSymm := by
  intro h
  have h1 := congrFun (congrFun h.eq 1) 0
  simp [Matrix.transpose_apply, dkfAsym2] at h1

/-- The symmetric non-idempotent `diag(2, 0)` — the H5/H7 fixture and a
P-section fixture. -/
def dkfDiag2 : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![2, 0]

theorem dkfDiag2_symmetric : dkfDiag2.IsSymm := by
  show dkfDiag2ᵀ = dkfDiag2
  exact Matrix.diagonal_transpose _

theorem dkfDiag2_not_mul_self : ¬ (dkfDiag2 * dkfDiag2 = dkfDiag2) := by
  intro h
  have e := congrFun (congrFun h 0) 0
  simp only [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two,
    dkfDiag2, Matrix.diagonal_apply] at e
  norm_num at e

theorem dkfDiag2_rank : dkfDiag2.rank = 1 := by
  unfold dkfDiag2
  rw [Matrix.rank_diagonal]
  have hfe : (Finset.univ.filter fun x => (![2, 0] : Fin 2 → ℝ) x ≠ 0)
      = ({0} : Finset (Fin 2)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases x <;> simp
  simp only [Fintype.card_subtype, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hfe, Finset.card_singleton]

/-- **The H4 fence: `hP : P.IsSymm` of the trivial endpoint is
load-bearing.** The asymmetric idempotent `!![1,2;0,0]]` against `Q = 0`
(every kept clause genuine) has `P *ᵥ ![1,2] = ![5,0]`, so `‖P‖² ≥ 5`
and `‖P - Q‖ ≤ 1` fails. -/
theorem dkf_one_hP_fence : ¬ (‖dkfAsym2 - 0‖ ≤ 1) := by
  intro hcon
  have hz : dkfAsym2 - 0 = dkfAsym2 := sub_zero _
  rw [hz] at hcon
  have hw := dotProduct_mulVec_norm2_le_l2OpNorm_sq dkfAsym2
    (![1, 2] : Fin 2 → ℝ)
  have hmv : dkfAsym2 *ᵥ (![1, 2] : Fin 2 → ℝ) = ![5, 0] := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, dkfAsym2]
    all_goals norm_num
  have hd : (![5, 0] : Fin 2 → ℝ) ⬝ᵥ ![5, 0] = 25 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    norm_num
  have he : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 2] = 5 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    norm_num
  rw [hmv, hd, he] at hw
  have hnn : (0:ℝ) ≤ ‖dkfAsym2‖ := norm_nonneg _
  nlinarith [hcon, hnn]

/-- **H4 isolation:** every kept clause is genuine (`Q = 0` is a
symmetric idempotent; `P` is idempotent), so `hP` is the only failing
hypothesis. -/
theorem dkf_one_hP_isolation :
    dkfAsym2 * dkfAsym2 = dkfAsym2 ∧
      (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm ∧
      ((0 : Matrix (Fin 2) (Fin 2) ℝ) * 0 = 0) ∧ ¬ dkfAsym2.IsSymm :=
  ⟨dkfAsym2_mul_self, zero_isSymm_QA, mul_zero _, dkfAsym2_not_isSymm⟩

/-- **The H5 fence: `hPP : P * P = P` of the trivial endpoint is
load-bearing.** The symmetric non-idempotent `diag(2, 0)` against
`Q = 0` has `‖P‖² ≥ 4` (witness `e₀`), so `‖P - Q‖ ≤ 1` fails. -/
theorem dkf_one_hPP_fence : ¬ (‖dkfDiag2 - 0‖ ≤ 1) := by
  intro hcon
  have hz : dkfDiag2 - 0 = dkfDiag2 := sub_zero _
  rw [hz] at hcon
  have hw := dotProduct_mulVec_norm2_le_l2OpNorm_sq dkfDiag2
    (![1, 0] : Fin 2 → ℝ)
  have hmv : dkfDiag2 *ᵥ (![1, 0] : Fin 2 → ℝ) = ![2, 0] := by
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, dkfDiag2,
        Matrix.diagonal_apply]
  have hd : (![2, 0] : Fin 2 → ℝ) ⬝ᵥ ![2, 0] = 4 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    norm_num
  have he : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [hmv, hd, he] at hw
  have hnn : (0:ℝ) ≤ ‖dkfDiag2‖ := norm_nonneg _
  nlinarith [hcon, hnn]

/-- **H5 isolation.** -/
theorem dkf_one_hPP_isolation :
    dkfDiag2.IsSymm ∧ (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm ∧
      ((0 : Matrix (Fin 2) (Fin 2) ℝ) * 0 = 0) ∧
      ¬ (dkfDiag2 * dkfDiag2 = dkfDiag2) :=
  ⟨dkfDiag2_symmetric, zero_isSymm_QA, mul_zero _, dkfDiag2_not_mul_self⟩

/-- **The H6 fence: `hQ` of the trivial endpoint is load-bearing** —
the mirror of H4 at the same fixture. -/
theorem dkf_one_hQ_fence : ¬ (‖(0 : Matrix (Fin 2) (Fin 2) ℝ) - dkfAsym2‖ ≤ 1) := by
  intro hcon
  rw [zero_sub, norm_neg] at hcon
  exact dkf_one_hP_fence (by rw [sub_zero]; exact hcon)

/-- **H6 isolation** — mirror of H4's. -/
theorem dkf_one_hQ_isolation :
    (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm ∧
      ((0 : Matrix (Fin 2) (Fin 2) ℝ) * 0 = 0) ∧
      dkfAsym2 * dkfAsym2 = dkfAsym2 ∧ ¬ dkfAsym2.IsSymm :=
  ⟨zero_isSymm_QA, mul_zero _, dkfAsym2_mul_self, dkfAsym2_not_isSymm⟩

/-- **The H7 fence: `hQQ` of the trivial endpoint is load-bearing** —
the mirror of H5 at the same fixture. -/
theorem dkf_one_hQQ_fence : ¬ (‖(0 : Matrix (Fin 2) (Fin 2) ℝ) - dkfDiag2‖ ≤ 1) := by
  intro hcon
  rw [zero_sub, norm_neg] at hcon
  exact dkf_one_hPP_fence (by rw [sub_zero]; exact hcon)

/-- **H7 isolation** — mirror of H5's. -/
theorem dkf_one_hQQ_isolation :
    (0 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm ∧
      ((0 : Matrix (Fin 2) (Fin 2) ℝ) * 0 = 0) ∧
      dkfDiag2.IsSymm ∧ ¬ (dkfDiag2 * dkfDiag2 = dkfDiag2) :=
  ⟨zero_isSymm_QA, mul_zero _, dkfDiag2_symmetric, dkfDiag2_not_mul_self⟩

/-!
## The H8 layer: the sorted-step lemma's eigenvalue clause
-/

/-- **The H8 fence: `h : evals k < eigvalOf i` of the sorted-step lemma
is load-bearing.** At `dkA` with `k = 0`, the pinned spectrum is
`[0, 2]` and some eigenbasis index carries the bottom eigenvalue `0`
(the sub-level filter is nonempty and no eigenvalue is below the
bottom), so the dropped statement reads `2 ≤ 0`. -/
theorem dkf_sortedstep_fence : ∃ i : Fin 2,
    ¬ (evals dkA_symmetric ⟨(0:ℕ) + 1, by simp⟩ ≤ eigvalOf dkA dkA_symmetric i) := by
  have hge := succ_le_card_filter_eigvalOf_le dkA_symmetric ⟨0, by simp⟩
  rw [dkA_evals_pin.1] at hge
  have hne : (Finset.univ.filter fun i => eigvalOf dkA dkA_symmetric i ≤ 0).Nonempty :=
    Finset.card_pos.1 (by omega)
  obtain ⟨i₀, hi₀⟩ := hne
  have hle : eigvalOf dkA dkA_symmetric i₀ ≤ 0 := (Finset.mem_filter.1 hi₀).2
  have hfirst : evals dkA_symmetric ⟨0, by simp⟩ ≤ eigvalOf dkA dkA_symmetric i₀ :=
    evals_first_le_eigvalOf dkA_symmetric (by norm_num : (1:ℕ) ≤ Fintype.card (Fin 2)) i₀
  rw [dkA_evals_pin.1] at hfirst
  have heq : eigvalOf dkA dkA_symmetric i₀ = 0 := le_antisymm hle hfirst
  refine ⟨i₀, ?_⟩
  intro hc
  have h1 : evals dkA_symmetric ⟨(0:ℕ) + 1, by simp⟩ = 2 := by
    show evals dkA_symmetric ⟨1, by simp⟩ = 2
    exact dkA_evals_pin.2
  rw [h1, heq] at hc
  norm_num at hc

/-- **H8 isolation:** the dropped clause fails at the found index —
`evals ⟨0⟩ = 0` is not strictly below `eigvalOf i₀ = 0`. -/
theorem dkf_sortedstep_isolation :
    ¬ (∀ i : Fin 2, evals dkA_symmetric ⟨0, by simp⟩ < eigvalOf dkA dkA_symmetric i) := by
  intro h
  have hge := succ_le_card_filter_eigvalOf_le dkA_symmetric ⟨0, by simp⟩
  rw [dkA_evals_pin.1] at hge
  have hne : (Finset.univ.filter fun i => eigvalOf dkA dkA_symmetric i ≤ 0).Nonempty :=
    Finset.card_pos.1 (by omega)
  obtain ⟨i₀, hi₀⟩ := hne
  have hle : eigvalOf dkA dkA_symmetric i₀ ≤ 0 := (Finset.mem_filter.1 hi₀).2
  have hfirst : evals dkA_symmetric ⟨0, by simp⟩ ≤ eigvalOf dkA dkA_symmetric i₀ :=
    evals_first_le_eigvalOf dkA_symmetric (by norm_num : (1:ℕ) ≤ Fintype.card (Fin 2)) i₀
  rw [dkA_evals_pin.1] at hfirst
  have heq : eigvalOf dkA dkA_symmetric i₀ = 0 := le_antisymm hle hfirst
  have hlt := h i₀
  rw [show evals dkA_symmetric ⟨0, by simp⟩ = 0 from dkA_evals_pin.1] at hlt
  rw [heq] at hlt
  exact absurd hlt (by norm_num)


end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
