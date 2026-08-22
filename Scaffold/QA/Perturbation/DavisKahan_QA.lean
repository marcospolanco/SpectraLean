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

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
