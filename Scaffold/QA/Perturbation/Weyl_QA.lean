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
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl

/-!
# QA for the Weyl perturbation interface

Zero-perturbation instances of `weyl_inequality` and
`spectral_gap_stability`, and a nonzero-perturbation instance with all
spectra pinned from trace/determinant/sortedness. Since the
2026-08-20 retirement (`proposals/discharge-perturbation-axioms.md`),
`weyl_inequality` is a proved theorem, and this file exercises the
proved interface (it no longer derives consequences from an admitted
axiom):

- the zero perturbation pins the identity bound (`E = 0` moves nothing);
- the additive bounds (`weyl_additive_upper`/`weyl_additive_lower`) are
  instantiated on the pinned fixture at both indices;
- the full bound at a genuinely nonzero perturbation is **attained**
  exactly at one index (the interface is tight, not loose by accident)
  and **strict** at the other (not vacuously satisfied);
- the additive window's endpoints are load-bearing: replacing `λₙ(E)`
  by `λ₁(E)` in the upper bound is refuted on the same fixture
  (`6 ≤ 4` is false).
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
/-- The zero matrix is symmetric (interface convenience). -/
theorem zero_isSymm_QA : (0 : Matrix V V ℝ).IsSymm := isSymm_zero

/-- Eigenvalues are invariant under adding zero. -/
theorem evals_add_zero (A : Matrix V V ℝ) (hA : A.IsSymm)
    (i : Fin (Fintype.card V)) :
    evals (show (A + 0).IsSymm by rw [add_zero]; exact hA) i = evals hA i := by
  have h := weyl_inequality A 0 hA zero_isSymm_QA i
  rw [norm_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- Instantiating Weyl's inequality at `E = 0`: every eigenvalue is
fixed. Exercises the sorted-eigenvalue indexing and the ℓ² operator
norm of the interface. -/
theorem zero_perturbation_QA (A : Matrix V V ℝ) (hA : A.IsSymm)
    (i : Fin (Fintype.card V)) :
    |evals (show (A + 0).IsSymm by rw [add_zero]; exact hA) i - evals hA i|
      ≤ ‖(0 : Matrix V V ℝ)‖ := by
  rw [evals_add_zero A hA i, sub_self, abs_zero, norm_zero]

/-- Instantiating gap stability at `E = 0`: the spectral gap is exactly
preserved, since `γ - 2 * 0 = γ`. -/
theorem spectral_gap_zero_perturbation_QA (A : Matrix V V ℝ) (hA : A.IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (γ : ℝ)
    (hγ : spectralGap A hA k hk ≥ γ) :
    spectralGap (A + 0) (show (A + 0).IsSymm by rw [add_zero]; exact hA) k hk
      ≥ γ := by
  have h := spectral_gap_stability A 0 hA zero_isSymm_QA k hk 0
    (norm_zero.le) γ hγ
  simpa using h

/-!
## Nonzero-perturbation fixture

`A = E = !![2,1;1,2]` (spectrum `[1, 3]`, pinned from
trace/determinant/sortedness), so `A + E = !![4,2;2,4]` with spectrum
`[2, 6]` and `‖E‖ = 3` (through the proved operator-norm bridge). Every
value below is computed from the raw fixture, independent of the theorem
under test.
-/

section NonzeroFixture

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

/-- The base and perturbing fixture `!![2,1;1,2]`. -/
def mat2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1; 1, 2]

theorem mat2_symmetric : mat2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, mat2]

theorem mat2_trace : mat2.trace = 4 := by
  simp [Matrix.trace, mat2]
  norm_num

theorem mat2_det : mat2.det = 3 := by
  have h00 : mat2 0 0 = 2 := by simp [mat2]
  have h11 : mat2 1 1 = 2 := by simp [mat2]
  have h01 : mat2 0 1 = 1 := by simp [mat2]
  have h10 : mat2 1 0 = 1 := by simp [mat2]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

/-- The sorted spectrum of the fixture is exactly `[1, 3]`, pinned from
trace, determinant, and sortedness — independent of every theorem under
test below. -/
theorem mat2_evals_pin :
    evals mat2_symmetric ⟨0, by simp⟩ = 1 ∧
      evals mat2_symmetric ⟨1, by simp⟩ = 3 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).sum = 1 + 3 := by
    have htr : ∑ i : Fin 2, eigvalOf mat2 mat2_symmetric i = 1 + 3 := by
      rw [eigvalOf_sum_eq_trace, mat2_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).prod = 1 * 3 := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues i) = 3 := by
      have h := (isHermitian_of_isSymm mat2_symmetric).det_eq_prod_eigenvalues
      rw [mat2_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := 1) (hi := 3) (by norm_num)
    hlen hsorted hsum hprod

/-- The perturbed fixture `!![4,2;2,4]` as the literal sum, so its
trace and determinant compute entrywise. -/
theorem mat2_add_trace : (mat2 + mat2).trace = 8 := by
  simp [Matrix.trace, mat2]
  norm_num

theorem mat2_add_det : (mat2 + mat2).det = 12 := by
  have h00 : (mat2 + mat2) 0 0 = 4 := by
    simp only [Matrix.add_apply, mat2]; norm_num
  have h11 : (mat2 + mat2) 1 1 = 4 := by
    simp only [Matrix.add_apply, mat2]; norm_num
  have h01 : (mat2 + mat2) 0 1 = 2 := by
    simp only [Matrix.add_apply, mat2]; norm_num
  have h10 : (mat2 + mat2) 1 0 = 2 := by
    simp only [Matrix.add_apply, mat2]; norm_num
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

/-- The sorted spectrum of the perturbed matrix is exactly `[2, 6]`,
pinned independently (trace `8`, determinant `12`, sortedness). -/
theorem mat2_add_evals_pin :
    evals (mat2_symmetric.add mat2_symmetric) ⟨0, by simp⟩ = 2 ∧
      evals (mat2_symmetric.add mat2_symmetric) ⟨1, by simp⟩ = 6 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (mat2_symmetric.add mat2_symmetric)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (mat2_symmetric.add mat2_symmetric)).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (mat2_symmetric.add mat2_symmetric)).eigenvalues))).sum = 2 + 6 := by
    have htr : ∑ i : Fin 2,
        eigvalOf (mat2 + mat2) (mat2_symmetric.add mat2_symmetric) i = 2 + 6 := by
      rw [eigvalOf_sum_eq_trace, mat2_add_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (mat2_symmetric.add mat2_symmetric)).eigenvalues))).prod = 2 * 6 := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm (mat2_symmetric.add mat2_symmetric)).eigenvalues i) = 12 := by
      have h := (isHermitian_of_isSymm (mat2_symmetric.add mat2_symmetric)).det_eq_prod_eigenvalues
      rw [mat2_add_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := 2) (hi := 6) (by norm_num)
    hlen hsorted hsum hprod

/-- The perturbation norm `‖mat2‖ = 3` — the top of the pinned
spectrum, computed through the proved operator-norm bridge's two
directions (not through any Weyl statement). -/
theorem mat2_opNorm_eq_three : ‖mat2‖ = 3 := by
  refine le_antisymm ?_ ?_
  · refine Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_le_of_abs_evals_le
      mat2_symmetric (by norm_num) ?_
    intro k
    fin_cases k
    · rw [mat2_evals_pin.1, abs_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)]
      try norm_num
    · rw [mat2_evals_pin.2, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
      try norm_num
  · have h := Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.abs_evals_le_l2OpNorm
      mat2_symmetric ⟨1, by simp⟩
    rw [mat2_evals_pin.2, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)] at h
    exact h

/-- **Nonzero-perturbation instance:** with `A = E = !![2,1;1,2]`, the
eigenvalues move from `[1, 3]` to `[2, 6]` and the bound
`|λᵢ(A+E) − λᵢ(A)| ≤ ‖E‖` holds at both indices against the
independently pinned values. -/
theorem weyl_nonzero_perturbation_QA :
    |evals (mat2_symmetric.add mat2_symmetric) ⟨0, by simp⟩
        - evals mat2_symmetric ⟨0, by simp⟩| ≤ ‖mat2‖ ∧
    |evals (mat2_symmetric.add mat2_symmetric) ⟨1, by simp⟩
        - evals mat2_symmetric ⟨1, by simp⟩| ≤ ‖mat2‖ := by
  constructor
  · exact weyl_inequality mat2 mat2 mat2_symmetric mat2_symmetric ⟨0, by simp⟩
  · exact weyl_inequality mat2 mat2 mat2_symmetric mat2_symmetric ⟨1, by simp⟩

/-- **Tightness:** at the top index the bound is attained exactly —
`|6 − 3| = 3 = ‖E‖` — so the proved interface has no accidental slack
(a weakened restatement with room to spare would still pass
`weyl_nonzero_perturbation_QA` but not this. -/
theorem weyl_bound_attained_QA :
    |evals (mat2_symmetric.add mat2_symmetric) ⟨1, by simp⟩
        - evals mat2_symmetric ⟨1, by simp⟩| = ‖mat2‖ := by
  rw [mat2_add_evals_pin.2, mat2_evals_pin.2, mat2_opNorm_eq_three]
  norm_num

/-- **Strictness (the non-vacuity witness the proposal's QA plan
requires):** at the bottom index the movement `|2 − 1| = 1` is strictly
below the bound `3` — a genuinely nonzero perturbation where the bound
is strict, not satisfied at equality trivially. -/
theorem weyl_bound_strict_QA :
    |evals (mat2_symmetric.add mat2_symmetric) ⟨0, by simp⟩
        - evals mat2_symmetric ⟨0, by simp⟩| < ‖mat2‖ := by
  rw [mat2_add_evals_pin.1, mat2_evals_pin.1, mat2_opNorm_eq_three]
  norm_num

/-- **Additive bounds, bottom index:** `λ₁(A) + λ₁(E) = 1 + 1 = 2` is
attained exactly by `λ₁(A+E) = 2`, and `λ₁(A+E) = 2 ≤ 1 + 3 = λ₁(A) +
λₙ(E)` — the additive window holds with equality at its lower endpoint. -/
theorem weyl_additive_bottom_QA :
    evals mat2_symmetric ⟨0, by simp⟩ + evals mat2_symmetric ⟨0, by simp⟩
      = evals (mat2_symmetric.add mat2_symmetric) ⟨0, by simp⟩ ∧
    evals (mat2_symmetric.add mat2_symmetric) ⟨0, by simp⟩
      ≤ evals mat2_symmetric ⟨0, by simp⟩
        + evals mat2_symmetric ⟨1, by simp⟩ := by
  have hcard : (1 : ℕ) ≤ Fintype.card (Fin 2) := by norm_num
  refine ⟨?_, ?_⟩
  · rw [mat2_evals_pin.1, mat2_add_evals_pin.1]
    norm_num
  · have h0 := weyl_additive_upper mat2 mat2 mat2_symmetric mat2_symmetric hcard
      ⟨0, by simp⟩
    -- defeq-ascribe to canonical index forms (proof-irrelevant `Fin`
    -- fields), then rewrite syntactically on both sides
    have h0' : evals mat2_symmetric ⟨0, by simp⟩
        + evals mat2_symmetric ⟨1, by simp⟩
        ≥ evals (mat2_symmetric.add mat2_symmetric) ⟨0, by simp⟩ := h0
    rw [mat2_evals_pin.1, mat2_evals_pin.2, mat2_add_evals_pin.1] at h0'
    rw [mat2_evals_pin.1, mat2_evals_pin.2, mat2_add_evals_pin.1]
    exact h0'

/-- **Additive bounds, top index:** `λ₂(A) + λ₁(E) = 3 + 1 = 4 ≤
λ₂(A+E) = 6 ≤ 3 + 3 = λ₂(A) + λₙ(E)` — the upper endpoint is attained
exactly. -/
theorem weyl_additive_top_QA :
    evals mat2_symmetric ⟨1, by simp⟩ + evals mat2_symmetric ⟨0, by simp⟩
      ≤ evals (mat2_symmetric.add mat2_symmetric) ⟨1, by simp⟩ ∧
    evals (mat2_symmetric.add mat2_symmetric) ⟨1, by simp⟩
      = evals mat2_symmetric ⟨1, by simp⟩
        + evals mat2_symmetric ⟨1, by simp⟩ := by
  have hcard : (1 : ℕ) ≤ Fintype.card (Fin 2) := by norm_num
  refine ⟨?_, ?_⟩
  · have h1 := weyl_additive_lower mat2 mat2 mat2_symmetric mat2_symmetric hcard
      ⟨1, by simp⟩
    have h1' : evals mat2_symmetric ⟨1, by simp⟩
        + evals mat2_symmetric ⟨0, by simp⟩
        ≤ evals (mat2_symmetric.add mat2_symmetric) ⟨1, by simp⟩ := h1
    rw [mat2_evals_pin.2, mat2_evals_pin.1, mat2_add_evals_pin.2] at h1'
    rw [mat2_evals_pin.2, mat2_evals_pin.1, mat2_add_evals_pin.2]
    exact h1'
  · have h2 := weyl_additive_upper mat2 mat2 mat2_symmetric mat2_symmetric hcard
      ⟨1, by simp⟩
    have h2' : evals mat2_symmetric ⟨1, by simp⟩
        + evals mat2_symmetric ⟨1, by simp⟩
        ≥ evals (mat2_symmetric.add mat2_symmetric) ⟨1, by simp⟩ := h2
    rw [mat2_evals_pin.2, mat2_add_evals_pin.2] at h2'
    rw [mat2_evals_pin.2, mat2_add_evals_pin.2]
    linarith

/-- **Window-endpoint guard:** the upper additive bound with `λ₁(E)` in
place of `λₙ(E)` is refuted on this fixture (`6 ≤ 3 + 1 = 4` is false) —
the window's endpoints are load-bearing and not interchangeable. -/
theorem weyl_window_endpoint_guard_QA :
    ¬ (evals (mat2_symmetric.add mat2_symmetric) ⟨1, by simp⟩
      ≤ evals mat2_symmetric ⟨1, by simp⟩
        + evals mat2_symmetric ⟨0, by simp⟩) := by
  rw [mat2_add_evals_pin.2, mat2_evals_pin.2, mat2_evals_pin.1]
  norm_num

end NonzeroFixture

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
