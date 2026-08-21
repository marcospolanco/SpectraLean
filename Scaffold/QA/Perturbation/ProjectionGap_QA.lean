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
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.ProjectionGap

/-!
# QA for the projection-gap (equal-rank projector identity) interface

`Analysis/OperatorTheory/Perturbation/ProjectionGap.lean` is pure hard
crust: the always-true max layer, the equal-rank core, and the headline
gap identity `‖P − Q‖ = ‖(I − Q) * P‖` are all proved (no admitted
statement is involved). This file exercises that proved interface on
fully rational fixtures:

- the **rotation fixture**: `P` projects onto the first coordinate and
  `Q` onto the line spanned by `(4/5, 3/5)` — two rank-one orthogonal
  projectors at a single Pythagorean principal angle with
  `sin θ = 3/5`. (The execution-plan sketch said "30° rotation"; the
  Pythagorean angle carries the same mathematics — one irrational-free
  principal angle — while keeping every pinned value in ℚ, the same
  discipline as the band-projector QA's 3-4-5 triangle.) Every norm is
  pinned **twice, by independent routes**:
  `‖(I − Q) * P‖ = 3/5` through the module's own squared-residual
  theorem (`1 − τ` at the pinned sandwich spectrum `{0, 16/25}`) and
  through raw literal arithmetic on `((I − Q) P)ᵀ ((I − Q) P)` plus the
  proved operator-norm bridge; `‖P − Q‖ = 3/5` through the difference
  matrix's own pinned spectrum `{−3/5, 3/5}` (trace `0`, determinant
  `−9/25`). The headline identity is then checked against both pins.
- the **unequal-rank guard**: `P` as above against `Q = 1`. The
  hypothesis-free form of the headline is *refuted* (`‖P − 1‖ = 1` while
  `‖(1 − 1) * P‖ = 0`), and the always-true max form is instantiated
  where the *right* residual is the maximum — documenting that for
  unequal ranks the max, not the left residual, is what survives.

All spectra are pinned from trace/determinant/sortedness exactly as in
`Weyl_QA.lean`, independent of the theorem under test.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open Matrix SpectralGraphTheory
open Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
open Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent

/-!
## Two-point spectrum pinning (the `Weyl_QA` recipe)
-/

private theorem list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- A sorted length-two list with sum `lo + hi` and product `lo * hi`
is `[lo, hi]` whenever `lo ≤ hi`. -/
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

/-!
## The rotation fixture

`pDiag` projects onto the first coordinate; `qRot` projects onto the
line of `(4/5, 3/5)`. The principal angle has `cos θ = 4/5`,
`sin θ = 3/5`, so every residual norm below is `3/5`.
-/

/-- The rank-one coordinate projector `diag (1, 0)`. -/
noncomputable def pDiag : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal ![1, 0]

/-- The rank-one projector onto the line of `(4/5, 3/5)`. -/
noncomputable def qRot : Matrix (Fin 2) (Fin 2) ℝ :=
  !![16 / 25, 12 / 25; 12 / 25, 9 / 25]

theorem pDiag_isSymm : pDiag.IsSymm := by
  show pDiagᵀ = pDiag
  exact Matrix.diagonal_transpose _

theorem qRot_isSymm : qRot.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, qRot]

theorem pDiag_mul_self : pDiag * pDiag = pDiag := by
  show Matrix.diagonal (![1, 0] : Fin 2 → ℝ)
      * Matrix.diagonal (![1, 0] : Fin 2 → ℝ)
    = Matrix.diagonal (![1, 0] : Fin 2 → ℝ)
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.diagonal_apply]
  all_goals norm_num

theorem qRot_mul_self : qRot * qRot = qRot := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two, qRot]
  all_goals try ring

theorem pDiag_rank : pDiag.rank = 1 := by
  unfold pDiag
  rw [Matrix.rank_diagonal]
  have hfe : (Finset.univ.filter fun x => (![1, 0] : Fin 2 → ℝ) x ≠ 0)
      = ({0} : Finset (Fin 2)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    fin_cases x <;> simp
  simp only [Fintype.card_subtype, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hfe, Finset.card_singleton]

/-- Every image `qRot *ᵥ x` is a multiple of the generating line. -/
private theorem qRot_mulVec_eq_smul (x : Fin 2 → ℝ) :
    qRot *ᵥ x = (Matrix.dotProduct (![4 / 5, 3 / 5] : Fin 2 → ℝ) x)
      • (![4 / 5, 3 / 5] : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, qRot]
  all_goals try ring

theorem qRot_rank : qRot.rank = 1 := by
  have hv : (![4 / 5, 3 / 5] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  set v : Fin 2 → ℝ := ![4 / 5, 3 / 5] with hvdef
  have hvv : Matrix.dotProduct v v = 1 := by
    simp [Matrix.dotProduct, hvdef]
    norm_num
  have hmem : ∀ y ∈ LinearMap.range qRot.mulVecLin,
      y ∈ Submodule.span ℝ ({v} : Set (Fin 2 → ℝ)) := by
    rintro y ⟨x, rfl⟩
    simp only [Matrix.mulVecLin_apply]
    rw [qRot_mulVec_eq_smul x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))
  have hvrange : v ∈ LinearMap.range qRot.mulVecLin := by
    refine LinearMap.mem_range.2 ⟨v, ?_⟩
    simp only [Matrix.mulVecLin_apply]
    rw [qRot_mulVec_eq_smul v, hvv, one_smul]
  have hspanle : Submodule.span ℝ ({v} : Set (Fin 2 → ℝ))
      ≤ LinearMap.range qRot.mulVecLin :=
    Submodule.span_le.2 (fun y hy => by
      rcases Set.mem_singleton_iff.1 hy with rfl
      exact hvrange)
  have hrange : LinearMap.range qRot.mulVecLin
      = Submodule.span ℝ ({v} : Set (Fin 2 → ℝ)) :=
    le_antisymm (fun y hy => hmem y hy) hspanle
  rw [Matrix.rank, hrange, finrank_span_singleton hv]

/-!
### The pinned spectra
-/

private theorem pin_two_by_two {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.IsSymm) (htr : M.trace = lo + hi) (hlo : lo ≤ hi)
    (hdt : M.det = lo * hi) :
    evals hM ⟨0, by simp⟩ = lo ∧ evals hM ⟨1, by simp⟩ = hi := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).sum = lo + hi := by
    have htr' : ∑ i : Fin 2, eigvalOf M hM i = lo + hi := by
      rw [eigvalOf_sum_eq_trace]; exact htr
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr'
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hM).eigenvalues))).prod = lo * hi := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm hM).eigenvalues i) = lo * hi := by
      have h := (isHermitian_of_isSymm hM).det_eq_prod_eigenvalues
      rw [hdt] at h
      exact h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd0
  exact two_point_pin_of_sum_prod hlo hlen hsorted hsum hprod

theorem qRot_evals_pin :
    evals qRot_isSymm ⟨0, by simp⟩ = 0 ∧
      evals qRot_isSymm ⟨1, by simp⟩ = 1 := by
  have h00 : qRot 0 0 = 16 / 25 := by simp [qRot]
  have h11 : qRot 1 1 = 9 / 25 := by simp [qRot]
  have h01 : qRot 0 1 = 12 / 25 := by simp [qRot]
  have h10 : qRot 1 0 = 12 / 25 := by simp [qRot]
  refine pin_two_by_two qRot_isSymm ?_ (by norm_num) ?_
  · simp only [Matrix.trace, qRot]
    norm_num
  · rw [Matrix.det_fin_two, h00, h11, h01, h10]
    norm_num

/-- The sandwich `pDiag * qRot * pDiag` is the literal diagonal
`diag (16/25, 0)` — the squared cosine of the principal angle sits in
the surviving entry. -/
theorem pqp_literal :
    pDiag * qRot * pDiag = !![16 / 25, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two, pDiag,
      qRot, Matrix.diagonal_apply]

theorem pqp_evals_pin :
    evals (pqp_isSymm pDiag_isSymm qRot_isSymm) ⟨0, by simp⟩ = 0 ∧
      evals (pqp_isSymm pDiag_isSymm qRot_isSymm) ⟨1, by simp⟩
        = 16 / 25 := by
  have hs : (pDiag * qRot * pDiag).IsSymm :=
    pqp_isSymm pDiag_isSymm qRot_isSymm
  have htr : (pDiag * qRot * pDiag).trace = 0 + 16 / 25 := by
    rw [pqp_literal]
    simp [Matrix.trace]
  have hdt : (pDiag * qRot * pDiag).det = 0 * (16 / 25) := by
    rw [pqp_literal]
    rw [Matrix.det_fin_two]
    norm_num
  exact pin_two_by_two (pqp_isSymm pDiag_isSymm qRot_isSymm) htr
    (by norm_num) hdt

/-- The squared residual `((1 − qRot) * pDiag)ᵀ * ((1 − qRot) * pDiag)`
is the literal `diag (9/25, 0)` — `sin² θ` in the surviving entry. -/
theorem resid_literal :
    (1 - qRot) * pDiag = !![9 / 25, 0; -12 / 25, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two, pDiag,
      qRot, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.one_apply]
  all_goals try ring

theorem resid_transpose_literal :
    ((1 - qRot) * pDiag)ᵀ = !![9 / 25, -12 / 25; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, resid_literal]

theorem resid_gram_literal :
    ((1 - qRot) * pDiag)ᵀ * ((1 - qRot) * pDiag) = !![9 / 25, 0; 0, 0] := by
  rw [resid_transpose_literal, resid_literal]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two]
  all_goals try norm_num

/-- The difference projector `pDiag − qRot` (for its independent
spectral pin). -/
theorem diff_literal :
    pDiag - qRot = !![9 / 25, -12 / 25; -12 / 25, -9 / 25] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, pDiag, qRot, Matrix.diagonal_apply]
  all_goals try ring

theorem diff_isSymm : (pDiag - qRot).IsSymm := by
  rw [diff_literal]
  exact Matrix.IsSymm.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem diff_evals_pin :
    evals diff_isSymm ⟨0, by simp⟩ = -3 / 5 ∧
      evals diff_isSymm ⟨1, by simp⟩ = 3 / 5 := by
  have htr : (pDiag - qRot).trace = -3 / 5 + 3 / 5 := by
    rw [diff_literal]
    simp [Matrix.trace]
    norm_num
  have hdt : (pDiag - qRot).det = -3 / 5 * (3 / 5) := by
    rw [diff_literal, Matrix.det_fin_two]
    norm_num
  exact pin_two_by_two diff_isSymm htr (by norm_num) hdt

/-!
### The pinned norms

`‖(I − qRot) * pDiag‖ = 3/5` by two independent routes, and
`‖pDiag − qRot‖ = 3/5` through the difference's own spectrum.
-/

/-- **Route A (through the module under test):** the squared-residual
theorem gives `‖(1 − qRot) * pDiag‖² = 1 − τ` with `τ = 16/25` the top
of the pinned sandwich spectrum. -/
theorem resid_opNorm_by_module_QA :
    ‖(1 - qRot) * pDiag‖ * ‖(1 - qRot) * pDiag‖ = 9 / 25 := by
  have hr : 0 < pDiag.rank := by rw [pDiag_rank]; norm_num
  have h := l2OpNorm_one_sub_mul_sq_eq pDiag_isSymm pDiag_mul_self
    qRot_isSymm qRot_mul_self hr
  have hidx : (rankIdx pDiag hr : Fin (Fintype.card (Fin 2)))
      = ⟨1, by simp⟩ := by
    refine Fin.ext ?_
    simp only [rankIdx, pDiag_rank]
    norm_num
  rw [hidx] at h
  -- defeq-ascribe to the canonical index form (proof-irrelevant `Fin`
  -- fields), then rewrite syntactically
  have h' : ‖(1 - qRot) * pDiag‖ * ‖(1 - qRot) * pDiag‖
      = 1 - evals (pqp_isSymm pDiag_isSymm qRot_isSymm) ⟨1, by simp⟩ := h
  rw [pqp_evals_pin.2] at h'
  rw [h']
  norm_num

/-- **Route B (independent of the module's headline statements):** the
Gram matrix `((1 − qRot) * pDiag)ᵀ * ((1 − qRot) * pDiag)` is the
literal `diag (9/25, 0)`, whose norm `9/25` is pinned through the
operator-norm bridge's two directions from its pinned spectrum. -/
theorem gram_isSymm :
    (((1 - qRot) * pDiag)ᵀ * ((1 - qRot) * pDiag)).IsSymm := by
  rw [resid_gram_literal]
  exact Matrix.IsSymm.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem gram_evals_pin :
    evals gram_isSymm ⟨0, by simp⟩ = 0 ∧
      evals gram_isSymm ⟨1, by simp⟩ = 9 / 25 := by
  have htr : (((1 - qRot) * pDiag)ᵀ * ((1 - qRot) * pDiag)).trace
      = 0 + 9 / 25 := by
    rw [resid_gram_literal]
    simp only [Matrix.trace]
    norm_num
  have hdt : (((1 - qRot) * pDiag)ᵀ * ((1 - qRot) * pDiag)).det
      = 0 * (9 / 25) := by
    rw [resid_gram_literal, Matrix.det_fin_two]
    norm_num
  exact pin_two_by_two gram_isSymm htr (by norm_num) hdt

theorem gram_opNorm_QA :
    ‖((1 - qRot) * pDiag)ᵀ * ((1 - qRot) * pDiag)‖ = 9 / 25 := by
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le gram_isSymm (by norm_num) ?_
    intro k
    fin_cases k
    · rw [gram_evals_pin.1,
        abs_of_nonneg (show (0 : ℝ) ≤ 0 by norm_num)]
      norm_num
    · rw [gram_evals_pin.2,
        abs_of_nonneg (show (0 : ℝ) ≤ 9 / 25 by norm_num)]
  · have h := abs_evals_le_l2OpNorm gram_isSymm ⟨1, by simp⟩
    rw [gram_evals_pin.2,
      abs_of_nonneg (show (0 : ℝ) ≤ 9 / 25 by norm_num)] at h
    exact h

/-- **Route agreement:** the residual norm is `3/5`, computed through
the C*-identity from the independent Gram pin. -/
theorem resid_opNorm_indep_QA : ‖(1 - qRot) * pDiag‖ = 3 / 5 := by
  have hcstar : ‖(1 - qRot) * pDiag‖ * ‖(1 - qRot) * pDiag‖
      = ‖((1 - qRot) * pDiag)ᵀ * ((1 - qRot) * pDiag)‖ :=
    (Matrix.l2_opNorm_conjTranspose_mul_self _).symm
  rw [gram_opNorm_QA] at hcstar
  refine (pow_left_inj₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp ?_
  rw [sq, sq]
  nlinarith [hcstar]

/-- The module's squared-residual theorem and the independent literal
route meet at the same value. -/
theorem resid_route_agreement_QA :
    ‖(1 - qRot) * pDiag‖ * ‖(1 - qRot) * pDiag‖
      = ‖((1 - qRot) * pDiag)ᵀ * ((1 - qRot) * pDiag)‖ := by
  rw [resid_opNorm_by_module_QA, gram_opNorm_QA]

/-- The difference norm `‖pDiag − qRot‖ = 3/5` from the difference's
own pinned spectrum — independent of every projector-gap statement. -/
theorem diff_opNorm_QA : ‖pDiag - qRot‖ = 3 / 5 := by
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le diff_isSymm (by norm_num) ?_
    intro k
    fin_cases k
    · rw [diff_evals_pin.1,
        abs_of_nonpos (show (-3 : ℝ) / 5 ≤ 0 by norm_num)]
      norm_num
    · rw [diff_evals_pin.2,
        abs_of_nonneg (show (0 : ℝ) ≤ 3 / 5 by norm_num)]
  · have h := abs_evals_le_l2OpNorm diff_isSymm ⟨1, by simp⟩
    rw [diff_evals_pin.2,
      abs_of_nonneg (show (0 : ℝ) ≤ 3 / 5 by norm_num)] at h
    exact h

/-!
### The theorems under test, instantiated
-/

theorem equal_rank_hyp_QA : pDiag.rank = qRot.rank := by
  rw [pDiag_rank, qRot_rank]

/-- **The equal-rank core, instantiated:** the two directed residual
norms agree on the rotation fixture (each is `3/5`). -/
theorem one_sub_mul_eq_of_rank_eq_QA :
    ‖(1 - qRot) * pDiag‖ = ‖(1 - pDiag) * qRot‖ :=
  l2OpNorm_one_sub_mul_eq_of_rank_eq pDiag_isSymm pDiag_mul_self
    qRot_isSymm qRot_mul_self equal_rank_hyp_QA

/-- **The headline gap identity, instantiated and numerically pinned:**
`‖pDiag − qRot‖ = ‖(1 − qRot) * pDiag‖`, both sides `3/5` — the
theorem's value agrees with the independent difference-spectrum pin. -/
theorem headline_gap_identity_QA :
    ‖pDiag - qRot‖ = ‖(1 - qRot) * pDiag‖ ∧ ‖pDiag - qRot‖ = 3 / 5 := by
  refine ⟨l2OpNorm_sub_eq_of_rank_eq pDiag_isSymm pDiag_mul_self
    qRot_isSymm qRot_mul_self equal_rank_hyp_QA, diff_opNorm_QA⟩

/-- The residual computed by the module agrees with the value forced by
the headline pin: `3/5`. -/
theorem resid_forced_by_headline_QA :
    ‖(1 - qRot) * pDiag‖ = 3 / 5 := by
  rw [← headline_gap_identity_QA.1, headline_gap_identity_QA.2]

/-- **Triple agreement:** the difference norm and both directed residual
norms all equal `3/5` on the rotation fixture. -/
theorem triple_agreement_QA :
    ‖pDiag - qRot‖ = 3 / 5 ∧ ‖(1 - qRot) * pDiag‖ = 3 / 5
      ∧ ‖(1 - pDiag) * qRot‖ = 3 / 5 := by
  refine ⟨diff_opNorm_QA, resid_opNorm_indep_QA, ?_⟩
  rw [← one_sub_mul_eq_of_rank_eq_QA, resid_opNorm_indep_QA]

/-!
## The unequal-rank guard

`pDiag` (rank 1) against `1` (rank 2): the hypothesis-free form of the
headline is refuted, and the always-true max form is instantiated where
the *right* residual is the maximum.
-/

theorem one_rank_QA : (1 : Matrix (Fin 2) (Fin 2) ℝ).rank = 2 := by
  rw [Matrix.rank_one, Fintype.card_fin]

theorem unequal_rank_QA :
    pDiag.rank ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ).rank := by
  rw [pDiag_rank, one_rank_QA]
  norm_num

theorem diff_one_literal :
    pDiag - (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![0, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.sub_apply, pDiag, Matrix.diagonal_apply, Matrix.one_apply]

theorem diff_one_isSymm :
    (pDiag - (1 : Matrix (Fin 2) (Fin 2) ℝ)).IsSymm := by
  rw [diff_one_literal]
  exact Matrix.IsSymm.ext fun i j => by
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]

theorem diff_one_evals_pin :
    evals diff_one_isSymm ⟨0, by simp⟩ = -1 ∧
      evals diff_one_isSymm ⟨1, by simp⟩ = 0 := by
  have htr : (pDiag - (1 : Matrix (Fin 2) (Fin 2) ℝ)).trace
      = -1 + 0 := by
    rw [diff_one_literal]
    simp only [Matrix.trace]
    norm_num
  have hdt : (pDiag - (1 : Matrix (Fin 2) (Fin 2) ℝ)).det
      = -1 * 0 := by
    rw [diff_one_literal, Matrix.det_fin_two]
    norm_num
  exact pin_two_by_two diff_one_isSymm htr (by norm_num) hdt

theorem diff_one_opNorm_QA :
    ‖pDiag - (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le diff_one_isSymm (by norm_num) ?_
    intro k
    fin_cases k
    · rw [diff_one_evals_pin.1,
        abs_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)]
      norm_num
    · rw [diff_one_evals_pin.2,
        abs_of_nonneg (show (0 : ℝ) ≤ 0 by norm_num)]
      norm_num
  · have h := abs_evals_le_l2OpNorm diff_one_isSymm ⟨0, by simp⟩
    rw [diff_one_evals_pin.1,
      abs_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)] at h
    simpa using h

theorem zero_left_resid_QA :
    ‖(1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)) * pDiag‖ = 0 := by
  rw [sub_self, zero_mul, norm_zero]

/-- **The right residual at unequal rank:** `‖(1 − pDiag) * 1‖ = 1`,
pinned from the literal `diag (0, 1)`'s own spectrum (trace `1`,
determinant `0`) through the two-direction operator-norm bridge. -/
theorem right_resid_opNorm_QA :
    ‖(1 - pDiag) * (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ = 1 := by
  have hsub : (1 - pDiag) * (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = !![0, 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.dotProduct, Fin.sum_univ_two,
        pDiag, Matrix.diagonal_apply, Matrix.sub_apply,
        Matrix.one_apply]
  have hs : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).IsSymm :=
    Matrix.IsSymm.ext fun i j => by
      fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply]
  have htr : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).trace
      = 0 + 1 := by
    simp only [Matrix.trace]
    norm_num
  have hdt : (!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det
      = 0 * 1 := by
    rw [Matrix.det_fin_two]
    norm_num
  have hpin := pin_two_by_two hs htr (by norm_num) hdt
  calc ‖(1 - pDiag) * (1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      = ‖(!![0, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)‖ := by rw [hsub]
    _ = 1 := by
      refine le_antisymm ?_ ?_
      · refine l2OpNorm_le_of_abs_evals_le hs (by norm_num) ?_
        intro k
        fin_cases k
        · rw [hpin.1, abs_of_nonneg (show (0 : ℝ) ≤ 0 by norm_num)]
          norm_num
        · rw [hpin.2, abs_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)]
      · have h := abs_evals_le_l2OpNorm hs ⟨1, by simp⟩
        rw [hpin.2, abs_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)] at h
        exact h

/-- **The guard:** the hypothesis-free form of the headline identity is
*refuted* at unequal rank — `‖pDiag − 1‖ = 1` while `‖(1 − 1) * pDiag‖
= 0` — so the equal-rank hypothesis is load-bearing, not decorative. -/
theorem headline_rank_guard_QA :
    ¬ (‖pDiag - (1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      = ‖(1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)) * pDiag‖) := by
  rw [diff_one_opNorm_QA, zero_left_resid_QA]
  norm_num

/-- **The always-true max form at unequal rank:** instantiated where the
*right* residual is the maximum (`1`, against the left residual's `0`)
— documenting that for unequal ranks the max form, not the left
residual, carries the content. -/
theorem max_form_unequal_rank_QA :
    ‖pDiag - (1 : Matrix (Fin 2) (Fin 2) ℝ)‖
      = max ‖(1 - (1 : Matrix (Fin 2) (Fin 2) ℝ)) * pDiag‖
          ‖(1 - pDiag) * (1 : Matrix (Fin 2) (Fin 2) ℝ)‖ := by
  rw [l2OpNorm_sub_eq_max_of_isSymm_idempotent
      (Q := (1 : Matrix (Fin 2) (Fin 2) ℝ)) pDiag_isSymm pDiag_mul_self
      (by
        refine Matrix.IsSymm.ext fun i j => ?_
        simp only [Matrix.transpose_apply, Matrix.one_apply]
        fin_cases i <;> fin_cases j <;> simp)
      (by rw [Matrix.mul_one]),
    zero_left_resid_QA, right_resid_opNorm_QA]

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
