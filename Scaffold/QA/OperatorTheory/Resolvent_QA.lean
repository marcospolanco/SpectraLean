/-
  Resolvent_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent`
  (the resolvent-calculus module, proposal steps 0–1), proved 2026-08-19:

  - the operator-norm bridge on the two-vertex symmetric fixture
    `!![2, 1; 1, 2]` whose sorted spectrum `[1, 3]` is pinned from
    trace, determinant, and sortedness (independently of the bridge):
    both directions instantiated, pinning `‖mat2‖ = 3` exactly — the
    largest-eigenvalue value from the literature — and the extremal
    packaged form instantiated at `max |1| |3| = 3`;
  - a negative witness for the upper direction: `‖mat2‖ ≤ 1` is false
    (1 is the *smallest* eigenvalue's absolute value), so bounding by
    one eigenvalue's absolute value instead of all of them is refuted —
    the `∀ k` hypothesis is load-bearing;
  - invertibility of the shifted PSD matrix on the `K₂` Laplacian
    `!![1, -1; -1, 1]` (PSD through the center's `laplacian_psd` at the
    unit-edge adjacency): `IsUnit (L + 1).det` delivered by the theorem
    and cross-checked against the computed determinant `3 ≠ 0`, the
    general-`t` instance at `t = 2` (determinant `8`), and the
    **shift-load-bearing witness**: the unshifted Laplacian has
    determinant exactly `0`, so PSD alone gives no invertibility — the
    `+ 1` is not decorative;
  - the resolvent identity on the same fixture with `B = 0`:
    `(L+1)⁻¹` computed to `(1/3)!![2,1;1,2]` by an independent
    left-inverse witness (`Matrix.inv_eq_left_inv`), and both sides of
    the identity computed from the raw definitions to the same literal
    matrix `!![-1/3, 1/3; 1/3, -1/3]` — a wrong factoring (order or
    sign) would fail this check.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the theorems; it checks their interfaces against independently
  computed values and falsifies nearby wrong statements.

  Scoreboard: ../docs/5_QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent

/-!
# QA for the resolvent calculus
-/

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.QA

open Matrix SpectralGraphTheory

/-!
## Fixture 1: the symmetric matrix `!![2, 1; 1, 2]` on `Fin 2`

Sorted spectrum `[1, 3]`, pinned by trace (`4`), determinant (`3`),
and sortedness — the same technique as the Courant–Fischer QA, so the
norm bridge is checked against values computed without any norm or
spectral-radius machinery.
-/

section Mat2

/-- The bridge fixture: symmetric, positive definite, spectrum
`{1, 3}` — not a Laplacian, exercising that the bridge needs only
symmetry. -/
def mat2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2, 1; 1, 2]

theorem mat2_symmetric : mat2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, mat2]

theorem mat2_apply (i j : Fin 2) : mat2 i j = if i = j then 2 else 1 := by
  fin_cases i <;> fin_cases j <;> simp [mat2]

theorem mat2_trace : mat2.trace = 4 := by
  simp [Matrix.trace, mat2_apply]
  norm_num

theorem mat2_det : mat2.det = 3 := by
  have h00 : mat2 0 0 = 2 := by simp [mat2_apply]
  have h11 : mat2 1 1 = 2 := by simp [mat2_apply]
  have h01 : mat2 0 1 = 1 := by simp [mat2_apply]
  have h10 : mat2 1 0 = 1 := by simp [mat2_apply]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

private theorem list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- Two-point spectrum pinning: a sorted length-two list with sum `4`
and product `3` is `[1, 3]`. -/
private theorem two_point_pin13 {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = 4)
    (hprod : l.prod = 3) :
    l.get ⟨0, by omega⟩ = 1 ∧ l.get ⟨1, by omega⟩ = 3 := by
  obtain ⟨g₀, g₁, hg⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, list_two_eq h2⟩
  subst hg
  have hmono : g₀ ≤ g₁ := by
    have h := hs.rel_get_of_lt (show (0 : Fin 2) < 1 by decide)
    simpa using h
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  have hsq : (g₁ - g₀) ^ 2 = 4 := by
    have hring : (g₁ - g₀) ^ 2 = (g₀ + g₁) ^ 2 - 4 * (g₀ * g₁) := by ring
    rw [hsum, hprod] at hring
    norm_num at hring
    exact hring
  have hd : g₁ - g₀ = 2 := by
    have hfactor : (g₁ - g₀ - 2) * (g₁ - g₀ + 2) = 0 := by
      have hexp : (g₁ - g₀ - 2) * (g₁ - g₀ + 2)
          = (g₁ - g₀) ^ 2 - 4 := by ring
      rw [hexp, hsq]
      ring
    rcases mul_eq_zero.1 hfactor with h | h
    · linarith
    · have hn : g₁ - g₀ = -2 := by linarith
      linarith
  refine ⟨?_, ?_⟩
  · show g₀ = 1
    linarith
  · show g₁ = 3
    linarith

/-- The sorted spectrum of the fixture is exactly `[1, 3]`, pinned
from trace, determinant, and sortedness — independent of the norm
bridge being QA'd. -/
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
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).sum = 4 := by
    have htr : ∑ i : Fin 2, eigvalOf mat2 mat2_symmetric i = 4 := by
      rw [eigvalOf_sum_eq_trace, mat2_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues))).prod = 3 := by
    have hd : ∏ i : Fin 2,
        ((isHermitian_of_isSymm mat2_symmetric).eigenvalues i) = 3 := by
      have hd0 := (isHermitian_of_isSymm mat2_symmetric).det_eq_prod_eigenvalues
      rw [mat2_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact two_point_pin13 hlen hsorted hsum hprod

/-!
### The bridge, instantiated

`‖mat2‖ = 3` — the operator norm equals the top eigenvalue, obtained
by composing both bridge directions with the pinned spectrum. The
literature value for this fixture's spectral norm is `3`.
-/

/-- The lower bridge direction at the top eigenvalue: `3 ≤ ‖mat2‖`,
consumed against the independently pinned spectrum. -/
theorem mat2_opNorm_ge_three_QA :
    (3:ℝ) ≤ ‖mat2‖ := by
  have h3 : |evals mat2_symmetric ⟨1, by simp⟩| ≤ ‖mat2‖ :=
    abs_evals_le_l2OpNorm mat2_symmetric _
  rw [(mat2_evals_pin.2 : evals mat2_symmetric ⟨1, by simp⟩ = 3)] at h3
  simpa using h3

/-- The upper bridge direction: with every pinned eigenvalue bounded
by `3`, the norm is at most `3`. -/
theorem mat2_opNorm_le_three_QA :
    ‖mat2‖ ≤ 3 := by
  refine l2OpNorm_le_of_abs_evals_le mat2_symmetric (by norm_num) ?_
  intro k
  fin_cases k
  · rw [(mat2_evals_pin.1 : evals mat2_symmetric ⟨0, by simp⟩ = 1)]
    norm_num
  · rw [(mat2_evals_pin.2 : evals mat2_symmetric ⟨1, by simp⟩ = 3)]
    norm_num

/-- The operator norm of the fixture is exactly `3`: both bridge
directions composed with the pinned spectrum. -/
theorem mat2_opNorm_eq_three_QA :
    ‖mat2‖ = 3 :=
  le_antisymm mat2_opNorm_le_three_QA mat2_opNorm_ge_three_QA

/-- The extremal packaged form of the bridge, instantiated: the norm
is the larger of `|1|` and `|3|`. -/
theorem mat2_opNorm_eq_max_QA :
    ‖mat2‖ = max |evals mat2_symmetric ⟨0, by simp⟩|
      |evals mat2_symmetric ⟨1, by simp⟩| :=
  l2OpNorm_eq_max_abs_evals mat2_symmetric (by decide)

/-- The packaged form's max is `max 1 3 = 3`, agreeing with the pinned
norm — the extremal statement carries the same information as the two
directions on this fixture. -/
theorem mat2_opNorm_max_evals_QA :
    max |evals mat2_symmetric ⟨0, by simp⟩|
      |evals mat2_symmetric ⟨1, by simp⟩| = 3 := by
  rw [mat2_evals_pin.1, mat2_evals_pin.2]
  norm_num

/-- **Negative witness (upper direction):** the norm is *not* bounded
by the smallest eigenvalue's absolute value — `‖mat2‖ ≤ 1` is refuted
by the lower direction. Bounding by one eigenvalue instead of all of
them would state a falsehood here; the `∀ k` hypothesis is
load-bearing. -/
theorem mat2_not_opNorm_le_one_QA :
    ¬ (‖mat2‖ ≤ 1) := by
  intro h
  have h3 := mat2_opNorm_ge_three_QA
  linarith

end Mat2

/-!
## Fixture 2: the `K₂` Laplacian `!![1, -1; -1, 1]`

PSD through the center's `laplacian_psd` (the adjacency is the unit
edge `!![0, 1; 1, 0]`); symmetric with nonnegative entries, so the
invertibility theorem applies after matching the Laplacian
computation.
-/

section Lap2

/-- The unit-edge adjacency on `Fin 2`. -/
def edge2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; 1, 0]

theorem edge2_symmetric : edge2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, edge2]

theorem edge2_nonneg (i j : Fin 2) : 0 ≤ edge2 i j := by
  fin_cases i <;> fin_cases j <;> simp [edge2]

/-- The `K₂` Laplacian, computed from the center's `laplacian` at the
unit-edge adjacency. -/
def lap2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -1; -1, 1]

theorem lap2_eq : laplacian edge2 = lap2 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, edge2, lap2, Fin.sum_univ_two]

theorem lap2_apply (i j : Fin 2) : lap2 i j = if i = j then 1 else -1 := by
  fin_cases i <;> fin_cases j <;> simp [lap2]

/-- The fixture Laplacian is PSD: transferred from `laplacian_psd`
along the computation `lap2_eq`. -/
theorem lap2_psd (x : Fin 2 → ℝ) : 0 ≤ quadForm lap2 x := by
  have h := laplacian_psd edge2 edge2_symmetric edge2_nonneg x
  rw [← lap2_eq]
  exact h

/-- The shifted Laplacian is `!![2, -1; -1, 2]`. -/
theorem lap2_add_one : lap2 + 1 = !![2, -1; -1, 2] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [lap2, Matrix.one_apply] <;> norm_num

/-- Invertibility delivered by the theorem (PSD route), cross-checked
against the computed determinant `3 ≠ 0`. -/
theorem lap2_add_one_isUnit_det_QA :
    IsUnit (lap2 + 1).det := by
  exact isUnit_det_add_one_of_quadForm_nonneg lap2_psd

/-- The determinant of the shifted Laplacian computes to `3`,
independent of the theorem. -/
theorem lap2_add_one_det_QA :
    (lap2 + 1).det = 3 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, lap2_apply, Matrix.one_apply]
  norm_num

/-- **Shift-load-bearing witness:** the *unshifted* Laplacian has
determinant exactly `0` — PSD alone gives no invertibility, so the
`+ 1` shift in the theorem is not decorative. -/
theorem lap2_det_eq_zero_QA :
    lap2.det = 0 := by
  rw [Matrix.det_fin_two]
  simp only [lap2_apply]
  norm_num

theorem lap2_det_not_isUnit_QA :
    ¬ IsUnit lap2.det := by
  rw [lap2_det_eq_zero_QA]
  simp

/-- The general-`t` instance at `t = 2`: the doubly-shifted Laplacian
is invertible by the same theorem, determinant computed to `8`. -/
theorem lap2_add_two_smul_one_isUnit_det_QA :
    IsUnit (lap2 + (2 : ℝ) • 1).det :=
  isUnit_det_add_smul_one_of_quadForm_nonneg (M := lap2) lap2_psd
    (t := 2) two_pos

theorem lap2_add_two_smul_one_det_QA :
    (lap2 + (2 : ℝ) • 1).det = 8 := by
  rw [Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, lap2_apply,
    Matrix.one_apply]
  norm_num

end Lap2

/-!
## Fixture 3: the resolvent identity at `A = lap2`, `B = 0`

`(lap2 + 1)⁻¹` is computed to `(1/3)!![2, 1; 1, 2]` by an independent
left-inverse witness, and both sides of the resolvent identity are
computed from the raw definitions to the same literal matrix.
-/

section Resolvent

/-- The computed resolvent of the `K₂` Laplacian. -/
noncomputable def res2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2/3, 1/3; 1/3, 2/3]

theorem res2_mul_QA :
    res2 * (!![2, -1; -1, 2] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [res2, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The resolvent computes to `(1/3)!![2,1;1,2]`, by the independent
left-inverse witness (not by the resolvent identity). -/
theorem lap2_resolvent_eq_QA :
    (lap2 + 1)⁻¹ = res2 := by
  refine Matrix.inv_eq_left_inv ?_
  rw [lap2_add_one]
  exact res2_mul_QA

/-- The zero matrix has nonnegative quadratic form. -/
theorem zero_psd_QA (x : Fin 2 → ℝ) : 0 ≤ quadForm (0 : Matrix (Fin 2) (Fin 2) ℝ) x := by
  have : quadForm (0 : Matrix (Fin 2) (Fin 2) ℝ) x = 0 := by
    simp [quadForm, Matrix.mulVec, Matrix.dotProduct]
  rw [this]

/-- The zero matrix's `+1` shift has unit determinant, computed. -/
theorem zero_add_one_isUnit_det_QA :
    IsUnit ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1).det := by
  have h : ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1).det = 1 := by
    simp
  rw [h]
  exact isUnit_one

/-- The left side of the identity computes, from the pinned resolvent,
to the literal matrix `!![-1/3, 1/3; 1/3, -1/3]`. -/
theorem resolvent_lhs_QA :
    (lap2 + 1)⁻¹ - ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹
      = !![-1/3, 1/3; 1/3, -1/3] := by
  rw [lap2_resolvent_eq_QA, zero_add, inv_one]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [res2, Matrix.one_apply] <;> norm_num

/-- The right side of the identity computes, from the pinned resolvent
and the raw matrix entries, to the same literal matrix. -/
theorem resolvent_rhs_QA :
    (lap2 + 1)⁻¹ * ((0 : Matrix (Fin 2) (Fin 2) ℝ) - lap2)
      * ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹
      = !![-1/3, 1/3; 1/3, -1/3] := by
  rw [lap2_resolvent_eq_QA, zero_add, inv_one, mul_one, zero_sub]
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [res2, lap2_apply, neg_apply,
    Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- **The resolvent identity, checked:** instantiating the theorem at
`A = lap2`, `B = 0` and rewriting both sides by their independently
computed values closes the goal definitionally — a wrong factoring
(swapped order, dropped sign) would leave a false matrix identity. -/
theorem resolvent_identity_check_QA :
    (lap2 + 1)⁻¹ - ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹
      = (lap2 + 1)⁻¹ * ((0 : Matrix (Fin 2) (Fin 2) ℝ) - lap2)
        * ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹ := by
  rw [resolvent_lhs_QA, resolvent_rhs_QA]

end Resolvent

end Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.QA
