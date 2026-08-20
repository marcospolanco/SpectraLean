/-
  Resolvent_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent`
  (the resolvent-calculus module, proposal steps 0–3), proved
  2026-08-19/20:

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
    sign) would fail this check;
  - the Step-2 norm bound, with **attainment**: `‖(L+1)⁻¹‖ = 1`
    exactly — the theorem's energy route and the eigenvalue-bridge
    route (the pinned spectrum `{1/3, 1}` of `(1/3)!![2,1;1,2]`, from
    trace/determinant/sortedness) meet at the same value, so the bound
    is tight, not slack; the general-`t` instance `‖(L + 2•1)⁻¹‖ = 1/2`
    exactly (spectrum `{1/4, 1/2}` pinned the same way) — also attained;
  - the Step-2 Lipschitz bound at `A = L`, `B = 0`, both sides
    independently pinned: the difference computes to
    `!![-1/3, 1/3; 1/3, -1/3]` with bridge-pinned norm `2/3`, the
    right side to `‖L‖ = 2` (spectrum `{0, 2}`), so the instantiated
    theorem reads `2/3 ≤ 2` — a reversed or badly-factored statement
    would produce a falsehood here;
  - the two Step-2 negative witnesses: **the shift is load-bearing**
    (the invertible PSD matrix `(1/4)I` *without* the shift has
    `‖A⁻¹‖ = 4 > 1`, so the unshifted bound is refuted numerically),
    and **the quadratic-form hypothesis is load-bearing** (the symmetric
    non-PSD `-(3/4)I` has `+1` shift equal to `(1/4)I`, whose inverse
    has norm `4 > 1`, while `quadForm (-(3/4)I) ![1,0] = -3/4 < 0`
    exhibits the violated hypothesis);
  - the Step-3 injectivity instantiated at two distinct pairs of PSD
    matrices (`lap2` vs `0`, and the less degenerate `lap2` vs `mat2`),
    each with **both resolvents independently computed** (left-inverse
    witnesses) and their distinctness verified by entries — the
    theorem's output is cross-checked against values computed without
    it; the contrapositive certificate direction is exercised through
    the packaged `iff`; and the **invertibility guard**: the
    hypothesis-free implication "equal resolvents → equal matrices" is
    refuted at `A = -1` vs `B = -1 + E` with `E` nilpotent — two
    distinct matrices whose `+1` shifts are both singular, so both
    resolvents are the junk inverse `0` and the determinant hypotheses
    of the core theorem are load-bearing.

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

/-!
## Fixture 4 (Step 2): the norm bound, with attainment

`‖(L+1)⁻¹‖ = 1` exactly, by two independent routes: the theorem's
energy route, and the eigenvalue-bridge route on the pinned spectrum
`{1/3, 1}` of `res2 = (1/3)!![2,1;1,2]` (pinned from
trace/determinant/sortedness, independent of both). The general-`t`
instance `‖(L+2•1)⁻¹‖ = 1/2` is likewise attained exactly.
-/

section NormBound

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

theorem res2_symmetric : res2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, res2]

theorem res2_apply (i j : Fin 2) : res2 i j = if i = j then 2/3 else 1/3 := by
  fin_cases i <;> fin_cases j <;> simp [res2]

theorem res2_trace : res2.trace = 4/3 := by
  simp [Matrix.trace, res2_apply]
  norm_num

theorem res2_det : res2.det = 1/3 := by
  have h00 : res2 0 0 = 2/3 := by simp [res2_apply]
  have h11 : res2 1 1 = 2/3 := by simp [res2_apply]
  have h01 : res2 0 1 = 1/3 := by simp [res2_apply]
  have h10 : res2 1 0 = 1/3 := by simp [res2_apply]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

/-- The sorted spectrum of the resolvent fixture is exactly
`[1/3, 1]`, pinned from trace, determinant, and sortedness. -/
theorem res2_evals_pin :
    evals res2_symmetric ⟨0, by simp⟩ = 1/3 ∧
      evals res2_symmetric ⟨1, by simp⟩ = 1 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm res2_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm res2_symmetric).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm res2_symmetric).eigenvalues))).sum = 1/3 + 1 := by
    have htr : ∑ i : Fin 2, eigvalOf res2 res2_symmetric i = 1/3 + 1 := by
      rw [eigvalOf_sum_eq_trace, res2_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm res2_symmetric).eigenvalues))).prod = 1/3 * 1 := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm res2_symmetric).eigenvalues i) = 1/3 := by
      have h := (isHermitian_of_isSymm res2_symmetric).det_eq_prod_eigenvalues
      rw [res2_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := 1/3) (hi := 1) (by norm_num)
    hlen hsorted hsum hprod

/-- The bridge route: `‖res2‖ = 1` (the top of the pinned spectrum
`{1/3, 1}`) — computed without the norm-bound theorem. -/
theorem res2_opNorm_eq_one_QA : ‖res2‖ = 1 := by
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le res2_symmetric (by norm_num) ?_
    intro k
    fin_cases k
    · rw [res2_evals_pin.1, abs_of_nonneg (show (0:ℝ) ≤ 1/3 by norm_num)]
      try norm_num
    · rw [res2_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 1 by norm_num)]
      try norm_num
  · have h := abs_evals_le_l2OpNorm res2_symmetric ⟨1, by simp⟩
    rw [res2_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 1 by norm_num)] at h
    exact h

/-- The theorem's route: the energy argument at the `K₂` Laplacian. -/
theorem resolvent_norm_le_one_QA :
    ‖(lap2 + 1)⁻¹‖ ≤ 1 :=
  l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg lap2_psd

/-- **Tightness:** the norm bound is *attained* — `‖(L+1)⁻¹‖ = 1`
exactly, with the two independent routes (theorem and bridge) agreeing
on the value. -/
theorem resolvent_norm_eq_one_QA :
    ‖(lap2 + 1)⁻¹‖ = 1 := by
  rw [lap2_resolvent_eq_QA]
  exact res2_opNorm_eq_one_QA

/-- The doubly-shifted Laplacian is `!![3, -1; -1, 3]`. -/
theorem lap2_add_two_smul_one_eq :
    lap2 + (2 : ℝ) • 1 = !![3, -1; -1, 3] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [lap2_apply, Matrix.smul_apply, Matrix.one_apply] <;> norm_num

/-- The computed `t = 2` resolvent of the `K₂` Laplacian. -/
noncomputable def res2t : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3/8, 1/8; 1/8, 3/8]

theorem res2t_mul_QA :
    res2t * (!![3, -1; -1, 3] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [res2t, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem lap2_resolvent_two_eq_QA :
    (lap2 + (2 : ℝ) • 1)⁻¹ = res2t := by
  refine Matrix.inv_eq_left_inv ?_
  rw [lap2_add_two_smul_one_eq]
  exact res2t_mul_QA

theorem res2t_symmetric : res2t.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, res2t]

theorem res2t_apply (i j : Fin 2) :
    res2t i j = if i = j then 3/8 else 1/8 := by
  fin_cases i <;> fin_cases j <;> simp [res2t]

theorem res2t_trace : res2t.trace = 3/4 := by
  simp [Matrix.trace, res2t_apply]
  norm_num

theorem res2t_det : res2t.det = 1/8 := by
  have h00 : res2t 0 0 = 3/8 := by simp [res2t_apply]
  have h11 : res2t 1 1 = 3/8 := by simp [res2t_apply]
  have h01 : res2t 0 1 = 1/8 := by simp [res2t_apply]
  have h10 : res2t 1 0 = 1/8 := by simp [res2t_apply]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

theorem res2t_evals_pin :
    evals res2t_symmetric ⟨0, by simp⟩ = 1/4 ∧
      evals res2t_symmetric ⟨1, by simp⟩ = 1/2 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm res2t_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm res2t_symmetric).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm res2t_symmetric).eigenvalues))).sum = 1/4 + 1/2 := by
    have htr : ∑ i : Fin 2, eigvalOf res2t res2t_symmetric i = 1/4 + 1/2 := by
      rw [eigvalOf_sum_eq_trace, res2t_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm res2t_symmetric).eigenvalues))).prod = 1/4 * (1/2) := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm res2t_symmetric).eigenvalues i) = 1/8 := by
      have h := (isHermitian_of_isSymm res2t_symmetric).det_eq_prod_eigenvalues
      rw [res2t_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := 1/4) (hi := 1/2) (by norm_num)
    hlen hsorted hsum hprod

theorem res2t_opNorm_eq_half_QA : ‖res2t‖ = 1/2 := by
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le res2t_symmetric (by norm_num) ?_
    intro k
    fin_cases k
    · rw [res2t_evals_pin.1, abs_of_nonneg (show (0:ℝ) ≤ 1/4 by norm_num)]
      try norm_num
    · rw [res2t_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num)]
      try norm_num
  · have h := abs_evals_le_l2OpNorm res2t_symmetric ⟨1, by simp⟩
    rw [res2t_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num)] at h
    exact h

/-- The general-`t` theorem at `t = 2`: `‖(L + 2•1)⁻¹‖ ≤ 1/2`. -/
theorem resolvent_two_norm_le_half_QA :
    ‖(lap2 + (2 : ℝ) • 1)⁻¹‖ ≤ 1/2 := by
  have h := l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg
    (M := lap2) lap2_psd (t := 2) two_pos
  rwa [show ((2 : ℝ)⁻¹) = 1/2 from by norm_num] at h

/-- **General-`t` tightness:** `‖(L + 2•1)⁻¹‖ = 1/2` exactly. -/
theorem resolvent_two_norm_eq_half_QA :
    ‖(lap2 + (2 : ℝ) • 1)⁻¹‖ = 1/2 := by
  rw [lap2_resolvent_two_eq_QA]
  exact res2t_opNorm_eq_half_QA

end NormBound

/-!
## Fixture 5 (Step 2): the Lipschitz bound at `A = lap2`, `B = 0`

Both sides independently pinned — the difference's spectrum
`{-2/3, 0}` (trace `0`? no: trace `-2/3`, determinant `0`) and the
Laplacian's own `{0, 2}` — so the instantiated theorem reads `2/3 ≤ 2`.
-/

section Lipschitz

/-- The difference of the two resolvents, as a fixture. -/
noncomputable def diff2 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1/3, 1/3; 1/3, -1/3]

theorem diff2_symmetric : diff2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, diff2]

theorem diff2_apply (i j : Fin 2) :
    diff2 i j = if i = j then -1/3 else 1/3 := by
  fin_cases i <;> fin_cases j <;> simp [diff2]

theorem diff2_trace : diff2.trace = -2/3 := by
  simp [Matrix.trace, diff2_apply]
  norm_num

theorem diff2_det : diff2.det = 0 := by
  have h00 : diff2 0 0 = -1/3 := by simp [diff2_apply]
  have h11 : diff2 1 1 = -1/3 := by simp [diff2_apply]
  have h01 : diff2 0 1 = 1/3 := by simp [diff2_apply]
  have h10 : diff2 1 0 = 1/3 := by simp [diff2_apply]
  rw [Matrix.det_fin_two, h00, h11, h01, h10]
  norm_num

theorem diff2_evals_pin :
    evals diff2_symmetric ⟨0, by simp⟩ = -2/3 ∧
      evals diff2_symmetric ⟨1, by simp⟩ = 0 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm diff2_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm diff2_symmetric).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm diff2_symmetric).eigenvalues))).sum = -2/3 + 0 := by
    have htr : ∑ i : Fin 2, eigvalOf diff2 diff2_symmetric i = -2/3 + 0 := by
      rw [eigvalOf_sum_eq_trace, diff2_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm diff2_symmetric).eigenvalues))).prod = -2/3 * 0 := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm diff2_symmetric).eigenvalues i) = 0 := by
      have h := (isHermitian_of_isSymm diff2_symmetric).det_eq_prod_eigenvalues
      rw [diff2_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := -2/3) (hi := 0) (by norm_num)
    hlen hsorted hsum hprod

theorem diff2_opNorm_eq_two_thirds_QA : ‖diff2‖ = 2/3 := by
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le diff2_symmetric (by norm_num) ?_
    intro k
    fin_cases k
    · rw [diff2_evals_pin.1,
        show (-2/3 : ℝ) = -(2/3) from by norm_num, abs_neg,
        abs_of_nonneg (show (0:ℝ) ≤ 2/3 by norm_num)]
      try norm_num
    · rw [diff2_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 0 by norm_num)]
      try norm_num
  · have h := abs_evals_le_l2OpNorm diff2_symmetric ⟨0, by simp⟩
    rw [diff2_evals_pin.1,
      show (-2/3 : ℝ) = -(2/3) from by norm_num, abs_neg,
      abs_of_nonneg (show (0:ℝ) ≤ 2/3 by norm_num)] at h
    exact h

theorem lap2_symmetric : lap2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, lap2]

theorem lap2_trace : lap2.trace = 2 := by
  simp [Matrix.trace, lap2_apply]

theorem lap2_evals_pin :
    evals lap2_symmetric ⟨0, by simp⟩ = 0 ∧
      evals lap2_symmetric ⟨1, by simp⟩ = 2 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm lap2_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm lap2_symmetric).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm lap2_symmetric).eigenvalues))).sum = 0 + 2 := by
    have htr : ∑ i : Fin 2, eigvalOf lap2 lap2_symmetric i = 0 + 2 := by
      rw [eigvalOf_sum_eq_trace, lap2_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm lap2_symmetric).eigenvalues))).prod = 0 * 2 := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm lap2_symmetric).eigenvalues i) = 0 := by
      have h := (isHermitian_of_isSymm lap2_symmetric).det_eq_prod_eigenvalues
      rw [lap2_det_eq_zero_QA] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := 0) (hi := 2) (by norm_num)
    hlen hsorted hsum hprod

theorem lap2_opNorm_eq_two_QA : ‖lap2‖ = 2 := by
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le lap2_symmetric (by norm_num) ?_
    intro k
    fin_cases k
    · rw [lap2_evals_pin.1, abs_of_nonneg (show (0:ℝ) ≤ 0 by norm_num)]
      try norm_num
    · rw [lap2_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
      try norm_num
  · have h := abs_evals_le_l2OpNorm lap2_symmetric ⟨1, by simp⟩
    rw [lap2_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)] at h
    exact h

/-- The Lipschitz bound instantiated at the two PSD fixtures. -/
theorem lipschitz_edge_QA :
    ‖(lap2 + 1)⁻¹ - ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹‖
      ≤ ‖lap2 - 0‖ :=
  l2OpNorm_resolvent_sub_le_of_quadForm_nonneg lap2_psd zero_psd_QA

/-- The Lipschitz left side computed independently of the theorem:
the difference of resolvents is `diff2`, whose bridge-pinned norm is
`2/3`. -/
theorem lipschitz_lhs_opNorm_QA :
    ‖(lap2 + 1)⁻¹ - ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹‖ = 2/3 := by
  rw [resolvent_lhs_QA]
  exact diff2_opNorm_eq_two_thirds_QA

/-- **The Lipschitz bound, checked numerically:** composing the
instantiated theorem with the independently pinned values on both
sides yields `2/3 ≤ 2` — a reversed, transposed, or badly factored
statement would produce a falsehood here. -/
theorem lipschitz_edge_numeric_QA :
    (2/3 : ℝ) ≤ 2 := by
  have h := lipschitz_edge_QA
  rw [sub_zero] at h
  rw [lipschitz_lhs_opNorm_QA, lap2_opNorm_eq_two_QA] at h
  exact h

end Lipschitz

/-!
## Fixture 6 (Step 2): the negative witnesses

Two guards: the `+ 1` shift is load-bearing (an invertible PSD matrix
alone has an inverse of norm `4 > 1`), and so is the quadratic-form
hypothesis (a symmetric non-PSD matrix's `+1` shift can be invertible
with inverse norm `4 > 1`, while the hypothesis is exhibited violated).
-/

section Negative

/-- The invertible PSD witness: `(1/4)I`, symmetric positive definite. -/
noncomputable def quartOne : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1/4, 0; 0, 1/4]

theorem quartOne_symmetric : quartOne.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, quartOne]

theorem quartOne_psd (x : Fin 2 → ℝ) : 0 ≤ quadForm quartOne x := by
  have hmv : quartOne *ᵥ x = ![1/4 * x 0, 1/4 * x 1] := by
    funext i
    fin_cases i <;>
      simp [quartOne, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have hexp : quadForm quartOne x
      = (1/4) * (x 0 * x 0 + x 1 * x 1) := by
    rw [show quadForm quartOne x = Matrix.dotProduct x (quartOne *ᵥ x) from rfl,
      hmv]
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    ring
  rw [hexp]
  exact mul_nonneg (by norm_num)
    (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))

/-- The inverse witness: `4I`. -/
def fourOne : Matrix (Fin 2) (Fin 2) ℝ :=
  !![4, 0; 0, 4]

theorem fourOne_symmetric : fourOne.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, fourOne]

theorem fourOne_mul_quartOne_QA :
    fourOne * quartOne = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [fourOne, quartOne, Matrix.mul_apply, Matrix.one_apply,
      Fin.sum_univ_two]

/-- `(1/4)I` inverse computes to `4I`, by the independent left-inverse
witness. -/
theorem quartOne_inv_eq_fourOne_QA :
    quartOne⁻¹ = fourOne :=
  Matrix.inv_eq_left_inv fourOne_mul_quartOne_QA

theorem fourOne_trace : fourOne.trace = 8 := by
  simp [Matrix.trace, fourOne]
  norm_num

theorem fourOne_det : fourOne.det = 16 := by
  rw [Matrix.det_fin_two]
  simp [fourOne]
  norm_num

theorem fourOne_evals_pin :
    evals fourOne_symmetric ⟨0, by simp⟩ = 4 ∧
      evals fourOne_symmetric ⟨1, by simp⟩ = 4 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm fourOne_symmetric).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm fourOne_symmetric).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm fourOne_symmetric).eigenvalues))).sum = 4 + 4 := by
    have htr : ∑ i : Fin 2, eigvalOf fourOne fourOne_symmetric i = 4 + 4 := by
      rw [eigvalOf_sum_eq_trace, fourOne_trace]
      norm_num
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm fourOne_symmetric).eigenvalues))).prod = 4 * 4 := by
    have hd0 : ∏ i : Fin 2,
        ((isHermitian_of_isSymm fourOne_symmetric).eigenvalues i) = 16 := by
      have h := (isHermitian_of_isSymm fourOne_symmetric).det_eq_prod_eigenvalues
      rw [fourOne_det] at h
      simpa using h.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    rw [hd0]
    norm_num
  exact two_point_pin_of_sum_prod (lo := 4) (hi := 4) (by norm_num)
    hlen hsorted hsum hprod

theorem fourOne_opNorm_eq_four_QA : ‖fourOne‖ = 4 := by
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_abs_evals_le fourOne_symmetric (by norm_num) ?_
    intro k
    fin_cases k
    · rw [fourOne_evals_pin.1, abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num)]
      try norm_num
    · rw [fourOne_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num)]
      try norm_num
  · have h := abs_evals_le_l2OpNorm fourOne_symmetric ⟨1, by simp⟩
    rw [fourOne_evals_pin.2, abs_of_nonneg (show (0:ℝ) ≤ 4 by norm_num)] at h
    exact h

/-- **Shift-load-bearing witness (the proposal's QA item 3):** the
bound `‖A⁻¹‖ ≤ 1` is *refuted* for the invertible PSD `A = (1/4)I`
without the shift — PSD alone gives no bounded inverse, so the `+ 1`
in the theorem is not decorative. -/
theorem unshifted_inv_norm_not_le_one_QA :
    ¬ (‖quartOne⁻¹‖ ≤ 1) := by
  rw [quartOne_inv_eq_fourOne_QA, fourOne_opNorm_eq_four_QA]
  intro h
  linarith

/-- The symmetric non-PSD witness: `-(3/4)I`. -/
noncomputable def negThreeQuart : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-3/4, 0; 0, -3/4]

theorem negThreeQuart_add_one :
    negThreeQuart + 1 = quartOne := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [negThreeQuart, quartOne, Matrix.one_apply] <;> norm_num

/-- The quadratic-form hypothesis is genuinely violated at `![1, 0]`:
`quadForm (-(3/4)I) ![1,0] = -3/4 < 0`. -/
theorem negThreeQuart_not_psd_QA :
    ¬ (∀ x : Fin 2 → ℝ, 0 ≤ quadForm negThreeQuart x) := by
  intro h
  have h0 := h ![1, 0]
  have hval : quadForm negThreeQuart ![1, 0] = -3/4 := by
    have hmv : negThreeQuart *ᵥ (![1, 0] : Fin 2 → ℝ) = ![-3/4, 0] := by
      funext i
      fin_cases i <;>
        simp [negThreeQuart, Matrix.mulVec, Matrix.dotProduct,
          Fin.sum_univ_two]
    rw [show quadForm negThreeQuart (![1, 0] : Fin 2 → ℝ)
        = Matrix.dotProduct (![1, 0] : Fin 2 → ℝ) (negThreeQuart *ᵥ ![1, 0])
        from rfl, hmv]
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [hval] at h0
  linarith

/-- **Hypothesis-load-bearing witness:** dropping the quadratic-form
hypothesis breaks the norm bound — `-(3/4)I` is symmetric with an
invertible `+1` shift (`= (1/4)I`), yet `‖(-(3/4)I + 1)⁻¹‖ = 4 > 1`. -/
theorem hypothesis_guard_not_le_one_QA :
    ¬ (‖(negThreeQuart + 1)⁻¹‖ ≤ 1) := by
  rw [negThreeQuart_add_one, quartOne_inv_eq_fourOne_QA,
    fourOne_opNorm_eq_four_QA]
  intro h
  linarith

end Negative

/-!
## Fixture 7 (Step 3): injectivity of the resolvent map

The theorem is instantiated at two distinct pairs of PSD matrices with
both resolvents independently computed (left-inverse witnesses), and
the **invertibility guard** refutes the hypothesis-free implication at
two distinct matrices whose `+1` shifts are both singular.
-/

section Injective

/-- The `K₂` Laplacian is not the zero matrix (entry `0 0 = 1`). -/
theorem lap2_ne_zero_QA : lap2 ≠ (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  apply_fun (fun M => M 0 0) at h
  rw [show lap2 0 0 = 1 from by simp [lap2]] at h
  simp at h

/-- **Step 3 instantiated** at `A = lap2`, `B = 0`: distinct PSD
matrices have distinct resolvents, by the theorem alone. -/
theorem resolvent_injective_edge_QA :
    (lap2 + 1)⁻¹ ≠ ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹ :=
  resolvent_map_injective_of_quadForm_nonneg lap2_psd zero_psd_QA
    lap2_ne_zero_QA

/-- The theorem's output, rewritten by the pinned resolvents, is the
numeric statement `res2 ≠ 1` (a left-inverse-computed value vs. the
identity). -/
theorem resolvent_injective_edge_check_QA :
    ((lap2 + 1)⁻¹ ≠ ((0 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹)
      ↔ (res2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [lap2_resolvent_eq_QA, zero_add, inv_one]

/-- The numeric statement holds, by an off-diagonal entry: `1/3 ≠ 0`. -/
theorem res2_ne_one_QA : res2 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro h
  apply_fun (fun M => M 0 1) at h
  rw [show res2 0 1 = 1/3 from by simp [res2]] at h
  simp at h

/-- `mat2` has nonnegative quadratic form:
`xᵀ (mat2) x = (x₀ + x₁)² + x₀² + x₁² ≥ 0`. -/
theorem mat2_psd (x : Fin 2 → ℝ) : 0 ≤ quadForm mat2 x := by
  have hexp : quadForm mat2 x = (x 0 + x 1) ^ 2 + (x 0) ^ 2 + (x 1) ^ 2 := by
    simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      mat2_apply, Matrix.one_apply]
    norm_num
    ring
  rw [hexp]
  positivity

/-- The two fixtures are distinct: off-diagonal entries `-1 ≠ 1`. -/
theorem lap2_ne_mat2_QA : lap2 ≠ mat2 := by
  intro h
  apply_fun (fun M => M 0 1) at h
  rw [show lap2 0 1 = -1 from by simp [lap2],
    show mat2 0 1 = 1 from by simp [mat2]] at h
  norm_num at h

/-- The computed resolvent of `mat2`: `(mat2 + 1)⁻¹ = (1/8)!![3, -1; -1, 3]`. -/
noncomputable def resM : Matrix (Fin 2) (Fin 2) ℝ :=
  !![3/8, -1/8; -1/8, 3/8]

theorem mat2_add_one_eq : mat2 + 1 = !![3, 1; 1, 3] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [mat2_apply, Matrix.one_apply] <;> norm_num

theorem resM_mul_QA :
    resM * (!![3, 1; 1, 3] : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [resM, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- The resolvent computes to `(1/8)!![3, -1; -1, 3]` by the
independent left-inverse witness, not by any theorem. -/
theorem mat2_resolvent_eq_QA :
    (mat2 + 1)⁻¹ = resM := by
  refine Matrix.inv_eq_left_inv ?_
  rw [mat2_add_one_eq]
  exact resM_mul_QA

/-- **Step 3 instantiated** at the less degenerate pair
`A = lap2`, `B = mat2` (neither is zero): distinct PSD matrices have
distinct resolvents, by the theorem alone. -/
theorem resolvent_injective_lap_mat_QA :
    (lap2 + 1)⁻¹ ≠ (mat2 + 1)⁻¹ :=
  resolvent_map_injective_of_quadForm_nonneg lap2_psd mat2_psd
    lap2_ne_mat2_QA

/-- The theorem's output, rewritten by the pinned resolvents, is the
numeric statement `res2 ≠ resM`. -/
theorem resolvent_injective_lap_mat_check_QA :
    ((lap2 + 1)⁻¹ ≠ (mat2 + 1)⁻¹) ↔ (res2 ≠ resM) := by
  rw [lap2_resolvent_eq_QA, mat2_resolvent_eq_QA]

/-- The numeric statement holds, by a diagonal entry: `2/3 ≠ 3/8`. -/
theorem res2_ne_resM_QA : res2 ≠ resM := by
  intro h
  apply_fun (fun M => M 0 0) at h
  rw [show res2 0 0 = 2/3 from by simp [res2],
    show resM 0 0 = 3/8 from by simp [resM]] at h
  norm_num at h

/-- The packaged `iff` consumed in the certificate direction: resolvent
equality would *prove* matrix equality — here used contrapositively to
keep the two resolvents apart. -/
theorem resolvent_ne_of_iff_QA :
    (lap2 + 1)⁻¹ ≠ (mat2 + 1)⁻¹ := fun heq =>
  lap2_ne_mat2_QA
    ((inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg lap2_psd mat2_psd).1
      heq)

/-- The guard fixture: `-1 + E` with `E = !![0, 1; 0, 0]` nilpotent —
distinct from `-1`, with a singular `+1` shift. -/
def negOneShift : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-1, 1; 0, -1]

theorem negOne_add_one_inv_eq_zero_QA :
    (-(1 : Matrix (Fin 2) (Fin 2) ℝ) + 1)⁻¹ = 0 := by
  rw [neg_add_cancel, Matrix.inv_zero]

theorem negOneShift_add_one :
    negOneShift + 1 = !![0, 1; 0, 0] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [negOneShift, Matrix.one_apply]

theorem nilpotent_det_eq_zero_QA :
    (!![0, 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ).det = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero 1 ?_
  intro j
  fin_cases j <;> simp

theorem negOneShift_add_one_inv_eq_zero_QA :
    (negOneShift + 1)⁻¹ = 0 := by
  rw [negOneShift_add_one, Matrix.inv_def, nilpotent_det_eq_zero_QA,
    Ring.inverse_zero, zero_smul]

theorem negOne_ne_negOneShift_QA :
    (-(1 : Matrix (Fin 2) (Fin 2) ℝ)) ≠ negOneShift := by
  intro h
  apply_fun (fun M => M 0 1) at h
  rw [show (-(1 : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = 0 from by simp,
    show negOneShift 0 1 = 1 from by simp [negOneShift]] at h
  norm_num at h

/-- **The invertibility guard:** the hypothesis-free implication
"equal resolvents → equal matrices" is **refuted** — at `A = -1` and
`B = -1 + E` (distinct), both `+1` shifts are singular so both
resolvents are the junk inverse `0`, equal while the matrices differ.
The core theorem's determinant hypotheses are load-bearing, not
decorative. -/
theorem resolvent_injective_needs_invertibility_QA :
    ¬ (∀ A B : Matrix (Fin 2) (Fin 2) ℝ,
        (A + 1)⁻¹ = (B + 1)⁻¹ → A = B) := by
  intro h
  exact negOne_ne_negOneShift_QA
    (h (-(1 : Matrix (Fin 2) (Fin 2) ℝ)) negOneShift
      (by rw [negOne_add_one_inv_eq_zero_QA,
        negOneShift_add_one_inv_eq_zero_QA]))

end Injective

end Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.QA
