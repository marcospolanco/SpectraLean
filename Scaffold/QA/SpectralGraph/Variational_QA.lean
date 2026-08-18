/-
  Variational_QA.lean

  Purpose
  -------
  QA lemmas for the Rayleigh quotient interface of
  `Scaffold.Mathlib.GraphTheory.Spectral`: nonnegativity on PSD
  operators, kernel vectors, and homogeneity — the pieces composed by
  the variational characterization of `λ₂` — together with QA for the
  characterization itself (`lambda2_variational`, proved since
  2026-08-18):

  - a refutation of the pre-repair axiom shape, which assumed only
    symmetry: on a negative-weight two-vertex graph it asserts
    `0 = -2`;
  - an exact instantiation on `K₂`, where `λ₂ = 2` is computed twice,
    once from trace/determinant/sortedness and once through the
    theorem from the independently computed Rayleigh side;
  - the disconnected instantiation `λ₂ = 0` on two disjoint edges;
  - the upper value pin `λ₂ ≤ 1` on the three-vertex path.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the characterization; it checks its interface and falsifies
  the retired shape.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The Rayleigh quotient has the documented junk value at the zero
vector. -/
theorem rayleigh_zero_QA (M : Matrix V V ℝ) : rayleigh M 0 = 0 := by
  simp [rayleigh]

/-- For a nonzero vector the Rayleigh denominator (a sum of squares) is
strictly positive. -/
theorem rayleigh_denominator_pos_QA {x : V → ℝ} (hx : x ≠ 0) :
    0 < Matrix.dotProduct x x := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hx (funext hcon)
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩

/-- For a PSD operator the Rayleigh quotient of any nonzero vector is
nonnegative. -/
theorem rayleigh_nonneg_psd_QA (M : Matrix V V ℝ)
    (hpsd : ∀ x : V → ℝ, 0 ≤ quadForm M x) (x : V → ℝ) (hx : x ≠ 0) :
    0 ≤ rayleigh M x := by
  rw [rayleigh, if_neg hx]
  exact div_nonneg (hpsd x) (rayleigh_denominator_pos_QA hx).le

/-- Kernel vectors have Rayleigh quotient zero. -/
theorem rayleigh_zero_in_kernel_QA (M : Matrix V V ℝ) (x : V → ℝ)
    (hx : x ≠ 0) (hker : M.mulVec x = 0) :
    rayleigh M x = 0 := by
  rw [rayleigh, if_neg hx, quadForm, hker, Matrix.dotProduct_zero, zero_div]

/-- The Rayleigh quotient is homogeneous of degree zero: rescaling the
vector by a nonzero constant leaves it unchanged. -/
theorem rayleigh_homogeneous_QA (M : Matrix V V ℝ) (x : V → ℝ) (c : ℝ)
    (hx : x ≠ 0) (hc : c ≠ 0) :
    rayleigh M (c • x) = rayleigh M x := by
  have hcx : c • x ≠ 0 := smul_ne_zero_iff.mpr ⟨hc, hx⟩
  have hc2 : c * c ≠ 0 := mul_ne_zero hc hc
  have hd : Matrix.dotProduct x x ≠ 0 :=
    ne_of_gt (rayleigh_denominator_pos_QA hx)
  rw [rayleigh, if_neg hcx, rayleigh, if_neg hx, quadForm, quadForm]
  simp only [Matrix.mulVec_smul, Matrix.smul_dotProduct,
    Matrix.dotProduct_smul, smul_eq_mul, mul_assoc]
  field_simp
  ring

/-!
## The variational characterization of λ₂ (proved) and the old,
symmetry-only shape, refuted

`lambda2_variational` is a theorem for symmetric nonnegative weights.
The nonnegativity hypothesis is load-bearing: with only symmetry the
statement is false, as the negative-weight fixture below shows in
proved form.
-/

section NegWeight

/-- Adjacency of the negative-weight two-vertex fixture: symmetric,
with a `-1` off-diagonal weight. -/
def negAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else -1

theorem negAdj_symmetric : negAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [negAdj]

/-- The Laplacian of the negative-weight fixture, entrywise `-1` on the
diagonal and `1` off it (negative row sums: the weights are negative). -/
theorem negAdj_laplacian_entry (i j : Fin 2) :
    laplacian negAdj i j = if i = j then -1 else 1 := by
  by_cases h : i = j
  · subst h
    have hdeg : deg negAdj i = -1 := by
      fin_cases i <;> simp [deg, negAdj, Fin.sum_univ_two]
    rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, hdeg]
    simp [negAdj]
  · rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ h, negAdj]
    simp [h]

theorem negAdj_laplacian_trace : (laplacian negAdj).trace = -2 := by
  simp [Matrix.trace, negAdj_laplacian_entry]

theorem negAdj_laplacian_det : (laplacian negAdj).det = 0 := by
  rw [Matrix.det_fin_two]
  have e01 : (0 : Fin 2) ≠ 1 := by decide
  have e10 : (1 : Fin 2) ≠ 0 := by decide
  simp [negAdj_laplacian_entry, e01, e10]

/-- The Rayleigh quotient of the negative-weight Laplacian is exactly
`-2` at every nonzero vector orthogonal to `onesVec` — a parametric
computation from the entries, independent of any spectral theorem. -/
theorem negAdj_rayleigh_of_orth (x : Fin 2 → ℝ) (hx0 : x ≠ 0)
    (hx : Matrix.dotProduct x onesVec = 0) :
    rayleigh (laplacian negAdj) x = -2 := by
  have hsum : x 0 + x 1 = 0 := by
    simpa [Matrix.dotProduct, onesVec, Fin.sum_univ_two] using hx
  have hx1 : x 1 = -x 0 := by linarith
  have hx0' : x 0 ≠ 0 := by
    intro h
    apply hx0
    funext i
    fin_cases i <;> simp [h, hx1]
  have hq : quadForm (laplacian negAdj) x = -(4 * x 0 ^ 2) := by
    simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      negAdj_laplacian_entry]
    norm_num
    rw [hx1]
    ring
  have hd : Matrix.dotProduct x x = 2 * x 0 ^ 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_two]
    rw [hx1]
    ring
  have hdne : (2 : ℝ) * x 0 ^ 2 ≠ 0 :=
    mul_ne_zero two_ne_zero (pow_ne_zero 2 hx0')
  rw [rayleigh, if_neg hx0, hq, hd, div_eq_iff hdne]
  ring

/-- Two-point sorted-list pin for the negative fixture: a sorted
two-element list with sum `-2` and product `0` is `[-2, 0]`. -/
private theorem two_point_pin_neg {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = -2)
    (hprod : l.prod = 0) :
    l.get ⟨1, by omega⟩ = 0 := by
  match l with
  | a :: b :: [] =>
    have hmono : a ≤ b := by
      have h := hs.rel_get_of_lt (show (0 : Fin 2) < 1 by decide)
      simpa using h
    simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
      List.prod_nil, mul_one] at hsum hprod
    show b = 0
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with h0 | h1
    · linarith
    · exact h1

/-- `λ₂` of the negative-weight fixture is `0`, from trace, determinant,
and sortedness — no axiom, no spectral-theorem computation. -/
theorem negAdj_lambda2_eq_zero :
    lambda2 negAdj negAdj_symmetric (le_refl 2) = 0 := by
  have hL := laplacian_symmetric negAdj negAdj_symmetric
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).sum = -2 := by
    have htr : ∑ i : Fin 2, eigvalOf (laplacian negAdj) hL i = -2 := by
      rw [eigvalOf_sum_eq_trace, negAdj_laplacian_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2, ((isHermitian_of_isSymm hL).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm hL).det_eq_prod_eigenvalues
      rw [negAdj_laplacian_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  show (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).get ⟨1, by omega⟩ = 0
  exact two_point_pin_neg hlen hsorted hsum hprod

/-- **Refutation of the pre-repair statement shape.** The
`lambda2_variational` axiom as admitted before 2026-08-18 assumed only
symmetry; on this negative-weight graph `λ₂ = 0` while the constraint
set's infimum is `-2` (every element is `-2` by the parametric
computation above), so the asserted equality reads `0 = -2`. The
`hnonneg` hypothesis of the proved theorem is load-bearing, and this
witness shows it. -/
theorem old_lambda2_variational_refuted_QA :
    ¬ (lambda2 negAdj negAdj_symmetric (le_refl 2) =
      sInf {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
        Matrix.dotProduct x onesVec = 0 ∧
        rayleigh (laplacian negAdj) x = r}) := by
  intro h
  have hall : ∀ r ∈ {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian negAdj) x = r}, r = -2 := by
    rintro r ⟨x, hx0, hxorth, rfl⟩
    exact negAdj_rayleigh_of_orth x hx0 hxorth
  have hwne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h1 : (![1, -1] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
    simp at h1
  have hworth : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) onesVec = 0 := by
    simp [Matrix.dotProduct, onesVec, Fin.sum_univ_two]
  have hmem : (-2 : ℝ) ∈ {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian negAdj) x = r} :=
    ⟨![1, -1], hwne, hworth, negAdj_rayleigh_of_orth _ hwne hworth⟩
  have hbd : BddBelow {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian negAdj) x = r} :=
    ⟨-2, fun r hr => by rw [hall r hr]⟩
  have hle : sInf {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian negAdj) x = r} ≤ -2 := csInf_le hbd hmem
  rw [negAdj_lambda2_eq_zero] at h
  rw [← h] at hle
  norm_num at hle

end NegWeight

/-!
### `K₂`: both sides of the characterization, computed independently
-/

section EdgeK2

/-- Adjacency of `K₂` (two-vertex edge, weight `1`). -/
def k2Adj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem k2Adj_symmetric : k2Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [k2Adj]

theorem k2Adj_nonneg : ∀ i j, 0 ≤ k2Adj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [k2Adj]

theorem k2Adj_laplacian_entry (i j : Fin 2) :
    laplacian k2Adj i j = if i = j then 1 else -1 := by
  by_cases h : i = j
  · subst h
    have hdeg : deg k2Adj i = 1 := by
      fin_cases i <;> simp [deg, k2Adj, Fin.sum_univ_two]
    rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, hdeg]
    simp [k2Adj]
  · rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ h, k2Adj]
    simp [h]

theorem k2_laplacian_trace : (laplacian k2Adj).trace = 2 := by
  simp [Matrix.trace, k2Adj_laplacian_entry]

theorem k2_laplacian_det : (laplacian k2Adj).det = 0 := by
  rw [Matrix.det_fin_two]
  have e01 : (0 : Fin 2) ≠ 1 := by decide
  have e10 : (1 : Fin 2) ≠ 0 := by decide
  simp [k2Adj_laplacian_entry, e01, e10]

/-- Two-point sorted-list pin for `K₂`: sorted, sum `2`, product `0`
gives the list `[0, 2]`. -/
private theorem two_point_pin_pos {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = 2)
    (hprod : l.prod = 0) :
    l.get ⟨1, by omega⟩ = 2 := by
  match l with
  | a :: b :: [] =>
    have hmono : a ≤ b := by
      have h := hs.rel_get_of_lt (show (0 : Fin 2) < 1 by decide)
      simpa using h
    simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
      List.prod_nil, mul_one] at hsum hprod
    show b = 2
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with h0 | h1
    · linarith
    · linarith

/-- `λ₂(K₂) = 2` from trace, determinant, and sortedness — the sorted
spectrum is `[0, 2]`. Independent of the variational theorem. -/
theorem k2_lambda2_eq_two :
    lambda2 k2Adj k2Adj_symmetric (le_refl 2) = 2 := by
  have hL := laplacian_symmetric k2Adj k2Adj_symmetric
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).sum = 2 := by
    have htr : ∑ i : Fin 2, eigvalOf (laplacian k2Adj) hL i = 2 := by
      rw [eigvalOf_sum_eq_trace, k2_laplacian_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2, ((isHermitian_of_isSymm hL).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm hL).det_eq_prod_eigenvalues
      rw [k2_laplacian_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  show (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm hL).eigenvalues))).get ⟨1, by omega⟩ = 2
  exact two_point_pin_pos hlen hsorted hsum hprod

/-- The Rayleigh quotient of the `K₂` Laplacian is exactly `2` at every
nonzero vector orthogonal to `onesVec` — parametric, independent of the
spectral side. -/
theorem k2_rayleigh_of_orth (x : Fin 2 → ℝ) (hx0 : x ≠ 0)
    (hx : Matrix.dotProduct x onesVec = 0) :
    rayleigh (laplacian k2Adj) x = 2 := by
  have hsum : x 0 + x 1 = 0 := by
    simpa [Matrix.dotProduct, onesVec, Fin.sum_univ_two] using hx
  have hx1 : x 1 = -x 0 := by linarith
  have hx0' : x 0 ≠ 0 := by
    intro h
    apply hx0
    funext i
    fin_cases i <;> simp [h, hx1]
  have hq : quadForm (laplacian k2Adj) x = 4 * x 0 ^ 2 := by
    simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      k2Adj_laplacian_entry]
    norm_num
    rw [hx1]
    ring
  have hd : Matrix.dotProduct x x = 2 * x 0 ^ 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_two]
    rw [hx1]
    ring
  have hdne : (2 : ℝ) * x 0 ^ 2 ≠ 0 :=
    mul_ne_zero two_ne_zero (pow_ne_zero 2 hx0')
  rw [rayleigh, if_neg hx0, hq, hd, div_eq_iff hdne]
  ring

/-- The constraint set's infimum on `K₂` is `2`: every element is `2`
and `2` is attained. -/
theorem k2_set_sInf_eq_two :
    sInf {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian k2Adj) x = r} = 2 := by
  have hall : ∀ r ∈ {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian k2Adj) x = r}, r = 2 := by
    rintro r ⟨x, hx0, hxorth, rfl⟩
    exact k2_rayleigh_of_orth x hx0 hxorth
  have hwne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h
    have h1 : (![1, -1] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
    simp at h1
  have hworth : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) onesVec = 0 := by
    simp [Matrix.dotProduct, onesVec, Fin.sum_univ_two]
  have hmem : (2 : ℝ) ∈ {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian k2Adj) x = r} :=
    ⟨![1, -1], hwne, hworth, k2_rayleigh_of_orth _ hwne hworth⟩
  have hbd : BddBelow {r : ℝ | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian k2Adj) x = r} :=
    ⟨2, fun r hr => by rw [hall r hr]⟩
  exact le_antisymm (csInf_le hbd hmem)
    (le_csInf ⟨2, hmem⟩ fun r hr => (hall r hr).ge)

/-- `λ₂(K₂) = 2` derived **through the proved theorem** from the
independently computed Rayleigh side — the two routes to the value
(trace/determinant vs. Rayleigh infimum) must agree through
`lambda2_variational`. -/
theorem edge_lambda2_variational_transfer_QA :
    lambda2 k2Adj k2Adj_symmetric (le_refl 2) = 2 := by
  rw [lambda2_variational k2Adj k2Adj_symmetric k2Adj_nonneg (le_refl 2),
    k2_set_sInf_eq_two]

end EdgeK2

/-!
### Disconnected graph: `λ₂ = 0`, through the theorem

Two disjoint edges on `Fin 4`: the component-indicator difference
`![1,1,-1,-1]` is a nonzero kernel vector orthogonal to `onesVec`, so
the constraint set attains `0` and, by PSD, contains nothing smaller.
-/

section TwoEdge

/-- Adjacency of two disjoint edges on `Fin 4` (vertices `0-1` and
`2-3`): adjacent iff distinct and in the same pair. -/
def twoEdgeAdj : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i ≠ j ∧ ((i : ℕ) ≤ 1) = ((j : ℕ) ≤ 1) then 1 else 0

theorem twoEdgeAdj_symmetric : twoEdgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [twoEdgeAdj] <;> norm_num

theorem twoEdgeAdj_nonneg : ∀ i j, 0 ≤ twoEdgeAdj i j := by
  intro i j
  simp only [twoEdgeAdj, Matrix.of_apply]
  split <;> norm_num

theorem twoEdge_kernel_witness :
    (laplacian twoEdgeAdj) *ᵥ (![1, 1, -1, -1] : Fin 4 → ℝ) = 0 := by
  funext i
  have hdiff : ∀ k : Fin 4, twoEdgeAdj i k * ((![1, 1, -1, -1] : Fin 4 → ℝ) i
      - (![1, 1, -1, -1] : Fin 4 → ℝ) k) = 0 := by
    intro k
    fin_cases i <;> fin_cases k <;>
      simp [twoEdgeAdj, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_succ, Matrix.head_cons] <;> norm_num <;> omega
  rw [laplacian_mulVec_apply, Finset.sum_eq_zero fun k _ => hdiff k]
  rfl

theorem twoEdge_witness_nonzero : (![1, 1, -1, -1] : Fin 4 → ℝ) ≠ 0 := by
  intro h
  have h1 : (![1, 1, -1, -1] : Fin 4 → ℝ) 0 = 0 := congrFun h 0
  simp at h1

theorem twoEdge_witness_orth :
    Matrix.dotProduct (![1, 1, -1, -1] : Fin 4 → ℝ) onesVec = 0 := by
  simp [Matrix.dotProduct, onesVec, Fin.sum_univ_four]

theorem twoEdge_witness_rayleigh :
    rayleigh (laplacian twoEdgeAdj) (![1, 1, -1, -1] : Fin 4 → ℝ) = 0 := by
  rw [rayleigh, if_neg twoEdge_witness_nonzero, quadForm,
    twoEdge_kernel_witness, Matrix.dotProduct_zero, zero_div]

/-- `λ₂ = 0` on the disconnected fixture, through the proved
characterization: the witness puts `0` in the constraint set and PSD
keeps every element nonnegative. -/
theorem twoEdge_lambda2_eq_zero_QA :
    lambda2 twoEdgeAdj twoEdgeAdj_symmetric (by norm_num) = 0 := by
  rw [lambda2_variational twoEdgeAdj twoEdgeAdj_symmetric twoEdgeAdj_nonneg
    (by norm_num)]
  have hpsd := laplacian_psd twoEdgeAdj twoEdgeAdj_symmetric twoEdgeAdj_nonneg
  have hge : ∀ r ∈ {r : ℝ | ∃ x : Fin 4 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian twoEdgeAdj) x = r}, (0 : ℝ) ≤ r := by
    rintro r ⟨x, hx0, -, rfl⟩
    rw [rayleigh, if_neg hx0]
    refine div_nonneg (hpsd x) ?_
    simp only [Matrix.dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hmem : (0 : ℝ) ∈ {r : ℝ | ∃ x : Fin 4 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian twoEdgeAdj) x = r} :=
    ⟨![1, 1, -1, -1], twoEdge_witness_nonzero, twoEdge_witness_orth,
      twoEdge_witness_rayleigh⟩
  have hbd : BddBelow {r : ℝ | ∃ x : Fin 4 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian twoEdgeAdj) x = r} :=
    ⟨0, hge⟩
  exact le_antisymm (csInf_le hbd hmem) (le_csInf ⟨0, hmem⟩ hge)

end TwoEdge

/-!
### The three-vertex path: `λ₂ ≤ 1`

The alternating vector `![1,0,-1]` is harmonic (`L *ᵥ x = x`), so its
Rayleigh quotient is `1` and the infimum is at most `1`. (The
literature value is `λ₂(P₃) = 1`.)
-/

section Path3

/-- Adjacency of the three-vertex path. -/
def path3Adj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then 1 else 0

theorem path3Adj_symmetric : path3Adj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [path3Adj]

theorem path3Adj_nonneg : ∀ i j, 0 ≤ path3Adj i j := by
  intro i j
  simp only [path3Adj, Matrix.of_apply]
  split <;> norm_num

theorem path3_lambda2_le_one_QA :
    lambda2 path3Adj path3Adj_symmetric (by norm_num) ≤ 1 := by
  rw [lambda2_variational path3Adj path3Adj_symmetric path3Adj_nonneg
    (by norm_num)]
  have hpsd := laplacian_psd path3Adj path3Adj_symmetric path3Adj_nonneg
  have hwne : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h1 : (![1, 0, -1] : Fin 3 → ℝ) 0 = 0 := congrFun h 0
    simp at h1
  have hworth : Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ) onesVec = 0 := by
    simp [Matrix.dotProduct, onesVec, Fin.sum_univ_three]
  have hmul : (laplacian path3Adj) *ᵥ (![1, 0, -1] : Fin 3 → ℝ)
      = (![1, 0, -1] : Fin 3 → ℝ) := by
    funext i
    rw [laplacian_mulVec_apply]
    fin_cases i <;>
      simp [path3Adj, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_succ, Matrix.head_cons, Fin.sum_univ_three] <;>
      norm_num
  have hray : rayleigh (laplacian path3Adj) (![1, 0, -1] : Fin 3 → ℝ) = 1 := by
    rw [rayleigh, if_neg hwne, quadForm, hmul]
    norm_num [Matrix.dotProduct, Fin.sum_univ_three]
  have hmem : (1 : ℝ) ∈ {r : ℝ | ∃ x : Fin 3 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian path3Adj) x = r} :=
    ⟨![1, 0, -1], hwne, hworth, hray⟩
  have hbd : BddBelow {r : ℝ | ∃ x : Fin 3 → ℝ, x ≠ 0 ∧
      Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (laplacian path3Adj) x = r} :=
    ⟨0, by
      rintro r ⟨x, hx0, -, rfl⟩
      rw [rayleigh, if_neg hx0]
      refine div_nonneg (hpsd x) ?_
      simp only [Matrix.dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _⟩
  exact csInf_le hbd hmem

end Path3

end SpectralGraphTheory.QA
