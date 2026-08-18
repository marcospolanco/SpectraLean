/-
  Cheeger_QA.lean

  Purpose
  -------
  QA lemmas for the Cheeger inequality interface of
  `Scaffold.Mathlib.GraphTheory.Cheeger`: structural conductance facts
  proved from the definitions, and coherence checks that derive
  consequences from the two admitted bounds.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the Cheeger axioms; it checks that their interfaces compose.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Cheeger

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Structural conductance facts (proved)
-/

/-- The boundary of `S` equals the boundary of its complement for
symmetric weights. -/
theorem boundary_complement_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (S : Finset V) :
    boundary A Sᶜ = boundary A S := by
  show (∑ i in Sᶜ, ∑ j in Sᶜᶜ, A i j) = ∑ i in S, ∑ j in Sᶜ, A i j
  rw [compl_compl, Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
    rw [hA.apply y x]

/-- The boundary of `S` is at most the volume of `S`. -/
theorem boundary_le_vol_QA (A : WAdj (V := V)) (hnonneg : ∀ i j, 0 ≤ A i j)
    (S : Finset V) :
    boundary A S ≤ vol A S := by
  have h : ∀ i : V, (∑ j in Sᶜ, A i j) ≤ deg A i := by
    intro i
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun j _ _ => hnonneg i j
  show (∑ i in S, ∑ j in Sᶜ, A i j) ≤ vol A S
  exact Finset.sum_le_sum fun i _ => h i

/-- The boundary is bounded by both volumes, hence by their minimum. -/
theorem boundary_le_min_vol_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V) :
    boundary A S ≤ min (vol A S) (vol A Sᶜ) := by
  refine le_min_iff.mpr ⟨boundary_le_vol_QA A hnonneg S, ?_⟩
  rw [← boundary_complement_QA A hA S]
  exact boundary_le_vol_QA A hnonneg Sᶜ

/-- Conductance is bounded by one for symmetric nonnegative weights. In
the zero-volume case the conductance evaluates to the junk value
`0 / 0 = 0`, still at most one. -/
theorem conductance_le_one_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V) :
    conductance A S ≤ 1 := by
  rcases lt_or_le 0 (min (vol A S) (vol A Sᶜ)) with hpos | hnpos
  · rw [conductance]
    exact (div_le_one hpos).mpr (boundary_le_min_vol_QA A hA hnonneg S)
  · have h0min : 0 ≤ min (vol A S) (vol A Sᶜ) :=
      le_min_iff.mpr ⟨vol_nonneg A hnonneg S, vol_nonneg A hnonneg Sᶜ⟩
    have hmin : min (vol A S) (vol A Sᶜ) = 0 := le_antisymm hnpos h0min
    have hbd : boundary A S = 0 :=
      le_antisymm (le_trans (boundary_le_min_vol_QA A hA hnonneg S)
        (hmin ▸ le_refl _)) (boundary_nonneg A hnonneg S)
    rw [conductance, hbd, hmin, div_zero]
    exact zero_le_one

/-- The Cheeger constant is at most one whenever a nonempty proper
subset exists (in particular for at least two vertices). -/
theorem cheegerConstant_le_one_QA (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (S : Finset V)
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    cheegerConstant A ≤ 1 :=
  le_trans (conductance_ge_cheegerConstant A hnonneg S hS hSc)
    (conductance_le_one_QA A hA hnonneg S)

/-!
## Coherence of the admitted Cheeger bounds
-/

/-- A positive Cheeger constant forces a positive second eigenvalue of
the regular normalized Laplacian, derived from the admitted lower
bound. (Conditional on the axiom; this is an interface consequence,
not a proof of the axiom.) -/
theorem cheeger_positive_implies_secondEval_pos_QA (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (hcard : 2 ≤ Fintype.card V) (hpos : 0 < cheegerConstant A) :
    0 < secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard := by
  have h := cheeger_lower_bound A hA hnonneg d hd hdpos hcard
  calc 0 < (cheegerConstant A) ^ 2 / 2 :=
        div_pos (sq_pos_of_pos hpos) (by norm_num)
    _ ≤ secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard := h

/-- The two admitted Cheeger bounds are mutually coherent: the squared
constant is controlled by `λ₂` and `λ₂` by twice the constant, for the
same matrix, regularity data, and Cheeger constant. -/
theorem cheeger_bounds_coherent_QA (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (hcard : 2 ≤ Fintype.card V) :
    (cheegerConstant A) ^ 2 / 2 ≤
        secondEval (regularNormalizedLaplacian A d)
          (regularNormalizedLaplacian_symmetric A hA d) hcard ∧
      secondEval (regularNormalizedLaplacian A d)
          (regularNormalizedLaplacian_symmetric A hA d) hcard ≤
        2 * cheegerConstant A :=
  ⟨cheeger_lower_bound A hA hnonneg d hd hdpos hcard,
    cheeger_upper_bound A hA hnonneg d hd hdpos hcard⟩

/-!
## Fixture: the two-vertex edge

`edgeAdj` is the adjacency matrix of `K₂`, a `1`-regular graph. The
fixture serves two purposes:

- a **refutation of the pre-repair statement shape**: composing the old
  `lambda2` with the normalized Laplacian read the spectrum of
  `L(L_sym) = -L_sym`, whose second sorted eigenvalue on `K₂` is `0`,
  so the old lower-bound instance asserted `1/2 ≤ 0`;
- an **independent value check of the corrected shape**: the corrected
  spectral side `secondEval (L_sym)` equals `2` on `K₂`, computed from
  the eigenvector equation, trace, determinant, and sortedness — no
  spectral-theorem computation, no axiom.
-/

/-- Adjacency matrix of the two-vertex edge: a `1`-regular weighted
graph on `Fin 2`. -/
def edgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem edgeAdj_symmetric : edgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [edgeAdj]

theorem edgeAdj_nonneg : ∀ i j, 0 ≤ edgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [edgeAdj]

/-- `K₂` is `1`-regular. -/
theorem edgeAdj_regular : ∀ i, deg edgeAdj i = 1 := by
  intro i
  fin_cases i <;> simp [deg, edgeAdj, Fin.sum_univ_two]

theorem edgeAdj_card : 2 ≤ Fintype.card (Fin 2) := le_refl 2

section EdgeCuts

/-- The edge cut of either singleton has boundary weight `1`. -/
theorem edge_boundary_singleton (i : Fin 2) : boundary edgeAdj {i} = 1 := by
  fin_cases i
  · simp [boundary, edgeAdj,
      show ({0} : Finset (Fin 2))ᶜ = {1} by decide, Finset.sum_singleton]
  · simp [boundary, edgeAdj,
      show ({1} : Finset (Fin 2))ᶜ = {0} by decide, Finset.sum_singleton]

/-- Both sides of the edge cut have volume `1`. -/
theorem edge_vol_singleton (i : Fin 2) :
    vol edgeAdj {i} = 1 ∧ vol edgeAdj {i}ᶜ = 1 := by
  have h1 : ∀ j : Fin 2, vol edgeAdj {j} = 1 := by
    intro j
    rw [vol, Finset.sum_singleton, edgeAdj_regular]
  have h2 : ∀ j : Fin 2, vol edgeAdj {j}ᶜ = 1 := by
    intro j
    rw [vol, Finset.sum_congr rfl (fun i _ => edgeAdj_regular i),
      Finset.sum_const, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin]
    norm_num
  exact ⟨h1 i, h2 i⟩

/-- The conductance of the edge cut is `1`, so the Cheeger constant of
`K₂` — the infimum over its two cuts — is `1`. -/
theorem edge_cheegerConstant : cheegerConstant edgeAdj = 1 := by
  have hcond : ∀ i : Fin 2, conductance edgeAdj {i} = 1 := by
    intro i
    obtain ⟨hv1, hv2⟩ := edge_vol_singleton i
    rw [conductance, edge_boundary_singleton i, hv1, hv2]
    norm_num
  have hset : {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance edgeAdj S = c} = {1} := by
    ext c
    constructor
    · rintro ⟨S, hne, hcn, rfl⟩
      fin_cases S
      · exact absurd hne (by decide)
      · simpa using hcond 0
      · simpa using hcond 1
      · exact absurd hcn (by decide)
    · rintro ⟨rfl⟩
      exact ⟨{0}, by decide, by decide, by simpa using hcond 0⟩
  rw [cheegerConstant, hset]
  simp

end EdgeCuts

/-!
### The old statement shape, refuted
-/

section OldShape

/-- Entries of the normalized Laplacian of `K₂`: `1` on the diagonal,
`-1` off it. -/
theorem edge_normLap_diag (i : Fin 2) :
    regularNormalizedLaplacian edgeAdj 1 i i = 1 := by
  fin_cases i <;> simp [regularNormalizedLaplacian, edgeAdj]

theorem edge_normLap_off {i j : Fin 2} (h : i ≠ j) :
    regularNormalizedLaplacian edgeAdj 1 i j = -1 := by
  simp [regularNormalizedLaplacian, edgeAdj, h]

/-- Rows of the normalized Laplacian of a regular graph sum to zero, so
its degree matrix vanishes. -/
theorem edge_normLap_degreeMatrix :
    degreeMatrix (regularNormalizedLaplacian edgeAdj 1) = 0 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    have hdeg : deg (regularNormalizedLaplacian edgeAdj 1) a = 0 := by
      fin_cases a <;>
        simp [deg, regularNormalizedLaplacian, edgeAdj, Fin.sum_univ_two]
    simp [degreeMatrix, hdeg]
  · simp [degreeMatrix, hab]

/-- The combinatorial Laplacian *of* the normalized Laplacian of `K₂`
is its negation, entrywise `L(L_sym) = -L_sym`. -/
theorem edge_lapOfNormLap_entry (i j : Fin 2) :
    laplacian (regularNormalizedLaplacian edgeAdj 1) i j
      = if i = j then -1 else 1 := by
  by_cases h : i = j
  · subst h
    have hdeg : deg (regularNormalizedLaplacian edgeAdj 1) i = 0 := by
      fin_cases i <;>
        simp [deg, regularNormalizedLaplacian, edgeAdj, Fin.sum_univ_two]
    rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal, hdeg,
      edge_normLap_diag]
    norm_num
  · rw [laplacian, Matrix.sub_apply, degreeMatrix_off_diagonal _ h,
      edge_normLap_off h]
    simp [h]

/-- The Rayleigh form of `L(L_sym) = -L_sym` at any vector is the
negated squared difference `-(x 0 - x 1)²`. -/
theorem edge_old_quadForm (x : Fin 2 → ℝ) :
    Matrix.dotProduct x
        ((laplacian (regularNormalizedLaplacian edgeAdj 1)).mulVec x)
      = -(x 0 - x 1) ^ 2 := by
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    edge_lapOfNormLap_entry]
  norm_num
  ring

/-- Every eigenvalue of `L(L_sym) = -L_sym` is nonpositive, by the
center's one-sided Rayleigh bound at the orthonormal eigenbasis. -/
theorem edge_old_eigvalOf_le_zero (i : Fin 2) :
    eigvalOf (laplacian (regularNormalizedLaplacian edgeAdj 1))
        (laplacian_symmetric _ (regularNormalizedLaplacian_symmetric
          edgeAdj edgeAdj_symmetric 1)) i ≤ 0 :=
  eigvalOf_le_of_quadForm_nonpos
    (laplacian (regularNormalizedLaplacian edgeAdj 1))
    (laplacian_symmetric (regularNormalizedLaplacian edgeAdj 1)
      (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1))
    (by
      intro x
      rw [edge_old_quadForm x]
      exact neg_nonpos.mpr (sq_nonneg _))
    i

/-- The sorted spectrum of `L(L_sym) = -L_sym` is entrywise nonpositive. -/
theorem edge_old_evals_le_zero :
    evals (laplacian_symmetric (regularNormalizedLaplacian edgeAdj 1)
      (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1))
        (1 : Fin 2) ≤ 0 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric (regularNormalizedLaplacian edgeAdj 1)
      (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1))
    (1 : Fin 2)
  rw [hi]
  exact edge_old_eigvalOf_le_zero i

/-- **Refutation of the pre-repair statement shape.** The lower-bound
axiom as stated before 2026-08-18 — with its spectral side
`lambda2 (regularNormalizedLaplacian A d) …`, which reads the spectrum
of the combinatorial Laplacian *of* the normalized Laplacian — is false
on `K₂`: it asserts `1²/2 ≤ 0`. This lemma documents, in proved form,
why the axiom had to be restated at the corrected shape
`secondEval (regularNormalizedLaplacian A d) …`; the hypotheses below
are exactly the instance data of `K₂` (symmetric, nonnegative,
`1`-regular, positive degree, two vertices). -/
theorem old_cheeger_lower_bound_refuted_QA
    (h : (cheegerConstant edgeAdj) ^ 2 / 2 ≤
      lambda2 (regularNormalizedLaplacian edgeAdj 1)
        (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1)
        (le_refl 2)) : False := by
  rw [edge_cheegerConstant] at h
  simp only [lambda2] at h
  have hbad : (1 : ℝ) ^ 2 / 2 ≤ 0 := le_trans h edge_old_evals_le_zero
  norm_num at hbad

end OldShape

/-!
### The corrected statement shape, pinned to its classical value
-/

section NewShape

/-- A length-two list is the list of its two entries. -/
private theorem list_two_eq {l : List ℝ} (h : l.length = 2) :
    l = [l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩] :=
  List.ext_get h (by
    intro n h₁ h₂
    have hn2 : n < 2 := by omega
    interval_cases n <;> simp)

/-- Two-point spectrum pinning: a sorted length-two list with sum `2`
and product `0` has second entry `2` (hence first entry `0`). This is
the whole computational content of the eigenvalue check below. -/
private theorem two_point_pin {l : List ℝ} (h2 : l.length = 2)
    (hs : l.Sorted (fun a b => a ≤ b)) (hsum : l.sum = 2) (hprod : l.prod = 0) :
    l.get ⟨1, by omega⟩ = 2 := by
  obtain ⟨g₀, g₁, hg⟩ : ∃ a b : ℝ, l = [a, b] :=
    ⟨l.get ⟨0, by omega⟩, l.get ⟨1, by omega⟩, list_two_eq h2⟩
  subst hg
  have hlt : (0 : Fin 2) < (1 : Fin 2) := by decide
  have hmono : g₀ ≤ g₁ := hs.rel_get_of_lt hlt
  simp only [List.sum_cons, List.sum_nil, add_zero, List.prod_cons,
    List.prod_nil, mul_one] at hsum hprod
  rw [List.get_cons_succ]
  simp
  rcases eq_zero_or_eq_zero_of_mul_eq_zero hprod with h0 | h1
  · linarith
  · linarith

/-- Trace and determinant of the normalized Laplacian of `K₂`. -/
theorem edge_normLap_trace :
    (regularNormalizedLaplacian edgeAdj 1).trace = 2 := by
  simp [Matrix.trace, edge_normLap_diag]

theorem edge_normLap_det :
    (regularNormalizedLaplacian edgeAdj 1).det = 0 := by
  rw [Matrix.det_fin_two]
  have e01 : (0 : Fin 2) ≠ 1 := by decide
  have e10 : (1 : Fin 2) ≠ 0 := by decide
  simp [edge_normLap_diag, edge_normLap_off e01, edge_normLap_off e10]

/-- The sorted spectrum of the normalized Laplacian of `K₂` is the
two-element list `[0, 2]`: sortedness plus trace (`0 + 2 = 2`) and
determinant (`0 * 2 = 0`) pin both entries. This is a computational
eigenvalue check performed without any axiom or spectral-theorem
computation: trace and determinant come from entrywise arithmetic, the
sum/product bridges from `Multiset.sort_eq`, and the pin from
`two_point_pin`. -/
theorem edge_normLap_secondEval_eq_two_QA :
    secondEval (regularNormalizedLaplacian edgeAdj 1)
      (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1)
      (le_refl 2) = 2 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
          edgeAdj edgeAdj_symmetric 1)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
          edgeAdj edgeAdj_symmetric 1)).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
          edgeAdj edgeAdj_symmetric 1)).eigenvalues))).sum = 2 := by
    have htr : ∑ i : Fin 2, eigvalOf (regularNormalizedLaplacian edgeAdj 1)
        (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1) i
          = 2 := by
      rw [eigvalOf_sum_eq_trace, edge_normLap_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
          edgeAdj edgeAdj_symmetric 1)).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2, ((isHermitian_of_isSymm
        (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric
          1)).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
        edgeAdj edgeAdj_symmetric 1)).det_eq_prod_eigenvalues
      rw [edge_normLap_det] at hd0
      simpa using hd0.symm
    rw [← Multiset.prod_coe, Multiset.sort_eq, ← Finset.prod_eq_multiset_prod]
    exact hd
  exact two_point_pin hlen hsorted hsum hprod

/-- The corrected Cheeger sandwich on `K₂` instantiates to the true
numeric statement `1/2 ≤ 2 ≤ 2`: both the conductance value `φ = 1`
and the spectral value `λ₂(L_sym) = 2` are computed independently of
the axioms, so a defective spectral side (as in the pre-repair shape,
which evaluates to `0` and violates this check) cannot pass. -/
theorem cheeger_bounds_edge_QA :
    (cheegerConstant edgeAdj) ^ 2 / 2 ≤
        secondEval (regularNormalizedLaplacian edgeAdj 1)
          (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1)
          (le_refl 2) ∧
      secondEval (regularNormalizedLaplacian edgeAdj 1)
        (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1)
        (le_refl 2) ≤ 2 * cheegerConstant edgeAdj := by
  constructor <;> [
    exact cheeger_lower_bound edgeAdj edgeAdj_symmetric edgeAdj_nonneg 1
      edgeAdj_regular (by norm_num) edgeAdj_card;
    exact cheeger_upper_bound edgeAdj edgeAdj_symmetric edgeAdj_nonneg 1
      edgeAdj_regular (by norm_num) edgeAdj_card]

end NewShape

end SpectralGraphTheory.QA
