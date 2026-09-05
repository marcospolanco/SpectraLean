/-
  Cheeger_QA.lean

  Purpose
  -------
  QA lemmas for the Cheeger inequality interface of
  `Scaffold.Mathlib.GraphTheory.Cheeger`: structural conductance facts
  proved from the definitions, and coherence checks that derive
  consequences from the bounds — both directions are proved theorems
  (the easy direction since 2026-08-18, the hard direction since
  2026-08-23; the family is hard crust, no admitted axiom involved).
  Since 2026-09-04 this file also carries the family's adversarial
  fence audit (`RegularFences`): hypothesis-form negative witnesses
  plus isolation companions for the pre-discipline QA's unfenced
  load-bearing clauses.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA checks that
  the interfaces compose.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Cheeger
import Scaffold.QA.SpectralGraph.Exhaustive_QA

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

/-- The two Cheeger bounds are mutually coherent: the squared constant
is controlled by `λ₂` (admitted lower bound) and `λ₂` by twice the
constant (proved upper bound, retired from an axiom on 2026-08-18),
for the same matrix, regularity data, and Cheeger constant. -/
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

`cheegerEdgeAdj` is the adjacency matrix of `K₂`, a `1`-regular graph. The
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
def cheegerEdgeAdj : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem cheegerEdgeAdj_symmetric : cheegerEdgeAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [cheegerEdgeAdj]

theorem cheegerEdgeAdj_nonneg : ∀ i j, 0 ≤ cheegerEdgeAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cheegerEdgeAdj]

/-- `K₂` is `1`-regular. -/
theorem cheegerEdgeAdj_regular : ∀ i, deg cheegerEdgeAdj i = 1 := by
  intro i
  fin_cases i <;> simp [deg, cheegerEdgeAdj, Fin.sum_univ_two]

theorem cheegerEdgeAdj_card : 2 ≤ Fintype.card (Fin 2) := le_refl 2

section EdgeCuts

/-- The edge cut of either singleton has boundary weight `1`. -/
theorem edge_boundary_singleton (i : Fin 2) : boundary cheegerEdgeAdj {i} = 1 := by
  fin_cases i
  · simp [boundary, cheegerEdgeAdj,
      show ({0} : Finset (Fin 2))ᶜ = {1} by decide, Finset.sum_singleton]
  · simp [boundary, cheegerEdgeAdj,
      show ({1} : Finset (Fin 2))ᶜ = {0} by decide, Finset.sum_singleton]

/-- Both sides of the edge cut have volume `1`. -/
theorem edge_vol_singleton (i : Fin 2) :
    vol cheegerEdgeAdj {i} = 1 ∧ vol cheegerEdgeAdj {i}ᶜ = 1 := by
  have h1 : ∀ j : Fin 2, vol cheegerEdgeAdj {j} = 1 := by
    intro j
    rw [vol, Finset.sum_singleton, cheegerEdgeAdj_regular]
  have h2 : ∀ j : Fin 2, vol cheegerEdgeAdj {j}ᶜ = 1 := by
    intro j
    rw [vol, Finset.sum_congr rfl (fun i _ => cheegerEdgeAdj_regular i),
      Finset.sum_const, Finset.card_compl, Finset.card_singleton,
      Fintype.card_fin]
    norm_num
  exact ⟨h1 i, h2 i⟩

/-- The conductance of the edge cut is `1`, so the Cheeger constant of
`K₂` — the infimum over its two cuts — is `1`. -/
theorem edge_cheegerConstant : cheegerConstant cheegerEdgeAdj = 1 := by
  have hcond : ∀ i : Fin 2, conductance cheegerEdgeAdj {i} = 1 := by
    intro i
    obtain ⟨hv1, hv2⟩ := edge_vol_singleton i
    rw [conductance, edge_boundary_singleton i, hv1, hv2]
    norm_num
  have hset : {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance cheegerEdgeAdj S = c} = {1} := by
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
    regularNormalizedLaplacian cheegerEdgeAdj 1 i i = 1 := by
  fin_cases i <;> simp [regularNormalizedLaplacian, cheegerEdgeAdj]

theorem edge_normLap_off {i j : Fin 2} (h : i ≠ j) :
    regularNormalizedLaplacian cheegerEdgeAdj 1 i j = -1 := by
  simp [regularNormalizedLaplacian, cheegerEdgeAdj, h]

/-- Rows of the normalized Laplacian of a regular graph sum to zero, so
its degree matrix vanishes. -/
theorem edge_normLap_degreeMatrix :
    degreeMatrix (regularNormalizedLaplacian cheegerEdgeAdj 1) = 0 := by
  ext a b
  by_cases hab : a = b
  · subst hab
    have hdeg : deg (regularNormalizedLaplacian cheegerEdgeAdj 1) a = 0 := by
      fin_cases a <;>
        simp [deg, regularNormalizedLaplacian, cheegerEdgeAdj, Fin.sum_univ_two]
    simp [degreeMatrix, hdeg]
  · simp [degreeMatrix, hab]

/-- The combinatorial Laplacian *of* the normalized Laplacian of `K₂`
is its negation, entrywise `L(L_sym) = -L_sym`. -/
theorem edge_lapOfNormLap_entry (i j : Fin 2) :
    laplacian (regularNormalizedLaplacian cheegerEdgeAdj 1) i j
      = if i = j then -1 else 1 := by
  by_cases h : i = j
  · subst h
    have hdeg : deg (regularNormalizedLaplacian cheegerEdgeAdj 1) i = 0 := by
      fin_cases i <;>
        simp [deg, regularNormalizedLaplacian, cheegerEdgeAdj, Fin.sum_univ_two]
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
        ((laplacian (regularNormalizedLaplacian cheegerEdgeAdj 1)).mulVec x)
      = -(x 0 - x 1) ^ 2 := by
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    edge_lapOfNormLap_entry]
  norm_num
  ring

/-- Every eigenvalue of `L(L_sym) = -L_sym` is nonpositive, by the
center's one-sided Rayleigh bound at the orthonormal eigenbasis. -/
theorem edge_old_eigvalOf_le_zero (i : Fin 2) :
    eigvalOf (laplacian (regularNormalizedLaplacian cheegerEdgeAdj 1))
        (laplacian_symmetric _ (regularNormalizedLaplacian_symmetric
          cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)) i ≤ 0 :=
  eigvalOf_le_of_quadForm_nonpos
    (laplacian (regularNormalizedLaplacian cheegerEdgeAdj 1))
    (laplacian_symmetric (regularNormalizedLaplacian cheegerEdgeAdj 1)
      (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1))
    (by
      intro x
      rw [edge_old_quadForm x]
      exact neg_nonpos.mpr (sq_nonneg _))
    i

/-- The sorted spectrum of `L(L_sym) = -L_sym` is entrywise nonpositive. -/
theorem edge_old_evals_le_zero :
    evals (laplacian_symmetric (regularNormalizedLaplacian cheegerEdgeAdj 1)
      (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1))
        (1 : Fin 2) ≤ 0 := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf
    (laplacian_symmetric (regularNormalizedLaplacian cheegerEdgeAdj 1)
      (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1))
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
    (h : (cheegerConstant cheegerEdgeAdj) ^ 2 / 2 ≤
      lambda2 (regularNormalizedLaplacian cheegerEdgeAdj 1)
        (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
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
    (regularNormalizedLaplacian cheegerEdgeAdj 1).trace = 2 := by
  simp [Matrix.trace, edge_normLap_diag]

theorem edge_normLap_det :
    (regularNormalizedLaplacian cheegerEdgeAdj 1).det = 0 := by
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
    secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
      (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
      (le_refl 2) = 2 := by
  have hlen : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
          cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)).eigenvalues))).length = 2 := by
    rw [Multiset.length_sort, Multiset.card_map]; simp
  have hsorted : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
          cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)).eigenvalues))).Sorted
        (fun a b => a ≤ b) :=
    Multiset.sort_sorted _ _
  have hsum : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
          cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)).eigenvalues))).sum = 2 := by
    have htr : ∑ i : Fin 2, eigvalOf (regularNormalizedLaplacian cheegerEdgeAdj 1)
        (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1) i
          = 2 := by
      rw [eigvalOf_sum_eq_trace, edge_normLap_trace]
    rw [← Multiset.sum_coe, Multiset.sort_eq, ← Finset.sum_eq_multiset_sum]
    exact htr
  have hprod : (Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset (Fin 2)).val.map
        ((isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
          cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)).eigenvalues))).prod = 0 := by
    have hd : ∏ i : Fin 2, ((isHermitian_of_isSymm
        (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric
          1)).eigenvalues i) = 0 := by
      have hd0 := (isHermitian_of_isSymm (regularNormalizedLaplacian_symmetric
        cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)).det_eq_prod_eigenvalues
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
    (cheegerConstant cheegerEdgeAdj) ^ 2 / 2 ≤
        secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
          (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
          (le_refl 2) ∧
      secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
        (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
        (le_refl 2) ≤ 2 * cheegerConstant cheegerEdgeAdj := by
  constructor <;> [
    exact cheeger_lower_bound cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg 1
      cheegerEdgeAdj_regular (by norm_num) cheegerEdgeAdj_card;
    exact cheeger_upper_bound cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg 1
      cheegerEdgeAdj_regular (by norm_num) cheegerEdgeAdj_card]

end NewShape

/-!
## The easy direction, proved: computed test-vector witnesses

  `cheeger_upper_bound` was retired from axiom to theorem on
  2026-08-18, proved from `secondEval_variational` through the cut test
  vector `cutTestVector`. These witnesses exercise the new machinery
  numerically: the test vector's values and Rayleigh quotient are
  computed from the definitions on two regular fixtures (`K₂` from this
  file, `C₄` from `Exhaustive_QA`), and the proved bound is instantiated
  and cross-checked against independently pinned values.
-/

section ProvedEasyDirection

/-- The cut test vector of the singleton cut on `K₂` computes to
`![1, -1]` — the values `vol Sᶜ = 1` on `S` and `- vol S = -1` off it,
from the definitions. -/
theorem cutTestVector_edge_QA :
    cutTestVector cheegerEdgeAdj ({0} : Finset (Fin 2)) = ![1, -1] := by
  obtain ⟨hv1, hv2⟩ := edge_vol_singleton 0
  funext i
  fin_cases i
  · simp [cutTestVector_apply, hv2]
  · simp [cutTestVector_apply, hv1]

/-- The test-vector Rayleigh value on `K₂`'s singleton cut is `2`,
computed through the proved cut identity
`boundary · vol V / (vol S · vol Sᶜ) = 1 · 2 / (1 · 1)`. This is
exactly the independently pinned value `λ₂(L_sym) = 2`
(`edge_normLap_secondEval_eq_two_QA`): the test-vector bound is
*attained* on `K₂`, at the vector whose values are pinned by
`cutTestVector_edge_QA`. -/
theorem cutTestVector_edge_rayleigh_QA :
    rayleigh (regularNormalizedLaplacian cheegerEdgeAdj 1)
        (cutTestVector cheegerEdgeAdj ({0} : Finset (Fin 2))) = 2 := by
  obtain ⟨hv1, hv2⟩ := edge_vol_singleton 0
  have hvV : vol cheegerEdgeAdj (Finset.univ : Finset (Fin 2)) = 2 := by
    rw [← vol_compl cheegerEdgeAdj ({0} : Finset (Fin 2)), hv1, hv2]
    norm_num
  rw [rayleigh_regularNormalizedLaplacian_cutTestVector cheegerEdgeAdj
    cheegerEdgeAdj_symmetric 1 cheegerEdgeAdj_regular (by norm_num) (by decide)
    (by decide), edge_boundary_singleton 0, hv1, hv2, hvV]
  norm_num

/-- **The proved bound is attained on `K₂`:** `λ₂(L_sym) = 2 = 2φ`.
Both the spectral value (`edge_normLap_secondEval_eq_two_QA`) and the
conductance (`edge_cheegerConstant`) are computed independently of the
theorem, so the equality is a genuine cross-check of the proved bound
rather than an axiom instantiation. -/
theorem cheeger_upper_bound_edge_eq_QA :
    secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
        (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
        (le_refl 2) = 2 * cheegerConstant cheegerEdgeAdj := by
  rw [edge_normLap_secondEval_eq_two_QA, edge_cheegerConstant]
  norm_num

/-- `C₄` has nonnegative weights (needed as the theorem's `hnonneg`). -/
theorem cycleAdj4_nonneg : ∀ i j, 0 ≤ cycleAdj4 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [cycleAdj4]

/-- Total volume of `C₄`: four vertices of degree `2`. -/
theorem cyc_vol_univ :
    vol cycleAdj4 (Finset.univ : Finset (Fin 4)) = 8 := by
  rw [← vol_compl cycleAdj4 ({0, 1} : Finset (Fin 4)), cyc_vol_01,
    complc_01, cyc_vol_23]
  norm_num

/-- The test-vector Rayleigh value on `C₄`'s adjacent-pair cut `{0,1}`
is `1` — the classical value of `λ₂` of the normalized cycle Laplacian,
obtained here purely from the cut identity
`boundary · vol V / (vol S · vol Sᶜ) = 2 · 8 / (4 · 4)` with the
exhaustively computed boundary and volumes. -/
theorem cutTestVector_cycle_rayleigh_QA :
    rayleigh (regularNormalizedLaplacian cycleAdj4 2)
        (cutTestVector cycleAdj4 ({0, 1} : Finset (Fin 4))) = 1 := by
  rw [rayleigh_regularNormalizedLaplacian_cutTestVector cycleAdj4
    cycleAdj4_isSymm 2 cycleAdj4_deg (by norm_num) (by decide)
    (by decide), cyc_boundary_01, cyc_vol_01, complc_01, cyc_vol_23,
    cyc_vol_univ]
  norm_num

/-- The proved easy direction instantiated on `C₄`:
`λ₂(L_sym) ≤ 2φ ≤ 2 · (1/2) = 1`, using the exhaustively computed
conductance `1/2` of the adjacent-pair cut. Together with
`cutTestVector_cycle_rayleigh_QA` (the test-vector bound evaluates to
exactly `1`), the instantiated bound is tight at this cut. -/
theorem cheeger_upper_bound_cycle_le_QA :
    secondEval (regularNormalizedLaplacian cycleAdj4 2)
        (regularNormalizedLaplacian_symmetric cycleAdj4 cycleAdj4_isSymm 2)
        (by norm_num) ≤ 1 := by
  have h1 := cheeger_upper_bound cycleAdj4 cycleAdj4_isSymm
    cycleAdj4_nonneg 2 cycleAdj4_deg (by norm_num) (by norm_num)
  calc secondEval (regularNormalizedLaplacian cycleAdj4 2)
        (regularNormalizedLaplacian_symmetric cycleAdj4 cycleAdj4_isSymm 2)
        (by norm_num)
      ≤ 2 * cheegerConstant cycleAdj4 := h1
    _ ≤ 2 * conductance cycleAdj4 {0, 1} := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact conductance_ge_cheegerConstant cycleAdj4 cycleAdj4_nonneg
          {0, 1} (by decide) (by decide)
    _ = 1 := by rw [cyc_conductance_01]; norm_num

end ProvedEasyDirection

/-!
## The hard direction, Step 1a: pure-algebra components (witnesses)

The pure-algebra layer of the Cheeger hard-direction program
(`proposals/discharge-perturbation-axioms.md` Step 1a, added 2026-08-23,
all proved, zero axioms): Component A (`core_sum_abs_sq_sub_sq`), the
fused median-part contraction
(`sum_edgeWeight_sq_posPart_add_sq_negPart_le`), and the normalization
(`rayleigh_regularNormalizedLaplacian_eq`). The witnesses pin their
constants numerically — the discipline the proposal carries forward
after the repository was burned by a false Cheeger shape — and fence
their statement guards with negative witnesses: symmetry is load-bearing
on Component A (refuted on asymmetric nonnegative input) and
nonnegativity on the contraction (refuted on a symmetric negative-input
fixture). The K₂ equality pins of the surrounding chain (`φ = d = 1`,
`λ₂(L_sym) = 2`) are `edge_cheegerConstant`,
`edge_normLap_secondEval_eq_two_QA` above.
-/

section HardDirectionStep1a

/-- Test function `![1, 0]` on `Fin 2` for the Component A witness. -/
def edgeF : Fin 2 → ℝ := ![1, 0]

theorem edgeF_zero : edgeF 0 = 1 := by simp [edgeF]

theorem edgeF_one : edgeF 1 = 0 := by simp [edgeF]

/-- Component A's left-hand total-variation sum on `K₂` at `edgeF`,
computed from the definitions: `|1² - 0²|` across both ordered pairs. -/
theorem edge_core_tv :
    ∑ i, ∑ j, cheegerEdgeAdj i j * |edgeF i ^ 2 - edgeF j ^ 2| = 2 := by
  simp only [Fin.sum_univ_two, cheegerEdgeAdj, edgeF_zero, edgeF_one]
  norm_num

/-- Component A's energy factor on `K₂` at `edgeF`, computed raw. -/
theorem edge_core_E' :
    ∑ i, ∑ j, cheegerEdgeAdj i j * (edgeF i - edgeF j) ^ 2 = 2 := by
  simp only [Fin.sum_univ_two, cheegerEdgeAdj, edgeF_zero, edgeF_one]
  norm_num

/-- Component A's degree-weighted factor on `K₂` at `edgeF`, through
the new regularity bridge `sum_deg_mul_eq_of_regular` (so the bridge is
load-bearing here, not decorative). -/
theorem edge_core_degsum :
    ∑ i, deg cheegerEdgeAdj i * edgeF i ^ 2 = 1 := by
  rw [sum_deg_mul_eq_of_regular cheegerEdgeAdj 1 cheegerEdgeAdj_regular edgeF]
  simp only [Fin.sum_univ_two, edgeF_zero, edgeF_one]
  norm_num

/-- **Component A instantiated on `K₂`:** at `edgeF = ![1, 0]` the
instance reads `4 ≤ 8`, with all three quantities pinned independently
above. -/
theorem core_edge_QA :
    (∑ i, ∑ j, cheegerEdgeAdj i j * |edgeF i ^ 2 - edgeF j ^ 2|) ^ 2
      ≤ (∑ i, ∑ j, cheegerEdgeAdj i j * (edgeF i - edgeF j) ^ 2)
        * (4 * ∑ i, deg cheegerEdgeAdj i * edgeF i ^ 2) :=
  core_sum_abs_sq_sub_sq cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg edgeF

/-- **The strict case:** on `K₂` at `edgeF` the Component A bound is
strict with a visible gap, `4 < 8` — the bound is not vacuously tight
here. (The slack is exactly the AM-GM loss on the crossing pair:
`(1 + 0)² = 1 < 2·1² + 2·0² = 2`.) -/
theorem core_edge_strict_QA :
    (∑ i, ∑ j, cheegerEdgeAdj i j * |edgeF i ^ 2 - edgeF j ^ 2|) ^ 2
      < (∑ i, ∑ j, cheegerEdgeAdj i j * (edgeF i - edgeF j) ^ 2)
        * (4 * ∑ i, deg cheegerEdgeAdj i * edgeF i ^ 2) := by
  rw [edge_core_tv, edge_core_E', edge_core_degsum]
  norm_num

/-- Test function on `C₄` for the contraction *equality* case: the
values `![1, 0, -1, 0]` at threshold `m = 0` put one vertex strictly
above, one strictly below, and two exactly at the threshold. -/
def cycX1 : Fin 4 → ℝ := ![1, 0, -1, 0]

/-- Test function on `C₄` for the contraction *strict* case: the
values `![1, 1, -1, -1]` at threshold `m = 0` split the cycle into two
dominant halves. -/
def cycX2 : Fin 4 → ℝ := ![1, 1, -1, -1]

theorem cycX1_pos_E' :
    ∑ i, ∑ j, cycleAdj4 i j
      * (max (cycX1 i - 0) 0 - max (cycX1 j - 0) 0) ^ 2 = 4 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycX1, sub_zero]
  norm_num

theorem cycX1_neg_E' :
    ∑ i, ∑ j, cycleAdj4 i j
      * (max (0 - cycX1 i) 0 - max (0 - cycX1 j) 0) ^ 2 = 4 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycX1]
  norm_num

theorem cycX1_E' :
    ∑ i, ∑ j, cycleAdj4 i j * (cycX1 i - cycX1 j) ^ 2 = 8 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycX1]
  norm_num

theorem cycX2_pos_E' :
    ∑ i, ∑ j, cycleAdj4 i j
      * (max (cycX2 i - 0) 0 - max (cycX2 j - 0) 0) ^ 2 = 4 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycX2, sub_zero]
  norm_num

theorem cycX2_neg_E' :
    ∑ i, ∑ j, cycleAdj4 i j
      * (max (0 - cycX2 i) 0 - max (0 - cycX2 j) 0) ^ 2 = 4 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycX2]
  norm_num

theorem cycX2_E' :
    ∑ i, ∑ j, cycleAdj4 i j * (cycX2 i - cycX2 j) ^ 2 = 16 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycX2]
  norm_num

/-- **The contraction is attained with equality on `C₄` at `cycX1`:**
the two median parts carry `4 + 4` and the energy of `x` is `8`. Every
edge of this fixture either stays within one side or touches a threshold
vertex, so the cross-edge slack is never used — the equality case of
`sum_edgeWeight_sq_posPart_add_sq_negPart_le`. -/
theorem pair_contraction_cycle_eq_QA :
    (∑ i, ∑ j, cycleAdj4 i j
        * (max (cycX1 i - 0) 0 - max (cycX1 j - 0) 0) ^ 2)
      + (∑ i, ∑ j, cycleAdj4 i j
          * (max (0 - cycX1 i) 0 - max (0 - cycX1 j) 0) ^ 2)
      = ∑ i, ∑ j, cycleAdj4 i j * (cycX1 i - cycX1 j) ^ 2 := by
  have h := sum_edgeWeight_sq_posPart_add_sq_negPart_le cycleAdj4
    cycleAdj4_nonneg 0 cycX1
  rw [cycX1_pos_E', cycX1_neg_E', cycX1_E'] at h
  rw [cycX1_pos_E', cycX1_neg_E', cycX1_E']
  linarith

/-- **The strict case:** on `C₄` at `cycX2 = ![1, 1, -1, -1]` the parts
carry `4 + 4 = 8` against the energy `16` — the cross-edge slack
`(1 - (-1))² = 4 ≥ 1² + 1²` is visibly in use. -/
theorem pair_contraction_cycle_lt_QA :
    (∑ i, ∑ j, cycleAdj4 i j
        * (max (cycX2 i - 0) 0 - max (cycX2 j - 0) 0) ^ 2)
      + (∑ i, ∑ j, cycleAdj4 i j
          * (max (0 - cycX2 i) 0 - max (0 - cycX2 j) 0) ^ 2)
      < ∑ i, ∑ j, cycleAdj4 i j * (cycX2 i - cycX2 j) ^ 2 := by
  have h := sum_edgeWeight_sq_posPart_add_sq_negPart_le cycleAdj4
    cycleAdj4_nonneg 0 cycX2
  rw [cycX2_pos_E', cycX2_neg_E', cycX2_E'] at h
  rw [cycX2_pos_E', cycX2_neg_E', cycX2_E']
  linarith

/-- **The normalization on `K₂`, cross-checked.** The new lemma
evaluates the Rayleigh quotient of `L_sym` at `![1, -1]` through the
Dirichlet double sum: `E' = 8`, `‖x‖² = 2`, `d = 1`, giving `8 / 4 = 2`
— the independently pinned `λ₂(L_sym) = 2`
(`edge_normLap_secondEval_eq_two_QA`) and the cut test vector's
Rayleigh value (`cutTestVector_edge_rayleigh_QA`, at the same vector
`![1, -1]` by `cutTestVector_edge_QA`). -/
theorem rayleigh_regularNormalizedLaplacian_edge_eq_QA :
    rayleigh (regularNormalizedLaplacian cheegerEdgeAdj 1) ![1, -1] = 2 := by
  rw [rayleigh_regularNormalizedLaplacian_eq cheegerEdgeAdj cheegerEdgeAdj_symmetric 1
    cheegerEdgeAdj_regular (by norm_num) (by
      intro h
      have h0 : (![1, -1] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
      norm_num at h0)]
  have hE : ∑ i, ∑ j, cheegerEdgeAdj i j * (![1, -1] i - ![1, -1] j) ^ 2 = 8 := by
    simp only [Fin.sum_univ_two, cheegerEdgeAdj]
    norm_num
  have hd : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) ![1, -1] = 2 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    norm_num
  rw [hE, hd]
  norm_num

/-- **The normalized quotient attains the pinned spectrum:** the value
delivered by `rayleigh_regularNormalizedLaplacian_eq` at `![1, -1]`
equals the independently computed `λ₂(L_sym) = 2` — the constant-`2`
denominator of the normalization is exactly right; a defective `/ 1`
or `/ 4` shape would fail this check. -/
theorem rayleigh_edge_attains_secondEval_QA :
    rayleigh (regularNormalizedLaplacian cheegerEdgeAdj 1) ![1, -1]
      = secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
          (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
          (le_refl 2) := by
  rw [rayleigh_regularNormalizedLaplacian_edge_eq_QA,
    edge_normLap_secondEval_eq_two_QA]

/-- The asymmetric fixture for the Component A guard: nonnegative, with
the column sum at vertex `0` exceeding its row sum (`1` vs `1/10`) —
exactly the mismatch `IsSymm` rules out. -/
noncomputable def asymA : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1 / 10; 1, 0]

theorem asymA_nonneg : ∀ i j, 0 ≤ asymA i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [asymA]

theorem asymA_not_isSymm : ¬ asymA.IsSymm := by
  intro h
  have h1 := h.apply 1 0
  simp only [asymA, Matrix.of_apply] at h1
  norm_num at h1

theorem asymA_core_lhs :
    (∑ i, ∑ j, asymA i j * |edgeF i ^ 2 - edgeF j ^ 2|) ^ 2
      = 121 / 100 := by
  simp only [Fin.sum_univ_two, asymA, edgeF_zero, edgeF_one]
  norm_num

theorem asymA_core_rhs :
    (∑ i, ∑ j, asymA i j * (edgeF i - edgeF j) ^ 2)
      * (4 * ∑ i, deg asymA i * edgeF i ^ 2) = 44 / 100 := by
  simp only [Fin.sum_univ_two, asymA, edgeF_zero, edgeF_one, deg]
  norm_num

/-- **The `IsSymm` guard of Component A is load-bearing.** With the
symmetry hypothesis dropped, the statement is false at a nonnegative
fixture satisfying every other hypothesis: `asymA` above has all entries
nonnegative (`asymA_nonneg`) but is provably not symmetric
(`asymA_not_isSymm`), and the instance reads `121/100 ≤ 44/100`. The
mechanism: the cross double sum's column sums must match `deg`'s row
sums for the second factor's degree collapse, and here vertex `0`'s
column sum (`1`) exceeds its row sum (`1/10`). -/
theorem core_sum_abs_sq_sub_sq_asymmetry_refuted_QA
    (h : (∑ i, ∑ j, asymA i j * |edgeF i ^ 2 - edgeF j ^ 2|) ^ 2
      ≤ (∑ i, ∑ j, asymA i j * (edgeF i - edgeF j) ^ 2)
        * (4 * ∑ i, deg asymA i * edgeF i ^ 2)) : False := by
  rw [asymA_core_lhs, asymA_core_rhs] at h
  norm_num at h

/-- The negative-weight fixture for the contraction guard: symmetric
with unit-magnitude off-diagonal entries, all negative. -/
def negEdge : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, -1; -1, 0]

theorem negEdge_isSymm : negEdge.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [negEdge]

theorem negEdge_not_nonneg : ¬ (∀ i j, 0 ≤ negEdge i j) := by
  intro h
  have h1 := h 0 1
  simp only [negEdge, Matrix.of_apply] at h1
  norm_num at h1

/-- Test function `![2, 1]` for the contraction guard witness, at
threshold `m = 3/2` (its median level). -/
def negX : Fin 2 → ℝ := ![2, 1]

theorem negEdge_pair_parts :
    ((∑ i, ∑ j, negEdge i j
        * (max (negX i - 3 / 2) 0 - max (negX j - 3 / 2) 0) ^ 2)
      + ∑ i, ∑ j, negEdge i j
          * (max (3 / 2 - negX i) 0 - max (3 / 2 - negX j) 0) ^ 2)
      = -1 ∧
    ∑ i, ∑ j, negEdge i j * (negX i - negX j) ^ 2 = -2 := by
  constructor
  · simp only [Fin.sum_univ_two, negEdge, negX]
    norm_num
  · simp only [Fin.sum_univ_two, negEdge, negX]
    norm_num

/-- **The nonnegativity guard of the contraction is load-bearing.**
With the weight-nonnegativity hypothesis dropped, the statement is false
at a fixture satisfying the other structure: `negEdge` is provably
symmetric (`negEdge_isSymm`) but has negative entries
(`negEdge_not_nonneg`), and at `negX = ![2, 1]`, `m = 3/2` the parts
carry `-1/2 + -1/2 = -1` against the energy `-2`. -/
theorem pair_contraction_refuted_QA
    (h : (∑ i, ∑ j, negEdge i j
        * (max (negX i - 3 / 2) 0 - max (negX j - 3 / 2) 0) ^ 2)
      + (∑ i, ∑ j, negEdge i j
          * (max (3 / 2 - negX i) 0 - max (3 / 2 - negX j) 0) ^ 2)
      ≤ ∑ i, ∑ j, negEdge i j * (negX i - negX j) ^ 2) : False := by
  rw [negEdge_pair_parts.1, negEdge_pair_parts.2] at h
  norm_num at h

end HardDirectionStep1a

/-!
## The Cheeger hard direction, Step 1b: the co-area core (proved)
-/

section HardDirectionStep1b

/-- Test function for the co-area witnesses on `K₂`: the one-hot
`![1, 0]` — every positive level set is `{0}` or empty, so the minority
hypothesis holds. -/
def edgeY : Fin 2 → ℝ := ![1, 0]

theorem edgeY_zero : edgeY 0 = 1 := by simp [edgeY]

theorem edgeY_one : edgeY 1 = 0 := by simp [edgeY]

/-- The minority hypothesis holds at `edgeY`: at any positive level the
closed superlevel set is `{0}` (card `1`) or empty, and `2 * 1 ≤ 2`. -/
theorem edgeY_minority : ∀ t : ℝ, 0 < t →
    2 * (Finset.univ.filter (fun i => t ≤ edgeY i ^ 2)).card
      ≤ Fintype.card (Fin 2) := by
  intro t ht
  have hsub : (Finset.univ.filter (fun i => t ≤ edgeY i ^ 2))
      ⊆ ({0} : Finset (Fin 2)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    fin_cases i
    · decide
    · exfalso
      simp [edgeY] at hi
      linarith
  have hcard : (Finset.univ.filter (fun i => t ≤ edgeY i ^ 2)).card
      ≤ ({0} : Finset (Fin 2)).card := Finset.card_le_card hsub
  rw [Fintype.card_fin]
  have h1 : ({0} : Finset (Fin 2)).card = 1 := by decide
  omega

/-- The right-hand total-variation sum at `edgeY`, computed raw:
`|1² - 0²|` across both ordered pairs of the edge. -/
theorem edge_pairsum :
    ∑ i, ∑ j, cheegerEdgeAdj i j * |edgeY i ^ 2 - edgeY j ^ 2| = 2 := by
  simp only [Fin.sum_univ_two, cheegerEdgeAdj, edgeY_zero, edgeY_one]
  norm_num

theorem edge_sumYsq : ∑ i, edgeY i ^ 2 = 1 := by
  simp only [Fin.sum_univ_two, edgeY_zero, edgeY_one]
  norm_num

/-- **The co-area core instantiated on `K₂`** at `edgeY`, through the
theorem (the minority hypothesis supplied by `edgeY_minority`,
load-bearing). -/
theorem coarea_edge_instance_QA :
    2 * (cheegerConstant cheegerEdgeAdj * (1:ℝ) * ∑ i, edgeY i ^ 2)
      ≤ ∑ i, ∑ j, cheegerEdgeAdj i j * |edgeY i ^ 2 - edgeY j ^ 2| :=
  coarea_core cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg 1 cheegerEdgeAdj_regular
    (by norm_num) edgeY edgeY_minority

/-- **The co-area bound is attained with equality on `K₂`:** both sides
evaluate to `2` — `φ = 1` (`edge_cheegerConstant`), `d = 1`, `∑ y² = 1`
against the raw total variation above. A defective constant anywhere in
the layer-cake chain would break this equality. -/
theorem coarea_edge_eq_QA :
    2 * (cheegerConstant cheegerEdgeAdj * (1:ℝ) * ∑ i, edgeY i ^ 2)
      = ∑ i, ∑ j, cheegerEdgeAdj i j * |edgeY i ^ 2 - edgeY j ^ 2| := by
  rw [edge_cheegerConstant, edge_sumYsq, edge_pairsum]
  norm_num

/-- Test function for the strict `C₄` witness: the two-level vector
`![2, 1, 0, 0]`, whose squared values `(4, 1, 0, 0)` exercise two
distinct positive level strata (`{0, 1}` on `(0, 1]`, `{0}` on
`(1, 4]`). -/
def cycY : Fin 4 → ℝ := ![2, 1, 0, 0]

theorem cycY_zero : cycY 0 = 2 := by simp [cycY]

theorem cycY_one : cycY 1 = 1 := by simp [cycY]

theorem cycY_two : cycY 2 = 0 := by simp [cycY]

theorem cycY_three : cycY 3 = 0 := by simp [cycY]

/-- The minority hypothesis holds at `cycY`: every positive level set
sits inside `{0, 1}` (card `2`), and `2 * 2 ≤ 4`. -/
theorem cycY_minority : ∀ t : ℝ, 0 < t →
    2 * (Finset.univ.filter (fun i => t ≤ cycY i ^ 2)).card
      ≤ Fintype.card (Fin 4) := by
  intro t ht
  have hsub : (Finset.univ.filter (fun i => t ≤ cycY i ^ 2))
      ⊆ ({0, 1} : Finset (Fin 4)) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    fin_cases i
    · decide
    · decide
    · exfalso
      simp [cycY] at hi
      linarith
    · exfalso
      simp [cycY] at hi
      linarith
  have hcard : (Finset.univ.filter (fun i => t ≤ cycY i ^ 2)).card
      ≤ ({0, 1} : Finset (Fin 4)).card := Finset.card_le_card hsub
  rw [Fintype.card_fin]
  have h2 : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
  omega

/-- The right-hand total-variation sum at `cycY`, computed raw: the
adjacent pairs of `C₄` contribute `3 + 3` (edge `0-1`), `1 + 1`
(edge `1-2`), `0` (edge `2-3`), `4 + 4` (edge `3-0`) — total `16`. -/
theorem cyc_pairsum :
    ∑ i, ∑ j, cycleAdj4 i j * |cycY i ^ 2 - cycY j ^ 2| = 16 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycY_zero, cycY_one, cycY_two,
    cycY_three]
  norm_num

theorem cyc_sumYsq : ∑ i, cycY i ^ 2 = 5 := by
  simp only [Fin.sum_univ_four, cycY_zero, cycY_one, cycY_two, cycY_three]
  norm_num

/-- **The indicator↔cardinality dictionary pinned on `cycY` at level
`t = 1`:** the closed-set semantics is load-bearing — vertex `1` has
`cycY 1 ^ 2 = 1 = t` and its indicator is `1` (closed superlevel set),
not `0`. -/
theorem sum_indicatorLE_cycY_QA :
    ∑ i, indicatorLE (cycY i ^ 2) 1 = 2 := by
  have h0 : indicatorLE (cycY 0 ^ 2) 1 = 1 := by
    rw [cycY_zero]; exact indicatorLE_of_le (by norm_num)
  have h1 : indicatorLE (cycY 1 ^ 2) 1 = 1 := by
    rw [cycY_one]; exact indicatorLE_of_le (by norm_num)
  have h2 : indicatorLE (cycY 2 ^ 2) 1 = 0 := by
    rw [cycY_two]; exact indicatorLE_of_lt (by norm_num)
  have h3 : indicatorLE (cycY 3 ^ 2) 1 = 0 := by
    rw [cycY_three]; exact indicatorLE_of_lt (by norm_num)
  simp only [Fin.sum_univ_four, h0, h1, h2, h3]
  norm_num

/-- **The co-area core instantiated on `C₄`** at the multi-level
`cycY`, through the theorem. -/
theorem coarea_cycle_instance_QA :
    2 * (cheegerConstant cycleAdj4 * 2 * ∑ i, cycY i ^ 2)
      ≤ ∑ i, ∑ j, cycleAdj4 i j * |cycY i ^ 2 - cycY j ^ 2| :=
  coarea_core cycleAdj4 cycleAdj4_isSymm cycleAdj4_nonneg 2 cycleAdj4_deg
    (by norm_num) cycY cycY_minority

/-- **The co-area bound is strict on the `C₄` witness:** the left side
is `2 * φ * 2 * 5 = 20 * φ ≤ 10` (via the adjacent-pair cut's
conducted conductance `φ ≤ 1/2`), strictly below the raw total
variation `16`. -/
theorem coarea_cycle_lt_QA :
    2 * (cheegerConstant cycleAdj4 * 2 * ∑ i, cycY i ^ 2)
      < ∑ i, ∑ j, cycleAdj4 i j * |cycY i ^ 2 - cycY j ^ 2| := by
  have hφ : cheegerConstant cycleAdj4 ≤ 1 / 2 :=
    le_trans (conductance_ge_cheegerConstant cycleAdj4 cycleAdj4_nonneg
      {0, 1} (by decide) (by decide)) (le_of_eq cyc_conductance_01)
  rw [cyc_sumYsq, cyc_pairsum]
  nlinarith

/-- The minority-hypothesis-free conclusion is refuted on `K₂` at
`![1, 1]`: the level set at `t = 1` is everything, so the hypothesis
provably fails (both vertices on the majority side), while every other
hypothesis of the theorem holds on the fixture — the minority
hypothesis is the load-bearing one. -/
def edgeOnes : Fin 2 → ℝ := ![1, 1]

theorem edgeOnes_minority_fails :
    ¬ (∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ edgeOnes i ^ 2)).card
        ≤ Fintype.card (Fin 2)) := by
  intro h
  have h1 := h 1 (by norm_num)
  have hcard : (Finset.univ.filter (fun i => (1:ℝ) ≤ edgeOnes i ^ 2)).card
      = 2 := by
    have huniv : (Finset.univ.filter (fun i => (1:ℝ) ≤ edgeOnes i ^ 2))
        = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_univ]
      fin_cases i <;> simp [edgeOnes]
    rw [huniv, Finset.card_univ, Fintype.card_fin]
  rw [hcard, Fintype.card_fin] at h1
  norm_num at h1

/-- **Minority refuted-on-omission:** at `![1, 1]` the hypothesis-free
statement reads `4 ≤ 0` (left side `2 * 1 * 1 * 2` against vanishing
total variation) — false, with the failure isolated at the minority
hypothesis by `edgeOnes_minority_fails`. -/
theorem coarea_minority_refuted_QA :
    ¬ (2 * (cheegerConstant cheegerEdgeAdj * (1:ℝ) * ∑ i, edgeOnes i ^ 2)
      ≤ ∑ i, ∑ j, cheegerEdgeAdj i j * |edgeOnes i ^ 2 - edgeOnes j ^ 2|) := by
  intro h
  rw [edge_cheegerConstant] at h
  simp only [Fin.sum_univ_two, cheegerEdgeAdj, edgeOnes] at h
  norm_num at h

end HardDirectionStep1b

/-!
## The hard direction, Step 1c: median + assembly (witnesses)

The final layer of the Cheeger hard-direction program
(`proposals/discharge-perturbation-axioms.md` Step 1c, added 2026-08-23,
all proved, zero axioms): median existence, the per-part composition,
the norm split, the sweep lemma, and the retirement of
`cheeger_lower_bound` to a proved theorem. The witnesses pin each new
layer numerically: the median forced into its interval on a tie-heavy
`Fin 4` fixture, the per-part bound at the Step-1b `K₂` equality data,
the norm split's exact `+ n·m²` remainder at two medians, and the sweep
on `K₂` (`1/2 ≤ 2`, against the pinned `λ₂`) and on `C₄` (`φ²/2 ≤ 1/8 <
1 = R`, at `d = 2`).
-/

section HardDirectionStep1c

/-- Tie-heavy test vector `![1, 1, -1, -1]` on `Fin 4` for the median
witness: both values repeated twice, so any valid median must land in
`[-1, 1]` — a value above `1` or below `-1` puts all four values on one
strict side, violating one of the two at-most-half counts. -/
def tieX : Fin 4 → ℝ := ![1, 1, -1, -1]

theorem tieX_val : ∀ i : Fin 4, tieX i = 1 ∨ tieX i = -1 := by
  intro i
  fin_cases i <;> simp [tieX]

/-- **The median is forced into its interval on the tie-heavy fixture:**
the theorem's returned `m` satisfies `-1 ≤ m ≤ 1`. A defective median
(off-by-one counting, min/max of the values) would return `m > 1` or
`m < -1`, and the corresponding at-most-half count would read `2 * 4 ≤
4` — refuted. -/
theorem median_fin4_QA :
    ∃ m : ℝ, -1 ≤ m ∧ m ≤ 1 := by
  obtain ⟨m, hup, hlow⟩ := exists_median (tieX : Fin 4 → ℝ)
  refine ⟨m, ?_, ?_⟩
  · by_contra hc
    push_neg at hc
    have hfull : (Finset.univ.filter (fun i => m < tieX i))
        = (Finset.univ : Finset (Fin 4)) :=
      Finset.eq_univ_iff_forall.2 fun i => Finset.mem_filter.2
        ⟨Finset.mem_univ i, by
          rcases tieX_val i with h | h <;> rw [h] <;> linarith⟩
    rw [hfull, Finset.card_univ, Fintype.card_fin] at hup
    norm_num at hup
  · by_contra hc
    push_neg at hc
    have hfull : (Finset.univ.filter (fun i => tieX i < m))
        = (Finset.univ : Finset (Fin 4)) :=
      Finset.eq_univ_iff_forall.2 fun i => Finset.mem_filter.2
        ⟨Finset.mem_univ i, by
          rcases tieX_val i with h | h <;> rw [h] <;> linarith⟩
    rw [hfull, Finset.card_univ, Fintype.card_fin] at hlow
    norm_num at hlow

/-- The Dirichlet double sum at `edgeY`, computed raw: `(1 - 0)²` across
both ordered pairs of the edge. -/
theorem edge_energy_Y :
    ∑ i, ∑ j, cheegerEdgeAdj i j * (edgeY i - edgeY j) ^ 2 = 2 := by
  simp only [Fin.sum_univ_two, cheegerEdgeAdj, edgeY_zero, edgeY_one]
  norm_num

/-- **The per-part bound instantiated on `K₂`** at the Step-1b equality
fixture `edgeY` (the minority hypothesis supplied by `edgeY_minority`,
load-bearing). -/
theorem perPart_edge_QA :
    cheegerConstant cheegerEdgeAdj ^ 2 * (1:ℝ) * ∑ i, edgeY i ^ 2
      ≤ ∑ i, ∑ j, cheegerEdgeAdj i j * (edgeY i - edgeY j) ^ 2 :=
  hardDirection_perPart cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg 1
    cheegerEdgeAdj_regular (by norm_num) edgeY edgeY_minority

/-- **The per-part bound pinned numerically:** the left side is exactly
`φ² · d · ∑ y² = 1` against the raw energy `2` — the composition of the
Step-1b co-area core (itself at equality, `2 ≤ 2`) with the Step-1a
Cauchy–Schwarz core (strict, `4 ≤ 8`), so the composed bound inherits
coarea's tight left factor. -/
theorem perPart_edge_eq_QA :
    cheegerConstant cheegerEdgeAdj ^ 2 * (1:ℝ) * ∑ i, edgeY i ^ 2 = 1
      ∧ ∑ i, ∑ j, cheegerEdgeAdj i j * (edgeY i - edgeY j) ^ 2 = 2 := by
  rw [edge_cheegerConstant, edge_sumYsq, edge_energy_Y]
  norm_num

/-- Test vector `![1, -1, 3, -3]` on `Fin 4` for the norm-split witness:
orthogonal to `1`, with squared mass `20`. -/
def normX : Fin 4 → ℝ := ![1, -1, 3, -3]

theorem normX_val_zero : normX 0 = 1 := by simp [normX]

theorem normX_val_one : normX 1 = -1 := by simp [normX]

theorem normX_val_two : normX 2 = 3 := by simp [normX]

theorem normX_val_three : normX 3 = -3 := by simp [normX]

theorem normX_orth : Matrix.dotProduct normX onesVec = 0 := by
  simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_four,
    normX_val_zero, normX_val_one, normX_val_two, normX_val_three]
  norm_num

theorem normX_sumsq : ∑ i, normX i ^ 2 = 20 := by
  simp only [Fin.sum_univ_four, normX_val_zero, normX_val_one,
    normX_val_two, normX_val_three]
  norm_num

/-- **The norm split's exact remainder, at the trivial median `m = 0`:**
the two parts carry exactly `∑ x² = 20` (one part vanishes on each
side; no `n·m²` remainder). -/
theorem median_parts_norm_fin4_m0_QA :
    (∑ i, (max (normX i - 0) 0) ^ 2
        + ∑ i, (max (0 - normX i) 0) ^ 2) = 20 := by
  simp only [Fin.sum_univ_four, normX_val_zero, normX_val_one,
    normX_val_two, normX_val_three]
  norm_num

/-- **The norm split at the nontrivial median `m = 1`:** the two parts
carry `24 = 20 + 4 · 1²` — the `n·m²` remainder visible — and the
theorem's inequality is the strict `20 ≤ 24`. -/
theorem median_parts_norm_fin4_m1_QA :
    ∑ i, normX i ^ 2
      ≤ ∑ i, (max (normX i - 1) 0) ^ 2 + ∑ i, (max (1 - normX i) 0) ^ 2
        ∧ (∑ i, (max (normX i - 1) 0) ^ 2
            + ∑ i, (max (1 - normX i) 0) ^ 2) = 24 := by
  constructor
  · exact median_parts_norm (m := 1) normX_orth
  · simp only [Fin.sum_univ_four, normX_val_zero, normX_val_one,
      normX_val_two, normX_val_three]
    norm_num

/-- Test vector `![1, 0, -1, 0]` on `Fin 4` for the `C₄` sweep witness:
orthogonal to `1`, the normalized-Laplacian eigen-shape of the cycle. -/
def cycSweepX : Fin 4 → ℝ := ![1, 0, -1, 0]

theorem cycSweepX_val_zero : cycSweepX 0 = 1 := by simp [cycSweepX]

theorem cycSweepX_val_one : cycSweepX 1 = 0 := by simp [cycSweepX]

theorem cycSweepX_val_two : cycSweepX 2 = -1 := by simp [cycSweepX]

theorem cycSweepX_val_three : cycSweepX 3 = 0 := by simp [cycSweepX]

theorem cycSweepX_ne_zero : cycSweepX ≠ 0 := by
  intro h
  have h0 : cycSweepX 0 = 0 := congrFun h 0
  rw [cycSweepX_val_zero] at h0
  norm_num at h0

theorem cycSweepX_orth : Matrix.dotProduct cycSweepX onesVec = 0 := by
  simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_four,
    cycSweepX_val_zero, cycSweepX_val_one, cycSweepX_val_two,
    cycSweepX_val_three]
  norm_num

/-- The Dirichlet double sum of the sweep vector on `C₄`, raw: each of
the four edges contributes `1` twice, total `8`. -/
theorem cycSweepX_energy :
    ∑ i, ∑ j, cycleAdj4 i j * (cycSweepX i - cycSweepX j) ^ 2 = 8 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycSweepX_val_zero,
    cycSweepX_val_one, cycSweepX_val_two, cycSweepX_val_three]
  norm_num

theorem cycSweepX_dot :
    Matrix.dotProduct cycSweepX cycSweepX = 2 := by
  simp only [Matrix.dotProduct, Fin.sum_univ_four, cycSweepX_val_zero,
    cycSweepX_val_one, cycSweepX_val_two, cycSweepX_val_three]
  norm_num

/-- The sweep vector's Rayleigh quotient on `C₄` (`d = 2`), through the
Step-1a normalization: `E' / (2 · d · ‖x‖²) = 8 / 8 = 1` — the classical
`λ₂` of the normalized cycle Laplacian. -/
theorem cycSweepX_rayleigh :
    rayleigh (regularNormalizedLaplacian cycleAdj4 2) cycSweepX = 1 := by
  rw [rayleigh_regularNormalizedLaplacian_eq cycleAdj4 cycleAdj4_isSymm 2
    cycleAdj4_deg (by norm_num) cycSweepX_ne_zero, cycSweepX_energy,
    cycSweepX_dot]
  norm_num

/-- **The sweep lemma instantiated on `K₂`:** `φ²/2 = 1/2 ≤
R(![1, -1])` — through the theorem, with the quotient independently
pinned at `2` (`rayleigh_regularNormalizedLaplacian_edge_eq_QA`), the
same value as the pinned `λ₂`. A defective constant anywhere in the 1c
chain would fail this instance. -/
theorem sweep_edge_QA :
    (1:ℝ) / 2
      ≤ rayleigh (regularNormalizedLaplacian cheegerEdgeAdj 1) ![1, -1] := by
  have h := cheeger_sweep cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg 1
    cheegerEdgeAdj_regular (by norm_num) (by
      intro h
      have h0 : (![1, -1] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
      norm_num at h0) (by
      simp only [Matrix.dotProduct, onesVec, mul_one, Fin.sum_univ_two]
      norm_num)
  rw [edge_cheegerConstant] at h
  norm_num at h
  exact h

/-- **The sweep lemma instantiated on `C₄`** (`d = 2`, a non-unit
degree): `φ²/2 ≤ R(cycSweepX)`. -/
theorem sweep_cycle_QA :
    cheegerConstant cycleAdj4 ^ 2 / 2
      ≤ rayleigh (regularNormalizedLaplacian cycleAdj4 2) cycSweepX :=
  cheeger_sweep cycleAdj4 cycleAdj4_isSymm cycleAdj4_nonneg 2
    cycleAdj4_deg (by norm_num) cycSweepX_ne_zero cycSweepX_orth

/-- **The visible gap on `C₄`:** `φ ≤ 1/2` (the adjacent-pair cut's
exhaustively computed conductance) makes `φ²/2 ≤ 1/8 < 1 = R` — the
sweep bound is honest with a wide margin at this non-critical vector. -/
theorem sweep_cycle_gap_QA :
    cheegerConstant cycleAdj4 ^ 2 / 2
      < rayleigh (regularNormalizedLaplacian cycleAdj4 2) cycSweepX := by
  have hφ : cheegerConstant cycleAdj4 ≤ 1 / 2 :=
    le_trans (conductance_ge_cheegerConstant cycleAdj4 cycleAdj4_nonneg
      {0, 1} (by decide) (by decide)) (le_of_eq cyc_conductance_01)
  have hφ0 : 0 ≤ cheegerConstant cycleAdj4 :=
    cheegerConstant_nonneg cycleAdj4 cycleAdj4_nonneg
  rw [cycSweepX_rayleigh]
  nlinarith

/-- **The retired bound instantiated on `K₂`:** `φ²/2 = 1/2 ≤
λ₂(L_sym) = 2` — through the proved `cheeger_lower_bound`, with both
endpoints independently pinned (`edge_cheegerConstant`,
`edge_normLap_secondEval_eq_two_QA`). Previously this instantiation
consumed the admitted axiom; it is now hard crust. -/
theorem cheeger_lower_bound_edge_QA :
    (1:ℝ) / 2
      ≤ secondEval (regularNormalizedLaplacian cheegerEdgeAdj 1)
          (regularNormalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric 1)
          (le_refl 2) := by
  rw [edge_normLap_secondEval_eq_two_QA]
  have h := cheeger_lower_bound cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg 1
    cheegerEdgeAdj_regular (by norm_num) (le_refl 2)
  rw [edge_cheegerConstant, edge_normLap_secondEval_eq_two_QA] at h
  simpa using h

end HardDirectionStep1c

/-!
## Sweep-extraction witnesses (`proposals/sweep-cut-extraction.md`)

The swept-level-set extraction (`sweep_level_extract` and
`cheeger_sweep_cut`, proved 2026-08-24 in `GraphTheory.Cheeger`)
exercised on the `C₄` fixture: the per-part extraction's returned set
*forced* through its level-membership iff, the assembled sweep family
characterized at two orthogonal test vectors (at `cycX2` the swept cut
ties the global optimum `1/2`; at `cycSweepX` the best swept cut is
`1`, honestly inside the bound `2`), and the orthogonality hypothesis
refuted on the constant vector — whose sweep family has no nonempty
proper member at all, so the hypothesis-free conclusion is false for
*every* set, not merely uncertified.
-/

section SweepExtractionQA

/-- Conductance of either singleton on `C₄`: boundary `2` over the
minority volume `2`. -/
theorem cyc_conductance_single (i : Fin 4) :
    conductance cycleAdj4 {i} = 1 := by
  have hb : boundary cycleAdj4 {i} = 2 := by
    fin_cases i
    · exact cyc_boundary_0
    · exact cyc_boundary_1
    · exact cyc_boundary_2
    · exact cyc_boundary_3
  have hv : vol cycleAdj4 {i} = 2 := by
    rw [vol, Finset.sum_singleton, cycleAdj4_deg i]
  have hvc : vol cycleAdj4 ({i} : Finset (Fin 4))ᶜ = 6 := by
    have h := vol_compl cycleAdj4 {i}
    rw [hv, cyc_vol_univ] at h
    linarith
  rw [conductance, hb, hv, hvc, min_eq_left (by linarith : (2 : ℝ) ≤ 6)]
  rw [div_self two_ne_zero]

/-- Conductance of the adjacent pair `{2, 3}` on `C₄`. -/
theorem cyc_conductance_23 :
    conductance cycleAdj4 ({2, 3} : Finset (Fin 4)) = 1 / 2 := by
  have hv : vol cycleAdj4 ({2, 3} : Finset (Fin 4)) = 4 := by
    rw [vol]; simp [cycleAdj4_deg]; norm_num
  have hvc : vol cycleAdj4 ({2, 3} : Finset (Fin 4))ᶜ = 4 := by
    have h := vol_compl cycleAdj4 ({2, 3} : Finset (Fin 4))
    rw [hv, cyc_vol_univ] at h
    linarith
  rw [conductance, cyc_boundary_23, hv, hvc, min_eq_left (le_refl (4 : ℝ))]
  norm_num

/-- Conductance of the triple `{0, 1, 3}` on `C₄`: boundary `2` over
the minority (complement) volume `2`. -/
theorem cyc_conductance_013 :
    conductance cycleAdj4 ({0, 1, 3} : Finset (Fin 4)) = 1 := by
  have hv : vol cycleAdj4 ({0, 1, 3} : Finset (Fin 4)) = 6 := by
    rw [vol]; simp [cycleAdj4_deg]; norm_num
  have hvc : vol cycleAdj4 ({0, 1, 3} : Finset (Fin 4))ᶜ = 2 := by
    have h := vol_compl cycleAdj4 ({0, 1, 3} : Finset (Fin 4))
    rw [hv, cyc_vol_univ] at h
    linarith
  rw [conductance, cyc_boundary_013, hv, hvc,
    min_eq_right (by linarith : (2 : ℝ) ≤ 6)]
  rw [div_self two_ne_zero]

/-- Conductance of the triple `{1, 2, 3}` on `C₄`. -/
theorem cyc_conductance_123 :
    conductance cycleAdj4 ({1, 2, 3} : Finset (Fin 4)) = 1 := by
  have hv : vol cycleAdj4 ({1, 2, 3} : Finset (Fin 4)) = 6 := by
    rw [vol]; simp [cycleAdj4_deg]; norm_num
  have hvc : vol cycleAdj4 ({1, 2, 3} : Finset (Fin 4))ᶜ = 2 := by
    have h := vol_compl cycleAdj4 ({1, 2, 3} : Finset (Fin 4))
    rw [hv, cyc_vol_univ] at h
    linarith
  rw [conductance, cyc_boundary_123, hv, hvc,
    min_eq_right (by linarith : (2 : ℝ) ≤ 6)]
  rw [div_self two_ne_zero]

/-- **The sweep family of `cycSweepX`** (values `1, 0, -1, 0`): every
nonempty proper closed superlevel or sublevel set is one of the four
pinned cuts — each of conductance `1`. -/
theorem cycSweepX_family (S : Finset (Fin 4)) (hS : S.Nonempty)
    (hSc : Sᶜ.Nonempty)
    (hfam : (∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ cycSweepX i) ∨
      (∃ t : ℝ, ∀ i, i ∈ S ↔ cycSweepX i ≤ t)) :
    S = ({0} : Finset (Fin 4)) ∨ S = ({2} : Finset (Fin 4))
      ∨ S = ({0, 1, 3} : Finset (Fin 4)) ∨ S = ({1, 2, 3} : Finset (Fin 4)) := by
  rcases hfam with ⟨t, ht⟩ | ⟨t, ht⟩
  · by_cases hA : t ≤ cycSweepX 2
    · exfalso
      have hA' : t ≤ -1 := by rw [← cycSweepX_val_two]; exact hA
      have h0 : (0 : Fin 4) ∈ S := by
        refine (ht 0).2 ?_
        rw [cycSweepX_val_zero]; linarith
      have h1 : (1 : Fin 4) ∈ S := by
        refine (ht 1).2 ?_
        rw [cycSweepX_val_one]; linarith
      have h2 : (2 : Fin 4) ∈ S := (ht 2).2 hA
      have h3 : (3 : Fin 4) ∈ S := by
        refine (ht 3).2 ?_
        rw [cycSweepX_val_three]; linarith
      have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3)
      rw [hEq] at hSc
      exact absurd hSc (by simp)
    · by_cases hB : t ≤ cycSweepX 1
      · refine Or.inr (Or.inr (Or.inl ?_))
        have hB' : t ≤ 0 := by rw [← cycSweepX_val_one]; exact hB
        have h0 : (0 : Fin 4) ∈ S := by
          refine (ht 0).2 ?_
          rw [cycSweepX_val_zero]; linarith
        have h1 : (1 : Fin 4) ∈ S := (ht 1).2 hB
        have h3 : (3 : Fin 4) ∈ S := by
          refine (ht 3).2 ?_
          rw [cycSweepX_val_three]; linarith
        have h2 : (2 : Fin 4) ∉ S := fun hc => hA ((ht 2).1 hc)
        apply Finset.ext
        intro i
        fin_cases i
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
      · by_cases hC : t ≤ cycSweepX 0
        · refine Or.inl ?_
          have h0 : (0 : Fin 4) ∈ S := (ht 0).2 hC
          have h1 : (1 : Fin 4) ∉ S := fun hc => hB ((ht 1).1 hc)
          have h2 : (2 : Fin 4) ∉ S := fun hc => hA ((ht 2).1 hc)
          have h3 : (3 : Fin 4) ∉ S := fun hc => hB ((ht 3).1 hc)
          apply Finset.ext
          intro i
          fin_cases i
          · simp [h0]
          · simp [h1]
          · simp [h2]
          · simp [h3]
        · exfalso
          have h0 : (0 : Fin 4) ∉ S := fun hc => hC ((ht 0).1 hc)
          have h1 : (1 : Fin 4) ∉ S := fun hc => hB ((ht 1).1 hc)
          have h2 : (2 : Fin 4) ∉ S := fun hc => hA ((ht 2).1 hc)
          have h3 : (3 : Fin 4) ∉ S := fun hc => hB ((ht 3).1 hc)
          have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
            intro i hi
            fin_cases i
            · exact h0 hi
            · exact h1 hi
            · exact h2 hi
            · exact h3 hi)
          rw [hEq] at hS
          simp at hS
  · by_cases hA : cycSweepX 0 ≤ t
    · exfalso
      have hA' : 1 ≤ t := by rw [← cycSweepX_val_zero]; exact hA
      have h0 : (0 : Fin 4) ∈ S := (ht 0).2 hA
      have h1 : (1 : Fin 4) ∈ S := by
        refine (ht 1).2 ?_
        rw [cycSweepX_val_one]; linarith
      have h2 : (2 : Fin 4) ∈ S := by
        refine (ht 2).2 ?_
        rw [cycSweepX_val_two]; linarith
      have h3 : (3 : Fin 4) ∈ S := by
        refine (ht 3).2 ?_
        rw [cycSweepX_val_three]; linarith
      have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3)
      rw [hEq] at hSc
      exact absurd hSc (by simp)
    · by_cases hB : cycSweepX 1 ≤ t
      · refine Or.inr (Or.inr (Or.inr ?_))
        have hB' : 0 ≤ t := by rw [← cycSweepX_val_one]; exact hB
        have h1 : (1 : Fin 4) ∈ S := (ht 1).2 hB
        have h2 : (2 : Fin 4) ∈ S := by
          refine (ht 2).2 ?_
          rw [cycSweepX_val_two]; linarith
        have h3 : (3 : Fin 4) ∈ S := by
          refine (ht 3).2 ?_
          rw [cycSweepX_val_three]; linarith
        have h0 : (0 : Fin 4) ∉ S := fun hc => hA ((ht 0).1 hc)
        apply Finset.ext
        intro i
        fin_cases i
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
      · by_cases hC : cycSweepX 2 ≤ t
        · refine Or.inr (Or.inl ?_)
          have h2 : (2 : Fin 4) ∈ S := (ht 2).2 hC
          have h0 : (0 : Fin 4) ∉ S := fun hc => hA ((ht 0).1 hc)
          have h1 : (1 : Fin 4) ∉ S := fun hc => hB ((ht 1).1 hc)
          have h3 : (3 : Fin 4) ∉ S := fun hc => hB ((ht 3).1 hc)
          apply Finset.ext
          intro i
          fin_cases i
          · simp [h0]
          · simp [h1]
          · simp [h2]
          · simp [h3]
        · exfalso
          have h0 : (0 : Fin 4) ∉ S := fun hc => hA ((ht 0).1 hc)
          have h1 : (1 : Fin 4) ∉ S := fun hc => hB ((ht 1).1 hc)
          have h2 : (2 : Fin 4) ∉ S := fun hc => hC ((ht 2).1 hc)
          have h3 : (3 : Fin 4) ∉ S := fun hc => hB ((ht 3).1 hc)
          have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
            intro i hi
            fin_cases i
            · exact h0 hi
            · exact h1 hi
            · exact h2 hi
            · exact h3 hi)
          rw [hEq] at hS
          simp at hS

theorem cycX2_ne_zero : cycX2 ≠ 0 := by
  intro h
  have h0 : (cycX2 : Fin 4 → ℝ) 0 = 0 := congrFun h 0
  simp [cycX2] at h0

theorem cycX2_dot : Matrix.dotProduct cycX2 cycX2 = 4 := by
  simp [Matrix.dotProduct, Fin.sum_univ_four, cycX2]; norm_num

/-- The Rayleigh quotient of `cycX2` (`d = 2`): `16 / (2 · 2 · 4) = 1`
through the Step-1a normalization and the pinned energy `16`. -/
theorem cycX2_rayleigh :
    rayleigh (regularNormalizedLaplacian cycleAdj4 2) cycX2 = 1 := by
  rw [rayleigh_regularNormalizedLaplacian_eq cycleAdj4 cycleAdj4_isSymm 2
    cycleAdj4_deg (by norm_num) cycX2_ne_zero, cycX2_E', cycX2_dot]
  norm_num

/-- **The sweep family of `cycX2`** (values `1, 1, -1, -1`): the
nonempty proper members are exactly the two dominant halves. -/
theorem cycX2_family (S : Finset (Fin 4)) (hS : S.Nonempty)
    (hSc : Sᶜ.Nonempty)
    (hfam : (∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ cycX2 i) ∨
      (∃ t : ℝ, ∀ i, i ∈ S ↔ cycX2 i ≤ t)) :
    S = ({0, 1} : Finset (Fin 4)) ∨ S = ({2, 3} : Finset (Fin 4)) := by
  rcases hfam with ⟨t, ht⟩ | ⟨t, ht⟩
  · by_cases hA : t ≤ cycX2 2
    · exfalso
      have hA' : t ≤ -1 := by rw [← show cycX2 2 = -1 by rfl]; exact hA
      have h0 : (0 : Fin 4) ∈ S := by
        refine (ht 0).2 ?_
        rw [show cycX2 0 = 1 by rfl]; linarith
      have h1 : (1 : Fin 4) ∈ S := by
        refine (ht 1).2 ?_
        rw [show cycX2 1 = 1 by rfl]; linarith
      have h2 : (2 : Fin 4) ∈ S := (ht 2).2 hA
      have h3 : (3 : Fin 4) ∈ S := by
        refine (ht 3).2 ?_
        rw [show cycX2 3 = -1 by rfl]; linarith
      have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3)
      rw [hEq] at hSc
      exact absurd hSc (by simp)
    · by_cases hB : t ≤ cycX2 0
      · refine Or.inl ?_
        have h0 : (0 : Fin 4) ∈ S := (ht 0).2 hB
        have h1 : (1 : Fin 4) ∈ S := (ht 1).2 (by
          rw [show cycX2 1 = cycX2 0 from rfl]; exact hB)
        have h2 : (2 : Fin 4) ∉ S := fun hc => hA ((ht 2).1 hc)
        have h3 : (3 : Fin 4) ∉ S := fun hc => hA ((ht 3).1 hc)
        apply Finset.ext
        intro i
        fin_cases i
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
      · exfalso
        have h0 : (0 : Fin 4) ∉ S := fun hc => hB ((ht 0).1 hc)
        have h1 : (1 : Fin 4) ∉ S := fun hc => hB ((ht 1).1 hc)
        have h2 : (2 : Fin 4) ∉ S := fun hc => hA ((ht 2).1 hc)
        have h3 : (3 : Fin 4) ∉ S := fun hc => hA ((ht 3).1 hc)
        have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
          intro i hi
          fin_cases i
          · exact h0 hi
          · exact h1 hi
          · exact h2 hi
          · exact h3 hi)
        rw [hEq] at hS
        simp at hS
  · by_cases hA : cycX2 0 ≤ t
    · exfalso
      have hA' : 1 ≤ t := by rw [← show cycX2 0 = 1 by rfl]; exact hA
      have h0 : (0 : Fin 4) ∈ S := (ht 0).2 hA
      have h1 : (1 : Fin 4) ∈ S := by
        refine (ht 1).2 ?_
        rw [show cycX2 1 = 1 by rfl]; linarith
      have h2 : (2 : Fin 4) ∈ S := by
        refine (ht 2).2 ?_
        rw [show cycX2 2 = -1 by rfl]; linarith
      have h3 : (3 : Fin 4) ∈ S := by
        refine (ht 3).2 ?_
        rw [show cycX2 3 = -1 by rfl]; linarith
      have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3)
      rw [hEq] at hSc
      exact absurd hSc (by simp)
    · by_cases hB : cycX2 2 ≤ t
      · refine Or.inr ?_
        have h2 : (2 : Fin 4) ∈ S := (ht 2).2 hB
        have h3 : (3 : Fin 4) ∈ S := (ht 3).2 (by
          rw [show cycX2 3 = cycX2 2 from rfl]; exact hB)
        have h0 : (0 : Fin 4) ∉ S := fun hc => hA ((ht 0).1 hc)
        have h1 : (1 : Fin 4) ∉ S := fun hc => hA ((ht 1).1 hc)
        apply Finset.ext
        intro i
        fin_cases i
        · simp [h0]
        · simp [h1]
        · simp [h2]
        · simp [h3]
      · exfalso
        have h0 : (0 : Fin 4) ∉ S := fun hc => hA ((ht 0).1 hc)
        have h1 : (1 : Fin 4) ∉ S := fun hc => hA ((ht 1).1 hc)
        have h2 : (2 : Fin 4) ∉ S := fun hc => hB ((ht 2).1 hc)
        have h3 : (3 : Fin 4) ∉ S := fun hc => hB ((ht 3).1 hc)
        have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
          intro i hi
          fin_cases i
          · exact h0 hi
          · exact h1 hi
          · exact h2 hi
          · exact h3 hi)
        rw [hEq] at hS
        simp at hS

/-- **`cheeger_sweep_cut` instantiated at `cycSweepX`:** whatever set
the theorem returns lies in the characterized family, hence has
conductance exactly `1`, and the theorem bound reads `1 ≤ 2 · R = 2`
against the pinned `R = 1` (`cycSweepX_rayleigh`). The swept cut here
is *not* the global optimum (`1/2`, the adjacent pairs) — the theorem
honestly does not promise that. -/
theorem sweep_cut_cycle_QA :
    ∃ S : Finset (Fin 4), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ cycSweepX i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ cycSweepX i ≤ t)) ∧
      conductance cycleAdj4 S = 1 ∧
      conductance cycleAdj4 S ^ 2
        ≤ 2 * rayleigh (regularNormalizedLaplacian cycleAdj4 2) cycSweepX := by
  obtain ⟨S, hS, hSc, hfam, hle⟩ :=
    cheeger_sweep_cut cycleAdj4 cycleAdj4_isSymm cycleAdj4_nonneg 2
      cycleAdj4_deg (by norm_num) cycSweepX_ne_zero cycSweepX_orth
  rcases cycSweepX_family S hS hSc hfam with h | h | h | h
  · exact ⟨S, hS, hSc, hfam, by rw [h]; exact cyc_conductance_single 0, hle⟩
  · exact ⟨S, hS, hSc, hfam, by rw [h]; exact cyc_conductance_single 2, hle⟩
  · exact ⟨S, hS, hSc, hfam, by rw [h]; exact cyc_conductance_013, hle⟩
  · exact ⟨S, hS, hSc, hfam, by rw [h]; exact cyc_conductance_123, hle⟩

/-- The bound in numbers: `1 = conductance S ^ 2 ≤ 2 · 1 = 2 · R`, both
endpoints independently pinned. -/
theorem sweep_cut_cycle_numeric_QA :
    ∃ S : Finset (Fin 4), conductance cycleAdj4 S ^ 2 = 1 ∧ (1 : ℝ) ≤ 2 * 1 := by
  obtain ⟨S, -, -, -, h1, h2⟩ := sweep_cut_cycle_QA
  have h3 : conductance cycleAdj4 S ^ 2 = 1 := by rw [h1]; norm_num
  rw [cycSweepX_rayleigh] at h2
  rw [h3] at h2
  exact ⟨S, h3, h2⟩

/-- **`cheeger_sweep_cut` instantiated at `cycX2`, where the sweep is
optimal:** the returned set lies in the two-member family, hence has
conductance exactly `1/2` — *tied with the exhaustively computed best
cut* `cyc_conductance_01` — against the honest bound `2 · R = 2`. The
theorem does not promise optimality; this fixture exhibits it anyway,
marking the tight end of the family's quality range. -/
theorem sweep_cut_cycle_optimal_QA :
    ∃ S : Finset (Fin 4), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ cycX2 i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ cycX2 i ≤ t)) ∧
      conductance cycleAdj4 S = 1 / 2 ∧
      conductance cycleAdj4 S ^ 2
        ≤ 2 * rayleigh (regularNormalizedLaplacian cycleAdj4 2) cycX2 := by
  obtain ⟨S, hS, hSc, hfam, hle⟩ :=
    cheeger_sweep_cut cycleAdj4 cycleAdj4_isSymm cycleAdj4_nonneg 2
      cycleAdj4_deg (by norm_num) cycX2_ne_zero (by
        simp [Matrix.dotProduct, onesVec, Fin.sum_univ_four, cycX2])
  rcases cycX2_family S hS hSc hfam with h | h
  · exact ⟨S, hS, hSc, hfam, by rw [h]; exact cyc_conductance_01, hle⟩
  · exact ⟨S, hS, hSc, hfam, by rw [h]; exact cyc_conductance_23, hle⟩

/-- **The orthogonality fence (proved refutation).** Dropping `x ⊥ 1`,
the hypothesis-free conclusion at the constant vector `onesVec` (whose
Rayleigh quotient is `0`, so the bound demanded is `conductance ≤ 0`)
is false for *every* candidate: the constant vector's sweep family has
no nonempty proper member at all — superlevels and sublevels alike
degenerate to `univ` or `∅`. Exactly `horth` isolated. -/
theorem sweep_cut_orth_dropped_refuted_QA :
    ¬ (∃ S : Finset (Fin 4), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ onesVec i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ onesVec i ≤ t)) ∧
      conductance cycleAdj4 S ^ 2
        ≤ 2 * rayleigh (regularNormalizedLaplacian cycleAdj4 2) onesVec) := by
  rintro ⟨S, hS, hSc, hfam, -⟩
  have hone : ∀ i : Fin 4, onesVec i = 1 := fun i => rfl
  rcases hfam with ⟨t, ht⟩ | ⟨t, ht⟩
  · by_cases h : t ≤ 1
    · have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        exact (ht i).2 (by rw [hone i]; exact h))
      rw [hEq] at hSc
      simp at hSc
    · have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
        intro i hi
        exact h ((ht i).1 hi))
      rw [hEq] at hS
      simp at hS
  · by_cases h : 1 ≤ t
    · have hEq : S = Finset.univ := Finset.eq_univ_iff_forall.2 (by
        intro i
        exact (ht i).2 (by rw [hone i]; exact h))
      rw [hEq] at hSc
      simp at hSc
    · have hEq : S = ∅ := Finset.eq_empty_iff_forall_not_mem.2 (by
        intro i hi
        exact h ((ht i).1 hi))
      rw [hEq] at hS
      simp at hS

/-- Test function for the per-part extraction: the positive part of
`cycSweepX` at the median `0`. -/
def cycPos : Fin 4 → ℝ := ![1, 0, 0, 0]

theorem cycPos_sq (i : Fin 4) :
    cycPos i ^ 2 = if i = 0 then 1 else 0 := by
  fin_cases i <;> simp [cycPos]

theorem cycPos_minority : ∀ t : ℝ, 0 < t →
    2 * (Finset.univ.filter (fun i => t ≤ cycPos i ^ 2)).card
      ≤ Fintype.card (Fin 4) := by
  intro t ht
  have hsub : (Finset.univ.filter (fun i => t ≤ cycPos i ^ 2))
      ⊆ ({0} : Finset (Fin 4)) := by
    intro i hi
    by_cases h0 : i = 0
    · simp [h0]
    · exfalso
      have hc := (Finset.mem_filter.1 hi).2
      rw [cycPos_sq i, if_neg h0] at hc
      linarith
  have hcard := Finset.card_le_card hsub
  simp at hcard
  rw [Fintype.card_fin]
  omega

theorem cycPos_M : ∑ i, cycPos i ^ 2 = 1 := by
  simp [Fin.sum_univ_four, cycPos]

theorem cycPos_E' :
    ∑ i, ∑ j, cycleAdj4 i j * (cycPos i - cycPos j) ^ 2 = 4 := by
  simp only [Fin.sum_univ_four, cycleAdj4, cycPos]; norm_num

/-- **`sweep_level_extract` instantiated at `cycPos`:** the level
membership iff *forces* the extracted set — the filter is a subset of
`{0}` (the sole positive value), and nonemptiness rules out `∅`, so the
returned cut is pinned, its conductance computed to `1` raw, and the
theorem bound reads `1 ≤ 4 / (2 · 1) = 2`. -/
theorem sweep_extract_cycle_QA :
    ∃ S : Finset (Fin 4), ∃ t : ℝ, 0 < t ∧
      (∀ i, i ∈ S ↔ t ≤ cycPos i ^ 2) ∧
      S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance cycleAdj4 S = 1 ∧
      conductance cycleAdj4 S ^ 2
        ≤ (∑ i, ∑ j, cycleAdj4 i j * (cycPos i - cycPos j) ^ 2)
          / (2 * ∑ i, cycPos i ^ 2) := by
  obtain ⟨S, t, ht, hmem, hS, hSc, hcond⟩ :=
    sweep_level_extract cycleAdj4 cycleAdj4_isSymm cycleAdj4_nonneg 2
      cycleAdj4_deg (by norm_num) cycPos cycPos_minority
      (by rw [cycPos_M]; norm_num)
  rcases le_or_lt t 1 with h1 | h1
  · have hsub : S ⊆ ({0} : Finset (Fin 4)) := by
      intro i hi
      by_cases h0 : i = 0
      · simp [h0]
      · exfalso
        have hc := (hmem i).1 hi
        rw [cycPos_sq i, if_neg h0] at hc
        linarith
    rcases Finset.subset_singleton_iff.1 hsub with hE | hE
    · rw [hE] at hS
      simp at hS
    · exact ⟨S, t, ht, hmem, hS, hSc, by rw [hE]; exact cyc_conductance_single 0,
        hcond⟩
  · exfalso
    have hsub : S ⊆ (∅ : Finset (Fin 4)) := by
      intro i hi
      exfalso
      have hc := (hmem i).1 hi
      rw [cycPos_sq i] at hc
      by_cases h0 : i = 0
      · rw [if_pos h0] at hc
        exact h1.not_le hc
      · rw [if_neg h0] at hc
        linarith
    rw [Finset.subset_empty.1 hsub] at hS
    simp at hS

/-- The per-part bound in numbers: `1 = conductance S ^ 2 ≤ 4 / 2`,
both endpoints independently computed. -/
theorem sweep_extract_cycle_numeric_QA :
    ∃ S : Finset (Fin 4), conductance cycleAdj4 S ^ 2 = 1
      ∧ (1 : ℝ) ≤ 4 / (2 * 1) := by
  obtain ⟨S, -, -, -, -, -, h1, h2⟩ := sweep_extract_cycle_QA
  rw [cycPos_E', cycPos_M] at h2
  have h3 : conductance cycleAdj4 S ^ 2 = 1 := by rw [h1]; norm_num
  rw [h3] at h2
  exact ⟨S, h3, h2⟩

end SweepExtractionQA

section RegularFences

/-!
### Fixtures: the signed, wrong-degree, asymmetric, and zero matrices

Five new small fixtures, all `2×2` with rational spectra (see the
proposal `proposals/adversarial-fences-regular-cheeger-family.md` for
the full pricing and the companion-audit note): the signed `d = 2`-regular
`rcSAdj` (kills `hnn` clauses), the nonnegative `d = 3`-regular
`rcPosAdj` (kills `hd` clauses at claimed wrong degrees), the
nonnegative row-regular asymmetric `rcAsymPsdAdj` (kills the PSD
engine's `hA`), and the zero matrix `rcZeroAdj` (the `hdpos` corner of
the upper bound and the cut-test-vector junk corners).
-/

def rcSAdj : Matrix (Fin 2) (Fin 2) ℝ := !![3, -1; -1, 3]

theorem rcSAdj_symmetric : rcSAdj.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rcSAdj]

theorem rcSAdj_not_nonneg : ¬ (∀ i j, 0 ≤ rcSAdj i j) := by
  intro h
  have h01 := h 0 1
  simp only [rcSAdj] at h01
  norm_num at h01

theorem rcSAdj_regular : ∀ i, deg rcSAdj i = 2 := by
  intro i
  fin_cases i <;> norm_num [deg, rcSAdj, Fin.sum_univ_two]

def rcPosAdj : Matrix (Fin 2) (Fin 2) ℝ := !![2, 1; 1, 2]

theorem rcPosAdj_symmetric : rcPosAdj.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rcPosAdj]

theorem rcPosAdj_nonneg : ∀ i j, 0 ≤ rcPosAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rcPosAdj]

theorem rcPosAdj_regular : ∀ i, deg rcPosAdj i = 3 := by
  intro i
  fin_cases i <;> norm_num [deg, rcPosAdj, Fin.sum_univ_two]

theorem rcPosAdj_not_regular_four : ¬ (∀ i, deg rcPosAdj i = 4) := by
  intro h
  have h0 := h 0
  rw [rcPosAdj_regular 0] at h0
  norm_num at h0

theorem rcPosAdj_not_regular_one : ¬ (∀ i, deg rcPosAdj i = 1) := by
  intro h
  have h0 := h 0
  rw [rcPosAdj_regular 0] at h0
  norm_num at h0

theorem rcPosAdj_not_regular_one_eighth : ¬ (∀ i, deg rcPosAdj i = 1 / 8) := by
  intro h
  have h0 := h 0
  rw [rcPosAdj_regular 0] at h0
  norm_num at h0

theorem rcPosAdj_not_regular_forty : ¬ (∀ i, deg rcPosAdj i = 40) := by
  intro h
  have h0 := h 0
  rw [rcPosAdj_regular 0] at h0
  norm_num at h0

def rcAsymPsdAdj : Matrix (Fin 2) (Fin 2) ℝ := !![4, 1; 3, 2]

theorem rcAsymPsdAdj_not_isSymm : ¬ rcAsymPsdAdj.IsSymm := by
  intro h
  have h01 := h.apply 0 1
  simp only [rcAsymPsdAdj] at h01
  norm_num at h01

theorem rcAsymPsdAdj_nonneg : ∀ i j, 0 ≤ rcAsymPsdAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rcAsymPsdAdj]

theorem rcAsymPsdAdj_regular : ∀ i, deg rcAsymPsdAdj i = 5 := by
  intro i
  fin_cases i <;> norm_num [deg, rcAsymPsdAdj, Fin.sum_univ_two]

def rcZeroAdj : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 0, 0]

theorem rcZeroAdj_symmetric : rcZeroAdj.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rcZeroAdj]

theorem rcZeroAdj_nonneg : ∀ i j, 0 ≤ rcZeroAdj i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rcZeroAdj]

theorem rcZeroAdj_regular_zero : ∀ i, deg rcZeroAdj i = 0 := by
  intro i
  fin_cases i <;> norm_num [deg, rcZeroAdj, Fin.sum_univ_two]

theorem rcZeroAdj_not_regular_one : ¬ (∀ i, deg rcZeroAdj i = 1) := by
  intro h
  have h0 := h 0
  rw [rcZeroAdj_regular_zero 0] at h0
  norm_num at h0

/-!
### Conductance pins

The Cheeger constant at each new fixture (the `edge_cheegerConstant`
pattern: both singleton cuts have equal conductance by symmetry).
-/

theorem rcS_boundary_zero : boundary rcSAdj ({0} : Finset (Fin 2)) = -1 := by
  simp only [boundary, Finset.sum_singleton]
  rw [show (({0} : Finset (Fin 2))ᶜ) = {1} from by decide]
  simp [rcSAdj]

theorem rcS_boundary_one : boundary rcSAdj ({1} : Finset (Fin 2)) = -1 := by
  simp only [boundary, Finset.sum_singleton]
  rw [show (({1} : Finset (Fin 2))ᶜ) = {0} from by decide]
  simp [rcSAdj]

theorem rcS_vol_zero : vol rcSAdj ({0} : Finset (Fin 2)) = 2 := by
  simp [vol, rcSAdj_regular]

theorem rcS_vol_one : vol rcSAdj ({1} : Finset (Fin 2)) = 2 := by
  simp [vol, rcSAdj_regular]

theorem rcS_vol_compl_zero : vol rcSAdj (({0} : Finset (Fin 2))ᶜ) = 2 := by
  rw [show (({0} : Finset (Fin 2))ᶜ) = {1} from by decide]
  simp [vol, rcSAdj_regular]

theorem rcS_conductance_single_zero : conductance rcSAdj ({0} : Finset (Fin 2)) = -1 / 2 := by
  rw [conductance, rcS_boundary_zero, rcS_vol_zero, rcS_vol_compl_zero]
  norm_num

theorem rcS_vol_compl_one : vol rcSAdj (({1} : Finset (Fin 2))ᶜ) = 2 := by
  rw [show (({1} : Finset (Fin 2))ᶜ) = {0} from by decide]
  simp [vol, rcSAdj_regular]

theorem rcS_conductance_single_one : conductance rcSAdj ({1} : Finset (Fin 2)) = -1 / 2 := by
  rw [conductance, rcS_boundary_one, rcS_vol_one, rcS_vol_compl_one]
  norm_num

theorem rcS_cheegerConstant : cheegerConstant rcSAdj = -1 / 2 := by
  have hset : {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance rcSAdj S = c} = {-1 / 2} := by
    ext c
    constructor
    · rintro ⟨S, hne, hcn, rfl⟩
      fin_cases S
      · exact absurd hne (by decide)
      · simpa using rcS_conductance_single_zero
      · simpa using rcS_conductance_single_one
      · exact absurd hcn (by decide)
    · rintro ⟨rfl⟩
      exact ⟨{0}, by decide, by decide, rcS_conductance_single_zero⟩
  rw [cheegerConstant, hset]
  simp

theorem rcPos_boundary_zero : boundary rcPosAdj ({0} : Finset (Fin 2)) = 1 := by
  simp only [boundary, Finset.sum_singleton]
  rw [show (({0} : Finset (Fin 2))ᶜ) = {1} from by decide]
  simp [rcPosAdj]

theorem rcPos_boundary_one : boundary rcPosAdj ({1} : Finset (Fin 2)) = 1 := by
  simp only [boundary, Finset.sum_singleton]
  rw [show (({1} : Finset (Fin 2))ᶜ) = {0} from by decide]
  simp [rcPosAdj]

theorem rcPos_vol_zero : vol rcPosAdj ({0} : Finset (Fin 2)) = 3 := by
  simp [vol, rcPosAdj_regular]

theorem rcPos_vol_one : vol rcPosAdj ({1} : Finset (Fin 2)) = 3 := by
  simp [vol, rcPosAdj_regular]

theorem rcPos_vol_compl_zero : vol rcPosAdj (({0} : Finset (Fin 2))ᶜ) = 3 := by
  rw [show (({0} : Finset (Fin 2))ᶜ) = {1} from by decide]
  simp [vol, rcPosAdj_regular]

theorem rcPos_conductance_single_zero :
    conductance rcPosAdj ({0} : Finset (Fin 2)) = 1 / 3 := by
  rw [conductance, rcPos_boundary_zero, rcPos_vol_zero, rcPos_vol_compl_zero]
  norm_num

theorem rcPos_vol_compl_one : vol rcPosAdj (({1} : Finset (Fin 2))ᶜ) = 3 := by
  rw [show (({1} : Finset (Fin 2))ᶜ) = {0} from by decide]
  simp [vol, rcPosAdj_regular]

theorem rcPos_conductance_single_one :
    conductance rcPosAdj ({1} : Finset (Fin 2)) = 1 / 3 := by
  rw [conductance, rcPos_boundary_one, rcPos_vol_one, rcPos_vol_compl_one]
  norm_num

theorem rcPos_cheegerConstant : cheegerConstant rcPosAdj = 1 / 3 := by
  have hset : {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance rcPosAdj S = c} = {1 / 3} := by
    ext c
    constructor
    · rintro ⟨S, hne, hcn, rfl⟩
      fin_cases S
      · exact absurd hne (by decide)
      · simpa using rcPos_conductance_single_zero
      · simpa using rcPos_conductance_single_one
      · exact absurd hcn (by decide)
    · rintro ⟨rfl⟩
      exact ⟨{0}, by decide, by decide, rcPos_conductance_single_zero⟩
  rw [cheegerConstant, hset]
  simp

theorem rcZero_boundary_zero : boundary rcZeroAdj ({0} : Finset (Fin 2)) = 0 := by
  simp only [boundary, Finset.sum_singleton]
  rw [show (({0} : Finset (Fin 2))ᶜ) = {1} from by decide]
  simp [rcZeroAdj]

theorem rcZero_vol_zero : vol rcZeroAdj ({0} : Finset (Fin 2)) = 0 := by
  simp [vol, rcZeroAdj_regular_zero]

theorem rcZero_vol_compl_zero : vol rcZeroAdj (({0} : Finset (Fin 2))ᶜ) = 0 := by
  rw [show (({0} : Finset (Fin 2))ᶜ) = {1} from by decide]
  simp [vol, rcZeroAdj_regular_zero]

/-- The junk-conductance pin: every cut of the zero matrix has
conductance `0/0 = 0`. -/
theorem rcZero_conductance_single_zero :
    conductance rcZeroAdj ({0} : Finset (Fin 2)) = 0 := by
  rw [conductance, rcZero_boundary_zero, rcZero_vol_zero, rcZero_vol_compl_zero]
  norm_num

theorem rcZero_boundary_one : boundary rcZeroAdj ({1} : Finset (Fin 2)) = 0 := by
  simp only [boundary, Finset.sum_singleton]
  rw [show (({1} : Finset (Fin 2))ᶜ) = {0} from by decide]
  simp [rcZeroAdj]

theorem rcZero_vol_one : vol rcZeroAdj ({1} : Finset (Fin 2)) = 0 := by
  simp [vol, rcZeroAdj_regular_zero]

theorem rcZero_vol_compl_one : vol rcZeroAdj (({1} : Finset (Fin 2))ᶜ) = 0 := by
  rw [show (({1} : Finset (Fin 2))ᶜ) = {0} from by decide]
  simp [vol, rcZeroAdj_regular_zero]

theorem rcZero_conductance_single_one :
    conductance rcZeroAdj ({1} : Finset (Fin 2)) = 0 := by
  rw [conductance, rcZero_boundary_one, rcZero_vol_one, rcZero_vol_compl_one]
  norm_num

theorem rcZero_cheegerConstant : cheegerConstant rcZeroAdj = 0 := by
  have hset : {c : ℝ | ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance rcZeroAdj S = c} = {0} := by
    ext c
    constructor
    · rintro ⟨S, hne, hcn, rfl⟩
      fin_cases S
      · exact absurd hne (by decide)
      · simpa using rcZero_conductance_single_zero
      · simpa using rcZero_conductance_single_one
      · exact absurd hcn (by decide)
    · rintro ⟨rfl⟩
      exact ⟨{0}, by decide, by decide, rcZero_conductance_single_zero⟩
  rw [cheegerConstant, hset]
  simp

/-!
### Operator literals and quadratic-form identities

The normalized/combinatorial operators at each fixture, pinned as
literal matrices first (so later proofs never fight `if i = j` inside
sums), then the pointwise quadratic-form identities the engines and
Rayleigh pins consume.
-/

theorem rcS_regNL :
    regularNormalizedLaplacian rcSAdj 2 = !![-1/2, 1/2; 1/2, -1/2] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [regularNormalizedLaplacian, rcSAdj]
  all_goals norm_num

theorem rcPosD1_regNL :
    regularNormalizedLaplacian rcPosAdj 1 = !![-1, -1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [regularNormalizedLaplacian, rcPosAdj]
  all_goals norm_num

theorem rcZero_regNL :
    regularNormalizedLaplacian rcZeroAdj 0 = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [regularNormalizedLaplacian, rcZeroAdj, inv_zero]

theorem rcS_lap :
    laplacian rcSAdj = !![-1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [laplacian, degreeMatrix, deg, rcSAdj, Fin.sum_univ_two]

theorem rcPos_lap :
    laplacian rcPosAdj = !![1, -1; -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [laplacian, degreeMatrix, deg, rcPosAdj, Fin.sum_univ_two]

theorem rcAsym_regNL :
    regularNormalizedLaplacian rcAsymPsdAdj 5 = !![1/5, -1/5; -3/5, 3/5] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [regularNormalizedLaplacian, rcAsymPsdAdj]
  all_goals norm_num

theorem rcE_regNL :
    regularNormalizedLaplacian cheegerEdgeAdj 1 = !![1, -1; -1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [regularNormalizedLaplacian, cheegerEdgeAdj]

theorem rcS_regNL_quadForm (x : Fin 2 → ℝ) :
    quadForm (regularNormalizedLaplacian rcSAdj 2) x
      = -((x 0 - x 1)^2)/2 := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    rcS_regNL, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

theorem rcPosD1_regNL_quadForm (x : Fin 2 → ℝ) :
    quadForm (regularNormalizedLaplacian rcPosAdj 1) x
      = -((x 0 + x 1)^2) := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    rcPosD1_regNL, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

theorem rcS_lap_quadForm (x : Fin 2 → ℝ) :
    quadForm (laplacian rcSAdj) x = -((x 0 - x 1)^2) := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    rcS_lap, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

theorem rcPos_lap_quadForm (x : Fin 2 → ℝ) :
    quadForm (laplacian rcPosAdj) x = (x 0 - x 1)^2 := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    rcPos_lap, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  ring

private theorem rc_vec_ne_zero {v : Fin 2 → ℝ} (h : v 0 ≠ 0) : v ≠ 0 :=
  fun hc => h (congrFun hc 0)

/-!
### The two Fin 2 pinning engines

The eigenvalue-witness route for lower bounds (at two vertices
`secondEval` is the top sorted entry) and the subspace engine route for
upper bounds (the whole-space test family), both private.
-/

private theorem rc_secondEval_ge_of_eigvec {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.IsSymm) {x : Fin 2 → ℝ} {μ : ℝ}
    (hxμ : M *ᵥ x = μ • x) (hx : x ≠ 0) :
    μ ≤ secondEval M hM (le_refl 2) := by
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul hM hx hxμ
  have hlast := eigvalOf_le_evals_last hM (by norm_num) i
  rw [hi] at hlast
  exact hlast

private theorem rc_evals_le_of_quadForm {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.IsSymm) {t : ℝ}
    (hbnd : ∀ x : Fin 2 → ℝ, quadForm M x ≤ t * Matrix.dotProduct x x) :
    secondEval M hM (le_refl 2) ≤ t := by
  refine evals_le_of_linearIndependent hM (k := 2) (by norm_num) (by norm_num)
    (g := (![![1, 0], ![0, 1]] : Fin 2 → (Fin 2 → ℝ))) ?_ ?_
  · rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h0 := congrFun hc 0
    have h1 := congrFun hc 1
    simp only [Finset.sum_apply, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h0 h1
    fin_cases i
    · norm_num at h0; exact h0
    · norm_num at h1; exact h1
  · intro c
    have hvec : (∑ i, c i • (![![1, 0], ![0, 1]] : Fin 2 → (Fin 2 → ℝ)) i) = c := by
      funext j
      rw [Finset.sum_apply]
      fin_cases j <;>
        simp [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
    rw [hvec]
    exact hbnd c

/-!
### Spectrum and Rayleigh pins
-/

theorem rcS_regNL_mulVec_ones :
    (regularNormalizedLaplacian rcSAdj 2) *ᵥ (![1, 1] : Fin 2 → ℝ)
      = (0 : ℝ) • (![1, 1] : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, rcS_regNL,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, smul_eq_mul]
  <;> norm_num

theorem rcS_regNL_secondEval_eq_zero :
    secondEval (regularNormalizedLaplacian rcSAdj 2)
      (regularNormalizedLaplacian_symmetric rcSAdj rcSAdj_symmetric 2)
      (le_refl 2) = 0 := by
  refine le_antisymm (rc_evals_le_of_quadForm _ ?_) ?_
  · intro x
    rw [rcS_regNL_quadForm x, zero_mul]
    have h := sq_nonneg (x 0 - x 1)
    linarith
  · exact rc_secondEval_ge_of_eigvec
      (regularNormalizedLaplacian_symmetric rcSAdj rcSAdj_symmetric 2)
      rcS_regNL_mulVec_ones (rc_vec_ne_zero (by simp))

theorem rcS_lap_mulVec_ones :
    (laplacian rcSAdj) *ᵥ (![1, 1] : Fin 2 → ℝ)
      = (0 : ℝ) • (![1, 1] : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, rcS_lap,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, smul_eq_mul]

theorem rcS_lap_secondEval_eq_zero :
    secondEval (laplacian rcSAdj) (laplacian_symmetric rcSAdj rcSAdj_symmetric)
      (le_refl 2) = 0 := by
  refine le_antisymm (rc_evals_le_of_quadForm _ ?_) ?_
  · intro x
    rw [rcS_lap_quadForm x, zero_mul]
    have h := sq_nonneg (x 0 - x 1)
    linarith
  · exact rc_secondEval_ge_of_eigvec (laplacian_symmetric rcSAdj rcSAdj_symmetric)
      rcS_lap_mulVec_ones (rc_vec_ne_zero (by simp))

theorem rcPosD4_mulVec_mode :
    (regularNormalizedLaplacian rcPosAdj 4) *ᵥ (![1, -1] : Fin 2 → ℝ)
      = ((3 : ℝ)/4) • (![1, -1] : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      regularNormalizedLaplacian, rcPosAdj, smul_eq_mul] <;> norm_num

theorem rcPosD4_secondEval_ge :
    (3/4) ≤ secondEval (regularNormalizedLaplacian rcPosAdj 4)
      (regularNormalizedLaplacian_symmetric rcPosAdj rcPosAdj_symmetric 4)
      (le_refl 2) := by
  exact rc_secondEval_ge_of_eigvec
    (regularNormalizedLaplacian_symmetric rcPosAdj rcPosAdj_symmetric 4)
    rcPosD4_mulVec_mode (rc_vec_ne_zero (by simp))

theorem rcPosD1_secondEval_le_zero :
    secondEval (regularNormalizedLaplacian rcPosAdj 1)
      (regularNormalizedLaplacian_symmetric rcPosAdj rcPosAdj_symmetric 1)
      (le_refl 2) ≤ 0 := by
  refine rc_evals_le_of_quadForm _ ?_
  intro x
  rw [rcPosD1_regNL_quadForm x, zero_mul]
  have h := sq_nonneg (x 0 + x 1)
  linarith

theorem rcPos_lap_mulVec_mode :
    (laplacian rcPosAdj) *ᵥ (![1, -1] : Fin 2 → ℝ)
      = (2 : ℝ) • (![1, -1] : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, rcPos_lap,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, smul_eq_mul]
  <;> norm_num

theorem rcPos_lap_secondEval_ge_two :
    2 ≤ secondEval (laplacian rcPosAdj)
      (laplacian_symmetric rcPosAdj rcPosAdj_symmetric) (le_refl 2) := by
  exact rc_secondEval_ge_of_eigvec
    (laplacian_symmetric rcPosAdj rcPosAdj_symmetric)
    rcPos_lap_mulVec_mode (rc_vec_ne_zero (by simp))

theorem rcPos_lap_secondEval_le_two :
    secondEval (laplacian rcPosAdj)
      (laplacian_symmetric rcPosAdj rcPosAdj_symmetric) (le_refl 2) ≤ 2 := by
  refine rc_evals_le_of_quadForm _ ?_
  intro x
  have hd : Matrix.dotProduct x x = x 0 * x 0 + x 1 * x 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [rcPos_lap_quadForm x, hd]
  have h := sq_nonneg (x 0 + x 1)
  nlinarith [h]

theorem rcZero_regNL_mulVec_e0 :
    (regularNormalizedLaplacian rcZeroAdj 0) *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (1 : ℝ) • (![1, 0] : Fin 2 → ℝ) := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two, rcZero_regNL,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, smul_eq_mul]

theorem rcZero_regNL_secondEval_ge_one :
    1 ≤ secondEval (regularNormalizedLaplacian rcZeroAdj 0)
      (regularNormalizedLaplacian_symmetric rcZeroAdj rcZeroAdj_symmetric 0)
      (le_refl 2) := by
  exact rc_secondEval_ge_of_eigvec
    (regularNormalizedLaplacian_symmetric rcZeroAdj rcZeroAdj_symmetric 0)
    rcZero_regNL_mulVec_e0 (rc_vec_ne_zero (by simp))

/-- Rayleigh pin at the antisymmetric mode of the signed fixture. -/
theorem rcS_regNL_rayleigh_mode :
    rayleigh (regularNormalizedLaplacian rcSAdj 2) (![1, -1] : Fin 2 → ℝ) = -1 := by
  have hne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := rc_vec_ne_zero (by simp)
  have hd : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) (![1, -1] : Fin 2 → ℝ) = 2 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    norm_num
  rw [rayleigh, if_neg hne, rcS_regNL_quadForm, hd]
  norm_num

/-- Rayleigh pin at the constant vector of the wrong-degree-one
fixture: the operator is `!![-1,-1;-1,-1]`, killing every vector. -/
theorem rcPosD1_regNL_rayleigh_mode :
    rayleigh (regularNormalizedLaplacian rcPosAdj 1) (![1, -1] : Fin 2 → ℝ) = 0 := by
  have hne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := rc_vec_ne_zero (by simp)
  have hd : Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) (![1, -1] : Fin 2 → ℝ) = 2 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    norm_num
  rw [rayleigh, if_neg hne, rcPosD1_regNL_quadForm, hd]
  norm_num

/-- Rayleigh of the junk argument `0` is the definitional branch `0`. -/
theorem rcE_regNL_rayleigh_zero :
    rayleigh (regularNormalizedLaplacian cheegerEdgeAdj 1) (0 : Fin 2 → ℝ) = 0 := by
  rw [rayleigh, if_pos rfl]

/-- Rayleigh of the constant vector on the edge: the regular normalized
Laplacian kills `onesVec`, so the quotient is `0`. -/
theorem rcE_regNL_rayleigh_ones :
    rayleigh (regularNormalizedLaplacian cheegerEdgeAdj 1) (onesVec : Fin 2 → ℝ) = 0 := by
  have hne : (onesVec : Fin 2 → ℝ) ≠ 0 := rc_vec_ne_zero (by simp [onesVec])
  have hq : quadForm (regularNormalizedLaplacian cheegerEdgeAdj 1) (onesVec : Fin 2 → ℝ) = 0 := by
    have hmv : (regularNormalizedLaplacian cheegerEdgeAdj 1) *ᵥ (onesVec : Fin 2 → ℝ) = 0 := by
      funext i
      fin_cases i <;>
        simp [Matrix.mulVec, Matrix.dotProduct, onesVec, Fin.sum_univ_two,
          rcE_regNL, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
    rw [quadForm, hmv]
    simp
  rw [rayleigh, if_neg hne, hq]
  norm_num


/-!
### The inequality fences: `cheeger_upper_bound`

Hypothesis order on the shelf: `(hA) (hnonneg) (d) (hd) (hdpos)
(hcard)`. Each fence negates the conclusion at a specific instantiation;
each companion verifies every other clause genuine and the dropped
clause failing.
-/

/-- **Fence (`cheeger_upper_bound`, `hnonneg`)**: at the signed
`d = 2`-regular fixture every other hypothesis is genuine, and the
nonnegativity-dropped conclusion reads `λ₂ = 0 ≤ 2φ = -1` — false. -/
theorem rcF_upper_hnn_fence_QA :
    ¬ (secondEval (regularNormalizedLaplacian rcSAdj 2)
        (regularNormalizedLaplacian_symmetric rcSAdj rcSAdj_symmetric 2)
        (le_refl 2)
      ≤ 2 * cheegerConstant rcSAdj) := by
  rw [rcS_regNL_secondEval_eq_zero, rcS_cheegerConstant]
  norm_num

/-- Isolation companion: every other clause genuine, `hnonneg` exactly
the failure. -/
theorem rcF_upper_hnn_isolation_QA :
    rcSAdj.IsSymm ∧ (∀ i, deg rcSAdj i = 2) ∧ (0 < (2:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (∀ i j, 0 ≤ rcSAdj i j) :=
  ⟨rcSAdj_symmetric, rcSAdj_regular, by norm_num, le_refl 2, rcSAdj_not_nonneg⟩

/-- **Fence (`cheeger_upper_bound`, `hd`)**: the nonnegative `d = 3`-regular
fixture instantiated at the *claimed* wrong degree `d' = 4` (so
`regularNormalizedLaplacian rcPosAdj 4` is the wrong operator): the
genuine eigenvalue `3/4` at the mode `![1, -1]` exceeds `2φ = 2/3`. -/
theorem rcF_upper_hd_fence_QA :
    ¬ (secondEval (regularNormalizedLaplacian rcPosAdj 4)
        (regularNormalizedLaplacian_symmetric rcPosAdj rcPosAdj_symmetric 4)
        (le_refl 2)
      ≤ 2 * cheegerConstant rcPosAdj) := by
  rw [rcPos_cheegerConstant]
  linarith [rcPosD4_secondEval_ge]

theorem rcF_upper_hd_isolation_QA :
    rcPosAdj.IsSymm ∧ (∀ i j, 0 ≤ rcPosAdj i j) ∧ (0 < (4:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (∀ i, deg rcPosAdj i = 4) :=
  ⟨rcPosAdj_symmetric, rcPosAdj_nonneg, by norm_num, le_refl 2,
    rcPosAdj_not_regular_four⟩

/-- **Fence (`cheeger_upper_bound`, `hdpos`)**: at the zero matrix with
genuine regularity `d = 0` (every degree is `0`) and genuine
nonnegativity, the operator is the identity, `λ₂ = 1`, while the junk
conductance `0/0 = 0` collapses `2φ` to `0`. -/
theorem rcF_upper_hdpos_fence_QA :
    ¬ (secondEval (regularNormalizedLaplacian rcZeroAdj 0)
        (regularNormalizedLaplacian_symmetric rcZeroAdj rcZeroAdj_symmetric 0)
        (le_refl 2)
      ≤ 2 * cheegerConstant rcZeroAdj) := by
  rw [rcZero_cheegerConstant]
  linarith [rcZero_regNL_secondEval_ge_one]

theorem rcF_upper_hdpos_isolation_QA :
    rcZeroAdj.IsSymm ∧ (∀ i j, 0 ≤ rcZeroAdj i j) ∧ (∀ i, deg rcZeroAdj i = 0)
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (0 < (0:ℝ)) :=
  ⟨rcZeroAdj_symmetric, rcZeroAdj_nonneg, rcZeroAdj_regular_zero,
    le_refl 2, by norm_num⟩

/-!
### The inequality fences: `cheeger_lower_bound`
-/

/-- **Fence (`cheeger_lower_bound`, `hnonneg`)**: at the signed fixture
the dropped conclusion reads `φ²/2 = 1/8 ≤ λ₂ = 0` — false. -/
theorem rcF_lower_hnn_fence_QA :
    ¬ ((cheegerConstant rcSAdj)^2 / 2
        ≤ secondEval (regularNormalizedLaplacian rcSAdj 2)
          (regularNormalizedLaplacian_symmetric rcSAdj rcSAdj_symmetric 2)
          (le_refl 2)) := by
  rw [rcS_cheegerConstant, rcS_regNL_secondEval_eq_zero]
  norm_num

theorem rcF_lower_hnn_isolation_QA :
    rcSAdj.IsSymm ∧ (∀ i, deg rcSAdj i = 2) ∧ (0 < (2:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (∀ i j, 0 ≤ rcSAdj i j) :=
  ⟨rcSAdj_symmetric, rcSAdj_regular, by norm_num, le_refl 2, rcSAdj_not_nonneg⟩

/-- **Fence (`cheeger_lower_bound`, `hd`)**: the wrong claimed degree
`d' = 1` makes `regularNormalizedLaplacian rcPosAdj 1 = !![-1,-1;-1,-1]`,
whose spectrum is `{-2, 0}`, so `λ₂ = 0 < φ²/2 = 1/18`. -/
theorem rcF_lower_hd_fence_QA :
    ¬ ((cheegerConstant rcPosAdj)^2 / 2
        ≤ secondEval (regularNormalizedLaplacian rcPosAdj 1)
          (regularNormalizedLaplacian_symmetric rcPosAdj rcPosAdj_symmetric 1)
          (le_refl 2)) := by
  rw [rcPos_cheegerConstant]
  linarith [rcPosD1_secondEval_le_zero]

theorem rcF_lower_hd_isolation_QA :
    rcPosAdj.IsSymm ∧ (∀ i j, 0 ≤ rcPosAdj i j) ∧ (0 < (1:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (∀ i, deg rcPosAdj i = 1) :=
  ⟨rcPosAdj_symmetric, rcPosAdj_nonneg, by norm_num, le_refl 2,
    rcPosAdj_not_regular_one⟩

/-!
### The inequality fences: `cheeger_sweep`

Hypothesis order: `(hA) (hnn) (d) (hd) (hdpos) (hx0) (horth)`.
-/

/-- **Fence (`cheeger_sweep`, `hx0`)**: the junk Rayleigh branch —
`rayleigh` is definitionally `0` at the zero vector, while `φ²/2 = 1/2`
on the edge. -/
theorem rcF_sweep_hx0_fence_QA :
    ¬ (cheegerConstant cheegerEdgeAdj ^ 2 / 2
        ≤ rayleigh (regularNormalizedLaplacian cheegerEdgeAdj 1) (0 : Fin 2 → ℝ)) := by
  rw [edge_cheegerConstant, rcE_regNL_rayleigh_zero]
  norm_num

theorem rcF_sweep_hx0_isolation_QA :
    cheegerEdgeAdj.IsSymm ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j) ∧ (∀ i, deg cheegerEdgeAdj i = 1)
      ∧ (0 < (1:ℝ)) ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ (Matrix.dotProduct (0 : Fin 2 → ℝ) onesVec = 0) ∧ ¬ ((0 : Fin 2 → ℝ) ≠ 0) :=
  ⟨cheegerEdgeAdj_symmetric, cheegerEdgeAdj_nonneg, cheegerEdgeAdj_regular, by norm_num,
    le_refl 2, by simp [Matrix.dotProduct], by simp⟩

/-- **Fence (`cheeger_sweep`, `horth`)**: the constant vector is in the
operator's kernel (`R = 0`) but not orthogonal to itself — the dropped
conclusion reads `1/2 ≤ 0`. -/
theorem rcF_sweep_horth_fence_QA :
    ¬ (cheegerConstant cheegerEdgeAdj ^ 2 / 2
        ≤ rayleigh (regularNormalizedLaplacian cheegerEdgeAdj 1)
            (onesVec : Fin 2 → ℝ)) := by
  rw [edge_cheegerConstant, rcE_regNL_rayleigh_ones]
  norm_num

theorem rcF_sweep_horth_isolation_QA :
    cheegerEdgeAdj.IsSymm ∧ (∀ i j, 0 ≤ cheegerEdgeAdj i j) ∧ (∀ i, deg cheegerEdgeAdj i = 1)
      ∧ (0 < (1:ℝ)) ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ ((onesVec : Fin 2 → ℝ) ≠ 0)
      ∧ ¬ (Matrix.dotProduct (onesVec : Fin 2 → ℝ) onesVec = 0) :=
  ⟨cheegerEdgeAdj_symmetric, cheegerEdgeAdj_nonneg, cheegerEdgeAdj_regular, by norm_num,
    le_refl 2, rc_vec_ne_zero (by simp [onesVec]),
    by norm_num [onesVec, Matrix.dotProduct, Fin.sum_univ_two]⟩

/-- **Fence (`cheeger_sweep`, `hnn`)**: at the signed fixture with the
orthogonal mode `![1, -1]` (orthogonality genuine), the dropped
conclusion reads `φ²/2 = 1/8 ≤ R = -1` — false. -/
theorem rcF_sweep_hnn_fence_QA :
    ¬ (cheegerConstant rcSAdj ^ 2 / 2
        ≤ rayleigh (regularNormalizedLaplacian rcSAdj 2)
            (![1, -1] : Fin 2 → ℝ)) := by
  rw [rcS_cheegerConstant, rcS_regNL_rayleigh_mode]
  norm_num

theorem rcF_sweep_hnn_isolation_QA :
    rcSAdj.IsSymm ∧ (∀ i, deg rcSAdj i = 2) ∧ (0 < (2:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ ((![1, -1] : Fin 2 → ℝ) ≠ 0)
      ∧ (Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) onesVec = 0)
      ∧ ¬ (∀ i j, 0 ≤ rcSAdj i j) :=
  ⟨rcSAdj_symmetric, rcSAdj_regular, by norm_num, le_refl 2,
    rc_vec_ne_zero (by simp),
    by simp [onesVec, Matrix.dotProduct, Fin.sum_univ_two], rcSAdj_not_nonneg⟩

/-- **Fence (`cheeger_sweep`, `hd`)**: the wrong claimed degree `d' = 1`
at the mode `![1, -1]`: the operator kills the mode, `R = 0 < φ²/2 =
1/18`. -/
theorem rcF_sweep_hd_fence_QA :
    ¬ (cheegerConstant rcPosAdj ^ 2 / 2
        ≤ rayleigh (regularNormalizedLaplacian rcPosAdj 1)
            (![1, -1] : Fin 2 → ℝ)) := by
  rw [rcPos_cheegerConstant, rcPosD1_regNL_rayleigh_mode]
  norm_num

theorem rcF_sweep_hd_isolation_QA :
    rcPosAdj.IsSymm ∧ (∀ i j, 0 ≤ rcPosAdj i j) ∧ (0 < (1:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2)
      ∧ ((![1, -1] : Fin 2 → ℝ) ≠ 0)
      ∧ (Matrix.dotProduct (![1, -1] : Fin 2 → ℝ) onesVec = 0)
      ∧ ¬ (∀ i, deg rcPosAdj i = 1) :=
  ⟨rcPosAdj_symmetric, rcPosAdj_nonneg, by norm_num, le_refl 2,
    rc_vec_ne_zero (by simp),
    by simp [onesVec, Matrix.dotProduct, Fin.sum_univ_two],
    rcPosAdj_not_regular_one⟩

/-!
### The inequality fences: the `_laplacian` twins
-/

/-- **Fence (`cheeger_lower_bound_laplacian`, `hnonneg`)**: at the
signed fixture the combinatorial Laplacian is `!![-1,1;1,-1]` with
`λ₂(L) = 0`, while `d φ²/2 = 2 · 1/8 = 1/4`. -/
theorem rcF_lowerlap_hnn_fence_QA :
    ¬ (2 * (cheegerConstant rcSAdj)^2 / 2
        ≤ lambda2 rcSAdj rcSAdj_symmetric (le_refl 2)) := by
  have h2 : lambda2 rcSAdj rcSAdj_symmetric (le_refl 2) = 0 :=
    rcS_lap_secondEval_eq_zero
  rw [h2, rcS_cheegerConstant]
  norm_num

theorem rcF_lowerlap_hnn_isolation_QA :
    rcSAdj.IsSymm ∧ (∀ i, deg rcSAdj i = 2) ∧ (0 < (2:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (∀ i j, 0 ≤ rcSAdj i j) :=
  ⟨rcSAdj_symmetric, rcSAdj_regular, by norm_num, le_refl 2, rcSAdj_not_nonneg⟩

/-- **Fence (`cheeger_lower_bound_laplacian`, `hd`)**: the wrong claimed
degree `d' = 40` inflates the left side to `20/9` while the true
combinatorial `λ₂(L) = 2` is degree-independent. -/
theorem rcF_lowerlap_hd_fence_QA :
    ¬ (40 * (cheegerConstant rcPosAdj)^2 / 2
        ≤ lambda2 rcPosAdj rcPosAdj_symmetric (le_refl 2)) := by
  have h2 : lambda2 rcPosAdj rcPosAdj_symmetric (le_refl 2) ≤ 2 :=
    rcPos_lap_secondEval_le_two
  rw [rcPos_cheegerConstant]
  norm_num
  linarith

theorem rcF_lowerlap_hd_isolation_QA :
    rcPosAdj.IsSymm ∧ (∀ i j, 0 ≤ rcPosAdj i j) ∧ (0 < (40:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (∀ i, deg rcPosAdj i = 40) :=
  ⟨rcPosAdj_symmetric, rcPosAdj_nonneg, by norm_num, le_refl 2,
    rcPosAdj_not_regular_forty⟩

/-- **Fence (`cheeger_upper_bound_laplacian`, `hnonneg`)**: at the
signed fixture the dropped conclusion reads `λ₂(L) = 0 ≤ 2 d φ = -2` —
false. -/
theorem rcF_upperlap_hnn_fence_QA :
    ¬ (lambda2 rcSAdj rcSAdj_symmetric (le_refl 2)
        ≤ 2 * (2 * cheegerConstant rcSAdj)) := by
  have h2 : lambda2 rcSAdj rcSAdj_symmetric (le_refl 2) = 0 :=
    rcS_lap_secondEval_eq_zero
  rw [h2, rcS_cheegerConstant]
  norm_num

theorem rcF_upperlap_hnn_isolation_QA :
    rcSAdj.IsSymm ∧ (∀ i, deg rcSAdj i = 2) ∧ (0 < (2:ℝ))
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (∀ i j, 0 ≤ rcSAdj i j) :=
  ⟨rcSAdj_symmetric, rcSAdj_regular, by norm_num, le_refl 2, rcSAdj_not_nonneg⟩

/-- **Fence (`cheeger_upper_bound_laplacian`, `hd`)**: the wrong claimed
degree `d' = 1/8` deflates the right side to `1/12` against the true
`λ₂(L) = 2`. -/
theorem rcF_upperlap_hd_fence_QA :
    ¬ (lambda2 rcPosAdj rcPosAdj_symmetric (le_refl 2)
        ≤ 2 * ((1/8) * cheegerConstant rcPosAdj)) := by
  have h2 : 2 ≤ lambda2 rcPosAdj rcPosAdj_symmetric (le_refl 2) :=
    rcPos_lap_secondEval_ge_two
  rw [rcPos_cheegerConstant]
  norm_num
  linarith

theorem rcF_upperlap_hd_isolation_QA :
    rcPosAdj.IsSymm ∧ (∀ i j, 0 ≤ rcPosAdj i j) ∧ (0 < ((1/8:ℝ)))
      ∧ 2 ≤ Fintype.card (Fin 2) ∧ ¬ (∀ i, deg rcPosAdj i = 1/8) :=
  ⟨rcPosAdj_symmetric, rcPosAdj_nonneg, by norm_num, le_refl 2,
    rcPosAdj_not_regular_one_eighth⟩

/-!
### The PSD engine fences: `regularNormalizedLaplacian_psd`

The conclusion is a universally quantified nonnegativity claim; each
fence exhibits a witness with strictly negative quadratic form.
-/

/-- The negative-witness value at the asymmetric fixture: the quadratic
form sees the symmetric part `[[4,2],[2,2]]`, whose `![2,1]`-Rayleigh
`26/5` exceeds the claimed degree `5`. -/
theorem rcAsym_regNL_quadForm_witness :
    quadForm (regularNormalizedLaplacian rcAsymPsdAdj 5) (![2, 1] : Fin 2 → ℝ)
      = -1/5 := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    rcAsym_regNL, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  norm_num

/-- **Fence (`regularNormalizedLaplacian_psd`, `hA`)**: at the
nonnegative row-regular asymmetric fixture, `quadForm = -1/5 < 0` at
`![2, 1]`. -/
theorem rcF_psd_hA_fence_QA :
    ¬ (∀ x : Fin 2 → ℝ, 0 ≤ quadForm (regularNormalizedLaplacian rcAsymPsdAdj 5) x) := by
  intro h
  have h2 := h (![2, 1] : Fin 2 → ℝ)
  rw [rcAsym_regNL_quadForm_witness] at h2
  norm_num at h2

theorem rcF_psd_hA_isolation_QA :
    (∀ i j, 0 ≤ rcAsymPsdAdj i j) ∧ (∀ i, deg rcAsymPsdAdj i = 5)
      ∧ (0 < (5:ℝ)) ∧ ¬ rcAsymPsdAdj.IsSymm :=
  ⟨rcAsymPsdAdj_nonneg, rcAsymPsdAdj_regular, by norm_num, rcAsymPsdAdj_not_isSymm⟩

/-- **Fence (`regularNormalizedLaplacian_psd`, `hnonneg`)**: at the
signed fixture `quadForm = -2 < 0` at the mode `![1, -1]`. -/
theorem rcF_psd_hnn_fence_QA :
    ¬ (∀ x : Fin 2 → ℝ,
        0 ≤ quadForm (regularNormalizedLaplacian rcSAdj 2) x) := by
  intro h
  have h2 := h (![1, -1] : Fin 2 → ℝ)
  rw [rcS_regNL_quadForm] at h2
  norm_num at h2

theorem rcF_psd_hnn_isolation_QA :
    rcSAdj.IsSymm ∧ (∀ i, deg rcSAdj i = 2) ∧ (0 < (2:ℝ))
      ∧ ¬ (∀ i j, 0 ≤ rcSAdj i j) :=
  ⟨rcSAdj_symmetric, rcSAdj_regular, by norm_num, rcSAdj_not_nonneg⟩

/-- **Fence (`regularNormalizedLaplacian_psd`, `hd`)**: the wrong
claimed degree `d' = 1` gives the all-`-1` operator, `quadForm 1 = -4`. -/
theorem rcF_psd_hd_fence_QA :
    ¬ (∀ x : Fin 2 → ℝ,
        0 ≤ quadForm (regularNormalizedLaplacian rcPosAdj 1) x) := by
  intro h
  have h2 := h (![1, 1] : Fin 2 → ℝ)
  rw [rcPosD1_regNL_quadForm] at h2
  norm_num at h2

theorem rcF_psd_hd_isolation_QA :
    rcPosAdj.IsSymm ∧ (∀ i j, 0 ≤ rcPosAdj i j) ∧ (0 < (1:ℝ))
      ∧ ¬ (∀ i, deg rcPosAdj i = 1) :=
  ⟨rcPosAdj_symmetric, rcPosAdj_nonneg, by norm_num, rcPosAdj_not_regular_one⟩

/-!
### The cut-test-vector junk corners: `cutTestVector_ne_zero`

Hypothesis order: `(d) (hd) (hdpos) (hS) (hSc)`.
-/

theorem rcZero_cutTestVector_zero :
    cutTestVector rcZeroAdj ({0} : Finset (Fin 2)) = 0 := by
  funext i
  fin_cases i
  · simp [cutTestVector, cutTestVector_apply, rcZero_vol_compl_zero]
  · simp [cutTestVector, cutTestVector_apply, rcZero_vol_zero]

/-- **Fence (`cutTestVector_ne_zero`, `hd`)**: at the zero matrix with
claimed `d = 1` (regularity failing, positivity genuine), the cut test
vector of `{0}` is identically `0`. -/
theorem rcF_ctv_hd_fence_QA :
    ¬ (cutTestVector rcZeroAdj ({0} : Finset (Fin 2)) ≠ 0) := by
  intro h
  exact h rcZero_cutTestVector_zero

theorem rcF_ctv_hd_isolation_QA :
    (0 < (1:ℝ)) ∧ (({0} : Finset (Fin 2)).Nonempty)
      ∧ (({0} : Finset (Fin 2))ᶜ.Nonempty)
      ∧ ¬ (∀ i, deg rcZeroAdj i = 1) :=
  ⟨by norm_num, by decide, by decide, rcZeroAdj_not_regular_one⟩

/-- **Fence (`cutTestVector_ne_zero`, `hdpos`)**: genuine regularity
`d = 0` (every degree `0`), positivity dropped — the same junk corner. -/
theorem rcF_ctv_hdpos_fence_QA :
    ¬ (cutTestVector rcZeroAdj ({0} : Finset (Fin 2)) ≠ 0) := by
  intro h
  exact h rcZero_cutTestVector_zero

theorem rcF_ctv_hdpos_isolation_QA :
    (∀ i, deg rcZeroAdj i = 0) ∧ (({0} : Finset (Fin 2)).Nonempty)
      ∧ (({0} : Finset (Fin 2))ᶜ.Nonempty) ∧ ¬ (0 < (0:ℝ)) :=
  ⟨rcZeroAdj_regular_zero, by decide, by decide, by norm_num⟩

/-- **Fence (`cutTestVector_ne_zero`, `hS`)**: the empty cut — the
vector is constantly `-vol ∅ = 0`. -/
theorem rcF_ctv_hS_fence_QA :
    ¬ (cutTestVector cheegerEdgeAdj (∅ : Finset (Fin 2)) ≠ 0) := by
  intro h
  apply h
  funext i
  simp [cutTestVector, cutTestVector_apply, vol]

theorem rcF_ctv_hS_isolation_QA :
    (∀ i, deg cheegerEdgeAdj i = 1) ∧ (0 < (1:ℝ))
      ∧ ((∅ : Finset (Fin 2))ᶜ.Nonempty) ∧ ¬ ((∅ : Finset (Fin 2)).Nonempty) :=
  ⟨cheegerEdgeAdj_regular, by norm_num, by decide, by simp⟩

/-- **Fence (`cutTestVector_ne_zero`, `hSc`)**: the full cut — the
vector is constantly `vol univᶜ = vol ∅ = 0`. -/
theorem rcF_ctv_hSc_fence_QA :
    ¬ (cutTestVector cheegerEdgeAdj (Finset.univ : Finset (Fin 2)) ≠ 0) := by
  intro h
  apply h
  funext i
  simp [cutTestVector, cutTestVector_apply, vol, Finset.compl_univ]

theorem rcF_ctv_hSc_isolation_QA :
    (∀ i, deg cheegerEdgeAdj i = 1) ∧ (0 < (1:ℝ))
      ∧ (Finset.univ : Finset (Fin 2)).Nonempty
      ∧ ¬ ((Finset.univ : Finset (Fin 2))ᶜ.Nonempty) :=
  ⟨cheegerEdgeAdj_regular, by norm_num, by simp, by simp⟩

end RegularFences

end SpectralGraphTheory.QA
