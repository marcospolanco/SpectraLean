/-
  Cheeger_QA.lean

  Purpose
  -------
  QA lemmas for the Cheeger inequality interface of
  `Scaffold.Mathlib.GraphTheory.Cheeger`: structural conductance facts
  proved from the definitions, and coherence checks that derive
  consequences from the bounds — since 2026-08-18 the *upper* bound
  (easy direction) is a proved theorem; the *lower* bound (hard
  direction) remains admitted.

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the admitted lower-bound axiom; it checks that the interfaces
  compose.

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
    cutTestVector edgeAdj ({0} : Finset (Fin 2)) = ![1, -1] := by
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
    rayleigh (regularNormalizedLaplacian edgeAdj 1)
        (cutTestVector edgeAdj ({0} : Finset (Fin 2))) = 2 := by
  obtain ⟨hv1, hv2⟩ := edge_vol_singleton 0
  have hvV : vol edgeAdj (Finset.univ : Finset (Fin 2)) = 2 := by
    rw [← vol_compl edgeAdj ({0} : Finset (Fin 2)), hv1, hv2]
    norm_num
  rw [rayleigh_regularNormalizedLaplacian_cutTestVector edgeAdj
    edgeAdj_symmetric 1 edgeAdj_regular (by norm_num) (by decide)
    (by decide), edge_boundary_singleton 0, hv1, hv2, hvV]
  norm_num

/-- **The proved bound is attained on `K₂`:** `λ₂(L_sym) = 2 = 2φ`.
Both the spectral value (`edge_normLap_secondEval_eq_two_QA`) and the
conductance (`edge_cheegerConstant`) are computed independently of the
theorem, so the equality is a genuine cross-check of the proved bound
rather than an axiom instantiation. -/
theorem cheeger_upper_bound_edge_eq_QA :
    secondEval (regularNormalizedLaplacian edgeAdj 1)
        (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1)
        (le_refl 2) = 2 * cheegerConstant edgeAdj := by
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
    ∑ i, ∑ j, edgeAdj i j * |edgeF i ^ 2 - edgeF j ^ 2| = 2 := by
  simp only [Fin.sum_univ_two, edgeAdj, edgeF_zero, edgeF_one]
  norm_num

/-- Component A's energy factor on `K₂` at `edgeF`, computed raw. -/
theorem edge_core_E' :
    ∑ i, ∑ j, edgeAdj i j * (edgeF i - edgeF j) ^ 2 = 2 := by
  simp only [Fin.sum_univ_two, edgeAdj, edgeF_zero, edgeF_one]
  norm_num

/-- Component A's degree-weighted factor on `K₂` at `edgeF`, through
the new regularity bridge `sum_deg_mul_eq_of_regular` (so the bridge is
load-bearing here, not decorative). -/
theorem edge_core_degsum :
    ∑ i, deg edgeAdj i * edgeF i ^ 2 = 1 := by
  rw [sum_deg_mul_eq_of_regular edgeAdj 1 edgeAdj_regular edgeF]
  simp only [Fin.sum_univ_two, edgeF_zero, edgeF_one]
  norm_num

/-- **Component A instantiated on `K₂`:** at `edgeF = ![1, 0]` the
instance reads `4 ≤ 8`, with all three quantities pinned independently
above. -/
theorem core_edge_QA :
    (∑ i, ∑ j, edgeAdj i j * |edgeF i ^ 2 - edgeF j ^ 2|) ^ 2
      ≤ (∑ i, ∑ j, edgeAdj i j * (edgeF i - edgeF j) ^ 2)
        * (4 * ∑ i, deg edgeAdj i * edgeF i ^ 2) :=
  core_sum_abs_sq_sub_sq edgeAdj edgeAdj_symmetric edgeAdj_nonneg edgeF

/-- **The strict case:** on `K₂` at `edgeF` the Component A bound is
strict with a visible gap, `4 < 8` — the bound is not vacuously tight
here. (The slack is exactly the AM-GM loss on the crossing pair:
`(1 + 0)² = 1 < 2·1² + 2·0² = 2`.) -/
theorem core_edge_strict_QA :
    (∑ i, ∑ j, edgeAdj i j * |edgeF i ^ 2 - edgeF j ^ 2|) ^ 2
      < (∑ i, ∑ j, edgeAdj i j * (edgeF i - edgeF j) ^ 2)
        * (4 * ∑ i, deg edgeAdj i * edgeF i ^ 2) := by
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
    rayleigh (regularNormalizedLaplacian edgeAdj 1) ![1, -1] = 2 := by
  rw [rayleigh_regularNormalizedLaplacian_eq edgeAdj edgeAdj_symmetric 1
    edgeAdj_regular (by norm_num) (by
      intro h
      have h0 : (![1, -1] : Fin 2 → ℝ) 0 = 0 := congrFun h 0
      norm_num at h0)]
  have hE : ∑ i, ∑ j, edgeAdj i j * (![1, -1] i - ![1, -1] j) ^ 2 = 8 := by
    simp only [Fin.sum_univ_two, edgeAdj]
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
    rayleigh (regularNormalizedLaplacian edgeAdj 1) ![1, -1]
      = secondEval (regularNormalizedLaplacian edgeAdj 1)
          (regularNormalizedLaplacian_symmetric edgeAdj edgeAdj_symmetric 1)
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

end SpectralGraphTheory.QA
