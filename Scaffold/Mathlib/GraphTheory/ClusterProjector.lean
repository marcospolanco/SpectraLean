/-
  ClusterProjector.lean

  Purpose
  -------
  The set-valued spectral projector: the orthogonal projector onto the
  span of the eigenvectors whose eigenvalues lie in an arbitrary set
  `S ⊆ ℝ`,

  ```
  clusterProjector M hM S = ∑_{i : λᵢ ∈ S} vᵢ vᵢᵀ
  ```

  over the orthonormal eigenbasis of `Spectral.lean`
  (`proposals/cluster-projector.md`, the recorded follow-on of the band
  Davis–Kahan cluster/symmetric deliveries). Pure hard crust: no `axiom`
  declarations; every theorem is proved from the already-proved
  eigenbasis algebra of `Scaffold.Mathlib.GraphTheory.Spectral`.

  Why a set projector: every projector on the shelf selects eigenvalues
  by an *interval* — `spectralProjector` at `≤ c`, `bandProjector` at
  `(a, b]` — while the classical statements the perturbation family
  serves (Davis–Kahan's spectral-projector theorem, Yu–Wang–Samworth
  Theorem 1) are stated at *clusters*: arbitrary eigenvalue sets. A
  consumer wanting the projector onto `{λ : |λ| ≥ 3}` — two half-lines —
  had no object to name. The definition is total and **junk-free**: a set
  has no orientation, so there is no reversed-endpoint regime and none
  of the `a ≤ b` guards the band family carries.

  Design (per the proposal): `S : Set ℝ` (clusters are sets in the cited
  statements, and the complement law reads `Sᶜ`); no `S.Finite`
  hypothesis anywhere — `S` only ever enters through membership of the
  finitely many eigenvalues of `V`'s eigenbasis filter; classical
  decidability for that filter (the definition is `noncomputable`, like
  `spectralProjector`).

  The interface transfers through one lemma — the component action
  `v i ⬝ᵥ (P_S *ᵥ y) = χ(λ i ∈ S) · (v i ⬝ᵥ y)`, the mirror of
  PolyFilter's band form and the only projector input the commutator/
  shift perturbation engine consumes. Highlights:

  - the **intersection product law**
    `clusterProjector_mul_clusterProjector : P_S * P_T = P_{S ∩ T}` —
    the spectral-projector nestedness law's set twin; idempotence is
    its diagonal (`S ∩ S = S`) and disjoint-set orthogonality its
    empty-intersection case;
  - the **complement law** `one_sub_clusterProjector :
    1 − P_S = P_{Sᶜ}` — a partition of the eigenbasis filter, and the
    structural fact the *window* family lacks (`1 − bandProjector` is
    not a band projector, which is why the window difference form
    needed a separate complement engine and this module's set form does
    not);
  - the **band agreement**
    `clusterProjector_eq_bandProjector : clusterProjector M hM (Set.Ioc a b)
    = bandProjector M hM a b` — the entire delivered band family is the
    interval-set special case; the guard `a ≤ b` is the *band's* junk
    regime, not the set's;
  - the **rank supplier** `rank_clusterProjector_eq_card` — rank =
    cardinality of the in-`S` eigenbasis filter (via the trace and the
    exact `{0, 1}` spectrum of a symmetric idempotent), making the
    set-form difference theorem's equal-rank hypothesis checkable.

  Related modules: the threshold/band projectors and the eigenbasis
  algebra live in `Scaffold.Mathlib.GraphTheory.Spectral` and `.Band`;
  the set-form Davis–Kahan pair consuming this interface lives in
  `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
  (`SetForm` sections).
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.Band

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The definition, mode selection, and the component action -/

open Classical in
/-- The set-valued spectral projector: the sum of the outer products
`vᵢ vᵢᵀ` over the orthonormal eigenbasis vectors whose eigenvalues lie
in `S` — the orthogonal projector onto the span of the eigenvectors of
the cluster `S`.

Symmetric by construction (`clusterProjector_symmetric`), idempotent
(`clusterProjector_idempotent`), fixing each in-`S` eigenvector and
annihilating each out-of-`S` one. The definition is total and
junk-free: unlike the interval bands there is no orientation, hence no
reversed-endpoint regime, and no theorem below carries a guard on `S`. -/
noncomputable def clusterProjector (M : Matrix V V ℝ) (hM : M.IsSymm)
    (S : Set ℝ) : Matrix V V ℝ :=
  Matrix.of fun a b =>
    ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ∈ S),
      eigvecOf M hM i a * eigvecOf M hM i b

/-- Cluster projectors are symmetric by construction (each outer
product `vᵢvᵢᵀ` is symmetric). -/
theorem clusterProjector_symmetric (M : Matrix V V ℝ) (hM : M.IsSymm)
    (S : Set ℝ) :
    (clusterProjector M hM S).IsSymm := by
  refine Matrix.IsSymm.ext fun a b => ?_
  simp only [clusterProjector, Matrix.transpose_apply, Matrix.of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

open Classical in
/-- The complete action of a cluster projector on the eigenbasis: the
projector of `S` fixes the eigenvector when its eigenvalue lies in `S`
and annihilates it when it does not — the cluster's mode-selection
interface, with no guard (a set has no junk regime). -/
theorem clusterProjector_mulVec_eigvecOf (M : Matrix V V ℝ)
    (hM : M.IsSymm) (S : Set ℝ) (i : V) :
    clusterProjector M hM S *ᵥ eigvecOf M hM i
      = if eigvalOf M hM i ∈ S then eigvecOf M hM i else 0 := by
  classical
  ext b
  simp only [Matrix.mulVec, Matrix.dotProduct, clusterProjector,
    Matrix.of_apply]
  have hexp : ∀ k : V,
      (∑ i' ∈ Finset.univ.filter (fun x => eigvalOf M hM x ∈ S),
          eigvecOf M hM i' b * eigvecOf M hM i' k) * eigvecOf M hM i k =
      ∑ i' ∈ Finset.univ.filter (fun x => eigvalOf M hM x ∈ S),
        (eigvecOf M hM i' b * eigvecOf M hM i' k * eigvecOf M hM i k) :=
    fun k => Finset.sum_mul _ _ _
  simp only [hexp]
  rw [Finset.sum_comm]
  have hterm : ∀ i' : V,
      (∑ k : V, eigvecOf M hM i' b * eigvecOf M hM i' k
          * eigvecOf M hM i k) =
      eigvecOf M hM i' b * (if i' = i then 1 else 0) := by
    intro i'
    have hring : ∀ k : V,
        eigvecOf M hM i' b * eigvecOf M hM i' k * eigvecOf M hM i k =
        eigvecOf M hM i' b * (eigvecOf M hM i' k * eigvecOf M hM i k) :=
      fun k => by ring
    rw [Finset.sum_congr rfl (fun k _ => hring k), ← Finset.mul_sum,
      eigvecOf_inner]
  rw [Finset.sum_congr rfl (fun i' _ => hterm i')]
  have hite : ∀ i' : V,
      eigvecOf M hM i' b * (if i' = i then 1 else 0) =
      if i' = i then eigvecOf M hM i' b else 0 := by
    intro i'
    by_cases hd : i' = i <;> simp [hd]
  rw [Finset.sum_congr rfl (fun i' _ => hite i'), Finset.sum_ite_eq']
  have hmem : i ∈ Finset.univ.filter (fun x : V => eigvalOf M hM x ∈ S) ↔
      eigvalOf M hM i ∈ S := by simp [Finset.mem_filter]
  by_cases h : eigvalOf M hM i ∈ S
  · rw [if_pos (hmem.2 h), ite_apply, if_pos h]
  · rw [if_neg (fun hc => h (hmem.1 hc)), ite_apply, if_neg h]
    rfl

/-- In-cluster modes are fixed: an eigenvector whose eigenvalue lies in
`S` is fixed by the cluster projector. -/
theorem clusterProjector_mulVec_eigvecOf_self (M : Matrix V V ℝ)
    (hM : M.IsSymm) (S : Set ℝ) (i : V)
    (h : eigvalOf M hM i ∈ S) :
    clusterProjector M hM S *ᵥ eigvecOf M hM i = eigvecOf M hM i := by
  rw [clusterProjector_mulVec_eigvecOf M hM S i, if_pos h]

/-- Out-of-cluster modes are annihilated: an eigenvector whose
eigenvalue lies outside `S` is killed by the cluster projector. -/
theorem clusterProjector_mulVec_eigvecOf_eq_zero (M : Matrix V V ℝ)
    (hM : M.IsSymm) (S : Set ℝ) (i : V)
    (h : eigvalOf M hM i ∉ S) :
    clusterProjector M hM S *ᵥ eigvecOf M hM i = 0 := by
  rw [clusterProjector_mulVec_eigvecOf M hM S i, if_neg h]

/-- Two vectors with identical eigenbasis components are equal (basis
injectivity, through the entrywise expansion). -/
private theorem eq_of_forall_dotProduct_eigvecOf_eq {M : Matrix V V ℝ}
    (hM : M.IsSymm) (x y : V → ℝ)
    (h : ∀ i, Matrix.dotProduct (eigvecOf M hM i) x
      = Matrix.dotProduct (eigvecOf M hM i) y) : x = y := by
  funext a
  have hx := eigvecOf_expansion_apply hM x a
  have hy := eigvecOf_expansion_apply hM y a
  rw [← hx, ← hy]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

open Classical in
/-- The cluster projector's component action: pairing the projector's
action on any vector against an eigenbasis vector picks out that
eigenvalue's mode — `v i ⬝ᵥ (P_S *ᵥ y) = χ_{λ i ∈ S} · (v i ⬝ᵥ y)`.
The mirror of the threshold/band component actions (PolyFilter), and
the single projector input the set-form Davis–Kahan engine consumes. -/
theorem eigvecOf_dotProduct_clusterProjector_mulVec
    {M : Matrix V V ℝ} (hM : M.IsSymm) (S : Set ℝ) (i : V)
    (y : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) ((clusterProjector M hM S) *ᵥ y)
      = (if eigvalOf M hM i ∈ S then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf M hM i) y := by
  classical
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    (clusterProjector_symmetric M hM S).eq,
    clusterProjector_mulVec_eigvecOf M hM S i]
  by_cases h : eigvalOf M hM i ∈ S
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul, Matrix.zero_dotProduct]

/-! ## The projector algebra -/

/-- **The intersection product law.** Cluster projectors compose to the
projector of the intersection: `P_S * P_T = P_{S ∩ T}`. Route: both
sides' actions on any vector agree componentwise — the component action
of `P_S` applied outside the action of `P_T`, the conditions fusing at
`S ∩ T` — and equal actions on every vector give equal matrices (the
column-extraction idiom). The set twin of the threshold projectors'
nestedness law (`spectralProjector_mul_spectralProjector`), with no
order constraint because sets have none. Idempotence is the diagonal
`S ∩ S = S`; disjointness is the empty intersection. -/
theorem clusterProjector_mul_clusterProjector (M : Matrix V V ℝ)
    (hM : M.IsSymm) (S T : Set ℝ) :
    clusterProjector M hM S * clusterProjector M hM T
      = clusterProjector M hM (S ∩ T) := by
  classical
  have hact : ∀ y : V → ℝ,
      (clusterProjector M hM S * clusterProjector M hM T) *ᵥ y
        = clusterProjector M hM (S ∩ T) *ᵥ y := by
    intro y
    refine eq_of_forall_dotProduct_eigvecOf_eq hM _ _ fun i => ?_
    rw [← Matrix.mulVec_mulVec y (clusterProjector M hM S)
        (clusterProjector M hM T),
      eigvecOf_dotProduct_clusterProjector_mulVec hM S i,
      eigvecOf_dotProduct_clusterProjector_mulVec hM T i,
      eigvecOf_dotProduct_clusterProjector_mulVec hM (S ∩ T) i]
    by_cases h : eigvalOf M hM i ∈ S ∩ T
    · rw [if_pos h.1, if_pos h.2, if_pos h]
      ring
    · by_cases hS : eigvalOf M hM i ∈ S
      · by_cases hT : eigvalOf M hM i ∈ T
        · exact absurd (Set.mem_inter hS hT) h
        · rw [if_pos hS, if_neg hT,
            if_neg (show ¬(eigvalOf M hM i ∈ S ∩ T) from
              fun hc => hT hc.2)]
          ring
      · rw [if_neg hS,
          if_neg (show ¬(eigvalOf M hM i ∈ S ∩ T) from
            fun hc => hS hc.1)]
        ring
  have hcol : ∀ i j : V,
      (clusterProjector M hM S * clusterProjector M hM T
        - clusterProjector M hM (S ∩ T)) i j = 0 := by
    intro i j
    have hzero : (clusterProjector M hM S * clusterProjector M hM T
        - clusterProjector M hM (S ∩ T)) *ᵥ (Pi.single j (1 : ℝ)) = 0 := by
      rw [Matrix.sub_mulVec, hact (Pi.single j (1 : ℝ)), sub_self]
    have hj := congrFun hzero i
    simpa [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply,
      Matrix.sub_apply] using hj
  exact Matrix.ext fun i j => sub_eq_zero.mp (hcol i j)

/-- Cluster projectors are idempotent: the diagonal case of the
intersection product law (`S ∩ S = S`). -/
theorem clusterProjector_idempotent (M : Matrix V V ℝ) (hM : M.IsSymm)
    (S : Set ℝ) :
    clusterProjector M hM S * clusterProjector M hM S
      = clusterProjector M hM S := by
  rw [clusterProjector_mul_clusterProjector, Set.inter_self]

/-- The empty-cluster corner: a set selecting no eigenvalue gives the
zero projector (the filter is empty, the sum vanishes). -/
theorem clusterProjector_eq_zero_of_forall_not_mem {M : Matrix V V ℝ}
    (hM : M.IsSymm) (S : Set ℝ)
    (h : ∀ i, eigvalOf M hM i ∉ S) :
    clusterProjector M hM S = 0 := by
  classical
  have hS : (Finset.univ : Finset V).filter
      (fun i => eigvalOf M hM i ∈ S) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun x _ => h x
  ext a b
  simp [clusterProjector, hS]

/-- A covering cluster is the identity: a set containing every
eigenvalue selects the whole eigenbasis, which resolves the identity
(`eigvecOf_complete`). -/
theorem clusterProjector_eq_one_of_forall_mem {M : Matrix V V ℝ}
    (hM : M.IsSymm) (S : Set ℝ)
    (h : ∀ i, eigvalOf M hM i ∈ S) :
    clusterProjector M hM S = 1 := by
  classical
  ext a b
  have hS : (Finset.univ : Finset V).filter
      (fun i => eigvalOf M hM i ∈ S) = Finset.univ := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_of_true (h x) trivial
  simp only [clusterProjector, Matrix.of_apply, hS]
  rw [eigvecOf_complete, Matrix.one_apply]

/-- Disjoint clusters compose to zero: when `S` and `T` share no
eigenvalue, the intersection projector vanishes — the empty-intersection
case of the product law. -/
theorem clusterProjector_mul_clusterProjector_eq_zero_of_disjoint
    (M : Matrix V V ℝ) (hM : M.IsSymm) (S T : Set ℝ)
    (hST : Disjoint S T) :
    clusterProjector M hM S * clusterProjector M hM T = 0 := by
  rw [clusterProjector_mul_clusterProjector,
    clusterProjector_eq_zero_of_forall_not_mem hM (S ∩ T)]
  intro i hi
  have hbot : eigvalOf M hM i ∈ (⊥ : Set ℝ) := hST.le_bot hi
  simp at hbot

/-! ## The complement law and commutation -/

/-- **The partition of the identity.** The cluster projector of `S` and
that of its complement sum to the identity: each eigenbasis mode
contributes its outer product on exactly one side of the `S`/`Sᶜ`
split, and the whole eigenbasis resolves the identity. This is the
structural fact the interval family lacks — the complement of a band is
not a band — and it is what lets the set-form difference theorem run
without a separate complement engine. -/
theorem clusterProjector_add_clusterProjector_compl {M : Matrix V V ℝ}
    (hM : M.IsSymm) (S : Set ℝ) :
    clusterProjector M hM S + clusterProjector M hM Sᶜ = 1 := by
  classical
  have hact : ∀ y : V → ℝ,
      (clusterProjector M hM S + clusterProjector M hM Sᶜ) *ᵥ y
        = (1 : Matrix V V ℝ) *ᵥ y := by
    intro y
    refine eq_of_forall_dotProduct_eigvecOf_eq hM _ _ fun i => ?_
    rw [Matrix.add_mulVec, Matrix.dotProduct_add, Matrix.one_mulVec,
      eigvecOf_dotProduct_clusterProjector_mulVec hM S i,
      eigvecOf_dotProduct_clusterProjector_mulVec hM Sᶜ i]
    by_cases h : eigvalOf M hM i ∈ S
    · rw [if_pos h,
        if_neg (show eigvalOf M hM i ∉ Sᶜ from fun hc => hc h)]
      ring
    · rw [if_neg h, if_pos (show eigvalOf M hM i ∈ Sᶜ from h)]
      ring
  have hcol : ∀ i j : V,
      (clusterProjector M hM S + clusterProjector M hM Sᶜ - 1) i j = 0 := by
    intro i j
    have hzero : (clusterProjector M hM S + clusterProjector M hM Sᶜ - 1)
        *ᵥ (Pi.single j (1 : ℝ)) = 0 := by
      rw [Matrix.sub_mulVec, hact, Matrix.one_mulVec, sub_self]
    have hj := congrFun hzero i
    simpa [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply,
      Matrix.sub_apply] using hj
  exact Matrix.ext fun i j => sub_eq_zero.mp (hcol i j)

/-- **The complement law.** `1 − P_S = P_{Sᶜ}`: the complementary
cluster projector is the residual of the identity, immediate from the
partition of the identity. -/
theorem one_sub_clusterProjector {M : Matrix V V ℝ} (hM : M.IsSymm)
    (S : Set ℝ) :
    1 - clusterProjector M hM S = clusterProjector M hM Sᶜ := by
  rw [← clusterProjector_add_clusterProjector_compl hM S]
  abel

open Classical in
/-- A self-adjoint matrix commutes with its own cluster projector, at
the vector level. Componentwise: both sides' eigencomponents are
`χ(λ i ∈ S) * λ i * (v i ⬝ᵥ u)` — the eigenaction against the
component action. -/
theorem mulVec_clusterProjector_comm {M : Matrix V V ℝ} (hM : M.IsSymm)
    (S : Set ℝ) (u : V → ℝ) :
    M *ᵥ ((clusterProjector M hM S) *ᵥ u)
      = (clusterProjector M hM S) *ᵥ (M *ᵥ u) := by
  classical
  refine eq_of_forall_dotProduct_eigvecOf_eq hM _ _ fun i => ?_
  rw [dotProduct_eigvecOf_mulVec hM i,
    eigvecOf_dotProduct_clusterProjector_mulVec hM S i,
    eigvecOf_dotProduct_clusterProjector_mulVec hM S i,
    dotProduct_eigvecOf_mulVec hM i]
  ring_nf

/-! ## Window agreement -/

/-- The threshold projector's component action, pairing form (the
PolyFilter lemma's route, restated privately so this module needs no
PolyFilter dependency: transpose to the symmetric self, apply the
eigenbasis action, split the indicator). -/
private theorem eigvecOf_dotProduct_spectralProjector_mulVec'
    {M : Matrix V V ℝ} (hM : M.IsSymm) (c : ℝ) (i : V) (y : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) ((spectralProjector M hM c) *ᵥ y)
      = (if eigvalOf M hM i ≤ c then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf M hM i) y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    (spectralProjector_symmetric M hM c).eq,
    spectralProjector_mulVec_eigvecOf M hM c i]
  by_cases h : eigvalOf M hM i ≤ c
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul, Matrix.zero_dotProduct]

/-- The band projector's component action, pairing form (the PolyFilter
lemma's route at `a ≤ b`, restated privately — the window-agreement
bridge consumes it). -/
private theorem eigvecOf_dotProduct_bandProjector_mulVec'
    {M : Matrix V V ℝ} (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b) (i : V)
    (y : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) ((bandProjector M hM a b) *ᵥ y)
      = (if a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf M hM i) y := by
  rw [bandProjector, Matrix.sub_mulVec, Matrix.dotProduct_sub,
    eigvecOf_dotProduct_spectralProjector_mulVec' hM b i y,
    eigvecOf_dotProduct_spectralProjector_mulVec' hM a i y]
  by_cases h1 : eigvalOf M hM i ≤ b
  · by_cases h2 : eigvalOf M hM i ≤ a
    · rw [if_pos h1, if_pos h2,
        if_neg (fun hlt => not_lt.2 h2 hlt.1)]
      ring
    · rw [if_pos (⟨by linarith, h1⟩ :
          a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b), if_pos h1, if_neg h2]
      ring
  · have hband : ¬(a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b) :=
      fun hb => h1 hb.2
    have hlea : ¬(eigvalOf M hM i ≤ a) := fun hle => h1 (hle.trans hab)
    rw [if_neg h1, if_neg hband, if_neg hlea]
    ring


/-- **Capture equality at sets.** Two sets selecting the same eigenvalues
give the same cluster projector — the cluster is a class of the set, not
the set. Filter congruence on the definition; no guards (contrast the
band family's window guards, which exist only for the band's junk
regime). -/
theorem clusterProjector_eq_of_forall_mem_iff {M : Matrix V V ℝ}
    (hM : M.IsSymm) (S T : Set ℝ)
    (hiff : ∀ i, eigvalOf M hM i ∈ S ↔ eigvalOf M hM i ∈ T) :
    clusterProjector M hM S = clusterProjector M hM T := by
  classical
  have hfeq : (Finset.univ.filter (fun i => eigvalOf M hM i ∈ S))
      = Finset.univ.filter (fun i => eigvalOf M hM i ∈ T) :=
    Finset.filter_congr fun i _ => hiff i
  ext a b
  simp only [clusterProjector, Matrix.of_apply, hfeq]

/-- **The band agreement.** The cluster projector of the interval-set
`Set.Ioc a b` *is* the band projector: the entire delivered band family
(threshold, band, and every Davis–Kahan form over them) is the
interval-set special case of this module. The `a ≤ b` guard is the
*band's* junk regime — at `a > b` the band projector is the negated
`(b, a]` band while the cluster projector of the empty `Set.Ioc a b` is
`0` — not a defect of the set definition, which carries no guard. -/
theorem clusterProjector_eq_bandProjector {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b) :
    clusterProjector M hM (Set.Ioc a b) = bandProjector M hM a b := by
  classical
  have hact : ∀ y : V → ℝ,
      clusterProjector M hM (Set.Ioc a b) *ᵥ y
        = bandProjector M hM a b *ᵥ y := by
    intro y
    refine eq_of_forall_dotProduct_eigvecOf_eq hM _ _ fun i => ?_
    rw [eigvecOf_dotProduct_clusterProjector_mulVec hM (Set.Ioc a b) i,
      eigvecOf_dotProduct_bandProjector_mulVec' hM a b hab i]
    by_cases h : a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b
    · rw [if_pos (Set.mem_Ioc.mpr h), if_pos h]
    · rw [if_neg (fun hc => h (Set.mem_Ioc.mp hc)), if_neg h]
  have hcol : ∀ i j : V,
      (clusterProjector M hM (Set.Ioc a b) - bandProjector M hM a b) i j
        = 0 := by
    intro i j
    have hzero : (clusterProjector M hM (Set.Ioc a b)
        - bandProjector M hM a b) *ᵥ (Pi.single j (1 : ℝ)) = 0 := by
      rw [Matrix.sub_mulVec, hact (Pi.single j (1 : ℝ)), sub_self]
    have hj := congrFun hzero i
    simpa [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply,
      Matrix.sub_apply] using hj
  exact Matrix.ext fun i j => sub_eq_zero.mp (hcol i j)

/-! ## The rank supplier

The set-form difference theorem's equal-rank hypothesis is its one
supply-side burden; these lemmas make it checkable: the rank of a
cluster projector *is* the cardinality of the in-`S` eigenbasis filter
(via the trace and the exact `{0, 1}` spectrum of a symmetric
idempotent) — the `rank_bandProjector_eq_card` route, restated at sets. -/

section RankSupplier

variable {M : Matrix V V ℝ}

omit [DecidableEq V] in
/-- Filter-card of a predicate equals the subtype card (the
`rank_eq_card_non_zero_eigs` bridge; the ProjectionGap idiom). -/
private theorem card_filter_univ_eq' {p : V → Prop} [DecidablePred p] :
    (Finset.univ.filter p).card = Fintype.card {i // p i} := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  refine ⟨fun x => ⟨x.1, (Finset.mem_filter.1 x.2).2⟩,
    fun y => ⟨y.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, y.2⟩⟩,
    ?_, ?_⟩
  · intro x; simp
  · intro y; simp

/-- **The exact spectrum of an idempotent:** every eigenvalue of a
symmetric idempotent satisfies `μ² = μ` (apply `P² = P` to the
eigen-equation), hence lies in `{0, 1}` *exactly*. -/
private theorem eigvalOf_isSymm_idempotent_sq {P : Matrix V V ℝ}
    (hP : P.IsSymm) (hPP : P * P = P) (i : V) :
    eigvalOf P hP i * eigvalOf P hP i = eigvalOf P hP i := by
  have hev : P *ᵥ eigvecOf P hP i = eigvalOf P hP i • eigvecOf P hP i :=
    (isHermitian_of_isSymm hP).mulVec_eigenvectorBasis i
  have hv0 : eigvecOf P hP i ≠ 0 := by
    intro h
    have hnn := eigvecOf_inner P hP i i
    rw [h, if_pos rfl] at hnn
    simp at hnn
  have hL : P *ᵥ (P *ᵥ eigvecOf P hP i)
      = eigvalOf P hP i • eigvalOf P hP i • eigvecOf P hP i := by
    rw [hev, Matrix.mulVec_smul_assoc, hev]
  have hR : P *ᵥ (P *ᵥ eigvecOf P hP i)
      = eigvalOf P hP i • eigvecOf P hP i := by
    rw [Matrix.mulVec_mulVec _ P P, hPP, hev]
  have key : (eigvalOf P hP i * eigvalOf P hP i - eigvalOf P hP i)
      • eigvecOf P hP i = 0 := by
    rw [sub_smul, sub_eq_zero, mul_smul, ← hL, hR]
  rcases smul_eq_zero.mp key with h | h
  · linarith
  · exact absurd h hv0

open Classical in
/-- The trace of a cluster projector is the cardinality of the
in-`S` eigenbasis filter: each outer product `v vᵀ` contributes its unit
eigenvector's squared diagonal. -/
theorem trace_clusterProjector_eq_card (hM : M.IsSymm) (S : Set ℝ) :
    (clusterProjector M hM S).trace
      = ((Finset.univ.filter fun i => eigvalOf M hM i ∈ S).card : ℝ) := by
  classical
  have hvv : ∀ i : V,
      ∑ a : V, eigvecOf M hM i a * eigvecOf M hM i a = 1 := by
    intro i
    have h := eigvecOf_inner M hM i i
    rw [if_pos rfl] at h
    exact h
  calc (clusterProjector M hM S).trace
      = ∑ a : V, ∑ i ∈ Finset.univ.filter
          (fun i => eigvalOf M hM i ∈ S),
          eigvecOf M hM i a * eigvecOf M hM i a := by
        simp only [Matrix.trace, Matrix.diag_apply, clusterProjector,
          Matrix.of_apply]
    _ = ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ∈ S),
          ∑ a : V, eigvecOf M hM i a * eigvecOf M hM i a :=
          Finset.sum_comm
    _ = ∑ i ∈ Finset.univ.filter (fun i => eigvalOf M hM i ∈ S), (1 : ℝ) :=
          Finset.sum_congr rfl fun i _ => hvv i
    _ = _ := by simp

open Classical in
/-- **The rank supplier.** The rank of a cluster projector is exactly
the cardinality of the in-`S` eigenbasis filter — the checkable form of
the set-form difference theorem's equal-rank hypothesis (a symmetric
idempotent's rank is its trace because its spectrum lies in `{0, 1}`
exactly). -/
theorem rank_clusterProjector_eq_card (hM : M.IsSymm) (S : Set ℝ) :
    (clusterProjector M hM S).rank
      = (Finset.univ.filter fun i => eigvalOf M hM i ∈ S).card := by
  classical
  have hCP : (clusterProjector M hM S).IsSymm :=
    clusterProjector_symmetric M hM S
  have hCPidem := clusterProjector_idempotent M hM S
  have hrank' : (clusterProjector M hM S).rank
      = (Finset.univ.filter
          fun i => eigvalOf (clusterProjector M hM S) hCP i ≠ 0).card := by
    rw [card_filter_univ_eq']
    have hcard : (clusterProjector M hM S).rank = Fintype.card
        {i // (isHermitian_of_isSymm hCP).eigenvalues i ≠ 0} :=
      (isHermitian_of_isSymm hCP).rank_eq_card_non_zero_eigs
    rw [hcard]
    simp only [eigvalOf]
  have h01 : ∀ i, eigvalOf (clusterProjector M hM S) hCP i = 0 ∨
      eigvalOf (clusterProjector M hM S) hCP i = 1 := by
    intro i
    have hsq := eigvalOf_isSymm_idempotent_sq hCP hCPidem i
    have h' : eigvalOf (clusterProjector M hM S) hCP i
        * (eigvalOf (clusterProjector M hM S) hCP i - 1) = 0 := by
      rw [mul_sub, mul_one, hsq, sub_self]
    rcases mul_eq_zero.1 h' with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  have hcardsum : ((Finset.univ.filter
      fun i => eigvalOf (clusterProjector M hM S) hCP i ≠ 0).card : ℝ)
      = ∑ i, eigvalOf (clusterProjector M hM S) hCP i := by
    calc ((Finset.univ.filter
          fun i => eigvalOf (clusterProjector M hM S) hCP i ≠ 0).card : ℝ)
        = ∑ i ∈ Finset.univ.filter
            (fun i => eigvalOf (clusterProjector M hM S) hCP i ≠ 0), (1 : ℝ) :=
            by simp
      _ = ∑ i ∈ Finset.univ.filter
            (fun i => eigvalOf (clusterProjector M hM S) hCP i ≠ 0),
            eigvalOf (clusterProjector M hM S) hCP i := by
            refine Finset.sum_congr rfl fun i hi => ?_
            rw [Finset.mem_filter] at hi
            rcases h01 i with h | h
            · exact absurd h hi.2
            · exact h.symm
      _ = ∑ i, eigvalOf (clusterProjector M hM S) hCP i := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun i _ => ?_
            by_cases h : eigvalOf (clusterProjector M hM S) hCP i ≠ 0
            · rw [if_pos h]
            · rw [if_neg h, not_not.mp h]
  have htrace : ∑ i, eigvalOf (clusterProjector M hM S) hCP i
      = (clusterProjector M hM S).trace :=
    eigvalOf_sum_eq_trace _ hCP
  have hcast : (((clusterProjector M hM S).rank : ℕ) : ℝ)
      = ((Finset.univ.filter fun i => eigvalOf M hM i ∈ S).card : ℝ) := by
    rw [hrank', hcardsum, htrace, trace_clusterProjector_eq_card hM S]
  exact Nat.cast_inj.mp hcast

end RankSupplier

end SpectralGraphTheory
