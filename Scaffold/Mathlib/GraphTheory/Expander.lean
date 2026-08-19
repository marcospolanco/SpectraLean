/-
  Expander.lean

  Purpose
  -------
  Step 1 of proposal `proposals/decidable-spectral-certificates.md`
  (High; its Step 0 gate was completed and recorded in the proposal on
  2026-08-19, immediately before this module was written): the
  combinatorial edge-weight and discrepancy core for the Expander Mixing
  Lemma.

  `edgeWeight A S T = ∑ i ∈ S, ∑ j ∈ T, A i j` is the total weight of the
  ordered `(S, T)` cut. Its interface facts: the matrix form
  `indicatorVec S ⬝ᵥ (A *ᵥ indicatorVec T)` (the bilinear identity every
  spectral proof of the mixing lemma starts from) and symmetry of the
  weight in `(S, T)` for symmetric weights (sum swap).

  The characteristic-vector decomposition of the proposal: the 0/1
  indicator of `S` splits as `(card S / card V) • onesVec +
  centeredIndicator S`, where `centeredIndicator S` is exactly
  orthogonal to `onesVec` — unconditionally: on the empty vertex type
  the centered indicator vanishes, so no `Nonempty`/cardinality
  hypothesis is carried. Load-bearing for Step 2: the centered
  components of the two indicators are the vectors the adjacency
  operator acts on, and their orthogonality to `onesVec` is what makes
  the `d`-regular cross terms vanish.

  The headline `edgeWeight_eq_regular_add_centered`: on a symmetric
  `d`-regular network, `edgeWeight A S T` is exactly the population
  main term `d • |S| • |T| / |V|` plus the centered cross term
  `centeredIndicator S ⬝ᵥ (A *ᵥ centeredIndicator T)`. Step 2 of the
  proposal bounds the cross term by `μ` through the eigenbasis
  machinery; the main term is what the mixing lemma measures deviation
  from. Stated at full strength with no cardinality hypothesis (the
  empty-type case degenerates to `0 = 0 + 0`).

  Everything here is proved hard crust; this module adds no axioms.
  The decomposition is load-bearing on the exact shape of `deg` (row
  sums) and `Matrix.dotProduct_mulVec` (the transpose step that turns
  `1 ⬝ᵥ (A *ᵥ v)` into `(Aᵀ *ᵥ 1) ⬝ᵥ v`, where symmetry and regularity
  meet): an error in either breaks the main-term evaluation rather than
  passing beside it.
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## 1. Subset edge weight
-/

/-- Total weight of the ordered `(S, T)` cut: `∑ i ∈ S, ∑ j ∈ T, A i j`.
For 0/1 weights this counts the ordered pairs of adjacent vertices, so
an undirected edge inside `S ∩ T` contributes once here and once in the
reversed cut (`edgeWeight_symm`). -/
def edgeWeight (A : WAdj (V := V)) (S T : Finset V) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ T, A i j

/-- The 0/1 indicator vector of a vertex subset, as a plain function. -/
def indicatorVec (S : Finset V) : V → ℝ :=
  fun i => if i ∈ S then 1 else 0

/-- The centered indicator: the indicator of `S` minus its mean
`card S / card V`. The orthogonal component of the characteristic
vector of `S` along `onesVec`. -/
noncomputable def centeredIndicator (S : Finset V) : V → ℝ :=
  fun i => indicatorVec S i - (S.card : ℝ) / (Fintype.card V : ℝ)

omit [Fintype V] [DecidableEq V] in
/-- Degenerate cut: no source vertices, no weight. -/
theorem edgeWeight_empty_left (A : WAdj (V := V)) (T : Finset V) :
    edgeWeight A ∅ T = 0 := by
  simp [edgeWeight]

omit [Fintype V] [DecidableEq V] in
/-- Degenerate cut: no target vertices, no weight. -/
theorem edgeWeight_empty_right (A : WAdj (V := V)) (S : Finset V) :
    edgeWeight A S ∅ = 0 := by
  simp [edgeWeight]

omit [DecidableEq V] in
/-- Against the whole vertex set, the cut weight is the row-degree sum
over `S`. -/
theorem edgeWeight_univ_right (A : WAdj (V := V)) (S : Finset V) :
    edgeWeight A S Finset.univ = ∑ i ∈ S, deg A i := by
  simp [edgeWeight, deg]

/-- The matrix form of the cut weight: the bilinear identity every
spectral proof of the mixing lemma starts from. No hypotheses on `A`. -/
theorem edgeWeight_eq_dotProduct (A : WAdj (V := V)) (S T : Finset V) :
    edgeWeight A S T = indicatorVec S ⬝ᵥ (A *ᵥ indicatorVec T) := by
  have key : ∀ (g : V → ℝ) (S : Finset V),
      ∑ i, (if i ∈ S then g i else 0) = ∑ i ∈ S, g i := by
    intro g S
    rw [← Finset.sum_filter]
    congr 1
    exact Finset.ext fun i => by simp [Finset.mem_filter]
  have hite : ∀ (t : ℝ) (x : V),
      (if x ∈ S then 1 else 0) * t = if x ∈ S then t else 0 := by
    intro t x
    by_cases h : x ∈ S <;> simp [h]
  simp only [edgeWeight, indicatorVec, Matrix.dotProduct, Matrix.mulVec,
    mul_ite, mul_zero, mul_one, Finset.mul_sum, hite, key]

omit [Fintype V] [DecidableEq V] in
/-- Entrywise symmetry of the weights makes the cut weight symmetric in
`(S, T)`. -/
theorem edgeWeight_symm (A : WAdj (V := V)) (hsymm : A.IsSymm)
    (S T : Finset V) :
    edgeWeight A S T = edgeWeight A T S := by
  have h : ∀ i j, A i j = A j i := fun i j =>
    (congrArg (fun M : Matrix V V ℝ => M i j) hsymm.eq).symm
  simp only [edgeWeight]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
    h j i

/-!
## 2. The characteristic-vector decomposition
-/

/-- The sum of the indicator entries is the cardinality. -/
theorem sum_indicatorVec (S : Finset V) :
    ∑ i, indicatorVec S i = (S.card : ℝ) := by
  simp [indicatorVec,
    Finset.sum_ite_eq' Finset.univ S fun _ => (1 : ℝ)]

/-- The centered indicator sums to zero — the characteristic vector's
component along `onesVec` has been removed exactly. Unconditional: on
the empty vertex type the sum runs over an empty universe, and on a
nonempty type the cardinals cancel. -/
theorem sum_centeredIndicator_eq_zero (S : Finset V) :
    ∑ i, centeredIndicator S i = 0 := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hp
  · -- empty type: the sum runs over an empty universe
    have hne : ∀ i : V, False := by
      intro i
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨i⟩
      omega
    exact Finset.sum_eq_zero fun i _ => (hne i).elim
  · -- nonempty: `card S - card V * (card S / card V) = 0`
    have hnn : ((Fintype.card V : ℝ)) ≠ 0 := by exact_mod_cast hp.ne'
    simp only [centeredIndicator, Finset.sum_sub_distrib,
      sum_indicatorVec, Finset.sum_const, smul_eq_mul,
      Finset.card_univ (α := V)]
    field_simp

/-- The centered indicator is orthogonal to `onesVec`. -/
theorem centeredIndicator_dotProduct_onesVec (S : Finset V) :
    centeredIndicator S ⬝ᵥ onesVec = 0 := by
  simp only [Matrix.dotProduct, onesVec, mul_one]
  exact sum_centeredIndicator_eq_zero S

/-- The characteristic-vector decomposition: the indicator of `S` is its
`onesVec` component plus the centered remainder. -/
theorem indicatorVec_eq_smul_onesVec_add_centeredIndicator
    (S : Finset V) :
    indicatorVec S =
      ((S.card : ℝ) / (Fintype.card V : ℝ)) • onesVec +
        centeredIndicator S := by
  funext i
  simp only [indicatorVec, centeredIndicator, Pi.smul_apply, onesVec,
    Pi.add_apply, smul_eq_mul, mul_one]
  rw [show ((S.card : ℝ) / (Fintype.card V : ℝ)) +
      ((if i ∈ S then 1 else 0) - (S.card : ℝ) / (Fintype.card V : ℝ)) =
      (if i ∈ S then 1 else 0) from by ring]

/-!
## 3. The `d`-regular decomposition (headline)
-/

omit [DecidableEq V] in
/-- On a `d`-regular network, `A *ᵥ onesVec` is the constant `d`
(`deg` is exactly the row sum). -/
theorem mulVec_onesVec_eq_const {A : WAdj (V := V)} {d : ℝ}
    (hreg : ∀ i, deg A i = d) :
    A *ᵥ onesVec = fun _ => d := by
  funext i
  simp only [Matrix.mulVec, Matrix.dotProduct, onesVec, mul_one]
  exact hreg i

/-- **The `d`-regular decomposition.** On a symmetric `d`-regular
network, the `(S, T)` cut weight is exactly the population main term
`d • |S| • |T| / |V|` plus the centered cross term. The Expander
Mixing Lemma (proposal step 2) measures the deviation
`centeredIndicator S ⬝ᵥ (A *ᵥ centeredIndicator T)` — the bilinear
form of `A` on vectors orthogonal to `onesVec` — against the main term.
Symmetry is load-bearing (the `1 ⬝ᵥ (A *ᵥ v)` cross term dies through
`Matrix.dotProduct_mulVec`'s transpose), as is regularity (the
`A *ᵥ onesVec = d` evaluation); an error in `deg`'s row-sum shape or in
the transpose identity breaks the main-term evaluation rather than
passing beside it. No cardinality hypothesis: the empty type
degenerates to `0 = 0 + 0`. -/
theorem edgeWeight_eq_regular_add_centered (A : WAdj (V := V))
    (hsymm : A.IsSymm) (d : ℝ) (hreg : ∀ i, deg A i = d)
    (S T : Finset V) :
    edgeWeight A S T =
      d * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ) +
        centeredIndicator S ⬝ᵥ (A *ᵥ centeredIndicator T) := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hp
  · -- empty type: both cuts are empty and everything vanishes
    have hS : S = ∅ := Finset.card_eq_zero.mp (by
      have hb := Finset.card_le_card (Finset.subset_univ S)
      simp only [Finset.card_univ] at hb
      omega)
    have hT : T = ∅ := Finset.card_eq_zero.mp (by
      have hb := Finset.card_le_card (Finset.subset_univ T)
      simp only [Finset.card_univ] at hb
      omega)
    subst hS
    subst hT
    simp [edgeWeight, centeredIndicator, indicatorVec,
      Matrix.dotProduct, zero_div]
  · -- nonempty type: split, expand bilinearly, watch the cross terms die
    have hnn : ((Fintype.card V : ℝ)) ≠ 0 := by exact_mod_cast hp.ne'
    have hA1 : A *ᵥ onesVec = fun _ => d := mulVec_onesVec_eq_const hreg
    -- symmetry turns `1 ⬝ᵥ (A *ᵥ v)` into a `d`-multiple of `v ⬝ᵥ 1`
    have h1v : ∀ v : V → ℝ,
        onesVec ⬝ᵥ (A *ᵥ v) = d * (v ⬝ᵥ onesVec) := by
      intro v
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        hsymm.eq, hA1]
      simp only [Matrix.dotProduct, onesVec, mul_one, Finset.mul_sum]
    have hv1 : ∀ v : V → ℝ,
        v ⬝ᵥ ((fun _ => d : V → ℝ)) = d * (v ⬝ᵥ onesVec) := by
      intro v
      simp only [Matrix.dotProduct, onesVec, mul_one]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => (mul_comm d (v i)).symm
    have hnd : onesVec ⬝ᵥ ((fun _ => d : V → ℝ)) =
        (Fintype.card V : ℝ) * d := by
      simp [Matrix.dotProduct, onesVec, Finset.sum_const,
        Finset.card_univ]
    -- the target-vector splitting through the adjacency operator
    have hW : A *ᵥ (((T.card : ℝ) / (Fintype.card V : ℝ)) • onesVec +
        centeredIndicator T) =
        ((T.card : ℝ) / (Fintype.card V : ℝ)) • (fun _ => d) +
          A *ᵥ centeredIndicator T := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, hA1]
    -- the onesVec-source term evaluates to the population main block
    have tA : (((S.card : ℝ) / (Fintype.card V : ℝ)) • onesVec) ⬝ᵥ
        (A *ᵥ (((T.card : ℝ) / (Fintype.card V : ℝ)) • onesVec +
          centeredIndicator T)) =
        ((S.card : ℝ) / (Fintype.card V : ℝ)) *
          (((T.card : ℝ) / (Fintype.card V : ℝ)) *
            ((Fintype.card V : ℝ) * d)) := by
      rw [Matrix.smul_dotProduct, hW, Matrix.dotProduct_add,
        Matrix.dotProduct_smul]
      simp only [smul_eq_mul, h1v, hnd,
        centeredIndicator_dotProduct_onesVec, mul_zero, add_zero]
    -- the centered-source term is the centered cross term
    have tB : centeredIndicator S ⬝ᵥ
        (A *ᵥ (((T.card : ℝ) / (Fintype.card V : ℝ)) • onesVec +
          centeredIndicator T)) =
        centeredIndicator S ⬝ᵥ (A *ᵥ centeredIndicator T) := by
      rw [hW, Matrix.dotProduct_add, Matrix.dotProduct_smul]
      simp only [smul_eq_mul, hv1,
        centeredIndicator_dotProduct_onesVec, mul_zero, smul_zero,
        zero_add]
    rw [edgeWeight_eq_dotProduct,
      indicatorVec_eq_smul_onesVec_add_centeredIndicator S,
      indicatorVec_eq_smul_onesVec_add_centeredIndicator T,
      Matrix.add_dotProduct, tA, tB]
    field_simp
    ring

end SpectralGraphTheory
