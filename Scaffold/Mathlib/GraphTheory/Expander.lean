/-
  Expander.lean

  Purpose
  -------
  Steps 1 and 2 of proposal `proposals/decidable-spectral-certificates.md`
  (High; its Step 0 gate was completed and recorded in the proposal on
  2026-08-19): the combinatorial edge-weight and discrepancy core, and
  the Expander Mixing Lemma itself — the bridge between Laplacian
  spectral gaps and combinatorial pseudorandomness.

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
  hypothesis is carried. The centered components of the two indicators
  are the vectors the adjacency operator acts on, and their
  orthogonality to `onesVec` is what makes the `d`-regular cross terms
  vanish.

  `edgeWeight_eq_regular_add_centered`: on a symmetric `d`-regular
  network, `edgeWeight A S T` is exactly the population main term
  `d • |S| • |T| / |V|` plus the centered cross term
  `centeredIndicator S ⬝ᵥ (A *ᵥ centeredIndicator T)`. Stated at full
  strength with no cardinality hypothesis (the empty-type case
  degenerates to `0 = 0 + 0`).

  Step 2, the bridge layer and the headline `expander_mixing_lemma`:
  the spectral hypothesis is stated in Laplacian terms (Step 0's
  convention decision), `μ ≥ max |d − λ₂(L)| |d − λ_max(L)|`, and the
  proof is a Rayleigh sandwich on `1⊥` — no eigenspace decomposition
  of the adjacency operator, no kernel case analysis, no affine
  spectrum transfer:

  - the `d`-regular identity `quadForm A x + quadForm L x = d • ‖x‖²`
    (the quadratic form of `A + L = D`; regularity alone, no
    looplessness — the Step 0 sketch carried `hloop`, found
    unnecessary and dropped, a strengthening recorded in the
    proposal);
  - the lower bound `λ₂ • ‖x‖² ≤ xᵀLx` on `x ⊥ 1`
    (`lambda2_mul_dotProduct_le_quadForm`, from the proved
    `secondEval_le_rayleigh` multiplied out) and the upper bound
    `xᵀLx ≤ λ_max • ‖x‖²` (the generic `quadForm_le_evals_last`, whose
    support lemma `eigvalOf_le_evals_last` and public positivity idiom
    `dotProduct_self_pos` live in `GraphTheory.Spectral`);
  - the operator bound `|xᵀAx| ≤ μ ‖x‖²` on `1⊥`
    (`abs_quadForm_le_of_ortho_onesVec`);
  - the sharp bilinear bound `(x ⬝ᵥ (A *ᵥ y))² ≤ μ² ‖x‖² ‖y‖²` on
    `1⊥ × 1⊥` (`quadForm_bilinear_sq_le_of_ortho_onesVec`) by the
    scaling trick — the polarization identity
    (`quadForm_add_sub_eq`) applied to `√Y • x ± √X • y`, where the
    choice `a² = Y, b² = X` attains the arithmetic-geometric equality,
    so no AM–GM slack enters;
  - the variance identity `‖centeredIndicator S‖² = |S|(|V|−|S|)/|V|`
    (`dotProduct_centeredIndicator_self`), which evaluates the
    geometric factor.

  Everything here is proved hard crust; this module adds no axioms.
  The decomposition is load-bearing on the exact shape of `deg` (row
  sums) and `Matrix.dotProduct_mulVec` (the transpose step that turns
  `1 ⬝ᵥ (A *ᵥ v)` into `(Aᵀ *ᵥ 1) ⬝ᵥ v`, where symmetry and regularity
  meet): an error in either breaks the main-term evaluation rather than
  passing beside it. The sandwich is load-bearing on the two variational
  bounds and the `A + L = D` identity: an error in any of the three
  breaks the mixing lemma rather than passing beside it.
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

/-!
## 4. The polarization identity and the degree-matrix form (Step 2)

Pure matrix algebra consumed by the Rayleigh sandwich: the bilinear
cross term of a symmetric form is recovered from quadratic forms at
sums and differences, and the quadratic form of the degree matrix is
the degree-weighted sum of squares.
-/

omit [DecidableEq V] in
/-- Quadratic forms are additive in the matrix: `D − A = L` bookkeeping
starts here. -/
theorem quadForm_add (M N : Matrix V V ℝ) (x : V → ℝ) :
    quadForm (M + N) x = quadForm M x + quadForm N x := by
  show x ⬝ᵥ ((M + N) *ᵥ x) = x ⬝ᵥ (M *ᵥ x) + x ⬝ᵥ (N *ᵥ x)
  rw [Matrix.add_mulVec, Matrix.dotProduct_add]

omit [DecidableEq V] in
/-- **Polarization for symmetric forms.** The difference of the
quadratic form at `x + y` and at `x - y` isolates four times the
bilinear cross term `x ⬝ᵥ (M *ᵥ y)`. Symmetry is load-bearing: it is
what folds the `y ⬝ᵥ (M *ᵥ x)` half of the pointwise expansion onto
the `x ⬝ᵥ (M *ᵥ y)` half. -/
theorem quadForm_add_sub_eq {M : Matrix V V ℝ} (hM : M.IsSymm)
    (x y : V → ℝ) :
    quadForm M (x + y) - quadForm M (x - y) = 4 * (x ⬝ᵥ (M *ᵥ y)) := by
  have hkey : ∀ i : V,
      (x i + y i) * ((M *ᵥ x) i + (M *ᵥ y) i)
        - (x i - y i) * ((M *ᵥ x) i - (M *ᵥ y) i)
        = 2 * (x i * (M *ᵥ y) i) + 2 * (y i * (M *ᵥ x) i) := fun i => by ring
  have hswap : y ⬝ᵥ (M *ᵥ x) = x ⬝ᵥ (M *ᵥ y) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM.eq,
      Matrix.dotProduct_comm]
  simp only [Matrix.dotProduct] at hswap
  have hBsum : ∑ i, 2 * (y i * (M *ᵥ x) i)
      = ∑ i, 2 * (x i * (M *ᵥ y) i) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hswap]
  simp only [quadForm, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.dotProduct, Pi.add_apply, Pi.sub_apply]
  have hfold2 : ∑ i, 2 * (x i * (M *ᵥ y) i) = 2 * ∑ i, x i * (M *ᵥ y) i :=
    (Finset.mul_sum _ _ _).symm
  rw [← Finset.sum_sub_distrib,
    Finset.sum_congr rfl fun i _ => hkey i, Finset.sum_add_distrib,
    hBsum, hfold2]
  ring

/-- The quadratic form of the degree matrix is the degree-weighted sum
of squares (the diagonal carries the degrees, everything else dies). -/
theorem quadForm_degreeMatrix (A : WAdj (V := V)) (x : V → ℝ) :
    quadForm (degreeMatrix A) x = ∑ i, deg A i * x i ^ 2 := by
  have hrow : ∀ i : V, ∑ j, degreeMatrix A i j * x j = deg A i * x i := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [degreeMatrix_diagonal]
    · intro j _ hj
      rw [degreeMatrix_off_diagonal A (Ne.symm hj), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [hrow i]; ring

/-!
## 5. The Rayleigh sandwich on `1⊥` (Step 2 bridge layer)

The Expander Mixing Lemma's spectral input is stated in *Laplacian*
terms (Step 0's convention decision): `μ ≥ max |d − λ₂(L)| |d −
λ_max(L)|`. The bridge to the adjacency operator's action on `1⊥` is a
sandwich: on vectors orthogonal to `onesVec`, the Laplacian energy sits
between `λ₂ • ‖x‖²` (the proved variational lower bound, multiplied
out) and `λ_max • ‖x‖²` (top-eigenvalue Rayleigh domination), while the
`d`-regular identity `quadForm A x + quadForm L x = d • ‖x‖²` trades
between the two operators. No eigenspace decomposition of the adjacency
operator, no case analysis on the kernel, and no affine spectrum
transfer are needed — the sandwich is exactly the two variational
bounds the center already owns.
-/

/-- The `d`-regular identity: adjacency energy plus Laplacian energy is
`d` times the squared norm — the quadratic form of `A + L = D` under
regularity. Consumes only `deg`'s row-sum shape; no looplessness is
needed (self-loop weights cancel in `D − A` either way). -/
theorem quadForm_add_quadForm_laplacian (A : WAdj (V := V)) (d : ℝ)
    (hreg : ∀ i, deg A i = d) (x : V → ℝ) :
    quadForm A x + quadForm (laplacian A) x = d * (x ⬝ᵥ x) := by
  have hsum : quadForm (A + laplacian A) x
      = quadForm A x + quadForm (laplacian A) x := quadForm_add _ _ _
  have hAL : A + laplacian A = degreeMatrix A := by
    rw [laplacian]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  have hdeg : quadForm (degreeMatrix A) x = d * (x ⬝ᵥ x) := by
    rw [quadForm_degreeMatrix,
      Finset.sum_congr rfl fun i _ => by rw [hreg i], ← Finset.mul_sum]
    congr 1
    show ∑ i, x i ^ 2 = ∑ i, x i * x i
    exact Finset.sum_congr rfl fun i _ => by rw [pow_two]
  rw [← hsum, hAL, hdeg]

/-- **The variational lower bound, multiplication form.** On nonzero
vectors orthogonal to `onesVec`, the Laplacian energy is at least `λ₂`
times the squared norm. `secondEval_le_rayleigh` multiplied out through
the denominator positivity; the zero vector is handled separately (both
sides vanish), so consumers never case-split. -/
theorem lambda2_mul_dotProduct_le_quadForm (A : WAdj (V := V))
    (hsymm : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V)
    {x : V → ℝ} (hx : x ⬝ᵥ onesVec = 0) :
    lambda2 A hsymm hcard * (x ⬝ᵥ x) ≤ quadForm (laplacian A) x := by
  by_cases hx0 : x = 0
  · subst hx0
    have h0 : quadForm (laplacian A) (0 : V → ℝ) = 0 := by
      show (0 : V → ℝ) ⬝ᵥ ((laplacian A) *ᵥ (0 : V → ℝ)) = 0
      rw [Matrix.zero_dotProduct]
    rw [h0, Matrix.zero_dotProduct, mul_zero]
  · have hX : 0 < x ⬝ᵥ x := dotProduct_self_pos hx0
    have h := secondEval_le_rayleigh (laplacian_symmetric A hsymm)
      (laplacian_psd A hsymm hnn) (laplacian_ones_in_kernel A) hcard hx0 hx
    unfold rayleigh at h
    rw [if_neg hx0, le_div_iff₀ hX, ← lambda2_eq_secondEval] at h
    exact h

/-- **The operator bound on `1⊥` — the Step 2 bridge.** For a
symmetric, nonnegative, `d`-regular network whose Laplacian spectrum
satisfies `max |d − λ₂| |d − λ_max| ≤ μ`, every vector orthogonal to
`onesVec` has adjacency energy bounded by `μ` times its squared norm.
The proof is the Rayleigh sandwich: `quadForm A x = d‖x‖² −
quadForm L x` with `quadForm L x` pinned between `λ₂‖x‖²` and
`λ_max‖x‖²`. Load-bearing on `secondEval_le_rayleigh`,
`quadForm_le_evals_last`, and the `A + L = D` identity — an error in
any of the three breaks the sandwich rather than passing beside it. -/
theorem abs_quadForm_le_of_ortho_onesVec (A : WAdj (V := V))
    (hsymm : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ)
    (hreg : ∀ i, deg A i = d) (hcard : 2 ≤ Fintype.card V) (μ : ℝ)
    (hμ : max |d - lambda2 A hsymm hcard|
          |d - evals (laplacian_symmetric A hsymm)
              ⟨Fintype.card V - 1, by omega⟩| ≤ μ)
    {x : V → ℝ} (hx : x ⬝ᵥ onesVec = 0) :
    |quadForm A x| ≤ μ * (x ⬝ᵥ x) := by
  have hn : 1 ≤ Fintype.card V := le_trans (by norm_num) hcard
  have hXnn : 0 ≤ x ⬝ᵥ x :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hlow : lambda2 A hsymm hcard * (x ⬝ᵥ x)
      ≤ quadForm (laplacian A) x :=
    lambda2_mul_dotProduct_le_quadForm A hsymm hnn hcard hx
  have hup : quadForm (laplacian A) x ≤
      evals (laplacian_symmetric A hsymm) ⟨Fintype.card V - 1, by omega⟩ *
        (x ⬝ᵥ x) :=
    quadForm_le_evals_last (laplacian_symmetric A hsymm) hn x
  have haff : quadForm A x + quadForm (laplacian A) x = d * (x ⬝ᵥ x) :=
    quadForm_add_quadForm_laplacian A d hreg x
  have ha1 : |d - lambda2 A hsymm hcard| ≤ μ :=
    le_trans (le_max_left _ _) hμ
  have ha2 : |d - evals (laplacian_symmetric A hsymm)
      ⟨Fintype.card V - 1, by omega⟩| ≤ μ :=
    le_trans (le_max_right _ _) hμ
  refine abs_le.2 ⟨?_, ?_⟩ <;>
    nlinarith [hXnn, hlow, hup, haff, ha1, ha2, abs_le.1 ha1, abs_le.1 ha2]

/-- **The bilinear bound on `1⊥`, sharp form.** The centered cross term
of the mixing lemma is bounded in squared form: `(x ⬝ᵥ (A *ᵥ y))² ≤
μ² ‖x‖² ‖y‖²` for `x, y ⊥ onesVec`. The proof is the scaling trick —
apply the operator bound to `√Y • x ± √X • y`, where the two quadratic
forms differ by polarization, and divide by `(4 √X √Y)²`; the choice
`a² = Y, b² = X` attains the arithmetic-geometric equality, so no
AM–GM slack is introduced. -/
theorem quadForm_bilinear_sq_le_of_ortho_onesVec (A : WAdj (V := V))
    (hsymm : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ)
    (hreg : ∀ i, deg A i = d) (hcard : 2 ≤ Fintype.card V) (μ : ℝ)
    (hμ : max |d - lambda2 A hsymm hcard|
          |d - evals (laplacian_symmetric A hsymm)
              ⟨Fintype.card V - 1, by omega⟩| ≤ μ)
    {x y : V → ℝ} (hx : x ⬝ᵥ onesVec = 0) (hy : y ⬝ᵥ onesVec = 0) :
    (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ μ ^ 2 * (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  have hXnn : 0 ≤ x ⬝ᵥ x :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hYnn : 0 ≤ y ⬝ᵥ y :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (y i)
  rcases eq_or_lt_of_le hXnn with hX0 | hXpos
  · -- ‖x‖² = 0 forces x = 0 and the cross term dies
    have hx0 : x = 0 := by
      funext i
      by_contra hne
      exact absurd hX0 (Finset.sum_pos'
        (fun j _ => mul_self_nonneg (x j))
        ⟨i, Finset.mem_univ _, mul_self_pos.2 hne⟩).ne
    rw [hx0, Matrix.dotProduct_zero]
    simp
  rcases eq_or_lt_of_le hYnn with hY0 | hYpos
  · -- ‖y‖² = 0 forces y = 0 and the operator kills it
    have hy0 : y = 0 := by
      funext i
      by_contra hne
      exact absurd hY0 (Finset.sum_pos'
        (fun j _ => mul_self_nonneg (y j))
        ⟨i, Finset.mem_univ _, mul_self_pos.2 hne⟩).ne
    rw [hy0, Matrix.mulVec_zero, Matrix.dotProduct_zero]
    simp
  -- both squared norms positive: the scaled polarization argument
  set a : ℝ := Real.sqrt (y ⬝ᵥ y) with hadef
  set b : ℝ := Real.sqrt (x ⬝ᵥ x) with hbdef
  have ha2 : a ^ 2 = y ⬝ᵥ y := Real.sq_sqrt hYnn
  have hb2 : b ^ 2 = x ⬝ᵥ x := Real.sq_sqrt hXnn
  have hμpos : 0 ≤ μ := le_trans (abs_nonneg _) (le_trans (le_max_left _ _) hμ)
  -- the two scaled combinations stay orthogonal to onesVec
  have hz1 : (a • x + b • y) ⬝ᵥ onesVec = 0 := by
    rw [Matrix.add_dotProduct, Matrix.smul_dotProduct,
      Matrix.smul_dotProduct, hx, hy, smul_zero, smul_zero, add_zero]
  have hz2 : (a • x - b • y) ⬝ᵥ onesVec = 0 := by
    rw [Matrix.sub_dotProduct, Matrix.smul_dotProduct,
      Matrix.smul_dotProduct, hx, hy, smul_zero, smul_zero, sub_zero]
  have hb1 := abs_quadForm_le_of_ortho_onesVec A hsymm hnn d hreg hcard μ hμ hz1
  have hb2' := abs_quadForm_le_of_ortho_onesVec A hsymm hnn d hreg hcard μ hμ hz2
  -- the cross term is bilinear
  have hbil : (a • x) ⬝ᵥ (A *ᵥ (b • y)) = a * b * (x ⬝ᵥ (A *ᵥ y)) := by
    rw [Matrix.mulVec_smul, Matrix.smul_dotProduct, Matrix.dotProduct_smul,
      smul_eq_mul, smul_eq_mul]
    ring
  -- polarization isolates the cross term
  have hpol : quadForm A (a • x + b • y) - quadForm A (a • x - b • y)
      = 4 * (a * b * (x ⬝ᵥ (A *ᵥ y))) := by
    rw [quadForm_add_sub_eq hsymm, hbil]
  -- the parallelogram identity on the two norms
  have hpara : (a • x + b • y) ⬝ᵥ (a • x + b • y)
      + (a • x - b • y) ⬝ᵥ (a • x - b • y)
      = 4 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) := by
    have hgen : ∀ u w : V → ℝ,
        (u + w) ⬝ᵥ (u + w) + (u - w) ⬝ᵥ (u - w)
          = 2 * (u ⬝ᵥ u) + 2 * (w ⬝ᵥ w) := by
      intro u w
      have e1 : ∀ i : V, (u i + w i) * (u i + w i)
          + (u i - w i) * (u i - w i)
          = 2 * (u i * u i) + 2 * (w i * w i) := fun i => by ring
      simp only [Matrix.dotProduct, Pi.add_apply, Pi.sub_apply]
      rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun i _ => e1 i,
        Finset.sum_add_distrib]
      congr 1 <;> exact (Finset.mul_sum _ _ _).symm
    calc (a • x + b • y) ⬝ᵥ (a • x + b • y)
        + (a • x - b • y) ⬝ᵥ (a • x - b • y)
        = 2 * ((a • x) ⬝ᵥ (a • x)) + 2 * ((b • y) ⬝ᵥ (b • y)) :=
          hgen (a • x) (b • y)
      _ = 4 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) := by
          rw [Matrix.smul_dotProduct, Matrix.dotProduct_smul,
            Matrix.smul_dotProduct, Matrix.dotProduct_smul, smul_eq_mul,
            smul_eq_mul, smul_eq_mul, smul_eq_mul]
          nlinarith [ha2, hb2]
  -- combine the two operator bounds through polarization
  have key : |4 * (a * b * (x ⬝ᵥ (A *ᵥ y)))|
      ≤ μ * (4 * ((x ⬝ᵥ x) * (y ⬝ᵥ y))) := by
    rw [← hpol]
    calc |quadForm A (a • x + b • y) - quadForm A (a • x - b • y)|
        ≤ |quadForm A (a • x + b • y)|
            + |quadForm A (a • x - b • y)| := abs_sub _ _
      _ ≤ μ * ((a • x + b • y) ⬝ᵥ (a • x + b • y))
            + μ * ((a • x - b • y) ⬝ᵥ (a • x - b • y)) :=
          add_le_add hb1 hb2'
      _ = μ * (4 * ((x ⬝ᵥ x) * (y ⬝ᵥ y))) := by
          rw [← hpara]; ring
  -- square and divide by the positive common factor (4ab)² = 16 ‖x‖²‖y‖²
  have hnonnegR : 0 ≤ μ * (4 * ((x ⬝ᵥ x) * (y ⬝ᵥ y))) := by
    exact mul_nonneg hμpos (by nlinarith)
  obtain ⟨hneg, hposle⟩ := abs_le.mp key
  have h1sq : (4 * (a * b * (x ⬝ᵥ (A *ᵥ y)))) ^ 2
      ≤ (μ * (4 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)))) ^ 2 := sq_le_sq' hneg hposle
  have hCpos : (0:ℝ) < 16 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) := by nlinarith
  rw [← mul_le_mul_left hCpos]
  have h1exp : (4 * (a * b * (x ⬝ᵥ (A *ᵥ y)))) ^ 2
      = 16 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) * (x ⬝ᵥ (A *ᵥ y)) ^ 2 := by
    linear_combination (16 * (x ⬝ᵥ (A *ᵥ y)) ^ 2 * a ^ 2) * hb2
      + (16 * (x ⬝ᵥ (A *ᵥ y)) ^ 2 * (x ⬝ᵥ x)) * ha2
  calc 16 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) * (x ⬝ᵥ (A *ᵥ y)) ^ 2
      = (4 * (a * b * (x ⬝ᵥ (A *ᵥ y)))) ^ 2 := h1exp.symm
    _ ≤ (μ * (4 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)))) ^ 2 := h1sq
    _ = 16 * ((x ⬝ᵥ x) * (y ⬝ᵥ y)) * (μ ^ 2 * (x ⬝ᵥ x) * (y ⬝ᵥ y)) := by
          ring

/-!
## 6. The norm of the centered indicator
-/

/-- The squared norm of the centered indicator of `S` is
`|S| • (|V| − |S|) / |V|` — the variance of the 0/1 indicator. This is
the geometric factor the Expander Mixing Lemma's bound carries. On the
empty vertex type both sides vanish (the sum runs over an empty
universe and the numerator carries a zero factor). -/
theorem dotProduct_centeredIndicator_self (S : Finset V) :
    centeredIndicator S ⬝ᵥ centeredIndicator S =
      (S.card : ℝ) * ((Fintype.card V : ℝ) - (S.card : ℝ)) /
        (Fintype.card V : ℝ) := by
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h0 | hp
  · have hne : ∀ i : V, False := by
      intro i
      have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨i⟩
      omega
    have hS : S = ∅ := Finset.card_eq_zero.mp (by
      have hb := Finset.card_le_card (Finset.subset_univ S)
      simp only [Finset.card_univ] at hb
      omega)
    subst hS
    have hL : centeredIndicator (∅ : Finset V) ⬝ᵥ centeredIndicator ∅ = 0 := by
      simp [Matrix.dotProduct, centeredIndicator, indicatorVec]
    rw [hL, Finset.card_empty]
    norm_num
  · have hnn : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hexp : ∀ i : V, centeredIndicator S i * centeredIndicator S i
        = (indicatorVec S i) ^ 2
          - 2 * ((S.card : ℝ) / (Fintype.card V : ℝ)) * indicatorVec S i
          + ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 := by
      intro i
      simp only [centeredIndicator, Pi.sub_apply]
      ring
    have hself : ∀ i : V, (indicatorVec S i) ^ 2 = indicatorVec S i := by
      intro i
      by_cases h : i ∈ S <;> simp [indicatorVec, h]
    have hmid : ∑ i, 2 * ((S.card : ℝ) / (Fintype.card V : ℝ))
        * indicatorVec S i
        = 2 * ((S.card : ℝ) / (Fintype.card V : ℝ)) * (S.card : ℝ) := by
      rw [show ∑ i, 2 * ((S.card : ℝ) / (Fintype.card V : ℝ))
          * indicatorVec S i
          = 2 * ((S.card : ℝ) / (Fintype.card V : ℝ))
            * ∑ i, indicatorVec S i from (Finset.mul_sum _ _ _).symm,
        sum_indicatorVec]
    have hconst : ∑ i : V, ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2
        = (Fintype.card V : ℝ)
          * ((S.card : ℝ) / (Fintype.card V : ℝ)) ^ 2 := by
      simp [Finset.sum_const]
    show ∑ i, centeredIndicator S i * centeredIndicator S i = _
    rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_congr rfl fun i _ => hself i,
      sum_indicatorVec, hmid, hconst]
    field_simp
    ring

/-!
## 7. The Expander Mixing Lemma (Step 2 headline)
-/

omit [DecidableEq V] in
/-- Arithmetic packaging (private): from the squared bilinear bound
`B² ≤ μ² • (s(n−s)/n) • (t(n−t)/n)` with nonnegative `s ≤ n`, `t ≤ n`,
positive `n`, nonnegative `μ`, assemble the radical-form bound
`|B| ≤ μ • √(s t (n−s) (n−t)) / n`. Pure ordered-field and
square-root manipulation; no graph content. -/
private theorem sqrt_assembly {s t n μ B : ℝ} (hn : 0 < n) (hs : 0 ≤ s)
    (ht : 0 ≤ t) (hsn : s ≤ n) (htn : t ≤ n) (hμ : 0 ≤ μ)
    (hB : B ^ 2 ≤ μ ^ 2 * (s * (n - s) / n) * (t * (n - t) / n)) :
    |B| ≤ μ * Real.sqrt (s * t * (n - s) * (n - t)) / n := by
  have hnn1 : 0 ≤ n - s := sub_nonneg.2 hsn
  have hnn2 : 0 ≤ n - t := sub_nonneg.2 htn
  have hP : 0 ≤ s * t * (n - s) * (n - t) :=
    mul_nonneg (mul_nonneg (mul_nonneg hs ht) hnn1) hnn2
  have hR : 0 ≤ μ * Real.sqrt (s * t * (n - s) * (n - t)) / n :=
    div_nonneg (mul_nonneg hμ (Real.sqrt_nonneg _)) hn.le
  have hnum : (μ * Real.sqrt (s * t * (n - s) * (n - t))) ^ 2
      = μ ^ 2 * (s * t * (n - s) * (n - t)) := by
    have hq : Real.sqrt (s * t * (n - s) * (n - t))
        * Real.sqrt (s * t * (n - s) * (n - t))
        = s * t * (n - s) * (n - t) := Real.mul_self_sqrt hP
    nlinarith [hq]
  have key : B ^ 2 ≤ (μ * Real.sqrt (s * t * (n - s) * (n - t)) / n) ^ 2 := by
    rw [div_pow, hnum]
    field_simp at hB ⊢
    linear_combination hB
  have habs : |B| ^ 2 = B ^ 2 := by
    rw [pow_two, ← abs_mul, abs_of_nonneg (mul_self_nonneg B), pow_two]
  rw [← habs] at key
  exact le_of_sq_le_sq key hR

/-- **The Expander Mixing Lemma** (proposal
`decidable-spectral-certificates.md`, Step 2; convention per its Step 0
decision 1: Laplacian-first through the `d`-regular bridge).

For a symmetric, nonnegative, `d`-regular network whose Laplacian
spectrum satisfies `μ ≥ max |d − λ₂(L)| |d − λ_max(L)|`, the `(S, T)`
cut weight deviates from the population main term
`d • |S| • |T| / |V|` by at most
`μ • √(|S| |T| (|V|−|S|) (|V|−|T|)) / |V|` — the classical discrepancy
bound between algebraic spectral gaps and combinatorial
pseudorandomness ([AC]: Alon–Chung 1988; [HLW]: Hoory–Linial–Wigderson
2006, §2; [V]: Vadhan 2012, §4).

The statement is the proposal's restated `√`-form; both sides are
nonnegative and the proof works with the squared inequality in
ordered-field arithmetic (`sqrt_assembly`). Note on hypotheses: the
Step 0 sketch carried `hloop : ∀ i, A i i = 0`; the delivered route
does not consume it (the identity `A + L = D` holds under regularity
alone, since `D`'s diagonal already carries the row sums including
self-loops), so it is dropped — a statement-shape strengthening
recorded in the proposal's delivery note.

Proof: the `d`-regular decomposition (Step 1) reduces the deviation to
the centered cross term; the Rayleigh sandwich on `1⊥` bounds it
through the sharp bilinear form; `dotProduct_centeredIndicator_self`
evaluates the geometric factor. -/
theorem expander_mixing_lemma (A : WAdj (V := V)) (hsymm : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ) (hreg : ∀ i, deg A i = d)
    (hcard : 2 ≤ Fintype.card V) (μ : ℝ)
    (hμ : max |d - lambda2 A hsymm hcard|
          |d - evals (laplacian_symmetric A hsymm)
              ⟨Fintype.card V - 1, by omega⟩| ≤ μ)
    (S T : Finset V) :
    |edgeWeight A S T
        - d * (S.card : ℝ) * (T.card : ℝ) / (Fintype.card V : ℝ)| ≤
      μ * Real.sqrt ((S.card : ℝ) * (T.card : ℝ)
        * ((Fintype.card V : ℝ) - (S.card : ℝ))
        * ((Fintype.card V : ℝ) - (T.card : ℝ)))
        / (Fintype.card V : ℝ) := by
  have hn : (0:ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast (by omega : 0 < Fintype.card V)
  have hsnn : 0 ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have htnn : 0 ≤ (T.card : ℝ) := Nat.cast_nonneg _
  have hsn : (S.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.subset_univ S)
  have htn : (T.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.subset_univ T)
  have hμpos : 0 ≤ μ := le_trans (abs_nonneg _) (le_trans (le_max_left _ _) hμ)
  have hcross := quadForm_bilinear_sq_le_of_ortho_onesVec A hsymm hnn d hreg
    hcard μ hμ (centeredIndicator_dotProduct_onesVec S)
    (centeredIndicator_dotProduct_onesVec T)
  rw [dotProduct_centeredIndicator_self S,
    dotProduct_centeredIndicator_self T] at hcross
  rw [edgeWeight_eq_regular_add_centered A hsymm d hreg S T,
    add_sub_cancel_left]
  exact sqrt_assembly hn hsnn htnn hsn htn hμpos hcross

end SpectralGraphTheory
