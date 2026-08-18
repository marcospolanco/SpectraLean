import Scaffold.Mathlib.GraphTheory.Spectral

/-!
# Cheeger inequalities for regular graphs

The relationship between the conductance (Cheeger constant) of a graph
and the spectral gap of its normalized Laplacian.

For `d`-regular graphs the symmetric normalized Laplacian
`L_sym = I - D^{-1/2} A D^{-1/2}` reduces to `1 - d⁻¹ • A`, so the
inequalities can be stated with Scaffold's matrix-first API without a
matrix square root. The general irregular statement is future work: it
requires positive-definite degree matrices and a matrix square root
(`Matrix.posSqrt` is not available in the pinned Mathlib).

Source:
- Chung, F. R. K., "Spectral Graph Theory", CBMS Regional Conference
  Series 92, AMS, 1997, Chapter 2. Section-level locator; the legacy
  page-level locators recorded in earlier revisions referred to a
  different statement shape and were dropped pending citation review.

Conventions: `cheegerConstant` is defined from the volume-based
conductance `boundary / min (vol S, vol Sᶜ)`; for a `d`-regular graph
with positive degree this is the standard conductance, since
`vol S = d * card S`.
-/

open scoped Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The symmetric normalized Laplacian of a `d`-regular weighted graph,
where `D = d • 1` and `L_sym = I - d⁻¹ • A`. For nonzero `d` this matrix
is symmetric whenever `A` is; regularity is a hypothesis of the
inequalities below, not of the definition. -/
noncomputable def regularNormalizedLaplacian (A : WAdj (V := V)) (d : ℝ) : Matrix V V ℝ :=
  1 - d⁻¹ • A

/-- The regular normalized Laplacian of a symmetric weighted adjacency
matrix is symmetric. -/
theorem regularNormalizedLaplacian_symmetric (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (d : ℝ) :
    Matrix.IsSymm (regularNormalizedLaplacian A d) := by
  refine Matrix.IsSymm.ext fun i j => ?_
  simp only [regularNormalizedLaplacian, Matrix.sub_apply, Pi.one_apply,
    Matrix.one_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h
    simp [(hA.apply i i).symm]
  · simp [h, Ne.symm h, hA.apply j i]

/-- Cheeger lower bound for `d`-regular graphs: the squared conductance
controls the second-smallest normalized Laplacian eigenvalue from below,
`φ(G)² / 2 ≤ λ₂(L_sym)`.

Source:
- Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997,
  Chapter 2.

Statement differences: restricted to `d`-regular graphs with positive
degree `d` (so that `regularNormalizedLaplacian A d` is the symmetric
normalized Laplacian); `cheegerConstant` is the infimum of the
volume-based conductance over nonempty proper vertex subsets.

Statement-shape correction (2026-08-18): earlier revisions stated the
spectral side as `lambda2 (regularNormalizedLaplacian A d) …`. That was
a defective shape, not a strengthening: `lambda2` reads the spectrum of
the *combinatorial Laplacian of* its argument, and every row of a
normalized Laplacian sums to zero, so the asserted quantity was
`λ₂(L(L_sym)) = λ₂(-L_sym)` — on the two-vertex edge the instance reads
`1/2 ≤ 0`, which is false (refuted in proved form by
`SpectralGraphTheory.QA.old_cheeger_lower_bound_refuted_QA`). The
corrected side `secondEval (regularNormalizedLaplacian A d) …` reads
`λ₂(L_sym)` itself, matching the cited source; hypotheses and name are
otherwise unchanged.

QA: exercised by
`SpectralGraphTheory.QA.cheeger_positive_implies_secondEval_pos_QA` and
`SpectralGraphTheory.QA.cheeger_bounds_coherent_QA` in
`Scaffold/QA/SpectralGraph/Cheeger_QA.lean`, which derives consequences
from this axiom, and by
`SpectralGraphTheory.QA.edge_normLap_secondEval_eq_two_QA`, which pins
the corrected right-hand side on the two-vertex edge to its classical
value `2`.
-/
axiom cheeger_lower_bound (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) :
    (cheegerConstant A) ^ 2 / 2 ≤
      secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard

/-!
### Regularity bridges to the combinatorial Laplacian and volumes
(proved)
-/

omit [DecidableEq V] in
/-- The quadratic form of a scaled matrix is the scaled quadratic form. -/
theorem quadForm_smul (c : ℝ) (M : Matrix V V ℝ) (x : V → ℝ) :
    quadForm (c • M) x = c * quadForm M x := by
  simp only [quadForm, Matrix.mulVec, Matrix.dotProduct, Matrix.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => by ring

/-- Under `d`-regularity with `d ≠ 0`, the combinatorial Laplacian is
`d • L_sym`: the degree matrix is `d • 1` entrywise. -/
theorem smul_regularNormalizedLaplacian (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdne : d ≠ 0) :
    d • regularNormalizedLaplacian A d = laplacian A := by
  ext i j
  have hdA : d * (d⁻¹ * A i j) = A i j := by
    rw [← mul_assoc, mul_inv_cancel₀ hdne, one_mul]
  by_cases hij : i = j
  · subst hij
    have hdg : degreeMatrix A i i = d := by rw [degreeMatrix_diagonal, hd i]
    rw [Matrix.smul_apply, smul_eq_mul, regularNormalizedLaplacian,
      Matrix.sub_apply, Matrix.one_apply, if_pos rfl, Matrix.smul_apply,
      smul_eq_mul, mul_sub, mul_one, laplacian, Matrix.sub_apply, hdg, hdA]
  · rw [Matrix.smul_apply, smul_eq_mul, regularNormalizedLaplacian,
      Matrix.sub_apply, Matrix.one_apply, if_neg hij, Matrix.smul_apply,
      smul_eq_mul, mul_sub, mul_zero, zero_sub, laplacian,
      Matrix.sub_apply, degreeMatrix_off_diagonal A hij, zero_sub, hdA]

/-- The regular normalized Laplacian's quadratic form is the
combinatorial one scaled by `d⁻¹` (via `smul_regularNormalizedLaplacian`,
no square roots needed). -/
theorem quadForm_regularNormalizedLaplacian (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdne : d ≠ 0) (x : V → ℝ) :
    quadForm (regularNormalizedLaplacian A d) x
      = d⁻¹ * quadForm (laplacian A) x := by
  have hQ : quadForm (d • regularNormalizedLaplacian A d) x
      = d * quadForm (regularNormalizedLaplacian A d) x :=
    quadForm_smul d (regularNormalizedLaplacian A d) x
  rw [smul_regularNormalizedLaplacian A d hd hdne] at hQ
  rw [eq_inv_mul_iff_mul_eq₀ hdne]  -- d⁻¹ * QL = quadForm L_sym ↔ QL = d * ...
  exact hQ.symm

/-- Positive semidefiniteness of the regular normalized Laplacian, by
scaling from `laplacian_psd`. -/
theorem regularNormalizedLaplacian_psd (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdpos : 0 < d) :
    ∀ x : V → ℝ, 0 ≤ quadForm (regularNormalizedLaplacian A d) x := by
  intro x
  rw [quadForm_regularNormalizedLaplacian A d hd hdpos.ne' x]
  exact mul_nonneg (inv_nonneg.2 hdpos.le) (laplacian_psd A hA hnonneg x)

/-- Rows of the regular normalized Laplacian sum to zero under
`d`-regularity: `onesVec` is in its kernel,
`L_sym *ᵥ 1 = (1 - d⁻¹ • A) *ᵥ 1 = 1 - d⁻¹ • deg = 0`. -/
theorem regularNormalizedLaplacian_mulVec_onesVec (A : WAdj (V := V))
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdne : d ≠ 0) :
    (regularNormalizedLaplacian A d).mulVec onesVec = 0 := by
  funext i
  have hsum1 : ∑ j, (if i = j then (1 : ℝ) else 0) = 1 := by simp
  have hdeg : d⁻¹ * deg A i = 1 := by
    rw [hd i, inv_mul_cancel₀ hdne]
  simp only [Matrix.mulVec, Matrix.dotProduct, onesVec, mul_one,
    Pi.zero_apply, regularNormalizedLaplacian, Matrix.sub_apply,
    Finset.sum_sub_distrib, Matrix.one_apply, Matrix.smul_apply,
    smul_eq_mul, ← Finset.mul_sum]
  rw [hsum1, show ∑ j, A i j = deg A i from rfl, hdeg, sub_self]

omit [DecidableEq V] in
/-- Under `d`-regularity the volume of a set is `d` times its
cardinality. -/
theorem vol_eq_of_regular (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (S : Finset V) :
    vol A S = d * (S.card : ℝ) := by
  rw [vol, Finset.sum_congr rfl (fun i _ => hd i), Finset.sum_const,
    nsmul_eq_mul]
  ring

omit [DecidableEq V] in
/-- Under `d`-regularity with `0 < d`, every nonempty set has positive
volume. -/
theorem vol_pos_of_regular (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdpos : 0 < d) {S : Finset V}
    (hS : S.Nonempty) : 0 < vol A S := by
  rw [vol_eq_of_regular A d hd S]
  exact mul_pos hdpos (Nat.cast_pos.2 (Finset.card_pos.2 hS))

/-!
### The cut test vector (proved)

The volume-centered indicator of a cut: `x i = vol Sᶜ` on `S` and
`x i = - vol S` off it. This is the test vector of the Cheeger easy
direction (and of sweep-cut arguments generally).
-/

/-- The volume-centered cut indicator: `vol Sᶜ` on `S`, `- vol S` on
`Sᶜ`. Orthogonal to `onesVec` under regularity (both sides of the cut
are balanced in volume); its Dirichlet energy and norm are computed by
the lemmas below. -/
def cutTestVector (A : WAdj (V := V)) (S : Finset V) : V → ℝ :=
  fun i => if i ∈ S then vol A Sᶜ else - vol A S

@[simp] theorem cutTestVector_apply (A : WAdj (V := V)) (S : Finset V)
    (i : V) :
    cutTestVector A S i = if i ∈ S then vol A Sᶜ else - vol A S := rfl

/-- Under regularity the cut test vector is orthogonal to `onesVec`:
`|S| · vol Sᶜ = |Sᶜ| · vol S` because both equal `d · |S| · |Sᶜ|`. -/
theorem cutTestVector_dotProduct_onesVec (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (S : Finset V) :
    Matrix.dotProduct (cutTestVector A S) onesVec = 0 := by
  simp only [Matrix.dotProduct, onesVec, mul_one, cutTestVector_apply]
  rw [← Finset.sum_add_sum_compl S
      (fun i => if i ∈ S then vol A Sᶜ else - vol A S),
    Finset.sum_congr rfl (fun i hi => if_pos hi),
    Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_compl.1 hi)),
    Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul,
    vol_eq_of_regular A d hd S, vol_eq_of_regular A d hd Sᶜ]
  ring

/-- The cut test vector of a nonempty proper cut is nonzero under
regularity with `0 < d`: on `S` it takes the value `vol Sᶜ > 0`. -/
theorem cutTestVector_ne_zero (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdpos : 0 < d) {S : Finset V}
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    cutTestVector A S ≠ 0 := by
  obtain ⟨i, hi⟩ := hS
  intro h
  have h1 : (cutTestVector A S) i = 0 := congrFun h i
  rw [cutTestVector_apply, if_pos hi, vol_eq_of_regular A d hd Sᶜ] at h1
  rw [mul_eq_zero] at h1
  rcases h1 with h | h
  · exact hdpos.ne' h
  · exact hSc.ne_empty (Finset.card_eq_zero.1 (Nat.cast_eq_zero.1 h))

/-- Dirichlet energy of the cut test vector for the *combinatorial*
Laplacian, for arbitrary weighted graphs (no regularity): the energy is
the boundary weight of `S` times the squared total volume. Crossing
pairs contribute `(vol Sᶜ - (-vol S))² = (vol V)²` by `vol_compl`, and
within-side pairs contribute zero; the two crossing halves give
`boundary S + boundary Sᶜ = 2 · boundary S` by `boundary_compl`. -/
theorem quadForm_laplacian_cutTestVector (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (S : Finset V) :
    quadForm (laplacian A) (cutTestVector A S)
      = boundary A S * (vol A (Finset.univ : Finset V)) ^ 2 := by
  classical
  -- the two crossing differences: +vol V (S to Sᶜ) and -vol V (Sᶜ to S)
  have hcross1 : ∀ i j : V, i ∈ S → j ∈ Sᶜ →
      cutTestVector A S i - cutTestVector A S j
        = vol A (Finset.univ : Finset V) := by
    intro i j hi hj
    rw [cutTestVector_apply, cutTestVector_apply, if_pos hi,
      if_neg (Finset.mem_compl.1 hj), sub_neg_eq_add, add_comm,
      vol_compl A S]
  have hcross2 : ∀ i j : V, i ∉ S → j ∈ S →
      cutTestVector A S i - cutTestVector A S j
        = -(vol A (Finset.univ : Finset V)) := by
    intro i j hi hj
    have hneg : -vol A S - vol A Sᶜ = -(vol A S + vol A Sᶜ) := by ring
    rw [cutTestVector_apply, cutTestVector_apply, if_neg hi, if_pos hj,
      hneg, vol_compl A S]
  -- the (i ∈ S, j ∈ Sᶜ) half of the double sum
  have hSS : ∀ i ∈ S, ∑ j, A i j * (cutTestVector A S i
      - cutTestVector A S j) ^ 2
      = ∑ j in Sᶜ, A i j * (vol A (Finset.univ : Finset V)) ^ 2 := by
    intro i hi
    have hvan : ∑ j in S, A i j * (cutTestVector A S i
        - cutTestVector A S j) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have h0 : cutTestVector A S i - cutTestVector A S j = 0 := by
        rw [cutTestVector_apply, cutTestVector_apply, if_pos hi,
          if_pos hj, sub_self]
      rw [h0, zero_pow two_ne_zero, mul_zero]
    rw [← Finset.sum_add_sum_compl S
        (fun j => A i j * (cutTestVector A S i - cutTestVector A S j) ^ 2),
      hvan, zero_add]
    exact Finset.sum_congr rfl fun j hj => by rw [hcross1 i j hi hj]
  -- the (i ∈ Sᶜ, j ∈ S) half of the double sum
  have hScSc : ∀ i ∈ Sᶜ, ∑ j, A i j * (cutTestVector A S i
      - cutTestVector A S j) ^ 2
      = ∑ j in S, A i j * (vol A (Finset.univ : Finset V)) ^ 2 := by
    intro i hi
    have hval : ∀ j ∈ S, A i j * (cutTestVector A S i
        - cutTestVector A S j) ^ 2
        = A i j * (vol A (Finset.univ : Finset V)) ^ 2 := by
      intro j hj
      rw [hcross2 i j (Finset.mem_compl.1 hi) hj, neg_sq]
    have hvan : ∑ j in Sᶜ, A i j * (cutTestVector A S i
        - cutTestVector A S j) ^ 2 = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have h0 : cutTestVector A S i - cutTestVector A S j = 0 := by
        rw [cutTestVector_apply, cutTestVector_apply,
          if_neg (Finset.mem_compl.1 hi),
          if_neg (Finset.mem_compl.1 hj), sub_self]
      rw [h0, zero_pow two_ne_zero, mul_zero]
    rw [← Finset.sum_add_sum_compl S
        (fun j => A i j * (cutTestVector A S i - cutTestVector A S j) ^ 2),
      Finset.sum_congr rfl hval, hvan, add_zero]
  -- pull the squared volume out of both halves
  have hpull : ∀ T U : Finset V,
      ∑ i in T, ∑ j in U, A i j * (vol A (Finset.univ : Finset V)) ^ 2
        = (∑ i in T, ∑ j in U, A i j)
          * (vol A (Finset.univ : Finset V)) ^ 2 := by
    intro T U
    simp only [Finset.sum_mul]
  -- the two remaining double sums are the two boundaries
  have hbd1 : ∑ i in S, ∑ j in Sᶜ, A i j = boundary A S := rfl
  have hbd2 : ∑ i in Sᶜ, ∑ j in S, A i j = boundary A S := by
    rw [show ∑ i in Sᶜ, ∑ j in S, A i j = boundary A Sᶜ from by
      rw [boundary, compl_compl], boundary_compl A hA S]
  rw [laplacian_quadForm A hA,
    ← Finset.sum_add_sum_compl S
      (fun i => ∑ j, A i j * (cutTestVector A S i
        - cutTestVector A S j) ^ 2),
    Finset.sum_congr rfl (fun i hi => hSS i hi),
    Finset.sum_congr rfl (fun i hi => hScSc i hi),
    hpull S Sᶜ, hpull Sᶜ S, hbd1, hbd2]
  ring

/-- Squared norm of the cut test vector under regularity:
`‖x‖² = |S| · vol Sᶜ² + |Sᶜ| · vol S² = vol S · vol Sᶜ · vol V / d`,
substituting `|T| = vol T / d`. -/
theorem dotProduct_cutTestVector_self (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdne : d ≠ 0) (S : Finset V) :
    Matrix.dotProduct (cutTestVector A S) (cutTestVector A S)
      = vol A S * vol A Sᶜ * vol A (Finset.univ : Finset V) / d := by
  classical
  have hvS : vol A S = d * (S.card : ℝ) := vol_eq_of_regular A d hd S
  have hvSc : vol A Sᶜ = d * (Sᶜ.card : ℝ) :=
    vol_eq_of_regular A d hd Sᶜ
  have hcS : (S.card : ℝ) = vol A S / d := by
    rw [hvS, mul_div_cancel_left₀ _ hdne]
  have hcSc : (Sᶜ.card : ℝ) = vol A Sᶜ / d := by
    rw [hvSc, mul_div_cancel_left₀ _ hdne]
  simp only [Matrix.dotProduct, cutTestVector_apply]
  rw [← Finset.sum_add_sum_compl S
      (fun i => (if i ∈ S then vol A Sᶜ else - vol A S)
        * (if i ∈ S then vol A Sᶜ else - vol A S)),
    show ∑ i in S, (if i ∈ S then vol A Sᶜ else - vol A S)
        * (if i ∈ S then vol A Sᶜ else - vol A S)
      = ∑ i in S, vol A Sᶜ * vol A Sᶜ from
        Finset.sum_congr rfl fun i hi => by rw [if_pos hi],
    Finset.sum_const, nsmul_eq_mul,
    show ∑ i in Sᶜ, (if i ∈ S then vol A Sᶜ else - vol A S)
        * (if i ∈ S then vol A Sᶜ else - vol A S)
      = ∑ i in Sᶜ, (- vol A S) * (- vol A S) from
        Finset.sum_congr rfl fun i hi => by
          rw [if_neg (Finset.mem_compl.1 hi)],
    Finset.sum_const, nsmul_eq_mul, hcS, hcSc, ← vol_compl A S]
  field_simp
  ring

/-- Rayleigh quotient of the regular normalized Laplacian at the cut
test vector, in cut terms: `R(x) = boundary · vol V / (vol S · vol Sᶜ)`
— the scaling `d⁻¹` from the quadratic form cancels against the `d` in
the volume-cardinality substitution for the norm. -/
theorem rayleigh_regularNormalizedLaplacian_cutTestVector
    (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d) {S : Finset V}
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    rayleigh (regularNormalizedLaplacian A d) (cutTestVector A S)
      = boundary A S * vol A (Finset.univ : Finset V)
          / (vol A S * vol A Sᶜ) := by
  have hex : ∃ i₀ : V, i₀ ∈ S := hS
  obtain ⟨i₀, -⟩ := hex
  have hne := cutTestVector_ne_zero A d hd hdpos hS hSc
  have hvs := vol_pos_of_regular A d hd hdpos hS
  have hvsc := vol_pos_of_regular A d hd hdpos hSc
  have hvV : 0 < vol A (Finset.univ : Finset V) :=
    vol_pos_of_regular A d hd hdpos ⟨i₀, Finset.mem_univ i₀⟩
  have hd0 : d ≠ 0 := hdpos.ne'
  rw [rayleigh, if_neg hne,
    quadForm_regularNormalizedLaplacian A d hd hd0 (cutTestVector A S),
    quadForm_laplacian_cutTestVector A hA S,
    dotProduct_cutTestVector_self A d hd hd0 S]
  field_simp
  ring

/-- Cheeger upper bound for `d`-regular graphs: the second-smallest
normalized Laplacian eigenvalue controls the conductance from above,
`λ₂(L_sym) ≤ 2 φ(G)`.

Source (classical background; this is a proof, not an admission):
- Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997,
  Chapter 2 (the `λ ≤ 2φ` half of the eigenvalue–conductance
  relationship; the easy direction).

Statement differences: restricted to `d`-regular graphs with positive
degree `d`; `cheegerConstant` is the infimum of the volume-based
conductance over nonempty proper vertex subsets. The spectral side is
the corrected 2026-08-18 shape `secondEval (L_sym)`.

Retirement (2026-08-18): previously admitted as an axiom; now proved
from `secondEval_variational` (the general-operator Courant–Fischer,
through `secondEval_le_rayleigh` at the volume-centered cut indicator
`cutTestVector`), with no admitted dependencies — the explicit axiom
count drops 17 → 16. This is the *easy* direction of Cheeger: a
test-vector argument. The remaining Cheeger axiom
(`cheeger_lower_bound`, `φ²/2 ≤ λ₂`) is the hard direction.

Route: for each nonempty proper `S`, the volume-centered indicator is
orthogonal to `onesVec` (`cutTestVector_dotProduct_onesVec`), so the
variational characterization bounds `λ₂` by its Rayleigh quotient
`boundary · vol V / (vol S · vol Sᶜ)`
(`rayleigh_regularNormalizedLaplacian_cutTestVector`); since
`min ≤ vol S, vol Sᶜ`, that quotient is at most `2 · boundary / min`,
which is `2 · conductance S`. The per-cut bound passes to the infimum
over all nonempty proper cuts (`le_csInf`; the cut set is nonempty
because `2 ≤ card V`).

QA: exercised by `SpectralGraphTheory.QA.cheeger_bounds_coherent_QA`
and `SpectralGraphTheory.QA.cheeger_bounds_edge_QA` in
`Scaffold/QA/SpectralGraph/Cheeger_QA.lean` (the edge instantiation now
exercises a proved theorem), and by the new computed test-vector
witnesses there (`cutTestVector_edge_QA`,
`cheeger_upper_bound_edge_eq_QA`,
`cheeger_upper_bound_cycle_le_QA`). -/
theorem cheeger_upper_bound (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) :
    secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard ≤
      2 * cheegerConstant A := by
  classical
  have hLsym := regularNormalizedLaplacian_symmetric A hA d
  -- the per-cut bound: λ₂ ≤ 2 · conductance S for every nonempty proper S
  have hcut : ∀ S : Finset V, S.Nonempty → Sᶜ.Nonempty →
      secondEval (regularNormalizedLaplacian A d) hLsym hcard
        ≤ 2 * conductance A S := by
    intro S hS hSc
    have hvs := vol_pos_of_regular A d hd hdpos hS
    have hvsc := vol_pos_of_regular A d hd hdpos hSc
    have hex : ∃ i₀ : V, i₀ ∈ S := hS
    obtain ⟨i₀, -⟩ := hex
    have hvV : 0 < vol A (Finset.univ : Finset V) :=
      vol_pos_of_regular A d hd hdpos ⟨i₀, Finset.mem_univ i₀⟩
    -- λ₂ ≤ R(cut test vector) = boundary · vol V / (vol S · vol Sᶜ)
    have hle1 := secondEval_le_rayleigh hLsym
      (regularNormalizedLaplacian_psd A hA hnonneg d hd hdpos)
      (regularNormalizedLaplacian_mulVec_onesVec A d hd hdpos.ne') hcard
      (cutTestVector_ne_zero A d hd hdpos hS hSc)
      (cutTestVector_dotProduct_onesVec A d hd S)
    rw [rayleigh_regularNormalizedLaplacian_cutTestVector A hA d hd
      hdpos hS hSc] at hle1
    rcases eq_or_lt_of_le (boundary_nonneg A hnonneg S) with hB0 | hBpos
    · -- zero boundary: both sides vanish
      rw [← hB0] at hle1
      simp only [zero_mul, zero_div] at hle1
      rw [conductance, ← hB0]
      simp
      exact hle1
    · -- min · (vol S + vol Sᶜ) ≤ 2 · vol S · vol Sᶜ, since min ≤ each
      have hkey : min (vol A S) (vol A Sᶜ) * (vol A S + vol A Sᶜ)
          ≤ 2 * vol A S * vol A Sᶜ := by
        have h1 : min (vol A S) (vol A Sᶜ) ≤ vol A S := min_le_left _ _
        have h2 : min (vol A S) (vol A Sᶜ) ≤ vol A Sᶜ := min_le_right _ _
        calc min (vol A S) (vol A Sᶜ) * (vol A S + vol A Sᶜ)
            = min (vol A S) (vol A Sᶜ) * vol A S
              + min (vol A S) (vol A Sᶜ) * vol A Sᶜ := by ring
          _ ≤ vol A Sᶜ * vol A S + vol A S * vol A Sᶜ :=
              add_le_add (mul_le_mul_of_nonneg_right h2 hvs.le)
                (mul_le_mul_of_nonneg_right h1 hvsc.le)
          _ = 2 * vol A S * vol A Sᶜ := by ring
      have hstep : boundary A S * vol A (Finset.univ : Finset V)
          / (vol A S * vol A Sᶜ)
          ≤ 2 * boundary A S / min (vol A S) (vol A Sᶜ) := by
        rw [div_le_div_iff₀ (mul_pos hvs hvsc) (lt_min hvs hvsc),
          ← vol_compl A S]
        calc boundary A S * (vol A S + vol A Sᶜ)
              * min (vol A S) (vol A Sᶜ)
            = boundary A S
              * (min (vol A S) (vol A Sᶜ) * (vol A S + vol A Sᶜ)) := by ring
          _ ≤ boundary A S * (2 * vol A S * vol A Sᶜ) :=
              mul_le_mul_of_nonneg_left hkey hBpos.le
          _ = 2 * boundary A S * (vol A S * vol A Sᶜ) := by ring
      calc secondEval (regularNormalizedLaplacian A d) hLsym hcard
          ≤ boundary A S * vol A (Finset.univ : Finset V)
              / (vol A S * vol A Sᶜ) := hle1
        _ ≤ 2 * boundary A S / min (vol A S) (vol A Sᶜ) := hstep
        _ = 2 * conductance A S := by rw [conductance]; ring
  -- the cut set is nonempty because at least two vertices exist
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v := by
    have h1 : 1 < (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]
      omega
    obtain ⟨a, b, -, -, hab⟩ := Finset.one_lt_card_iff.1 h1
    exact ⟨a, b, hab⟩
  have hsetne : {c : ℝ | ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance A S = c}.Nonempty :=
    ⟨conductance A {u}, ⟨{u}, ⟨u, Finset.mem_singleton.2 rfl⟩,
      ⟨v, by
        simp only [Finset.mem_compl, Finset.mem_singleton]
        exact Ne.symm huv⟩, rfl⟩⟩
  have hdiv : secondEval (regularNormalizedLaplacian A d) hLsym hcard / 2
      ≤ cheegerConstant A := by
    rw [cheegerConstant]
    refine le_csInf hsetne ?_
    rintro c ⟨S, hS, hSc, rfl⟩
    exact (div_le_iff₀ two_pos).2 (by rw [mul_comm]; exact hcut S hS hSc)
  calc secondEval (regularNormalizedLaplacian A d) hLsym hcard
      = 2 * (secondEval (regularNormalizedLaplacian A d) hLsym hcard / 2) := by
        ring
    _ ≤ 2 * cheegerConstant A :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)

end SpectralGraphTheory
