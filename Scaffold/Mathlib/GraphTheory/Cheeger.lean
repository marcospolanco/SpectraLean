import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Analysis.SpecialFunctions.Integrals

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

/-!
### The Cheeger lower bound (hard direction)

`cheeger_lower_bound` — `φ(G)² / 2 ≤ λ₂(L_sym)` on `d`-regular graphs —
was this file's last explicit axiom (admitted 2026-08-18, statement
repaired the same day) and is proved below at the unchanged statement in
the "hard direction Step 1c" section (2026-08-23); the declaration lives
there, after its dependencies.
-/

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

/-!
### The Cheeger hard direction, Step 1a: pure-algebra components (proved)

`proposals/discharge-perturbation-axioms.md` Step 1a (surveyed
2026-08-22): the pure-algebra layers of the hard-direction proof, proved
here with zero new axioms. The remaining components — the co-area core
(Step 1b) and the median/assembly layer (Step 1c) — consume exactly
these interfaces.

Convention: `E'(x) := ∑ i j, A i j * (x i - x j) ^ 2` is the *ordered*
double sum, which is twice the combinatorial energy
(`laplacian_quadForm`). The constant budget of the hard-direction chain
runs through these statements as follows: Component A bounds the squared
weighted total variation of `f ^ 2` by `E'(f) * 4 * ∑ i, deg A i * f i ^ 2`;
the co-area core (1b) will bound it from below by `2 * φ * d * ‖f‖²`;
together they give the per-part bound `φ ^ 2 * d * ‖y‖² ≤ E'(y)`, and
the fused contraction below sums the two median parts *jointly* into
`E'(x)` — the cross-edge slack `(u + v) ^ 2 ≥ u ^ 2 + v ^ 2` is exactly
what pays for carrying both parts, so nothing is lost against the
statement's final `/2`.
-/

omit [DecidableEq V] in
/-- **Step 1a contraction (pointwise).** The two median parts of a
shift by `m`, taken jointly, contract the squared difference. This
*fused* form — rather than two separate 1-Lipschitz contractions summed
afterwards — is what makes the Cheeger constant budget exact: each part
contracts individually, and the cross terms `(u + v) ^ 2 ≥ u ^ 2 + v ^ 2`
absorb the doubling that summing two separate bounds would otherwise
introduce. The translation invariance of the energy is built into the
right-hand side being `(a - b) ^ 2` itself. -/
theorem sq_posPart_sub_add_sq_negPart_sub_le (m a b : ℝ) :
    (max (a - m) 0 - max (b - m) 0) ^ 2
      + (max (m - a) 0 - max (m - b) 0) ^ 2 ≤ (a - b) ^ 2 := by
  rcases le_total m a with ha | ha <;> rcases le_total m b with hb | hb
  · rw [max_eq_left (by linarith), max_eq_left (by linarith),
      max_eq_right (by linarith), max_eq_right (by linarith)]
    have heq : (a - m - (b - m)) ^ 2 + (0 - 0) ^ 2 = (a - b) ^ 2 := by ring
    rw [heq]
  · rw [max_eq_left (by linarith), max_eq_right (by linarith),
      max_eq_right (by linarith), max_eq_left (by linarith)]
    have h1 : (0 : ℝ) ≤ (a - m) * (m - b) :=
      mul_nonneg (by linarith) (by linarith)
    have heq : (a - b) ^ 2 = (a - m - 0) ^ 2 + (0 - (m - b)) ^ 2
      + 2 * (a - m) * (m - b) := by ring
    rw [heq]
    linarith
  · rw [max_eq_right (by linarith), max_eq_left (by linarith),
      max_eq_left (by linarith), max_eq_right (by linarith)]
    have h1 : (0 : ℝ) ≤ (m - a) * (b - m) :=
      mul_nonneg (by linarith) (by linarith)
    have heq : (a - b) ^ 2 = (0 - (b - m)) ^ 2 + (m - a - 0) ^ 2
      + 2 * (m - a) * (b - m) := by ring
    rw [heq]
    linarith
  · rw [max_eq_right (by linarith), max_eq_right (by linarith),
      max_eq_left (by linarith), max_eq_left (by linarith)]
    have heq : (0 - 0) ^ 2 + (m - a - (m - b)) ^ 2 = (a - b) ^ 2 := by ring
    rw [heq]

omit [DecidableEq V] in
/-- **Step 1a contraction, summed.** For nonnegative weights, the two
median parts of `x` (at threshold `m`) carry *jointly* at most the
energy of `x` itself: `E'((x - m)⁺) + E'((x - m)⁻) ≤ E'(x)`. This is
the tight form of the contraction that the hard-direction assembly
consumes; summing two separate partwise bounds would lose the factor
`2` that the statement's `/2` exactly spends. Only nonnegativity of the
weights is used — symmetry is not needed.

QA: instantiated to equality and strict cases on `C₄` in
`SpectralGraphTheory.QA.pair_contraction_cycle_eq_QA` and
`SpectralGraphTheory.QA.pair_contraction_cycle_lt_QA`, with the
nonnegativity hypothesis refuted-on-omission in
`SpectralGraphTheory.QA.pair_contraction_refuted_QA`. -/
theorem sum_edgeWeight_sq_posPart_add_sq_negPart_le (A : WAdj (V := V))
    (hnn : ∀ i j, 0 ≤ A i j) (m : ℝ) (x : V → ℝ) :
    (∑ i, ∑ j, A i j * (max (x i - m) 0 - max (x j - m) 0) ^ 2)
      + (∑ i, ∑ j, A i j * (max (m - x i) 0 - max (m - x j) 0) ^ 2)
      ≤ ∑ i, ∑ j, A i j * (x i - x j) ^ 2 := by
  have hpt : ∀ i j : V,
      A i j * (max (x i - m) 0 - max (x j - m) 0) ^ 2
        + A i j * (max (m - x i) 0 - max (m - x j) 0) ^ 2
      ≤ A i j * (x i - x j) ^ 2 := by
    intro i j
    have h := mul_le_mul_of_nonneg_left
      (sq_posPart_sub_add_sq_negPart_sub_le m (x i) (x j)) (hnn i j)
    rw [mul_add] at h
    exact h
  calc (∑ i, ∑ j, A i j * (max (x i - m) 0 - max (x j - m) 0) ^ 2)
        + ∑ i, ∑ j, A i j * (max (m - x i) 0 - max (m - x j) 0) ^ 2
      = ∑ i, ∑ j, (A i j * (max (x i - m) 0 - max (x j - m) 0) ^ 2
          + A i j * (max (m - x i) 0 - max (m - x j) 0) ^ 2) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib.symm
    _ ≤ ∑ i, ∑ j, A i j * (x i - x j) ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpt i j

omit [DecidableEq V] in
/-- **Component A of the Cheeger hard direction** (the Cauchy–Schwarz
core): the squared `A`-weighted total variation of the squared values is
controlled by the Dirichlet energy times four times the degree-weighted
squared norm,

`(∑ i j, A i j * |f i ^ 2 - f j ^ 2|) ^ 2
  ≤ E'(f) * (4 * ∑ i, deg A i * f i ^ 2)`.

Unconditional in `f` (no sign hypothesis needed). By
Cauchy–Schwarz (`Finset.sum_mul_sq_le_sq_mul_sq`) over the product type
`V × V` with the pointwise factorization
`|a ^ 2 - b ^ 2| = |a - b| * |a + b|`; the second factor's estimate
`(f i + f j) ^ 2 ≤ 2 * f i ^ 2 + 2 * f j ^ 2` needs the *column* sums of
the cross double sum to match `deg`'s row sums, which is why `IsSymm` is
load-bearing here (refuted on asymmetric nonnegative input in QA:
`SpectralGraphTheory.QA.core_sum_abs_sq_sub_sq_asymmetry_refuted_QA`).

QA: pinned on `K₂` (both sides computed raw, the strict inequality
`4 < 8` visible) in `SpectralGraphTheory.QA.core_edge_QA` and
`SpectralGraphTheory.QA.core_edge_strict_QA`. -/
theorem core_sum_abs_sq_sub_sq (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (f : V → ℝ) :
    (∑ i, ∑ j, A i j * |f i ^ 2 - f j ^ 2|) ^ 2
      ≤ (∑ i, ∑ j, A i j * (f i - f j) ^ 2)
        * (4 * ∑ i, deg A i * f i ^ 2) := by
  classical
  have habs : ∀ x : ℝ, |x| * |x| = x * x := fun x => by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg x)]
  have h1 : ∀ p : V × V, Real.sqrt (A p.1 p.2) * Real.sqrt (A p.1 p.2)
      = A p.1 p.2 := fun p => Real.mul_self_sqrt (hnn p.1 p.2)
  -- the pointwise cross identity: √A|Δ| · √A|Σ| = A |f₁² − f₂²|
  have hlhs : ∀ p : V × V, Real.sqrt (A p.1 p.2) * |f p.1 - f p.2|
      * (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|)
      = A p.1 p.2 * |f p.1 ^ 2 - f p.2 ^ 2| := by
    intro p
    rw [mul_mul_mul_comm, h1 p, ← abs_mul]
    have hring : (f p.1 - f p.2) * (f p.1 + f p.2)
        = f p.1 ^ 2 - f p.2 ^ 2 := by ring
    rw [hring]
  -- Cauchy–Schwarz over the product type, restated at the target shape
  have hcs : (∑ p : V × V, A p.1 p.2 * |f p.1 ^ 2 - f p.2 ^ 2|) ^ 2
      ≤ (∑ p : V × V, (Real.sqrt (A p.1 p.2) * |f p.1 - f p.2|) ^ 2)
        * ∑ p : V × V, (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (V × V))
      (fun p => Real.sqrt (A p.1 p.2) * |f p.1 - f p.2|)
      (fun p => Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|)
    simp only [hlhs] at h
    exact h
  -- first factor: exactly the Dirichlet double sum
  have hF2 : ∑ p : V × V, (Real.sqrt (A p.1 p.2) * |f p.1 - f p.2|) ^ 2
      = ∑ i, ∑ j, A i j * (f i - f j) ^ 2 := by
    rw [← Fintype.sum_prod_type' (fun i j => A i j * (f i - f j) ^ 2)]
    refine Finset.sum_congr rfl fun p _ => ?_
    calc (Real.sqrt (A p.1 p.2) * |f p.1 - f p.2|) ^ 2
        = (Real.sqrt (A p.1 p.2) * |f p.1 - f p.2|)
            * (Real.sqrt (A p.1 p.2) * |f p.1 - f p.2|) := by rw [pow_two]
      _ = A p.1 p.2 * (f p.1 - f p.2) ^ 2 := by
          rw [mul_mul_mul_comm, h1 p, habs, pow_two]
  -- second factor: pointwise AM-GM, then the two degree sums (symmetry
  -- load-bearing on the column side)
  have hG2 : ∑ p : V × V, (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|) ^ 2
      ≤ 4 * ∑ i, deg A i * f i ^ 2 := by
    have hpt : ∀ p : V × V,
        (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|) ^ 2
          ≤ A p.1 p.2 * (2 * f p.1 ^ 2 + 2 * f p.2 ^ 2) := by
      intro p
      have ham : (f p.1 + f p.2) ^ 2 ≤ 2 * f p.1 ^ 2 + 2 * f p.2 ^ 2 := by
        nlinarith [sq_nonneg (f p.1 - f p.2)]
      have heq : (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|) ^ 2
          = A p.1 p.2 * (f p.1 + f p.2) ^ 2 := by
        rw [pow_two, mul_mul_mul_comm, h1 p, habs, pow_two]
      calc (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|) ^ 2
          = A p.1 p.2 * (f p.1 + f p.2) ^ 2 := heq
        _ ≤ A p.1 p.2 * (2 * f p.1 ^ 2 + 2 * f p.2 ^ 2) :=
            mul_le_mul_of_nonneg_left ham (hnn p.1 p.2)
    have hsplit : ∑ p : V × V, A p.1 p.2 * (2 * f p.1 ^ 2 + 2 * f p.2 ^ 2)
        = 2 * ∑ p : V × V, A p.1 p.2 * f p.1 ^ 2
          + 2 * ∑ p : V × V, A p.1 p.2 * f p.2 ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    have hrow : ∑ p : V × V, A p.1 p.2 * f p.1 ^ 2
        = ∑ i, deg A i * f i ^ 2 := by
      rw [Fintype.sum_prod_type' (fun i j => A i j * f i ^ 2)]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_mul]; rfl
    have hcol : ∑ p : V × V, A p.1 p.2 * f p.2 ^ 2
        = ∑ i, deg A i * f i ^ 2 := by
      rw [Fintype.sum_prod_type' (fun i j => A i j * f j ^ 2), Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_mul]
      have hsym : ∑ i, A i j = deg A j :=
        Finset.sum_congr rfl fun i _ => hA.apply j i
      rw [hsym]
    calc ∑ p : V × V, (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|) ^ 2
        ≤ ∑ p : V × V, A p.1 p.2 * (2 * f p.1 ^ 2 + 2 * f p.2 ^ 2) :=
          Finset.sum_le_sum fun p _ => hpt p
      _ = 4 * ∑ i, deg A i * f i ^ 2 := by rw [hsplit, hrow, hcol]; ring
  -- final assembly on the double-sum goal
  have hAbs2 : ∑ i, ∑ j, A i j * |f i ^ 2 - f j ^ 2|
      = ∑ p : V × V, A p.1 p.2 * |f p.1 ^ 2 - f p.2 ^ 2| :=
    (Fintype.sum_prod_type' (fun i j => A i j * |f i ^ 2 - f j ^ 2|)).symm
  have hDir2 : ∑ i, ∑ j, A i j * (f i - f j) ^ 2
      = ∑ p : V × V, A p.1 p.2 * (f p.1 - f p.2) ^ 2 :=
    (Fintype.sum_prod_type' (fun i j => A i j * (f i - f j) ^ 2)).symm
  rw [hAbs2, hDir2]
  calc (∑ p : V × V, A p.1 p.2 * |f p.1 ^ 2 - f p.2 ^ 2|) ^ 2
      ≤ (∑ p : V × V, (Real.sqrt (A p.1 p.2) * |f p.1 - f p.2|) ^ 2)
        * ∑ p : V × V, (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|) ^ 2 := hcs
    _ = (∑ p : V × V, A p.1 p.2 * (f p.1 - f p.2) ^ 2)
        * ∑ p : V × V, (Real.sqrt (A p.1 p.2) * |f p.1 + f p.2|) ^ 2 := by
        rw [hF2, hDir2]
    _ ≤ (∑ p : V × V, A p.1 p.2 * (f p.1 - f p.2) ^ 2)
        * (4 * ∑ i, deg A i * f i ^ 2) :=
        mul_le_mul_of_nonneg_left hG2 (Finset.sum_nonneg fun p _ =>
          mul_nonneg (hnn p.1 p.2) (sq_nonneg _))

omit [DecidableEq V] in
/-- Under `d`-regularity the degree-weighted squared norm collapses to
`d` times the plain squared norm — the bridge between Component A's
second factor `4 * ∑ i, deg A i * f i ^ 2` and the `4 * d * ‖f‖²` form
the hard-direction chain combines it into. -/
theorem sum_deg_mul_eq_of_regular (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (f : V → ℝ) :
    ∑ i, deg A i * f i ^ 2 = d * ∑ i, f i ^ 2 := by
  calc ∑ i, deg A i * f i ^ 2
      = ∑ i, d * f i ^ 2 := Finset.sum_congr rfl fun i _ => by rw [hd i]
    _ = d * ∑ i, f i ^ 2 := (Finset.mul_sum Finset.univ (fun i => f i ^ 2) d).symm

/-- **Step 1a normalization.** The Rayleigh quotient of the regular
normalized Laplacian, expressed through the ordered Dirichlet double
sum `E'(x) := ∑ i j, A i j * (x i - x j) ^ 2`: since
`quadForm (laplacian A) x = E'(x) / 2` (`laplacian_quadForm`) and
`quadForm (L_sym) x = d⁻¹ * quadForm (laplacian A) x`, the quotient is
`R(x) = E'(x) / (2 * d * ‖x‖²)`. The explicit `2` in the denominator is
the constant budget of the hard-direction chain: the per-part bound
`φ ^ 2 * d * ‖y‖² ≤ E'(y)` sums (through
`sum_edgeWeight_sq_posPart_add_sq_negPart_le`) to
`φ ^ 2 * d * ‖x‖² ≤ E'(x) = 2 * d * R(x) * ‖x‖²`, i.e.
`φ ^ 2 / 2 ≤ R(x)` — the sweep lemma, with nothing lost anywhere.

QA: cross-checked on `K₂` against the independently pinned values
`λ₂(L_sym) = 2` and the cut test vector's Rayleigh quotient in
`SpectralGraphTheory.QA.rayleigh_regularNormalizedLaplacian_edge_eq_QA`. -/
theorem rayleigh_regularNormalizedLaplacian_eq (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (d : ℝ) (hd : ∀ i, deg A i = d) (hdne : d ≠ 0)
    {x : V → ℝ} (hx : x ≠ 0) :
    rayleigh (regularNormalizedLaplacian A d) x
      = (∑ i, ∑ j, A i j * (x i - x j) ^ 2)
          / (2 * d * Matrix.dotProduct x x) := by
  have hdot : Matrix.dotProduct x x ≠ 0 := by
    intro h
    apply hx
    funext i
    have hsum : ∑ j, x j * x j = 0 := by
      simpa [Matrix.dotProduct] using h
    have hmem := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (x j))).1 hsum i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hmem
  rw [rayleigh, if_neg hx, quadForm_regularNormalizedLaplacian A d hd hdne,
    laplacian_quadForm A hA, ← div_div]
  simp only [div_eq_mul_inv]
  ring

/-!
### The Cheeger hard direction, Step 1b: the co-area core (proved)

`proposals/discharge-perturbation-axioms.md` Step 1b (surveyed
2026-08-22): the co-area layer of the hard-direction proof, proved here
with zero new axioms. For a vector whose nonempty closed superlevel sets
are all minority-side, the weighted total variation of the squared
values dominates `2 * φ * d` times the squared norm — the lower
complement of Component A above; composed with it (Step 1c) this yields
the per-part bound `φ ^ 2 * d * ‖y‖ ^ 2 ≤ E'(y)`.

Survey correction (2026-08-23, found by the Step-1b spike): the priced
hand Finset-induction Fubini is unnecessary — the pin *has* a
finite-sum ↔ interval-integral interchange, `intervalIntegral.
integral_finset_sum` (the survey searched for the name
`integral_sum`), together with `IntervalIntegrable.sum`, `.abs`, and
`integral_mono_ae_restrict`. The `Iic`-indicator encoding below — chosen
to match `intervalIntegral.integral_indicator`'s own truncation shape —
also dissolves the survey's `Ι = Ioc` right-endpoint drop-point trap:
every congruence in the chain is pointwise.

Statement-shape notes (both are hypothesis *drops* relative to the
survey's sketch): no `hynonneg : ∀ i, 0 ≤ y i` — the whole chain runs
on `y i ^ 2`, nonnegative automatically, so the theorem holds for
arbitrary `y : V → ℝ`; and no `hcard : 2 ≤ Fintype.card V` — minority
`2 * |S| ≤ n` already forces `Sᶜ` nonempty whenever `S` is (`|Sᶜ| ≥
|S| ≥ 1`), which is all the conductance step needs.
-/

section Step1b

open MeasureTheory intervalIntegral

/-- The closed cumulative level step `1_{t ≤ c}`. Layer-cake primitive
of the co-area encoding; stated through `Set.indicator` on `{x | x ≤ c}`
to match `intervalIntegral.integral_indicator` exactly. -/
noncomputable def indicatorLE (c t : ℝ) : ℝ :=
  Set.indicator {x : ℝ | x ≤ c} (fun _ => 1) t

theorem indicatorLE_of_le {c t : ℝ} (h : t ≤ c) : indicatorLE c t = 1 :=
  Set.indicator_of_mem (show t ∈ {x : ℝ | x ≤ c} by exact h) _

theorem indicatorLE_of_lt {c t : ℝ} (h : c < t) : indicatorLE c t = 0 :=
  Set.indicator_of_not_mem (show t ∉ {x : ℝ | x ≤ c} by exact not_le.2 h) _

theorem indicatorLE_mono (c d t : ℝ) (hcd : c ≤ d) :
    indicatorLE c t ≤ indicatorLE d t := by
  by_cases h1 : t ≤ c
  · rw [indicatorLE_of_le h1, indicatorLE_of_le (h1.trans hcd)]
  · have hc : c < t := not_le.1 h1
    rw [indicatorLE_of_lt hc]
    by_cases h2 : t ≤ d
    · have h3 := indicatorLE_of_le h2; simp [h3]
    · have h3 := indicatorLE_of_lt (not_le.1 h2); simp [h3]

/-- The level step is interval-integrable on every interval: it is the
indicator of a measurable set, bounded, on a finite-measure interval. -/
theorem intervalIntegrable_indicatorLE (c a b : ℝ) :
    IntervalIntegrable (indicatorLE c) volume a b := by
  rw [intervalIntegrable_iff]
  refine ((integrableOn_const (C := (1 : ℝ)) (μ := volume)).mpr ?_).indicator
    (measurableSet_Iic (a := c))
  right
  rcases le_total a b with hab | hab
  · rw [Set.uIoc_of_le hab, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  · rw [Set.uIoc_of_ge hab, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top

/-- A constant multiple of an interval-integrable function is
interval-integrable (small helper; the pin's `IntervalIntegrable`
API has no `const_mul`). -/
theorem intervalIntegrable_const_mul {f : ℝ → ℝ} {a b : ℝ} (k : ℝ)
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => k * f t) volume a b := by
  rw [intervalIntegrable_iff] at hf ⊢
  exact hf.const_mul k

/-- **Mass layer-cake.** The closed level step integrates to its
threshold: `∫ t in 0..R, 1_{t ≤ c} = c` for `0 ≤ c ≤ R`. Direct from
`intervalIntegral.integral_indicator` (whose truncation shape the
indicator matches exactly) and `integral_const`. -/
theorem integral_indicatorLE {c R : ℝ} (h1 : 0 ≤ c) (h2 : c ≤ R) :
    ∫ t in (0:ℝ)..R, indicatorLE c t = c := by
  have h := intervalIntegral.integral_indicator (μ := volume)
    (f := fun _ => (1 : ℝ))
    (show c ∈ Set.Icc 0 R from ⟨h1, h2⟩)
  simp only [indicatorLE] at h ⊢
  rw [h, intervalIntegral.integral_const]
  simp

/-- **Pair layer-cake.** The total variation of the two level steps
integrates to the absolute value gap: for `0 ≤ c, d` with `max c d ≤ R`,
`∫ t in 0..R, |1_{t ≤ c} − 1_{t ≤ d}| = |c − d|`. Pointwise
monotonicity of the steps resolves the absolute value by cases, then
two mass layer-cakes close each case. -/
theorem integral_abs_indicatorLE_sub {c d R : ℝ} (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hR : max c d ≤ R) :
    ∫ t in (0:ℝ)..R, |indicatorLE c t - indicatorLE d t| = |c - d| := by
  have hRc : c ≤ R := le_trans (le_max_left c d) hR
  have hRd : d ≤ R := le_trans (le_max_right c d) hR
  rcases le_total c d with h | h
  · have hpt : ∀ t : ℝ,
        |indicatorLE c t - indicatorLE d t|
          = indicatorLE d t - indicatorLE c t := by
      intro t
      have hle := indicatorLE_mono c d t h
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [intervalIntegral.integral_congr (fun t _ => hpt t),
      intervalIntegral.integral_sub (intervalIntegrable_indicatorLE d 0 R)
        (intervalIntegrable_indicatorLE c 0 R),
      integral_indicatorLE hd hRd, integral_indicatorLE hc hRc]
    rw [abs_of_nonpos (by linarith : c - d ≤ 0)]
    ring
  · have hpt : ∀ t : ℝ,
        |indicatorLE c t - indicatorLE d t|
          = indicatorLE c t - indicatorLE d t := by
      intro t
      have hle := indicatorLE_mono d c t h
      rw [abs_of_nonneg (by linarith)]
    rw [intervalIntegral.integral_congr (fun t _ => hpt t),
      intervalIntegral.integral_sub (intervalIntegrable_indicatorLE c 0 R)
        (intervalIntegrable_indicatorLE d 0 R),
      integral_indicatorLE hc hRc, integral_indicatorLE hd hRd]
    rw [abs_of_nonneg (by linarith : 0 ≤ c - d)]

omit [DecidableEq V] in
/-- The indicator↔cardinality dictionary: the sum of the level
indicators is the size of the closed level set `{i : t ≤ g i}`. -/
theorem sum_indicatorLE_eq_card_filter (g : V → ℝ) (t : ℝ) :
    ∑ i, indicatorLE (g i) t
      = ((Finset.univ.filter (fun i => t ≤ g i)).card : ℝ) := by
  classical
  have h1 : ∀ i : V, indicatorLE (g i) t
      = ↑(if t ≤ g i then (1 : ℕ) else 0) := by
    intro i
    by_cases h : t ≤ g i
    · rw [indicatorLE_of_le h, if_pos h]; norm_num
    · rw [indicatorLE_of_lt (not_le.1 h), if_neg h]; norm_num
  rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Nat.cast_sum,
    ← Finset.sum_filter, Finset.sum_const]
  simp

/-- **Per-level cut identity.** For any threshold `t`, the
`A`-weighted total variation of the level indicators is twice the edge
boundary of the closed level set `S = {i : t ≤ y i ^ 2}` — crossing
pairs contribute `1` in each direction, and the two directions are the
two boundaries, equal by symmetry (`boundary_compl`). -/
theorem sum_pairAbs_eq_two_boundary (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (y : V → ℝ) (t : ℝ) (S : Finset V) (hS : ∀ i, i ∈ S ↔ t ≤ y i ^ 2) :
    ∑ i, ∑ j, A i j * |indicatorLE (y i ^ 2) t - indicatorLE (y j ^ 2) t|
      = 2 * boundary A S := by
  have hin : ∀ i ∈ S, indicatorLE (y i ^ 2) t = 1 := fun i hi =>
    indicatorLE_of_le ((hS i).1 hi)
  have hout : ∀ i ∉ S, indicatorLE (y i ^ 2) t = 0 := by
    intro i hi
    refine indicatorLE_of_lt ?_
    by_contra hcon
    exact hi ((hS i).2 (not_lt.1 hcon))
  have hSS : ∀ i ∈ S, ∑ j, A i j * |indicatorLE (y i ^ 2) t
        - indicatorLE (y j ^ 2) t| = ∑ j in Sᶜ, A i j := by
    intro i hi
    rw [← Finset.sum_add_sum_compl S (fun j => A i j
      * |indicatorLE (y i ^ 2) t - indicatorLE (y j ^ 2) t|)]
    have h1 : ∑ j in S, A i j * |indicatorLE (y i ^ 2) t
        - indicatorLE (y j ^ 2) t| = 0 :=
      Finset.sum_eq_zero fun j hj => by simp [hin i hi, hin j hj]
    rw [h1, zero_add]
    have hcongr1 : ∀ j ∈ Sᶜ, A i j * |indicatorLE (y i ^ 2) t
        - indicatorLE (y j ^ 2) t| = A i j := by
      intro j hj
      simp [hin i hi, hout j (Finset.mem_compl.1 hj)]
    exact Finset.sum_congr rfl hcongr1
  have hScSc : ∀ i ∈ Sᶜ, ∑ j, A i j * |indicatorLE (y i ^ 2) t
        - indicatorLE (y j ^ 2) t| = ∑ j in S, A i j := by
    intro i hi
    rw [← Finset.sum_add_sum_compl S (fun j => A i j
      * |indicatorLE (y i ^ 2) t - indicatorLE (y j ^ 2) t|)]
    have h2 : ∑ j in Sᶜ, A i j * |indicatorLE (y i ^ 2) t
        - indicatorLE (y j ^ 2) t| = 0 :=
      Finset.sum_eq_zero fun j hj => by
        simp [hout i (Finset.mem_compl.1 hi), hout j (Finset.mem_compl.1 hj)]
    have hcongr2 : ∀ j ∈ S, A i j * |indicatorLE (y i ^ 2) t
        - indicatorLE (y j ^ 2) t| = A i j := by
      intro j hj
      simp [hout i (Finset.mem_compl.1 hi), hin j hj]
    rw [Finset.sum_congr rfl hcongr2, h2, add_zero]
  have hbd1 : ∑ i ∈ S, ∑ j ∈ Sᶜ, A i j = boundary A S := rfl
  rw [← Finset.sum_add_sum_compl S (fun i => ∑ j, A i j
      * |indicatorLE (y i ^ 2) t - indicatorLE (y j ^ 2) t|),
    Finset.sum_congr rfl (fun i hi => hSS i hi),
    Finset.sum_congr rfl (fun i hi => hScSc i hi), hbd1,
    show ∑ i ∈ Sᶜ, ∑ j ∈ S, A i j = boundary A Sᶜ from by
      simp only [boundary, compl_compl],
    boundary_compl A hA S]
  ring

/-- **Minority conductance.** On a `d`-regular graph with `0 < d`, a
nonempty set occupying at most half the vertices has boundary at least
`φ * d * |S|`: its conductance bounds the Cheeger constant from below,
and minority makes `S`'s volume the smaller side. -/
theorem boundary_ge_of_minority (A : WAdj (V := V)) (hnn : ∀ i j, 0 ≤ A i j)
    (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d) {S : Finset V}
    (hS : S.Nonempty) (hcard : 2 * S.card ≤ Fintype.card V) :
    cheegerConstant A * d * (S.card : ℝ) ≤ boundary A S := by
  have hc := Finset.card_add_card_compl S
  have h0 : 0 < S.card := Finset.card_pos.2 hS
  have hcardle : S.card ≤ Sᶜ.card := by omega
  obtain ⟨j, hj⟩ := Finset.card_pos.1 (by omega : 0 < Sᶜ.card)
  have hφ := conductance_ge_cheegerConstant A hnn S hS ⟨j, hj⟩
  have hmin : min (vol A S) (vol A Sᶜ) = d * (S.card : ℝ) := by
    rw [vol_eq_of_regular A d hd S, vol_eq_of_regular A d hd Sᶜ,
      min_eq_left (mul_le_mul_of_nonneg_left (by exact_mod_cast hcardle) hdpos.le)]
  have hcond : conductance A S = boundary A S / min (vol A S) (vol A Sᶜ) := rfl
  rw [hcond, hmin] at hφ
  have hkey := (le_div_iff₀ (by positivity : 0 < d * (S.card : ℝ))).1 hφ
  linarith

/-- **The per-level co-area bound.** At every positive level `t`, twice
the minority conductance bound bounds the weighted total variation of
the level indicators: the closed level set's cardinality enters through
`sum_indicatorLE_eq_card_filter`, and the cut identity plus minority
conductance close the chain. -/
theorem sum_pairAbs_ge (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (y : V → ℝ) (hy : ∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ y i ^ 2)).card ≤ Fintype.card V)
    (t : ℝ) (ht : 0 < t) :
    2 * (cheegerConstant A * d
        * ((Finset.univ.filter (fun i => t ≤ y i ^ 2)).card : ℝ))
      ≤ ∑ i, ∑ j, A i j * |indicatorLE (y i ^ 2) t - indicatorLE (y j ^ 2) t| := by
  have hSm : ∀ i, i ∈ Finset.univ.filter (fun i => t ≤ y i ^ 2) ↔ t ≤ y i ^ 2 := by
    intro i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [sum_pairAbs_eq_two_boundary A hA y t _ hSm]
  rcases (Finset.univ.filter (fun i => t ≤ y i ^ 2)).eq_empty_or_nonempty
    with hE | hNE
  · rw [hE]
    have hb0 : boundary A (∅ : Finset V) = 0 := by simp [boundary]
    rw [hb0]
    simp
  · have hbd := boundary_ge_of_minority A hnn d hd hdpos hNE (hy t ht)
    linarith

/-- **The co-area core of the Cheeger hard direction** (Step 1b; the
`1b` component of `proposals/discharge-perturbation-axioms.md`): for any
`y : V → ℝ` whose nonempty closed superlevel sets `{i : t ≤ y i ^ 2}`
(`0 < t`) are all minority-side (`2 * |S_t| ≤ Fintype.card V`),

`2 * (φ * d * ∑ i, y i ^ 2) ≤ ∑ i j, A i j * |y i ^ 2 - y j ^ 2|`.

Composed with Component A (`core_sum_abs_sq_sub_sq`, whose upper bound
carries the same total-variation quantity) this yields the per-part
bound `φ ^ 2 * d * ‖y‖ ^ 2 ≤ E'(y)` of the hard-direction chain — the
input Step 1c consumes through the Step-1a fused contraction and the
`E' / (2 * d * ‖x‖ ^ 2)` normalization.

Route: both sides are layer-cake integrals over `[0, R]` for any
`R ≥ max_i y i ^ 2` (mass: `integral_indicatorLE`; pair:
`integral_abs_indicatorLE_sub`; interchange by
`intervalIntegral.integral_finset_sum` over the product type), and the
integrand inequality holds at every level `t > 0` by the per-level
bound above; `t = 0` is the single failure point of the integrand
inequality and is absorbed measure-theoretically
(`integral_mono_ae_restrict`; Lebesgue has no atoms).

Statement-shape guards: the minority hypothesis is stated on *closed*
superlevel sets at positive levels only — at `t = 0` the closed set is
all of `V` for every `y`, so a `t ≥ 0` reading would be unsatisfiable;
and `2 ≤ Fintype.card V` is *not* assumed (see the section header).

QA: the `K₂` equality pin (both sides `2`), the strict multi-level `C₄`
witness, the indicator↔cardinality dictionary pin, and the
minority-hypothesis refutation-on-omission live in
`Scaffold/QA/SpectralGraph/Cheeger_QA.lean` (`coarea_edge_eq_QA`,
`coarea_cycle_lt_QA`, `sum_indicatorLE_edge_QA`,
`coarea_minority_refuted_QA`). -/
theorem coarea_core (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (y : V → ℝ) (hy : ∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ y i ^ 2)).card ≤ Fintype.card V) :
    2 * (cheegerConstant A * d * ∑ i, y i ^ 2)
      ≤ ∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2| := by
  classical
  have hy2 : ∀ i, 0 ≤ y i ^ 2 := fun i => sq_nonneg _
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i, y i ^ 2 + 1 := ⟨_, rfl⟩
  have hRpos : 0 ≤ R := by
    rw [hRdef]
    have hsumnn : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => hy2 i
    linarith
  have hcR : ∀ i, y i ^ 2 ≤ R := by
    intro i
    have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hy2 i)
      (Finset.mem_univ i)
    rw [hRdef]
    linarith
  -- integrability of both mono sides
  have hintL : IntervalIntegrable (fun t =>
      (2 * (cheegerConstant A * d)) * ∑ i, indicatorLE (y i ^ 2) t) volume 0 R := by
    have hsum : IntervalIntegrable
        (fun t => ∑ i, indicatorLE (y i ^ 2) t) volume 0 R := by
      have h := IntervalIntegrable.sum (Finset.univ : Finset V)
        (f := fun i t => indicatorLE (y i ^ 2) t)
        (fun i _ => intervalIntegrable_indicatorLE (y i ^ 2) 0 R)
      have hfun : (fun t => ∑ i, indicatorLE (y i ^ 2) t)
          = ∑ i : V, (fun t => indicatorLE (y i ^ 2) t) := by
        funext t
        rw [Finset.sum_apply]
      rw [hfun]
      exact h
    exact intervalIntegrable_const_mul _ hsum
  have hintR : IntervalIntegrable (fun t => ∑ p : V × V,
      A p.1 p.2 * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|)
      volume 0 R := by
    have h := IntervalIntegrable.sum (Finset.univ : Finset (V × V))
      (f := fun p t => A p.1 p.2
        * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|)
      (fun p _ => intervalIntegrable_const_mul _
        (((intervalIntegrable_indicatorLE (y p.1 ^ 2) 0 R).sub
          (intervalIntegrable_indicatorLE (y p.2 ^ 2) 0 R)).abs))
    have hfun : (fun t => ∑ p : V × V, A p.1 p.2
        * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|)
        = ∑ p : V × V, (fun t => A p.1 p.2
          * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|) := by
      funext t
      rw [Finset.sum_apply]
    rw [hfun]
    exact h
  -- the mass layer-cake
  have hmass : ∫ t in (0:ℝ)..R, ∑ i, indicatorLE (y i ^ 2) t
      = ∑ i, y i ^ 2 := by
    rw [intervalIntegral.integral_finset_sum
      (fun i _ => intervalIntegrable_indicatorLE (y i ^ 2) 0 R)]
    exact Finset.sum_congr rfl fun i _ => integral_indicatorLE (hy2 i) (hcR i)
  -- the pair layer-cake
  have hint : ∫ t in (0:ℝ)..R, ∑ p : V × V, A p.1 p.2
        * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|
      = ∑ p : V × V, ∫ t in (0:ℝ)..R, A p.1 p.2
        * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t| :=
    intervalIntegral.integral_finset_sum
      (fun p _ => intervalIntegrable_const_mul _
        (((intervalIntegrable_indicatorLE (y p.1 ^ 2) 0 R).sub
          (intervalIntegrable_indicatorLE (y p.2 ^ 2) 0 R)).abs))
  have hpair : ∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2|
      = ∫ t in (0:ℝ)..R, ∑ p : V × V, A p.1 p.2
          * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t| := by
    rw [hint, ← Fintype.sum_prod_type'
      (fun i j => A i j * |y i ^ 2 - y j ^ 2|)]
    exact Finset.sum_congr rfl fun p _ => by
      rw [intervalIntegral.integral_const_mul,
        integral_abs_indicatorLE_sub (hy2 p.1) (hy2 p.2)
          (max_le (hcR p.1) (hcR p.2))]
  -- the ae mono (the t = 0 endpoint is the only failure point)
  have hne : {t : ℝ | t ≠ 0} ∈ MeasureTheory.ae volume := by
    rw [MeasureTheory.mem_ae_iff]; simp [Real.volume_singleton]
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 R)),
      (2 * (cheegerConstant A * d)) * ∑ i, indicatorLE (y i ^ 2) t
        ≤ ∑ p : V × V, A p.1 p.2
          * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t| := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hne] with t ht
    intro htI
    have h0t : 0 < t := lt_of_le_of_ne htI.1 (Ne.symm ht)
    have hper := sum_pairAbs_ge A hA hnn d hd hdpos y hy t h0t
    rw [← sum_indicatorLE_eq_card_filter (fun i => y i ^ 2) t] at hper
    rw [← Fintype.sum_prod_type'
      (fun i j => A i j * |indicatorLE (y i ^ 2) t
        - indicatorLE (y j ^ 2) t|)] at hper
    linarith
  calc 2 * (cheegerConstant A * d * ∑ i, y i ^ 2)
      = (2 * (cheegerConstant A * d)) * ∑ i, y i ^ 2 := by ring
    _ = (2 * (cheegerConstant A * d))
        * ∫ t in (0:ℝ)..R, ∑ i, indicatorLE (y i ^ 2) t := by rw [hmass]
    _ = ∫ t in (0:ℝ)..R, (2 * (cheegerConstant A * d))
        * ∑ i, indicatorLE (y i ^ 2) t :=
        (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ ∫ t in (0:ℝ)..R, ∑ p : V × V,
          A p.1 p.2 * |indicatorLE (y p.1 ^ 2) t
            - indicatorLE (y p.2 ^ 2) t| :=
        intervalIntegral.integral_mono_ae_restrict hRpos hintL hintR hae
    _ = ∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2| := hpair.symm

end Step1b

/-!
### The Cheeger hard direction, Step 1c: median + assembly (proved)

`proposals/discharge-perturbation-axioms.md` Step 1c (the final
component): the median split of `x − m·1` into its two nonzero-sign
parts, the per-part bound `φ ^ 2 * d * ‖y‖ ^ 2 ≤ E'(y)` composing the
Step-1b co-area core with the Step-1a Cauchy–Schwarz core, the norm
split, the fused contraction, and the assembly into the sweep lemma —
retiring `cheeger_lower_bound` from admitted axiom to proved theorem at
the unchanged statement (explicit axioms 10 → 9; the proposal's program
is thereby complete: Weyl, Davis–Kahan, and both Cheeger directions are
all proved hard crust).

The median here is *any* value splitting the value multiset into two
at-most-half strict sides (`|{x > m}| ≤ n/2` and `|{x < m}| ≤ n/2`); it
exists by pure Finset arithmetic — no sorting: the set
`T := {i : 2·|{j : x i < x j}| ≤ n}` is nonempty at a maximizing vertex,
and a `T`-member of minimal value works, since otherwise the maximizer
inside the (majority) strict lower level set would itself lie in `T`
below the minimum.
-/

section Step1c

omit [DecidableEq V] in
/-- **A median exists on every finite value multiset**: there is `m` with
at most half the values strictly above and at most half strictly below
(`2 * |{m < x i}| ≤ n` and `2 * |{x i < m}| ≤ n`). Route: `T := {i :
2·|{j : x i < x j}| ≤ n}` is nonempty (a maximizing vertex has an empty
strict upper level set); a vertex of `T` with minimal value works —
otherwise the (majority) strict lower level set's maximizer would itself
lie in `T` below the minimum. Pure Finset arithmetic; no sorting.

QA: `SpectralGraphTheory.QA.median_fin4_QA` pins the returned median of
a four-vertex tie-heavy vector into the forced interval `[-1, 1]`. -/
theorem exists_median (x : V → ℝ) :
    ∃ m : ℝ,
      2 * (Finset.univ.filter (fun i => m < x i)).card ≤ Fintype.card V
        ∧ 2 * (Finset.univ.filter (fun i => x i < m)).card
            ≤ Fintype.card V := by
  classical
  rcases isEmpty_or_nonempty V with hEmpty | hNE
  · -- empty vertex type: every level set is empty and `n = 0`
    have hcard0 : Fintype.card V = 0 := Fintype.card_eq_zero
    have huniv : (Finset.univ : Finset V) = ∅ := by
      have : (Finset.univ : Finset V).card = 0 := by
        rw [Finset.card_univ, hcard0]
      exact Finset.card_eq_zero.1 this
    refine ⟨0, ?_, ?_⟩
    · rw [huniv, Finset.filter_empty, Finset.card_empty, hcard0]
    · rw [huniv, Finset.filter_empty, Finset.card_empty, hcard0]
  -- T is nonempty: at a maximizing vertex the strict upper set is empty
  obtain ⟨imax0⟩ := hNE
  obtain ⟨imax, -, himax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset V) x
      ⟨imax0, Finset.mem_univ imax0⟩
  have hempty : (Finset.univ.filter (fun j => x imax < x j)) = ∅ :=
    Finset.filter_eq_empty_iff.2 fun j hj => not_lt.2 (himax j hj)
  have hcardmax : 2 * (Finset.univ.filter (fun j => x imax < x j)).card
      ≤ Fintype.card V := by
    rw [hempty, Finset.card_empty]; omega
  -- take a T-member with minimal value
  obtain ⟨i₀, hi₀, hi₀min⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun i =>
      2 * (Finset.univ.filter (fun j => x i < x j)).card ≤ Fintype.card V))
    x ⟨imax, Finset.mem_filter.2 ⟨Finset.mem_univ imax, hcardmax⟩⟩
  have hi₀cond := (Finset.mem_filter.1 hi₀).2
  refine ⟨x i₀, hi₀cond, ?_⟩
  -- the lower count: by contradiction, the lower level set would be a
  -- majority, and its maximizer would be a T-member below the minimum
  by_contra hcon
  push_neg at hcon
  have hSne : (Finset.univ.filter (fun i => x i < x i₀)).Nonempty := by
    rcases Finset.eq_empty_or_nonempty
      (Finset.univ.filter (fun i => x i < x i₀)) with hE | hNE'
    · rw [hE, Finset.card_empty] at hcon; omega
    · exact hNE'
  obtain ⟨i₁, hi₁S, hi₁max⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun i => x i < x i₀)) x hSne
  have hsub : (Finset.univ.filter (fun j => x i₁ < x j))
      ⊆ (Finset.univ.filter (fun i => x i < x i₀))ᶜ := by
    intro j hj
    rw [Finset.mem_compl]
    by_contra hjlow
    have hup := (Finset.mem_filter.1 hj).2
    have hlow := (Finset.mem_filter.1 hjlow).2
    have hmax := hi₁max j hjlow
    linarith
  have hcardle : 2 * (Finset.univ.filter (fun j => x i₁ < x j)).card
      ≤ Fintype.card V := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_add_card_compl
      (Finset.univ.filter (fun i => x i < x i₀))
    have h3 : (Finset.univ.filter (fun i => x i < x i₀)).card
        ≤ Fintype.card V := by
      rw [← Finset.card_univ (α := V)]
      exact Finset.card_le_univ _
    omega
  have hi₁T : i₁ ∈ Finset.univ.filter (fun i =>
      2 * (Finset.univ.filter (fun j => x i < x j)).card ≤ Fintype.card V) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ i₁, hcardle⟩
  have hmin := hi₀min i₁ hi₁T
  have hlow := (Finset.mem_filter.1 hi₁S).2
  linarith

omit [DecidableEq V] in
/-- The positive part's closed superlevel set at a positive level sits
inside the strict upper level set `{i : m < x i}` — at `t > 0` the level
condition forces `x i - m` strictly positive. -/
theorem posPart_superlevel_subset {x : V → ℝ} {m : ℝ} (t : ℝ) (ht : 0 < t) :
    (Finset.univ.filter (fun i => t ≤ (max (x i - m) 0) ^ 2))
      ⊆ (Finset.univ.filter (fun i => m < x i)) := by
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  by_contra hc
  push_neg at hc
  have hle : max (x i - m) 0 = 0 := max_eq_right (by linarith)
  rw [hle, zero_pow two_ne_zero] at hi
  linarith

omit [DecidableEq V] in
/-- The negative part's closed superlevel set at a positive level sits
inside the strict lower level set `{i : x i < m}`. -/
theorem negPart_superlevel_subset {x : V → ℝ} {m : ℝ} (t : ℝ) (ht : 0 < t) :
    (Finset.univ.filter (fun i => t ≤ (max (m - x i) 0) ^ 2))
      ⊆ (Finset.univ.filter (fun i => x i < m)) := by
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  by_contra hc
  push_neg at hc
  have hle : max (m - x i) 0 = 0 := max_eq_right (by linarith)
  rw [hle, zero_pow two_ne_zero] at hi
  linarith

omit [DecidableEq V] in
/-- The positive part's closed superlevel sets at positive levels are
minority-side, from the median's upper count — exactly `coarea_core`'s
hypothesis, supplied by the median. -/
theorem minority_posPart {x : V → ℝ} {m : ℝ}
    (hup : 2 * (Finset.univ.filter (fun i => m < x i)).card ≤ Fintype.card V)
    (t : ℝ) (ht : 0 < t) :
    2 * (Finset.univ.filter (fun i => t ≤ (max (x i - m) 0) ^ 2)).card
      ≤ Fintype.card V := by
  have h1 : (Finset.univ.filter (fun i => t ≤ (max (x i - m) 0) ^ 2)).card
      ≤ (Finset.univ.filter (fun i => m < x i)).card :=
    Finset.card_le_card (posPart_superlevel_subset t ht)
  omega

omit [DecidableEq V] in
/-- The negative part's closed superlevel sets at positive levels are
minority-side, from the median's lower count. -/
theorem minority_negPart {x : V → ℝ} {m : ℝ}
    (hlow : 2 * (Finset.univ.filter (fun i => x i < m)).card ≤ Fintype.card V)
    (t : ℝ) (ht : 0 < t) :
    2 * (Finset.univ.filter (fun i => t ≤ (max (m - x i) 0) ^ 2)).card
      ≤ Fintype.card V := by
  have h1 : (Finset.univ.filter (fun i => t ≤ (max (m - x i) 0) ^ 2)).card
      ≤ (Finset.univ.filter (fun i => x i < m)).card :=
    Finset.card_le_card (negPart_superlevel_subset t ht)
  omega

/-- **Per-part bound of the hard-direction chain** (Step 1c composing
1a with 1b): for any `y : V → ℝ` whose closed superlevel sets at
positive levels are minority-side,
`φ ^ 2 * d * ∑ i, y i ^ 2 ≤ E'(y)`. The Step-1b co-area core bounds the
weighted total variation of `y ^ 2` from below, the Step-1a
Cauchy–Schwarz core bounds its square from above, and the regularity
bridge turns the degree-weighted second factor into `4 * d * ‖y‖²`; the
degenerate zero-norm case is discharged by nonnegativity of `E'` (the
weights are nonnegative).

QA: `SpectralGraphTheory.QA.perPart_edge_QA` pins the instance on `K₂`
at `![1, 0]` (`1 ≤ 2`, both sides computed raw). -/
theorem hardDirection_perPart (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (y : V → ℝ) (hy : ∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ y i ^ 2)).card ≤ Fintype.card V) :
    cheegerConstant A ^ 2 * d * ∑ i, y i ^ 2
      ≤ ∑ i, ∑ j, A i j * (y i - y j) ^ 2 := by
  have hSnn : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hEnn : 0 ≤ ∑ i, ∑ j, A i j * (y i - y j) ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => mul_nonneg (hnn i j) (sq_nonneg _)
  rcases eq_or_ne (∑ i, y i ^ 2) 0 with h0 | h0
  · rw [h0, mul_zero]
    exact hEnn
  · have hco := coarea_core A hA hnn d hd hdpos y hy
    have hcs := core_sum_abs_sq_sub_sq A hA hnn y
    rw [sum_deg_mul_eq_of_regular A d hd y] at hcs
    have hTVnn : 0 ≤ ∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hnn i j) (abs_nonneg _)
    have hc0 : 0 ≤ 2 * (cheegerConstant A * d * ∑ i, y i ^ 2) :=
      mul_nonneg (by norm_num)
        (mul_nonneg (mul_nonneg (cheegerConstant_nonneg A hnn) hdpos.le) hSnn)
    have hsq : (2 * (cheegerConstant A * d * ∑ i, y i ^ 2)) ^ 2
        ≤ (∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2|) ^ 2 := by
      have h1 := mul_le_mul hco hco hc0 hTVnn
      rw [sq, sq]
      exact h1
    have hcomb : (2 * (cheegerConstant A * d * ∑ i, y i ^ 2)) ^ 2
        ≤ (∑ i, ∑ j, A i j * (y i - y j) ^ 2) * (4 * (d * ∑ i, y i ^ 2)) :=
      le_trans hsq hcs
    have hprod : 0 < 4 * (d * ∑ i, y i ^ 2) := by
      refine mul_pos (by norm_num) (mul_pos hdpos ?_)
      exact lt_of_le_of_ne hSnn (Ne.symm h0)
    have hring : (2 * (cheegerConstant A * d * ∑ i, y i ^ 2)) ^ 2
        = 4 * (d * ∑ i, y i ^ 2)
            * (cheegerConstant A ^ 2 * d * ∑ i, y i ^ 2) := by
      ring
    rw [hring] at hcomb
    have hfinal : 4 * (d * ∑ i, y i ^ 2)
          * (cheegerConstant A ^ 2 * d * ∑ i, y i ^ 2)
        ≤ 4 * (d * ∑ i, y i ^ 2)
            * (∑ i, ∑ j, A i j * (y i - y j) ^ 2) := by
      rw [mul_comm (4 * (d * ∑ i, y i ^ 2))
        (∑ i, ∑ j, A i j * (y i - y j) ^ 2)]
      exact hcomb
    exact le_of_mul_le_mul_left hfinal hprod

omit [DecidableEq V] in
/-- Pointwise, the two median parts of `x - m` split its square: at each
vertex one of the two parts vanishes, so `u ^ 2 + v ^ 2 = (x - m) ^ 2`
entrywise. -/
theorem posPart_add_negPart_sq (a m : ℝ) :
    (max (a - m) 0) ^ 2 + (max (m - a) 0) ^ 2 = (a - m) ^ 2 := by
  rcases le_total m a with h | h
  · rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    ring

omit [DecidableEq V] in
/-- **Norm split.** For `x ⊥ 1`, the two median parts jointly carry at
least the full squared norm — in fact
`∑ (x−m)⁺² + ∑ (m−x)⁺² = ∑ x² + n·m² ≥ ∑ x²`, the `n·m²` remainder being
nonnegative. This is the step that makes the constants tight: the two
parts jointly carry the full norm, so summing the per-part bound over
both parts loses nothing that the statement's `/2` does not pay back.

QA: `SpectralGraphTheory.QA.median_parts_norm_fin4_eq_QA` pins the exact
identity (with the `+ 4·m²` remainder visible) at two medians. -/
theorem median_parts_norm {x : V → ℝ} {m : ℝ}
    (horth : Matrix.dotProduct x onesVec = 0) :
    ∑ i, x i ^ 2
      ≤ ∑ i, (max (x i - m) 0) ^ 2 + ∑ i, (max (m - x i) 0) ^ 2 := by
  have hsum : ∑ i, x i = 0 := by
    simpa [Matrix.dotProduct, onesVec] using horth
  have hpt : ∀ i, (max (x i - m) 0) ^ 2 + (max (m - x i) 0) ^ 2
      = (x i - m) ^ 2 := fun i => posPart_add_negPart_sq (x i) m
  have hterm : ∀ i, (x i - m) ^ 2 = (x i ^ 2 - 2 * m * x i) + m ^ 2 :=
    fun i => by ring
  have hsplit : (∑ i, (max (x i - m) 0) ^ 2
      + ∑ i, (max (m - x i) 0) ^ 2)
      = ∑ i, x i ^ 2 + (Fintype.card V : ℝ) * m ^ 2 := by
    rw [← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun i _ => hpt i),
      Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero,
      Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [hsplit]
  have : 0 ≤ (Fintype.card V : ℝ) * m ^ 2 := by positivity
  linarith

/-- **Sweep lemma** (the Cheeger hard direction at test-vector level): on
a `d`-regular graph with positive degree, every nonzero `x ⊥ 1` has
`φ²/2 ≤ R_{L_sym}(x)`. The median split routes both parts to their
minority sides (so the Step-1b co-area core applies to each), the per-part
bounds sum through the Step-1a *fused* contraction — whose cross-edge
slack pays for carrying both parts — and the norm split carries the full
squared norm; the Step-1a normalization `R = E'/(2·d·‖x‖²)` then turns
`φ²·d·‖x‖² ≤ E'(x)` into the claimed `φ²/2 ≤ R` with nothing lost
anywhere in the chain.

QA: `SpectralGraphTheory.QA.sweep_edge_QA` (on `K₂`, `1/2 ≤ 2` against
the independently pinned `λ₂(L_sym) = 2`) and
`SpectralGraphTheory.QA.sweep_cycle_QA` (on `C₄` at `d = 2`, where
`φ²/2 ≤ 1/8 < 1 = R(x)` with a visible gap). -/
theorem cheeger_sweep (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    {x : V → ℝ} (hx0 : x ≠ 0) (horth : Matrix.dotProduct x onesVec = 0) :
    cheegerConstant A ^ 2 / 2
      ≤ rayleigh (regularNormalizedLaplacian A d) x := by
  obtain ⟨m, hup, hlow⟩ := exists_median x
  have hyu : ∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ (max (x i - m) 0) ^ 2)).card
        ≤ Fintype.card V :=
    fun t ht => minority_posPart hup t ht
  have hyv : ∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ (max (m - x i) 0) ^ 2)).card
        ≤ Fintype.card V :=
    fun t ht => minority_negPart hlow t ht
  have hu := hardDirection_perPart A hA hnn d hd hdpos
    (fun i => max (x i - m) 0) (fun t ht => hyu t ht)
  have hv := hardDirection_perPart A hA hnn d hd hdpos
    (fun i => max (m - x i) 0) (fun t ht => hyv t ht)
  have hc := sum_edgeWeight_sq_posPart_add_sq_negPart_le A hnn m x
  have hn := median_parts_norm (m := m) horth
  -- the two per-part bounds sum, through the fused contraction, into E'
  have hsum : cheegerConstant A ^ 2 * d * ∑ i, x i ^ 2
      ≤ ∑ i, ∑ j, A i j * (x i - x j) ^ 2 := by
    calc cheegerConstant A ^ 2 * d * ∑ i, x i ^ 2
        ≤ cheegerConstant A ^ 2 * d
            * (∑ i, (max (x i - m) 0) ^ 2
              + ∑ i, (max (m - x i) 0) ^ 2) := by
              refine mul_le_mul_of_nonneg_left hn ?_
              exact mul_nonneg
                (pow_nonneg (cheegerConstant_nonneg A hnn) 2) hdpos.le
      _ = cheegerConstant A ^ 2 * d * ∑ i, (max (x i - m) 0) ^ 2
          + cheegerConstant A ^ 2 * d * ∑ i, (max (m - x i) 0) ^ 2 := by
          ring
      _ ≤ ∑ i, ∑ j, A i j * (max (x i - m) 0 - max (x j - m) 0) ^ 2
          + ∑ i, ∑ j, A i j * (max (m - x i) 0 - max (m - x j) 0) ^ 2 :=
          add_le_add hu hv
      _ ≤ ∑ i, ∑ j, A i j * (x i - x j) ^ 2 := hc
  -- normalization and division
  have hR := rayleigh_regularNormalizedLaplacian_eq A hA d hd hdpos.ne' hx0
  have hdot : Matrix.dotProduct x x ≠ 0 := by
    intro h
    apply hx0
    funext i
    have hsum2 : ∑ j, x j * x j = 0 := by
      simpa [Matrix.dotProduct] using h
    have hmem := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (x j))).1 hsum2 i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hmem
  have hdotpos : 0 < Matrix.dotProduct x x := by
    rcases lt_or_ge 0 (Matrix.dotProduct x x) with h | h
    · exact h
    · exfalso
      have hE : Matrix.dotProduct x x = 0 :=
        le_antisymm h (by
          simp only [Matrix.dotProduct]
          exact Finset.sum_nonneg fun j _ => mul_self_nonneg _)
      exact hdot hE
  have hprod : 0 < 2 * d * Matrix.dotProduct x x :=
    mul_pos (mul_pos two_pos hdpos) hdotpos
  have hdotsum : Matrix.dotProduct x x = ∑ i, x i ^ 2 := by
    simp only [Matrix.dotProduct, pow_two]
  rw [hR, div_le_div_iff₀ two_pos hprod]
  calc cheegerConstant A ^ 2 * (2 * d * Matrix.dotProduct x x)
      = 2 * (cheegerConstant A ^ 2 * d * ∑ i, x i ^ 2) := by
        rw [hdotsum]; ring
    _ ≤ 2 * ∑ i, ∑ j, A i j * (x i - x j) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (∑ i, ∑ j, A i j * (x i - x j) ^ 2) * 2 := by ring

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

Retirement (2026-08-23): previously admitted as an axiom; now proved
(`proposals/discharge-perturbation-axioms.md` Steps 1a/1b/1c), with no
admitted dependencies — the explicit axiom count drops 10 → 9, and the
proposal's program (Weyl, Davis–Kahan, Cheeger easy and hard
directions) is complete. Route: the sweep lemma `cheeger_sweep` above
(the median split, per-part co-area + Cauchy–Schwarz composition, the
fused contraction, the norm split, and the exact-constant
normalization), discharged to the spectrum through
`secondEval_variational` + `le_csInf` at the `Pi.single` difference
witness. With `cheeger_upper_bound` proved since 2026-08-18, both
Cheeger inequalities are now hard crust.

QA: exercised by
`SpectralGraphTheory.QA.cheeger_positive_implies_secondEval_pos_QA` and
`SpectralGraphTheory.QA.cheeger_bounds_coherent_QA` in
`Scaffold/QA/SpectralGraph/Cheeger_QA.lean` (which now derive
consequences from a proved theorem), by
`SpectralGraphTheory.QA.edge_normLap_secondEval_eq_two_QA`, which pins
the right-hand side on the two-vertex edge to its classical value `2`,
and by the Step-1c witnesses `SpectralGraphTheory.QA.median_fin4_QA`,
`SpectralGraphTheory.QA.perPart_edge_QA`,
`SpectralGraphTheory.QA.median_parts_norm_fin4_eq_QA`,
`SpectralGraphTheory.QA.sweep_edge_QA`, and
`SpectralGraphTheory.QA.sweep_cycle_QA`, which pin the new layers
numerically. -/
theorem cheeger_lower_bound (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) :
    (cheegerConstant A) ^ 2 / 2 ≤
      secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard := by
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v := by
    have h1 : 1 < (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]; omega
    obtain ⟨a, b, -, -, hab⟩ := Finset.one_lt_card_iff.1 h1
    exact ⟨a, b, hab⟩
  -- the sInf set is nonempty: the single-edge difference vector
  have hsetne : {r : ℝ | ∃ x : V → ℝ, x ≠ 0 ∧ Matrix.dotProduct x onesVec = 0 ∧
      rayleigh (regularNormalizedLaplacian A d) x = r}.Nonempty := by
    refine ⟨rayleigh (regularNormalizedLaplacian A d)
      (Pi.single u 1 - Pi.single v 1 : V → ℝ), ?_⟩
    refine ⟨Pi.single u 1 - Pi.single v 1, ?_, ?_, rfl⟩
    · intro h
      have h1 : (Pi.single u 1 - Pi.single v 1 : V → ℝ) u = 0 := congrFun h u
      simp [Pi.sub_apply, Pi.single_apply, huv] at h1
    · simp only [Matrix.dotProduct, onesVec, Pi.sub_apply, mul_one,
        Finset.sum_sub_distrib]
      have hpu : ∀ w : V, ∑ i, Pi.single w (1 : ℝ) i = 1 := fun w => by simp
      rw [hpu u, hpu v, sub_self]
  rw [secondEval_variational (regularNormalizedLaplacian_symmetric A hA d)
    (regularNormalizedLaplacian_psd A hA hnonneg d hd hdpos)
    (regularNormalizedLaplacian_mulVec_onesVec A d hd hdpos.ne') hcard]
  refine le_csInf hsetne ?_
  rintro r ⟨x, hx0, horth, rfl⟩
  exact cheeger_sweep A hA hnonneg d hd hdpos hx0 horth

end Step1c

/-!
### The conductance minimum is attained (proved)

On a type with at least two vertices the `sInf` defining
`cheegerConstant` is a minimum: the filtered powerset of nonempty proper
subsets is a nonempty finite set, so a conductance-minimal cut exists.
This is what turns the Cheeger *inequalities* (bounds on the infimum)
into *cut-existence* corollaries — the Fiedler Phase B certificate
(`GraphTheory.Fiedler.cheeger_cut_existence`) is its named consumer.
-/

/-- The conductance minimum is attained: on at least two vertices there
is a nonempty proper cut whose conductance equals `cheegerConstant`
(the filtered powerset is a nonempty finite set, so
`Finset.exists_min_image` realizes the `sInf` as a minimum).

QA: `SpectralGraphTheory.QA.attainment_edge_QA` in
`Scaffold/QA/SpectralGraph/Fiedler_QA.lean` instantiates it on `K₂`
against the independently pinned `cheegerConstant edgeAdj = 1`. -/
theorem cheegerConstant_attained (A : WAdj (V := V))
    (hnonneg : ∀ i j, 0 ≤ A i j) (hcard : 2 ≤ Fintype.card V) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance A S = cheegerConstant A := by
  classical
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v := by
    have h1 : 1 < (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]; omega
    obtain ⟨a, b, -, -, hab⟩ := Finset.one_lt_card_iff.1 h1
    exact ⟨a, b, hab⟩
  have hucompl : ({u} : Finset V)ᶜ.Nonempty :=
    ⟨v, Finset.mem_compl.2 (fun hv =>
      Ne.symm huv (Finset.mem_singleton.1 hv))⟩
  obtain ⟨S₀, hS₀, hmin⟩ := Finset.exists_min_image
    ((Finset.univ : Finset (Finset V)).filter
      (fun S => S.Nonempty ∧ Sᶜ.Nonempty))
    (fun S => conductance A S)
    ⟨{u}, Finset.mem_filter.2 ⟨Finset.mem_univ {u},
      ⟨Finset.singleton_nonempty u, hucompl⟩⟩⟩
  obtain ⟨-, ⟨hS₀ne, hS₀c⟩⟩ := Finset.mem_filter.1 hS₀
  refine ⟨S₀, hS₀ne, hS₀c, ?_⟩
  have hle : conductance A S₀ ≤ cheegerConstant A := by
    rw [cheegerConstant]
    refine le_csInf ⟨conductance A {u},
      ⟨{u}, Finset.singleton_nonempty u, hucompl, rfl⟩⟩ ?_
    rintro c ⟨S, hS, hSc, rfl⟩
    exact hmin S (Finset.mem_filter.2 ⟨Finset.mem_univ S, ⟨hS, hSc⟩⟩)
  exact le_antisymm hle
    (conductance_ge_cheegerConstant A hnonneg S₀ hS₀ne hS₀c)

/-!
### The sweep extraction (proved)

`proposals/sweep-cut-extraction.md`, delivered 2026-08-24 as pure hard
crust (zero new axioms): the *algorithm-facing* strengthening of the
Cheeger hard direction. `cheeger_sweep` bounds the conductance
**infimum**; the theorems below exhibit an explicit **swept level set**
— the object the classical spectral-partitioning sweep actually
returns — at the same constant:

- `sweep_level_extract` (per part): for any `y` whose nonempty closed
  superlevel sets at positive levels are all minority-side (exactly
  `coarea_core`'s hypothesis), some closed superlevel set `S = {i :
  t ≤ y i ^ 2}` of `y ^ 2` at a positive level attains
  `conductance A S ^ 2 ≤ E'(y) / (d * ∑ y i ^ 2)`.

- `cheeger_sweep_cut` (median assembly): for any `x ⊥ 1`, `x ≠ 0`,
  some closed superlevel or sublevel set `S` of `x` itself satisfies
  `conductance A S ^ 2 ≤ 2 * R_{L_sym}(x)` — the same constant as
  `cheeger_sweep` (`φ_min ^ 2 / 2 ≤ R`), with the witness explicit.

The extraction route replaces the textbook averaging-by-pigeonhole
(which needs a *strict* integral inequality) with **attainment**: the
boundary-to-size ratio is minimized over the finitely many positive
values of `y ^ 2` (`Finset.exists_min_image`); every closed superlevel
set equals one at an attained value (its own least dominating value,
by `Finset.min'`); the resulting per-level bound is non-strict, so the
layer-cake integration is a structural clone of `coarea_core`'s own
proof. Composed with Component A (`core_sum_abs_sq_sub_sq`) and the
minority conductance conversion, the chain loses nothing against the
Step-1c per-part bound — indeed `sweep_level_extract` *implies* the
per-part statement, since the level set's conductance bounds the
Cheeger constant from below.

The named consumer is the spectral-partitioning algorithm interface
(`GraphTheory.Fiedler.fiedler_sweep_cut`, the Phase C instantiation at
the Fiedler vector): a consumer that wants *the cut the sweep returns*,
not an existence statement over the non-constructive conductance
minimizer of `cheeger_cut_existence`.
-/

section SweepExtraction

omit [Fintype V] [DecidableEq V] in
/-- Level-set conversion for the positive part at a positive level: a
closed superlevel set of `(x − m)⁺ ^ 2` at level `t > 0` is exactly a
closed superlevel set of `x` at level `m + √t`. Private to the sweep
extraction. -/
theorem mem_of_posPart_sq {x : V → ℝ} {m t : ℝ} (ht : 0 < t) (i : V) :
    (t ≤ (max (x i - m) 0) ^ 2) ↔ (m + Real.sqrt t ≤ x i) := by
  constructor
  · intro h
    rcases lt_or_le (x i) m with hx | hx
    · exfalso
      rw [max_eq_right (by linarith : x i - m ≤ 0)] at h
      norm_num at h
      linarith
    · rw [max_eq_left (by linarith : 0 ≤ x i - m)] at h
      have hs : Real.sqrt t ≤ Real.sqrt ((x i - m) ^ 2) :=
        Real.sqrt_le_sqrt h
      rw [Real.sqrt_sq (by linarith : 0 ≤ x i - m)] at hs
      linarith
  · intro h
    have hxm : 0 ≤ x i - m := by
      have := Real.sqrt_nonneg t
      linarith
    rw [max_eq_left hxm]
    have h1 : Real.sqrt t ≤ x i - m := by
      have := Real.sqrt_nonneg t
      linarith
    have h2 : |Real.sqrt t| ≤ |x i - m| := by
      rw [abs_of_nonneg (Real.sqrt_nonneg t), abs_of_nonneg hxm]
      exact h1
    calc t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht.le).symm
      _ = |Real.sqrt t| ^ 2 := by rw [abs_of_nonneg (Real.sqrt_nonneg t)]
      _ ≤ |x i - m| ^ 2 := by exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (x i - m) ^ 2 := by rw [abs_of_nonneg hxm]

omit [Fintype V] [DecidableEq V] in
/-- Level-set conversion for the negative part at a positive level: a
closed superlevel set of `(m − x)⁺ ^ 2` at level `t > 0` is exactly a
closed sublevel set of `x` at level `m − √t`. Private to the sweep
extraction. -/
theorem mem_of_negPart_sq {x : V → ℝ} {m t : ℝ} (ht : 0 < t) (i : V) :
    (t ≤ (max (m - x i) 0) ^ 2) ↔ (x i ≤ m - Real.sqrt t) := by
  constructor
  · intro h
    rcases lt_or_le m (x i) with hx | hx
    · exfalso
      rw [max_eq_right (by linarith : m - x i ≤ 0)] at h
      norm_num at h
      linarith
    · rw [max_eq_left (by linarith : 0 ≤ m - x i)] at h
      have hs : Real.sqrt t ≤ Real.sqrt ((m - x i) ^ 2) :=
        Real.sqrt_le_sqrt h
      rw [Real.sqrt_sq (by linarith : 0 ≤ m - x i)] at hs
      linarith
  · intro h
    have hxm : 0 ≤ m - x i := by
      have := Real.sqrt_nonneg t
      linarith
    rw [max_eq_left hxm]
    have h1 : Real.sqrt t ≤ m - x i := by
      have := Real.sqrt_nonneg t
      linarith
    have h2 : |Real.sqrt t| ≤ |m - x i| := by
      rw [abs_of_nonneg (Real.sqrt_nonneg t), abs_of_nonneg hxm]
      exact h1
    calc t = Real.sqrt t ^ 2 := (Real.sq_sqrt ht.le).symm
      _ = |Real.sqrt t| ^ 2 := by rw [abs_of_nonneg (Real.sqrt_nonneg t)]
      _ ≤ |m - x i| ^ 2 := by exact pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (m - x i) ^ 2 := by rw [abs_of_nonneg hxm]

section L1

open MeasureTheory intervalIntegral

/-- **The per-part sweep extraction.** For any `y : V → ℝ` whose
nonempty closed superlevel sets `{i : t ≤ y i ^ 2}` at positive levels
are all minority-side (`2 * |S_t| ≤ Fintype.card V` — exactly
`coarea_core`'s hypothesis), with `0 < ∑ i, y i ^ 2`, there is a
positive level `t` whose closed superlevel set `S = {i : t ≤ y i ^ 2}`
is nonempty, proper, and satisfies

`conductance A S ^ 2 ≤ E'(y) / (d * ∑ i, y i ^ 2)`

where `E'(y) = ∑ i j, A i j * (y i - y j) ^ 2` is the ordered Dirichlet
double sum. This is the *explicit* sweep-cut object: the level set the
spectral-partitioning sweep would return, with the same per-part
constant the Step-1c chain gives for the infimum (`hardDirection_perPart`
follows from this, since the exhibited set's conductance bounds
`cheegerConstant` from below).

Route (recorded in `proposals/sweep-cut-extraction.md`): attainment
replaces averaging — the boundary-to-size ratio is minimized over the
finitely many positive values of `y ^ 2`; every closed superlevel set
at a positive level equals one at an attained value (its least
dominating value); the per-level bound is non-strict, so the
layer-cake integration is `coarea_core`'s own proof pattern (mass and
pair layer-cakes, the `t = 0` endpoint absorbed a.e.), closed by
Component A (`core_sum_abs_sq_sub_sq`) and the minority conductance
conversion (`min (vol S) (vol Sᶜ) = d * |S|`).

Statement-shape notes: no `2 ≤ Fintype.card V` hypothesis (minority at
a nonempty level forces it); the level-set membership is stated as an
iff so consumers get the sweep family membership, not just any set.

QA: `SpectralGraphTheory.QA.sweep_extract_cycle_QA` in
`Scaffold/QA/SpectralGraph/Cheeger_QA.lean` forces the extracted set to
`{0}` on `C₄` at `y = ![1, 0, 0, 0]` and pins its conductance to `1`
against the theorem bound `E'(y) / (d * M) = 4 / 2 = 2`. -/
theorem sweep_level_extract (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (y : V → ℝ) (hy : ∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ y i ^ 2)).card ≤ Fintype.card V)
    (hM : 0 < ∑ i, y i ^ 2) :
    ∃ S : Finset V, ∃ t : ℝ, 0 < t ∧ (∀ i, i ∈ S ↔ t ≤ y i ^ 2) ∧
      S.Nonempty ∧ Sᶜ.Nonempty ∧
      conductance A S ^ 2
        ≤ (∑ i, ∑ j, A i j * (y i - y j) ^ 2) / (d * ∑ i, y i ^ 2) := by
  classical
  have himg : ∀ i : V, y i ^ 2 ∈ Finset.univ.image (fun i => y i ^ 2) :=
    fun i => Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hy2 : ∀ i, 0 ≤ y i ^ 2 := fun i => sq_nonneg _
  obtain ⟨i₀, hi₀⟩ : ∃ i : V, 0 < y i ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have hz : ∑ i, y i ^ 2 = 0 :=
      Finset.sum_eq_zero fun i _ => le_antisymm (hcon i) (hy2 i)
    linarith
  -- the attained positive values, with the minimal boundary-to-size ratio
  have hFne : ((Finset.univ.image (fun i => y i ^ 2)).filter
    (fun c => 0 < c)).Nonempty :=
    ⟨y i₀ ^ 2, Finset.mem_filter.2 ⟨himg i₀, hi₀⟩⟩
  obtain ⟨cstar, hcstarmem, hcstarmin⟩ := Finset.exists_min_image
    ((Finset.univ.image (fun i => y i ^ 2)).filter (fun c => 0 < c))
    (fun c : ℝ => boundary A (Finset.univ.filter (fun i => c ≤ y i ^ 2))
      / ((Finset.univ.filter (fun i => c ≤ y i ^ 2)).card : ℝ)) hFne
  have hcstarimg : cstar ∈ Finset.univ.image (fun i => y i ^ 2) :=
    (Finset.mem_filter.1 hcstarmem).1
  have hcstarpos : 0 < cstar := (Finset.mem_filter.1 hcstarmem).2
  obtain ⟨iw, hiw⟩ : ∃ i : V, y i ^ 2 = cstar := by
    rw [Finset.mem_image] at hcstarimg
    obtain ⟨i, -, hi⟩ := hcstarimg
    exact ⟨i, hi⟩
  set Sstar : Finset V := Finset.univ.filter (fun i => cstar ≤ y i ^ 2) with hSstar
  have hSmem : ∀ i, i ∈ Sstar ↔ cstar ≤ y i ^ 2 := by
    intro i
    rw [hSstar]; exact Finset.mem_filter.trans (by simp)
  have hSstarne : Sstar.Nonempty :=
    ⟨iw, (hSmem iw).2 (le_of_eq hiw.symm)⟩
  have hcardstar : 0 < Sstar.card := Finset.card_pos.2 hSstarne
  have hcardposF : ∀ c ∈ (Finset.univ.image (fun i => y i ^ 2)).filter
      (fun c => 0 < c),
      0 < (Finset.univ.filter (fun i => c ≤ y i ^ 2)).card := by
    intro c hc
    have h1 := (Finset.mem_filter.1 hc).1
    rw [Finset.mem_image] at h1
    obtain ⟨i, -, hi⟩ := h1
    exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2
      ⟨Finset.mem_univ i, le_of_eq hi.symm⟩⟩
  -- the per-member multiplicative bound from minimality
  have hper : ∀ c ∈ (Finset.univ.image (fun i => y i ^ 2)).filter
      (fun c => 0 < c),
      (boundary A Sstar / (Sstar.card : ℝ))
        * ((Finset.univ.filter (fun i => c ≤ y i ^ 2)).card : ℝ)
      ≤ boundary A (Finset.univ.filter (fun i => c ≤ y i ^ 2)) := by
    intro c hc
    have h := hcstarmin c hc
    rw [div_le_div_iff₀ (Nat.cast_pos.2 hcardstar)
      (Nat.cast_pos.2 (hcardposF c hc))] at h
    rw [div_mul_eq_mul_div, div_le_iff₀ (Nat.cast_pos.2 hcardstar)]
    exact h
  -- the covering fact: every closed superlevel set at a positive level is
  -- one at an attained (positive) value
  have hcover : ∀ t : ℝ, 0 < t →
      (boundary A Sstar / (Sstar.card : ℝ))
        * ((Finset.univ.filter (fun i => t ≤ y i ^ 2)).card : ℝ)
      ≤ boundary A (Finset.univ.filter (fun i => t ≤ y i ^ 2)) := by
    intro t ht
    rcases (Finset.univ.filter (fun i => t ≤ y i ^ 2)).eq_empty_or_nonempty
      with hE | hNE
    · rw [hE]
      have hb : boundary A (∅ : Finset V) = 0 := by simp [boundary]
      rw [hb]
      simp
    · obtain ⟨j, hj⟩ := hNE
      have hGne : ((Finset.univ.image (fun i => y i ^ 2)).filter
          (fun c => t ≤ c)).Nonempty :=
        ⟨y j ^ 2, Finset.mem_filter.2 ⟨himg j, (Finset.mem_filter.1 hj).2⟩⟩
      obtain ⟨c', hc'mem, hc'le⟩ :
          ∃ c' : ℝ, c' ∈ (Finset.univ.image (fun i => y i ^ 2)).filter
              (fun c => t ≤ c)
            ∧ ∀ c ∈ (Finset.univ.image (fun i => y i ^ 2)).filter
                (fun c => t ≤ c), c' ≤ c :=
        ⟨((Finset.univ.image (fun i => y i ^ 2)).filter
            (fun c => t ≤ c)).min' hGne,
          Finset.min'_mem _ hGne,
          fun c hc => Finset.min'_le _ c hc⟩
      have hc't : t ≤ c' := (Finset.mem_filter.1 hc'mem).2
      have hc'F : c' ∈ (Finset.univ.image (fun i => y i ^ 2)).filter
          (fun c => 0 < c) :=
        Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hc'mem).1,
          lt_of_lt_of_le ht hc't⟩
      have hSetEq : (Finset.univ.filter (fun i => t ≤ y i ^ 2))
          = Finset.univ.filter (fun i => c' ≤ y i ^ 2) := by
        apply Finset.ext
        intro i
        constructor
        · intro hit
          refine Finset.mem_filter.2 ⟨Finset.mem_univ i, hc'le _ ?_⟩
          exact Finset.mem_filter.2 ⟨himg i, (Finset.mem_filter.1 hit).2⟩
        · intro hic
          exact Finset.mem_filter.2 ⟨Finset.mem_univ i,
            le_trans hc't ((Finset.mem_filter.1 hic).2)⟩
      rw [hSetEq]
      exact hper c' hc'F
  -- the layer-cake integration (a clone of coarea_core's proof)
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = ∑ i, y i ^ 2 + 1 := ⟨_, rfl⟩
  have hRpos : 0 ≤ R := by
    rw [hRdef]
    have hsumnn : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => hy2 i
    linarith
  have hcR : ∀ i, y i ^ 2 ≤ R := by
    intro i
    have hle := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => hy2 i)
      (Finset.mem_univ i)
    rw [hRdef]
    linarith
  have hintL : IntervalIntegrable (fun t =>
      (2 * (boundary A Sstar / (Sstar.card : ℝ)))
        * ∑ i, indicatorLE (y i ^ 2) t) volume 0 R := by
    have hsum : IntervalIntegrable
        (fun t => ∑ i, indicatorLE (y i ^ 2) t) volume 0 R := by
      have h := IntervalIntegrable.sum (Finset.univ : Finset V)
        (f := fun i t => indicatorLE (y i ^ 2) t)
        (fun i _ => intervalIntegrable_indicatorLE (y i ^ 2) 0 R)
      have hfun : (fun t => ∑ i, indicatorLE (y i ^ 2) t)
          = ∑ i : V, (fun t => indicatorLE (y i ^ 2) t) := by
        funext t
        rw [Finset.sum_apply]
      rw [hfun]
      exact h
    exact intervalIntegrable_const_mul _ hsum
  have hintR : IntervalIntegrable (fun t => ∑ p : V × V,
      A p.1 p.2 * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|)
      volume 0 R := by
    have h := IntervalIntegrable.sum (Finset.univ : Finset (V × V))
      (f := fun p t => A p.1 p.2
        * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|)
      (fun p _ => intervalIntegrable_const_mul _
        (((intervalIntegrable_indicatorLE (y p.1 ^ 2) 0 R).sub
          (intervalIntegrable_indicatorLE (y p.2 ^ 2) 0 R)).abs))
    have hfun : (fun t => ∑ p : V × V, A p.1 p.2
        * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|)
        = ∑ p : V × V, (fun t => A p.1 p.2
          * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|) := by
      funext t
      rw [Finset.sum_apply]
    rw [hfun]
    exact h
  have hmass : ∫ t in (0:ℝ)..R, ∑ i, indicatorLE (y i ^ 2) t
      = ∑ i, y i ^ 2 := by
    rw [intervalIntegral.integral_finset_sum
      (fun i _ => intervalIntegrable_indicatorLE (y i ^ 2) 0 R)]
    exact Finset.sum_congr rfl fun i _ => integral_indicatorLE (hy2 i) (hcR i)
  have hint : ∫ t in (0:ℝ)..R, ∑ p : V × V, A p.1 p.2
        * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t|
      = ∑ p : V × V, ∫ t in (0:ℝ)..R, A p.1 p.2
        * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t| :=
    intervalIntegral.integral_finset_sum
      (fun p _ => intervalIntegrable_const_mul _
        (((intervalIntegrable_indicatorLE (y p.1 ^ 2) 0 R).sub
          (intervalIntegrable_indicatorLE (y p.2 ^ 2) 0 R)).abs))
  have hpair : ∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2|
      = ∫ t in (0:ℝ)..R, ∑ p : V × V, A p.1 p.2
          * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t| := by
    rw [hint, ← Fintype.sum_prod_type'
      (fun i j => A i j * |y i ^ 2 - y j ^ 2|)]
    exact Finset.sum_congr rfl fun p _ => by
      rw [intervalIntegral.integral_const_mul,
        integral_abs_indicatorLE_sub (hy2 p.1) (hy2 p.2)
          (max_le (hcR p.1) (hcR p.2))]
  -- the a.e. per-level bound
  have hne : {t : ℝ | t ≠ 0} ∈ MeasureTheory.ae volume := by
    rw [MeasureTheory.mem_ae_iff]; simp [Real.volume_singleton]
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 R)),
      (2 * (boundary A Sstar / (Sstar.card : ℝ)))
        * ∑ i, indicatorLE (y i ^ 2) t
      ≤ ∑ p : V × V, A p.1 p.2
          * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t| := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hne] with t ht
    intro htI
    have h0t : 0 < t := lt_of_le_of_ne htI.1 (Ne.symm ht)
    have h1 : ∑ i, indicatorLE (y i ^ 2) t
        = ((Finset.univ.filter (fun i => t ≤ y i ^ 2)).card : ℝ) :=
      sum_indicatorLE_eq_card_filter (fun i => y i ^ 2) t
    have h2 : ∑ i, ∑ j, A i j * |indicatorLE (y i ^ 2) t
          - indicatorLE (y j ^ 2) t|
        = 2 * boundary A (Finset.univ.filter (fun i => t ≤ y i ^ 2)) :=
      sum_pairAbs_eq_two_boundary A hA y t _
        (fun i => Finset.mem_filter.trans (by simp))
    rw [← Fintype.sum_prod_type'
      (fun i j => A i j * |indicatorLE (y i ^ 2) t
        - indicatorLE (y j ^ 2) t|)] at h2
    have h3 := hcover t h0t
    rw [h1, h2]
    linarith
  have hint2r : 2 * (boundary A Sstar / (Sstar.card : ℝ)) * ∑ i, y i ^ 2
      ≤ ∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2| := by
    calc 2 * (boundary A Sstar / (Sstar.card : ℝ)) * ∑ i, y i ^ 2
        = (2 * (boundary A Sstar / (Sstar.card : ℝ)))
            * ∫ t in (0:ℝ)..R, ∑ i, indicatorLE (y i ^ 2) t := by rw [hmass]
      _ = ∫ t in (0:ℝ)..R, (2 * (boundary A Sstar / (Sstar.card : ℝ)))
            * ∑ i, indicatorLE (y i ^ 2) t :=
          (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ t in (0:ℝ)..R, ∑ p : V × V, A p.1 p.2
            * |indicatorLE (y p.1 ^ 2) t - indicatorLE (y p.2 ^ 2) t| :=
          intervalIntegral.integral_mono_ae_restrict hRpos hintL hintR hae
      _ = ∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2| := hpair.symm
  -- the conductance conversion (minority makes the volume the small side)
  have hminor : 2 * Sstar.card ≤ Fintype.card V := hy cstar hcstarpos
  have hcardle : Sstar.card ≤ Sstarᶜ.card := by
    have h1 : Sstar.card + Sstarᶜ.card = Fintype.card V :=
      Finset.card_add_card_compl Sstar
    omega
  have hScne : Sstarᶜ.Nonempty := by
    rcases Sstarᶜ.eq_empty_or_nonempty with hE | hNE
    · exfalso
      have hz : Sstarᶜ.card = 0 := by rw [hE]; simp
      omega
    · exact hNE
  have hminvol : min (vol A Sstar) (vol A Sstarᶜ)
      = d * (Sstar.card : ℝ) := by
    rw [vol_eq_of_regular A d hd Sstar, vol_eq_of_regular A d hd Sstarᶜ,
      min_eq_left (mul_le_mul_of_nonneg_left
        (by exact_mod_cast hcardle) hdpos.le)]
  -- Component A composition and the final algebra
  have hcomp := core_sum_abs_sq_sub_sq A hA hnn y
  rw [sum_deg_mul_eq_of_regular A d hd y] at hcomp
  have hbnn : 0 ≤ boundary A Sstar := boundary_nonneg A hnn Sstar
  have hk' : 0 ≤ (Sstar.card : ℝ) := Nat.cast_nonneg _
  have hkne : (Sstar.card : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 hcardstar)
  have hrnn : 0 ≤ boundary A Sstar / (Sstar.card : ℝ) :=
    div_nonneg hbnn hk'
  have hLnn : 0 ≤ 2 * (boundary A Sstar / (Sstar.card : ℝ)) * ∑ i, y i ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hrnn) hM.le
  have hTVnn : 0 ≤ ∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hnn i j) (abs_nonneg _)
  have habs : abs (2 * (boundary A Sstar / (Sstar.card : ℝ)) * ∑ i, y i ^ 2)
      ≤ abs (∑ i, ∑ j, A i j * |y i ^ 2 - y j ^ 2|) := by
    rw [abs_of_nonneg hLnn, abs_of_nonneg hTVnn]
    exact hint2r
  have hTVsq : (2 * (boundary A Sstar / (Sstar.card : ℝ)) * ∑ i, y i ^ 2) ^ 2
      ≤ (∑ i, ∑ j, A i j * (y i - y j) ^ 2) * (4 * (d * ∑ i, y i ^ 2)) :=
    le_trans (sq_le_sq.mpr habs) hcomp
  have hkey : (boundary A Sstar / (Sstar.card : ℝ))
      * ((boundary A Sstar / (Sstar.card : ℝ)) * ∑ i, y i ^ 2)
      ≤ d * ∑ i, ∑ j, A i j * (y i - y j) ^ 2 := by
    have h4 : (boundary A Sstar / (Sstar.card : ℝ) * ∑ i, y i ^ 2) ^ 2
        ≤ (∑ i, ∑ j, A i j * (y i - y j) ^ 2) * (d * ∑ i, y i ^ 2) := by
      nlinarith [hTVsq]
    have hring : (boundary A Sstar / (Sstar.card : ℝ) * ∑ i, y i ^ 2) ^ 2
        = ((boundary A Sstar / (Sstar.card : ℝ))
            * ((boundary A Sstar / (Sstar.card : ℝ)) * ∑ i, y i ^ 2))
          * ∑ i, y i ^ 2 := by
      ring
    rw [hring] at h4
    nlinarith [h4, hM]
  have hkey' : (boundary A Sstar) ^ 2 * ∑ i, y i ^ 2
      ≤ d * (∑ i, ∑ j, A i j * (y i - y j) ^ 2) * (Sstar.card : ℝ) ^ 2 := by
    have h1 : (boundary A Sstar) ^ 2 * ∑ i, y i ^ 2
        = (boundary A Sstar / (Sstar.card : ℝ))
          * ((boundary A Sstar / (Sstar.card : ℝ)) * ∑ i, y i ^ 2)
          * (Sstar.card : ℝ) * (Sstar.card : ℝ) := by
      field_simp [hkne]
      ring
    have h2 : d * (∑ i, ∑ j, A i j * (y i - y j) ^ 2) * (Sstar.card : ℝ) ^ 2
        = (d * ∑ i, ∑ j, A i j * (y i - y j) ^ 2)
          * (Sstar.card : ℝ) * (Sstar.card : ℝ) := by
      ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkey hk') hk'
  refine ⟨Sstar, cstar, hcstarpos, hSmem, hSstarne, hScne, ?_⟩
  have hcond : conductance A Sstar
      = boundary A Sstar / (d * (Sstar.card : ℝ)) := by
    rw [conductance, hminvol]
  rw [hcond, div_pow, div_le_div_iff₀ (pow_pos (mul_pos hdpos
    (Nat.cast_pos.2 hcardstar)) 2) (mul_pos hdpos hM)]
  calc (boundary A Sstar) ^ 2 * (d * ∑ i, y i ^ 2)
      = ((boundary A Sstar) ^ 2 * ∑ i, y i ^ 2) * d := by
        ring
    _ ≤ (d * ∑ i, ∑ j, A i j * (y i - y j) ^ 2) * (Sstar.card : ℝ) ^ 2 * d :=
        mul_le_mul_of_nonneg_right hkey' hdpos.le
    _ = (∑ i, ∑ j, A i j * (y i - y j) ^ 2) * (d * (Sstar.card : ℝ)) ^ 2 := by
        ring

end L1

/-- **The sweep-cut theorem (median assembly).** For any `x ⊥ 1`,
`x ≠ 0` on a `d`-regular graph of positive degree, there is a
nonempty proper cut which is a **closed superlevel or sublevel set of
`x` itself** — a member of the sweep family the spectral-partitioning
algorithm actually enumerates — with

`conductance A S ^ 2 ≤ 2 * rayleigh (regularNormalizedLaplacian A d) x`.

Same constant as `cheeger_sweep` (which bounds the *infimum* over all
cuts), but the witness is explicit: a swept level set of the test
vector. Route: the median split (`exists_median`,
`minority_posPart`/`minority_negPart` supply `sweep_level_extract`'s
hypothesis verbatim for both parts), the product test selecting which
part's extraction to run (with degenerate single-part cases when the
other part vanishes), the fused contraction
(`sum_edgeWeight_sq_posPart_add_sq_negPart_le`), the norm split
(`median_parts_norm`), and the Step-1a normalization
(`rayleigh_regularNormalizedLaplacian_eq`). The level membership of the
extracted part-sets converts to `x`-level sets through
`mem_of_posPart_sq`/`mem_of_negPart_sq` at the offset `√t`.

Trust level: hard crust; nothing axiom-backed. The strengthened
Cheeger cut-existence statement (an existential over this same sweep
family at the Fiedler vector) is
`GraphTheory.Fiedler.fiedler_sweep_cut`.

QA: `SpectralGraphTheory.QA.sweep_cut_cycle_QA`,
`SpectralGraphTheory.QA.sweep_cut_cycle_optimal_QA`, and
`SpectralGraphTheory.QA.sweep_cut_orth_dropped_refuted_QA` in
`Scaffold/QA/SpectralGraph/Cheeger_QA.lean`. -/
theorem cheeger_sweep_cut (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    {x : V → ℝ} (hx0 : x ≠ 0) (horth : Matrix.dotProduct x onesVec = 0) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ x i) ∨ (∃ t : ℝ, ∀ i, i ∈ S ↔ x i ≤ t)) ∧
      conductance A S ^ 2 ≤ 2 * rayleigh (regularNormalizedLaplacian A d) x := by
  obtain ⟨m, hup, hlow⟩ := exists_median x
  have hyu : ∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ (max (x i - m) 0) ^ 2)).card
        ≤ Fintype.card V := fun t ht => minority_posPart hup t ht
  have hyv : ∀ t : ℝ, 0 < t →
      2 * (Finset.univ.filter (fun i => t ≤ (max (m - x i) 0) ^ 2)).card
        ≤ Fintype.card V := fun t ht => minority_negPart hlow t ht
  have hMunn : 0 ≤ ∑ i, (max (x i - m) 0) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hMvnn : 0 ≤ ∑ i, (max (m - x i) 0) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfused := sum_edgeWeight_sq_posPart_add_sq_negPart_le A hnn m x
  have hnormsplit := median_parts_norm (m := m) horth
  have hdotne : Matrix.dotProduct x x ≠ 0 := by
    intro h
    apply hx0
    funext i
    have hsum2 : ∑ j, x j * x j = 0 := by simpa [Matrix.dotProduct] using h
    have hmem := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_self_nonneg (x j))).1 hsum2 i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hmem
  have hdotsum : Matrix.dotProduct x x = ∑ i, x i ^ 2 := by
    simp only [Matrix.dotProduct, pow_two]
  have hdotpos : 0 < Matrix.dotProduct x x := by
    rcases lt_or_ge 0 (Matrix.dotProduct x x) with h | h
    · exact h
    · exfalso
      have hE : Matrix.dotProduct x x = 0 :=
        le_antisymm h (by
          simp only [Matrix.dotProduct]
          exact Finset.sum_nonneg fun j _ => mul_self_nonneg _)
      exact hdotne hE
  have hR := rayleigh_regularNormalizedLaplacian_eq A hA d hd hdpos.ne' hx0
  have htwoR : 2 * rayleigh (regularNormalizedLaplacian A d) x
      = (∑ i, ∑ j, A i j * (x i - x j) ^ 2) / (d * Matrix.dotProduct x x) := by
    rw [hR]
    field_simp [hdpos.ne', hdotne]
    ring
  -- the shared numeric chain
  have hchain : ∀ yu yv : V → ℝ,
      ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2) * (∑ i, yv i ^ 2)
        ≤ (∑ i, ∑ j, A i j * (yv i - yv j) ^ 2) * (∑ i, yu i ^ 2)) →
      0 < ∑ i, yu i ^ 2 → 0 ≤ ∑ i, yv i ^ 2 →
      Matrix.dotProduct x x ≤ ∑ i, yu i ^ 2 + ∑ i, yv i ^ 2 →
      ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
        + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
        ≤ ∑ i, ∑ j, A i j * (x i - x j) ^ 2 →
      (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2) / (d * ∑ i, yu i ^ 2)
        ≤ 2 * rayleigh (regularNormalizedLaplacian A d) x := by
    intro yu yv hprod hMyu hMvnn hsplit hfus
    have hEunn : 0 ≤ ∑ i, ∑ j, A i j * (yu i - yu j) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hnn i j) (sq_nonneg _)
    have hEvnn : 0 ≤ ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hnn i j) (sq_nonneg _)
    have hMunn : 0 ≤ ∑ i, yu i ^ 2 := le_of_lt hMyu
    have hs1 : (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2) / (d * ∑ i, yu i ^ 2)
        ≤ ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          / (d * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2)) := by
      rw [div_le_div_iff₀ (mul_pos hdpos hMyu)
        (mul_pos hdpos (by linarith : (0:ℝ)
          < ∑ i, yu i ^ 2 + ∑ i, yv i ^ 2))]
      calc (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            * (d * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2))
          = d * ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2) * (∑ i, yu i ^ 2)
            + (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2) * (∑ i, yv i ^ 2)) := by
            ring
        _ ≤ d * ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2) * (∑ i, yu i ^ 2)
            + (∑ i, ∑ j, A i j * (yv i - yv j) ^ 2) * (∑ i, yu i ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (add_le_add_left hprod _) hdpos.le
        _ = ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (d * ∑ i, yu i ^ 2) := by
            ring
    have hs2 : ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          / (d * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2))
        ≤ (∑ i, ∑ j, A i j * (x i - x j) ^ 2)
          / (d * Matrix.dotProduct x x) := by
      rw [div_le_div_iff₀ (mul_pos hdpos (by linarith : (0:ℝ)
          < ∑ i, yu i ^ 2 + ∑ i, yv i ^ 2))
        (mul_pos hdpos hdotpos)]
      have h1 : ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2) * Matrix.dotProduct x x
          ≤ ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2) :=
        mul_le_mul_of_nonneg_left hsplit (add_nonneg hEunn hEvnn)
      have h2 : ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2)
          ≤ (∑ i, ∑ j, A i j * (x i - x j) ^ 2)
          * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2) :=
        mul_le_mul_of_nonneg_right hfus (add_nonneg hMunn hMvnn)
      calc ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
            * (d * Matrix.dotProduct x x)
          = d * (((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2) * Matrix.dotProduct x x) := by
            ring
        _ ≤ d * (((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 hdpos.le
        _ ≤ d * ((∑ i, ∑ j, A i j * (x i - x j) ^ 2)
          * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2)) :=
            mul_le_mul_of_nonneg_left h2 hdpos.le
        _ = (∑ i, ∑ j, A i j * (x i - x j) ^ 2)
          * (d * (∑ i, yu i ^ 2 + ∑ i, yv i ^ 2)) := by
            ring
    rw [htwoR]
    exact hs1.trans hs2
  have hdot_split : Matrix.dotProduct x x
      ≤ ∑ i, (max (x i - m) 0) ^ 2 + ∑ i, (max (m - x i) 0) ^ 2 := by
    rw [hdotsum]; exact hnormsplit
  -- the case tree
  by_cases hMyu : 0 < ∑ i, (max (x i - m) 0) ^ 2
  · by_cases hMyv : 0 < ∑ i, (max (m - x i) 0) ^ 2
    · by_cases hprod : (∑ i, ∑ j, A i j
            * ((max (x i - m) 0) - (max (x j - m) 0)) ^ 2)
          * (∑ i, (max (m - x i) 0) ^ 2)
          ≤ (∑ i, ∑ j, A i j
            * ((max (m - x i) 0) - (max (m - x j) 0)) ^ 2)
          * (∑ i, (max (x i - m) 0) ^ 2)
      · -- both parts positive, the product test picks the positive part
        obtain ⟨S, t, ht, hSmem, hSne, hScne, hcond⟩ :=
          sweep_level_extract A hA hnn d hd hdpos (fun i => max (x i - m) 0)
            hyu hMyu
        refine ⟨S, hSne, hScne, Or.inl ⟨m + Real.sqrt t, fun i => ?_⟩, ?_⟩
        · rw [hSmem i]
          exact mem_of_posPart_sq ht i
        · exact le_trans hcond (hchain (fun i => max (x i - m) 0)
            (fun i => max (m - x i) 0) hprod hMyu hMvnn hdot_split hfused)
      · -- both parts positive, the product test picks the negative part
        obtain ⟨S, t, ht, hSmem, hSne, hScne, hcond⟩ :=
          sweep_level_extract A hA hnn d hd hdpos (fun i => max (m - x i) 0)
            hyv hMyv
        refine ⟨S, hSne, hScne, Or.inr ⟨m - Real.sqrt t, fun i => ?_⟩, ?_⟩
        · rw [hSmem i]
          exact mem_of_negPart_sq ht i
        · refine le_trans hcond (hchain (fun i => max (m - x i) 0)
            (fun i => max (x i - m) 0) ?_ hMyv hMunn ?_
            (by rw [add_comm]; exact hfused))
          · exact le_of_not_le hprod
          · rw [hdotsum]
            rw [add_comm]
            exact hnormsplit
    · -- Mv = 0: the positive part alone carries the norm
      have hMv0 : ∑ i, (max (m - x i) 0) ^ 2 = 0 :=
        le_antisymm (le_of_not_gt hMyv) hMvnn
      have hEvnn : 0 ≤ ∑ i, ∑ j, A i j
          * ((max (m - x i) 0) - (max (m - x j) 0)) ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hnn i j) (sq_nonneg _)
      obtain ⟨S, t, ht, hSmem, hSne, hScne, hcond⟩ :=
          sweep_level_extract A hA hnn d hd hdpos (fun i => max (x i - m) 0)
            hyu hMyu
      refine ⟨S, hSne, hScne, Or.inl ⟨m + Real.sqrt t, fun i => ?_⟩, ?_⟩
      · rw [hSmem i]
        exact mem_of_posPart_sq ht i
      · refine le_trans hcond (hchain (fun i => max (x i - m) 0)
          (fun i => max (m - x i) 0) ?_ hMyu hMvnn hdot_split hfused)
        rw [hMv0, mul_zero]
        exact mul_nonneg hEvnn hMunn
  · -- Mu = 0, so Mv > 0 by the norm split
    have hMu0 : ∑ i, (max (x i - m) 0) ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hMyu) hMunn
    have hMvpos : 0 < ∑ i, (max (m - x i) 0) ^ 2 := by
      have h1 : (0:ℝ) ≤ ∑ i, (max (m - x i) 0) ^ 2 := hMvnn
      have h2 : ∑ i, x i ^ 2 ≤ 0 + ∑ i, (max (m - x i) 0) ^ 2 := by
        simpa [hMu0] using hnormsplit
      have h3 : 0 < ∑ i, x i ^ 2 := by rw [← hdotsum]; exact hdotpos
      linarith
    have hEunn : 0 ≤ ∑ i, ∑ j, A i j
        * ((max (x i - m) 0) - (max (x j - m) 0)) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hnn i j) (sq_nonneg _)
    obtain ⟨S, t, ht, hSmem, hSne, hScne, hcond⟩ :=
          sweep_level_extract A hA hnn d hd hdpos (fun i => max (m - x i) 0)
            hyv hMvpos
    refine ⟨S, hSne, hScne, Or.inr ⟨m - Real.sqrt t, fun i => ?_⟩, ?_⟩
    · rw [hSmem i]
      exact mem_of_negPart_sq ht i
    · refine le_trans hcond (hchain (fun i => max (m - x i) 0)
        (fun i => max (x i - m) 0) ?_ hMvpos hMunn ?_
        (by rw [add_comm]; exact hfused))
      · rw [hMu0, mul_zero]
        exact mul_nonneg hEunn hMvnn
      · rw [hdotsum]
        rw [add_comm]
        exact hnormsplit

end SweepExtraction

end SpectralGraphTheory
