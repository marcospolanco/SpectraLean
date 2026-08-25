/-
  VariationalTransfer.lean

  Purpose
  -------
  The variational consumer of the congruence bridge: quadratic-form and
  Rayleigh-quotient statements transfer between the combinatorial
  Laplacian `L = D - A` and the symmetric normalized Laplacian
  `L_sym = I - D^{-1/2} A D^{-1/2}` through the proved identity
  `√D · L_sym · √D = L`
  (`degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`).

  This is the second consuming module for the `Normalized` interfaces
  (after `GraphTheory.Stationary`), addressing the downstream-reuse
  constraint recorded on the SGT radar. Every statement is proved from
  the center; no new axioms are admitted.

  The headline statement is the classical normalized Rayleigh quotient:
  for a nonzero test vector `y` with positive degrees,

    rayleigh L_sym (√D y) = (yᵀ L y) / ∑ i, deg i · y i²,

  the quotient form through which Cheeger-type and walk-mixing bounds
  on irregular graphs are conventionally stated; the regular-only
  Cheeger axioms (`GraphTheory.Cheeger`) cannot express it. PSD of the
  normalized Laplacian also transfers, giving the nonnegativity half of
  the normalized variational picture on arbitrary positive-degree
  graphs.

  Consumers unlocked: normalized Rayleigh bounds on irregular graphs;
  statement shapes for a future irregular Cheeger family; quadratic-form
  reuse of every combinatorial-Laplacian Dirichlet identity in the
  normalized world. **That named irregular-Cheeger consumer is delivered
  below (2026-08-25): the easy direction
  `cheeger_upper_bound_normalized` together with its degree-stretched
  cut-test-vector layer — this module's first theorem consumers.**

  Related modules: the transferred objects are defined in
  `Scaffold.Mathlib.GraphTheory.Spectral` (`quadForm`, `rayleigh`,
  `laplacian`, `laplacian_psd`) and
  `Scaffold.Mathlib.GraphTheory.Normalized` (`degreeSqrt`,
  `degreeInvSqrt`, `normalizedLaplacian`, the congruence identity).
-/

import Scaffold.Mathlib.GraphTheory.Normalized

open scoped Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## The congruence lemma for quadratic forms
-/

omit [DecidableEq V] in
/-- Quadratic forms are invariant under symmetric congruence:
`quadForm (P M P) y = quadForm M (P *ᵥ y)` when `P` is symmetric. This
is the generic engine behind every transfer below: the change of
variables `x = P y` in the quadratic form costs exactly one transpose,
which symmetry absorbs. -/
theorem quadForm_congr {P M : Matrix V V ℝ} (hP : P.IsSymm) (y : V → ℝ) :
    quadForm (P * M * P) y = quadForm M (P *ᵥ y) := by
  have h1 : (P * M * P) *ᵥ y = P *ᵥ (M *ᵥ (P *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have h2 : y ⬝ᵥ (P *ᵥ (M *ᵥ (P *ᵥ y)))
      = (y ᵥ* P) ⬝ᵥ (M *ᵥ (P *ᵥ y)) :=
    Matrix.dotProduct_mulVec _ _ _
  have h3 : y ᵥ* P = P *ᵥ y := by
    rw [← Matrix.mulVec_transpose, hP]
  simp only [quadForm, h1, h2, h3]

/-!
## Transfer between the combinatorial and normalized worlds
-/

/-- The diagonal degree square root acts entrywise:
`degreeSqrt A *ᵥ y = fun i => √(deg A i) * y i`. -/
theorem degreeSqrt_mulVec (A : WAdj (V := V)) (y : V → ℝ) (i : V) :
    (degreeSqrt A *ᵥ y) i = Real.sqrt (deg A i) * y i := by
  simp [degreeSqrt, Matrix.mulVec_diagonal]

/-- The diagonal degree square root is symmetric. -/
theorem degreeSqrt_isSymm (A : WAdj (V := V)) :
    (degreeSqrt A).IsSymm := by
  show (degreeSqrt A)ᵀ = degreeSqrt A
  rw [degreeSqrt, Matrix.diagonal_transpose]

/-- The Dirichlet form transfers through the congruence bridge: for
positive degrees, the combinatorial quadratic form of `y` is the
normalized quadratic form of the stretched vector `√D y`. Every
quadratic-form statement about `laplacian` (Dirichlet identity, PSD,
kernel pairing) becomes a statement about `normalizedLaplacian` on the
stretched vector by this theorem. -/
theorem quadForm_laplacian_eq_quadForm_normalizedLaplacian
    (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i) (y : V → ℝ) :
    quadForm (laplacian A) y
      = quadForm (normalizedLaplacian A) (degreeSqrt A *ᵥ y) := by
  rw [← degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt A hd,
    quadForm_congr (degreeSqrt_isSymm A) y]

/-- The Rayleigh denominator of the stretched vector is the
degree-weighted `ℓ²` norm squared: `⬝(√D y, √D y) = ∑ i, deg i · y i²`
(degrees nonnegative). -/
theorem dotProduct_degreeSqrt_mulVec (A : WAdj (V := V))
    (hdeg : ∀ i, 0 ≤ deg A i) (y : V → ℝ) :
    Matrix.dotProduct (degreeSqrt A *ᵥ y) (degreeSqrt A *ᵥ y)
      = ∑ i, deg A i * y i * y i := by
  have hentry : ∀ i : V,
      (Real.sqrt (deg A i) * y i) * (Real.sqrt (deg A i) * y i)
        = deg A i * y i * y i := by
    intro i
    rw [show deg A i * y i * y i
        = Real.sqrt (deg A i) * Real.sqrt (deg A i) * (y i * y i) from by
          rw [Real.mul_self_sqrt (hdeg i)]
          ring]
    ring
  simp only [Matrix.dotProduct, degreeSqrt_mulVec, hentry]

/-- Nonzero vectors stay nonzero under the degree stretch when all
degrees are positive. -/
theorem degreeSqrt_mulVec_ne_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) {y : V → ℝ} (hy : y ≠ 0) :
    degreeSqrt A *ᵥ y ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hy (funext hcon)
  intro h
  have hzero := congrFun h i
  rw [degreeSqrt_mulVec, Pi.zero_apply] at hzero
  rcases mul_eq_zero.mp hzero with hs | hy0
  · exact absurd hs (Real.sqrt_ne_zero'.mpr (hd i))
  · exact absurd hy0 hi

/-- **Normalized Rayleigh quotient transfer.** For a nonzero test
vector on a positive-degree graph,

  rayleigh L_sym (√D y) = (yᵀ L y) / ∑ i, deg i · y i²,

the classical normalized Rayleigh quotient: numerator transferred by
the congruence (`quadForm_laplacian_eq_quadForm_normalizedLaplacian`),
denominator degree-weighted
(`dotProduct_degreeSqrt_mulVec`). This is the variational interface
through which Cheeger-type bounds and mixing statements on irregular
graphs are stated; the regular-only Cheeger axioms of
`GraphTheory.Cheeger` cannot express it. -/
theorem rayleigh_normalizedLaplacian_degreeSqrt
    (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i) {y : V → ℝ}
    (hy : y ≠ 0) :
    rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ y)
      = quadForm (laplacian A) y / ∑ i, deg A i * y i * y i := by
  rw [rayleigh, if_neg (degreeSqrt_mulVec_ne_zero A hd hy),
    quadForm_laplacian_eq_quadForm_normalizedLaplacian A hd,
    dotProduct_degreeSqrt_mulVec A (fun i => le_of_lt (hd i))]

/-- Positive semidefiniteness transfers to the normalized Laplacian:
for symmetric nonnegative weights and positive degrees, every
quadratic form of `L_sym` is nonnegative. Proof: un-stretch `x` by the
inverse diagonal `1/√D` (an exact inverse by
`degreeSqrt_mul_degreeInvSqrt`), so the stretched form is a
combinatorial form, and apply `laplacian_psd`. -/
theorem normalizedLaplacian_psd (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) :
    ∀ x : V → ℝ, 0 ≤ quadForm (normalizedLaplacian A) x := by
  intro x
  have hstretch : degreeSqrt A *ᵥ (degreeInvSqrt A *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, degreeSqrt_mul_degreeInvSqrt A hd,
      Matrix.one_mulVec]
  have htransfer := quadForm_laplacian_eq_quadForm_normalizedLaplacian
    A hd (degreeInvSqrt A *ᵥ x)
  rw [← hstretch, ← htransfer]
  exact laplacian_psd A hA hnonneg _

/-!
## The irregular Cheeger upper bound (proved)

The module's own recorded purpose — "statement shapes for a future
irregular Cheeger family" — delivered for the easy direction
(`proposals/irregular-cheeger-variational-transfer.md`, Step 0 + Step 1,
2026-08-25). On arbitrary symmetric nonnegative *positive-degree* graphs
— no `d`-regularity, and no connectivity — the second eigenvalue of the
symmetric normalized Laplacian obeys the same classical bound as the
regular family:

  `secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A`.

The route reuses the regular proof's arithmetic verbatim; everything
genuinely new is the *test vector*. The regular easy direction
(`GraphTheory.Cheeger.cheeger_upper_bound`) tests at the volume-centered
cut indicator `cutTestVector A S`, orthogonal to `onesVec` only under
regularity. On irregular input the normalized Laplacian's kernel vector
is `√D · onesVec` (`normalizedLaplacian_mulVec_degreeSqrt_onesVec`), and
the correct test object is the *degree-stretched* cut indicator
`√D *ᵥ cutTestVector A S`:

- its orthogonality to the kernel vector is the degree-weighted sum
  `∑ i, deg A i * cutTestVector A S i = vol S * vol Sᶜ - vol Sᶜ * vol S`,
  which vanishes *without any regularity* — the volume identity the
  regular proof obtained from `vol_eq_of_regular` is exact here
  (`dotProduct_degreeSqrt_mulVec_cutTestVector`);
- its numerator is this module's own congruence engine composed with the
  regularity-free energy identity
  `quadForm_laplacian_cutTestVector` (`quadForm (laplacian A) x =
  boundary * (vol V)²`), giving
  `quadForm L_sym (√D *ᵥ x) = boundary A S * (vol V)²`;
- its denominator is `∑ i, deg A i * x i² = vol S * vol Sᶜ * vol V`
  (`dotProduct_degreeSqrt_mulVec_cutTestVector_self`).

The Rayleigh quotient is therefore the *same* `boundary · vol V /
(vol S · vol Sᶜ)` as the regular case, and the closing `min`-arithmetic
and infimum pass are the delivered proof's verbatim. The variational
step runs through the general-kernel `secondEval_le_rayleigh_of_ker`
(the `onesVec`-based `secondEval_le_rayleigh` provably cannot express
this: on the QA P₃ fixture the test vector is *not* orthogonal to
`onesVec`).

The hard direction (`φ²/2 ≤ λ₂` in the volume-weighted measure) is
*not* delivered here: the coarea/median machinery of
`GraphTheory.Cheeger` is built on the cardinality-volume equivalence
that regularity supplies, and its irregular re-derivation is priced as
its own multi-step program in the proposal (the original Cheeger
discharge's Step 1a/1b/1c precedent).
-/

/-- Orthogonality of the degree-stretched cut test vector to the
normalized Laplacian's kernel vector, *without regularity*: the
degree-weighted sum of the volume-centered cut indicator is
`vol S · vol Sᶜ − vol Sᶜ · vol S = 0` — the volume identity that the
regular proof could only obtain through `vol_eq_of_regular`, exact in
the weighted measure. -/
theorem dotProduct_degreeSqrt_mulVec_cutTestVector (A : WAdj (V := V))
    (hdeg : ∀ i, 0 ≤ deg A i) (S : Finset V) :
    Matrix.dotProduct (degreeSqrt A *ᵥ cutTestVector A S)
        (degreeSqrt A *ᵥ onesVec) = 0 := by
  have hentry : ∀ i : V,
      (degreeSqrt A *ᵥ cutTestVector A S) i * (degreeSqrt A *ᵥ onesVec) i
      = deg A i * cutTestVector A S i := by
    intro i
    simp only [degreeSqrt_mulVec, onesVec, mul_one]
    linear_combination Real.mul_self_sqrt (hdeg i) * cutTestVector A S i
  have hconv : ∑ i, deg A i * cutTestVector A S i
      = (∑ i in S, deg A i * vol A Sᶜ)
        + (∑ i in Sᶜ, deg A i * (-vol A S)) := by
    rw [← Finset.sum_add_sum_compl S
        (fun i => deg A i * cutTestVector A S i)]
    have h1 : ∑ i in S, deg A i * cutTestVector A S i
        = ∑ i in S, deg A i * vol A Sᶜ :=
      Finset.sum_congr rfl fun i hi => by rw [cutTestVector_apply, if_pos hi]
    have h2 : ∑ i in Sᶜ, deg A i * cutTestVector A S i
        = ∑ i in Sᶜ, deg A i * (-vol A S) :=
      Finset.sum_congr rfl fun i hi => by
        rw [cutTestVector_apply, if_neg (Finset.mem_compl.1 hi)]
    rw [h1, h2]
  have hf : ∀ T : Finset V, ∀ c : ℝ,
      ∑ i in T, deg A i * c = vol A T * c := by
    intro T c
    rw [← Finset.sum_mul]
    rfl
  rw [Matrix.dotProduct, Finset.sum_congr rfl (fun i _ => hentry i), hconv,
    hf S _, hf Sᶜ _]
  ring

/-- The degree-weighted norm of the cut test vector:
`⬝(√D x, √D x) = vol S · vol Sᶜ · vol V` for the volume-centered cut
indicator `x` (no regularity). -/
theorem dotProduct_degreeSqrt_mulVec_cutTestVector_self (A : WAdj (V := V))
    (hdeg : ∀ i, 0 ≤ deg A i) (S : Finset V) :
    Matrix.dotProduct (degreeSqrt A *ᵥ cutTestVector A S)
        (degreeSqrt A *ᵥ cutTestVector A S)
      = vol A S * vol A Sᶜ * vol A (Finset.univ : Finset V) := by
  have hentry : ∀ i : V,
      (degreeSqrt A *ᵥ cutTestVector A S) i
        * (degreeSqrt A *ᵥ cutTestVector A S) i
      = deg A i * (cutTestVector A S i * cutTestVector A S i) := by
    intro i
    simp only [degreeSqrt_mulVec]
    linear_combination Real.mul_self_sqrt (hdeg i)
      * (cutTestVector A S i * cutTestVector A S i)
  have hconv : ∑ i, deg A i * (cutTestVector A S i * cutTestVector A S i)
      = (∑ i in S, deg A i * (vol A Sᶜ * vol A Sᶜ))
        + (∑ i in Sᶜ, deg A i * (vol A S * vol A S)) := by
    rw [← Finset.sum_add_sum_compl S
      (fun i => deg A i * (cutTestVector A S i * cutTestVector A S i))]
    have h1 : ∑ i in S, deg A i * (cutTestVector A S i * cutTestVector A S i)
        = ∑ i in S, deg A i * (vol A Sᶜ * vol A Sᶜ) :=
      Finset.sum_congr rfl fun i hi => by
        rw [cutTestVector_apply, if_pos hi]
    have h2 : ∑ i in Sᶜ, deg A i * (cutTestVector A S i * cutTestVector A S i)
        = ∑ i in Sᶜ, deg A i * (vol A S * vol A S) :=
      Finset.sum_congr rfl fun i hi => by
        rw [cutTestVector_apply, if_neg (Finset.mem_compl.1 hi)]
        ring
    rw [h1, h2]
  have hf : ∀ T : Finset V, ∀ c : ℝ,
      ∑ i in T, deg A i * c = vol A T * c := by
    intro T c
    rw [← Finset.sum_mul]
    rfl
  rw [Matrix.dotProduct, Finset.sum_congr rfl (fun i _ => hentry i), hconv,
    hf S _, hf Sᶜ _, ← vol_compl A S]
  ring

/-- The degree-stretched cut test vector of a nonempty proper cut is
nonzero on positive-degree graphs (it takes the value `√(deg i) · vol Sᶜ`
on `S`, both factors positive). -/
theorem degreeSqrt_mulVec_cutTestVector_ne_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) {S : Finset V}
    (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    degreeSqrt A *ᵥ cutTestVector A S ≠ 0 := by
  obtain ⟨i, hi⟩ := hS
  intro h
  have h1 := congrFun h i
  simp only [degreeSqrt_mulVec, cutTestVector_apply, if_pos hi,
    Pi.zero_apply] at h1
  rw [mul_eq_zero] at h1
  rcases h1 with hs | hv
  · exact (Real.sqrt_ne_zero'.mpr (hd i)) hs
  · exact (ne_of_gt (vol_pos_of_pos_deg A hd hSc)) hv

/-- **The irregular cut-test-vector Rayleigh quotient.** For the degree-
stretched volume-centered cut indicator on a positive-degree graph,

  R_{L_sym}(√D x) = boundary S · vol V / (vol S · vol Sᶜ),

*the same quotient the regular family computes*
(`rayleigh_regularNormalizedLaplacian_cutTestVector`) — numerator by this
module's congruence engine composed with the regularity-free cut energy
identity, denominator by the degree-weighted norm above. -/
theorem rayleigh_normalizedLaplacian_degreeSqrt_cutTestVector
    (A : WAdj (V := V)) (hA : Matrix.IsSymm A) (hd : ∀ i, 0 < deg A i)
    {S : Finset V} (hS : S.Nonempty) (hSc : Sᶜ.Nonempty) :
    rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ cutTestVector A S)
      = boundary A S * vol A (Finset.univ : Finset V)
          / (vol A S * vol A Sᶜ) := by
  have hne := degreeSqrt_mulVec_cutTestVector_ne_zero A hd hS hSc
  have hvs := vol_pos_of_pos_deg A hd hS
  have hvsc := vol_pos_of_pos_deg A hd hSc
  have hex : ∃ i₀ : V, i₀ ∈ S := hS
  obtain ⟨i₀, -⟩ := hex
  have hvV : 0 < vol A (Finset.univ : Finset V) :=
    vol_pos_of_pos_deg A hd ⟨i₀, Finset.mem_univ i₀⟩
  rw [rayleigh, if_neg hne,
    ← quadForm_laplacian_eq_quadForm_normalizedLaplacian A hd
      (cutTestVector A S),
    quadForm_laplacian_cutTestVector A hA S,
    dotProduct_degreeSqrt_mulVec_cutTestVector_self A
      (fun i => le_of_lt (hd i)) S]
  field_simp
  ring

/-- **Cheeger upper bound for irregular graphs** — the easy direction of
the eigenvalue–conductance relationship on arbitrary symmetric
nonnegative positive-degree weighted graphs, with no regularity and no
connectivity hypothesis:

  `secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A`.

Source (classical background; this is a proof, not an admission):
- Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997,
  Chapter 2 (the `λ ≤ 2φ` half, at the volume-weighted conductance the
  irregular statement requires).

Statement differences: `cheegerConstant` is the shelf's volume-based
infimum (already general — no irregular restatement was needed, per the
proposal's Step-0 survey); the spectral side is the general
`normalizedLaplacian`, which agrees with `regularNormalizedLaplacian` on
the regular cone
(`normalizedLaplacian_eq_regularNormalizedLaplacian`), so the delivered
regular `cheeger_upper_bound` is neither replaced nor regressed.

Route: per nonempty proper cut `S`, the degree-stretched cut indicator
is orthogonal to the kernel vector `√D · onesVec` (the volume identity,
no regularity), so the general-kernel variational characterization
`secondEval_le_rayleigh_of_ker` bounds `λ₂` by the quotient
`boundary · vol V / (vol S · vol Sᶜ)`; since `min ≤ vol S, vol Sᶜ`, that
quotient is at most `2 · boundary / min = 2 · conductance S`, and the
per-cut bound passes to the infimum over all nonempty proper cuts. The
closing arithmetic and infimum pass are the delivered regular proof's
verbatim.

QA: `Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean` — the
genuinely-irregular P₃ fixture (degrees 1, 2, 1) with the conductance
computed by hand, the test-vector layer verified entrywise, the
spectral side bounded independently through the eigenpair witness
`![1, 0, -1]` at eigenvalue `1` (a route through the new general-kernel
lemma at a vector *not* orthogonal to `onesVec`), the regular-recovery
consistency check on K₂, and the degree-hypothesis fence (the all-zero
adjacency, where every conductance is junk-zero yet `λ₂ = 1`). -/
theorem cheeger_upper_bound_normalized (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V) :
    secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard ≤
      2 * cheegerConstant A := by
  classical
  have hLsym := normalizedLaplacian_symmetric A hA
  -- the per-cut bound: λ₂ ≤ 2 · conductance S for every nonempty proper S
  have hcut : ∀ S : Finset V, S.Nonempty → Sᶜ.Nonempty →
      secondEval (normalizedLaplacian A) hLsym hcard
        ≤ 2 * conductance A S := by
    intro S hS hSc
    have hvs := vol_pos_of_pos_deg A hd hS
    have hvsc := vol_pos_of_pos_deg A hd hSc
    have hex : ∃ i₀ : V, i₀ ∈ S := hS
    obtain ⟨i₀, -⟩ := hex
    have hvV : 0 < vol A (Finset.univ : Finset V) :=
      vol_pos_of_pos_deg A hd ⟨i₀, Finset.mem_univ i₀⟩
    -- the kernel vector is nonzero (positive degrees)
    have hwne : degreeSqrt A *ᵥ onesVec ≠ 0 := by
      intro h
      have h1 := congrFun h i₀
      simp only [degreeSqrt_mulVec, onesVec, mul_one,
        Pi.zero_apply] at h1
      exact (Real.sqrt_ne_zero'.mpr (hd i₀)) h1
    -- λ₂ ≤ R(√D · cut test vector) = boundary · vol V / (vol S · vol Sᶜ)
    have hle1 := secondEval_le_rayleigh_of_ker hLsym
      (normalizedLaplacian_psd A hA hnonneg hd) hwne
      (normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd) hcard
      (degreeSqrt_mulVec_cutTestVector_ne_zero A hd hS hSc)
      (dotProduct_degreeSqrt_mulVec_cutTestVector A
        (fun i => le_of_lt (hd i)) S)
    rw [rayleigh_normalizedLaplacian_degreeSqrt_cutTestVector A hA hd
      hS hSc] at hle1
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
      calc secondEval (normalizedLaplacian A) hLsym hcard
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
  have hdiv : secondEval (normalizedLaplacian A) hLsym hcard / 2
      ≤ cheegerConstant A := by
    rw [cheegerConstant]
    refine le_csInf hsetne ?_
    rintro c ⟨S, hS, hSc, rfl⟩
    exact (div_le_iff₀ two_pos).2 (by rw [mul_comm]; exact hcut S hS hSc)
  calc secondEval (normalizedLaplacian A) hLsym hcard
      = 2 * (secondEval (normalizedLaplacian A) hLsym hcard / 2) := by
        ring
    _ ≤ 2 * cheegerConstant A :=
        mul_le_mul_of_nonneg_left hdiv (by norm_num)

end SpectralGraphTheory
