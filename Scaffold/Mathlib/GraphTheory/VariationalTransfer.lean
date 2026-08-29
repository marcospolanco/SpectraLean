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

  **The family's algorithm-facing capstone (2026-08-26): the irregular
  Fiedler instantiation** — `fiedler_sweep_cut_normalized` composes the
  sweep-cut extraction with the normalized-Laplacian Fiedler interface
  (`fiedlerIndexNormalized`, `fiedlerVectorNormalized`, the
  `D^{-1/2}` pullback `fiedlerSweepVector`): on every connected
  symmetric nonnegative positive-degree graph, an explicit closed
  superlevel/sublevel cut of the sweep vector itself satisfies
  `conductance S ^ 2 ≤ 2 * λ₂ (L_sym)` — the object the
  spectral-partitioning algorithm computes, at the regular family's own
  `2λ₂/d` constant on the regular cone.

  Related modules: the transferred objects are defined in
  `Scaffold.Mathlib.GraphTheory.Spectral` (`quadForm`, `rayleigh`,
  `laplacian`, `laplacian_psd`) and
  `Scaffold.Mathlib.GraphTheory.Normalized` (`degreeSqrt`,
  `degreeInvSqrt`, `normalizedLaplacian`, the congruence identity).
-/

import Scaffold.Mathlib.GraphTheory.Normalized
import Scaffold.Mathlib.GraphTheory.Cheeger

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

/-!
## The irregular Cheeger hard direction (proved)

The deferred half of the irregular Cheeger pair
(`proposals/irregular-cheeger-variational-transfer.md`, delivered
2026-08-25/26): on arbitrary symmetric nonnegative *positive-degree*
graphs — no `d`-regularity, and no connectivity —

  `cheegerConstant A ^ 2 / 2 ≤ secondEval (normalizedLaplacian A)`.

The route is the volume-weighted re-derivation of the regular family's
Step-1a/1b/1c chain, whose machinery lives in `GraphTheory.Cheeger`'s
`VolumeHardDirection` section (the volume median, the
minority-conductance at volume strength, the degree-weighted co-area
core, the per-part bound consuming Component A verbatim, and the
weighted norm split), discharged to the spectrum through the new
general-kernel Courant–Fischer sInf form
`SpectralGraphTheory.secondEval_variational_of_ker` — the normalized
Laplacian is killed by `√D · onesVec`, not by the constants, on every
irregular graph, so the onesVec form cannot express the constraint set.
With the easy direction above, both Cheeger inequalities now hold on
the same irregular hypotheses, closing the last "regular graphs only"
caveat of the Cheeger family.

QA: `Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean`'s
hard-direction section — the P₃ headline pin joined to the easy
direction's independently pinned spectral bracket, the sweep instance
on the same test vector both directions consume, the K₂ regular
recovery through the cone agreement, and the signed-weights fence
isolating nonnegativity.
-/

/-- Mixed bilinear form of the degree-weighted inner product:
`⬝(√D y, √D z) = ∑ i, deg i · y i · z i` (degrees nonnegative). The
diagonal companion `dotProduct_degreeSqrt_mulVec` is the `z = y`
instance. -/
theorem dotProduct_degreeSqrt_mulVec_mixed (A : WAdj (V := V))
    (hdeg : ∀ i, 0 ≤ deg A i) (y z : V → ℝ) :
    Matrix.dotProduct (degreeSqrt A *ᵥ y) (degreeSqrt A *ᵥ z)
      = ∑ i, deg A i * y i * z i := by
  have hentry : ∀ i : V,
      (Real.sqrt (deg A i) * y i) * (Real.sqrt (deg A i) * z i)
        = deg A i * y i * z i := by
    intro i
    rw [show deg A i * y i * z i
        = Real.sqrt (deg A i) * Real.sqrt (deg A i) * (y i * z i) from by
          rw [Real.mul_self_sqrt (hdeg i)]
          ring]
    ring
  simp only [Matrix.dotProduct, degreeSqrt_mulVec, hentry]

/-- The onesVec pairing of the degree-weighted inner product: pairing
the stretched vector against the stretched constants is the
degree-weighted sum — the constraint the irregular variational set
imposes on the un-stretched vector. -/
theorem dotProduct_degreeSqrt_mulVec_onesVec (A : WAdj (V := V))
    (hdeg : ∀ i, 0 ≤ deg A i) (y : V → ℝ) :
    Matrix.dotProduct (degreeSqrt A *ᵥ y)
        (degreeSqrt A *ᵥ (onesVec : V → ℝ))
      = ∑ i, deg A i * y i := by
  rw [dotProduct_degreeSqrt_mulVec_mixed A hdeg y (onesVec : V → ℝ)]
  exact Finset.sum_congr rfl fun i _ => by simp [onesVec]

/-- **Sweep lemma, irregular form** (the Cheeger hard direction at
test-vector level): on any symmetric nonnegative positive-degree
graph, every nonzero degree-weighted zero-sum `f` has
`φ²/2 ≤ R_{L_sym}(√D f)`. The volume median
(`exists_median_vol`) routes both parts to their volume-minority sides
(so the degree-weighted co-area core applies to each), the per-part
bounds sum through the regular family's fused contraction verbatim
(whose cross-edge slack pays for carrying both parts), the weighted
norm split carries the full degree-weighted norm, and the
normalization `R_{L_sym}(√D f) = quadForm L f / ∑ deg f²`
(`rayleigh_normalizedLaplacian_degreeSqrt` + `laplacian_quadForm`)
turns `φ² · ∑ deg f² ≤ E'(f)` into the claimed `φ²/2` with nothing
lost anywhere in the chain.

QA: `SpectralGraphTheory.QA.ichv_sweep_edge_QA` (on `K₂`, `1/2 ≤ 2`
against the independently pinned `λ₂(L_sym) = 2`) and the `P₃` sweep
instance `SpectralGraphTheory.QA.ichv_sweep_p3_QA` (the same cut test
vector both directions of the pair consume, `1/2 ≤ 4/3`). -/
theorem cheeger_sweep_normalized (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i) {f : V → ℝ}
    (hf0 : f ≠ 0) (horth : ∑ i, deg A i * f i = 0) :
    cheegerConstant A ^ 2 / 2
      ≤ rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ f) := by
  obtain ⟨m, hup, hlow⟩ := exists_median_vol A hnn f
  have hyu : ∀ t : ℝ, 0 < t →
      2 * vol A (Finset.univ.filter
        (fun i => t ≤ (max (f i - m) 0) ^ 2)) ≤ vol A (Finset.univ : Finset V) :=
    fun t ht => minority_posPart_vol hnn hup t ht
  have hyv : ∀ t : ℝ, 0 < t →
      2 * vol A (Finset.univ.filter
        (fun i => t ≤ (max (m - f i) 0) ^ 2)) ≤ vol A (Finset.univ : Finset V) :=
    fun t ht => minority_negPart_vol hnn hlow t ht
  have hu := hardDirection_perPart_vol A hA hnn hd
    (fun i => max (f i - m) 0) (fun t ht => hyu t ht)
  have hv := hardDirection_perPart_vol A hA hnn hd
    (fun i => max (m - f i) 0) (fun t ht => hyv t ht)
  have hc := sum_edgeWeight_sq_posPart_add_sq_negPart_le A hnn m f
  have hn := median_parts_norm_vol A hnn (m := m) horth
  -- the two per-part bounds sum, through the fused contraction, into E'
  have hsum : cheegerConstant A ^ 2 * (∑ i, deg A i * f i ^ 2)
      ≤ ∑ i, ∑ j, A i j * (f i - f j) ^ 2 := by
    calc cheegerConstant A ^ 2 * (∑ i, deg A i * f i ^ 2)
        ≤ cheegerConstant A ^ 2
            * (∑ i, deg A i * (max (f i - m) 0) ^ 2
              + ∑ i, deg A i * (max (m - f i) 0) ^ 2) := by
              refine mul_le_mul_of_nonneg_left hn ?_
              exact pow_nonneg (cheegerConstant_nonneg A hnn) 2
      _ = cheegerConstant A ^ 2 * ∑ i, deg A i * (max (f i - m) 0) ^ 2
          + cheegerConstant A ^ 2 * ∑ i, deg A i * (max (m - f i) 0) ^ 2 := by
          ring
      _ ≤ ∑ i, ∑ j, A i j * (max (f i - m) 0 - max (f j - m) 0) ^ 2
          + ∑ i, ∑ j, A i j * (max (m - f i) 0 - max (m - f j) 0) ^ 2 :=
          add_le_add hu hv
      _ ≤ ∑ i, ∑ j, A i j * (f i - f j) ^ 2 := hc
  -- normalization and division
  have hR := rayleigh_normalizedLaplacian_degreeSqrt A hd hf0
  have hQ := laplacian_quadForm A hA f
  have hWpos : 0 < ∑ i, deg A i * f i * f i := by
    obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hf0 (funext hcon)
    have hnW : ∀ j ∈ (Finset.univ : Finset V), 0 ≤ deg A j * f j * f j := by
      intro j _
      calc deg A j * f j * f j = deg A j * (f j * f j) := by ring
        _ ≥ 0 := mul_nonneg (hd j).le (mul_self_nonneg (f j))
    have hpos : 0 < deg A i * f i * f i := by
      calc deg A i * f i * f i = deg A i * (f i * f i) := by ring
        _ > 0 := mul_pos (hd i) (mul_self_pos.2 hi)
    exact Finset.sum_pos' hnW ⟨i, Finset.mem_univ i, hpos⟩
  have hW : ∑ i, deg A i * f i * f i = ∑ i, deg A i * f i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  rw [hR, hQ, div_le_div_iff₀ two_pos hWpos, hW]
  calc cheegerConstant A ^ 2 * ∑ i, deg A i * f i ^ 2
      ≤ ∑ i, ∑ j, A i j * (f i - f j) ^ 2 := hsum
    _ = ((∑ i, ∑ j, A i j * (f i - f j) ^ 2) / 2) * 2 := by ring

/-- Cheeger lower bound for arbitrary positive-degree weighted graphs:
the squared conductance controls the second-smallest eigenvalue of the
symmetric normalized Laplacian from below, `φ(G)² / 2 ≤ λ₂(L_sym)`,
with no regularity and no connectivity — the hard-direction sibling of
`cheeger_upper_bound_normalized` above, on exactly its hypotheses.

Source:
- Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997,
  Chapter 2 (the volume-weighted form of Theorem 2.2's lower bound;
  section-level locator per the standing citation policy).

Route: `secondEval_variational_of_ker` at the true kernel vector
`√D · onesVec` reduces the spectral claim to the sweep lemma at every
admissible vector; the un-stretched `f := (1/√D) x` of an orthogonal
`x` has degree-weighted zero sum by
`dotProduct_degreeSqrt_mulVec_onesVec`, and the sInf set's
nonemptiness is witnessed by the easy direction's own cut test vector
(`dotProduct_degreeSqrt_mulVec_cutTestVector` is exactly its
orthogonality).

QA: exercised by `SpectralGraphTheory.QA.ichv_p3_hard_bound_QA` and
`SpectralGraphTheory.QA.ichv_k2_regular_recovery_QA` in
`Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean`, and fenced by
`SpectralGraphTheory.QA.ichv_signed_fence_QA` (symmetric signed
positive-degree input refuting the nonnegativity-dropped conclusion). -/
theorem cheeger_lower_bound_normalized (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V) :
    cheegerConstant A ^ 2 / 2 ≤
      secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard := by
  have hker := normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd
  obtain ⟨u, v, huv⟩ : ∃ u v : V, u ≠ v := by
    have h1 : 1 < (Finset.univ : Finset V).card := by
      rw [Finset.card_univ]
      omega
    obtain ⟨x, y, -, -, hxy⟩ := Finset.one_lt_card_iff.1 h1
    exact ⟨x, y, hxy⟩
  have honesne : (onesVec : V → ℝ) ≠ 0 := by
    intro h
    have h1 : (1 : ℝ) = 0 := congrFun h u
    simp at h1
  have hwne : degreeSqrt A *ᵥ (onesVec : V → ℝ) ≠ 0 :=
    degreeSqrt_mulVec_ne_zero A hd honesne
  rw [secondEval_variational_of_ker
    (normalizedLaplacian_symmetric A hA)
    (normalizedLaplacian_psd A hA hnn hd) hwne hker hcard]
  refine le_csInf ?_ ?_
  · -- the sInf set is nonempty: the easy direction's cut test vector
    have hSne : ({u} : Finset V).Nonempty := Finset.singleton_nonempty u
    have hScne : ({u} : Finset V)ᶜ.Nonempty := ⟨v, by
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact huv.symm⟩
    refine ⟨rayleigh (normalizedLaplacian A)
      (degreeSqrt A *ᵥ cutTestVector A {u}),
      ⟨degreeSqrt A *ᵥ cutTestVector A {u},
        degreeSqrt_mulVec_cutTestVector_ne_zero A hd hSne hScne,
        dotProduct_degreeSqrt_mulVec_cutTestVector A
          (fun i => (hd i).le) {u}, rfl⟩⟩
  · rintro r ⟨x, hx0, hxorth, rfl⟩
    -- un-stretch: f := (1/√D) x, so √D f = x
    have hxf : degreeSqrt A *ᵥ (degreeInvSqrt A *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, degreeSqrt_mul_degreeInvSqrt A hd,
        Matrix.one_mulVec]
    have hf0 : degreeInvSqrt A *ᵥ x ≠ 0 := by
      intro h
      rw [h, Matrix.mulVec_zero] at hxf
      exact hx0 hxf.symm
    have horthf : ∑ i, deg A i * (degreeInvSqrt A *ᵥ x) i = 0 := by
      rw [← dotProduct_degreeSqrt_mulVec_onesVec A fun i => (hd i).le, hxf]
      exact hxorth
    rw [← hxf]
    exact cheeger_sweep_normalized A hA hnn hd hf0 horthf

/-!
### The irregular sweep-cut extraction (proved)

The volume-weighted analogue of the regular family's
`cheeger_sweep_cut` (the median assembly of
`proposals/sweep-cut-extraction.md`, delivered 2026-08-26 for the
irregular family): the hard direction `cheeger_lower_bound_normalized`
bounds the conductance *infimum*; the theorem below exhibits an
explicit **closed superlevel or sublevel set of the test vector
itself** — a member of the sweep family the spectral-partitioning
algorithm actually enumerates — at the same constant. On irregular
input, with the volume median (`exists_median_vol`) routing both
median parts to their volume-minority sides and
`GraphTheory.Cheeger.sweep_level_extract_vol` extracting the per-part
witness level set, every nonzero degree-weighted zero-sum `f` has a
swept nonempty proper cut `S` with

  `conductance A S ^ 2 ≤ 2 * R_{L_sym}(√D f)`.

No regularity, no connectivity, no cardinality hypothesis — exactly
the hard direction's own constraint shape (`∑ i, deg A i * f i = 0`,
the un-stretched form of orthogonality to the true kernel vector
`√D · onesVec`).
-/

/-- **The sweep-cut theorem, irregular median assembly.** For any
nonzero degree-weighted zero-sum `f` on a symmetric nonnegative
positive-degree graph, there is a nonempty proper cut which is a
**closed superlevel or sublevel set of `f` itself** — a member of the
sweep family the spectral-partitioning algorithm actually enumerates —
with

`conductance A S ^ 2 ≤ 2 * rayleigh (normalizedLaplacian A) (√D f)`.

Same constant as `cheeger_sweep_normalized` (which bounds the
conductance *infimum* over all cuts), but the witness is explicit: a
swept level set of the test vector. Route: the volume median
(`exists_median_vol`, `minority_posPart_vol`/`minority_negPart_vol`
supply `sweep_level_extract_vol`'s hypothesis verbatim for both
parts), the product test selecting which part's extraction to run
(with degenerate single-part cases when the other part vanishes), the
fused contraction (`sum_edgeWeight_sq_posPart_add_sq_negPart_le` —
already degree-weighted, consumed verbatim), the weighted norm split
(`median_parts_norm_vol`), and the Step-1a normalization
(`rayleigh_normalizedLaplacian_degreeSqrt` + `laplacian_quadForm`:
`2 * R_{L_sym}(√D f) = E'(f) / ∑ i, deg A i * f i ^ 2`). The level
membership of the extracted part-sets converts to `f`-level sets
through `mem_of_posPart_sq`/`mem_of_negPart_sq` at the offset `√t`.

Trust level: hard crust; nothing axiom-backed.

QA: `SpectralGraphTheory.QA.vsc_cut_p3_QA` (the `P₃` instantiation at
the pair's shared cut test vector, joined to the file's pinned
Rayleigh value), `SpectralGraphTheory.QA.vsc_cut_edge_QA` (the `K₂`
regular recovery against the pinned `λ₂ = 2`), and
`SpectralGraphTheory.QA.vsc_cut_orth_dropped_refuted_QA` (the
degree-weighted zero-sum fence: `K₂` at `f = ![1, 2]`, every swept
nonempty proper cut has conductance `1` while `2 * R = 2/5`) in
`Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean`. -/
theorem cheeger_sweep_cut_normalized (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) {f : V → ℝ}
    (hf0 : f ≠ 0) (horth : ∑ i, deg A i * f i = 0) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ f i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ f i ≤ t)) ∧
      conductance A S ^ 2
        ≤ 2 * rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ f) := by
  obtain ⟨m, hup, hlow⟩ := exists_median_vol A hnn f
  have hyu : ∀ t : ℝ, 0 < t →
      2 * vol A (Finset.univ.filter
        (fun i => t ≤ (max (f i - m) 0) ^ 2))
        ≤ vol A (Finset.univ : Finset V) :=
    fun t ht => minority_posPart_vol hnn hup t ht
  have hyv : ∀ t : ℝ, 0 < t →
      2 * vol A (Finset.univ.filter
        (fun i => t ≤ (max (m - f i) 0) ^ 2))
        ≤ vol A (Finset.univ : Finset V) :=
    fun t ht => minority_negPart_vol hnn hlow t ht
  have hMunn : 0 ≤ ∑ i, deg A i * (max (f i - m) 0) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (hd i)) (sq_nonneg _)
  have hMvnn : 0 ≤ ∑ i, deg A i * (max (m - f i) 0) ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (le_of_lt (hd i)) (sq_nonneg _)
  have hfused := sum_edgeWeight_sq_posPart_add_sq_negPart_le A hnn m f
  have hn := median_parts_norm_vol A hnn (m := m) horth
  -- the weighted norm of f is positive (f nonzero, degrees positive)
  have hWfpos : 0 < ∑ i, deg A i * f i ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i : V, f i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hf0 (funext hcon)
    have hnW : ∀ j ∈ (Finset.univ : Finset V),
        0 ≤ deg A j * f j ^ 2 := fun j _ =>
      mul_nonneg (le_of_lt (hd j)) (sq_nonneg _)
    have hpos : 0 < deg A i * (f i * f i) :=
      mul_pos (hd i) (mul_self_pos.2 hi)
    have hpos' : 0 < deg A i * f i ^ 2 := by
      rw [pow_two]
      exact hpos
    exact Finset.sum_pos' hnW ⟨i, Finset.mem_univ i, hpos'⟩
  -- the closing normalization: 2 * R_{L_sym}(√D f) = E'(f) / W_f
  have htwoR : 2 * rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ f)
      = (∑ i, ∑ j, A i j * (f i - f j) ^ 2)
        / (∑ i, deg A i * f i * f i) := by
    rw [rayleigh_normalizedLaplacian_degreeSqrt A hd hf0,
      laplacian_quadForm A hA f]
    ring
  have hWf : ∑ i, deg A i * f i * f i = ∑ i, deg A i * f i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by ring
  -- the shared numeric chain
  have hchain : ∀ yu yv : V → ℝ,
      ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
          * (∑ i, deg A i * yv i ^ 2)
        ≤ (∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (∑ i, deg A i * yu i ^ 2)) →
      0 < ∑ i, deg A i * yu i ^ 2 → 0 ≤ ∑ i, deg A i * yv i ^ 2 →
      ∑ i, deg A i * f i ^ 2
        ≤ ∑ i, deg A i * yu i ^ 2 + ∑ i, deg A i * yv i ^ 2 →
      ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
          + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
      ≤ ∑ i, ∑ j, A i j * (f i - f j) ^ 2 →
      (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
          / (∑ i, deg A i * yu i ^ 2)
        ≤ 2 * rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ f) := by
    intro yu yv hprod hMyu hMvnn hsplit hfus
    have hEunn : 0 ≤ ∑ i, ∑ j, A i j * (yu i - yu j) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hnn i j) (sq_nonneg _)
    have hEvnn : 0 ≤ ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hnn i j) (sq_nonneg _)
    have hs1 : (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
          / (∑ i, deg A i * yu i ^ 2)
        ≤ ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          / (∑ i, deg A i * yu i ^ 2
            + ∑ i, deg A i * yv i ^ 2) := by
      rw [div_le_div_iff₀ hMyu (by linarith : (0:ℝ)
        < ∑ i, deg A i * yu i ^ 2 + ∑ i, deg A i * yv i ^ 2)]
      calc (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            * (∑ i, deg A i * yu i ^ 2
              + ∑ i, deg A i * yv i ^ 2)
          = (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
              * (∑ i, deg A i * yu i ^ 2)
            + (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
              * (∑ i, deg A i * yv i ^ 2) := by
              ring
        _ ≤ (∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
              * (∑ i, deg A i * yu i ^ 2)
            + (∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
              * (∑ i, deg A i * yu i ^ 2) := by
              exact add_le_add_left hprod _
        _ = ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (∑ i, deg A i * yu i ^ 2) := by
            ring
    have hs2 : ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          / (∑ i, deg A i * yu i ^ 2 + ∑ i, deg A i * yv i ^ 2)
        ≤ (∑ i, ∑ j, A i j * (f i - f j) ^ 2)
          / (∑ i, deg A i * f i * f i) := by
      rw [div_le_div_iff₀ (by linarith : (0:ℝ)
          < ∑ i, deg A i * yu i ^ 2 + ∑ i, deg A i * yv i ^ 2)
        (by rw [hWf]; exact hWfpos)]
      have h1 : ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (∑ i, deg A i * f i * f i)
        ≤ ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (∑ i, deg A i * yu i ^ 2
            + ∑ i, deg A i * yv i ^ 2) := by
        rw [hWf]
        exact mul_le_mul_of_nonneg_left hsplit (add_nonneg hEunn hEvnn)
      have h2 : ((∑ i, ∑ j, A i j * (yu i - yu j) ^ 2)
            + ∑ i, ∑ j, A i j * (yv i - yv j) ^ 2)
          * (∑ i, deg A i * yu i ^ 2 + ∑ i, deg A i * yv i ^ 2)
        ≤ (∑ i, ∑ j, A i j * (f i - f j) ^ 2)
          * (∑ i, deg A i * yu i ^ 2
            + ∑ i, deg A i * yv i ^ 2) :=
          mul_le_mul_of_nonneg_right hfus
            (add_nonneg hMyu.le hMvnn)
      exact le_trans h1 h2
    rw [htwoR]
    exact hs1.trans hs2
  -- the case tree
  by_cases hMyu : 0 < ∑ i, deg A i * (max (f i - m) 0) ^ 2
  · by_cases hMyv : 0 < ∑ i, deg A i * (max (m - f i) 0) ^ 2
    · by_cases hprod : (∑ i, ∑ j, A i j
            * ((max (f i - m) 0) - (max (f j - m) 0)) ^ 2)
          * (∑ i, deg A i * (max (m - f i) 0) ^ 2)
        ≤ (∑ i, ∑ j, A i j
            * ((max (m - f i) 0) - (max (m - f j) 0)) ^ 2)
          * (∑ i, deg A i * (max (f i - m) 0) ^ 2)
      · -- both parts positive, the product test picks the positive part
        obtain ⟨S, t, ht, hSmem, hSne, hScne, hcond⟩ :=
          sweep_level_extract_vol A hA hnn hd (fun i => max (f i - m) 0)
            hyu hMyu
        refine ⟨S, hSne, hScne, Or.inl ⟨m + Real.sqrt t, fun i => ?_⟩, ?_⟩
        · rw [hSmem i]
          exact mem_of_posPart_sq ht i
        · exact le_trans hcond (hchain (fun i => max (f i - m) 0)
            (fun i => max (m - f i) 0) hprod hMyu hMvnn hn hfused)
      · -- both parts positive, the product test picks the negative part
        obtain ⟨S, t, ht, hSmem, hSne, hScne, hcond⟩ :=
          sweep_level_extract_vol A hA hnn hd (fun i => max (m - f i) 0)
            hyv hMyv
        refine ⟨S, hSne, hScne, Or.inr ⟨m - Real.sqrt t, fun i => ?_⟩, ?_⟩
        · rw [hSmem i]
          exact mem_of_negPart_sq ht i
        · refine le_trans hcond (hchain (fun i => max (m - f i) 0)
            (fun i => max (f i - m) 0) ?_ hMyv hMunn ?_
            (by rw [add_comm]; exact hfused))
          · exact le_of_not_le hprod
          · rw [add_comm]
            exact hn
    · -- Mv = 0: the positive part alone carries the norm
      have hMv0 : ∑ i, deg A i * (max (m - f i) 0) ^ 2 = 0 :=
        le_antisymm (le_of_not_gt hMyv) hMvnn
      have hEvnn : 0 ≤ ∑ i, ∑ j, A i j
          * ((max (m - f i) 0) - (max (m - f j) 0)) ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
          mul_nonneg (hnn i j) (sq_nonneg _)
      obtain ⟨S, t, ht, hSmem, hSne, hScne, hcond⟩ :=
          sweep_level_extract_vol A hA hnn hd (fun i => max (f i - m) 0)
            hyu hMyu
      refine ⟨S, hSne, hScne, Or.inl ⟨m + Real.sqrt t, fun i => ?_⟩, ?_⟩
      · rw [hSmem i]
        exact mem_of_posPart_sq ht i
      · refine le_trans hcond (hchain (fun i => max (f i - m) 0)
          (fun i => max (m - f i) 0) ?_ hMyu hMvnn hn hfused)
        rw [hMv0, mul_zero]
        exact mul_nonneg hEvnn hMunn
  · -- Mu = 0, so Mv > 0 by the norm split
    have hMu0 : ∑ i, deg A i * (max (f i - m) 0) ^ 2 = 0 :=
      le_antisymm (le_of_not_gt hMyu) hMunn
    have hMvpos : 0 < ∑ i, deg A i * (max (m - f i) 0) ^ 2 := by
      have h1 : (0:ℝ) ≤ ∑ i, deg A i * (max (m - f i) 0) ^ 2 := hMvnn
      have h2 : ∑ i, deg A i * f i ^ 2
          ≤ 0 + ∑ i, deg A i * (max (m - f i) 0) ^ 2 := by
        simpa [hMu0] using hn
      linarith
    have hEunn : 0 ≤ ∑ i, ∑ j, A i j
        * ((max (f i - m) 0) - (max (f j - m) 0)) ^ 2 :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (hnn i j) (sq_nonneg _)
    obtain ⟨S, t, ht, hSmem, hSne, hScne, hcond⟩ :=
          sweep_level_extract_vol A hA hnn hd (fun i => max (m - f i) 0)
            hyv hMvpos
    refine ⟨S, hSne, hScne, Or.inr ⟨m - Real.sqrt t, fun i => ?_⟩, ?_⟩
    · rw [hSmem i]
      exact mem_of_negPart_sq ht i
    · refine le_trans hcond (hchain (fun i => max (m - f i) 0)
        (fun i => max (f i - m) 0) ?_ hMvpos hMunn ?_
        (by rw [add_comm]; exact hfused))
      · rw [hMu0, mul_zero]
        exact mul_nonneg hEunn hMvnn
      · rw [add_comm]
        exact hn

/-!
## The connectivity transfer: `0 < λ₂ (L_sym) ↔ connected`

The irregular family's own recorded follow-on (delivered 2026-08-26,
pure hard crust): Fiedler's algebraic-connectivity certificate in the
volume-weighted world. On every symmetric nonnegative positive-degree
graph with at least two vertices, the second eigenvalue of
`normalizedLaplacian A` is positive *exactly when* the support graph is
connected — the hypothesis every downstream consumer of the delivered
Cheeger pair (`cheeger_upper_bound_normalized`,
`cheeger_lower_bound_normalized`) needs to make its gap meaningful.

The entry the proposal names — the kernel-vector layer: the kernel
characterization `normalizedLaplacian_mulVec_eq_zero_iff` identifies
`ker L_sym` as the line spanned by `√D · onesVec` (the stretched
constants), through the left-multiplied congruence
`√D · L_sym = L · D^{-1/2}` and the electrical program's
`laplacian_mulVec_eq_zero_iff_exists_const`. Both directions of the
equivalence then follow: connected input collapses the kernel to one
line, so the double-bottom multiplicity pin
(`exists_ne_eigvalOf_of_evals_head_eq`) contradicts orthonormality
(the Fiedler mirror of `lambda2_pos_of_connected`); disconnected input
admits a component indicator in the combinatorial kernel, whose
degree-stretched, Gram–Schmidt-orthogonalized image is a nonzero
Rayleigh-zero test vector orthogonal to `√D · onesVec`, forcing
`λ₂ = 0` through the delivered general-kernel engine
`secondEval_le_rayleigh_of_ker`.

The consumer corollary `cheegerConstant_pos_of_connected` joins the
delivered easy direction: on connected irregular graphs the Cheeger
constant is positive — the pair's content made explicit.
-/

/-- The left-multiplied congruence `√D · L_sym = L · D^{-1/2}`: the
companion of `normalizedLaplacian_mul_degreeSqrt` (the right-multiplied
form), through which the normalized Laplacian's *kernel* is located —
multiply the combinatorial kernel equation by `√D`. -/
theorem degreeSqrt_mul_normalizedLaplacian (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    degreeSqrt A * normalizedLaplacian A
      = laplacian A * degreeInvSqrt A := by
  have h1 : degreeSqrt A * normalizedLaplacian A
      = degreeSqrt A * (normalizedLaplacian A
        * (degreeSqrt A * degreeInvSqrt A)) := by
    rw [degreeSqrt_mul_degreeInvSqrt A hd, Matrix.mul_one]
  rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt A hd]

/-- The kernel-cone lift: every combinatorial kernel vector stretches
into the normalized kernel (`L *ᵥ y = 0 → L_sym *ᵥ (√D *ᵥ y) = 0`),
by the right-multiplied congruence. Pure matrix algebra; the
combinatorial content stays in `laplacian`. -/
theorem normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero
    (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i) {y : V → ℝ}
    (hy : laplacian A *ᵥ y = 0) :
    normalizedLaplacian A *ᵥ (degreeSqrt A *ᵥ y) = 0 := by
  rw [Matrix.mulVec_mulVec, normalizedLaplacian_mul_degreeSqrt A hd,
    ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero]

/-- **The kernel characterization**: on a connected graph with symmetric
nonnegative weights and positive degrees, the normalized Laplacian's
kernel is exactly the line spanned by the stretched constants
`√D · onesVec` (not by the constants themselves — the structural fact
separating the irregular from the regular variational picture, now in
iff form). The forward direction multiplies the kernel equation by
`√D` (the left-multiplied congruence), un-stretches by `1/√D`, and
applies the electrical program's combinatorial characterization; the
reverse is the delivered kernel-vector lemma. -/
theorem normalizedLaplacian_mulVec_eq_zero_iff (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (hconn : (supportGraph A hA).Connected) (x : V → ℝ) :
    normalizedLaplacian A *ᵥ x = 0
      ↔ ∃ c : ℝ, x = c • (degreeSqrt A *ᵥ onesVec) := by
  constructor
  · intro hx
    have h0 : laplacian A *ᵥ (degreeInvSqrt A *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec, ← degreeSqrt_mul_normalizedLaplacian A hd,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    obtain ⟨c, hc⟩ := laplacian_mulVec_eq_zero_iff_exists_const A hA hnn
      hconn _ |>.1 h0
    have hxrec : degreeSqrt A *ᵥ (degreeInvSqrt A *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, degreeSqrt_mul_degreeInvSqrt A hd,
        Matrix.one_mulVec]
    have hconst : (fun _ => c : V → ℝ) = c • onesVec := by
      funext i; simp [onesVec]
    refine ⟨c, ?_⟩
    rw [← hxrec, hc, hconst, Matrix.mulVec_smul_assoc]
  · rintro ⟨c, rfl⟩
    rw [Matrix.mulVec_smul_assoc, smul_eq_zero]
    exact Or.inr (normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd)

omit [DecidableEq V] in
/-- A nonzero vector has positive self dot product (support lemma for
the orthonormality and Gram–Schmidt steps below). -/
private theorem dotProduct_pos_of_ne_zero {w : V → ℝ}
    (hw : w ≠ 0) : 0 < Matrix.dotProduct w w := by
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw (funext hcon)
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
    ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩

omit [DecidableEq V] in
/-- Scaling both arguments of a dot product factors out
(support lemma). -/
private theorem dotProduct_smul_smul_self {w : V → ℝ}
    (c d : ℝ) :
    Matrix.dotProduct (c • w) (d • w) = c * d * Matrix.dotProduct w w := by
  have key : ∀ j : V, c * w j * (d * w j) = c * d * (w j * w j) :=
    fun j => by ring
  simp only [Matrix.dotProduct, Pi.smul_apply, smul_eq_mul, key,
    ← Finset.mul_sum]

/-- The stretched constants are nonzero whenever some degree is
positive and the graph is nonempty (support lemma). -/
private theorem degreeSqrt_mulVec_onesVec_ne_zero (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V) :
    degreeSqrt A *ᵥ (onesVec : V → ℝ) ≠ 0 := by
  obtain ⟨u⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
  intro h
  have h0 := congrFun h u
  rw [degreeSqrt_mulVec_apply A onesVec u] at h0
  simp only [onesVec, mul_one] at h0
  exact (Real.sqrt_ne_zero'.2 (hd u)) h0

/-- **Fiedler's algebraic-connectivity certificate, normalized form:**
on a connected graph with symmetric nonnegative weights and positive
degrees, `0 < λ₂ (L_sym)`. The Fiedler mirror of the delivered
combinatorial `lambda2_pos_of_connected`: PSD pins every eigenbasis
eigenvalue below by zero, so a nonpositive `λ₂` forces a double bottom
at `0`; the multiplicity pin yields two orthonormal eigenbasis vectors
in the kernel; but the kernel is exactly the stretched-constant line
(`normalizedLaplacian_mulVec_eq_zero_iff`), and two orthonormal
vectors cannot share a line. Load-bearing on the PSD transfer, both
multiplicity pins, and the kernel characterization at once. -/
theorem secondEval_normalizedLaplacian_pos_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) :
    0 < secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard := by
  have hLsym := normalizedLaplacian_symmetric A hA
  have hpsd := normalizedLaplacian_psd A hA hnn hd
  have hwne := degreeSqrt_mulVec_onesVec_ne_zero A hd hcard
  have hwker : normalizedLaplacian A *ᵥ
      (degreeSqrt A *ᵥ (onesVec : V → ℝ)) = 0 :=
    normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd
  have hwwpos : 0 < Matrix.dotProduct
      (degreeSqrt A *ᵥ (onesVec : V → ℝ))
      (degreeSqrt A *ᵥ (onesVec : V → ℝ)) :=
    dotProduct_pos_of_ne_zero hwne
  by_contra hcon
  push_neg at hcon
  -- Every eigenbasis eigenvalue is nonnegative (PSD at unit vectors).
  have hge : ∀ i : V, 0 ≤ eigvalOf (normalizedLaplacian A) hLsym i := by
    intro i
    rw [← quadForm_eigvecOf_self hLsym i]
    exact hpsd _
  have hev0 : (0 : ℝ) ≤ evals hLsym ⟨0, by omega⟩ := by
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf hLsym ⟨0, by omega⟩
    rw [hi]; exact hge i
  have hmono : evals hLsym ⟨0, by omega⟩ ≤ evals hLsym ⟨1, by omega⟩ :=
    evals_sorted hLsym
      (show (⟨0, by omega⟩ : Fin (Fintype.card V)) ≤ ⟨1, by omega⟩ by simp)
  have h1 : evals hLsym ⟨1, by omega⟩ = (0 : ℝ) :=
    le_antisymm hcon (hev0.trans hmono)
  have h0 : evals hLsym ⟨0, by omega⟩ = (0 : ℝ) :=
    le_antisymm (hmono.trans hcon) hev0
  obtain ⟨i₁, i₂, hne, he1, he2⟩ := exists_ne_eigvalOf_of_evals_head_eq
    hLsym hcard (by rw [h0, h1])
  -- Both eigenbasis vectors lie on the kernel line.
  have hspan : ∀ i : V, eigvalOf (normalizedLaplacian A) hLsym i = 0 →
      ∃ c : ℝ, eigvecOf (normalizedLaplacian A) hLsym i
        = c • (degreeSqrt A *ᵥ (onesVec : V → ℝ)) := by
    intro i hi
    have hmem : normalizedLaplacian A *ᵥ
        eigvecOf (normalizedLaplacian A) hLsym i = 0 := by
      have h := (isHermitian_of_isSymm hLsym).mulVec_eigenvectorBasis i
      rw [show (isHermitian_of_isSymm hLsym).eigenvalues i
          = eigvalOf (normalizedLaplacian A) hLsym i from rfl,
        hi, zero_smul] at h
      exact h
    exact (normalizedLaplacian_mulVec_eq_zero_iff A hA hnn hd hconn _).1 hmem
  obtain ⟨c₁, hc₁⟩ := hspan i₁ (he1.trans h1)
  obtain ⟨c₂, hc₂⟩ := hspan i₂ (he2.trans h1)
  have hortho : Matrix.dotProduct
      (eigvecOf (normalizedLaplacian A) hLsym i₁)
      (eigvecOf (normalizedLaplacian A) hLsym i₂) = 0 := by
    have h := eigvecOf_inner _ hLsym i₁ i₂
    simp only [if_neg hne] at h
    exact h
  have hn1 : Matrix.dotProduct
      (eigvecOf (normalizedLaplacian A) hLsym i₁)
      (eigvecOf (normalizedLaplacian A) hLsym i₁) = 1 := by
    simpa using eigvecOf_inner _ hLsym i₁ i₁
  have hn2 : Matrix.dotProduct
      (eigvecOf (normalizedLaplacian A) hLsym i₂)
      (eigvecOf (normalizedLaplacian A) hLsym i₂) = 1 := by
    simpa using eigvecOf_inner _ hLsym i₂ i₂
  rw [hc₁, hc₂, dotProduct_smul_smul_self] at hortho
  rw [hc₁, dotProduct_smul_smul_self] at hn1
  rw [hc₂, dotProduct_smul_smul_self] at hn2
  rcases mul_eq_zero.1 hortho with h | h
  · rcases mul_eq_zero.1 h with hc | hc
    · rw [hc, zero_mul, zero_mul] at hn1
      exact zero_ne_one hn1
    · rw [hc, zero_mul, zero_mul] at hn2
      exact zero_ne_one hn2
  · exact absurd h (ne_of_gt hwwpos)

/-- **The disconnected converse:** when the support graph is
disconnected, `λ₂ (L_sym) = 0` exactly. Route: an unreachable pair
defines the component indicator, a combinatorial kernel vector (every
positive weight stays inside a component); its degree-stretched image
is a normalized kernel vector (the cone lift), Gram–Schmidt against
the stretched constants `√D · 1` produces a *nonzero* kernel vector
orthogonal to them (the two stretched vectors are independent, since
the indicator is non-constant), and the delivered general-kernel
engine `secondEval_le_rayleigh_of_ker` pins `λ₂` below its zero
Rayleigh quotient, with the PSD transfer pinning it above. -/
theorem secondEval_normalizedLaplacian_eq_zero_of_not_connected
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V)
    (hdisc : ¬ (supportGraph A hA).Connected) :
    secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard = 0 := by
  classical
  have hLsym := normalizedLaplacian_symmetric A hA
  have hpsd := normalizedLaplacian_psd A hA hnn hd
  have hwne := degreeSqrt_mulVec_onesVec_ne_zero A hd hcard
  have hwker : normalizedLaplacian A *ᵥ
      (degreeSqrt A *ᵥ (onesVec : V → ℝ)) = 0 :=
    normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd
  -- the failure of connectivity gives an unreachable pair
  obtain ⟨u, v, hnr⟩ : ∃ a b : V, ¬ (supportGraph A hA).Reachable a b := by
    by_contra hcon
    push_neg at hcon
    apply hdisc
    obtain ⟨x⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨x, fun y => hcon x y⟩
  -- the component indicator of `u` is a combinatorial kernel vector
  set g : V → ℝ :=
    fun k => if (supportGraph A hA).Reachable u k then 1 else 0 with hg
  have hgu : g u = 1 := by
    rw [hg]
    simp [show (supportGraph A hA).Reachable u u from
      ⟨SimpleGraph.Walk.nil⟩]
  have hgv : g v = 0 := by rw [hg]; simpa using hnr
  have hre : ∀ i j : V, 0 < A i j → g i = g j := by
    intro i j hpos
    by_cases hij : i = j
    · rw [hij]
    · have hadj : (supportGraph A hA).Adj i j :=
        supportGraph_adj.2 ⟨hij, hpos⟩
      have hwalk : (supportGraph A hA).Reachable i j :=
        ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩
      rw [hg]
      by_cases h2 : (supportGraph A hA).Reachable u i
      · exact by
          simp [h2, SimpleGraph.Reachable.trans h2 hwalk]
      · have hj : ¬ (supportGraph A hA).Reachable u j := by
          intro hj'
          exact h2 (SimpleGraph.Reachable.trans hj'
            (SimpleGraph.Reachable.symm hwalk))
        exact by simp [h2, hj]
  have hLg : laplacian A *ᵥ g = 0 := by
    funext i
    rw [laplacian_mulVec_apply]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rcases eq_or_lt_of_le (hnn i j) with h0 | hpos
    · rw [← h0, zero_mul]
    · rw [hre i j hpos, sub_self, mul_zero]
  -- the stretched indicator is a normalized kernel vector
  have hg' : normalizedLaplacian A *ᵥ (degreeSqrt A *ᵥ g) = 0 :=
    normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero A hd
      hLg
  -- Gram–Schmidt against the kernel vector `√D · 1`
  have hwwpos : 0 < Matrix.dotProduct
      (degreeSqrt A *ᵥ (onesVec : V → ℝ))
      (degreeSqrt A *ᵥ (onesVec : V → ℝ)) :=
    dotProduct_pos_of_ne_zero hwne
  set c : ℝ := Matrix.dotProduct (degreeSqrt A *ᵥ g)
      (degreeSqrt A *ᵥ (onesVec : V → ℝ))
    * (Matrix.dotProduct (degreeSqrt A *ᵥ (onesVec : V → ℝ))
      (degreeSqrt A *ᵥ (onesVec : V → ℝ)))⁻¹ with hc
  set x : V → ℝ := degreeSqrt A *ᵥ g
    - c • (degreeSqrt A *ᵥ (onesVec : V → ℝ)) with hx
  have hxorth : Matrix.dotProduct x
      (degreeSqrt A *ᵥ (onesVec : V → ℝ)) = 0 := by
    have hcomm : Matrix.dotProduct
        (degreeSqrt A *ᵥ (onesVec : V → ℝ)) (degreeSqrt A *ᵥ g)
        = Matrix.dotProduct (degreeSqrt A *ᵥ g)
          (degreeSqrt A *ᵥ (onesVec : V → ℝ)) :=
      Matrix.dotProduct_comm _ _
    have hcancel : Matrix.dotProduct (degreeSqrt A *ᵥ g)
          (degreeSqrt A *ᵥ (onesVec : V → ℝ))
        * (Matrix.dotProduct (degreeSqrt A *ᵥ (onesVec : V → ℝ))
          (degreeSqrt A *ᵥ (onesVec : V → ℝ)))⁻¹
        * Matrix.dotProduct (degreeSqrt A *ᵥ (onesVec : V → ℝ))
          (degreeSqrt A *ᵥ (onesVec : V → ℝ))
      = Matrix.dotProduct (degreeSqrt A *ᵥ g)
        (degreeSqrt A *ᵥ (onesVec : V → ℝ)) := by
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hwwpos), mul_one]
    rw [hx, Matrix.dotProduct_comm, Matrix.dotProduct_sub,
      Matrix.dotProduct_smul, hcomm, smul_eq_mul, hc, hcancel]
    ring
  have hxker : normalizedLaplacian A *ᵥ x = 0 := by
    rw [hx, Matrix.mulVec_sub, Matrix.mulVec_smul, hg', hwker, smul_zero,
      sub_zero]
  have hxne : x ≠ 0 := by
    intro hx0
    rw [hx] at hx0
    have hsub : degreeSqrt A *ᵥ g
        = c • (degreeSqrt A *ᵥ (onesVec : V → ℝ)) := sub_eq_zero.1 hx0
    -- un-stretch: g = c • onesVec, contradicting g u = 1 ≠ 0 = g v
    have hcancel : degreeInvSqrt A *ᵥ (degreeSqrt A *ᵥ g) = g := by
      rw [Matrix.mulVec_mulVec, degreeInvSqrt_mul_degreeSqrt A hd,
        Matrix.one_mulVec]
    have hcancelw : degreeInvSqrt A *ᵥ
        (degreeSqrt A *ᵥ (onesVec : V → ℝ)) = (onesVec : V → ℝ) := by
      rw [Matrix.mulVec_mulVec, degreeInvSqrt_mul_degreeSqrt A hd,
        Matrix.one_mulVec]
    have hun : g = c • (onesVec : V → ℝ) := by
      rw [← hcancel, hsub, Matrix.mulVec_smul_assoc, hcancelw]
    have h1 : (1 : ℝ) = c := by
      have hq := congrFun hun u
      simp only [hgu, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at hq
      exact hq
    have h2 : (0 : ℝ) = c := by
      have hq := congrFun hun v
      simp only [hgv, Pi.smul_apply, smul_eq_mul, onesVec, mul_one] at hq
      exact hq
    rw [← h1] at h2
    exact zero_ne_one h2
  -- λ₂ ≤ R(x) = 0 and λ₂ ≥ 0
  have hle : secondEval (normalizedLaplacian A) hLsym hcard
      ≤ rayleigh (normalizedLaplacian A) x :=
    secondEval_le_rayleigh_of_ker hLsym hpsd hwne hwker hcard hxne hxorth
  have hray : rayleigh (normalizedLaplacian A) x = 0 := by
    rw [rayleigh, if_neg hxne, div_eq_zero_iff]
    exact Or.inl (by
      rw [quadForm, hxker, Matrix.dotProduct_zero])
  have hge : (0 : ℝ) ≤ secondEval (normalizedLaplacian A) hLsym hcard := by
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf hLsym ⟨1, by omega⟩
    show (0 : ℝ) ≤ evals hLsym ⟨1, by omega⟩
    rw [hi, ← quadForm_eigvecOf_self hLsym i]
    exact hpsd _
  exact le_antisymm (hle.trans_eq hray) hge

/-- **The packaged equivalence — algebraic connectivity *is*
connectivity in the volume-weighted world:** `0 < λ₂ (L_sym)` if and
only if the support graph is connected. Hypothesis-free statement (the
hypotheses of the two directions are discharged inside); the hypothesis
shape every downstream consumer of the irregular Cheeger pair wants. -/
theorem secondEval_normalizedLaplacian_pos_iff_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (hcard : 2 ≤ Fintype.card V) :
    0 < secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard
      ↔ (supportGraph A hA).Connected := by
  constructor
  · intro hpos
    by_contra hdisc
    rw [secondEval_normalizedLaplacian_eq_zero_of_not_connected
      A hA hnn hd hcard hdisc] at hpos
    exact absurd hpos (lt_irrefl 0)
  · exact secondEval_normalizedLaplacian_pos_of_connected A hA hnn hd hcard

/-- **The Cheeger consumer corollary:** on a connected irregular graph
the Cheeger constant is positive — the delivered easy direction
`cheeger_upper_bound_normalized` (`λ₂ ≤ 2φ`) joined to the positivity
transfer (`0 < λ₂`): `0 < λ₂ ≤ 2φ`. This is the gap-content statement
of the delivered Cheeger pair: on connected input the conductance
infimum is strictly positive. -/
theorem cheegerConstant_pos_of_connected (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) :
    0 < cheegerConstant A := by
  have hpos := secondEval_normalizedLaplacian_pos_of_connected A hA hnn hd
    hcard hconn
  have hcheb := cheeger_upper_bound_normalized A hA hnn hd hcard
  linarith

/-!
### The irregular Fiedler instantiation (proved)

The algorithm-facing capstone of the irregular Cheeger family
(delivered 2026-08-26): the sweep-cut extraction
`cheeger_sweep_cut_normalized` bounds an explicit swept cut for every
nonzero degree-weighted zero-sum `f` — but every application until now
supplied a hand-built test vector. The Fiedler instantiation supplies
the input the spectral-partitioning algorithm actually computes: the
eigenvector `u` of `L_sym` at `λ₂`, pulled back to the un-stretched
world as `f = D^{-1/2} u` (so that `√D f = u` — the stretch
cancellation is the `degreeSqrt/degreeInvSqrt` identity). The delivered
connectivity transfer is exactly what makes the join work: connectivity
gives `0 < λ₂`, distinct eigenvalues make the Fiedler vector orthogonal
to the true kernel vector `√D · onesVec`
(`eigvecOf_ortho_of_mulVec_eq_zero`), and the degree-weighted pairing
identity converts that orthogonality into the sweep family's own
constraint shape `∑ i, deg A i * f i = 0`. The Rayleigh quotient of the
Fiedler vector *is* `λ₂` (`quadForm_eigvecOf_self`), so the sweep
bound lands at the classical scale: `conductance S ^ 2 ≤ 2 * λ₂` — on
`d`-regular input exactly the regular family's `fiedler_sweep_cut`
constant `2 λ₂ (L) / d`, since `λ₂ (L_sym) = λ₂ (L) / d` on the cone.
-/

/-- An eigenbasis index of `L_sym` whose eigenvalue is the second
sorted normalized eigenvalue. Exists by `evals_mem_eigvalOf` (sorting a
multiset permutes it); fixed by classical choice. The cardinality
hypothesis keeps the sorted-spectrum position `1` admissible. This is
`GraphTheory.Fiedler.fiedlerIndex` at the operator the irregular world
actually uses. -/
noncomputable def fiedlerIndexNormalized (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) : V :=
  Classical.choose
    (evals_mem_eigvalOf (normalizedLaplacian_symmetric A hA) ⟨1, by omega⟩)

/-- Interface to the index choice: the chosen index's eigenvalue *is*
`λ₂ (L_sym)`. -/
theorem fiedlerIndexNormalized_eigvalOf (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) :
    eigvalOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA)
        (fiedlerIndexNormalized A hA hcard)
      = secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard :=
  (Classical.choose_spec
    (evals_mem_eigvalOf (normalizedLaplacian_symmetric A hA)
      ⟨1, by omega⟩)).symm

/-- The normalized Fiedler vector: the (unit) eigenvector of `L_sym`
at the index carrying `λ₂ (L_sym)`, from the proved orthonormal
eigenbasis. Noncomputable because the eigenbasis and the index choice
both come from the spectral theorem plus classical choice. -/
noncomputable def fiedlerVectorNormalized (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) : V → ℝ :=
  eigvecOf (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA)
    (fiedlerIndexNormalized A hA hcard)

/-- **The eigenvector equation.** The normalized Fiedler vector is a
genuine eigenvector of `L_sym` at eigenvalue `λ₂ (L_sym)` — the
statement every consumer starts from. -/
theorem fiedlerVectorNormalized_eigen (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) :
    normalizedLaplacian A *ᵥ fiedlerVectorNormalized A hA hcard
      = secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard •
        fiedlerVectorNormalized A hA hcard := by
  have hev := (isHermitian_of_isSymm (normalizedLaplacian_symmetric A hA)
    ).mulVec_eigenvectorBasis (fiedlerIndexNormalized A hA hcard)
  rw [← fiedlerIndexNormalized_eigvalOf A hA hcard]
  exact hev

/-- The normalized Fiedler vector has unit norm (it is a member of the
orthonormal eigenbasis), in dot-product form. -/
theorem fiedlerVectorNormalized_dot_self (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) :
    Matrix.dotProduct (fiedlerVectorNormalized A hA hcard)
        (fiedlerVectorNormalized A hA hcard) = 1 := by
  simpa [Matrix.dotProduct] using eigvecOf_inner
    (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA)
    (fiedlerIndexNormalized A hA hcard) (fiedlerIndexNormalized A hA hcard)

/-- The normalized Fiedler vector is nonzero, by unit norm. -/
theorem fiedlerVectorNormalized_ne_zero (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) :
    fiedlerVectorNormalized A hA hcard ≠ 0 := by
  intro h
  have hn := fiedlerVectorNormalized_dot_self A hA hcard
  rw [h, Matrix.dotProduct_zero] at hn
  exact zero_ne_one hn

/-- A unit eigenvector's quadratic form is its eigenvalue: the Fiedler
vector's `L_sym`-energy is exactly `λ₂ (L_sym)` — the value the
variational theory says is minimal among vectors orthogonal to the
stretched constants. -/
theorem fiedlerVectorNormalized_quadForm (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) :
    quadForm (normalizedLaplacian A) (fiedlerVectorNormalized A hA hcard)
      = secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard := by
  have h := quadForm_eigvecOf_self (normalizedLaplacian_symmetric A hA)
    (fiedlerIndexNormalized A hA hcard)
  rw [fiedlerIndexNormalized_eigvalOf A hA hcard] at h
  exact h

/-- The Rayleigh quotient of the normalized Fiedler vector is exactly
`λ₂ (L_sym)`. This is the spectral side of the sweep bound: the sweep
family's `2 * R_{L_sym}(√D f)` closes to `2 * λ₂` precisely here. -/
theorem fiedlerVectorNormalized_rayleigh (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) :
    rayleigh (normalizedLaplacian A) (fiedlerVectorNormalized A hA hcard)
      = secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard := by
  rw [rayleigh, if_neg (fiedlerVectorNormalized_ne_zero A hA hcard),
    fiedlerVectorNormalized_quadForm, fiedlerVectorNormalized_dot_self,
    div_one]

/-- **The orthogonality hinge.** Eigenvectors at nonzero eigenvalues
are orthogonal to the kernel vector; for the normalized Fiedler vector
this needs `0 < λ₂ (L_sym)`, which connectivity supplies
(`secondEval_normalizedLaplacian_pos_of_connected`) — the exact point
where the connectivity hypothesis enters the sweep cut. -/
theorem fiedlerVectorNormalized_ortho_degreeSqrt_onesVec
    (A : WAdj (V := V)) (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (hcard : 2 ≤ Fintype.card V)
    (hpos : 0 < secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard) :
    Matrix.dotProduct (fiedlerVectorNormalized A hA hcard)
        (degreeSqrt A *ᵥ (onesVec : V → ℝ)) = 0 :=
  eigvecOf_ortho_of_mulVec_eq_zero (normalizedLaplacian_symmetric A hA)
    (normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd) (by
      rw [fiedlerIndexNormalized_eigvalOf A hA hcard]
      exact hpos.ne')

/-- **The sweep vector**: the `D^{-1/2}` pullback of the normalized
Fiedler vector — the vector the spectral-partitioning algorithm
actually sorts. In the random-walk coordinates of the irregular world
this is `f = D^{-1/2} u`, the generalized eigenfunction of the pair
`(L, D)` at `λ₂`; sweeping its level sets is the classical
spectral-partitioning heuristic. -/
noncomputable def fiedlerSweepVector (A : WAdj (V := V))
    (hA : A.IsSymm) (hcard : 2 ≤ Fintype.card V) : V → ℝ :=
  degreeInvSqrt A *ᵥ fiedlerVectorNormalized A hA hcard

/-- The stretch cancellation: pulling the Fiedler vector back through
`1/√D` and stretching again recovers it (`√D · (1/√D) = 1` at positive
degrees). This is the identity that makes the sweep family's Rayleigh
argument `R_{L_sym}(√D f)` close at the eigenvector itself. -/
theorem fiedlerSweepVector_degreeSqrt_mulVec (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i)
    (hcard : 2 ≤ Fintype.card V) :
    degreeSqrt A *ᵥ fiedlerSweepVector A hA hcard
      = fiedlerVectorNormalized A hA hcard := by
  rw [fiedlerSweepVector, Matrix.mulVec_mulVec,
    degreeSqrt_mul_degreeInvSqrt A hd, Matrix.one_mulVec]

/-- The sweep vector is nonzero (conjugation by the invertible `1/√D`
preserves nonvanishing at positive degrees). -/
theorem fiedlerSweepVector_ne_zero (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V) :
    fiedlerSweepVector A hA hcard ≠ 0 :=
  degreeInvSqrt_mulVec_ne_zero A hd (fiedlerVectorNormalized_ne_zero A hA hcard)

/-- **The constraint conversion**: the sweep vector is degree-weighted
zero-sum — the sweep family's own hypothesis `∑ i, deg A i * f i = 0`,
obtained here from the eigen-orthogonality hinge rather than assumed.
The degree-weighted pairing identity turns orthogonality to `√D · 1`
into the un-stretched constraint; this is the join that makes the
Fiedler vector admissible sweep input without any hand-built test
vector. -/
theorem fiedlerSweepVector_sum_deg_eq_zero (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, 0 < deg A i) (hcard : 2 ≤ Fintype.card V)
    (hpos : 0 < secondEval (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) hcard) :
    ∑ i, deg A i * fiedlerSweepVector A hA hcard i = 0 := by
  rw [← dotProduct_degreeSqrt_mulVec_onesVec A (fun i => le_of_lt (hd i)),
    fiedlerSweepVector_degreeSqrt_mulVec A hA hd hcard]
  exact fiedlerVectorNormalized_ortho_degreeSqrt_onesVec A hA hd hcard hpos

/-- **The irregular Fiedler sweep cut — the family's algorithm-facing
capstone.** On every connected symmetric nonnegative positive-degree
graph with at least two vertices, there is a nonempty proper cut which
is a **closed superlevel or sublevel set of the sweep vector itself**
— a member of the sweep family the spectral-partitioning algorithm
actually enumerates, at the input it actually computes (the Fiedler
eigenvector of `L_sym`, pulled back through `1/√D`) — with

`conductance A S ^ 2 ≤ 2 * secondEval (normalizedLaplacian A)`.

Route: the connectivity transfer supplies `0 < λ₂`; the eigen-hinge and
the pairing identity make the sweep vector admissible
(`fiedlerSweepVector_sum_deg_eq_zero`); `cheeger_sweep_cut_normalized`
extracts the swept witness at `conductance S ^ 2 ≤ 2 *
R_{L_sym}(√D f)`; the stretch cancellation and
`fiedlerVectorNormalized_rayleigh` close the spectral side at `2 * λ₂`.
On `d`-regular input this is exactly the regular family's
`fiedler_sweep_cut` constant `2 * lambda2 / d`, since
`λ₂ (L_sym) = lambda2 / d` on the regular cone.

Trust level: hard crust; nothing axiom-backed.

QA: `SpectralGraphTheory.QA.ifc_p3_instance_QA` (the `P₃` instance at
the exact pinned `λ₂ = 1`), `SpectralGraphTheory.QA.ifc_edge_instance_QA`
(the `K₂` instance against the pinned `λ₂ = 2`), and
`SpectralGraphTheory.QA.ifc_disc_hinge_fence_QA` (the mechanism fence:
on the disconnected fixture `λ₂ = 0` and a kernel eigenvector provably
violates the orthogonality hinge — the constraint genuinely needs the
connectivity-supplied gap) in
`Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean`. -/
theorem fiedler_sweep_cut_normalized (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (hcard : 2 ≤ Fintype.card V)
    (hconn : (supportGraph A hA).Connected) :
    ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ t : ℝ, ∀ i, i ∈ S ↔ t ≤ fiedlerSweepVector A hA hcard i) ∨
        (∃ t : ℝ, ∀ i, i ∈ S ↔ fiedlerSweepVector A hA hcard i ≤ t)) ∧
      conductance A S ^ 2
        ≤ 2 * secondEval (normalizedLaplacian A)
            (normalizedLaplacian_symmetric A hA) hcard := by
  have hpos := secondEval_normalizedLaplacian_pos_of_connected A hA hnn hd
    hcard hconn
  obtain ⟨S, hSne, hScne, hlev, hcond⟩ :=
    cheeger_sweep_cut_normalized A hA hnn hd
      (fiedlerSweepVector_ne_zero A hA hd hcard)
      (fiedlerSweepVector_sum_deg_eq_zero A hA hd hcard hpos)
  refine ⟨S, hSne, hScne, hlev, ?_⟩
  rw [fiedlerSweepVector_degreeSqrt_mulVec A hA hd hcard,
    fiedlerVectorNormalized_rayleigh A hA hcard] at hcond
  exact hcond

/-!
## The degree eigenvalue sandwich (2026-08-29)

The eigenvalue-level bridge between the combinatorial and normalized
worlds — the engine the irregular analogue of the Cheeger window needs
(the delivered window family composes the combinatorial-λ₂ tail with
the regular Cheeger pair; the irregular Cheeger pair lives at
`secondEval (normalizedLaplacian A)` and, before this section, had no
eigenvalue-level connection to `lambda2` at all — only the quadratic-
form and Rayleigh-quotient transfers above).

The statement is the classical two-sided degree comparison: with every
degree in `[dmin, dmax]` and `0 < dmin`, at *every* sorted index `k`,

  `λₖ(L) / dmax ≤ λₖ(L_sym) ≤ λₖ(L) / dmin`.

No pointwise test-vector route exists — the two natural variational
problems constrain `x ⊥ 1` (combinatorial) and `x ⊥ √D · onesVec`
(normalized), and the degree substitution `x ↦ √D x` maps one
constraint set to a *degree-weighted* orthogonality, not the other — so
the proof rides the subspace min–max (`evals_min_max` with both
Courant–Fischer witness forms) with the witness subspaces transported
through the degree stretch (a linear equivalence at positive degrees):
the upper side dominates `λₖ(L_sym)`'s sInf by the image of the
combinatorial existence-form subspace, the lower side runs the
competitor form on the un-stretched preimage. The pointwise input is
the Rayleigh-quotient bracket `R_{L_sym}(√D x) ∈ [R_L(x)/dmax,
R_L(x)/dmin]` (the congruence engine plus `laplacian_psd`), which is
where an error in the congruence, the PSD hypothesis, or the degree
guards would break the whole sandwich.
-/

/-- The degree stretch as a linear equivalence: `x ↦ √D x` is bijective
exactly when every degree is positive (the inverse is the `1/√D`
stretch). The subspace transport of the sandwich runs through this. -/
noncomputable def degreeSqrtEquiv (A : WAdj (V := V)) (hd : ∀ i, 0 < deg A i) :
    (V → ℝ) ≃ₗ[ℝ] (V → ℝ) :=
  LinearEquiv.ofBijective (Matrix.mulVecLin (degreeSqrt A))
    ⟨fun x y h => by
      by_contra hxy
      have h1 : Matrix.mulVecLin (degreeSqrt A) (x - y) = 0 := by
        rw [map_sub, h, sub_self]
      have hz : degreeSqrt A *ᵥ (x - y) = 0 := h1
      exact absurd hz (degreeSqrt_mulVec_ne_zero A hd (sub_ne_zero.2 hxy)),
      fun y => ⟨degreeInvSqrt A *ᵥ y, by
        rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
          degreeSqrt_mul_degreeInvSqrt A hd, Matrix.one_mulVec]⟩⟩

omit [DecidableEq V] in
/-- The degree-weighted denominator, lower bound: with `dmin` below
every degree, the degree-weighted squared norm is at least `dmin`
times the plain squared norm. -/
theorem sum_deg_mul_sq_ge (A : WAdj (V := V)) (dmin : ℝ)
    (hdmin : ∀ i, dmin ≤ deg A i) (x : V → ℝ) :
    dmin * Matrix.dotProduct x x ≤ ∑ i, deg A i * x i * x i := by
  have h1 : dmin * ∑ i, x i * x i ≤ ∑ i, deg A i * x i * x i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      by nlinarith [hdmin i, sq_nonneg (x i)]
  rw [← Matrix.dotProduct]
  exact h1

omit [DecidableEq V] in
/-- The degree-weighted denominator, upper bound: with every degree at
most `dmax`, the degree-weighted squared norm is at most `dmax` times
the plain squared norm. -/
theorem sum_deg_mul_sq_le (A : WAdj (V := V)) (dmax : ℝ)
    (hdmax : ∀ i, deg A i ≤ dmax) (x : V → ℝ) :
    ∑ i, deg A i * x i * x i ≤ dmax * Matrix.dotProduct x x := by
  have h1 : ∑ i, deg A i * x i * x i ≤ dmax * ∑ i, x i * x i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      by nlinarith [hdmax i, sq_nonneg (x i)]
  rw [← Matrix.dotProduct]
  exact h1

/-- The quotient bracket, upper side: `R_{L_sym}(√D x) ≤ R_L(x)/dmin`
for nonzero `x` — the PSD numerator over a denominator at least `dmin`
times the plain norm. The pointwise engine of the sandwich's `dmin`
half; nonnegativity of the weights is load-bearing through
`laplacian_psd` (on signed input the combinatorial form is not PSD and
the division flips). -/
theorem rayleigh_normalizedLaplacian_le_div (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmin : ℝ) (hdmin : ∀ i, dmin ≤ deg A i) (hpos : 0 < dmin)
    {x : V → ℝ} (hx0 : x ≠ 0) :
    rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ x)
      ≤ rayleigh (laplacian A) x / dmin := by
  have hpsd := laplacian_psd A hA hnn
  have hs : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
  have hbr := sum_deg_mul_sq_ge A dmin hdmin x
  have hWpos : 0 < ∑ i, deg A i * x i * x i :=
    lt_of_lt_of_le (mul_pos hpos hs) hbr
  rw [rayleigh_normalizedLaplacian_degreeSqrt A hd hx0, rayleigh,
    if_neg hx0, div_div]
  rw [div_le_div_iff₀ hWpos (mul_pos hs hpos)]
  have hq := hpsd x
  nlinarith [hbr, hq]

/-- The quotient bracket, lower side: `R_L(x) ≤ dmax · R_{L_sym}(√D x)`
for nonzero `x` — the PSD numerator over a denominator at most `dmax`
times the plain norm. The pointwise engine of the sandwich's `dmax`
half. -/
theorem rayleigh_le_mul_rayleigh_normalizedLaplacian (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmax : ℝ) (hdmax : ∀ i, deg A i ≤ dmax)
    {x : V → ℝ} (hx0 : x ≠ 0) :
    rayleigh (laplacian A) x
      ≤ dmax * rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ x) := by
  have hpsd := laplacian_psd A hA hnn
  have hs : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
  have hbr := sum_deg_mul_sq_le A dmax hdmax x
  have hWpos : 0 < ∑ i, deg A i * x i * x i := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hx0 (funext hcon)
    exact Finset.sum_pos' (fun j _ => by
      calc deg A j * x j * x j = deg A j * (x j * x j) := by ring
        _ ≥ 0 := mul_nonneg (hd j).le (mul_self_nonneg _))
      ⟨i, Finset.mem_univ _, by
        calc deg A i * x i * x i = deg A i * (x i * x i) := by ring
          _ > 0 := mul_pos (hd i) (mul_self_pos.2 hi)⟩
  rw [rayleigh_normalizedLaplacian_degreeSqrt A hd hx0, rayleigh,
    if_neg hx0, ← mul_div_assoc]
  rw [div_le_div_iff₀ hs hWpos]
  have hq := hpsd x
  nlinarith [hbr, hq]

/-- **The bottom eigenvalue of the normalized Laplacian is exactly
`0`** on positive-degree graphs — no connectivity, the normalized
counterpart of `laplacian_evals_zero`. The stretched constants are an
eigenvector at `0`, and PSD of `L_sym` rules out anything smaller. The
pin every exact normalized-spectrum fixture starts from. -/
theorem normalizedLaplacian_evals_zero (A : WAdj (V := V))
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (hcard : 0 < Fintype.card V) :
    evals (normalizedLaplacian_symmetric A hA) ⟨0, by omega⟩ = 0 := by
  have hpsd := normalizedLaplacian_psd A hA hnn hd
  obtain ⟨v⟩ := Fintype.card_pos_iff.1 hcard
  have hvne : (onesVec : V → ℝ) ≠ 0 := by
    intro h
    have hv : (onesVec : V → ℝ) v = 0 := congrFun h v
    simp [onesVec] at hv
  have hwne : degreeSqrt A *ᵥ (onesVec : V → ℝ) ≠ 0 :=
    degreeSqrt_mulVec_ne_zero A hd hvne
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul
    (normalizedLaplacian_symmetric A hA) hwne
    (by rw [zero_smul]; exact normalizedLaplacian_mulVec_degreeSqrt_onesVec A hd)
  obtain ⟨i', hi'⟩ := evals_mem_eigvalOf (normalizedLaplacian_symmetric A hA)
    ⟨0, by omega⟩
  have hge : (0 : ℝ)
      ≤ eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i' := by
    have h := hpsd (eigvecOf (normalizedLaplacian A)
      (normalizedLaplacian_symmetric A hA) i')
    rw [quadForm_eigvecOf_self] at h
    exact h
  have hle : evals (normalizedLaplacian_symmetric A hA) ⟨0, by omega⟩
      ≤ eigvalOf (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) i :=
    evals_first_le_eigvalOf _ (by omega) i
  rw [← hi'] at hge
  rw [hi] at hle
  linarith

/-- **The degree eigenvalue sandwich, upper side (engine).** On any
symmetric nonnegative positive-degree graph, at every sorted index `k`,
the normalized-Laplacian eigenvalue is at most the combinatorial one
divided by the degree floor:

  `λₖ(L_sym) ≤ λₖ(L) / dmin`  whenever  `dmin ≤ deg A i` (all `i`),
  `0 < dmin`.

Source (classical background; this is a proof, not an admission):
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.2 (Courant–Fischer), whose
  subspace min–max applied to the degree-weighted Rayleigh quotient
  gives this comparison; the statement is the standard
  normalized/unnormalized eigenvalue sandwich of spectral graph theory.

Route: the combinatorial existence form exhibits a `(k+1)`-dimensional
subspace `W₁` whose Rayleigh quotients all sit below `λₖ(L)`; its
image under the degree stretch is again `(k+1)`-dimensional
(`finrank_map_eq_of_injective` through `degreeSqrtEquiv`), and the
quotient bracket bounds every image Rayleigh quotient by
`R_L(x)/dmin ≤ λₖ(L)/dmin` — so `λₖ(L)/dmin` is a dominating value of
`L_sym`'s min–max set, and `csInf_le` closes. The competitor direction
supplies the set's boundedness.

QA: `Scaffold/QA/SpectralGraph/DegreeSandwich_QA.lean` — the P₃
instance with the upper side *attained at equality*
(`dsP3_upper_tight_QA`: `λ₂(L_sym) = 1 = λ₂(L)/dmin`), the wrong-
constant pairing fence (`dsP3_wrongConstant_refuted_QA`), the K₂
regular squeeze (`dsK2_squeeze_*_QA`), the non-second index instance
(`dsP3_engine_k2_QA`), and the `dmin = 0` isolated-vertex junk fence
(`dsIso_upper_dmin_zero_refuted_QA`) showing the `0 < dmin` guard
load-bearing. -/
theorem evals_normalizedLaplacian_le_div (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmin : ℝ) (hdmin : ∀ i, dmin ≤ deg A i) (hpos : 0 < dmin)
    (k : Fin (Fintype.card V)) :
    evals (normalizedLaplacian_symmetric A hA) k
      ≤ evals (laplacian_symmetric A hA) k / dmin := by
  classical
  have hLsym := normalizedLaplacian_symmetric A hA
  have hL := laplacian_symmetric A hA
  obtain ⟨W₁, hW₁r, hW₁b⟩ := exists_submodule_forall_rayleigh_le hL k
  set f : (V → ℝ) →ₗ[ℝ] (V → ℝ) := Matrix.mulVecLin (degreeSqrt A) with hf
  have hinj : Function.Injective f := (degreeSqrtEquiv A hd).injective
  set S : Set ℝ := {r : ℝ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = (k : ℕ) + 1 ∧
      ∀ x ∈ W, x ≠ 0 → rayleigh (normalizedLaplacian A) x ≤ r} with hSdef
  have hdom : ∀ r ∈ S, evals hLsym k ≤ r := by
    rintro r ⟨W, hWr, hWb⟩
    obtain ⟨x, hxW, hx0, hge⟩ :=
      exists_ne_mem_rayleigh_ge_of_finrank_eq hLsym k W hWr
    exact hge.trans (hWb x hxW hx0)
  have hbdd : BddBelow S := ⟨evals hLsym k, fun r hr => hdom r hr⟩
  have hfin : Module.finrank ℝ (Submodule.map f W₁) = (k : ℕ) + 1 := by
    rw [finrank_map_eq_of_injective f hinj W₁]
    exact hW₁r
  have hmem : (evals hL k / dmin) ∈ S := by
    refine ⟨Submodule.map f W₁, hfin, ?_⟩
    rintro y ⟨x, hxW, hxy⟩ hy0
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hxy
      exact hy0 hxy.symm
    have hray :=
      rayleigh_normalizedLaplacian_le_div A hA hnn hd dmin hdmin hpos hx0
    have hxy' : degreeSqrt A *ᵥ x = y := hxy
    calc rayleigh (normalizedLaplacian A) y
        = rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ x) := by rw [hxy']
      _ ≤ rayleigh (laplacian A) x / dmin := hray
      _ ≤ evals hL k / dmin :=
          div_le_div_of_nonneg_right (hW₁b x hxW hx0) (le_of_lt hpos)
  rw [evals_min_max hLsym k]
  exact csInf_le hbdd hmem

/-- **The degree eigenvalue sandwich, lower side (engine).** On any
symmetric nonnegative positive-degree graph, at every sorted index `k`,

  `λₖ(L) / dmax ≤ λₖ(L_sym)`  whenever  `deg A i ≤ dmax` (all `i`).

Same source and same machinery, run in the other direction: every
dominating value `r` of the normalized min–max set (on some
`(k+1)`-dimensional `W`) yields, on the un-stretched preimage subspace,
a competitor vector `x` with `λₖ(L) ≤ R_L(x) ≤ dmax · R_{L_sym}(√D x)`
(the quotient bracket's lower side at `√D x ∈ W`, where the dominating
hypothesis bounds `R_{L_sym} ≤ r`), forcing `λₖ(L)/dmax ≤ r`; `le_csInf`
closes. The positivity `0 < dmax` is derived, not assumed (`2 ≤ card`
free: any vertex's degree is positive and bounded).

QA: as above — the P₃ lower instance (`dsP3_lower_QA`), the K₂ squeeze,
and the `k = 2` engine instance. -/
theorem div_le_evals_normalizedLaplacian (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmax : ℝ) (hdmax : ∀ i, deg A i ≤ dmax)
    (k : Fin (Fintype.card V)) :
    evals (laplacian_symmetric A hA) k / dmax
      ≤ evals (normalizedLaplacian_symmetric A hA) k := by
  classical
  have hLsym := normalizedLaplacian_symmetric A hA
  have hL := laplacian_symmetric A hA
  have hne : Nonempty V := Fintype.card_pos_iff.1 (by
    have := k.isLt
    omega)
  have hpos : 0 < dmax := by
    obtain ⟨i⟩ := hne
    exact lt_of_lt_of_le (hd i) (hdmax i)
  set g : (V → ℝ) →ₗ[ℝ] (V → ℝ) :=
    ((degreeSqrtEquiv A hd).symm.toLinearMap) with hg
  have hinjg : Function.Injective g := (degreeSqrtEquiv A hd).symm.injective
  set S : Set ℝ := {r : ℝ | ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = (k : ℕ) + 1 ∧
      ∀ x ∈ W, x ≠ 0 → rayleigh (normalizedLaplacian A) x ≤ r} with hSdef2
  have hne' : S.Nonempty := by
    obtain ⟨W₁, hW₁r, hW₁b⟩ := exists_submodule_forall_rayleigh_le hLsym k
    exact ⟨evals hLsym k, ⟨W₁, hW₁r, hW₁b⟩⟩
  have hmem' : ∀ r ∈ S, evals hL k / dmax ≤ r := by
    rintro r ⟨W, hWr, hWb⟩
    have hgr : Module.finrank ℝ (Submodule.map g W) = (k : ℕ) + 1 := by
      rw [finrank_map_eq_of_injective g hinjg W, hWr]
    obtain ⟨x, hxW', hx0, hge⟩ :=
      exists_ne_mem_rayleigh_ge_of_finrank_eq hL k (Submodule.map g W) hgr
    obtain ⟨y, hyW, hxy⟩ := Submodule.mem_map.1 hxW'
    have hstretch : degreeSqrt A *ᵥ x = y := by
      have h1 : (degreeSqrtEquiv A hd) x = y := by
        have h2 := congrArg (degreeSqrtEquiv A hd) hxy
        rw [show (degreeSqrtEquiv A hd) (g y) = y from
          LinearEquiv.apply_symm_apply (degreeSqrtEquiv A hd) y] at h2
        exact h2.symm
      exact h1
    have hy0 : y ≠ 0 := by
      intro h
      have hzero : degreeSqrt A *ᵥ x = 0 := hstretch.trans h
      exact hx0 (by
        by_contra hxne
        exact absurd (degreeSqrt_mulVec_ne_zero A hd hxne)
          (by rw [hzero]; simp))
    have hbr :=
      rayleigh_le_mul_rayleigh_normalizedLaplacian A hA hnn hd dmax hdmax hx0
    have hyr := hWb y hyW hy0
    rw [div_le_iff₀ hpos]
    calc evals hL k ≤ rayleigh (laplacian A) x := hge
      _ ≤ dmax * rayleigh (normalizedLaplacian A) (degreeSqrt A *ᵥ x) := hbr
      _ = dmax * rayleigh (normalizedLaplacian A) y := by rw [hstretch]
      _ ≤ dmax * r := mul_le_mul_of_nonneg_left hyr (le_of_lt hpos)
      _ = r * dmax := by ring
  rw [evals_min_max hLsym k]
  exact le_csInf hne' hmem'

/-- Interface corollary at `secondEval`/`lambda2`, upper side:
`λ₂(L_sym) ≤ lambda2 A / dmin` — the shape the irregular Cheeger-window
consumer composes with the delivered λ₂ tails. -/
theorem secondEval_normalizedLaplacian_le_div (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmin : ℝ) (hdmin : ∀ i, dmin ≤ deg A i) (hpos : 0 < dmin)
    (hcard : 2 ≤ Fintype.card V) :
    secondEval (normalizedLaplacian A) (normalizedLaplacian_symmetric A hA) hcard
      ≤ lambda2 A hA hcard / dmin :=
  evals_normalizedLaplacian_le_div A hA hnn hd dmin hdmin hpos ⟨1, by omega⟩

/-- Interface corollary at `secondEval`/`lambda2`, lower side:
`lambda2 A / dmax ≤ λ₂(L_sym)`. -/
theorem div_le_secondEval_normalizedLaplacian (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmax : ℝ) (hdmax : ∀ i, deg A i ≤ dmax)
    (hcard : 2 ≤ Fintype.card V) :
    lambda2 A hA hcard / dmax
      ≤ secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard :=
  div_le_evals_normalizedLaplacian A hA hnn hd dmax hdmax ⟨1, by omega⟩

/-- Division-free mul form, lower side: `dmin · λ₂(L_sym) ≤ lambda2`. -/
theorem mul_degMin_le_lambda2 (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmin : ℝ) (hdmin : ∀ i, dmin ≤ deg A i) (hpos : 0 < dmin)
    (hcard : 2 ≤ Fintype.card V) :
    dmin * secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard
      ≤ lambda2 A hA hcard := by
  have h := secondEval_normalizedLaplacian_le_div A hA hnn hd dmin hdmin hpos hcard
  calc dmin * secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard
      ≤ dmin * (lambda2 A hA hcard / dmin) :=
        mul_le_mul_of_nonneg_left h hpos.le
    _ = lambda2 A hA hcard := by field_simp

/-- Division-free mul form, upper side: `lambda2 ≤ dmax · λ₂(L_sym)`. -/
theorem lambda2_le_mul_degMax (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmax : ℝ) (hdmax : ∀ i, deg A i ≤ dmax)
    (hcard : 2 ≤ Fintype.card V) :
    lambda2 A hA hcard
      ≤ dmax * secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard := by
  have h := div_le_secondEval_normalizedLaplacian A hA hnn hd dmax hdmax hcard
  have hpos : 0 < dmax := by
    obtain ⟨i⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    exact lt_of_lt_of_le (hd i) (hdmax i)
  calc lambda2 A hA hcard
      = dmax * (lambda2 A hA hcard / dmax) := by field_simp
    _ ≤ dmax * secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard :=
        mul_le_mul_of_nonneg_left h hpos.le

/-- **The Cheeger floor at the combinatorial Laplacian, degree-window
form** — on any symmetric nonnegative positive-degree graph with degrees
in `[dmin, dmax]` (`0 < dmin`), `dmin · φ(G)² / 2 ≤ λ₂(L)`: the
irregular hard direction scaled through the sandwich's upper side
(`mul_degMin_le_lambda2`). On a `d`-regular graph (`dmin = d`) this is
`cheeger_lower_bound_laplacian`'s `d · φ²/2 ≤ λ₂` exactly; no
regularity hypothesis is needed.

First consumer: `Derived.EdgePerturbationTail
.edgePerturbation_normalized_cheeger_floor` (the irregular Cheeger
window under random edge resampling, 2026-08-29).

QA: `Scaffold.QA.Derived.EdgePerturbation.epK2_normWindow_engine_QA`
(K₂: `1/2 ≤ 2`, slack) and `.epP3_normWindow_engine_QA` (the genuinely
irregular P₃: `1/2 ≤ 1`, the bracket's honest slack). -/
theorem cheeger_lower_bound_laplacian_of_degree_window (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmin : ℝ) (hdmin : ∀ i, dmin ≤ deg A i) (hpos : 0 < dmin)
    (hcard : 2 ≤ Fintype.card V) :
    dmin * cheegerConstant A ^ 2 / 2 ≤ lambda2 A hA hcard := by
  calc dmin * cheegerConstant A ^ 2 / 2
      = dmin * (cheegerConstant A ^ 2 / 2) := by ring
    _ ≤ dmin * secondEval (normalizedLaplacian A)
        (normalizedLaplacian_symmetric A hA) hcard :=
          mul_le_mul_of_nonneg_left
            (cheeger_lower_bound_normalized A hA hnn hd hcard) hpos.le
    _ ≤ lambda2 A hA hcard :=
        mul_degMin_le_lambda2 A hA hnn hd dmin hdmin hpos hcard

/-- **The Cheeger ceiling at the combinatorial Laplacian, degree-window
form** — `λ₂(L) ≤ 2 · dmax · φ(G)`: the irregular easy direction scaled
through the sandwich's lower side (`lambda2_le_mul_degMax`), the
sibling of `cheeger_upper_bound_laplacian` at `dmax = d` on regular
input. Both window-Cheeger constants are load-bearing on the window
family's bracket: a wrong pairing of `dmin`/`dmax` breaks the
corresponding half of the assembly's `measure_mono`.

QA: the third conjunct of
`Scaffold.QA.Derived.EdgePerturbation.epK2_normWindow_engine_QA`
(K₂: `λ₂ = 2 = 2 · (1 · φ)`, attained with equality). -/
theorem cheeger_upper_bound_laplacian_of_degree_window (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmax : ℝ) (hdmax : ∀ i, deg A i ≤ dmax)
    (hcard : 2 ≤ Fintype.card V) :
    lambda2 A hA hcard ≤ 2 * (dmax * cheegerConstant A) := by
  have hdmaxpos : 0 < dmax := by
    obtain ⟨i⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    exact lt_of_lt_of_le (hd i) (hdmax i)
  calc lambda2 A hA hcard
      ≤ dmax * secondEval (normalizedLaplacian A)
          (normalizedLaplacian_symmetric A hA) hcard :=
          lambda2_le_mul_degMax A hA hnn hd dmax hdmax hcard
    _ ≤ dmax * (2 * cheegerConstant A) :=
        mul_le_mul_of_nonneg_left
          (cheeger_upper_bound_normalized A hA hnn hd hcard) hdmaxpos.le
    _ = 2 * (dmax * cheegerConstant A) := by ring

end SpectralGraphTheory
