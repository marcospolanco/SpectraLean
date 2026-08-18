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
  normalized world.

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

end SpectralGraphTheory
