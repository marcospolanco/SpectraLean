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

QA: exercised by `SpectralGraphTheory.QA.cheeger_positive_implies_lambda2_pos_QA`
in `Scaffold/QA/SpectralGraph/Cheeger_QA.lean`, which derives a
connectivity-flavored consequence from this axiom.
-/
axiom cheeger_lower_bound (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) :
    (cheegerConstant A) ^ 2 / 2 ≤
      lambda2 (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard

/-- Cheeger upper bound for `d`-regular graphs: the second-smallest
normalized Laplacian eigenvalue controls the conductance from above,
`λ₂(L_sym) ≤ 2 φ(G)`.

Source:
- Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997,
  Chapter 2.

Statement differences: as for `cheeger_lower_bound`.

QA: exercised by `SpectralGraphTheory.QA.cheegerConstant_le_two_QA` in
`Scaffold/QA/SpectralGraph/Cheeger_QA.lean`, which combines the two
Cheeger bounds into a sandwich on `cheegerConstant`.
-/
axiom cheeger_upper_bound (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) :
    lambda2 (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard ≤
      2 * cheegerConstant A

end SpectralGraphTheory
