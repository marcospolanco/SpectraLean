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

/-- Cheeger upper bound for `d`-regular graphs: the second-smallest
normalized Laplacian eigenvalue controls the conductance from above,
`λ₂(L_sym) ≤ 2 φ(G)`.

Source:
- Chung, F. R. K., "Spectral Graph Theory", CBMS 92, AMS, 1997,
  Chapter 2.

Statement differences: as for `cheeger_lower_bound`, including the
2026-08-18 statement-shape correction of the spectral side from
`lambda2 (regularNormalizedLaplacian A d) …` (which read
`λ₂(L(L_sym)) = λ₂(-L_sym)`) to `secondEval (regularNormalizedLaplacian A d) …`
(the second-smallest eigenvalue of the normalized Laplacian itself).

QA: exercised by `SpectralGraphTheory.QA.cheeger_bounds_coherent_QA` in
`Scaffold/QA/SpectralGraph/Cheeger_QA.lean`, which combines the two
Cheeger bounds into a sandwich on `cheegerConstant`, and by
`SpectralGraphTheory.QA.cheeger_bounds_edge_QA`, which instantiates the
sandwich on the two-vertex edge against the independently computed values
`φ = 1` and `λ₂(L_sym) = 2`.
-/
axiom cheeger_upper_bound (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d)
    (hdpos : 0 < d) (hcard : 2 ≤ Fintype.card V) :
    secondEval (regularNormalizedLaplacian A d)
        (regularNormalizedLaplacian_symmetric A hA d) hcard ≤
      2 * cheegerConstant A

end SpectralGraphTheory
