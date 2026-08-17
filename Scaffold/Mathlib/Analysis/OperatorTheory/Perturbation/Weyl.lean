/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Scaffold.Mathlib.GraphTheory.Spectral
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Weyl perturbation bounds

Weyl's inequality bounds the movement of each eigenvalue of a real
symmetric matrix under a symmetric perturbation, in the ℓ² operator
norm. Eigenvalues are indexed through Scaffold's sorted spectrum
`SpectralGraphTheory.evals`; the norm is the `Matrix.L2OpNorm` operator
norm on `Matrix V V ℝ`.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Weyl's inequality: every eigenvalue of a symmetric matrix moves by at
most the operator norm of a symmetric perturbation. With the spectra of
`A` and `A + E` sorted in nondecreasing order, `|λᵢ(A + E) - λᵢ(A)| ≤ ‖E‖`
for every index `i`.

Source:
- Weyl, H., "Das asymptotische Verteilungsgesetz der Eigenwerte linearer
  partieller Differentialgleichungen", Mathematische Annalen 71(4):441–479,
  1912.
- Bhatia, R., "Matrix Analysis", Springer, 1997, Theorem III.2.1.

Statement differences: eigenvalues are the sorted `evals` of
`SpectralGraphTheory` and the norm is the ℓ² operator norm, matching the
matrix-first representation convention of the SGT center.

QA: exercised by `zero_perturbation_QA` in
`Scaffold/QA/Perturbation/Weyl_QA.lean`, which instantiates `E = 0` and
checks the resulting identity bound.
-/
axiom weyl_inequality (A E : Matrix V V ℝ) (hA : A.IsSymm) (hE : E.IsSymm)
    (i : Fin (Fintype.card V)) :
    |evals (hA.add hE) i - evals hA i| ≤ ‖E‖

/-- Stability of a spectral gap under Weyl perturbation: if `E` moves the
matrix by at most `ε` in operator norm, the gap at index `k` shrinks by
at most `2ε` (each endpoint of the gap moves by at most `ε`).

Source:
- Corollary of Weyl's inequality as stated above; see Bhatia, "Matrix
  Analysis", Springer, 1997, Chapter III.2.

QA: exercised by `spectral_gap_zero_perturbation_QA` in
`Scaffold/QA/Perturbation/Weyl_QA.lean` (zero-perturbation instance).
-/
axiom spectral_gap_stability (A E : Matrix V V ℝ) (hA : A.IsSymm)
    (hE : E.IsSymm) (k : Fin (Fintype.card V))
    (hk : (k : ℕ) + 1 < Fintype.card V) (ε : ℝ) (hnorm : ‖E‖ ≤ ε)
    (γ : ℝ) (hγ : spectralGap A hA k hk ≥ γ) :
    spectralGap (A + E) (hA.add hE) k hk ≥ γ - 2 * ε

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
