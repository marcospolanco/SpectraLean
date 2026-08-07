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
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.NormedSpace.OperatorNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

/-
Davis-Kahan sin Θ theorem for eigenvector perturbation.

This module provides axioms for the Davis-Kahan theorem, which bounds the
rotation of an invariant subspace under a symmetric perturbation.
-/

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
Davis-Kahan Sin Θ theorem.

Source:
- Davis & Kahan, "The rotation of eigenvectors by a perturbation",
  SIAM Journal on Numerical Analysis, Vol. 7, No. 1, pp. 1-46, 1970
  Theorem 3.1, p. 10

Intended meaning:
Let A and A' = A + E be symmetric matrices.
Let S be a set of eigenvalues of A, and let δ be the distance between S and
the spectrum of A outside of S.
Let P and P' be the orthogonal projectors onto the invariant subspaces of A
and A' corresponding to S and the perturbation of S respectively.
Then ‖P - P'‖_op ≤ ‖E‖_op / δ.

QA: Exercised by `davis_kahan_zero_perturbation` in
`Scaffold/QA/Perturbation/DavisKahan_QA.lean`.
-/
axiom davis_kahan_sin_theta (A E : Matrix V V ℝ) (P P' : Matrix V V ℝ) (δ : ℝ)
  (h_symm_A : A.IsSymm)
  (h_symm_E : E.IsSymm)
  (h_proj_P : IsOrthogonalProjector P)
  (h_proj_P' : IsOrthogonalProjector P')
  (h_gap : 0 < δ)
  (h_invariant_P : A * P = P * A)
  (h_invariant_P' : (A + E) * P' = P' * (A + E))
  (h_sep : ∀ λ ∈ spectrum_outside A P, ∀ μ ∈ spectrum_inside (A + E) P', |λ - μ| ≥ δ) :
  ‖P - P'‖ ≤ ‖E‖ / δ

/-
A simplified version of Davis-Kahan for the spectral gap of a Laplacian.
Often used in spectral clustering stability and graph perturbation theory.
-/
axiom davis_kahan_spectral_gap (A E : Matrix V V ℝ) (r : ℕ) (gap : ℝ)
  (h_symm_A : A.IsSymm)
  (h_symm_E : E.IsSymm)
  (h_gap : 0 < gap) :
  let P := spectral_projector A r in
  let P' := spectral_projector (A + E) r in
  ‖P - P'‖ ≤ ‖E‖ / gap

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
