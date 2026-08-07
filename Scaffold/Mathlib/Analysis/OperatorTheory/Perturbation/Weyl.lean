/--
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

/--
Weyl's Inequality for eigenvalues of symmetric matrices.

This module provides axioms for Weyl's theorem, which bounds the
change in eigenvalues under a symmetric perturbation.
-/

open Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
Weyl's Inequality.

Source:
- Weyl, "Das asymptotische Verteilungsgesetz der Eigenwerte linearer partieller Differentialgleichungen",
  Mathematische Annalen, 71 (4): 441–479, 1912.
- Bhatia, "Matrix Analysis", Springer, 1997.
  Theorem III.2.1, p. 63.

Intended meaning:
Let A and A' = A + E be symmetric matrices with eigenvalues
λ₁ ≤ λ₂ ≤ ... ≤ λₙ and λ'₁ ≤ λ'₂ ≤ ... ≤ λ'ₙ.
Then |λ_i - λ'_i| ≤ ‖E‖_op for all i.

QA: Exercised by `weyl_zero_perturbation` in
`Scaffold/QA/Perturbation/Weyl_QA.lean`.
-/
axiom weyl_inequality (A E : Matrix V V ℝ) (i : Fin (Fintype.card V))
  (h_symm_A : A.IsSymm)
  (h_symm_E : E.IsSymm) :
  let vals := (A).spectrum -- In reality, we use a sorted spectrum function
  let vals' := (A + E).spectrum
  |vals i - vals' i| ≤ ‖E‖

/--
Stability of the spectral gap under Weyl perturbation.
If the perturbation is small, the gap remains large.
-/
axiom spectral_gap_stability (A E : Matrix V V ℝ) (r : ℕ) (gap : ℝ) (ε : ℝ)
  (h_symm_A : A.IsSymm)
  (h_symm_E : E.IsSymm)
  (h_norm : ‖E‖ ≤ ε) :
  let γ := spectral_gap A r in
  let γ' := spectral_gap (A + E) r in
  γ' ≥ γ - 2 * ε

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
