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
# Davis–Kahan subspace stability

The Davis–Kahan sin Θ theorem bounds the rotation of an invariant
spectral subspace of a symmetric matrix under symmetric perturbation,
inversely to the eigenvalue separation. Stated here for the spectral
projectors of the SGT center, with the ℓ² operator norm.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Davis–Kahan sin Θ bound for spectral projectors: if the top of the
lower cluster of `A` (its `k`-th sorted eigenvalue) is separated by at
least `δ` from the bottom of the upper cluster of `A + E` (its `k+1`-st
sorted eigenvalue), then the projector onto the span of the `k+1`
smallest eigenvectors moves by at most `‖E‖ / δ`.

Source:
- Davis, C. & Kahan, W. M., "The rotation of eigenvectors by a
  perturbation", SIAM Journal on Numerical Analysis 7(1):1–46, 1970.
- Yu, Y., Wang, T., Samworth, R. J., "A useful variant of the Davis–Kahan
  theorem for statisticians", Annals of Statistics 43(3):2028–2061, 2015,
  Theorem 1 — the classical Davis–Kahan sin Θ bound restated with the
  mixed population/sample separation `δ = inf{|λ̂ − λ| : λ in the
  population cluster, λ̂ in the sample outside-cluster set|}` and constant
  1; the paper notes both Frobenius norms there may be replaced by the
  operator norm. This axiom is that operator-norm form specialized to the
  bottom cluster (the `k+1` smallest eigenvalues, `d = k+1`).

Citation correction 2026-08-21 (Step-0 survey of
`proposals/discharge-perturbation-axioms.md`, paper read at
arXiv:1405.0680): an earlier revision of this note cited "Theorem 2
(two-sided separation, projector form, constant 1)" — a locator/constant
pairing that does not exist in the paper. YWS's actual Theorem 2 is a
*population-gap* result with constant 2 (numerator
`2 min(d^{1/2}‖E‖_op, ‖E‖_F)`, Frobenius norm, proved via Weyl and
Wielandt–Hoffman); this axiom's mixed-gap operator-norm constant-1 shape
is their Theorem 1.

Statement differences: the invariant subspaces are the
`SpectralGraphTheory.initialProjector` spectral projectors of the sorted
spectrum; the distance is the ℓ² operator norm of the projector
difference (the sin Θ metric). The separation hypothesis is the
two-cluster gap `λ_{k+1}(A + E) - λ_k(A) ≥ δ`, the single-pair reduction
(by sortedness; `SpectralGraphTheory.evals_sorted`) of YWS Theorem 1's
`δ` for the bottom cluster — there the outside-cluster set is only the
upper one, so the binding pair is the top of `A`'s cluster against the
bottom of `A + E`'s complement. An earlier revision of this axiom
quantified pairwise; it was tightened to the single-pair form on
2026-08-17 during citation review.

QA: exercised by `davis_kahan_zero_perturbation_QA` in
`Scaffold/QA/Perturbation/DavisKahan_QA.lean` (zero-perturbation
instance, where both sides vanish).
-/
axiom davis_kahan_sin_theta
    (A E : Matrix V V ℝ) (hA : A.IsSymm) (hAE : (A + E).IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : δ ≤ evals hAE ⟨(k : ℕ) + 1, hk⟩ - evals hA ⟨(k : ℕ), k.isLt⟩) :
    ‖initialProjector (A + E) hAE k - initialProjector A hA k‖ ≤ ‖E‖ / δ

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
