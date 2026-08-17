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

/-- Davis–Kahan sin Θ bound for spectral projectors: if every eigenvalue
of `A + E` above the cut index `k` is separated by at least `δ` from
every eigenvalue of `A` at or below the cut, then the projector onto the
span of the `k+1` smallest eigenvectors moves by at most `‖E‖ / δ`.

Source:
- Davis, C. & Kahan, W. M., "The rotation of eigenvectors by a
  perturbation", SIAM Journal on Numerical Analysis 7(1):1–46, 1970.
- Yu, Y., Wang, T., Samworth, R. J., "A useful variant of the Davis–Kahan
  theorem for statisticians", Annals of Statistics 43(3):2028–2061, 2015,
  Theorem 2 (two-sided separation, projector form, constant 1).

Statement differences: the invariant subspaces are the
`SpectralGraphTheory.initialProjector` spectral projectors of the sorted
spectrum; separation is a pairwise inequality on sorted eigenvalue
indices; the distance is the ℓ² operator norm of the projector
difference (the sin Θ metric).

QA: exercised by `davis_kahan_zero_perturbation_QA` in
`Scaffold/QA/Perturbation/DavisKahan_QA.lean` (zero-perturbation
instance, where both sides vanish).
-/
axiom davis_kahan_sin_theta
    (A E : Matrix V V ℝ) (hA : A.IsSymm) (hAE : (A + E).IsSymm)
    (k : Fin (Fintype.card V)) (hk : (k : ℕ) + 1 < Fintype.card V)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ i j : Fin (Fintype.card V), (i : ℕ) ≤ (k : ℕ) → (k : ℕ) < (j : ℕ) →
      δ ≤ evals hAE j - evals hA i) :
    ‖initialProjector (A + E) hAE k - initialProjector A hA k‖ ≤ ‖E‖ / δ

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
