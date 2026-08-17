import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Rank
import Scaffold.Mathlib.Core.Norms

/-!
# Matrix Update Identities

Axiomatizes the Woodbury matrix identity and its rank-one special case,
the Sherman–Morrison formula. These describe how "events" (low-rank
updates) move spectral quantities without recomputing a full inverse,
which is the algebraic mechanism behind event-driven Laplacian updates
in `Scaffold.Mathlib.GraphTheory.Dynamics`.

The statements are honest `Matrix.inv` identities over an arbitrary field
`𝕜` with explicit invertibility hypotheses; matrix inversion is total in
Mathlib (junk-valued at singular matrices), so the `IsUnit …det`
hypotheses are what make the equalities meaningful.

Source:
- Higham, N. J., "Accuracy and Stability of Numerical Algorithms",
  2nd ed., SIAM, 2002. Book-level citation; section-level locator to be
  refined during citation review.
- Henderson, H. V. & Searle, S. R., "On deriving the inverse of a sum of
  matrices", SIAM Review 23(1):53–60, 1981 (survey of both identities).
-/

universe u v

namespace Scaffold.Mathlib.Core

open scoped Matrix

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
  {𝕜 : Type*} [Field 𝕜]

/-- The Woodbury matrix identity:
`(A + U C V)⁻¹ = A⁻¹ - A⁻¹ U (C⁻¹ + V A⁻¹ U)⁻¹ V A⁻¹`.

Here written with the equivalent middle factor `C + V A⁻¹ U`, whose
invertibility is stated as a hypothesis. `A⁻¹` is `Matrix.inv`, which is
junk-valued at singular matrices; the three `IsUnit` hypotheses are the
explicit precondition that makes the identity meaningful.

Source:
- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed., SIAM, 2002.
- Henderson & Searle, SIAM Review 23(1):53–60, 1981.

QA: no thin QA lemma yet; the identity is an unconditional equality between
total functions, so a nonzero-dimensional instance check requires either a
second axiom or explicit matrix computations deferred to a later milestone.
-/
axiom woodbury_identity (A : Matrix n n 𝕜) (U : Matrix n k 𝕜) (C : Matrix k k 𝕜)
    (V : Matrix k n 𝕜)
    (hA : IsUnit A.det) (hC : IsUnit (C + V * A⁻¹ * U).det)
    (hS : IsUnit (A + U * C * V).det) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C + V * A⁻¹ * U)⁻¹ * V * A⁻¹

/-- The Sherman–Morrison formula (rank-one Woodbury):
`(A + u vᵀ)⁻¹ = A⁻¹ - (1 + vᵀ A⁻¹ u)⁻¹ (A⁻¹ u vᵀ A⁻¹)`.

`uᵀ`-style outer products are written entrywise via `fun i j => u i * v j`,
matching Mathlib's convention of representing vectors as plain functions.
The scalar denominator hypothesis `v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ -1` makes the rank-one
update invertible.

Source:
- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed., SIAM, 2002.
- Henderson & Searle, SIAM Review 23(1):53–60, 1981.

QA: no thin QA lemma yet; see the note on `woodbury_identity`.
-/
axiom sherman_morrison (A : Matrix n n 𝕜) (u v : n → 𝕜)
    (hA : IsUnit A.det)
    (hv : v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ -1) :
    (A + Matrix.of (fun i j => u i * v j))⁻¹
      = A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (A⁻¹ * Matrix.of (fun i j => u i * v j) * A⁻¹)

end Scaffold.Mathlib.Core
