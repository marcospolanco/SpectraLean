import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Rank
import Scaffold.Mathlib.Core.Norms

/-!
# Matrix Update Identities

The Woodbury matrix identity, *proved* from Mathlib
(`Matrix.invOf_add_mul_mul`), and its rank-one special case, the
Sherman–Morrison formula — also *proved*, as a specialization of the
Woodbury theorem at `k = Fin 1`. These describe how "events"
(low-rank updates) move spectral quantities without recomputing a full
inverse, which is the algebraic mechanism behind event-driven Laplacian
updates in `Scaffold.Mathlib.GraphTheory.Dynamics`.

The statements are honest `Matrix.inv` identities over an arbitrary field
`𝕜` with explicit invertibility hypotheses; matrix inversion is total in
Mathlib (junk-valued at singular matrices), so the `IsUnit …det`
hypotheses are what make the equalities meaningful.

Repair record (2026-08-18): `woodbury_identity` was previously an
admitted axiom with middle factor `C + V A⁻¹ U` and no invertibility
hypothesis on `C`. That statement is *false* — in the scalar case
`A = 1, U = V = 1, C = 0` every stated hypothesis holds while the two
sides evaluate to `1` and `0`; see
`Scaffold.QA.Core.MatrixUpdates_QA.old_woodbury_identity_refuted_QA`.
It was replaced the same day by the present theorem, proved from
Mathlib, with the standard middle factor `C⁻¹ + V A⁻¹ U` and the three
explicit `IsUnit` determinant hypotheses (per
`proposals/repair-and-retire-woodbury.md`).

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

Proved from Mathlib's `Matrix.invOf_add_mul_mul` (the `⅟` version of the
identity, `Mathlib/Data/Matrix/Invertible.lean`) through the
`NonsingularInverse` bridges `Matrix.invertibleOfIsUnitDet` and
`Matrix.invOf_eq_nonsing_inv`. `A⁻¹` is `Matrix.inv`, which is
junk-valued at singular matrices; the three `IsUnit` determinant
hypotheses are the explicit precondition that makes the identity
meaningful. Invertibility of the sum `A + U C V` is *not* a hypothesis:
Mathlib's `Matrix.invertibleAddMulMul` constructs its `Invertible`
instance from the three given ones, which is also why the middle factor
must be `C⁻¹ + V A⁻¹ U` (the form the identity is stated over) rather
than the former axiom's `C + V A⁻¹ U`.

Statement-shape repair (2026-08-18): the former admitted axiom at this
name used the middle factor `(C + V A⁻¹ U)⁻¹` with no invertibility
hypothesis on `C`; that statement is false (scalar instance
`A = 1, U = V = 1, C = 0`), refuted in
`Scaffold.QA.Core.MatrixUpdates_QA.old_woodbury_identity_refuted_QA`.
The corrected statement is an intentional public API migration; the old
shape had zero consumers.

Source:
- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed., SIAM, 2002.
- Henderson & Searle, SIAM Review 23(1):53–60, 1981.

QA: `Scaffold.QA.Core.MatrixUpdates_QA` — the refutation of the retired
false shape, positive instances of the corrected identity at nonzero
scalars and at a non-scalar rank-one update, and cross-checks of the
hypotheses' load-bearing role.
-/
theorem woodbury_identity (A : Matrix n n 𝕜) (U : Matrix n k 𝕜) (C : Matrix k k 𝕜)
    (V : Matrix k n 𝕜)
    (hA : IsUnit A.det) (hC : IsUnit C.det)
    (hM : IsUnit (C⁻¹ + V * A⁻¹ * U).det) :
    (A + U * C * V)⁻¹ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  letI iA := Matrix.invertibleOfIsUnitDet A hA
  letI iC := Matrix.invertibleOfIsUnitDet C hC
  have hMid : IsUnit (⅟C + V * ⅟A * U).det := by
    rw [Matrix.invOf_eq_nonsing_inv C, Matrix.invOf_eq_nonsing_inv A]
    exact hM
  letI iM := Matrix.invertibleOfIsUnitDet _ hMid
  letI iS : Invertible (A + U * C * V) := Matrix.invertibleAddMulMul A U C V
  have h := Matrix.invOf_add_mul_mul A U C V
  rw [Matrix.invOf_eq_nonsing_inv (A + U * C * V),
    Matrix.invOf_eq_nonsing_inv (⅟C + V * ⅟A * U)] at h
  rw [Matrix.invOf_eq_nonsing_inv A, Matrix.invOf_eq_nonsing_inv C] at h
  exact h

/-- The Sherman–Morrison formula (rank-one Woodbury):
`(A + u vᵀ)⁻¹ = A⁻¹ - (1 + vᵀ A⁻¹ u)⁻¹ (A⁻¹ u vᵀ A⁻¹)`.

`uᵀ`-style outer products are written entrywise via `fun i j => u i * v j`,
matching Mathlib's convention of representing vectors as plain functions.
The scalar denominator hypothesis `v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ -1` makes the rank-one
update invertible.

Retirement record (2026-08-18): this was previously an admitted axiom; it
is now a proved theorem at the same name, hypotheses, and statement, as
the `k = Fin 1` specialization of `woodbury_identity` (per
`proposals/retire-sherman-morrison.md`). Unlike the Woodbury retirement,
this was a **pure proof task, not a correctness repair**: the statement
was verified against the corrected Woodbury shape first — at `C = 1` the
rank-one middle factor `(1 + v ⬝ᵥ (A⁻¹ *ᵥ u))` is exactly
`C⁻¹ + V A⁻¹ U` as a 1×1 matrix, so the former axiom's statement was
already the correct specialization. The proof is the packing plumbing:
`u`, `v` into `Fin 1` column/row matrices, the 1×1 middle factor's
determinant (a unit exactly when the denominator is nonzero, i.e. when
`hv` holds), and its inverse (the 1×1 scalar inverse).

Source:
- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed., SIAM, 2002.
- Henderson & Searle, SIAM Review 23(1):53–60, 1981.

QA: `Scaffold.QA.Core.MatrixUpdates_QA` — a rank-one positive instance
whose value is checked independently of the theorem, and a negative
witness at the excluded denominator (where the update is singular).
-/
theorem sherman_morrison (A : Matrix n n 𝕜) (u v : n → 𝕜)
    (hA : IsUnit A.det)
    (hv : v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ -1) :
    (A + Matrix.of (fun i j => u i * v j))⁻¹
      = A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (A⁻¹ * Matrix.of (fun i j => u i * v j) * A⁻¹) := by
  classical
  -- the scalar denominator is a unit exactly by `hv`
  have hs : (1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) ≠ 0 := by
    intro h
    exact hv (by linear_combination h)
  set U : Matrix n (Fin 1) 𝕜 := Matrix.of fun i _ => u i with hU
  set V : Matrix (Fin 1) n 𝕜 := Matrix.of fun _ j => v j with hV
  -- the rank-one outer product is the single-term matrix product
  have hUV : U * V = Matrix.of fun i j => u i * v j := by
    ext i j
    simp [Matrix.mul_apply, Fin.sum_univ_one, hU, hV]
  -- the Woodbury hypotheses at `C = 1`
  have hC : IsUnit ((1 : Matrix (Fin 1) (Fin 1) 𝕜).det) := by
    rw [Matrix.det_one]
    exact isUnit_one
  have hOne : ((1 : Matrix (Fin 1) (Fin 1) 𝕜)⁻¹) = 1 :=
    Matrix.inv_eq_left_inv (B := 1) (by simp)
  -- the middle factor is the 1×1 matrix with the scalar denominator entry
  have hmid : ((1 : Matrix (Fin 1) (Fin 1) 𝕜)⁻¹ + V * A⁻¹ * U)
      = Matrix.of fun _ _ : Fin 1 => 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) := by
    rw [hOne, Matrix.dotProduct_mulVec]
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_one, hU, hV]
  have hM : IsUnit (((1 : Matrix (Fin 1) (Fin 1) 𝕜)⁻¹ + V * A⁻¹ * U).det) := by
    rw [hmid, Matrix.det_fin_one]
    simpa using hs.isUnit
  -- its inverse is the 1×1 matrix with the scalar inverse entry
  have hminv : ((1 : Matrix (Fin 1) (Fin 1) 𝕜)⁻¹ + V * A⁻¹ * U)⁻¹
      = Matrix.of fun _ _ : Fin 1 => (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ := by
    rw [hmid]
    refine Matrix.inv_eq_left_inv
      (B := Matrix.of fun _ _ : Fin 1 => (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹) ?_
    ext i j
    fin_cases i
    fin_cases j
    simp [Matrix.mul_apply, Fin.sum_univ_one, inv_mul_cancel₀ hs]
  -- the Woodbury instance, then pure matrix-algebra reshaping
  have key := woodbury_identity A U (1 : Matrix (Fin 1) (Fin 1) 𝕜) V hA hC hM
  have hsum : A + Matrix.of (fun i j => u i * v j)
      = A + U * (1 : Matrix (Fin 1) (Fin 1) 𝕜) * V := by
    rw [Matrix.mul_one, hUV]
  have hS : Matrix.of (fun _ _ : Fin 1 => (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹)
      = (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (1 : Matrix (Fin 1) (Fin 1) 𝕜) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  have hAUV : (A⁻¹ * U) * V = A⁻¹ * Matrix.of (fun i j => u i * v j) := by
    rw [Matrix.mul_assoc, hUV]
  rw [hsum, key, hminv, hS, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.smul_mul, hAUV]

end Scaffold.Mathlib.Core
