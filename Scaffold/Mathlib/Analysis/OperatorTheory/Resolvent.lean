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
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Resolvent calculus for PSD matrices

The resolvent `(A + 1)⁻¹` of a PSD matrix is the standard gap-free
alternative to spectral projection: it is defined whenever the
symmetric PSD matrix `A` is, without any spectral-gap hypothesis,
because the shift by the identity moves every eigenvalue strictly to
the right of zero.

This module delivers Steps 0, 1, and 2 of
`proposals/resolvent-calculus-psd.md`:

- **Step 0, the operator-norm bridge** (`l2OpNorm` ↔ spectrum): for a
  real symmetric matrix `M`, every eigenvalue satisfies
  `|λ| ≤ ‖M‖`, and conversely `‖M‖ ≤ c` whenever every eigenvalue
  satisfies `|λ| ≤ c`, packaged as the extremal-index equality
  `‖M‖ = max |evals hM 0| |evals hM last|`. Route decision (recorded):
  the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is
  **structurally inapplicable** to real matrices — it is stated for
  `[CStarAlgebra A]`, which extends `NormedAlgebra ℂ A` and
  `StarModule ℂ A`, and `NormedAlgebra ℂ (Matrix n n ℝ)` does not
  resolve (real matrices are not a complex algebra; elaboration
  checked on the pinned Mathlib). The scoped `Matrix.L2OpNorm`
  instances `NormedRing` and `CStarRing` do resolve, but the
  spectral-radius lemma is out of reach through them. The adopted
  fallback is the proposal's own contingency: a from-scratch
  finite-dimensional argument through Scaffold's proved eigenbasis
  machinery (Parseval `dotProduct_eigvecOf`, the eigenaction identity
  `dotProduct_eigvecOf_mulVec`) and Mathlib's
  `ContinuousLinearMap.le_opNorm` / `opNorm_le_bound`, transported
  along `Matrix.cstar_norm_def` (`‖M‖ = ‖toEuclideanCLM M‖`, `rfl`).

- **Step 1, invertibility and the resolvent identity**: for every
  symmetric matrix with nonnegative quadratic form (`∀ x, 0 ≤ quadForm
  M x` — PSD in the center's hypothesis style) and every `t > 0`, the
  shifted matrix `M + t • 1` has a unit determinant (a kernel vector
  would force `‖x‖² ≤ -quadForm M x ≤ 0`), and any two such shifted
  matrices satisfy the **resolvent identity**
  `(A+1)⁻¹ - (B+1)⁻¹ = (A+1)⁻¹ * (B - A) * (B+1)⁻¹` by pure
  `nonsing_inv` algebra.

- **Step 2, the norm bound and the Lipschitz bound**: for every matrix
  with nonnegative quadratic form and every `t > 0`, the resolvent
  satisfies `‖(M + t•1)⁻¹‖ ≤ t⁻¹` (at `t = 1`: the proposal's item 2,
  `‖(A+1)⁻¹‖ ≤ 1`), and the resolvent map is `1`-Lipschitz in the
  operator norm, `‖(A+1)⁻¹ - (B+1)⁻¹‖ ≤ ‖A - B‖` (item 4). Route
  (recorded deviation from the proposal's eigenvalue-transfer sketch):
  the *energy* argument — `y = (M+t•1)⁻¹ x` has
  `t‖y‖² ≤ quadForm M y + t‖y‖² = y ⬝ᵥ x ≤ ‖y‖‖x‖` by dot-product
  Cauchy–Schwarz — packaged through the same
  `ContinuousLinearMap.opNorm_le_bound` transport spine as the bridge.
  This needs **no symmetry hypothesis** (the same strengthening as
  Step 1's invertibility theorem: only the quadratic form at the
  resolvent's own argument is evaluated) and no sorted-eigenvalue
  transfer; the Lipschitz bound then composes the Step-1 resolvent
  identity with the scoped `NormedRing` submultiplicativity and the
  norm bound on both factors, so it is load-bearing on Step 1's
  invertibility theorem and on the identity itself.

Every declaration here is proved (`#print axioms` reads only
`propext, Classical.choice, Quot.sound`); there are no new axioms.
Step 3 of the proposal (injectivity of the resolvent map) consumes
this module and is not attempted here.

The norm throughout is the `Matrix.L2OpNorm` operator norm, the same
instance the admitted `weyl_inequality` uses.
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent

open Matrix SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## 1. The operator-norm bridge (Step 0)

Transport bookkeeping between plain functions `V → ℝ` and
`EuclideanSpace ℝ V`, then the two bridge directions and their
packaged extremal form in the sorted-spectrum API.
-/

section Bridge

variable {M : Matrix V V ℝ}

omit [DecidableEq V] in
/-- The Euclidean norm squared of a plain function packaged as an
`EuclideanSpace` element is its dot product with itself (the
inner-product structure of `EuclideanSpace` is the dot product). -/
private theorem norm_euclidean_sq (y : V → ℝ) :
    ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ ^ 2
      = Matrix.dotProduct y y := by
  have h : inner ((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)
      ((WithLp.equiv 2 (V → ℝ)).symm y) = Matrix.dotProduct y y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [star_trivial]
  rw [← real_inner_self_eq_norm_sq, h]

/-- **Bridge, lower direction.** Every eigenvalue of a symmetric
matrix (in the eigenbasis listing) is bounded by the operator norm:
`|λ| ≤ ‖M‖`. Route: the unit eigenvector, packaged as a Euclidean
element, is scaled by `λ` under `toEuclideanCLM M`, and the operator
norm bounds every image norm. Load-bearing on the eigenvector
equation and on `Matrix.cstar_norm_def` (`‖M‖ = ‖toEuclideanCLM M‖`). -/
theorem abs_eigvalOf_le_l2OpNorm (hM : M.IsSymm) (i : V) :
    |eigvalOf M hM i| ≤ ‖M‖ := by
  have hvv : Matrix.dotProduct (eigvecOf M hM i) (eigvecOf M hM i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner M hM i i
  have hev : M *ᵥ eigvecOf M hM i = eigvalOf M hM i • eigvecOf M hM i :=
    (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
  have hle := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
    ((WithLp.equiv 2 (V → ℝ)).symm (eigvecOf M hM i))
  rw [Matrix.toEuclideanCLM_piLp_equiv_symm, Matrix.toLin'_apply, hev] at hle
  have hsq : ‖((WithLp.equiv 2 (V → ℝ)).symm
      (eigvalOf M hM i • eigvecOf M hM i) : EuclideanSpace ℝ V)‖ ^ 2
      = eigvalOf M hM i ^ 2 := by
    have hdot : (eigvalOf M hM i • eigvecOf M hM i) ⬝ᵥ
        (eigvalOf M hM i • eigvecOf M hM i)
        = eigvalOf M hM i ^ 2 := by
      rw [Matrix.dotProduct_smul, Matrix.smul_dotProduct, hvv]
      simp only [smul_eq_mul]
      ring
    rw [norm_euclidean_sq]
    exact hdot
  have habs : |eigvalOf M hM i| ≤ ‖((WithLp.equiv 2 (V → ℝ)).symm
      (eigvalOf M hM i • eigvecOf M hM i) : EuclideanSpace ℝ V)‖ :=
    abs_le_of_sq_le_sq hsq.symm.le (norm_nonneg _)
  have hnorm1 : ‖((WithLp.equiv 2 (V → ℝ)).symm
      (eigvecOf M hM i) : EuclideanSpace ℝ V)‖ = 1 := by
    have h2 := norm_euclidean_sq (eigvecOf M hM i)
    rw [hvv] at h2
    rcases sq_eq_one_iff.1 h2 with h | h
    · exact h
    · exact absurd (h ▸ norm_nonneg _) (by norm_num)
  calc |eigvalOf M hM i| ≤ ‖((WithLp.equiv 2 (V → ℝ)).symm
        (eigvalOf M hM i • eigvecOf M hM i) : EuclideanSpace ℝ V)‖ := habs
    _ ≤ ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M :
          EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ * ‖((WithLp.equiv 2 (V → ℝ)).symm
        (eigvecOf M hM i) : EuclideanSpace ℝ V)‖ := hle
    _ = ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M :
          EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ := by rw [hnorm1, mul_one]
    _ = ‖M‖ := (Matrix.cstar_norm_def M).symm

/-- **Bridge, upper direction.** If every eigenvalue of a symmetric
matrix satisfies `|λ| ≤ c`, then the operator norm satisfies
`‖M‖ ≤ c`. Route: the Parseval resolution of `‖M *ᵥ y‖²` as
`∑ i, λ i² * (v i ⬝ᵥ y)²` (the eigenaction identity in both slots),
bounded termwise against `c² ∑ i, (v i ⬝ᵥ y)² = c² * ‖y‖²`, then
`ContinuousLinearMap.opNorm_le_bound`. Load-bearing on Parseval
(`dotProduct_eigvecOf`), the eigenaction identity
(`dotProduct_eigvecOf_mulVec`), and `Matrix.cstar_norm_def`. -/
theorem l2OpNorm_le_of_abs_eigvalOf_le (hM : M.IsSymm) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |eigvalOf M hM i| ≤ c) :
    ‖M‖ ≤ c := by
  have key : ∀ y : V → ℝ,
      ‖((WithLp.equiv 2 (V → ℝ)).symm (M *ᵥ y) : EuclideanSpace ℝ V)‖ ^ 2
        ≤ c ^ 2 * ‖((WithLp.equiv 2 (V → ℝ)).symm y :
            EuclideanSpace ℝ V)‖ ^ 2 := by
    intro y
    rw [norm_euclidean_sq, norm_euclidean_sq]
    rw [dotProduct_eigvecOf hM (M *ᵥ y) (M *ᵥ y),
      dotProduct_eigvecOf hM y y]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_)
      (ge_of_eq (Finset.mul_sum _ _ _))
    have hcoef : Matrix.dotProduct (eigvecOf M hM i) (M *ᵥ y)
        = eigvalOf M hM i * Matrix.dotProduct (eigvecOf M hM i) y :=
      dotProduct_eigvecOf_mulVec hM i y
    have hsq : eigvalOf M hM i * eigvalOf M hM i ≤ c * c := by
      obtain ⟨h1, h2⟩ := abs_le.mp (h i)
      have := sq_le_sq' h1 h2
      simpa [sq] using this
    rw [hcoef]
    nlinarith [hsq, sq_nonneg (Matrix.dotProduct (eigvecOf M hM i) y)]
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) hc ?_
  intro x
  have hxe : x = (WithLp.equiv 2 (V → ℝ)).symm
      ((WithLp.equiv 2 (V → ℝ)) x) := (Equiv.apply_symm_apply _ _).symm
  have hact : ((Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) x
      = (WithLp.equiv 2 (V → ℝ)).symm
          (M *ᵥ ((WithLp.equiv 2 (V → ℝ)) x)) := by
    conv_lhs => rw [hxe]
    rw [Matrix.toEuclideanCLM_piLp_equiv_symm, Matrix.toLin'_apply]
  rw [hact, hxe]
  have h2' : ‖((WithLp.equiv 2 (V → ℝ)).symm
      (M *ᵥ ((WithLp.equiv 2 (V → ℝ)) x)) : EuclideanSpace ℝ V)‖ ^ 2
      ≤ (c * ‖((WithLp.equiv 2 (V → ℝ)).symm
          ((WithLp.equiv 2 (V → ℝ)) x) : EuclideanSpace ℝ V)‖) ^ 2 := by
    rw [mul_pow]
    exact key _
  have hfinal := abs_le_of_sq_le_sq h2' (mul_nonneg hc (norm_nonneg _))
  rwa [abs_of_nonneg (norm_nonneg _)] at hfinal

end Bridge

/-!
## 2. Sorted-spectrum forms of the bridge

The `evals` API is the one downstream statements (Weyl bounds,
Cheeger, certificates) are phrased in; these corollaries restate both
bridge directions there, through the sorted-multiset membership lemmas.
-/

section Evals

variable {M : Matrix V V ℝ}

/-- An interval pin: a point between two reals is bounded in absolute
value by the larger endpoint absolute value. -/
private theorem abs_le_max_abs_of_le {l x u : ℝ} (hl : l ≤ x) (hu : x ≤ u) :
    |x| ≤ max |l| |u| := by
  have h3 : |l| ≤ max |l| |u| := le_max_left _ _
  have h4 : |u| ≤ max |l| |u| := le_max_right _ _
  rcases le_total 0 x with hx | hx
  · have hx' : |x| = x := abs_of_nonneg hx
    have hu' : x ≤ |u| := hu.trans (le_abs_self u)
    have hchain := hu'.trans h4
    rw [hx']
    linarith
  · have hx' : |x| = -x := abs_of_nonpos hx
    have hl' : -x ≤ -l := by linarith
    have hl'' : -l ≤ |l| := by linarith [neg_abs_le l]
    have hchain := hl'.trans (hl''.trans h3)
    rw [hx']
    linarith

/-- **Bridge, lower direction, sorted-spectrum form:** every entry of
the sorted spectrum is bounded by the operator norm. -/
theorem abs_evals_le_l2OpNorm (hM : M.IsSymm) (k : Fin (Fintype.card V)) :
    |evals hM k| ≤ ‖M‖ := by
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf hM k
  rw [hi]
  exact abs_eigvalOf_le_l2OpNorm hM i

/-- **Bridge, upper direction, sorted-spectrum form:** if every entry
of the sorted spectrum is bounded by `c` in absolute value, then
`‖M‖ ≤ c`. Consumes the endpoint-vs-listing bounds
(`evals_first_le_eigvalOf`, `eigvalOf_le_evals_last`). -/
theorem l2OpNorm_le_of_abs_evals_le (hM : M.IsSymm) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ k : Fin (Fintype.card V), |evals hM k| ≤ c) :
    ‖M‖ ≤ c := by
  refine l2OpNorm_le_of_abs_eigvalOf_le hM hc fun i => ?_
  rcases Nat.eq_zero_or_pos (Fintype.card V) with hcard0 | hcard
  · have : IsEmpty V := Fintype.card_eq_zero_iff.1 hcard0
    exact isEmptyElim i
  have hfirst : evals hM ⟨0, hcard⟩ ≤ eigvalOf M hM i :=
    evals_first_le_eigvalOf hM (by omega) i
  have hlast : eigvalOf M hM i
      ≤ evals hM ⟨Fintype.card V - 1, by omega⟩ :=
    eigvalOf_le_evals_last hM (by omega) i
  obtain ⟨hl1, hl2⟩ := abs_le.mp (h ⟨Fintype.card V - 1, by omega⟩)
  obtain ⟨hf1, hf2⟩ := abs_le.mp (h ⟨0, hcard⟩)
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- **The packaged operator-norm bridge:** the operator norm of a
symmetric matrix is the larger absolute value of the two extremal
sorted eigenvalues — the finite-dimensional spectral-radius identity
for real symmetric matrices, in Scaffold's sorted-spectrum API. This
is the Step 0 target statement of `proposals/resolvent-calculus-psd.md`.
-/
theorem l2OpNorm_eq_max_abs_evals (hM : M.IsSymm) (hcard : 1 ≤ Fintype.card V) :
    ‖M‖ = max |evals hM ⟨0, by omega⟩|
      |evals hM ⟨Fintype.card V - 1, by omega⟩| := by
  refine le_antisymm
    (l2OpNorm_le_of_abs_evals_le hM
      ((abs_nonneg _).trans (le_max_left _ _)) ?_)
    (max_le (abs_evals_le_l2OpNorm hM _) (abs_evals_le_l2OpNorm hM _))
  intro k
  exact abs_le_max_abs_of_le
    (evals_sorted hM (Fin.le_def.2 (Nat.zero_le _)))
    (evals_sorted hM (Fin.le_def.2 (by
      have hk := k.isLt
      simp only [Fin.val] at hk ⊢
      omega)))

end Evals

/-!
## 3. Invertibility of the shifted PSD matrix (Step 1, item 1)

A symmetric PSD matrix shifted by `t • 1` with `t > 0` is invertible:
a kernel vector `x` would give
`0 = xᵀ(M + t•1)x = quadForm M x + t‖x‖²` with both terms
nonnegative and the second positive — the spectral-gap-free
invertibility fact the resolvent exists for.
-/

section Invertible

/-- For a matrix with everywhere-nonnegative quadratic form and any
`t > 0`, the shift `M + t • 1` has a unit determinant. No symmetry
hypothesis is needed: the argument only evaluates the quadratic form
at the one hypothetical kernel vector. -/
theorem isUnit_det_add_smul_one_of_quadForm_nonneg {M : Matrix V V ℝ}
    (hpsd : ∀ x, 0 ≤ quadForm M x) {t : ℝ} (ht : 0 < t) :
    IsUnit (M + t • 1).det := by
  rcases eq_or_ne (M + t • 1).det 0 with hdet | hdet
  · obtain ⟨v, hv0, hvm⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    have hexp : (t • (1 : Matrix V V ℝ)) *ᵥ v = t • v := by
      rw [Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
    have hexpand : (M + t • 1) *ᵥ v = M *ᵥ v + t • v := by
      rw [Matrix.add_mulVec, hexp]
    have hzero : Matrix.dotProduct v (M *ᵥ v) + t * Matrix.dotProduct v v
        = 0 := by
      have hlhs : Matrix.dotProduct v ((M + t • 1) *ᵥ v) = 0 := by
        rw [hvm, Matrix.dotProduct_zero]
      rw [hexpand, Matrix.dotProduct_add, Matrix.dotProduct_smul,
        smul_eq_mul] at hlhs
      exact hlhs
    have hpsdv : 0 ≤ Matrix.dotProduct v (M *ᵥ v) := by
      have h := hpsd v
      rw [show quadForm M v = Matrix.dotProduct v (M *ᵥ v) from rfl] at h
      exact h
    have hvv : 0 < Matrix.dotProduct v v := dotProduct_self_pos hv0
    nlinarith [hvv, ht, hpsdv]
  · exact isUnit_iff_ne_zero.2 hdet

/-- The proposal's item 1, stated at the resolvent's own shift: for a
matrix with everywhere-nonnegative quadratic form, `M + 1` has a unit
determinant. -/
theorem isUnit_det_add_one_of_quadForm_nonneg {M : Matrix V V ℝ}
    (hpsd : ∀ x, 0 ≤ quadForm M x) :
    IsUnit (M + 1).det := by
  have hone : (1 : ℝ) • (1 : Matrix V V ℝ) = 1 := one_smul _ _
  have : M + 1 = M + (1 : ℝ) • (1 : Matrix V V ℝ) := by rw [hone]
  rw [this]
  exact isUnit_det_add_smul_one_of_quadForm_nonneg hpsd one_pos

end Invertible

/-!
## 4. The resolvent identity (Step 1, item 3)

For any two matrices whose `+1` shifts are invertible,
`(A+1)⁻¹ - (B+1)⁻¹ = (A+1)⁻¹ * (B - A) * (B+1)⁻¹` — pure
`nonsing_inv` algebra; no symmetry or PSD hypothesis enters (those are
needed only to *supply* the determinant hypotheses, as in
`isUnit_det_add_one_of_quadForm_nonneg`).
-/

/-- The **resolvent identity**: the difference of two resolvents
factors through the difference of the underlying matrices,
`(A+1)⁻¹ - (B+1)⁻¹ = (A+1)⁻¹ * (B - A) * (B+1)⁻¹`. -/
theorem resolvent_identity_sub {A B : Matrix V V ℝ}
    (hA : IsUnit (A + 1).det) (hB : IsUnit (B + 1).det) :
    (A + 1)⁻¹ - (B + 1)⁻¹ = (A + 1)⁻¹ * (B - A) * (B + 1)⁻¹ := by
  have hXA := Matrix.nonsing_inv_mul (A + 1) hA
  have hYB := Matrix.mul_nonsing_inv (B + 1) hB
  have key : (A + 1)⁻¹ * (B + 1) - 1
      = (A + 1)⁻¹ * ((B + 1) - (A + 1)) := by
    have h1 : (A + 1)⁻¹ * ((B + 1) - (A + 1))
        = (A + 1)⁻¹ * (B + 1) - (A + 1)⁻¹ * (A + 1) :=
      Matrix.mul_sub _ _ _
    rw [h1, hXA]
  calc (A + 1)⁻¹ - (B + 1)⁻¹
      = ((A + 1)⁻¹ * (B + 1) - 1) * (B + 1)⁻¹ := by
        rw [Matrix.sub_mul, Matrix.mul_assoc, hYB, Matrix.mul_one,
          Matrix.one_mul]
    _ = ((A + 1)⁻¹ * ((B + 1) - (A + 1))) * (B + 1)⁻¹ := by rw [key]
    _ = (A + 1)⁻¹ * (B - A) * (B + 1)⁻¹ := by
        refine congrArg (fun X => X * (B + 1)⁻¹) ?_
        refine congrArg ((A + 1)⁻¹ * ·) ?_
        abel

/-!
## 5. The resolvent norm bound (Step 2, item 2)

The energy route: for `y = (M + t•1)⁻¹ *ᵥ x`, the quadratic-form
hypothesis gives `t • (y ⬝ᵥ y) ≤ y ⬝ᵥ ((M + t•1) *ᵥ y) = y ⬝ᵥ x`, and
Cauchy–Schwarz bounds the right side by `‖y‖‖x‖`. Packaged through the
same `opNorm_le_bound` transport spine as the bridge, this yields the
norm bound at general `t > 0` — with **no symmetry hypothesis**
(the recorded deviation from the proposal's eigenvalue-transfer sketch,
mirroring Step 1's strengthening).
-/

section NormBound

variable {M : Matrix V V ℝ}

omit [DecidableEq V] in
/-- Cauchy–Schwarz for plain-function dot products: the transported
`abs_real_inner_le_norm`, through the same `EuclideanSpace` packaging
as the bridge's norm bookkeeping. -/
private theorem abs_dotProduct_le (x y : V → ℝ) :
    |x ⬝ᵥ y| ≤ ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖ *
      ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ := by
  have hin : inner ((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)
      ((WithLp.equiv 2 (V → ℝ)).symm y) = x ⬝ᵥ y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [star_trivial]
  have hcs := abs_real_inner_le_norm
    ((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)
    ((WithLp.equiv 2 (V → ℝ)).symm y)
  rw [hin] at hcs
  exact hcs

/-- The energy inequality behind the norm bound: if
`(M + t•1) *ᵥ y = x` with `M` of nonnegative quadratic form, then
`t • (y ⬝ᵥ y) ≤ y ⬝ᵥ x` for **any** `t` (the shift supplies `t‖y‖²` of
energy and `M` a nonnegative remainder; strict positivity of `t`
enters only at the division step in the packaged bound). -/
private theorem t_smul_dotProduct_self_le (hpsd : ∀ x, 0 ≤ quadForm M x)
    {t : ℝ} {y x : V → ℝ} (hy : (M + t • 1) *ᵥ y = x) :
    t * Matrix.dotProduct y y ≤ Matrix.dotProduct y x := by
  have hsplit : (M + t • 1) *ᵥ y = M *ᵥ y + t • y := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
  have hlhs : Matrix.dotProduct y ((M + t • 1) *ᵥ y)
      = Matrix.dotProduct y (M *ᵥ y) + t * Matrix.dotProduct y y := by
    rw [hsplit, Matrix.dotProduct_add, Matrix.dotProduct_smul, smul_eq_mul]
  rw [hy] at hlhs
  have hq : 0 ≤ quadForm M y := hpsd y
  have hqf : quadForm M y = Matrix.dotProduct y (M *ᵥ y) := rfl
  linarith

/-- **Step 2, item 2, general shift:** for every matrix with
nonnegative quadratic form (PSD in the center's hypothesis style) and
every `t > 0`, the resolvent `(M + t•1)⁻¹` is `t⁻¹`-bounded in the
operator norm. Route (recorded deviation from the proposal's
eigenvalue-transfer sketch): the energy inequality plus dot-product
Cauchy–Schwarz through the bridge's `opNorm_le_bound` transport spine —
no symmetry hypothesis is needed, and the sorted-eigenvalue transfer
for inverted matrices is never required. Load-bearing on Step 1: the
invertibility hypothesis is supplied by
`isUnit_det_add_smul_one_of_quadForm_nonneg`. -/
theorem l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg
    (hpsd : ∀ x, 0 ≤ quadForm M x) {t : ℝ} (ht : 0 < t) :
    ‖(M + t • 1)⁻¹‖ ≤ t⁻¹ := by
  have hN : IsUnit (M + t • 1).det :=
    isUnit_det_add_smul_one_of_quadForm_nonneg hpsd ht
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) ((M + t • 1)⁻¹) :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
      (le_of_lt (inv_pos.2 ht)) ?_
  intro z
  have hxe : z = (WithLp.equiv 2 (V → ℝ)).symm
      ((WithLp.equiv 2 (V → ℝ)) z) := (Equiv.apply_symm_apply _ _).symm
  have hact : ((Matrix.toEuclideanCLM (𝕜 := ℝ) ((M + t • 1)⁻¹) :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) z
      = (WithLp.equiv 2 (V → ℝ)).symm
          ((M + t • 1)⁻¹ *ᵥ (WithLp.equiv 2 (V → ℝ)) z) := by
    conv_lhs => rw [hxe]
    rw [Matrix.toEuclideanCLM_piLp_equiv_symm, Matrix.toLin'_apply]
  set x := (WithLp.equiv 2 (V → ℝ)) z with hxz
  set y := (M + t • 1)⁻¹ *ᵥ x with hyd
  have hnormz : ‖z‖
      = ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖ := by
    rw [hxe]
  rw [hact, hnormz]
  have hinv : (M + t • 1) *ᵥ y = x := by
    rw [hyd, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hN,
      Matrix.one_mulVec]
  have henergy := t_smul_dotProduct_self_le hpsd hinv
  rw [← norm_euclidean_sq y] at henergy
  have hcs := abs_dotProduct_le y x
  have hyx : Matrix.dotProduct y x
      ≤ ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ *
        ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖ :=
    (le_abs_self _).trans hcs
  have hchain : t * ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ ^ 2
      ≤ ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ *
        ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖ :=
    henergy.trans hyx
  rcases eq_or_ne ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ 0
    with h0 | hne
  · rw [h0]
    positivity
  · have hpos : 0 < ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hkey : t * ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖
          * ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖
        ≤ ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖ *
          ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ := by
      have hring : t * ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖
          * ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖
          = t * ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ ^ 2 := by
        ring
      rw [hring, mul_comm ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖
        ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖]
      exact hchain
    have hdiv : t * ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖
        ≤ ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖ :=
      (mul_le_mul_iff_of_pos_right hpos).1 hkey
    calc ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖
        = t⁻¹ * (t * ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ht), one_mul]
      _ ≤ t⁻¹ * ‖((WithLp.equiv 2 (V → ℝ)).symm x : EuclideanSpace ℝ V)‖ :=
          mul_le_mul_of_nonneg_left hdiv (inv_nonneg.2 ht.le)

/-- **Step 2, item 2**, the proposal's statement: the resolvent
`(A+1)⁻¹` of a matrix with nonnegative quadratic form is a contraction
in the operator norm. -/
theorem l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg
    (hpsd : ∀ x, 0 ≤ quadForm M x) :
    ‖(M + 1)⁻¹‖ ≤ 1 := by
  have hone : (1 : ℝ) • (1 : Matrix V V ℝ) = 1 := one_smul _ _
  have hM : M + 1 = M + (1 : ℝ) • (1 : Matrix V V ℝ) := by rw [hone]
  have h := l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg hpsd one_pos
  rw [inv_one] at h
  rw [hM]
  exact h

end NormBound

/-!
## 6. The Lipschitz bound (Step 2, item 4)

The resolvent map `A ↦ (A+1)⁻¹` is `1`-Lipschitz in the operator norm
on the matrices with nonnegative quadratic form: factor the difference
by the Step-1 resolvent identity, then bound each factor — the two
resolvents by the norm bound (item 2) and the middle by the scoped
`NormedRing` submultiplicativity. Load-bearing on Step 1 throughout:
the determinant hypotheses are supplied by the Step-1 invertibility
theorem, and the factoring *is* the Step-1 identity.
-/

/-- **Step 2, item 4 — the Lipschitz bound:** for any two matrices
with nonnegative quadratic form,
`‖(A + 1)⁻¹ - (B + 1)⁻¹‖ ≤ ‖A - B‖`. -/
theorem l2OpNorm_resolvent_sub_le_of_quadForm_nonneg
    {A B : Matrix V V ℝ}
    (hA : ∀ x, 0 ≤ quadForm A x) (hB : ∀ x, 0 ≤ quadForm B x) :
    ‖(A + 1)⁻¹ - (B + 1)⁻¹‖ ≤ ‖A - B‖ := by
  have hA' := isUnit_det_add_one_of_quadForm_nonneg hA
  have hB' := isUnit_det_add_one_of_quadForm_nonneg hB
  have hnormA : ‖(A + 1)⁻¹‖ ≤ 1 :=
    l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg hA
  have hnormB : ‖(B + 1)⁻¹‖ ≤ 1 :=
    l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg hB
  have hBA : ‖B - A‖ = ‖A - B‖ := norm_sub_rev B A
  have hBAle : ‖B - A‖ ≤ ‖A - B‖ := by rw [hBA]
  calc ‖(A + 1)⁻¹ - (B + 1)⁻¹‖
      = ‖(A + 1)⁻¹ * (B - A) * (B + 1)⁻¹‖ := by
        rw [resolvent_identity_sub hA' hB']
    _ = ‖(A + 1)⁻¹ * ((B - A) * (B + 1)⁻¹)‖ := by rw [Matrix.mul_assoc]
    _ ≤ ‖(A + 1)⁻¹‖ * ‖(B - A) * (B + 1)⁻¹‖ := norm_mul_le _ _
    _ ≤ ‖(A + 1)⁻¹‖ * (‖B - A‖ * ‖(B + 1)⁻¹‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ 1 * (‖A - B‖ * 1) := by
        refine mul_le_mul hnormA ?_
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
        exact mul_le_mul hBAle hnormB (norm_nonneg _) (norm_nonneg _)
    _ = ‖A - B‖ := by ring

end Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent
