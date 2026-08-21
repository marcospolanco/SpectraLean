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
import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The projection gap: equal-rank projector identity

For two orthogonal projectors `P`, `Q` (real symmetric idempotent
matrices) of equal rank, the distance `‖P − Q‖` in the ℓ² operator
norm equals the one-sided residual norm `‖(I − Q) * P‖`. This is the
classical *gap metric* identity for subspaces of equal finite
dimension: the directed distance and the subspace distance agree.

This module delivers it as pure hard crust — **no statement is
admitted** — together with the always-true layer it sits on:

- `l2OpNorm_sub_eq_max_of_isSymm_idempotent` — for any two orthogonal
  projectors (no rank hypothesis), `‖P − Q‖` is the *maximum* of the
  two directed residual norms `‖(I − Q) * P‖` and `‖(I − P) * Q‖`.
- `l2OpNorm_one_sub_mul_eq_of_rank_eq` — the equal-rank core: the two
  directed residual norms agree when `P.rank = Q.rank`.
- `l2OpNorm_sub_eq_of_rank_eq` — the headline identity
  `‖P − Q‖ = ‖(I − Q) * P‖` under `P.rank = Q.rank`.

## Why this lemma (the Davis–Kahan Step-1 component)

The Duhamel/exponential-integral route to `davis_kahan_sin_theta`
(surveyed 2026-08-21 in `proposals/discharge-perturbation-axioms.md`)
bounds `‖(I − Q) * P‖` directly at constant 1; converting that into a
bound on `‖P − Q‖` requires exactly the equal-rank identity delivered
here (bounding the reverse directed residual instead degrades through
Weyl to the gap `δ − 2‖E‖`). This is the first of the two new
components the survey estimated; the FTC assembly is the second.

## Route (recorded before stating; no characteristic-polynomial machinery)

The equal-rank core reduces each directed residual norm to a threshold
of the sorted spectrum of `P * Q * P`:

- `‖(I − Q) * P‖² = ‖P * (I − Q) * P‖` (the C*-identity
  `Matrix.l2_opNorm_conjTranspose_mul_self`), and the latter's top
  eigenvalue is `1 − τ` with `τ := evals (P*Q*P) ⟨n − P.rank⟩` — the
  `P.rank`-th largest eigenvalue of `P * Q * P`, i.e. the smallest
  eigenvalue of the compression of `Q` to `range P.mulVecLin`.
- The two inequality directions: the upper holds because
  `P * Q * P ⪰ τ • P` on `range P` (eigenbasis expansion; the
  Courant–Fischer strict-count lemma
  `card_filter_eigvalOf_lt_evals_le` forces every nonzero eigenvalue of
  `P * Q * P` to lie at or above `τ`, and when
  `rank (P*Q*P) = P.rank` the nonzero eigenbasis spans `range P` —
  otherwise `τ = 0` by the same counting and the claim is PSD
  triviality); the lower holds at a witness (the minimizing
  eigenvector when `τ > 0`; a vector of `range P ∩ ker Q` when
  `τ = 0`, nonempty because `ker (Q*P) = ker (P*Q*P)` via the identity
  `x ⬝ᵥ ((P*Q*P) *ᵥ x) = ‖Q *ᵥ (P *ᵥ x)‖²`).
- The threshold is symmetric in the pair: `evals (P*Q*P) =
  evals (Q*P*Q)`, proved by transferring eigenspaces (`v ↦ (Q*P) *ᵥ v`,
  injective at nonzero eigenvalues since
  `(P*Q) *ᵥ ((Q*P) *ᵥ v) = μ • v`), matching per-eigenvalue basis
  counts to eigenspace dimensions
  (`finrank_span_eigvecOf_finset`), and matching zero counts through
  `Matrix.rank_eq_card_non_zero_eigs` and the rank identities above.

No step uses a characteristic polynomial; everything runs on the
proved Courant–Fischer counting lemmas and the eigenbasis identities
of `GraphTheory.Spectral`, plus Mathlib's `Matrix.L2OpNorm` C*-layer.

Source (classical background; this is a proof, not an admission):
- Kato, T., "Perturbation Theory for Linear Operators", 2nd ed.,
  Springer, 1976, Chapter I, §4 (the gap of subspaces; the
  finite-dimensional equal-dimension case).
- Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
  University Press, 2013, Section 4.2 (Courant–Fischer background for
  the threshold lemmas).

Statement differences: projectors are symmetric idempotent matrices
(not subtypes of subspaces), the norm is the scoped `Matrix.L2OpNorm`,
rank is `Matrix.rank` (`finrank` of `mulVecLin`'s range), and the
equal-rank hypothesis is stated as `P.rank = Q.rank`. The always-true
layer additionally exposes the max form, which for unequal ranks
carries the content (the max need not equal the left residual).

QA: `Scaffold/QA/Perturbation/ProjectionGap_QA.lean` pins all three
theorems on a 30°-rotation projector fixture (`‖P − Q‖ =
‖(I−Q)*P‖ = ‖(I−P)*Q‖ = 1/2`, certified by explicit residual
witnesses against the spectral pin of `‖P − Q‖`), instantiates the
max form on the unequal-rank pair `P = diag(1,0)`, `Q = 1` (where the
max is the *right* residual), and refutes the hypothesis-free form of
the headline at the same pair (`1 ≠ 0`).
-/

open scoped Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation

open Matrix SpectralGraphTheory
open Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## 1. Contraction layer for symmetric idempotents

A symmetric idempotent `S` is an orthogonal projection: it splits every
vector orthogonally as `x = S *ᵥ x + ((1 - S) *ᵥ x)`, which bounds both
parts by `x`. The Pythagoras identity avoids any Cauchy–Schwarz.
-/

section Contraction

variable {S : Matrix V V ℝ}

omit [DecidableEq V] in
/-- Symmetry moves a symmetric matrix across the dot product. -/
theorem dotProduct_mulVec_symm (hS : S.IsSymm) (x y : V → ℝ) :
    x ⬝ᵥ (S *ᵥ y) = (S *ᵥ x) ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS.eq]

omit [DecidableEq V] in
/-- **The projector square identity.** For a symmetric idempotent, the
quadratic form at `x` is the squared norm of the projected vector. -/
theorem dotProduct_mulVec_self_of_isSymm_idempotent
    (hS : S.IsSymm) (hSS : S * S = S) (x : V → ℝ) :
    x ⬝ᵥ (S *ᵥ x) = (S *ᵥ x) ⬝ᵥ (S *ᵥ x) := by
  rw [dotProduct_mulVec_symm hS x x,
    dotProduct_mulVec_symm hS (S *ᵥ x) x, Matrix.mulVec_mulVec, hSS]

/-- **Pythagoras for an orthogonal projector.** A symmetric idempotent
splits `x` into two orthogonal parts, so `x ⬝ᵥ x` is the sum of the two
squared part-norms. -/
theorem dotProduct_self_eq_parts_of_isSymm_idempotent
    (hS : S.IsSymm) (hSS : S * S = S) (x : V → ℝ) :
    x ⬝ᵥ x = (S *ᵥ x) ⬝ᵥ (S *ᵥ x) + ((1 - S) *ᵥ x) ⬝ᵥ ((1 - S) *ᵥ x) := by
  have hsub : (1 - S) *ᵥ x = x - S *ᵥ x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hcross : (S *ᵥ x) ⬝ᵥ ((1 - S) *ᵥ x) = 0 := by
    rw [hsub, Matrix.dotProduct_sub, dotProduct_mulVec_symm hS (S *ᵥ x) x,
      Matrix.mulVec_mulVec, hSS, sub_self]
  have hx : x = S *ᵥ x + (1 - S) *ᵥ x := by
    rw [hsub, add_sub_cancel]
  calc x ⬝ᵥ x = (S *ᵥ x + (1 - S) *ᵥ x) ⬝ᵥ (S *ᵥ x + (1 - S) *ᵥ x) := by
        rw [← hx]
    _ = (S *ᵥ x) ⬝ᵥ (S *ᵥ x)
          + ((1 - S) *ᵥ x) ⬝ᵥ ((1 - S) *ᵥ x) := by
        rw [Matrix.dotProduct_add, Matrix.add_dotProduct,
          Matrix.add_dotProduct,
          Matrix.dotProduct_comm ((1 - S) *ᵥ x) (S *ᵥ x), hcross,
          zero_add, add_zero]

omit [DecidableEq V] in
/-- A real dot product with itself is nonnegative (sum of squares). -/
private theorem dotProduct_self_nonneg' (v : V → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [Matrix.dotProduct]
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (v i))

/-- Each part of the orthogonal splitting is bounded by the whole. -/
theorem dotProduct_mulVec_self_le_of_isSymm_idempotent
    (hS : S.IsSymm) (hSS : S * S = S) (x : V → ℝ) :
    (S *ᵥ x) ⬝ᵥ (S *ᵥ x) ≤ x ⬝ᵥ x := by
  rw [dotProduct_self_eq_parts_of_isSymm_idempotent hS hSS x]
  exact le_add_of_nonneg_right
    (dotProduct_self_nonneg' ((1 - S) *ᵥ x))

/-- Every eigenvalue of a symmetric idempotent lies in `[0, 1]`. -/
theorem eigvalOf_isSymm_idempotent_mem (hS : S.IsSymm)
    (hSS : S * S = S) (i : V) :
    0 ≤ eigvalOf S hS i ∧ eigvalOf S hS i ≤ 1 := by
  have hvv : Matrix.dotProduct (eigvecOf S hS i) (eigvecOf S hS i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner S hS i i
  have hev : S *ᵥ eigvecOf S hS i
      = eigvalOf S hS i • eigvecOf S hS i :=
    (isHermitian_of_isSymm hS).mulVec_eigenvectorBasis i
  have hform : quadForm S (eigvecOf S hS i)
      = eigvalOf S hS i := by
    rw [quadForm, hev, Matrix.dotProduct_smul, hvv, smul_eq_mul, mul_one]
  rw [← hform, quadForm, dotProduct_mulVec_self_of_isSymm_idempotent hS hSS]
  refine ⟨dotProduct_self_nonneg' (S *ᵥ eigvecOf S hS i), ?_⟩
  rw [show (1 : ℝ) = Matrix.dotProduct (eigvecOf S hS i)
      (eigvecOf S hS i) from hvv.symm]
  exact dotProduct_mulVec_self_le_of_isSymm_idempotent hS hSS _

/-- An orthogonal projector has operator norm at most one. -/
theorem l2OpNorm_le_one_of_isSymm_idempotent
    (hS : S.IsSymm) (hSS : S * S = S) : ‖S‖ ≤ 1 := by
  refine l2OpNorm_le_of_abs_eigvalOf_le hS (by norm_num : (0 : ℝ) ≤ 1) ?_
  intro i
  obtain ⟨hlo, hhi⟩ := eigvalOf_isSymm_idempotent_mem hS hSS i
  exact abs_le.2 ⟨by linarith, by linarith⟩

end Contraction

/-!
## 2. Transport helpers and the always-true max layer
-/

section MaxLayer

omit [DecidableEq V] in
private theorem norm_euclidean_sq (y : V → ℝ) :
    ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ ^ 2
      = Matrix.dotProduct y y := by
  have h : inner ((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)
      ((WithLp.equiv 2 (V → ℝ)).symm y) = Matrix.dotProduct y y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [star_trivial]
  rw [← real_inner_self_eq_norm_sq, h]

/-- Operator-norm bound on the `mulVec` action, at the dot-product
level: the squared length of `M *ᵥ z` is at most `‖M‖²` times the
squared length of `z`. -/
theorem dotProduct_mulVec_norm2_le_l2OpNorm_sq (M : Matrix V V ℝ)
    (z : V → ℝ) :
    (M *ᵥ z) ⬝ᵥ (M *ᵥ z) ≤ ‖M‖ * ‖M‖ * (z ⬝ᵥ z) := by
  have h1 : ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)
      ((WithLp.equiv 2 (V → ℝ)).symm z)‖ ≤
      ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M :
        EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ *
        ‖((WithLp.equiv 2 (V → ℝ)).symm z : EuclideanSpace ℝ V)‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have hact : ((Matrix.toEuclideanCLM (𝕜 := ℝ) M :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V))
      ((WithLp.equiv 2 (V → ℝ)).symm z)
      = (WithLp.equiv 2 (V → ℝ)).symm (M *ᵥ z) := by
    rw [Matrix.toEuclideanCLM_piLp_equiv_symm, Matrix.toLin'_apply]
  rw [hact] at h1
  have hnorm := norm_euclidean_sq (M *ᵥ z)
  have hnormz := norm_euclidean_sq z
  calc (M *ᵥ z) ⬝ᵥ (M *ᵥ z)
      = ‖((WithLp.equiv 2 (V → ℝ)).symm (M *ᵥ z) :
          EuclideanSpace ℝ V)‖ ^ 2 := hnorm.symm
    _ ≤ (‖(Matrix.toEuclideanCLM (𝕜 := ℝ) M :
          EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)‖ *
          ‖((WithLp.equiv 2 (V → ℝ)).symm z : EuclideanSpace ℝ V)‖) ^ 2 := by
          refine pow_le_pow_left₀ (by positivity) h1 2
    _ = ‖M‖ * ‖M‖ * (z ⬝ᵥ z) := by
          rw [mul_pow, ← Matrix.cstar_norm_def, hnormz, sq]

/-- Norm upper bound from squared `mulVec` bounds. -/
private theorem l2OpNorm_le_of_mulVec_dotProduct_le {M : Matrix V V ℝ}
    {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y : V → ℝ, (M *ᵥ y) ⬝ᵥ (M *ᵥ y) ≤ c * c * (y ⬝ᵥ y)) :
    ‖M‖ ≤ c := by
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
    rw [mul_pow, norm_euclidean_sq, norm_euclidean_sq, pow_two]
    exact h ((WithLp.equiv 2 (V → ℝ)) x)
  have hfinal := abs_le_of_sq_le_sq h2' (mul_nonneg hc (norm_nonneg _))
  rwa [abs_of_nonneg (norm_nonneg _)] at hfinal

variable {P Q : Matrix V V ℝ}

omit [DecidableEq V] in
/-- Pythagoras for an orthogonal pair: if `u ⬝ᵥ w = 0` then the squared
norm of the difference splits. -/
private theorem dotProduct_sub_self_eq (u w : V → ℝ) (h : u ⬝ᵥ w = 0) :
    (u - w) ⬝ᵥ (u - w) = u ⬝ᵥ u + w ⬝ᵥ w := by
  rw [Matrix.sub_dotProduct, Matrix.dotProduct_sub,
    Matrix.dotProduct_sub, h, Matrix.dotProduct_comm w u, h, sub_zero,
    zero_sub, sub_neg_eq_add]

/-- `(1 - S) * S = 0` for an idempotent `S`. -/
private theorem one_sub_mul_self_eq_zero {S : Matrix V V ℝ}
    (hSS : S * S = S) : (1 - S) * S = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, hSS, sub_self]

/-- **The gap identity, always-true layer.** For any two orthogonal
projectors, the distance is the maximum of the two directed residual
norms. For unequal ranks the maximum is what survives (the left
residual alone can be `0` while the distance is `1`). -/
theorem l2OpNorm_sub_eq_max_of_isSymm_idempotent
    (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) :
    ‖P - Q‖ = max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ := by
  have hsymm1Q : ((1 : Matrix V V ℝ) - Q).IsSymm := by
    refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.transpose_apply, sub_apply, Matrix.one_apply]
    rw [hQ.apply j i]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hidem1Q : (1 - Q) * (1 - Q) = (1 : Matrix V V ℝ) - Q := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      hQQ, sub_self, sub_zero]
  have hsymm1P : ((1 : Matrix V V ℝ) - P).IsSymm := by
    refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.transpose_apply, sub_apply, Matrix.one_apply]
    rw [hP.apply j i]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hidem1P : (1 - P) * (1 - P) = (1 : Matrix V V ℝ) - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      hPP, sub_self, sub_zero]
  have hkillL : Q * (1 - Q) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hQQ, sub_self]
  -- the orthogonal splitting of (P - Q) x
  have hsplitM : (1 - Q) * P - Q * (1 - P) = P - Q := by
    have h1 : (1 - Q) * P = P - Q * P := by
      calc (1 - Q) * P = 1 * P - Q * P := Matrix.sub_mul _ _ _
        _ = P - Q * P := by rw [Matrix.one_mul]
    have h2 : Q * (1 - P) = Q - Q * P := by
      calc Q * (1 - P) = Q * 1 - Q * P := Matrix.mul_sub _ _ _
        _ = Q - Q * P := by rw [Matrix.mul_one]
    rw [h1, h2, sub_sub_sub_cancel_right]
  have hsplit : ∀ x : V → ℝ,
      (P - Q) *ᵥ x = ((1 - Q) * P) *ᵥ x - (Q * (1 - P)) *ᵥ x := by
    intro x
    rw [← hsplitM, Matrix.sub_mulVec]
  have horth : ∀ x : V → ℝ,
      (((1 - Q) * P) *ᵥ x) ⬝ᵥ ((Q * (1 - P)) *ᵥ x) = 0 := by
    intro x
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_mulVec_symm hQ,
      Matrix.mulVec_mulVec (P *ᵥ x) Q (1 - Q), hkillL,
      Matrix.zero_mulVec, Matrix.zero_dotProduct]
  -- transpose bridge for the right residual
  have htr : (Q * (1 - P))ᵀ = (1 - P) * Q := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one,
      hQ.eq, hP.eq]
  have hbT : ‖Q * (1 - P)‖ = ‖(1 - P) * Q‖ := by
    rw [← htr, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.l2_opNorm_conjTranspose]
  have hmaxnn : (0 : ℝ) ≤ max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ :=
    le_trans (norm_nonneg ((1 - Q) * P)) (le_max_left _ _)
  refine le_antisymm ?_ ?_
  · refine l2OpNorm_le_of_mulVec_dotProduct_le hmaxnn ?_
    intro x
    have hnorm2 : ((P - Q) *ᵥ x) ⬝ᵥ ((P - Q) *ᵥ x)
        = (((1 - Q) * P) *ᵥ x) ⬝ᵥ (((1 - Q) * P) *ᵥ x)
          + ((Q * (1 - P)) *ᵥ x) ⬝ᵥ ((Q * (1 - P)) *ᵥ x) := by
      rw [hsplit x, dotProduct_sub_self_eq _ _ (horth x)]
    have hLx : ((1 - Q) * P) *ᵥ (P *ᵥ x) = ((1 - Q) * P) *ᵥ x := by
      rw [← Matrix.mulVec_mulVec (P *ᵥ x) (1 - Q) P,
        Matrix.mulVec_mulVec x P P, hPP,
        Matrix.mulVec_mulVec x (1 - Q) P]
    have hleft : (((1 - Q) * P) *ᵥ x) ⬝ᵥ (((1 - Q) * P) *ᵥ x)
        ≤ ‖(1 - Q) * P‖ * ‖(1 - Q) * P‖ * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) := by
      rw [← hLx]
      exact dotProduct_mulVec_norm2_le_l2OpNorm_sq ((1 - Q) * P)
        (P *ᵥ x)
    have hR1Px : (Q * (1 - P)) *ᵥ ((1 - P) *ᵥ x)
        = (Q * (1 - P)) *ᵥ x := by
      rw [← Matrix.mulVec_mulVec ((1 - P) *ᵥ x) Q (1 - P),
        Matrix.mulVec_mulVec x (1 - P) (1 - P), hidem1P,
        Matrix.mulVec_mulVec x Q (1 - P)]
    have hright : ((Q * (1 - P)) *ᵥ x) ⬝ᵥ ((Q * (1 - P)) *ᵥ x)
        ≤ ‖(1 - P) * Q‖ * ‖(1 - P) * Q‖ * (((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x)) := by
      rw [← hR1Px]
      have hle := dotProduct_mulVec_norm2_le_l2OpNorm_sq (Q * (1 - P))
        ((1 - P) *ᵥ x)
      rwa [hbT] at hle
    have hpyth : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) + ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x)
        = x ⬝ᵥ x :=
      (dotProduct_self_eq_parts_of_isSymm_idempotent hP hPP x).symm
    have hmaxL : ‖(1 - Q) * P‖
        ≤ max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ := le_max_left _ _
    have hmaxR : ‖(1 - P) * Q‖
        ≤ max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ := le_max_right _ _
    have hmaxle : ‖(1 - Q) * P‖ * ‖(1 - Q) * P‖
        ≤ max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖
          * max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ :=
      mul_le_mul hmaxL hmaxL (norm_nonneg _)
        (le_trans (norm_nonneg _) hmaxL)
    have hmaxle2 : ‖(1 - P) * Q‖ * ‖(1 - P) * Q‖
        ≤ max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖
          * max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ :=
      mul_le_mul hmaxR hmaxR (norm_nonneg _)
        (le_trans (norm_nonneg _) hmaxR)
    have hple : (P *ᵥ x) ⬝ᵥ (P *ᵥ x) ≤ x ⬝ᵥ x :=
      dotProduct_mulVec_self_le_of_isSymm_idempotent hP hPP x
    have h1ple : ((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x) ≤ x ⬝ᵥ x :=
      dotProduct_mulVec_self_le_of_isSymm_idempotent
        hsymm1P hidem1P x
    calc ((P - Q) *ᵥ x) ⬝ᵥ ((P - Q) *ᵥ x)
        = (((1 - Q) * P) *ᵥ x) ⬝ᵥ (((1 - Q) * P) *ᵥ x)
          + ((Q * (1 - P)) *ᵥ x) ⬝ᵥ ((Q * (1 - P)) *ᵥ x) := hnorm2
      _ ≤ ‖(1 - Q) * P‖ * ‖(1 - Q) * P‖ * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x))
          + ‖(1 - P) * Q‖ * ‖(1 - P) * Q‖ * (((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x)) :=
          add_le_add hleft hright
      _ ≤ max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖
            * max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x))
          + max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖
            * max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖
            * (((1 - P) *ᵥ x) ⬝ᵥ ((1 - P) *ᵥ x)) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_right hmaxle
              (dotProduct_self_nonneg' (P *ᵥ x))
          · exact mul_le_mul_of_nonneg_right hmaxle2
              (dotProduct_self_nonneg' ((1 - P) *ᵥ x))
      _ = max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖
            * max ‖(1 - Q) * P‖ ‖(1 - P) * Q‖ * (x ⬝ᵥ x) := by
          rw [← hpyth, ← mul_add]
  · refine max_le ?_ ?_
    · have hfacL : (1 - Q) * P = (1 - Q) * (P - Q) := by
        rw [Matrix.mul_sub, one_sub_mul_self_eq_zero hQQ, sub_zero]
      calc ‖(1 - Q) * P‖ = ‖(1 - Q) * (P - Q)‖ := by rw [← hfacL]
        _ ≤ ‖(1 - Q)‖ * ‖P - Q‖ := Matrix.l2_opNorm_mul (1 - Q) (P - Q)
        _ ≤ 1 * ‖P - Q‖ := mul_le_mul_of_nonneg_right
            (l2OpNorm_le_one_of_isSymm_idempotent hsymm1Q hidem1Q)
            (norm_nonneg _)
        _ = ‖P - Q‖ := by rw [one_mul]
    · have hfacR : (1 - P) * Q = (1 - P) * (Q - P) := by
        rw [Matrix.mul_sub, one_sub_mul_self_eq_zero hPP, sub_zero]
      calc ‖(1 - P) * Q‖ = ‖(1 - P) * (Q - P)‖ := by rw [← hfacR]
        _ ≤ ‖(1 - P)‖ * ‖Q - P‖ := Matrix.l2_opNorm_mul (1 - P) (Q - P)
        _ ≤ 1 * ‖Q - P‖ := mul_le_mul_of_nonneg_right
            (l2OpNorm_le_one_of_isSymm_idempotent hsymm1P hidem1P)
            (norm_nonneg _)
        _ = ‖P - Q‖ := by rw [one_mul, norm_sub_rev]

end MaxLayer

/-!
## 3. The sandwich matrix `P * Q * P` and its threshold

For the pair of projectors, `A := P * Q * P` is the matrix whose sorted
spectrum carries the principal-angle information: its `P.rank`-th
largest eigenvalue `τ` is the smallest eigenvalue of the compression of
`Q` to `range P.mulVecLin`, and `1 − τ` is the squared directed
residual norm.
-/

section Core

variable {P Q : Matrix V V ℝ}

omit [DecidableEq V] in
/-- Filter-card of a predicate equals the subtype card (bridge for
`Matrix.rank_eq_card_non_zero_eigs`). -/
private theorem card_filter_univ_eq {p : V → Prop} [DecidablePred p] :
    (Finset.univ.filter p).card = Fintype.card {i // p i} := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  refine ⟨fun x => ⟨x.1, (Finset.mem_filter.1 x.2).2⟩,
    fun y => ⟨y.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, y.2⟩⟩,
    ?_, ?_⟩
  · intro x; simp
  · intro y; simp

/-- The spectrum index paired with a positive rank: `n − rank M`, the
position of the `rank M`-th largest eigenvalue (ascending index).
Shared by all threshold statements so index proof terms agree
syntactically. -/
noncomputable def rankIdx (M : Matrix V V ℝ) (hr : 0 < M.rank) :
    Fin (Fintype.card V) :=
  ⟨Fintype.card V - M.rank, by
    have := Matrix.rank_le_card_width M; omega⟩

omit [DecidableEq V] in
/-- The sandwich of a symmetric pair is symmetric. -/
theorem pqp_isSymm (hP : P.IsSymm) (hQ : Q.IsSymm) :
    (P * Q * P).IsSymm := by
  show (P * Q * P)ᵀ = P * Q * P
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hP.eq, hQ.eq,
    Matrix.mul_assoc]

omit [DecidableEq V] in
/-- **The energy identity for the sandwich.** The quadratic form of
`P * Q * P` at `x` is the squared norm of `Q` applied to the projected
vector `P *ᵥ x` — the PSD certificate, and the kernel
characterization below. -/
theorem dotProduct_pqp_mulVec_eq (hP : P.IsSymm)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (x : V → ℝ) :
    x ⬝ᵥ ((P * Q * P) *ᵥ x)
      = (Q *ᵥ (P *ᵥ x)) ⬝ᵥ (Q *ᵥ (P *ᵥ x)) := by
  rw [Matrix.mul_assoc P Q P, ← Matrix.mulVec_mulVec x P (Q * P),
    dotProduct_mulVec_symm hP x ((Q * P) *ᵥ x),
    ← Matrix.mulVec_mulVec x Q P,
    dotProduct_mulVec_self_of_isSymm_idempotent hQ hQQ (P *ᵥ x)]

omit [DecidableEq V] in
/-- The sandwich and `Q * P` have the same kernel: `P * Q * P *ᵥ x = 0`
exactly when `Q * P *ᵥ x = 0`. -/
theorem ker_pqp_eq_ker_qp (hP : P.IsSymm)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) :
    LinearMap.ker (Matrix.mulVecLin (P * Q * P))
      = LinearMap.ker (Matrix.mulVecLin (Q * P)) := by
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hx
    have h0 : x ⬝ᵥ ((P * Q * P) *ᵥ x) = 0 := by
      rw [hx, Matrix.dotProduct_zero]
    rw [dotProduct_pqp_mulVec_eq hP hQ hQQ] at h0
    have h1 := Matrix.dotProduct_self_eq_zero.mp h0
    rwa [Matrix.mulVec_mulVec x Q P] at h1
  · intro hx
    have hrew : (P * Q * P) *ᵥ x = P *ᵥ ((Q * P) *ᵥ x) := by
      rw [Matrix.mul_assoc P Q P, ← Matrix.mulVec_mulVec]
    rw [hrew, hx, Matrix.mulVec_zero]

omit [DecidableEq V] in
/-- Rank transport along the kernel identity: the sandwich and `Q * P`
have equal rank. -/
theorem rank_pqp_eq_rank_qp (hP : P.IsSymm)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) :
    (P * Q * P).rank = (Q * P).rank := by
  have hker := ker_pqp_eq_ker_qp hP hQ hQQ
  have hrk : ∀ M : Matrix V V ℝ,
      Module.finrank ℝ (LinearMap.range M.mulVecLin)
        = Fintype.card V - Module.finrank ℝ (LinearMap.ker M.mulVecLin) := by
    intro M
    have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    rw [Module.finrank_pi] at h
    omega
  show Module.finrank ℝ (LinearMap.range (P * Q * P).mulVecLin)
    = Module.finrank ℝ (LinearMap.range (Q * P).mulVecLin)
  have h1 := hrk (P * Q * P)
  have h2 := hrk (Q * P)
  rw [hker] at h1
  omega

omit [DecidableEq V] in
/-- The sandwich's rank is symmetric in the pair. -/
theorem rank_pqp_eq_rank_qpq (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) :
    (P * Q * P).rank = (Q * P * Q).rank := by
  have h1 := rank_pqp_eq_rank_qp hP hQ hQQ
  have h2 := rank_pqp_eq_rank_qp hQ hP hPP
  have h3 : (Q * P).rank = (P * Q).rank := by
    rw [← Matrix.rank_transpose (Q * P), Matrix.transpose_mul, hQ.eq,
      hP.eq]
  omega

/-- Every eigenvalue of the sandwich lies in `[0, 1]`. -/
theorem eigvalOf_pqp_mem (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (i : V) :
    0 ≤ eigvalOf (P * Q * P) (pqp_isSymm hP hQ) i
      ∧ eigvalOf (P * Q * P) (pqp_isSymm hP hQ) i ≤ 1 := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  have hvv : Matrix.dotProduct (eigvecOf (P * Q * P) hA i)
      (eigvecOf (P * Q * P) hA i) = 1 := by
    simpa [Matrix.dotProduct] using eigvecOf_inner _ hA i i
  have hev : (P * Q * P) *ᵥ eigvecOf (P * Q * P) hA i
      = eigvalOf (P * Q * P) hA i • eigvecOf (P * Q * P) hA i :=
    (isHermitian_of_isSymm hA).mulVec_eigenvectorBasis i
  have hform : quadForm (P * Q * P) (eigvecOf (P * Q * P) hA i)
      = eigvalOf (P * Q * P) hA i := by
    rw [quadForm, hev, Matrix.dotProduct_smul, hvv, smul_eq_mul, mul_one]
  rw [← hform, quadForm,
    dotProduct_pqp_mulVec_eq hP hQ hQQ]
  refine ⟨dotProduct_self_nonneg' _, ?_⟩
  calc (Q *ᵥ (P *ᵥ eigvecOf (P * Q * P) hA i)) ⬝ᵥ
        (Q *ᵥ (P *ᵥ eigvecOf (P * Q * P) hA i))
      ≤ (P *ᵥ eigvecOf (P * Q * P) hA i) ⬝ᵥ
        (P *ᵥ eigvecOf (P * Q * P) hA i) :=
        dotProduct_mulVec_self_le_of_isSymm_idempotent hQ hQQ _
    _ ≤ eigvecOf (P * Q * P) hA i ⬝ᵥ eigvecOf (P * Q * P) hA i :=
        dotProduct_mulVec_self_le_of_isSymm_idempotent hP hPP _
    _ = 1 := hvv

/-- Every entry of the sandwich's sorted spectrum lies in `[0, 1]`. -/
theorem evals_pqp_mem (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (k : Fin (Fintype.card V)) :
    0 ≤ evals (pqp_isSymm hP hQ) k
      ∧ evals (pqp_isSymm hP hQ) k ≤ 1 := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  obtain ⟨i, hi⟩ := evals_mem_eigvalOf hA k
  rw [hi]
  exact eigvalOf_pqp_mem hP hPP hQ hQQ i

/-- **Threshold lower bound (strict-count lemma).** Every *nonzero*
eigenvalue of the sandwich lies at or above the threshold
`τ := evals (P*Q*P) ⟨n − P.rank⟩`. Route: a nonzero eigenvalue strictly
below `τ` would push the strict-below-`τ` count above `n − P.rank`
(the zeros of the sandwich already fill `n − rank (P*Q*P) ≥ n − P.rank`
slots), contradicting `card_filter_eigvalOf_lt_evals_le`. -/
theorem evals_pqp_le_eigvalOf_of_ne_zero (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (hr : 0 < P.rank)
    (i : V) (hμ : eigvalOf (P * Q * P) (pqp_isSymm hP hQ) i ≠ 0) :
    evals (pqp_isSymm hP hQ) (rankIdx P hr)
      ≤ eigvalOf (P * Q * P) (pqp_isSymm hP hQ) i := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  obtain ⟨hτlo, _⟩ := evals_pqp_mem hP hPP hQ hQQ (rankIdx P hr)
  by_contra hlt
  push_neg at hlt
  obtain ⟨hμlo, _⟩ := eigvalOf_pqp_mem hP hPP hQ hQQ i
  have hτpos : 0 < evals hA (rankIdx P hr) :=
    lt_of_le_of_lt hμlo hlt
  -- the nonzero-eigenvalue count is the rank, and the zero count its
  -- complement
  have hrk : (P * Q * P).rank = (Finset.univ.filter
      fun j => eigvalOf (P * Q * P) hA j ≠ 0).card := by
    rw [card_filter_univ_eq]
    have hM : (P * Q * P).rank = Fintype.card
        {i // (isHermitian_of_isSymm hA).eigenvalues i ≠ 0} :=
      (isHermitian_of_isSymm hA).rank_eq_card_non_zero_eigs
    rw [hM]
    simp only [eigvalOf]
  have hzerocompl : (Finset.univ.filter
      fun j => eigvalOf (P * Q * P) hA j ≠ 0)ᶜ
      = Finset.univ.filter fun j => eigvalOf (P * Q * P) hA j = 0 := by
    ext j
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [not_ne_iff]
  have hcardsplit := Finset.card_add_card_compl
    (Finset.univ.filter fun j => eigvalOf (P * Q * P) hA j ≠ 0)
  rw [hzerocompl] at hcardsplit
  -- the strict-below-τ count contains the zeros plus the witness i
  have hcnt := card_filter_eigvalOf_lt_evals_le hA (rankIdx P hr)
  have hsub : (Finset.univ.filter
        fun j => eigvalOf (P * Q * P) hA j = 0) ∪ ({i} : Finset V)
      ⊆ Finset.univ.filter
        fun j => eigvalOf (P * Q * P) hA j < evals hA (rankIdx P hr) := by
    intro j hj
    rw [Finset.mem_union, Finset.mem_singleton] at hj
    rcases hj with h | h
    · rw [Finset.mem_filter] at h ⊢
      exact ⟨h.1, by
        rw [h.2]
        exact hτpos⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [h]
      exact hlt
  have hcardle := Finset.card_le_card hsub
  have hiNotZero : i ∉ Finset.univ.filter
      fun j => eigvalOf (P * Q * P) hA j = 0 := by
    rw [Finset.mem_filter]
    exact fun h => hμ h.2
  have hunion : ((Finset.univ.filter
        fun j => eigvalOf (P * Q * P) hA j = 0) ∪ ({i} : Finset V)).card
      = (Finset.univ.filter fun j => eigvalOf (P * Q * P) hA j = 0).card
        + 1 :=
    Finset.card_union_of_disjoint (by
      rw [Finset.disjoint_singleton_right]
      exact hiNotZero)
  have hrankle : (P * Q * P).rank ≤ P.rank :=
    Matrix.rank_mul_le_right _ _
  have hidxval : ((rankIdx P hr : ℕ)) = Fintype.card V - P.rank := rfl
  omega


/-- The nonzero-eigenvalue count of a symmetric matrix is its rank. -/
private theorem rank_eq_card_filter_ne {M : Matrix V V ℝ} (hM : M.IsSymm) :
    M.rank = (Finset.univ.filter fun j => eigvalOf M hM j ≠ 0).card := by
  rw [card_filter_univ_eq]
  have hM' : M.rank = Fintype.card
      {i // (isHermitian_of_isSymm hM).eigenvalues i ≠ 0} :=
    (isHermitian_of_isSymm hM).rank_eq_card_non_zero_eigs
  rw [hM']
  simp only [eigvalOf]

/-- The zero and nonzero eigenvalue counts sum to the dimension. -/
private theorem card_filter_zero_add_ne {M : Matrix V V ℝ} (hM : M.IsSymm) :
    (Finset.univ.filter fun j => eigvalOf M hM j = 0).card
      + (Finset.univ.filter fun j => eigvalOf M hM j ≠ 0).card
      = Fintype.card V := by
  have h := Finset.card_add_card_compl
    (Finset.univ.filter fun j => eigvalOf M hM j ≠ 0)
  have hc : (Finset.univ.filter fun j => eigvalOf M hM j ≠ 0)ᶜ
      = Finset.univ.filter fun j => eigvalOf M hM j = 0 := by
    ext j
    simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [not_ne_iff]
  rw [hc] at h
  omega

/-- **Threshold positivity pins the rank.** If `τ > 0` then the
sandwich has full rank `P.rank`. Route: the zero eigenvalues all lie
strictly below `τ`, so the strict-below-`τ` count `≤ n − P.rank` bounds
the zero count, forcing `rank (P*Q*P) ≥ P.rank`. -/
theorem rank_pqp_of_evals_pos (hP : P.IsSymm) (hQ : Q.IsSymm)
    (hr : 0 < P.rank)
    (hτ : 0 < evals (pqp_isSymm hP hQ) (rankIdx P hr)) :
    (P * Q * P).rank = P.rank := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  have hrkle : (P * Q * P).rank ≤ P.rank := Matrix.rank_mul_le_right _ _
  have hzerosub : (Finset.univ.filter
      fun j => eigvalOf (P * Q * P) hA j = 0)
      ⊆ Finset.univ.filter
        fun j => eigvalOf (P * Q * P) hA j < evals hA (rankIdx P hr) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, by rw [hj.2]; exact hτ⟩
  have hzero : (Finset.univ.filter
      fun j => eigvalOf (P * Q * P) hA j = 0).card
      ≤ (Finset.univ.filter
        fun j => eigvalOf (P * Q * P) hA j
          < evals hA (rankIdx P hr)).card :=
    Finset.card_le_card hzerosub
  have hlt : (Finset.univ.filter
      fun j => eigvalOf (P * Q * P) hA j
        < evals hA (rankIdx P hr)).card
      ≤ ((rankIdx P hr : ℕ)) :=
    card_filter_eigvalOf_lt_evals_le hA (rankIdx P hr)
  have hcast : ((rankIdx P hr : ℕ))
      = Fintype.card V - P.rank := rfl
  have hsplit := card_filter_zero_add_ne hA
  have hrk := rank_eq_card_filter_ne hA
  have hrankbound : P.rank ≤ Fintype.card V :=
    Matrix.rank_le_card_width P
  omega

/-- **The sandwich dominates `τ • P` on the diagonal.** The threshold
inequality: `τ * ⟨x, P x⟩ ≤ ⟨x, (P*Q*P) x⟩` for every `x`. Route: when
`τ ≤ 0` this is PSD triviality; when `τ > 0` the sandwich has full rank
`P.rank`, the nonzero eigenbasis spans `range P.mulVecLin`, and the
Parseval resolutions of both sides (with eigenvalues `≥ τ` on the
nonzero spectrum, by the strict-count lemma) compare termwise. -/
theorem evals_pqp_mul_dotProduct_P_le (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (hr : 0 < P.rank) (x : V → ℝ) :
    evals (pqp_isSymm hP hQ) (rankIdx P hr) * (x ⬝ᵥ (P *ᵥ x))
      ≤ quadForm (P * Q * P) x := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  rcases le_or_lt (evals hA (rankIdx P hr)) 0 with hτle | hτpos
  · have hself : x ⬝ᵥ (P *ᵥ x) = (P *ᵥ x) ⬝ᵥ (P *ᵥ x) :=
      dotProduct_mulVec_self_of_isSymm_idempotent hP hPP x
    have hRHS : (0 : ℝ) ≤ quadForm (P * Q * P) x := by
      rw [quadForm, dotProduct_pqp_mulVec_eq hP hQ hQQ]
      exact dotProduct_self_nonneg' _
    rw [hself]
    have step : evals hA (rankIdx P hr) * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x))
        ≤ 0 * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) := by
      nlinarith [hτle, dotProduct_self_nonneg' (P *ᵥ x)]
    calc evals hA (rankIdx P hr) * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x))
        ≤ 0 * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) := step
      _ = 0 := zero_mul _
      _ ≤ quadForm (P * Q * P) x := hRHS
  · have hrk : (P * Q * P).rank = P.rank :=
      rank_pqp_of_evals_pos hP hQ hr hτpos
    obtain ⟨t, htdef⟩ : ∃ t : Finset V, t = Finset.univ.filter
      fun j => eigvalOf (P * Q * P) hA j ≠ 0 := ⟨_, rfl⟩
    have hvfix : ∀ j ∈ t, P *ᵥ eigvecOf (P * Q * P) hA j
        = eigvecOf (P * Q * P) hA j := by
      intro j hj
      rw [htdef, Finset.mem_filter] at hj
      have hev : (P * Q * P) *ᵥ eigvecOf (P * Q * P) hA j
          = eigvalOf (P * Q * P) hA j • eigvecOf (P * Q * P) hA j :=
        (isHermitian_of_isSymm hA).mulVec_eigenvectorBasis j
      have hassoc : P * (Q * P) = P * Q * P :=
        (Matrix.mul_assoc P Q P).symm
      have hmem : P *ᵥ ((eigvalOf (P * Q * P) hA j)⁻¹ •
          (Q * P) *ᵥ eigvecOf (P * Q * P) hA j)
          = eigvecOf (P * Q * P) hA j := by
        rw [Matrix.mulVec_smul_assoc, Matrix.mulVec_mulVec, hassoc, hev,
          inv_smul_smul₀ hj.2]
      calc P *ᵥ eigvecOf (P * Q * P) hA j
          = P *ᵥ (P *ᵥ ((eigvalOf (P * Q * P) hA j)⁻¹ •
              (Q * P) *ᵥ eigvecOf (P * Q * P) hA j)) := by rw [hmem]
        _ = (P * P) *ᵥ ((eigvalOf (P * Q * P) hA j)⁻¹ •
              (Q * P) *ᵥ eigvecOf (P * Q * P) hA j) :=
            Matrix.mulVec_mulVec
              ((eigvalOf (P * Q * P) hA j)⁻¹ •
                (Q * P) *ᵥ eigvecOf (P * Q * P) hA j) P P
        _ = P *ᵥ ((eigvalOf (P * Q * P) hA j)⁻¹ •
              (Q * P) *ᵥ eigvecOf (P * Q * P) hA j) := by rw [hPP]
        _ = eigvecOf (P * Q * P) hA j := hmem
    have hspanle : Submodule.span ℝ (Set.range fun i : {y // y ∈ t} =>
        eigvecOf (P * Q * P) hA i.1) ≤ LinearMap.range P.mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact LinearMap.mem_range.2 ⟨_, hvfix i.1 i.2⟩
    have hcardt : t.card = (P * Q * P).rank := by
      rw [htdef]; exact (rank_eq_card_filter_ne hA).symm
    have hfinrankspan : Module.finrank ℝ (Submodule.span ℝ
        (Set.range fun i : {y // y ∈ t} => eigvecOf (P * Q * P) hA i.1))
        = t.card := finrank_span_eigvecOf_finset hA t
    have hfinrankrange : Module.finrank ℝ
        (LinearMap.range P.mulVecLin) = P.rank := rfl
    have hrange : Submodule.span ℝ (Set.range fun i : {y // y ∈ t} =>
          eigvecOf (P * Q * P) hA i.1) = LinearMap.range P.mulVecLin :=
      Submodule.eq_of_le_of_finrank_eq hspanle
        (by rw [hfinrankspan, hcardt, hrk, hfinrankrange])
    have hmemPx : P *ᵥ x ∈ Submodule.span ℝ
        (Set.range fun i : {y // y ∈ t} => eigvecOf (P * Q * P) hA i.1) :=
      hrange.symm ▸ LinearMap.mem_range.2 ⟨x, rfl⟩
    have hvanish : ∀ j ∉ t,
        Matrix.dotProduct (eigvecOf (P * Q * P) hA j) (P *ᵥ x) = 0 :=
      fun j hj => dotProduct_eigvecOf_eq_zero_of_mem_span hA t hj hmemPx
    have hcoef : ∀ j,
        Matrix.dotProduct (eigvecOf (P * Q * P) hA j) (P *ᵥ x)
        = if j ∈ t then Matrix.dotProduct (eigvecOf (P * Q * P) hA j) x
          else 0 := by
      intro j
      by_cases hj : j ∈ t
      · have h1 : Matrix.dotProduct (eigvecOf (P * Q * P) hA j) (P *ᵥ x)
            = Matrix.dotProduct (P *ᵥ eigvecOf (P * Q * P) hA j) x :=
          dotProduct_mulVec_symm hP _ x
        have h2 : Matrix.dotProduct (P *ᵥ eigvecOf (P * Q * P) hA j) x
            = Matrix.dotProduct (eigvecOf (P * Q * P) hA j) x := by
          rw [hvfix j hj]
        rw [h1, h2, if_pos hj]
      · have h1 : Matrix.dotProduct (eigvecOf (P * Q * P) hA j) (P *ᵥ x)
            = 0 := hvanish j hj
        rw [h1, if_neg hj]
    have hPx2 : (P *ᵥ x) ⬝ᵥ (P *ᵥ x)
        = ∑ j ∈ t, (Matrix.dotProduct (eigvecOf (P * Q * P) hA j) x) ^ 2 := by
      rw [dotProduct_eigvecOf hA (P *ᵥ x) (P *ᵥ x)]
      have hsub : ∑ i ∈ (Finset.univ : Finset V),
          Matrix.dotProduct (eigvecOf (P * Q * P) hA i) (P *ᵥ x)
            * Matrix.dotProduct (eigvecOf (P * Q * P) hA i) (P *ᵥ x)
          = ∑ j ∈ t,
          Matrix.dotProduct (eigvecOf (P * Q * P) hA j) (P *ᵥ x)
            * Matrix.dotProduct (eigvecOf (P * Q * P) hA j) (P *ᵥ x) :=
        (Finset.sum_subset (Finset.subset_univ t) (fun j _ hj => by
          have h1 : Matrix.dotProduct (eigvecOf (P * Q * P) hA j) (P *ᵥ x)
              = 0 := hvanish j hj
          rw [h1, mul_zero])).symm
      rw [hsub]
      refine Finset.sum_congr rfl fun j hj => ?_
      have h1 := hcoef j
      rw [if_pos hj] at h1
      rw [h1, sq]
    have hmu0 : ∀ j ∉ t, eigvalOf (P * Q * P) hA j = 0 := by
      intro j hj
      by_contra hne
      exact hj (htdef.symm ▸ (Finset.mem_filter.2
        ⟨Finset.mem_univ j, hne⟩))
    have hqf : quadForm (P * Q * P) x
        = ∑ j ∈ t, eigvalOf (P * Q * P) hA j
            * (Matrix.dotProduct (eigvecOf (P * Q * P) hA j) x) ^ 2 := by
      rw [quadForm, dotProduct_eigvecOf hA x ((P * Q * P) *ᵥ x)]
      have hsub : ∑ i ∈ (Finset.univ : Finset V),
          Matrix.dotProduct (eigvecOf (P * Q * P) hA i) x
            * Matrix.dotProduct (eigvecOf (P * Q * P) hA i)
              ((P * Q * P) *ᵥ x)
          = ∑ j ∈ t,
          Matrix.dotProduct (eigvecOf (P * Q * P) hA j) x
            * Matrix.dotProduct (eigvecOf (P * Q * P) hA j)
              ((P * Q * P) *ᵥ x) :=
        (Finset.sum_subset (Finset.subset_univ t) (fun j _ hj => by
          rw [dotProduct_eigvecOf_mulVec hA j x, hmu0 j hj]; ring)).symm
      rw [hsub]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [dotProduct_eigvecOf_mulVec hA j x]; ring
    calc evals hA (rankIdx P hr) * (x ⬝ᵥ (P *ᵥ x))
        = evals hA (rankIdx P hr) * ((P *ᵥ x) ⬝ᵥ (P *ᵥ x)) := by
          rw [dotProduct_mulVec_self_of_isSymm_idempotent hP hPP x]
      _ = ∑ j ∈ t, evals hA (rankIdx P hr)
            * (Matrix.dotProduct (eigvecOf (P * Q * P) hA j) x) ^ 2 := by
          rw [hPx2, Finset.mul_sum]
      _ ≤ ∑ j ∈ t, eigvalOf (P * Q * P) hA j
            * (Matrix.dotProduct (eigvecOf (P * Q * P) hA j) x) ^ 2 :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right
            (evals_pqp_le_eigvalOf_of_ne_zero hP hPP hQ hQQ hr j
              (by rw [htdef, Finset.mem_filter] at hj; exact hj.2))
            (by positivity)
      _ = quadForm (P * Q * P) x := hqf.symm


omit [DecidableEq V] in
/-- **The spectral form of the residual quadratic form.** For the
residual matrix `P − P*Q*P`, the quadratic form splits as projected
norm minus sandwich form. -/
theorem quadForm_sub_pqp_eq (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (x : V → ℝ) :
    quadForm (P - P * Q * P) x
      = (P *ᵥ x) ⬝ᵥ (P *ᵥ x)
        - (Q *ᵥ (P *ᵥ x)) ⬝ᵥ (Q *ᵥ (P *ᵥ x)) := by
  rw [quadForm, Matrix.sub_mulVec, Matrix.dotProduct_sub,
    dotProduct_mulVec_self_of_isSymm_idempotent hP hPP,
    dotProduct_pqp_mulVec_eq hP hQ hQQ]

/-- **The threshold witness.** There is a nonzero vector at which the
residual quadratic form attains at least `1 − τ` per unit norm: the
minimizing eigenvector when `τ > 0`, and a vector of
`range P ∩ ker Q` when `τ = 0` — nonempty then because the sandwich's
rank falls short of `P.rank` (the `succ_le` counting forces
`τ > 0` at full rank), so some kernel vector of the sandwich lies
outside `ker P`. -/
theorem exists_ne_quadForm_sub_pqp_ge (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (hr : 0 < P.rank) :
    ∃ z : V → ℝ, z ≠ 0 ∧
      (1 - evals (pqp_isSymm hP hQ) (rankIdx P hr)) * (z ⬝ᵥ z)
        ≤ quadForm (P - P * Q * P) z := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  rcases lt_or_eq_of_le
      (evals_pqp_mem hP hPP hQ hQQ (rankIdx P hr)).1 with hτpos | hτ0
  · obtain ⟨i, hi⟩ := evals_mem_eigvalOf hA (rankIdx P hr)
    have hμne : eigvalOf (P * Q * P) hA i ≠ 0 := by
      rw [← hi]
      exact ne_of_gt hτpos
    have hev : (P * Q * P) *ᵥ eigvecOf (P * Q * P) hA i
        = eigvalOf (P * Q * P) hA i • eigvecOf (P * Q * P) hA i :=
      (isHermitian_of_isSymm hA).mulVec_eigenvectorBasis i
    have hvv : Matrix.dotProduct (eigvecOf (P * Q * P) hA i)
        (eigvecOf (P * Q * P) hA i) = 1 := by
      simpa [Matrix.dotProduct] using eigvecOf_inner _ hA i i
    have hassoc : P * (Q * P) = P * Q * P :=
      (Matrix.mul_assoc P Q P).symm
    have hvfix : P *ᵥ eigvecOf (P * Q * P) hA i
        = eigvecOf (P * Q * P) hA i := by
      have hmem : P *ᵥ ((eigvalOf (P * Q * P) hA i)⁻¹ •
          (Q * P) *ᵥ eigvecOf (P * Q * P) hA i)
          = eigvecOf (P * Q * P) hA i := by
        rw [Matrix.mulVec_smul_assoc, Matrix.mulVec_mulVec, hassoc, hev,
          inv_smul_smul₀ hμne]
      calc P *ᵥ eigvecOf (P * Q * P) hA i
          = P *ᵥ (P *ᵥ ((eigvalOf (P * Q * P) hA i)⁻¹ •
              (Q * P) *ᵥ eigvecOf (P * Q * P) hA i)) := by rw [hmem]
        _ = (P * P) *ᵥ ((eigvalOf (P * Q * P) hA i)⁻¹ •
              (Q * P) *ᵥ eigvecOf (P * Q * P) hA i) :=
            Matrix.mulVec_mulVec _ P P
        _ = P *ᵥ ((eigvalOf (P * Q * P) hA i)⁻¹ •
              (Q * P) *ᵥ eigvecOf (P * Q * P) hA i) := by rw [hPP]
        _ = eigvecOf (P * Q * P) hA i := hmem
    have hAz : quadForm (P * Q * P) (eigvecOf (P * Q * P) hA i)
        = evals hA (rankIdx P hr) := by
      have h1 : quadForm (P * Q * P) (eigvecOf (P * Q * P) hA i)
          = eigvalOf (P * Q * P) hA i :=
        calc quadForm (P * Q * P) (eigvecOf (P * Q * P) hA i)
            = Matrix.dotProduct (eigvecOf (P * Q * P) hA i)
                ((P * Q * P) *ᵥ eigvecOf (P * Q * P) hA i) := rfl
          _ = Matrix.dotProduct (eigvecOf (P * Q * P) hA i)
                (eigvalOf (P * Q * P) hA i
                  • eigvecOf (P * Q * P) hA i) := by rw [hev]
          _ = eigvalOf (P * Q * P) hA i := by
                rw [Matrix.dotProduct_smul, hvv, smul_eq_mul, mul_one]
      rw [h1, hi]
    have hQpart : (Q *ᵥ (eigvecOf (P * Q * P) hA i)) ⬝ᵥ
        (Q *ᵥ (eigvecOf (P * Q * P) hA i))
        = quadForm (P * Q * P) (eigvecOf (P * Q * P) hA i) := by
      have he := dotProduct_pqp_mulVec_eq hP hQ hQQ
        (eigvecOf (P * Q * P) hA i)
      rw [hvfix] at he
      rw [quadForm]
      exact he.symm
    refine ⟨eigvecOf (P * Q * P) hA i, ?_, ?_⟩
    · intro hzero
      rw [hzero] at hvv
      simp at hvv
    · rw [quadForm_sub_pqp_eq hP hPP hQ hQQ, hvfix, hQpart, hAz,
        hvv, mul_one]
  · -- tau = 0: a vector of range P ∩ ker Q
    have hrkne : (P * Q * P).rank ≠ P.rank := by
      intro heq
      have hsucc2 : ((rankIdx P hr : ℕ)) + 1
          ≤ (Finset.univ.filter
              fun j => eigvalOf (P * Q * P) hA j
                ≤ evals hA (rankIdx P hr)).card :=
        succ_le_card_filter_eigvalOf_le hA (rankIdx P hr)
      have hsub : (Finset.univ.filter
          fun j => eigvalOf (P * Q * P) hA j
            ≤ evals hA (rankIdx P hr))
          ⊆ Finset.univ.filter
            fun j => eigvalOf (P * Q * P) hA j = 0 := by
        intro j hj
        simp only [Finset.mem_filter] at hj
        refine Finset.mem_filter.2 ⟨hj.1, le_antisymm ?_ ?_⟩
        · exact hj.2.trans_eq hτ0.symm
        · exact (eigvalOf_pqp_mem hP hPP hQ hQQ j).1
      have hcardle := Finset.card_le_card hsub
      have hrkS := rank_eq_card_filter_ne hA
      have hsplit := card_filter_zero_add_ne hA
      have hidxval : ((rankIdx P hr : ℕ))
          = Fintype.card V - P.rank := rfl
      have hrankbound : P.rank ≤ Fintype.card V :=
        Matrix.rank_le_card_width P
      have hzeros : (Finset.univ.filter
          fun j => eigvalOf (P * Q * P) hA j = 0).card
          = Fintype.card V - (P * Q * P).rank := by
        have h2 := card_filter_zero_add_ne hA
        have h1 := rank_eq_card_filter_ne hA
        rw [h1]
        omega
      omega
    have hrkdim : ∀ M : Matrix V V ℝ,
        Module.finrank ℝ (LinearMap.ker M.mulVecLin)
          = Fintype.card V - Module.finrank ℝ
            (LinearMap.range M.mulVecLin) := by
      intro M
      have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
      rw [Module.finrank_pi] at h
      omega
    have hrankle : (P * Q * P).rank ≤ P.rank :=
      Matrix.rank_mul_le_right _ _
    have hcard : 1 ≤ Fintype.card V :=
      Nat.le_trans (Nat.succ_le_of_lt hr) (Matrix.rank_le_card_width P)
    have hrkboundS : (P * Q * P).rank ≤ Fintype.card V :=
      Matrix.rank_le_card_width _
    have hlt : Module.finrank ℝ (LinearMap.ker (P * Q * P).mulVecLin)
        > Module.finrank ℝ (LinearMap.ker P.mulVecLin) := by
      have h3 : (P * Q * P).rank < P.rank :=
        lt_of_le_of_ne hrankle hrkne
      have h1 : Module.finrank ℝ (LinearMap.ker (P * Q * P).mulVecLin)
          = Fintype.card V - Module.finrank ℝ
            (LinearMap.range (P * Q * P).mulVecLin) := hrkdim _
      have h2 : Module.finrank ℝ (LinearMap.ker P.mulVecLin)
          = Fintype.card V - Module.finrank ℝ
            (LinearMap.range P.mulVecLin) := hrkdim _
      have hr1 : (P * Q * P).rank = Module.finrank ℝ
          (LinearMap.range (P * Q * P).mulVecLin) := rfl
      have hr2 : P.rank = Module.finrank ℝ
          (LinearMap.range P.mulVecLin) := rfl
      have hrankbound : P.rank ≤ Fintype.card V :=
        Matrix.rank_le_card_width P
      rw [hr1] at h3
      rw [hr2] at h3 hrankbound
      omega
    have hnotle : ¬ (LinearMap.ker (P * Q * P).mulVecLin
        ≤ LinearMap.ker P.mulVecLin) := by
      intro hle
      have hmono := Submodule.finrank_mono hle
      omega
    obtain ⟨x0, hx0mem, hx0not⟩ :
        ∃ x0, x0 ∈ LinearMap.ker (P * Q * P).mulVecLin
          ∧ x0 ∉ LinearMap.ker P.mulVecLin := by
      by_contra hcon
      push_neg at hcon
      exact hnotle (fun y hy => hcon y hy)
    have hker : (P * Q * P) *ᵥ x0 = 0 := by
      simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hx0mem
    have hE : (Q *ᵥ (P *ᵥ x0)) ⬝ᵥ (Q *ᵥ (P *ᵥ x0)) = 0 := by
      have h0 : x0 ⬝ᵥ ((P * Q * P) *ᵥ x0) = 0 := by
        rw [hker, Matrix.dotProduct_zero]
      rw [dotProduct_pqp_mulVec_eq hP hQ hQQ] at h0
      exact h0
    have hfix : P *ᵥ (P *ᵥ x0) = P *ᵥ x0 := by
      rw [Matrix.mulVec_mulVec x0 P P, hPP]
    refine ⟨P *ᵥ x0, ?_, ?_⟩
    · intro hzero
      exact hx0not (by
        simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
          using hzero)
    · rw [quadForm_sub_pqp_eq hP hPP hQ hQQ, hfix, hE, sub_zero,
        hτ0.symm, sub_zero, one_mul]


/-!
### Eigenbasis helpers
-/

/-- An eigenvector of the spectral theorem listing has unit squared
norm. -/
private theorem eigvecOf_dotProduct_self {M : Matrix V V ℝ}
    (hM : M.IsSymm) (i : V) :
    Matrix.dotProduct (eigvecOf M hM i) (eigvecOf M hM i) = 1 := by
  simpa [Matrix.dotProduct] using eigvecOf_inner _ hM i i

/-- The quadratic form at an eigenvector is its eigenvalue. -/
private theorem quadForm_eq_eigvalOf {M : Matrix V V ℝ} (hM : M.IsSymm)
    (i : V) :
    quadForm M (eigvecOf M hM i) = eigvalOf M hM i := by
  have hev : M *ᵥ eigvecOf M hM i
      = eigvalOf M hM i • eigvecOf M hM i :=
    (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
  rw [quadForm, hev, Matrix.dotProduct_smul,
    eigvecOf_dotProduct_self hM i, smul_eq_mul, mul_one]

set_option maxHeartbeats 1000000 in
/-- **The squared directed residual.** `‖(I − Q) * P‖² = 1 − τ`, the
threshold pin: the C*-identity collapses the residual to the spectral
projector `P − P*Q*P` (symmetric PSD), whose top eigenvalue is
`1 − τ` — bounded above by the threshold domination lemma and attained
at the threshold witness. -/
theorem l2OpNorm_one_sub_mul_sq_eq (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) (hr : 0 < P.rank) :
    ‖(1 - Q) * P‖ * ‖(1 - Q) * P‖
      = 1 - evals (pqp_isSymm hP hQ) (rankIdx P hr) := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  have hτle1 : evals hA (rankIdx P hr) ≤ 1 :=
    (evals_pqp_mem hP hPP hQ hQQ (rankIdx P hr)).2
  have hsymm1Q : ((1 : Matrix V V ℝ) - Q).IsSymm := by
    refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.transpose_apply, sub_apply, Matrix.one_apply]
    rw [hQ.apply j i]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  have hidem1Q : (1 - Q) * (1 - Q) = (1 : Matrix V V ℝ) - Q := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      hQQ, sub_self, sub_zero]
  have hprod : ((1 - Q) * P)ᵀ * ((1 - Q) * P) = P - P * Q * P := by
    rw [Matrix.transpose_mul, Matrix.transpose_sub,
      Matrix.transpose_one, hP.eq, hQ.eq,
      Matrix.mul_assoc P (1 - Q) ((1 - Q) * P),
      ← Matrix.mul_assoc (1 - Q) (1 - Q) P, hidem1Q,
      ← Matrix.mul_assoc P (1 - Q) P, Matrix.mul_sub P 1 Q,
      Matrix.mul_one, Matrix.sub_mul, hPP]
  -- the residual matrix is symmetric PSD
  have hSPsymm : (P - P * Q * P).IsSymm := by
    show (P - P * Q * P)ᵀ = P - P * Q * P
    simp only [Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_one, hP.eq, hQ.eq]
    rw [Matrix.mul_assoc P Q P]
  have hSPpsd : ∀ x : V → ℝ, 0 ≤ quadForm (P - P * Q * P) x := by
    intro x
    rw [quadForm_sub_pqp_eq hP hPP hQ hQQ,
      dotProduct_self_eq_parts_of_isSymm_idempotent hQ hQQ (P *ᵥ x),
      add_sub_cancel_left]
    exact dotProduct_self_nonneg' _
  -- the two inequalities for the top eigenvalue
  have hcard : 1 ≤ Fintype.card V :=
    Nat.le_trans (Nat.succ_le_of_lt hr) (Matrix.rank_le_card_width P)
  have hidxlt : Fintype.card V - 1 < Fintype.card V :=
    Nat.sub_lt hcard (by omega)
  have hlastle : evals hSPsymm
      ⟨Fintype.card V - 1, hidxlt⟩
      ≤ 1 - evals hA (rankIdx P hr) := by
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf hSPsymm
      ⟨Fintype.card V - 1, hidxlt⟩
    rw [hi, ← quadForm_eq_eigvalOf hSPsymm i]
    have hupper : quadForm (P - P * Q * P)
        (eigvecOf (P - P * Q * P) hSPsymm i)
        ≤ (1 - evals hA (rankIdx P hr))
          * (eigvecOf (P - P * Q * P) hSPsymm i
              ⬝ᵥ eigvecOf (P - P * Q * P) hSPsymm i) := by
      set v : V → ℝ := eigvecOf (P - P * Q * P) hSPsymm i with hvdef
      have h1 : evals hA (rankIdx P hr) * (v ⬝ᵥ (P *ᵥ v))
          ≤ quadForm (P * Q * P) v :=
        evals_pqp_mul_dotProduct_P_le hP hPP hQ hQQ hr _
      have hvv2 : v ⬝ᵥ (P *ᵥ v) = (P *ᵥ v) ⬝ᵥ (P *ᵥ v) :=
        dotProduct_mulVec_self_of_isSymm_idempotent hP hPP v
      rw [hvv2, quadForm] at h1
      rw [quadForm_sub_pqp_eq hP hPP hQ hQQ,
        ← dotProduct_pqp_mulVec_eq hP hQ hQQ v]
      have hle : (P *ᵥ v) ⬝ᵥ (P *ᵥ v) ≤ v ⬝ᵥ v :=
        dotProduct_mulVec_self_le_of_isSymm_idempotent hP hPP v
      nlinarith [hτle1, hle]
    have hvv := eigvecOf_dotProduct_self hSPsymm i
    rw [hvv, mul_one] at hupper
    exact hupper
  have hlastge : 1 - evals hA (rankIdx P hr)
      ≤ evals hSPsymm ⟨Fintype.card V - 1, hidxlt⟩ := by
    obtain ⟨z, hz0, hzle⟩ :=
      exists_ne_quadForm_sub_pqp_ge hP hPP hQ hQQ hr
    have hquad := quadForm_le_evals_last hSPsymm hcard z
    have hzpos : 0 < z ⬝ᵥ z := by
      rcases lt_or_eq_of_le (dotProduct_self_nonneg' z) with h | h
      · exact h
      · exact absurd (Matrix.dotProduct_self_eq_zero.mp h.symm) hz0
    have hnonneg : 0 ≤ evals hSPsymm ⟨Fintype.card V - 1, hidxlt⟩ := by
      obtain ⟨i, hi⟩ := evals_mem_eigvalOf hSPsymm
        ⟨Fintype.card V - 1, hidxlt⟩
      rw [hi, ← quadForm_eq_eigvalOf hSPsymm i]
      exact hSPpsd _
    nlinarith [hzle, hquad, hzpos, hnonneg]
  -- assemble through the norm-eigenvalue bridge
  have hpsdall : ∀ k : Fin (Fintype.card V),
      0 ≤ evals hSPsymm k := by
    intro k
    obtain ⟨i, hi⟩ := evals_mem_eigvalOf hSPsymm k
    rw [hi, ← quadForm_eq_eigvalOf hSPsymm i]
    exact hSPpsd _
  have hbridge := l2OpNorm_eq_max_abs_evals hSPsymm hcard
  rw [abs_of_nonneg (hpsdall _), abs_of_nonneg (hpsdall _),
    max_eq_right (evals_sorted hSPsymm
      (Fin.le_def.2 (Nat.zero_le _)))] at hbridge
  have hnormsq : ‖(1 - Q) * P‖ * ‖(1 - Q) * P‖
      = ‖P - P * Q * P‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self,
      Matrix.conjTranspose_eq_transpose_of_trivial, hprod]
  rw [hnormsq, hbridge]
  exact le_antisymm hlastle hlastge

end Core

/-!
## 4. The eigenspace transfer and spectrum equality
-/

section Transfer

variable {P Q : Matrix V V ℝ}

/-- The eigenspace of a matrix at a real spectral value, as a
submodule of plain functions. -/
def eigSpace (M : Matrix V V ℝ) (μ : ℝ) : Submodule ℝ (V → ℝ) where
  carrier := {x | M *ᵥ x = μ • x}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [Matrix.mulVec_add, ha, hb]
    module
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [Matrix.mulVec_smul_assoc, ha]
    module
  zero_mem' := by
    simp

omit [DecidableEq V] in
theorem eigSpace_mem_iff {M : Matrix V V ℝ} {μ : ℝ} {x : V → ℝ} :
    x ∈ eigSpace M μ ↔ M *ᵥ x = μ • x := Iff.rfl

/-- A zero-rank matrix is zero. -/
private theorem eq_zero_of_rank_zero {M : Matrix V V ℝ}
    (h : M.rank = 0) : M = 0 := by
  have hfr : Module.finrank ℝ ↥(LinearMap.range M.mulVecLin) = 0 := h
  have hsub : Subsingleton ↥(LinearMap.range M.mulVecLin) :=
    Module.finrank_zero_iff.1 hfr
  have hzero : ∀ j : V, M *ᵥ Pi.single j (1 : ℝ) = 0 := by
    intro j
    have hmem : M *ᵥ Pi.single j (1 : ℝ)
        ∈ LinearMap.range M.mulVecLin :=
      LinearMap.mem_range.2 ⟨Pi.single j (1 : ℝ), rfl⟩
    exact congrArg Subtype.val (hsub.elim ⟨_, hmem⟩ 0)
  have hT : Mᵀ = 0 := by
    ext i j
    have h1 := congrFun (hzero i) j
    rw [Matrix.mulVec_single_one] at h1
    simpa using h1
  calc M = (Mᵀ)ᵀ := by rw [Matrix.transpose_transpose]
    _ = (0 : Matrix V V ℝ)ᵀ := by rw [hT]
    _ = 0 := by rw [Matrix.transpose_zero]

/-- The per-eigenvalue count of the eigenbasis listing is the
dimension of the eigenspace. -/
private theorem card_filter_eigvalOf_eq_finrank_eigSpace
    {M : Matrix V V ℝ} (hM : M.IsSymm) (μ : ℝ) :
    (Finset.univ.filter fun i => eigvalOf M hM i = μ).card
      = Module.finrank ℝ (eigSpace M μ) := by
  obtain ⟨t, htdef⟩ : ∃ t : Finset V, t = Finset.univ.filter
      fun i => eigvalOf M hM i = μ := ⟨_, rfl⟩
  have hgens : ∀ i ∈ t, eigvecOf M hM i ∈ eigSpace M μ := by
    intro i hi
    rw [htdef] at hi
    simp only [Finset.mem_filter] at hi
    rw [eigSpace_mem_iff]
    have hev : M *ᵥ eigvecOf M hM i
        = eigvalOf M hM i • eigvecOf M hM i := by
      exact (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis i
    rw [hev, ← hi.2]
  have hspanle : Submodule.span ℝ (Set.range fun i : {y // y ∈ t} =>
      eigvecOf M hM i.1) ≤ eigSpace M μ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hgens i.1 i.2
  have hfspan : Module.finrank ℝ (Submodule.span ℝ
      (Set.range fun i : {y // y ∈ t} => eigvecOf M hM i.1)) = t.card :=
    finrank_span_eigvecOf_finset hM t
  have hcardge : t.card ≤ Module.finrank ℝ (eigSpace M μ) :=
    le_trans (le_of_eq hfspan.symm) (Submodule.finrank_mono hspanle)
  -- eigenspace members have no eigencomponents outside the filter
  have hsub : ∀ x ∈ eigSpace M μ, x ∈ Submodule.span ℝ
      (Set.range fun i : {y // y ∈ t} => eigvecOf M hM i.1) := by
    intro x hx
    rw [eigSpace_mem_iff] at hx
    rw [Finsupp.mem_span_range_iff_exists_finsupp]
    have hvanish : ∀ i, i ∉ t →
        Matrix.dotProduct (eigvecOf M hM i) x = 0 := by
      intro i hi
      have hl := dotProduct_eigvecOf_mulVec hM i x
      have hne : eigvalOf M hM i ≠ μ := by
        intro heq
        exact hi (htdef ▸ (Finset.mem_filter.2 ⟨Finset.mem_univ i, heq⟩))
      have hlam : eigvalOf M hM i * Matrix.dotProduct (eigvecOf M hM i) x
          = μ * Matrix.dotProduct (eigvecOf M hM i) x := by
        rw [← hl, hx, Matrix.dotProduct_smul, smul_eq_mul]
      have hz : (eigvalOf M hM i - μ)
          * Matrix.dotProduct (eigvecOf M hM i) x = 0 := by
        rw [sub_mul, hlam, sub_self]
      rcases mul_eq_zero.1 hz with h1 | h2
      · exact absurd (sub_eq_zero.1 h1) hne
      · exact h2
    refine ⟨Finsupp.onFinset (Finset.univ : Finset {y // y ∈ t})
      (fun i => Matrix.dotProduct (eigvecOf M hM i.1) x)
      (fun i _ => Finset.mem_univ _), ?_⟩
    funext a
    have hexp := eigvecOf_expansion_apply hM x a
    rw [← hexp]
    simp only [Finsupp.sum, Finsupp.support_onFinset,
      Finsupp.onFinset_apply, Finset.mem_univ, if_true,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_image
      (f := fun j => Matrix.dotProduct (eigvecOf M hM j) x
        * eigvecOf M hM j a)
      (fun _ _ _ _ h => Subtype.ext h)]
    refine Finset.sum_subset (Finset.subset_univ _)
      (fun j _ hj => by
        by_cases hit : j ∈ t
        · have hdot : Matrix.dotProduct (eigvecOf M hM j) x = 0 := by
            by_contra hd
            exact hj (Finset.mem_image.2 ⟨⟨j, hit⟩,
              Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, rfl⟩)
          rw [hdot, zero_mul]
        · rw [hvanish j hit, zero_mul])
  have hcardle : Module.finrank ℝ (eigSpace M μ) ≤ t.card := by
    have hle : eigSpace M μ ≤ Submodule.span ℝ
        (Set.range fun i : {y // y ∈ t} => eigvecOf M hM i.1) :=
      fun x hx => hsub x hx
    exact (Submodule.finrank_mono hle).trans (le_of_eq hfspan)
  exact htdef ▸ le_antisymm hcardge hcardle

omit [DecidableEq V] in
/-- **The eigenspace transfer.** At a nonzero spectral value, the two
sandwich matrices `P * Q * P` and `Q * P * Q` have equal eigenspace
dimensions: `v ↦ (Q*P) *ᵥ v` maps the first eigenspace into the second
injectively (its inverse composition is `μ⁻¹ • (P*Q) *ᵥ ·`, since
`(P*Q) *ᵥ ((Q*P) *ᵥ v) = (P*Q*P) *ᵥ v = μ • v`). -/
private theorem finrank_eigSpace_transfer (hP : P.IsSymm)
    (hPP : P * P = P) (hQ : Q.IsSymm) (hQQ : Q * Q = Q)
    {μ : ℝ} (hμ : μ ≠ 0) :
    Module.finrank ℝ (eigSpace (P * Q * P) μ)
      = Module.finrank ℝ (eigSpace (Q * P * Q) μ) := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  have hB : (Q * P * Q).IsSymm := pqp_isSymm hQ hP
  -- the commutation identities (idempotence sandwiches; each rewrite
  -- carries explicit arguments so the associativity path is fixed)
  have keyL : (Q * P) * (P * Q) = (Q * P) * Q := by
    rw [← Matrix.mul_assoc (Q * P) P Q, Matrix.mul_assoc Q P P, hPP]
  have h1 : (Q * P * Q) * (Q * P) = (Q * P) * (P * Q * P) := by
    rw [← Matrix.mul_assoc (Q * P) (P * Q) P, keyL,
      Matrix.mul_assoc (Q * P) Q (Q * P), ← Matrix.mul_assoc Q Q P,
      ← Matrix.mul_assoc (Q * P) (Q * Q) P, hQQ]
  have keyR : (P * Q) * (Q * P) = (P * Q) * P := by
    rw [← Matrix.mul_assoc (P * Q) Q P, Matrix.mul_assoc P Q Q, hQQ]
  have h1' : (P * Q * P) * (P * Q) = (P * Q) * (Q * P * Q) := by
    rw [← Matrix.mul_assoc (P * Q) (Q * P) Q, keyR,
      Matrix.mul_assoc (P * Q) P (P * Q), ← Matrix.mul_assoc P P Q,
      ← Matrix.mul_assoc (P * Q) (P * P) Q, hPP]
  have hmem : ∀ v ∈ eigSpace (P * Q * P) μ,
      (Q * P) *ᵥ v ∈ eigSpace (Q * P * Q) μ := by
    intro v hv
    rw [eigSpace_mem_iff] at hv ⊢
    calc (Q * P * Q) *ᵥ ((Q * P) *ᵥ v)
        = ((Q * P * Q) * (Q * P)) *ᵥ v :=
          Matrix.mulVec_mulVec v (Q * P * Q) (Q * P)
      _ = ((Q * P) * (P * Q * P)) *ᵥ v := by rw [h1]
      _ = (Q * P) *ᵥ ((P * Q * P) *ᵥ v) :=
          (Matrix.mulVec_mulVec v (Q * P) (P * Q * P)).symm
      _ = (Q * P) *ᵥ (μ • v) := by rw [hv]
      _ = μ • ((Q * P) *ᵥ v) := Matrix.mulVec_smul_assoc _ _ _
  have hinj : ∀ v ∈ eigSpace (P * Q * P) μ,
      (Q * P) *ᵥ v = 0 → v = 0 := by
    intro v hv hzero
    rw [eigSpace_mem_iff] at hv
    have hstep : (P * Q) *ᵥ ((Q * P) *ᵥ v) = (P * Q * P) *ᵥ v := by
      rw [Matrix.mulVec_mulVec v (P * Q) (Q * P), keyR]
    rw [hzero, Matrix.mulVec_zero] at hstep
    have h2 : μ • v = 0 := hv.symm.trans hstep.symm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hμ
    · exact h3
  have hmem' : ∀ v ∈ eigSpace (Q * P * Q) μ,
      (P * Q) *ᵥ v ∈ eigSpace (P * Q * P) μ := by
    intro v hv
    rw [eigSpace_mem_iff] at hv ⊢
    calc (P * Q * P) *ᵥ ((P * Q) *ᵥ v)
        = ((P * Q * P) * (P * Q)) *ᵥ v :=
          Matrix.mulVec_mulVec v (P * Q * P) (P * Q)
      _ = ((P * Q) * (Q * P * Q)) *ᵥ v := by rw [h1']
      _ = (P * Q) *ᵥ ((Q * P * Q) *ᵥ v) :=
          (Matrix.mulVec_mulVec v (P * Q) (Q * P * Q)).symm
      _ = (P * Q) *ᵥ (μ • v) := by rw [hv]
      _ = μ • ((P * Q) *ᵥ v) := Matrix.mulVec_smul_assoc _ _ _
  have hinj' : ∀ v ∈ eigSpace (Q * P * Q) μ,
      (P * Q) *ᵥ v = 0 → v = 0 := by
    intro v hv hzero
    rw [eigSpace_mem_iff] at hv
    have hstep : (Q * P) *ᵥ ((P * Q) *ᵥ v) = (Q * P * Q) *ᵥ v := by
      rw [Matrix.mulVec_mulVec v (Q * P) (P * Q), keyL]
    rw [hzero, Matrix.mulVec_zero] at hstep
    have h2 : μ • v = 0 := hv.symm.trans hstep.symm
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hμ
    · exact h3
  refine le_antisymm ?_ ?_
  · let φ : eigSpace (P * Q * P) μ →ₗ[ℝ] eigSpace (Q * P * Q) μ :=
      LinearMap.codRestrict _
        ((Matrix.mulVecLin (Q * P)).comp
          (Submodule.subtype (eigSpace (P * Q * P) μ)))
        (fun v => hmem v v.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := φ) ?_
    intro v1 v2 heq
    have hv1 : (P * Q * P) *ᵥ ((v1 : V → ℝ)) = μ • ((v1 : V → ℝ)) := v1.2
    have hv2 : (P * Q * P) *ᵥ ((v2 : V → ℝ)) = μ • ((v2 : V → ℝ)) := v2.2
    have hmem12 : ((v1 : V → ℝ) - (v2 : V → ℝ)) ∈ eigSpace (P * Q * P) μ := by
      rw [eigSpace_mem_iff, Matrix.mulVec_sub, hv1, hv2, smul_sub]
    have h4 : (Q * P) *ᵥ ((v1 : V → ℝ) - (v2 : V → ℝ)) = 0 := by
      have h5 : (Q * P) *ᵥ ((v1 : V → ℝ))
          = (Q * P) *ᵥ ((v2 : V → ℝ)) := congrArg Subtype.val heq
      rw [Matrix.mulVec_sub, h5, sub_self]
    have h6 := hinj _ hmem12 h4
    exact Subtype.ext (sub_eq_zero.mp h6)
  · let ψ : eigSpace (Q * P * Q) μ →ₗ[ℝ] eigSpace (P * Q * P) μ :=
      LinearMap.codRestrict _
        ((Matrix.mulVecLin (P * Q)).comp
          (Submodule.subtype (eigSpace (Q * P * Q) μ)))
        (fun v => hmem' v v.2)
    refine LinearMap.finrank_le_finrank_of_injective (f := ψ) ?_
    intro v1 v2 heq
    have hv1 : (Q * P * Q) *ᵥ ((v1 : V → ℝ)) = μ • ((v1 : V → ℝ)) := v1.2
    have hv2 : (Q * P * Q) *ᵥ ((v2 : V → ℝ)) = μ • ((v2 : V → ℝ)) := v2.2
    have hmem12 : ((v1 : V → ℝ) - (v2 : V → ℝ)) ∈ eigSpace (Q * P * Q) μ := by
      rw [eigSpace_mem_iff, Matrix.mulVec_sub, hv1, hv2, smul_sub]
    have h4 : (P * Q) *ᵥ ((v1 : V → ℝ) - (v2 : V → ℝ)) = 0 := by
      have h5 : (P * Q) *ᵥ ((v1 : V → ℝ))
          = (P * Q) *ᵥ ((v2 : V → ℝ)) := congrArg Subtype.val heq
      rw [Matrix.mulVec_sub, h5, sub_self]
    have h6 := hinj' _ hmem12 h4
    exact Subtype.ext (sub_eq_zero.mp h6)

/-- **Spectrum equality of the two sandwiches.** `P * Q * P` and
`Q * P * Q` have the same sorted spectrum. Route: per-eigenvalue
counts of the eigenbasis listing agree — at nonzero values by the
eigenspace transfer, at zero by the rank transport (equal ranks,
complementary zero counts) — and equal multisets sort equally. -/
theorem evals_pqp_eq_evals_qpq (hP : P.IsSymm) (hPP : P * P = P)
    (hQ : Q.IsSymm) (hQQ : Q * Q = Q) :
    evals (pqp_isSymm hP hQ) = evals (pqp_isSymm hQ hP) := by
  have hA : (P * Q * P).IsSymm := pqp_isSymm hP hQ
  have hB : (Q * P * Q).IsSymm := pqp_isSymm hQ hP
  have hcount : ∀ μ : ℝ,
      (Finset.univ.filter fun i => eigvalOf (P * Q * P) hA i = μ).card
        = (Finset.univ.filter
            fun i => eigvalOf (Q * P * Q) hB i = μ).card := by
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      have h1 := rank_eq_card_filter_ne hA
      have h2 := rank_eq_card_filter_ne hB
      have h3 := card_filter_zero_add_ne hA
      have h4 := card_filter_zero_add_ne hB
      have h5 := rank_pqp_eq_rank_qpq hP hPP hQ hQQ
      omega
    · rw [card_filter_eigvalOf_eq_finrank_eigSpace hA,
        card_filter_eigvalOf_eq_finrank_eigSpace hB,
        finrank_eigSpace_transfer hP hPP hQ hQQ hμ]
  -- restate the counts over the raw spectral-theorem listing
  -- (`eigvalOf` is definitionally that listing, so `exact` transfers)
  have hcount' : ∀ μ : ℝ,
      (Finset.univ.filter fun i =>
        (isHermitian_of_isSymm hA).eigenvalues i = μ).card
        = (Finset.univ.filter fun i =>
          (isHermitian_of_isSymm hB).eigenvalues i = μ).card :=
    fun μ => hcount μ
  have hms : ((Finset.univ : Finset V).val.map
      ((isHermitian_of_isSymm hA).eigenvalues))
    = ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hB).eigenvalues)) := by
    refine Multiset.ext.2 fun μ => ?_
    have hcm1 : Multiset.count μ
        ((Finset.univ : Finset V).val.map
          ((isHermitian_of_isSymm hA).eigenvalues))
        = (Finset.univ.filter fun i =>
            μ = (isHermitian_of_isSymm hA).eigenvalues i).card :=
      Multiset.count_map ((isHermitian_of_isSymm hA).eigenvalues)
        (Finset.univ : Finset V).val μ
    have hcm2 : Multiset.count μ
        ((Finset.univ : Finset V).val.map
          ((isHermitian_of_isSymm hB).eigenvalues))
        = (Finset.univ.filter fun i =>
            μ = (isHermitian_of_isSymm hB).eigenvalues i).card :=
      Multiset.count_map ((isHermitian_of_isSymm hB).eigenvalues)
        (Finset.univ : Finset V).val μ
    rw [hcm1, hcm2]
    have hc1 : (Finset.univ.filter fun i =>
        μ = (isHermitian_of_isSymm hA).eigenvalues i).card
        = (Finset.univ.filter fun i =>
            (isHermitian_of_isSymm hA).eigenvalues i = μ).card :=
      congrArg Finset.card
        (Finset.ext fun i => by simp [eq_comm])
    have hc2 : (Finset.univ.filter fun i =>
        μ = (isHermitian_of_isSymm hB).eigenvalues i).card
        = (Finset.univ.filter fun i =>
            (isHermitian_of_isSymm hB).eigenvalues i = μ).card :=
      congrArg Finset.card
        (Finset.ext fun i => by simp [eq_comm])
    rw [hc1, hc2, hcount' μ]
  have hsort : Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hA).eigenvalues))
    = Multiset.sort (fun a b => a ≤ b)
      ((Finset.univ : Finset V).val.map
        ((isHermitian_of_isSymm hB).eigenvalues)) :=
    congrArg _ hms
  funext k
  simp only [evals]
  -- the length-bound proof inside each `.get` mentions its own multiset,
  -- so `rw [hsort]` has an ill-typed motive; transfer through proof
  -- irrelevance instead
  have key : ∀ (m n : List ℝ) (hmn : m = n) (i : ℕ)
      (h1 : i < m.length) (h2 : i < n.length),
      m.get ⟨i, h1⟩ = n.get ⟨i, h2⟩ := by
    intro m n hmn i h1 h2
    subst hmn
    rfl
  exact key _ _ hsort _ _ _

end Transfer

/-!
## 5. The headline identities
-/

section Headline

variable {P Q : Matrix V V ℝ}

/-- **The equal-rank core.** The two directed residual norms agree for
orthogonal projectors of equal rank: each squared equals
`1 − τ` at the shared threshold (`evals_pqp_eq_evals_qpq` transports
the threshold across the pair). -/
theorem l2OpNorm_one_sub_mul_eq_of_rank_eq (hP : P.IsSymm)
    (hPP : P * P = P) (hQ : Q.IsSymm) (hQQ : Q * Q = Q)
    (hrank : P.rank = Q.rank) :
    ‖(1 - Q) * P‖ = ‖(1 - P) * Q‖ := by
  rcases Nat.eq_zero_or_pos P.rank with h0 | hpos
  · have hP0 : P = 0 := eq_zero_of_rank_zero h0
    have hQ0 : Q = 0 := eq_zero_of_rank_zero (by rw [← hrank]; exact h0)
    subst hP0
    subst hQ0
    simp
  · have hQpos : 0 < Q.rank := by rw [← hrank]; exact hpos
    have h1 : ‖(1 - Q) * P‖ * ‖(1 - Q) * P‖
        = 1 - evals (pqp_isSymm hP hQ) (rankIdx P hpos) :=
      l2OpNorm_one_sub_mul_sq_eq hP hPP hQ hQQ hpos
    have h2 : ‖(1 - P) * Q‖ * ‖(1 - P) * Q‖
        = 1 - evals (pqp_isSymm hQ hP) (rankIdx Q hQpos) :=
      l2OpNorm_one_sub_mul_sq_eq hQ hQQ hP hPP hQpos
    have hidx : (rankIdx Q hQpos : Fin (Fintype.card V))
        = rankIdx P hpos := by
      refine Fin.ext ?_
      simp only [rankIdx, hrank]
    have h3 : evals (pqp_isSymm hQ hP) (rankIdx Q hQpos)
        = evals (pqp_isSymm hP hQ) (rankIdx P hpos) := by
      rw [hidx, evals_pqp_eq_evals_qpq hP hPP hQ hQQ]
    have hsq : ‖(1 - Q) * P‖ * ‖(1 - Q) * P‖
        = ‖(1 - P) * Q‖ * ‖(1 - P) * Q‖ := by
      rw [h1, h2, h3]
    have hsq' : ‖(1 - Q) * P‖ ^ 2 = ‖(1 - P) * Q‖ ^ 2 := by
      rw [sq, sq]; exact hsq
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq'

/-- **The equal-rank projector identity (the gap metric for
equal-dimensional subspaces).** For orthogonal projectors of equal
rank, the distance is the directed residual norm — Kato's Chapter I §4
finite-dimensional gap identity. This is the Davis–Kahan Step-1
component: the Duhamel bound on `‖(I − Q) * P‖` transfers to
`‖P − Q‖` exactly under this lemma. -/
theorem l2OpNorm_sub_eq_of_rank_eq (hP : P.IsSymm)
    (hPP : P * P = P) (hQ : Q.IsSymm) (hQQ : Q * Q = Q)
    (hrank : P.rank = Q.rank) :
    ‖P - Q‖ = ‖(1 - Q) * P‖ := by
  rw [l2OpNorm_sub_eq_max_of_isSymm_idempotent hP hPP hQ hQQ,
    l2OpNorm_one_sub_mul_eq_of_rank_eq hP hPP hQ hQQ hrank]
  exact max_eq_left (le_refl _)

end Headline

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
