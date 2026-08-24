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
import Scaffold.Mathlib.GraphTheory.Band
import Scaffold.Mathlib.GraphTheory.Krylov
import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent

/-!
# Polynomial filters and band projection — the Chebyshev layer's second consumer

`proposals/polyfilter-band-projection.md`, Step 1: the matrix-level
functional calculus behind the recorded statement shape

```
‖p_d(M) − bandProjector M hM a b‖₂ ≤ ε(d, gaps)
```

of the Krylov Step-0 survey (`proposals/approximate-spectral-projection.md`),
where a polynomial filter stands in for the exact band projector.

The engine is **filter-agnostic**: `aeval_sub_bandProjector_l2OpNorm_le`
turns per-eigenvalue filter quality (near `1` in-band, small
out-of-band) into an operator-norm bound, with no eigenvalues of the
difference ever computed — the proof resolves `p(M) − B` through the
orthonormal eigenbasis (`Parseval`) and transports through the
Resolvent bridge's `ContinuousLinearMap.opNorm_le_bound` /
`Matrix.cstar_norm_def` spine. This is the first theorem holding the
Krylov polynomial transfer, the Band projector action, the Spectral
Parseval identity, and the Resolvent norm spine in one statement —
load-bearing on all four at once (the strategy's falsifiability test).

Two classical instantiations supply the explicit `ε(d, gaps)` at the
top-eigenspace band:

- **The power filter** `p_d(μ) = (μ/Ltop)^d`: ε = `(t/Ltop)^d`, the
  power-method rate — `powFilter_l2OpNorm_le`.
- **The Chebyshev-damped filter** `p_d = T_d ∘ w / T_d(w(Ltop))` at
  the Krylov layer's affine band map `w = bandMap t Lbot`: ε =
  `1/T_d(w(Ltop))`, the damped-iteration rate, strictly better than
  the power rate in the small-gap regime —
  `chebyshevFilter_l2OpNorm_le`. **This is the Chebyshev scalar
  layer's second consumer** (`abs_T_eval_le_one`,
  `one_le_eval_T_of_one_le`, `bandMap` and its pins): the same five
  declarations that carried Kaniel–Paige now carry a projector
  approximation theorem.

Scope note (recorded before stating): the *uniform* wide-band
pass-filter designs (minimax two-interval approximation) are genuine
scalar approximation theory absent from the pinned Mathlib and stay a
recorded follow-on; the two instantiations here are the top-eigenspace
designs whose scalar facts are proved on the shelf. No limiting
statement (`d → ∞`) is made — the finite-`d` calibration of the
Kaniel–Paige program, tested there and found to hold.

Everything here is proved hard crust; this module adds no axioms.

QA: `Scaffold/QA/SpectralGraph/PolyFilter_QA.lean` — exact-projector
recovery through an affine filter, the power and Chebyshev
instantiations on the `diag13` fixture with the ε constants attained
at the out-mode (so they cannot be improved for these designs), the
power-vs-Chebyshev rate comparison, and the out-of-band hypothesis
refuted in proved form (a filter perfect in-band but not small
outside, with the conclusion failing).
-/

open scoped BigOperators Matrix Matrix.L2OpNorm
open Polynomial

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## Component actions

The Band module's projector action is stated on eigenvectors; the
filter theorem needs it in the *first slot of the dot product*, pairing
the projector's action on an arbitrary vector against an eigenbasis
vector. Both lemmas below are the mirrors of the shelf's
`dotProduct_eigvecOf_mulVec` (Spectral) at the two projectors, through
symmetry of the projector and its delivered eigenbasis action. -/

/-- The threshold projector's component action: pairing the
spectral projector's action on any vector against an eigenbasis
vector picks out that eigenvalue's mode — `v i ⬝ᵥ (P_c *ᵥ y)
= χ_{λ i ≤ c} * (v i ⬝ᵥ y)`. Route: transpose the projector to its
symmetric self, apply its delivered eigenbasis action, and split the
indicator. -/
theorem eigvecOf_dotProduct_spectralProjector_mulVec {M : Matrix V V ℝ}
    (hM : M.IsSymm) (c : ℝ) (i : V) (y : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) ((spectralProjector M hM c) *ᵥ y)
      = (if eigvalOf M hM i ≤ c then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf M hM i) y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    (spectralProjector_symmetric M hM c).eq,
    spectralProjector_mulVec_eigvecOf M hM c i]
  by_cases h : eigvalOf M hM i ≤ c
  · rw [if_pos h, if_pos h, one_mul]
  · rw [if_neg h, if_neg h, zero_mul, Matrix.zero_dotProduct]

/-- The band projector's component action: `v i ⬝ᵥ (B_{a,b} *ᵥ y)`
is `(v i ⬝ᵥ y)` for an in-band mode and `0` for an out-of-band one.
The `a ≤ b` guard is load-bearing for the indicator form: the band
projector's definition is total, and at `a > b` it is the *negation*
of the `(b, a]` band, so below-both-threshold modes would read `−1`,
not `0`. -/
theorem eigvecOf_dotProduct_bandProjector_mulVec {M : Matrix V V ℝ}
    (hM : M.IsSymm) (a b : ℝ) (hab : a ≤ b) (i : V) (y : V → ℝ) :
    Matrix.dotProduct (eigvecOf M hM i) ((bandProjector M hM a b) *ᵥ y)
      = (if a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b then (1 : ℝ) else 0)
        * Matrix.dotProduct (eigvecOf M hM i) y := by
  rw [bandProjector, Matrix.sub_mulVec, Matrix.dotProduct_sub,
    eigvecOf_dotProduct_spectralProjector_mulVec hM b i y,
    eigvecOf_dotProduct_spectralProjector_mulVec hM a i y]
  by_cases h1 : eigvalOf M hM i ≤ b
  · by_cases h2 : eigvalOf M hM i ≤ a
    · rw [if_pos h1, if_pos h2,
        if_neg (fun hlt => not_lt.2 h2 hlt.1)]
      ring
    · rw [if_pos (⟨by linarith, h1⟩ : a < eigvalOf M hM i
          ∧ eigvalOf M hM i ≤ b), if_pos h1, if_neg h2]
      ring
  · have hband : ¬(a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b) :=
      fun hb => h1 hb.2
    have hlea : ¬(eigvalOf M hM i ≤ a) := fun hle => h1 (hle.trans hab)
    rw [if_neg h1, if_neg hband, if_neg hlea]
    ring

/-! ## The transfer engine

The proof mirrors the Resolvent bridge's upper direction
(`l2OpNorm_le_of_abs_eigvalOf_le`): resolve the difference's action
through the eigenbasis, bound termwise, sum against Parseval, and
transport through the C*-norm spine. The survey's key finding: no
eigenvalues of the difference matrix are needed anywhere. -/

omit [DecidableEq V] in
/-- The Euclidean norm squared of a plain function packaged as a
`EuclideanSpace` element is its dot product with itself (the Resolvent
bridge's private spine, restated here for this module's use). -/
private theorem norm_euclidean_sq (y : V → ℝ) :
    ‖((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)‖ ^ 2
      = Matrix.dotProduct y y := by
  have h : inner ((WithLp.equiv 2 (V → ℝ)).symm y : EuclideanSpace ℝ V)
      ((WithLp.equiv 2 (V → ℝ)).symm y) = Matrix.dotProduct y y := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [star_trivial]
  rw [← real_inner_self_eq_norm_sq, h]

/-- **The polynomial-filter transfer theorem.** If a polynomial is
within `ε` of `1` at every in-band eigenvalue and within `ε` of `0` at
every out-of-band eigenvalue (the exhaustive band dichotomy `(a, b]`
of the `bandProjector` convention), then the polynomial image `p(M)`
approximates the band projector in operator norm within the same
`ε`. This is the matrix-level functional calculus of the recorded
filter shape: filter quality enters as a scalar hypothesis, the
operator-norm conclusion is exact, and every filter design — power,
Chebyshev-damped, or any future minimax design — lands here.

Load-bearing on four delivered layers at once: Krylov's
`eigvecOf_dotProduct_aeval_mulVec` (the polynomial side), this
module's component action (the projector side, itself load-bearing on
Band's eigenbasis action and symmetry), Spectral's `dotProduct_eigvecOf`
(Parseval), and the Resolvent bridge's `opNorm_le_bound` / `cstar_norm_def`
spine (the norm transport). -/
theorem aeval_sub_bandProjector_l2OpNorm_le {M : Matrix V V ℝ} (hM : M.IsSymm)
    (a b : ℝ) (hab : a ≤ b) (p : ℝ[X]) {ε : ℝ} (hε : 0 ≤ ε)
    (hin : ∀ i, a < eigvalOf M hM i → eigvalOf M hM i ≤ b →
      |p.eval (eigvalOf M hM i) - 1| ≤ ε)
    (hout : ∀ i, eigvalOf M hM i ≤ a ∨ b < eigvalOf M hM i →
      |p.eval (eigvalOf M hM i)| ≤ ε) :
    ‖(aeval M p) - bandProjector M hM a b‖ ≤ ε := by
  have key : ∀ y : V → ℝ,
      ‖((WithLp.equiv 2 (V → ℝ)).symm
          ((aeval M p - bandProjector M hM a b) *ᵥ y) :
          EuclideanSpace ℝ V)‖ ^ 2
        ≤ ε ^ 2 * ‖((WithLp.equiv 2 (V → ℝ)).symm y :
            EuclideanSpace ℝ V)‖ ^ 2 := by
    intro y
    set D := (aeval M p - bandProjector M hM a b) with hD
    have hcomp : ∀ i : V, Matrix.dotProduct (eigvecOf M hM i) (D *ᵥ y)
        = (p.eval (eigvalOf M hM i)
            - (if a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b then (1 : ℝ) else 0))
          * Matrix.dotProduct (eigvecOf M hM i) y := by
      intro i
      rw [hD, Matrix.sub_mulVec, Matrix.dotProduct_sub,
        eigvecOf_dotProduct_aeval_mulVec hM i p y,
        eigvecOf_dotProduct_bandProjector_mulVec hM a b hab i y]
      ring
    rw [norm_euclidean_sq, norm_euclidean_sq]
    rw [dotProduct_eigvecOf hM (D *ᵥ y) (D *ᵥ y),
      dotProduct_eigvecOf hM y y]
    refine le_trans (Finset.sum_le_sum fun i _ => ?_)
      (ge_of_eq (Finset.mul_sum _ _ _))
    rw [hcomp i]
    by_cases hband : a < eigvalOf M hM i ∧ eigvalOf M hM i ≤ b
    · rw [if_pos hband]
      have hle := hin i hband.1 hband.2
      obtain ⟨hl, hu⟩ := abs_le.mp hle
      have hsq : (p.eval (eigvalOf M hM i) - 1)
          * (p.eval (eigvalOf M hM i) - 1) ≤ ε * ε := by
        have := sq_le_sq' hl hu
        simpa [sq] using this
      nlinarith [hsq, sq_nonneg (Matrix.dotProduct (eigvecOf M hM i) y)]
    · rw [if_neg hband, sub_zero]
      have hdisj : eigvalOf M hM i ≤ a ∨ b < eigvalOf M hM i := by
        rcases le_or_gt (eigvalOf M hM i) a with h | h
        · exact Or.inl h
        · refine Or.inr ?_
          by_contra hcon
          push_neg at hcon
          exact hband ⟨h, hcon⟩
      have hle := hout i hdisj
      obtain ⟨hl, hu⟩ := abs_le.mp hle
      have hsq : p.eval (eigvalOf M hM i) * p.eval (eigvalOf M hM i)
          ≤ ε * ε := by
        have := sq_le_sq' hl hu
        simpa [sq] using this
      nlinarith [hsq, sq_nonneg (Matrix.dotProduct (eigvecOf M hM i) y)]
  rw [Matrix.cstar_norm_def]
  refine ContinuousLinearMap.opNorm_le_bound
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (aeval M p - bandProjector M hM a b) :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) hε ?_
  intro x
  have hxe : x = (WithLp.equiv 2 (V → ℝ)).symm
      ((WithLp.equiv 2 (V → ℝ)) x) := (Equiv.apply_symm_apply _ _).symm
  have hact : ((Matrix.toEuclideanCLM (𝕜 := ℝ)
        (aeval M p - bandProjector M hM a b) :
      EuclideanSpace ℝ V →L[ℝ] EuclideanSpace ℝ V)) x
      = (WithLp.equiv 2 (V → ℝ)).symm
          ((aeval M p - bandProjector M hM a b)
            *ᵥ ((WithLp.equiv 2 (V → ℝ)) x)) := by
    conv_lhs => rw [hxe]
    rw [Matrix.toEuclideanCLM_piLp_equiv_symm, Matrix.toLin'_apply]
  rw [hact, hxe]
  have h2' : ‖((WithLp.equiv 2 (V → ℝ)).symm
      ((aeval M p - bandProjector M hM a b) *ᵥ ((WithLp.equiv 2 (V → ℝ)) x)) :
      EuclideanSpace ℝ V)‖ ^ 2
      ≤ (ε * ‖((WithLp.equiv 2 (V → ℝ)).symm
          ((WithLp.equiv 2 (V → ℝ)) x) : EuclideanSpace ℝ V)‖) ^ 2 := by
    rw [mul_pow]
    exact key _
  have hfinal := abs_le_of_sq_le_sq h2' (mul_nonneg hε (norm_nonneg _))
  rwa [abs_of_nonneg (norm_nonneg _)] at hfinal

/-! ## Instantiation 1: the power filter -/

/-- **The power filter.** On a symmetric matrix with spectrum in
`[0, Ltop]` whose top-eigenspace band `(t, Ltop]` contains only the top
eigenvalue, the `d`-fold power filter `(M/Ltop)^d` approximates the
band projector with the power-method rate `(t/Ltop)^d`. The ε constant
is attained at every out-of-band mode (QA pins it), so it cannot be
improved for this design. -/
theorem powFilter_l2OpNorm_le {M : Matrix V V ℝ} (hM : M.IsSymm)
    {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (htc : t ≤ c)
    (hnn : ∀ i, 0 ≤ eigvalOf M hM i)
    (hmax : ∀ i, eigvalOf M hM i ≤ c)
    (htop : ∀ i, t < eigvalOf M hM i → eigvalOf M hM i = c)
    (d : ℕ) :
    ‖(aeval M ((C c⁻¹ * X) ^ d)) - bandProjector M hM t c‖ ≤ (t / c) ^ d := by
  have heval : ∀ μ : ℝ, ((C c⁻¹ * X) ^ d).eval μ = (c⁻¹ * μ) ^ d := by
    intro μ
    rw [eval_pow, eval_mul, eval_C, eval_X]
  refine aeval_sub_bandProjector_l2OpNorm_le hM t c htc _
    (pow_nonneg (div_nonneg ht hc.le) d) ?_ ?_
  · intro i h1 h2
    rw [heval, htop i h1, inv_mul_cancel₀ hc.ne', one_pow, sub_self,
      abs_zero]
    exact pow_nonneg (div_nonneg ht hc.le) d
  · intro i hd
    rcases hd with hle | hgt
    · have h0 : 0 ≤ c⁻¹ * eigvalOf M hM i := by
        apply mul_nonneg _ (hnn i)
        exact inv_nonneg.2 hc.le
      have h1 : c⁻¹ * eigvalOf M hM i ≤ t / c := by
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hle (inv_nonneg.2 hc.le)
      have h2 : (c⁻¹ * eigvalOf M hM i) ^ d ≤ (t / c) ^ d :=
        pow_le_pow_left₀ h0 h1 d
      rw [heval, abs_pow, abs_eq_self.2 h0]
      exact h2
    · exact (lt_irrefl c (hgt.trans_le (hmax i))).elim

/-! ## Instantiation 2: the Chebyshev-damped filter — the Chebyshev
layer's second consumer -/

/-- The damped Chebyshev filter `T_d ∘ w / T_d(w(Ltop))` at the Krylov
layer's affine band map `w = bandMap t Lbot`, which carries the
exterior interval `[Lbot, t]` into `[−1, 1]` and maps `Ltop` above
`1`. The normalization makes the filter exact (`= 1`) at the top
eigenvalue while damping the exterior by the growth of `T_d` past
`1`. -/
noncomputable def chebyshevFilter (d : ℕ) (t Lbot Ltop : ℝ) : ℝ[X] :=
  C (((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((bandMap t Lbot).eval Ltop))⁻¹)
    * (Polynomial.Chebyshev.T ℝ (d : ℤ)).comp (bandMap t Lbot)

/-- The filter evaluates as the damped ratio: `p(μ)
= T_d(w(μ)) / T_d(w(Ltop))`. -/
theorem chebyshevFilter_eval (d : ℕ) (t Lbot Ltop μ : ℝ) :
    (chebyshevFilter d t Lbot Ltop).eval μ
      = ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((bandMap t Lbot).eval μ))
        * (((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((bandMap t Lbot).eval Ltop))⁻¹) := by
  rw [chebyshevFilter, eval_mul, eval_C, eval_comp]
  ring

/-- **The Chebyshev-damped filter.** On a symmetric matrix with
spectrum in `[Lbot, Ltop]` whose top-eigenspace band `(t, Ltop]`
contains only the top eigenvalue, the damped Chebyshev filter
approximates the band projector within `1/T_d(w(Ltop))` — exponential
in `d` through the growth of the Chebyshev polynomial past `1`
(asymptotically the `cosh` rate; the cosh lower bound itself is the
Krylov program's recorded follow-on, not needed here). The rate is
strictly better than the power rate `(t/Ltop)^d` in the small-gap
regime (QA pins a concrete instance).

The second consumer of the Krylov Chebyshev layer: the band bound
`abs_T_eval_le_one` damps the exterior, the growth lemma
`one_le_eval_T_of_one_le` normalizes, and the affine band map carries
the spectrum into position — the same scalar layer that carried
Kaniel–Paige, now under a projector-approximation theorem. -/
theorem chebyshevFilter_l2OpNorm_le {M : Matrix V V ℝ} (hM : M.IsSymm)
    {Lbot t Ltop : ℝ} (hpos : 0 < t - Lbot) (htL : t < Ltop)
    (hbot : ∀ i, Lbot ≤ eigvalOf M hM i) (hmax : ∀ i, eigvalOf M hM i ≤ Ltop)
    (htop : ∀ i, t < eigvalOf M hM i → eigvalOf M hM i = Ltop)
    (d : ℕ) :
    ‖(aeval M (chebyshevFilter d t Lbot Ltop)) - bandProjector M hM t Ltop‖
      ≤ ((Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((bandMap t Lbot).eval Ltop))⁻¹ := by
  have hwl : 1 ≤ (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((bandMap t Lbot).eval Ltop) :=
    one_le_eval_T_of_one_le (one_le_bandMap_eval hpos htL.le) d
  have hwlpos : 0 < (Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((bandMap t Lbot).eval Ltop) :=
    lt_of_lt_of_le zero_lt_one hwl
  refine aeval_sub_bandProjector_l2OpNorm_le hM t Ltop htL.le _
    (inv_nonneg.2 hwlpos.le) ?_ ?_
  · intro i h1 h2
    rw [chebyshevFilter_eval, htop i h1, mul_inv_cancel₀ hwlpos.ne',
      sub_self, abs_zero]
    exact inv_nonneg.2 hwlpos.le
  · intro i hd
    rcases hd with hle | hgt
    · have hbandle : |(bandMap t Lbot).eval (eigvalOf M hM i)| ≤ 1 :=
        abs_bandMap_eval_le_one hpos (hbot i) hle
      obtain ⟨hlo, hhi⟩ := abs_le.mp hbandle
      have hT : |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((bandMap t Lbot).eval (eigvalOf M hM i))| ≤ 1 :=
        abs_T_eval_le_one d hlo hhi
      rw [chebyshevFilter_eval, abs_mul, abs_of_nonneg (inv_nonneg.2 hwlpos.le)]
      calc |(Polynomial.Chebyshev.T ℝ (d : ℤ)).eval ((bandMap t Lbot).eval (eigvalOf M hM i))| * _ ≤ 1 * _ :=
          mul_le_mul_of_nonneg_right hT (inv_nonneg.2 hwlpos.le)
        _ = _ := by rw [one_mul]
    · exact (lt_irrefl Ltop (hgt.trans_le (hmax i))).elim

end SpectralGraphTheory
