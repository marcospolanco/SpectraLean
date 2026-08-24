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
import Scaffold.Mathlib.GraphTheory.PolyFilter
import Scaffold.QA.SpectralGraph.Band_QA

/-!
# QA for polynomial filters and band projection

Exercises `GraphTheory.PolyFilter` — the transfer theorem and its two
instantiations — on the `diag13` fixture (`!![1, 0; 0, 3]`, spectrum
`{1, 3}`) reused from `Band_QA` (the QA-to-QA import precedent), where
the spectral analysis, eigenvalue membership, and threshold-projector
pins are already proved.

Sections:

1. **Exact recovery through the transfer engine** — an affine filter
   that is exactly `1` at the top eigenvalue and exactly `0` at the low
   one drives the engine's bound to `0`, recovering the band projector
   exactly; the two sides also pinned raw so a misstated engine or a
   misstated projector definition would break one route.
2. **The power filter** — instantiation at `t = 1`, `c = 3`, `d = 1, 2`
   with the ε constant `(1/3)^d` *attained* at the low mode (it cannot
   be improved for this design), and the filtered action on the low
   mode cross-checked by an independent raw route through the generic
   eigenvector action.
3. **The Chebyshev-damped filter** — instantiation at `Lbot = 1`,
   `t = 2`, `Ltop = 3`, `d = 1, 2` with the ε constants `1/3`, `1/17`
   attained at the low mode, and the power-vs-Chebyshev comparison
   `1/17 < (2/3)^2` — the damped rate provably better at the same gap.
4. **Fence** — the out-of-band filter-quality hypothesis is
   load-bearing: a filter perfect in-band but constant `1` outside has
   its out-of-band hypothesis fail at the low mode (proved), and the
   hypothesis-free conclusion is refuted in proved form (the norm
   lower-bounded at `1 > 1/2` through the vector the difference
   fixes).

All proofs are real Lean proofs (no `sorry`/`admit`).

Scoreboard: ../QA_SCOREBOARD.md
-/

open scoped BigOperators Matrix Matrix.L2OpNorm
open Polynomial

namespace SpectralGraphTheory.QA

/-!
## The band pin at `(2, 3]` and the affine exact filter
-/

/-- The band `(2, 3]` selects the eigenvalue-`3` mode: the second-axis
projector (the mirror of `Band_QA.band_diag13_overlap_high` one step
tighter — both thresholds strictly inside the gap). -/
theorem band_diag13_23 :
    bandProjector diag13 diag13_symm 2 3 = !![0, 0; 0, 1] := by
  rw [bandProjector,
    spectralProjector_eq_one diag13 diag13_symm 3
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h
        · rw [h]; norm_num
        · rw [h]),
    spectralProjector_diag13_eq 2 (by norm_num) (by norm_num)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]

/-- The affine exact filter for the band `(1, 3]`: `1` at the top
eigenvalue, `0` at the low one. -/
noncomputable def affineFilter : ℝ[X] := C (1 / 2) * (X - C 1)

theorem affineFilter_eval (μ : ℝ) :
    affineFilter.eval μ = (1 / 2) * (μ - 1) := by
  rw [affineFilter, eval_mul, eval_C, eval_sub, eval_X, eval_C]

/-- Raw pin: the affine filter's matrix image on the fixture is the
second-axis projector — computed through the algebra homomorphism
laws, independent of every band-projector theorem. -/
theorem aeval_diag13_affineFilter :
    aeval diag13 affineFilter = !![0, 0; 0, 1] := by
  have h : aeval diag13 affineFilter = (1 / 2 : ℝ) • (diag13 - 1) := by
    rw [affineFilter, map_mul, aeval_C, scalar_mul_eq_smul, map_sub,
      aeval_X, aeval_C, map_one]
  rw [h]
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [diag13]

/-- **Exact recovery through the transfer engine:** the affine filter
drives `‖p(M) − B‖` to `0` — the theorem route (ε = 0 forces the norm
to `0` from above, `norm_nonneg` from below). -/
theorem transfer_exact_QA :
    ‖aeval diag13 affineFilter
      - bandProjector diag13 diag13_symm 1 3‖ = 0 := by
  refine le_antisymm ?_ (norm_nonneg _)
  refine aeval_sub_bandProjector_l2OpNorm_le diag13_symm 1 3
    (by norm_num) affineFilter (by norm_num) ?_ ?_
  · intro i h1 _
    rcases diag13_eigvalOf_mem i with h | h
    · rw [h] at h1
      norm_num at h1
    · rw [h, affineFilter_eval]
      norm_num
  · intro i hd
    rcases diag13_eigvalOf_mem i with h | h
    · rw [h, affineFilter_eval]
      norm_num
    · rw [h] at hd
      rcases hd with hle | hgt
      · norm_num at hle
      · norm_num at hgt

/-- The band `(1, 3]` also selects the eigenvalue-`3` mode (the
eigenvalue `1` is excluded by the strict lower threshold): the
second-axis projector again, through the threshold-`1` pin. -/
theorem band_diag13_13 :
    bandProjector diag13 diag13_symm 1 3 = !![0, 0; 0, 1] := by
  rw [bandProjector,
    spectralProjector_eq_one diag13 diag13_symm 3
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h
        · rw [h]; norm_num
        · rw [h]),
    spectralProjector_diag13_one]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]

/-- Raw route to the same statement: both sides of the difference
pinned entrywise, their difference computed by literal subtraction. -/
theorem transfer_exact_raw_QA :
    aeval diag13 affineFilter
      - bandProjector diag13 diag13_symm 1 3 = 0 := by
  rw [aeval_diag13_affineFilter, band_diag13_13]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

/-!
## The power filter
-/

theorem diag13_nonneg (i : Fin 2) : 0 ≤ eigvalOf diag13 diag13_symm i := by
  rcases diag13_eigvalOf_mem i with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

theorem diag13_le_three (i : Fin 2) :
    eigvalOf diag13 diag13_symm i ≤ 3 := by
  rcases diag13_eigvalOf_mem i with h | h
  · rw [h]; norm_num
  · rw [h]

theorem diag13_top (i : Fin 2) (h : 1 < eigvalOf diag13 diag13_symm i) :
    eigvalOf diag13 diag13_symm i = 3 := by
  rcases diag13_eigvalOf_mem i with h' | h'
  · rw [h'] at h
    norm_num at h
  · exact h'

/-- The power-filter instantiation at `t = 1`, `c = 3`, any `d`. -/
theorem powFilter_diag13_QA (d : ℕ) :
    ‖aeval diag13 ((C (3 : ℝ)⁻¹ * X) ^ d)
      - bandProjector diag13 diag13_symm 1 3‖ ≤ (1 / 3) ^ d :=
  powFilter_l2OpNorm_le diag13_symm (by norm_num) (by norm_num)
    (by norm_num) diag13_nonneg diag13_le_three diag13_top d

/-- **The ε constant is attained** at the low mode: the filter value at
eigenvalue `1` is exactly `(1/3)^d`, so no smaller ε can hold for this
design at this fixture. -/
theorem powFilter_eps_attained_QA (d : ℕ) :
    ((C (3 : ℝ)⁻¹ * X) ^ d).eval 1 = (1 / 3) ^ d := by
  rw [eval_pow, eval_mul, eval_C, eval_X, mul_one, one_div]

/-- Raw cross-check by an independent route: the filtered action on the
low mode `![1, 0]` (an eigenvector by literal computation, not by the
spectral theorem's choice) is the damped value `((1/3)^d) • ![1, 0]` —
through Krylov's generic eigenvector action, not through any band or
norm theorem. -/
theorem powFilter_action_raw_QA (d : ℕ) :
    (aeval diag13 ((C (3 : ℝ)⁻¹ * X) ^ d)) *ᵥ
      (![1, 0] : Fin 2 → ℝ) = (((1 : ℝ) / 3) ^ d) • ![1, 0] := by
  have heig : diag13 *ᵥ (![1, 0] : Fin 2 → ℝ)
      = (1 : ℝ) • (![1, 0] : Fin 2 → ℝ) := by
    funext j
    fin_cases j <;>
      simp [diag13, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have h1 := aeval_mulVec_eq_eval_smul (M := diag13) heig
    ((C (3 : ℝ)⁻¹ * X) ^ d)
  rw [powFilter_eps_attained_QA] at h1
  exact h1

/-!
## The Chebyshev-damped filter
-/

/-- The band map `w = bandMap 2 1` on the fixture's spectrum: `w(1) = -1`
(exterior endpoint), `w(3) = 5` wait — `w(3) = 3`. -/
theorem bandMap_21_eval (μ : ℝ) :
    (bandMap 2 1).eval μ = 2 * μ - 3 := by
  rw [bandMap_eval]
  field_simp
  ring

theorem bandMap_21_three : (bandMap 2 1).eval 3 = 3 := by
  rw [bandMap_21_eval]
  norm_num

/-- Raw Chebyshev value: `T₁(3) = 3` (the `↑1` spelling is the
instantiated `(d : ℤ)` coercion form; `push_cast` bridges to the
pin's `T_one`). -/
theorem T_one_three :
    (Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ)).eval 3 = 3 := by
  rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) from by push_cast,
    Polynomial.Chebyshev.T_one]
  norm_num

/-- Raw Chebyshev value: `T₂(3) = 2 · 9 − 1 = 17`. -/
theorem T_two_three :
    (Polynomial.Chebyshev.T ℝ ((2 : ℕ) : ℤ)).eval 3 = 17 := by
  rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) from by push_cast,
    Polynomial.Chebyshev.T_two]
  norm_num [eval_mul, eval_pow, eval_X]

/-- Raw Chebyshev value: `T₁(-1) = -1` (the exterior endpoint). -/
theorem T_one_neg_one :
    (Polynomial.Chebyshev.T ℝ ((1 : ℕ) : ℤ)).eval (-1) = -1 := by
  rw [show ((1 : ℕ) : ℤ) = (1 : ℤ) from by push_cast,
    Polynomial.Chebyshev.T_one]
  norm_num

/-- The filter values at the two modes, `d = 1`: exact at the top
(`1`), damped to `-1/3` at the low mode. -/
theorem bandMap_21_one : (bandMap 2 1).eval 1 = -1 := by
  rw [bandMap_21_eval]
  norm_num

theorem chebyshevFilter_d1_evals :
    (chebyshevFilter 1 2 1 3).eval 3 = 1 ∧
      (chebyshevFilter 1 2 1 3).eval 1 = -1 / 3 := by
  constructor
  · rw [chebyshevFilter_eval, bandMap_21_three, T_one_three]
    norm_num
  · rw [chebyshevFilter_eval, bandMap_21_one, T_one_neg_one,
      bandMap_21_three, T_one_three]
    norm_num

theorem diag13_top_two (i : Fin 2) (h : 2 < eigvalOf diag13 diag13_symm i) :
    eigvalOf diag13 diag13_symm i = 3 := by
  rcases diag13_eigvalOf_mem i with h' | h'
  · rw [h'] at h
    norm_num at h
  · exact h'

/-- The Chebyshev instantiation at `d = 1`: the bound constant is
`1/3`, pinned equal to the raw Chebyshev value's reciprocal. -/
theorem chebyshevFilter_diag13_d1_QA :
    ‖aeval diag13 (chebyshevFilter 1 2 1 3)
      - bandProjector diag13 diag13_symm 2 3‖ ≤ 1 / 3 := by
  have h := chebyshevFilter_l2OpNorm_le (M := diag13) diag13_symm
    (t := 2) (Lbot := 1) (Ltop := 3) (by norm_num) (by norm_num)
    (fun i => by
      rcases diag13_eigvalOf_mem i with h | h
      · rw [h]
      · rw [h]; norm_num)
    diag13_le_three diag13_top_two 1
  rwa [bandMap_21_three, T_one_three, inv_eq_one_div] at h

/-- The Chebyshev instantiation at `d = 2`: the bound constant is
`1/17`, pinned equal to the raw Chebyshev value's reciprocal. -/
theorem chebyshevFilter_diag13_d2_QA :
    ‖aeval diag13 (chebyshevFilter 2 2 1 3)
      - bandProjector diag13 diag13_symm 2 3‖ ≤ 1 / 17 := by
  have h := chebyshevFilter_l2OpNorm_le (M := diag13) diag13_symm
    (t := 2) (Lbot := 1) (Ltop := 3) (by norm_num) (by norm_num)
    (fun i => by
      rcases diag13_eigvalOf_mem i with h | h
      · rw [h]
      · rw [h]; norm_num)
    diag13_le_three diag13_top_two 2
  rwa [bandMap_21_three, T_two_three, inv_eq_one_div] at h

/-- **The ε constant is attained** at the low mode at `d = 1`: the
filter value at eigenvalue `1` is exactly `-1/3`, of absolute value
`1/3` = the bound — no smaller ε holds for this design here. -/
theorem chebyshevFilter_eps_attained_QA :
    |(chebyshevFilter 1 2 1 3).eval 1| = 1 / 3 := by
  have h := chebyshevFilter_d1_evals.2
  rw [h]
  norm_num

/-- The damped rate `1/17` is the reciprocal of the raw Chebyshev
value `T₂(3) = 17` — the comparison's Chebyshev side, pinned raw. -/
theorem chebyshev_d2_rate_raw_QA :
    (((Polynomial.Chebyshev.T ℝ ((2 : ℕ) : ℤ)).eval
        ((bandMap 2 1).eval 3))⁻¹) = 1 / 17 := by
  rw [bandMap_21_three, T_two_three]
  norm_num

/-- **The rate comparison:** at the same gap and depth `d = 2`, the
damped Chebyshev rate `1/17` is strictly better than the power rate
`(2/3)^2 = 4/9`. The two instantiations of the same transfer engine,
compared numerically at one fixture. -/
theorem chebyshev_better_than_power_QA :
    (((Polynomial.Chebyshev.T ℝ ((2 : ℕ) : ℤ)).eval
        ((bandMap 2 1).eval 3))⁻¹) < ((2 / 3 : ℝ) ^ 2) := by
  rw [bandMap_21_three, T_two_three]
  norm_num

/-!
## The fence: the out-of-band hypothesis is load-bearing
-/

/-- The scalar failure: the constant filter `1` — perfect in-band
(`|1 − 1| = 0`) — does not satisfy the out-of-band quality hypothesis
at `ε = 1/2`, since its value at the low mode is `1 > 1/2`. -/
theorem polyFilter_hout_refuted_QA :
    ¬ (∀ i, eigvalOf diag13 diag13_symm i ≤ 2 ∨ 3 < eigvalOf diag13 diag13_symm i →
        |(C (1 : ℝ)).eval (eigvalOf diag13 diag13_symm i)| ≤ 1 / 2) := by
  intro h
  obtain ⟨i, hi⟩ := diag13_exists_one
  have h2 := h i (Or.inl (by rw [hi]; norm_num))
  rw [hi] at h2
  norm_num at h2

/-- The norm lower bound via a fixed unit vector: the difference
`1 − B_{2,3}` fixes `![1, 0]`, so its operator norm is at least `1` —
the `abs_eigvalOf_le_l2OpNorm` technique (vector action + the C*-norm
transport), no eigenvalue of the difference computed. -/
theorem one_le_norm_sub_band_diag13_23 :
    (1 : ℝ) ≤ ‖(1 : Matrix (Fin 2) (Fin 2) ℝ)
      - bandProjector diag13 diag13_symm 2 3‖ := by
  rw [band_diag13_23]
  have hfix : ((1 : Matrix (Fin 2) (Fin 2) ℝ) - !![0, 0; 0, 1]) *ᵥ
      (![1, 0] : Fin 2 → ℝ) = (![1, 0] : Fin 2 → ℝ) := by
    funext j
    fin_cases j <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have hn2 : ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm
      (![1, 0] : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2))‖ ^ 2 = 1 := by
    have h : inner ((WithLp.equiv 2 (Fin 2 → ℝ)).symm
        (![1, 0] : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2))
        ((WithLp.equiv 2 (Fin 2 → ℝ)).symm
          (![1, 0] : Fin 2 → ℝ))
        = Matrix.dotProduct (![1, 0] : Fin 2 → ℝ)
          (![1, 0] : Fin 2 → ℝ) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [star_trivial]
    rw [← real_inner_self_eq_norm_sq, h]
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  have hn : ‖((WithLp.equiv 2 (Fin 2 → ℝ)).symm
      (![1, 0] : Fin 2 → ℝ) : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rcases sq_eq_one_iff.1 hn2 with h | h
    · exact h
    · exact absurd (h ▸ norm_nonneg _) (by norm_num)
  rw [Matrix.cstar_norm_def]
  have h1 := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanCLM (𝕜 := ℝ)
      ((1 : Matrix (Fin 2) (Fin 2) ℝ) - !![0, 0; 0, 1]) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)))
    ((WithLp.equiv 2 (Fin 2 → ℝ)).symm (![1, 0] : Fin 2 → ℝ))
  rw [Matrix.toEuclideanCLM_piLp_equiv_symm, Matrix.toLin'_apply,
    hfix, hn, mul_one] at h1
  exact h1

/-- **The hypothesis-free conclusion is refuted:** with the constant
filter `1` and `ε = 1/2`, every hypothesis except the out-of-band one
holds, and the conclusion fails — the norm is at least `1 > 1/2`. The
out-of-band filter-quality hypothesis is load-bearing, not decorative. -/
theorem polyFilter_conclusion_refuted_QA :
    ¬ (‖aeval diag13 (C (1 : ℝ))
        - bandProjector diag13 diag13_symm 2 3‖ ≤ 1 / 2) := by
  intro h
  have hone : aeval diag13 (C (1 : ℝ))
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [aeval_C]
    simp
  rw [hone] at h
  have hlb := one_le_norm_sub_band_diag13_23
  linarith

end SpectralGraphTheory.QA
