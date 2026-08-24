/-
  BandDavisKahan_QA.lean

  Purpose
  -------
  QA lemmas for the bounded-window Davis–Kahan theorem of
  `Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan`
  (`proposals/band-davis-kahan.md`, backlog item 9): the product bound
  `‖Q * P‖ ≤ ‖A - B‖ / δ` for δ-separated band projectors, witnessed
  at every level the strategy's falsifiability test names.

  Four sections:

  1. **The rotated positive witness** — `A = diag13` (the Band_QA
     fixture, imported) with its low band `(−1, 2]`, against the
     rotated `B = !![1, 3/4; 3/4, 3]` with its top band `(3, 4]`. The
     theorem is instantiated at δ = 1, the perturbation norm is
     bounded by `3/4` through the pairing engine (the swap trick:
     `|y ⬝ᵥ (E *ᵥ x)| = (3/4) |(swap y) ⬝ᵥ x|` against
     Cauchy–Schwarz), and the product norm is pinned FROM BELOW by
     `1/√10` completely independently of the theorem: the filtered
     action `Q *ᵥ e₀` is resolved through B's eigenbasis (PolyFilter's
     component action, Parseval in Spectral), the surviving top-mode
     coordinate `v j 0` is constrained by the eigen-equation direction
     (`v j 1 = 3 * v j 0`) plus unit norm (`10 * (v j 0)² = 1`) — no
     `eigvecOf` value assumed — and the norm lower bound is closed
     through the delivered action bound `l2OpNorm_mulVec_le` at `e₀`.
     Cross-check: `1/10 ≤ 9/16`, i.e. the raw lower bound is strictly
     inside the delivered upper bound `3/4`.

  2. **The ε = 0 attainment** — `A = B = diag13` with disjoint bands:
     the theorem reads `‖Q * P‖ ≤ 0`, so the norm is exactly `0`
     (attained, not merely small), and the product is independently
     pinned zero through Band's disjoint-band law
     (`bandProjector_mul_bandProjector_eq_zero'`) in the
     `(5/2, 4] * (−1, 2]` order, with the window pin mirroring
     Band_QA's `band_diag13_high`.

  3. **The fence — separation load-bearing, refuted in proved form** —
     `A = B = diag13` with *identical* windows `(−1, 2]`: the
     hypothesis-free conclusion `‖P * P‖ ≤ ‖A − B‖ / δ` is refuted
     (the product is the nonzero projector `!![1,0;0,0]`, its norm
     bounded below by `1` through the action bound at `e₀`, while the
     right side is `0`), and every `hsep`-shaped hypothesis is
     exhibited impossible for positive δ. The separation is exercised
     as a fence, not decoration.

  4. **The mirror instance** — the `_of_gt` orientation on the same
     fixture pair: `A`'s high band `(2, 4]` against `B`'s bottom band
     `(−1, 3/2]` selecting the `3/4` mode, δ = 1/2, with the same
     two-route pattern (theorem bound `3/2`, raw lower `1/√10` at
     `e₁` through the bottom-mode direction constraint
     `v j 0 = -(3 * v j 1)`).

  All proofs are real Lean proofs (no `sorry`/`admit`).

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan
import Scaffold.QA.SpectralGraph.Band_QA

open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA

open SpectralGraphTheory
open SpectralGraphTheory.QA

/-!
## Fixture: the rotated matrix `B = !![1, 3/4; 3/4, 3]`

Eigenvalues `{3/4, 13/4}` pinned from trace `4` and determinant
`39/16` (the Band_QA `diag13` idiom); eigenvector *directions* from
the eigen-equation, never `eigvecOf` values.
-/

/-- The rotated fixture: `diag13` plus a `3/4` off-diagonal
perturbation, with eigenvalues `3/4` and `13/4` and rational
eigen-directions `(1, 3)` and `(3, −1)`. -/
noncomputable def bdkB : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, 3 / 4; 3 / 4, 3]

theorem bdkB_symm : bdkB.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, bdkB]

theorem bdkB_trace : bdkB.trace = 4 := by
  simp [Matrix.trace, bdkB]
  norm_num

theorem bdkB_det : bdkB.det = 39 / 16 := by
  rw [bdkB, Matrix.det_fin_two]
  norm_num

theorem bdkB_sum :
    eigvalOf bdkB bdkB_symm 0 + eigvalOf bdkB bdkB_symm 1 = 4 := by
  have h := eigvalOf_sum_eq_trace bdkB bdkB_symm
  rwa [Fin.sum_univ_two, bdkB_trace] at h

theorem bdkB_prod :
    eigvalOf bdkB bdkB_symm 0 * eigvalOf bdkB bdkB_symm 1 = 39 / 16 := by
  have h := Matrix.IsHermitian.det_eq_prod_eigenvalues
    (isHermitian_of_isSymm bdkB_symm)
  rw [bdkB_det] at h
  simpa [Fin.prod_univ_two] using h.symm

/-- Every eigenvalue of the rotated fixture is `3/4` or `13/4`: with
sum `4` and product `39/16`, each eigenvalue `x` satisfies
`(x − 3/4)(x − 13/4) = 0`. -/
theorem bdkB_eigvalOf_mem (i : Fin 2) :
    eigvalOf bdkB bdkB_symm i = 3 / 4 ∨
      eigvalOf bdkB bdkB_symm i = 13 / 4 := by
  have key : ∀ x y : ℝ, x + y = 4 → x * y = 39 / 16 →
      (x - 3 / 4) * (x - 13 / 4) = 0 := by
    intro x y hxy hprod
    have hr : (x - 3 / 4) * (x - 13 / 4)
        = x * x - 4 * x + 39 / 16 := by ring
    rw [hr, ← hxy, ← hprod]
    ring
  fin_cases i
  · show eigvalOf bdkB bdkB_symm 0 = 3 / 4 ∨
        eigvalOf bdkB bdkB_symm 0 = 13 / 4
    rcases mul_eq_zero.1 (key _ _ bdkB_sum bdkB_prod) with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · show eigvalOf bdkB bdkB_symm 1 = 3 / 4 ∨
        eigvalOf bdkB bdkB_symm 1 = 13 / 4
    have hsum' : eigvalOf bdkB bdkB_symm 1 + eigvalOf bdkB bdkB_symm 0
        = 4 := by rw [add_comm]; exact bdkB_sum
    have hprod' : eigvalOf bdkB bdkB_symm 1 * eigvalOf bdkB bdkB_symm 0
        = 39 / 16 := by rw [mul_comm]; exact bdkB_prod
    rcases mul_eq_zero.1 (key _ _ hsum' hprod') with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)

/-!
### Eigen-direction constraints (from the eigen-equation)
-/

/-- The `13/4`-eigenbasis vector points along `(1, 3)`: its second
coordinate is three times its first, read from the eigen-equation's
zeroth entry. -/
theorem bdkB_eigvec_top_dir (j : Fin 2)
    (h : eigvalOf bdkB bdkB_symm j = 13 / 4) :
    eigvecOf bdkB bdkB_symm j 1 = 3 * eigvecOf bdkB bdkB_symm j 0 := by
  have hev : bdkB *ᵥ eigvecOf bdkB bdkB_symm j
      = eigvalOf bdkB bdkB_symm j • eigvecOf bdkB bdkB_symm j :=
    (isHermitian_of_isSymm bdkB_symm).mulVec_eigenvectorBasis j
  rw [h] at hev
  have h0 := congrFun hev 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul] at h0
  rw [show bdkB 0 0 = (1 : ℝ) from by simp [bdkB],
      show bdkB 0 1 = (3 / 4 : ℝ) from by simp [bdkB]] at h0
  simp only [one_mul] at h0
  linear_combination (4 / 3 : ℝ) * h0

/-- Unit norm then pins the top-mode first coordinate squared to
exactly `1/10` — the value the raw lower-bound route consumes. -/
theorem bdkB_eigvec_top_sq (j : Fin 2)
    (h : eigvalOf bdkB bdkB_symm j = 13 / 4) :
    eigvecOf bdkB bdkB_symm j 0 * eigvecOf bdkB bdkB_symm j 0 = 1 / 10 := by
  have hu : eigvecOf bdkB bdkB_symm j 0 * eigvecOf bdkB bdkB_symm j 0
      + eigvecOf bdkB bdkB_symm j 1 * eigvecOf bdkB bdkB_symm j 1 = 1 := by
    have hnn := eigvecOf_inner bdkB bdkB_symm j j
    simpa [Fin.sum_univ_two] using hnn
  rw [bdkB_eigvec_top_dir j h] at hu
  have h10 : (10 : ℝ) * (eigvecOf bdkB bdkB_symm j 0
      * eigvecOf bdkB bdkB_symm j 0) = 1 := by nlinarith [hu]
  linear_combination (1 / 10 : ℝ) * h10

/-- The `3/4`-eigenbasis vector points along `(3, −1)`. -/
theorem bdkB_eigvec_bot_dir (j : Fin 2)
    (h : eigvalOf bdkB bdkB_symm j = 3 / 4) :
    eigvecOf bdkB bdkB_symm j 0 = -(3 * eigvecOf bdkB bdkB_symm j 1) := by
  have hev : bdkB *ᵥ eigvecOf bdkB bdkB_symm j
      = eigvalOf bdkB bdkB_symm j • eigvecOf bdkB bdkB_symm j :=
    (isHermitian_of_isSymm bdkB_symm).mulVec_eigenvectorBasis j
  rw [h] at hev
  have h0 := congrFun hev 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul] at h0
  rw [show bdkB 0 0 = (1 : ℝ) from by simp [bdkB],
      show bdkB 0 1 = (3 / 4 : ℝ) from by simp [bdkB]] at h0
  simp only [one_mul] at h0
  linear_combination (4 : ℝ) * h0

/-- Unit norm pins the bottom-mode second coordinate squared to
`1/10`. -/
theorem bdkB_eigvec_bot_sq (j : Fin 2)
    (h : eigvalOf bdkB bdkB_symm j = 3 / 4) :
    eigvecOf bdkB bdkB_symm j 1 * eigvecOf bdkB bdkB_symm j 1 = 1 / 10 := by
  have hu : eigvecOf bdkB bdkB_symm j 0 * eigvecOf bdkB bdkB_symm j 0
      + eigvecOf bdkB bdkB_symm j 1 * eigvecOf bdkB bdkB_symm j 1 = 1 := by
    have hnn := eigvecOf_inner bdkB bdkB_symm j j
    simpa [Fin.sum_univ_two] using hnn
  rw [bdkB_eigvec_bot_dir j h] at hu
  have h10 : (10 : ℝ) * (eigvecOf bdkB bdkB_symm j 1
      * eigvecOf bdkB bdkB_symm j 1) = 1 := by nlinarith [hu]
  linear_combination (1 / 10 : ℝ) * h10

/-!
## Section 1: the rotated positive witness (right separation)
-/

/-- The perturbation norm bound, through the pairing engine and the
swap trick: `E = diag13 − B` acts by swapping coordinates and scaling
by `−3/4`, so the pairing reduces to Cauchy–Schwarz against the
swapped vector. -/
theorem bdkE_norm_le : ‖diag13 - bdkB‖ ≤ 3 / 4 := by
  refine l2OpNorm_le_of_abs_dotProduct_le (by norm_num) ?_
  intro x y
  have hE : diag13 - bdkB = !![0, -(3 / 4); -(3 / 4), 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sub_apply, diag13, bdkB]
  have hact : (diag13 - bdkB) *ᵥ x
      = ![-(3 / 4) * x 1, -(3 / 4) * x 0] := by
    rw [hE]
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have hdot : y ⬝ᵥ ![-(3 / 4) * x 1, -(3 / 4) * x 0]
      = -(3 / 4) * (![y 1, y 0] ⬝ᵥ x) := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    ring
  have hswap : (![y 1, y 0] : Fin 2 → ℝ) ⬝ᵥ ![y 1, y 0] = y ⬝ᵥ y := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
    ring
  have hcs := abs_dotProduct_le (![y 1, y 0] : Fin 2 → ℝ) x
  rw [hswap] at hcs
  rw [hact, hdot, abs_mul, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 4)]
  calc (3 / 4) * |![y 1, y 0] ⬝ᵥ x|
      ≤ (3 / 4) * (Real.sqrt (y ⬝ᵥ y) * Real.sqrt (x ⬝ᵥ x)) :=
        mul_le_mul_of_nonneg_left hcs (by norm_num)
    _ = 3 / 4 * Real.sqrt (x ⬝ᵥ x) * Real.sqrt (y ⬝ᵥ y) := by ring

/-- The raw lower bound: the filtered action `Q *ᵥ e₀` has squared
norm exactly `1/10`, resolved through B's eigenbasis — the component
action kills the out-of-band mode, the top-mode coordinate is pinned
by the direction constraint, and no theorem of the new module is
consumed on this route. -/
theorem bdk_QPe0_sq :
    Matrix.dotProduct
        ((bandProjector bdkB bdkB_symm 3 4
          * bandProjector diag13 diag13_symm (-1) 2) *ᵥ ![1, 0])
        ((bandProjector bdkB bdkB_symm 3 4
          * bandProjector diag13 diag13_symm (-1) 2) *ᵥ ![1, 0])
      = 1 / 10 := by
  have hP : bandProjector diag13 diag13_symm (-1) 2 *ᵥ ![1, 0] = ![1, 0] := by
    rw [band_diag13_low]
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have hsplit : (bandProjector bdkB bdkB_symm 3 4
      * bandProjector diag13 diag13_symm (-1) 2) *ᵥ ![1, 0]
      = bandProjector bdkB bdkB_symm 3 4 *ᵥ ![1, 0] := by
    rw [← Matrix.mulVec_mulVec, hP]
  rw [hsplit, dotProduct_eigvecOf bdkB_symm _ _]
  have hcomp : ∀ j : Fin 2,
      Matrix.dotProduct (eigvecOf bdkB bdkB_symm j)
          (bandProjector bdkB bdkB_symm 3 4 *ᵥ ![1, 0])
        = (if 3 < eigvalOf bdkB bdkB_symm j ∧ eigvalOf bdkB bdkB_symm j ≤ 4
              then (1 : ℝ) else 0)
          * eigvecOf bdkB bdkB_symm j 0 := by
    intro j
    rw [eigvecOf_dotProduct_bandProjector_mulVec bdkB_symm 3 4
      (by norm_num) j ![1, 0]]
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [Fin.sum_univ_two]
  have hnbot : ¬((3 : ℝ) < 3 / 4 ∧ 3 / 4 ≤ 4) :=
    fun h => absurd h.1 (by norm_num)
  have hptop : (3 : ℝ) < 13 / 4 ∧ 13 / 4 ≤ 4 := ⟨by norm_num, by norm_num⟩
  rcases bdkB_eigvalOf_mem 0 with h0e | h0e
  · have h1e : eigvalOf bdkB bdkB_symm 1 = 13 / 4 := by
      rcases bdkB_eigvalOf_mem 1 with h | h
      · exfalso
        have hsum := bdkB_sum
        rw [h0e, h] at hsum
        norm_num at hsum
      · exact h
    rw [hcomp 0, hcomp 1, h0e, h1e]
    norm_num
    rw [bdkB_eigvec_top_sq 1 h1e]
  · have h1e : eigvalOf bdkB bdkB_symm 1 = 3 / 4 := by
      rcases bdkB_eigvalOf_mem 1 with h | h
      · exact h
      · exfalso
        have hsum := bdkB_sum
        rw [h0e, h] at hsum
        norm_num at hsum
    rw [hcomp 0, hcomp 1, h0e, h1e]
    norm_num
    rw [bdkB_eigvec_top_sq 0 h0e]

/-- The two-route positive witness: the raw eigenbasis route bounds
the product norm from below by `√(1/10)`, the theorem (at δ = 1, with
the perturbation bounded by `3/4`) bounds it from above by `3/4`, and
`1/10 < 9/16` — the two routes leave a proved nonempty gap, so a
misstatement on either side breaks the conjunction. -/
theorem bdk_rotated_QA :
    Real.sqrt (1 / 10)
      ≤ ‖bandProjector bdkB bdkB_symm 3 4
          * bandProjector diag13 diag13_symm (-1) 2‖
      ∧ ‖bandProjector bdkB bdkB_symm 3 4
          * bandProjector diag13 diag13_symm (-1) 2‖ ≤ 3 / 4 := by
  refine ⟨?_, ?_⟩
  · have hact := l2OpNorm_mulVec_le
      (bandProjector bdkB bdkB_symm 3 4
        * bandProjector diag13 diag13_symm (-1) 2) ![1, 0]
    rw [norm_euclidean_eq_sqrt, bdk_QPe0_sq, norm_euclidean_eq_sqrt] at hact
    have he0 : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [he0, Real.sqrt_one, mul_one] at hact
    exact hact
  · have hthm := l2OpNorm_bandProjector_mul_bandProjector_le_of_lt
      diag13_symm bdkB_symm (-1) 2 3 4 (by norm_num) (by norm_num)
      (δ := (1 : ℝ)) (by norm_num) (by norm_num)
    rw [div_one] at hthm
    exact le_trans hthm bdkE_norm_le

/-!
## Section 2: the ε = 0 attainment
-/

/-- The `(5/2, 4]` band of `diag13` is the second-axis projector (the
`band_diag13_high` pin at a tighter lower threshold, leaving a strict
window gap). -/
theorem band_diag13_52 :
    bandProjector diag13 diag13_symm (5 / 2) 4 = !![0, 0; 0, 1] := by
  rw [bandProjector, spectralProjector_eq_one diag13 diag13_symm 4
      (fun i => by
        rcases diag13_eigvalOf_mem i with h | h <;> rw [h] <;> norm_num),
    spectralProjector_diag13_eq (5 / 2) (by norm_num) (by norm_num)]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.one_apply]

/-- At zero perturbation with disjoint windows the bound is *attained*:
the theorem reads `‖Q * P‖ ≤ 0`, so the norm is exactly `0`. -/
theorem bdk_zeroE_attained :
    ‖bandProjector diag13 diag13_symm (5 / 2) 4
        * bandProjector diag13 diag13_symm (-1) 2‖ = 0 := by
  have hthm := l2OpNorm_bandProjector_mul_bandProjector_le_of_lt
      diag13_symm diag13_symm (-1) 2 (5 / 2) 4 (by norm_num) (by norm_num)
      (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have h0 : diag13 - diag13 = 0 := by
    ext i j; simp
  rw [h0, norm_zero, zero_div] at hthm
  exact le_antisymm hthm (norm_nonneg _)

/-- The independent raw route: the product is zero through Band's
disjoint-band law in the matching order. -/
theorem bdk_zeroE_raw :
    bandProjector diag13 diag13_symm (5 / 2) 4
        * bandProjector diag13 diag13_symm (-1) 2 = 0 :=
  bandProjector_mul_bandProjector_eq_zero' diag13 diag13_symm (-1) 2
    (5 / 2) 4 (by norm_num) (by norm_num) (by norm_num)

/-!
## Section 3: the fence — separation load-bearing
-/

/-- The hypothesis-free conclusion is false: at identical windows the
product is the nonzero projector `!![1,0;0,0]` (idempotence plus the
imported pin), its norm is at least `1` (the action bound at `e₀`:
`P *ᵥ e₀ = e₀`), while the right side is `‖diag13 − diag13‖ / δ = 0`. -/
theorem bdk_overlap_fence :
    ¬ (‖bandProjector diag13 diag13_symm (-1) 2
          * bandProjector diag13 diag13_symm (-1) 2‖
        ≤ ‖diag13 - diag13‖ / (1 : ℝ)) := by
  intro hcon
  have hQP : bandProjector diag13 diag13_symm (-1) 2
      * bandProjector diag13 diag13_symm (-1) 2 = !![1, 0; 0, 0] := by
    rw [bandProjector_idempotent diag13 diag13_symm (-1) 2 (by norm_num),
      band_diag13_low]
  have h0 : diag13 - diag13 = 0 := by
    ext i j; simp
  rw [hQP, h0, norm_zero, zero_div] at hcon
  have hact := l2OpNorm_mulVec_le (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ)
    ![1, 0]
  have hz : (!![1, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ
      (![1, 0] : Fin 2 → ℝ) = ![1, 0] := by
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have he0 : (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0] = 1 := by
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [hz, norm_euclidean_eq_sqrt] at hact
  rw [he0, Real.sqrt_one, mul_one] at hact
  linarith

/-- Every `hsep`-shaped hypothesis fails on the fence fixture: the two
windows coincide, so no positive δ separates them. Exactly `hsep` is
the violated hypothesis. -/
theorem bdk_overlap_sep_impossible : ∀ δ : ℝ, 0 < δ →
    ¬ ((2 : ℝ) + δ ≤ (-1 : ℝ)) := by
  intro δ hδ h
  linarith

/-!
## Section 4: the mirror instance (left separation)
-/

/-- The raw lower bound for the `_of_gt` orientation: the bottom-mode
filtered action `Q *ᵥ e₁` has squared norm exactly `1/10` (the
`(3, −1)` direction constraint). -/
theorem bdk_QPe1_sq :
    Matrix.dotProduct
        ((bandProjector bdkB bdkB_symm (-1) (3 / 2)
          * bandProjector diag13 diag13_symm 2 4) *ᵥ ![0, 1])
        ((bandProjector bdkB bdkB_symm (-1) (3 / 2)
          * bandProjector diag13 diag13_symm 2 4) *ᵥ ![0, 1])
      = 1 / 10 := by
  have hP : bandProjector diag13 diag13_symm 2 4 *ᵥ ![0, 1] = ![0, 1] := by
    rw [band_diag13_high]
    funext i
    fin_cases i <;> norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]
  have hsplit : (bandProjector bdkB bdkB_symm (-1) (3 / 2)
      * bandProjector diag13 diag13_symm 2 4) *ᵥ ![0, 1]
      = bandProjector bdkB bdkB_symm (-1) (3 / 2) *ᵥ ![0, 1] := by
    rw [← Matrix.mulVec_mulVec, hP]
  rw [hsplit, dotProduct_eigvecOf bdkB_symm _ _]
  have hcomp : ∀ j : Fin 2,
      Matrix.dotProduct (eigvecOf bdkB bdkB_symm j)
          (bandProjector bdkB bdkB_symm (-1) (3 / 2) *ᵥ ![0, 1])
        = (if (-1 : ℝ) < eigvalOf bdkB bdkB_symm j
              ∧ eigvalOf bdkB bdkB_symm j ≤ 3 / 2
              then (1 : ℝ) else 0)
          * eigvecOf bdkB bdkB_symm j 1 := by
    intro j
    rw [eigvecOf_dotProduct_bandProjector_mulVec bdkB_symm (-1) (3 / 2)
      (by norm_num) j ![0, 1]]
    simp [Matrix.dotProduct, Fin.sum_univ_two]
  rw [Fin.sum_univ_two]
  have hpbot : ((-1 : ℝ) < 3 / 4 ∧ 3 / 4 ≤ 3 / 2) := ⟨by norm_num, by norm_num⟩
  have hntop : ¬((-1 : ℝ) < 13 / 4 ∧ 13 / 4 ≤ 3 / 2) :=
    fun h => absurd h.2 (by norm_num)
  rcases bdkB_eigvalOf_mem 0 with h0e | h0e
  · have h1e : eigvalOf bdkB bdkB_symm 1 = 13 / 4 := by
      rcases bdkB_eigvalOf_mem 1 with h | h
      · exfalso
        have hsum := bdkB_sum
        rw [h0e, h] at hsum
        norm_num at hsum
      · exact h
    rw [hcomp 0, hcomp 1, h0e, h1e]
    norm_num
    rw [bdkB_eigvec_bot_sq 0 h0e]
  · have h1e : eigvalOf bdkB bdkB_symm 1 = 3 / 4 := by
      rcases bdkB_eigvalOf_mem 1 with h | h
      · exact h
      · exfalso
        have hsum := bdkB_sum
        rw [h0e, h] at hsum
        norm_num at hsum
    rw [hcomp 0, hcomp 1, h0e, h1e]
    norm_num
    rw [bdkB_eigvec_bot_sq 1 h1e]

/-- The mirror positive witness at δ = 1/2: raw lower `√(1/10)`,
theorem upper `‖E‖ / (1/2) ≤ 3/2`. -/
theorem bdk_mirror_QA :
    Real.sqrt (1 / 10)
      ≤ ‖bandProjector bdkB bdkB_symm (-1) (3 / 2)
          * bandProjector diag13 diag13_symm 2 4‖
      ∧ ‖bandProjector bdkB bdkB_symm (-1) (3 / 2)
          * bandProjector diag13 diag13_symm 2 4‖ ≤ 3 / 2 := by
  refine ⟨?_, ?_⟩
  · have hact := l2OpNorm_mulVec_le
      (bandProjector bdkB bdkB_symm (-1) (3 / 2)
        * bandProjector diag13 diag13_symm 2 4) ![0, 1]
    rw [norm_euclidean_eq_sqrt, bdk_QPe1_sq, norm_euclidean_eq_sqrt] at hact
    have he0 : (![0, 1] : Fin 2 → ℝ) ⬝ᵥ ![0, 1] = 1 := by
      simp [Matrix.dotProduct, Fin.sum_univ_two]
    rw [he0, Real.sqrt_one, mul_one] at hact
    exact hact
  · have hthm := l2OpNorm_bandProjector_mul_bandProjector_le_of_gt
      diag13_symm bdkB_symm 2 4 (-1) (3 / 2) (by norm_num) (by norm_num)
      (δ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
    rw [show ‖diag13 - bdkB‖ / (1 / 2)
        = (2 : ℝ) * ‖diag13 - bdkB‖ from by field_simp; ring] at hthm
    calc ‖bandProjector bdkB bdkB_symm (-1) (3 / 2)
          * bandProjector diag13 diag13_symm 2 4‖
        ≤ (2 : ℝ) * ‖diag13 - bdkB‖ := hthm
      _ ≤ (2 : ℝ) * (3 / 4) := mul_le_mul_of_nonneg_left bdkE_norm_le
          (by norm_num)
      _ = 3 / 2 := by norm_num

end Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.QA
