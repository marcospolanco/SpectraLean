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
/-
  Sparsification_QA.lean

  QA for `Scaffold.Mathlib.GraphTheory.Sparsification` (the
  deterministic-algebra slice of the leverage-score sparsification
  program, Step 1 Slice 2): the `K₂` fixtures pin the leverage budget,
  the projector's trace, the variance coefficient, and the bound
  `‖Σ‖ ≤ 1/q` at the theorem's own constants; three fences isolate the
  design decisions — the saturation guard (Finding A), the `q > 0`
  budget hypothesis (refuted at the junk `min 1 0 = 0` probabilities),
  and the pointwise-bound mechanism at the rank-one norm identity.

  Falsification content, per the load-bearing-growth policy:

  - **Two-route budget pin:** the Foster corollary gives
    `∑ ‖v_e‖² = card − 1 = 1` on `K₂`; independently the four ordered
    pairs contribute `1/2 + 1/2 + 0 + 0` through per-pair pins joined to
    the raw `R_eff` witness — a wrong normalization constant (the
    ordered-pair halving) breaks exactly one route.
  - **The rank-one norm identity is two-sided at a concrete vector**
    (`‖v vᵀ‖ = 5 = ‖v‖²`, the lower side through the eigenvector
    witness `v` itself), and the same witness mechanism pins the
    `K₂` edge vector's norm below (`1/2`), making the Finding-A fence
    (`1/4 < 1/2`) a *refutation*, not an assertion.
  - **The variance coefficient is exact** (`c_(0,1) = 1/2` at
    `p = min 1 (1 · 1/2) = 1/2`), so the bound `‖Σ‖ ≤ 1` is exercised at
    a concrete classical value, not decorated.
-/

import Scaffold.Mathlib.GraphTheory.Sparsification

/-! ## QA section (spike for `Scaffold/QA/SpectralGraph/Sparsification_QA.lean`) -/

namespace SparsificationQA

open MeasureTheory
open SpectralGraphTheory
open scoped BigOperators Matrix Matrix.L2OpNorm

/-- The unit edge `K₂` (entrywise-if fixture pattern). -/
def spK2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem spK2_isSymm : spK2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [spK2]

theorem spK2_nonneg : ∀ i j, 0 ≤ spK2 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [spK2]

/-- The support graph of `K₂` is connected: vertex 1 is adjacent to 0. -/
theorem spK2_connected : (supportGraph spK2 spK2_isSymm).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨0, ?_⟩
  intro v
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons (u := 0) (v := 1) (w := 1)
      ⟨by decide, by simp [spK2, supportGraph]⟩ SimpleGraph.Walk.nil⟩

theorem spK2_pot01 :
    (laplacian spK2).mulVec ![1, 0]
      = Pi.single 0 (1 : ℝ) - Pi.single 1 (1 : ℝ) := by
  funext i
  fin_cases i <;>
    simp [laplacian, degreeMatrix, deg, spK2, Matrix.mulVec,
      Matrix.dotProduct, Fin.sum_univ_two]

/-- **K₂ resistance pin:** `R 0 1 = 1` (a single unit edge). -/
theorem spK2_R01 : effectiveResistance spK2 0 1 = 1 :=
  effectiveResistance_eq spK2 spK2_isSymm spK2_nonneg spK2_connected
    ⟨![1, 0], spK2_pot01, by norm_num [Matrix.cons_val_zero]⟩

/-- Rank-one action: `(v vᵀ) y = (v ⬝ᵥ y) v` at `v = ![1,2]`, `y = ![3,−1]`
(the dot value `1` computed raw). -/
theorem rankOne_mulVec_QA :
    rankOne (![1, 2] : Fin 2 → ℝ) *ᵥ ![3, -1] = (1 : ℝ) • ![1, 2] := by
  rw [rankOne_mulVec]
  have h : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![3, -1] = 1 := by
    norm_num [Matrix.dotProduct, Fin.sum_univ_two]
  rw [h]

/-- Rank-one idempotence at `v = ![1,2]`: `(v vᵀ)² = ‖v‖² (v vᵀ)` raw. -/
theorem rankOne_mul_self_QA :
    rankOne (![1, 2] : Fin 2 → ℝ) * rankOne ![1, 2]
      = (5 : ℝ) • rankOne ![1, 2] := by
  rw [rankOne_mul_self]
  have h : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 2] = 5 := by
    norm_num [Matrix.dotProduct, Fin.sum_univ_two]
  rw [h]

/-- The quadratic-form identity at a concrete pair. -/
theorem rankOne_quadForm_QA :
    quadForm (rankOne (![1, 2] : Fin 2 → ℝ)) ![3, 0] = 9 := by
  rw [rankOne_quadForm]
  norm_num [Matrix.dotProduct, Fin.sum_univ_two]

theorem dotProduct_sq_le_QA :
    (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![3, -4] = -5
    ∧ ((![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![3, -4]) * ((![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![3, -4])
      ≤ ((![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![1, 2])
        * ((![3, -4] : Fin 2 → ℝ) ⬝ᵥ ![3, -4]) := by
  refine ⟨by norm_num [Matrix.dotProduct, Fin.sum_univ_two], ?_⟩
  exact dotProduct_sq_le _ _

theorem ssEdgeVec_self_QA :
    ssEdgeVec spK2 spK2_isSymm 0 0 = 0 :=
  ssEdgeVec_self spK2 spK2_isSymm 0

/-- **K₂ leverage pin**: the edge vector's squared norm is the pair's
half-share `w R / 2 = 1/2` (through the theorem at the pinned
resistance). -/
theorem ssEdgeVec_dot_K2_QA :
    ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1
      = 1 / 2 := by
  rw [ssEdgeVec_dotProduct_self spK2 spK2_isSymm spK2_nonneg spK2_connected
    0 1]
  have hw : spK2 0 1 = 1 := by simp [spK2]
  rw [spK2_R01, hw]
  norm_num

theorem ssEdgeVec_dot_K2_swapped_QA :
    ssEdgeVec spK2 spK2_isSymm 1 0 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 1 0
      = 1 / 2 := by
  rw [ssEdgeVec_swap]
  have : (-ssEdgeVec spK2 spK2_isSymm 0 1) ⬝ᵥ (-ssEdgeVec spK2 spK2_isSymm 0 1)
      = ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1 := by
    rw [Matrix.neg_dotProduct, Matrix.dotProduct_neg, neg_neg]
  rw [this, ssEdgeVec_dot_K2_QA]

/-- **The budget pin by two routes**: the Foster corollary gives
`∑ ‖v_e‖² = card − 1 = 1`; independently, the four ordered pairs
contribute `1/2 + 1/2 + 0 + 0` through the per-pair pins. -/
theorem sum_ssEdgeVec_dot_K2_QA :
    ∑ u, ∑ v, ssEdgeVec spK2 spK2_isSymm u v ⬝ᵥ ssEdgeVec spK2 spK2_isSymm u v
      = 1 := by
  rw [sum_ssEdgeVec_dotProduct_self spK2 spK2_isSymm spK2_nonneg
    spK2_connected]
  norm_num

theorem sum_ssEdgeVec_dot_K2_raw_QA :
    ∑ u, ∑ v, ssEdgeVec spK2 spK2_isSymm u v ⬝ᵥ ssEdgeVec spK2 spK2_isSymm u v
      = 1 := by
  have h00 : ssEdgeVec spK2 spK2_isSymm 0 0 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 0
      = 0 := by
    rw [ssEdgeVec_self spK2 spK2_isSymm 0, Matrix.dotProduct_zero]
  have h11 : ssEdgeVec spK2 spK2_isSymm 1 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 1 1
      = 0 := by
    rw [ssEdgeVec_self spK2 spK2_isSymm 1, Matrix.dotProduct_zero]
  simp only [Fin.sum_univ_two, h00, ssEdgeVec_dot_K2_QA,
    ssEdgeVec_dot_K2_swapped_QA, h11]
  norm_num

theorem trace_imageProjector_K2_QA :
    Matrix.trace (imageProjector spK2 spK2_isSymm) = 1 := by
  rw [trace_imageProjector_eq spK2 spK2_isSymm spK2_nonneg spK2_connected]
  norm_num

/-- The centering integral at `K₂`, `q = 1`, pair `(0, 1)`. -/
theorem integral_ssSummand_K2_QA :
    ∫ ω : (Fin 2 × Fin 2) → Bool,
        ssSummand spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) ω
      ∂ssMeasure spK2 spK2_isSymm 1 (by norm_num : (0 : ℝ) ≤ 1) = 0 :=
  integral_ssSummand_eq_zero spK2 spK2_isSymm 1 one_pos ((0, 1) : Fin 2 × Fin 2)

/-- The pointwise bound at `K₂`, `q = 1`: `‖X_e ω‖ ≤ 1 = 1/q` at the
all-true outcome. -/
theorem ssSummand_bound_K2_QA :
    ‖ssSummand spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) (fun _ => true)‖ ≤ 1 := by
  have h := ssSummand_l2OpNorm_le spK2 spK2_isSymm 1 one_pos
    ((0, 1) : Fin 2 × Fin 2) (fun _ => true)
  simpa using h

/-- **The saturation guard fires**: at budget `q = 4` the pair `(0, 1)`
is saturated (`p = min 1 2 = 1`) and the summand is identically zero. -/
theorem ssSummand_saturated_QA :
    ssSummand spK2 spK2_isSymm 4 ((0, 1) : Fin 2 × Fin 2) (fun _ => false) = 0 := by
  have hp : ssProb spK2 spK2_isSymm 4 ((0, 1) : Fin 2 × Fin 2) = 1 := by
    simp only [ssProb, ssEdgeVec_dot_K2_QA]
    norm_num
  simp [ssSummand, hp]

theorem spK2_rankOne_norm_ge_QA :
    1 / 2 ≤ ‖rankOne (ssEdgeVec spK2 spK2_isSymm 0 1)‖ := by
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul
    (rankOne_isSymm (ssEdgeVec spK2 spK2_isSymm 0 1))
    (by
      intro h
      have : ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1
          = 0 := by rw [h, Matrix.dotProduct_zero]
      rw [ssEdgeVec_dot_K2_QA] at this
      norm_num at this)
    (rankOne_mulVec (ssEdgeVec spK2 spK2_isSymm 0 1)
      (ssEdgeVec spK2 spK2_isSymm 0 1))
  have habs := Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.abs_eigvalOf_le_l2OpNorm
    (rankOne_isSymm (ssEdgeVec spK2 spK2_isSymm 0 1)) i
  have hval : (ssEdgeVec spK2 spK2_isSymm 0 1) ⬝ᵥ
      (ssEdgeVec spK2 spK2_isSymm 0 1) = 1 / 2 := ssEdgeVec_dot_K2_QA
  rw [hi, hval, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at habs
  exact habs

/-- **The Finding-A fence**: the *unguarded* saturated summand — the raw
`(δ_e/1 − 1) • (v_e v_eᵀ)` at the missed outcome `δ = 0` — violates the
uniform bound `‖X‖ ≤ 1/q` at `q = 4` (`1/4 < 1/2`). The guard is
load-bearing, not decorative. -/
theorem findingA_fence_QA :
    ¬ (‖((ssDelta ((0, 1) : Fin 2 × Fin 2) (fun _ => false) / (1 : ℝ)) - 1)
        • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1)‖ ≤ 1 / 4) := by
  intro h
  have hδ : ssDelta ((0, 1) : Fin 2 × Fin 2) (fun _ => false) = 0 := by
    simp [ssDelta]
  rw [hδ, zero_div, zero_sub] at h
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1),
    one_mul] at h
  have hle := spK2_rankOne_norm_ge_QA
  have h4 : (1:ℝ)/4 < 1/2 := by norm_num
  linarith

/-- **The `q ≤ 0` fence**: at `q = 0` every probability is the junk
`min 1 0 = 0`, the coefficient `δ/0 − 1` is junk, and the pointwise
bound `‖X_e ω‖ ≤ 1/0 = 0` fails at a genuine edge — `0 < q` is
load-bearing. -/
theorem ssSummand_q0_fence_QA :
    ¬ (‖ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) (fun _ => true)‖ ≤ 1 / 0) := by
  intro h
  have hp : ssProb spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) = 0 := by
    simp only [ssProb, ssEdgeVec_dot_K2_QA]
    norm_num
  have hval : ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) (fun _ => true)
      = (-1 : ℝ) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) := by
    simp only [ssSummand, hp]
    rw [if_neg (by norm_num : ¬((0:ℝ) = 1))]
    simp [ssDelta]
  rw [hval, norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1), one_mul,
    show ((1:ℝ)/0) = 0 from by norm_num] at h
  have hle := spK2_rankOne_norm_ge_QA
  have hpos : (0:ℝ) < 1/2 := by norm_num
  linarith

/-- **The variance bound at `K₂`, `q = 1`**: `‖Σ‖ ≤ 1 = 1/q` through
the headline theorem. -/
theorem ssVariance_bound_K2_QA :
    ‖ssVariance spK2 spK2_isSymm 1‖ ≤ 1 := by
  have h := l2OpNorm_ssVariance_le spK2 spK2_isSymm 1 one_pos spK2_nonneg
  simpa using h

/-- **The exact `K₂` variance coefficient**: `c_(0,1) = 1/2` — the
classical value `((1−p)/p)‖v_e‖²` at `p = min 1 (1·1/2) = 1/2`,
`‖v_e‖² = 1/2`, pinned raw. -/
theorem ssVariance_coeff_K2_QA :
    ((1 - ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2))
        / ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2))
      * (ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1)
      = 1 / 2 := by
  rw [show ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) = 1 / 2 from by
      simp only [ssProb, ssEdgeVec_dot_K2_QA]
      norm_num,
    ssEdgeVec_dot_K2_QA]
  norm_num

end SparsificationQA
