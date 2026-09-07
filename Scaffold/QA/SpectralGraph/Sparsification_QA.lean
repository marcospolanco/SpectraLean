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

  Since 2026-09-04 this file also carries the family's adversarial fence
  audit (`CoreFences`, proposal
  `proposals/adversarial-fences-sparsification-core-family.md`): the
  hypothesis-form negative witnesses for the deterministic core's
  `hA`/`hnn`/`hconn`/`hq`/`hpne`/`hv` clauses, at the delivered signed,
  signed-4-cycle, disconnected and `K₂` fixtures plus two new local ones
  (an asymmetric `Fin 2` and a nonpositive-spectrum `Fin 3`).
-/

import Scaffold.Mathlib.GraphTheory.Sparsification
import Scaffold.QA.SpectralGraph.ResistanceMetric_QA

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

/-! ## CoreFences: the adversarial fence audit (proposal
`adversarial-fences-sparsification-core-family.md`, 2026-09-04)

The audit method's pass over the deterministic core's theorem surface
(`governance/ADVERSARIAL_REVIEW.md`): every load-bearing hypothesis
clause with no negative witness anywhere in the repository, fenced in
hypothesis form (the dropped-hypothesis statement refuted at a fixture
where every other hypothesis is genuine, certified by an isolation
companion), with non-fenceables recorded in the proposal with their
mechanisms. QA-only, no axiom contact. -/

section CoreFences

open SpectralGraphTheory ProbabilityTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open SpectralGraphTheory.QA

/-! ## The strict dot-positivity `hv` fence -/

/-- **Fence (`dotProduct_self_pos_of_ne_zero`, `hv`)**: the dropped
statement reads `0 < 0 ⬝ᵥ 0` at the zero vector. -/
theorem spF_dotSelfPos_hv_fence_QA :
    ¬ (0 < (![0, 0] : Fin 2 → ℝ) ⬝ᵥ (![0, 0] : Fin 2 → ℝ)) := by
  norm_num [Matrix.dotProduct, Fin.sum_univ_two]

/-! ## The bilinear Dirichlet identity's `hA` fence at the asymmetric
fixture -/

/-- The asymmetric fixture: `A 0 1 = 2 ≠ 1 = A 1 0`. -/
def cfAsymAdj : Matrix (Fin 2) (Fin 2) ℝ := !![0, 2; 1, 0]

theorem cfAsymAdj_not_isSymm : ¬ cfAsymAdj.IsSymm := by
  intro h
  have h01 := h.apply 0 1
  simp only [cfAsymAdj, Matrix.head_cons, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val', Matrix.cons_val_fin_one] at h01
  norm_num at h01

/-- **Isolation (`hA` fence at the asymmetric fixture):** the statement's
only hypothesis fails, and nothing else needs isolating. -/
theorem spF_dirichlet_hA_isolation_QA : ¬ cfAsymAdj.IsSymm :=
  cfAsymAdj_not_isSymm

/-- **Fence (`laplacian_dirichlet_bilinear`, `hA`)**: the double sum sees
the two *unequal* off-diagonals (`2 + 1 = 3`) while the quadratic form
sees the symmetrized action (`2 · 2 = 4`) at `x = y = ![1,0]`. -/
theorem spF_dirichlet_hA_fence_QA :
    ¬ (∑ i, ∑ j, cfAsymAdj i j * (((![1, 0] : Fin 2 → ℝ) i - (![1, 0] : Fin 2 → ℝ) j)
          * ((![1, 0] : Fin 2 → ℝ) i - (![1, 0] : Fin 2 → ℝ) j))
        = 2 * ((![1, 0] : Fin 2 → ℝ) ⬝ᵥ (laplacian cfAsymAdj *ᵥ (![1, 0] : Fin 2 → ℝ)))) := by
  simp [Fin.sum_univ_two, laplacian, degreeMatrix, deg, cfAsymAdj, Matrix.mulVec,
    Matrix.dotProduct, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.head_cons, Matrix.cons_val_fin_one]
  norm_num

/-! ## The eigenvalue-nonnegativity engine's `hnn` fence at the
delivered signed fixture -/

/-- **Isolation (the `hnn` fences at the signed fixture):** symmetric,
connected support, not nonnegative — exactly the third clause failing. -/
theorem spF_signed_isolation_QA :
    signedAdj.IsSymm ∧ (supportGraph signedAdj signedAdj_isSymm).Connected
      ∧ ¬ (∀ i j : Fin 3, 0 ≤ signedAdj i j) :=
  signed_fence_isolation_QA

/-- **Fence (`eigvalOf_laplacian_nonneg`, `hnn`)**: at the signed fixture
`quadForm L ![0,1,-1] = -2` (delivered), and the spectral resolution
`quadForm_eigvalOf` forces some eigenvalue negative — the whole-family
reading, without locating the index. -/
theorem spF_eigvalOf_nonneg_hnn_fence_QA :
    ¬ (∀ k : Fin 3, 0 ≤ eigvalOf (laplacian signedAdj)
        (laplacian_symmetric signedAdj signedAdj_isSymm) k) := by
  intro h
  have hres := quadForm_eigvalOf
    (laplacian_symmetric signedAdj signedAdj_isSymm) (![0, 1, -1] : Fin 3 → ℝ)
  rw [signed_quadForm_01m1] at hres
  have hnn : ∀ k ∈ (Finset.univ : Finset (Fin 3)),
      (0 : ℝ) ≤ eigvalOf (laplacian signedAdj)
          (laplacian_symmetric signedAdj signedAdj_isSymm) k
        * (Matrix.dotProduct (eigvecOf (laplacian signedAdj)
            (laplacian_symmetric signedAdj signedAdj_isSymm) k)
            (![0, 1, -1] : Fin 3 → ℝ)) ^ 2 :=
    fun k _ => mul_nonneg (h k) (sq_nonneg _)
  have hle := Finset.sum_nonneg hnn
  linarith [hres.symm, hle]

/-! ## The leverage-share identity's `hnn` fence at the signed fixture's
negative pair -/

/-- Every coordinate of the signed fixture's `(2, 1)` edge vector is
zero: the zero-eigenvalue coordinates drop by definition, and at every
other coordinate the factor `√(A 2 1 / 2) = √(-1/2)` is junk-zero. -/
theorem spF_signed_edgeVec21_zero :
    ssEdgeVec signedAdj signedAdj_isSymm 2 1 = 0 := by
  funext k
  simp only [Pi.zero_apply]
  by_cases h0 : eigvalOf (laplacian signedAdj)
      (laplacian_symmetric signedAdj signedAdj_isSymm) k = 0
  · simp [ssEdgeVec, h0]
  · simp only [ssEdgeVec, if_neg h0]
    have hnple : signedAdj 2 1 / 2 ≤ 0 := by
      have h21 : signedAdj 2 1 = -1 := by simp [signedAdj]
      rw [h21]; norm_num
    rw [Real.sqrt_eq_zero_of_nonpos hnple, zero_mul, zero_div]

/-- **Fence (`ssEdgeVec_dotProduct_self`, `hnn`)**: at the signed
fixture's negative pair the edge vector is identically zero while the
right side is `(-1) · R 2 1 / 2 = 1` through the delivered
`signed_R21_QA`. `0 ≠ 1`. -/
theorem spF_edgeVec_dot_hnn_fence_QA :
    ¬ (ssEdgeVec signedAdj signedAdj_isSymm 2 1
          ⬝ᵥ ssEdgeVec signedAdj signedAdj_isSymm 2 1
        = signedAdj 2 1 * effectiveResistance signedAdj 2 1 / 2) := by
  rw [spF_signed_edgeVec21_zero, Matrix.dotProduct_zero, signed_R21_QA]
  have h21 : signedAdj 2 1 = -1 := by simp [signedAdj]
  rw [h21]
  norm_num

/-! ## The rank-1 signed 4-cycle `sgnK4Adj` (delivered fixture): the
budget identities' `hnn` fences -/

/-- **Isolation (the `hnn` fences at the signed 4-cycle):** symmetric,
connected support, not nonnegative. -/
theorem spF_sgnK4_isolation_QA :
    sgnK4Adj.IsSymm ∧ (supportGraph sgnK4Adj sgnK4Adj_isSymm).Connected
      ∧ ¬ (∀ i j : Fin 4, 0 ≤ sgnK4Adj i j) :=
  sgnK4_fence_isolation_QA

/-- The signed 4-cycle's Laplacian is the rank-one matrix
`(1,-1,-1,1)(1,-1,-1,1)ᵀ`: every degree is exactly `1` and the
off-diagonal entries are `-A i j = s i * s j`. -/
theorem spF_sgnK4_laplacian :
    laplacian sgnK4Adj = rankOne (![1, -1, -1, 1] : Fin 4 → ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, sgnK4Adj, rankOne, Fin.sum_univ_four]

theorem spF_sgnK4_mulVec (y : Fin 4 → ℝ) :
    (laplacian sgnK4Adj).mulVec y
      = ((![1, -1, -1, 1] : Fin 4 → ℝ) ⬝ᵥ y) • (![1, -1, -1, 1] : Fin 4 → ℝ) := by
  rw [spF_sgnK4_laplacian, rankOne_mulVec]

theorem spF_sgnK4_dot_self :
    (![1, -1, -1, 1] : Fin 4 → ℝ) ⬝ᵥ (![1, -1, -1, 1] : Fin 4 → ℝ) = 4 := by
  norm_num [Matrix.dotProduct, Fin.sum_univ_four]

theorem spF_sgnK4_s_ne_zero :
    (![1, -1, -1, 1] : Fin 4 → ℝ) ≠ 0 := by
  intro h0
  have e := congrFun h0 0
  simp at e

theorem spF_sgnK4_eig_exists :
    ∃ k : Fin 4, eigvalOf (laplacian sgnK4Adj)
        (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) k = 4 := by
  refine exists_eigvalOf_eq_of_mulVec_eq_smul
    (x := (![1, -1, -1, 1] : Fin 4 → ℝ)) (μ := 4)
    (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) spF_sgnK4_s_ne_zero ?_
  rw [spF_sgnK4_mulVec, spF_sgnK4_dot_self]

private theorem spF_dot_smul_smul {W : Type} [Fintype W] (a b : ℝ) (x y : W → ℝ) :
    (a • x) ⬝ᵥ (b • y) = a * b * (x ⬝ᵥ y) := by
  simp only [Matrix.dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Engine (shared with the nonpositive fixture):** if a symmetric
matrix acts as `M *ᵥ y = (w ⬝ᵥ y) • s`, it has *at most one* nonzero
eigenvalue — every nonzero-eigenvalue eigenvector lies on the line
`ℝ ∙ s`, and two orthonormal vectors cannot share a line. -/
private theorem spF_at_most_one_nonzero {W : Type} [Fintype W] [DecidableEq W]
    {M : Matrix W W ℝ} (hM : M.IsSymm) {w s : W → ℝ}
    (hmul : ∀ y : W → ℝ, M *ᵥ y = (w ⬝ᵥ y) • s) :
    ∀ k l : W, eigvalOf M hM k ≠ 0 → eigvalOf M hM l ≠ 0 → k = l := by
  intro k l hk hl
  by_contra hkl
  have hq : ∀ m : W, eigvalOf M hM m ≠ 0 →
      ∃ c : ℝ, eigvecOf M hM m = c • s := by
    intro m hm
    have hev : M *ᵥ eigvecOf M hM m = eigvalOf M hM m • eigvecOf M hM m :=
      (isHermitian_of_isSymm hM).mulVec_eigenvectorBasis m
    have h1 : eigvecOf M hM m
        = (eigvalOf M hM m)⁻¹ • (M *ᵥ eigvecOf M hM m) := by
      rw [hev, inv_smul_smul₀ hm]
    rw [hmul, smul_smul] at h1
    exact ⟨_, h1⟩
  obtain ⟨ck, hck⟩ := hq k hk
  obtain ⟨cl, hcl⟩ := hq l hl
  have huk : Matrix.dotProduct (eigvecOf M hM k) (eigvecOf M hM k) = 1 := by
    rw [eigvecOf_dotProduct hM k k, if_pos rfl]
  rw [hck, spF_dot_smul_smul] at huk
  have hul : Matrix.dotProduct (eigvecOf M hM l) (eigvecOf M hM l) = 1 := by
    rw [eigvecOf_dotProduct hM l l, if_pos rfl]
  rw [hcl, spF_dot_smul_smul] at hul
  have hortho : Matrix.dotProduct (eigvecOf M hM k) (eigvecOf M hM l) = 0 := by
    rw [eigvecOf_dotProduct hM k l, if_neg hkl]
  rw [hck, hcl, spF_dot_smul_smul] at hortho
  have hckne : ck ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at huk
    norm_num at huk
  have hclne : cl ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_mul] at hul
    norm_num at hul
  have hane : (s ⬝ᵥ s) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at huk
    norm_num at huk
  exact (mul_ne_zero (mul_ne_zero hckne hclne) hane) hortho

/-- The only nonzero eigenvalue of the signed 4-cycle's Laplacian sits
at a single index (the rank-one engine). -/
theorem spF_sgnK4_other_zero (k kstar : Fin 4)
    (hks : eigvalOf (laplacian sgnK4Adj)
        (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar = 4)
    (hk : k ≠ kstar) :
    eigvalOf (laplacian sgnK4Adj)
        (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) k = 0 := by
  by_contra hkne
  have := spF_at_most_one_nonzero
    (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) spF_sgnK4_mulVec k kstar hkne
    (by rw [hks]; norm_num)
  exact hk this

/-- At a positive pair of the signed 4-cycle, the sign vector
`(1,-1,-1,1)` differs across the pair and the weight is exactly `1`. -/
theorem spF_sgnK4_pos_diff (u v : Fin 4) (hpos : 0 < sgnK4Adj u v) :
    ((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v) ^ 2 = 4
      ∧ sgnK4Adj u v = 1 := by
  fin_cases u <;> fin_cases v <;>
    simp [sgnK4Adj, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons] at hpos ⊢ <;>
    norm_num at hpos ⊢

private theorem spF_sq_split (t a : ℝ) :
    t * a / 2 * (t * a / 2) = t * t * (a * a) / 4 := by ring

private theorem spF_quadForm_finset_sum {W ι : Type} [Fintype W] [DecidableEq W]
    [Fintype ι] [DecidableEq ι] (M : ι → Matrix W W ℝ) (x : W → ℝ) :
    quadForm (∑ i, M i) x = ∑ i, quadForm (M i) x := by
  have hadd : ∀ P Q : Matrix W W ℝ,
      quadForm (P + Q) x = quadForm P x + quadForm Q x :=
    fun P Q => quadForm_add P Q x
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [quadForm]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

/-- **The per-pair leverage value at the signed 4-cycle**: every edge
vector's squared norm is `1/8` at the eight positive ordered pairs and
`0` everywhere else (negative pairs junk-zero through `√(A/2)`; the
diagonal by `ssEdgeVec_self`; the single nonzero eigenvalue `4` is
genuine so no other junk enters). -/
theorem spF_sgnK4_edgeVec_dot (u v : Fin 4) :
    ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v
        ⬝ᵥ ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v
      = if 0 < sgnK4Adj u v then (1 / 8 : ℝ) else 0 := by
  obtain ⟨kstar, hks⟩ := spF_sgnK4_eig_exists
  have hkne : eigvalOf (laplacian sgnK4Adj)
      (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar ≠ 0 := by
    rw [hks]; norm_num
  have hs4 : Real.sqrt (eigvalOf (laplacian sgnK4Adj)
      (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar) = 2 := by
    rw [hks, show (4 : ℝ) = 2 * 2 from by norm_num,
      Real.sqrt_mul_self (by norm_num : (0 : ℝ) ≤ 2)]
  -- the nonzero eigenvector lies on the sign line
  obtain ⟨c, hc⟩ : ∃ c : ℝ, eigvecOf (laplacian sgnK4Adj)
      (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar
        = c • (![1, -1, -1, 1] : Fin 4 → ℝ) := by
    have hev : (laplacian sgnK4Adj) *ᵥ
        (eigvecOf (laplacian sgnK4Adj)
          (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar)
        = (eigvalOf (laplacian sgnK4Adj)
            (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar)
          • (eigvecOf (laplacian sgnK4Adj)
              (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar) :=
      (isHermitian_of_isSymm
        (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm)).mulVec_eigenvectorBasis kstar
    have h1 : (eigvecOf (laplacian sgnK4Adj)
          (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar)
        = ((eigvalOf (laplacian sgnK4Adj)
              (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar)⁻¹)
          • ((laplacian sgnK4Adj) *ᵥ
              (eigvecOf (laplacian sgnK4Adj)
                (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar)) := by
      rw [hev, inv_smul_smul₀ (by rw [hks]; norm_num)]
    rw [spF_sgnK4_mulVec, smul_smul] at h1
    exact ⟨_, h1⟩
  have hc2 : c * c = 1 / 4 := by
    have hu : Matrix.dotProduct (eigvecOf (laplacian sgnK4Adj)
          (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar)
        (eigvecOf (laplacian sgnK4Adj)
          (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) kstar) = 1 := by
      rw [eigvecOf_dotProduct _ kstar kstar, if_pos rfl]
    rw [hc, spF_dot_smul_smul, spF_sgnK4_dot_self] at hu
    linarith
  -- the sum collapses to the kstar coordinate
  have hcollapse : (ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v)
        ⬝ᵥ (ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v)
      = (ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v kstar)
          * (ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v kstar) := by
    rw [Matrix.dotProduct]
    refine Finset.sum_eq_single kstar ?_ ?_
    · intro k _ hkne
      have hk0 : eigvalOf (laplacian sgnK4Adj)
          (laplacian_symmetric sgnK4Adj sgnK4Adj_isSymm) k = 0 :=
        spF_sgnK4_other_zero k kstar hks hkne
      simp [ssEdgeVec, hk0]
    · intro hcon
      exact absurd (Finset.mem_univ kstar) hcon
  rw [hcollapse]
  by_cases hpos : 0 < sgnK4Adj u v
  · rw [if_pos hpos]
    obtain ⟨hdiff, hA1⟩ := spF_sgnK4_pos_diff u v hpos
    have hentry : (ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v kstar)
        = Real.sqrt (sgnK4Adj u v / 2)
            * (c * (((![1, -1, -1, 1] : Fin 4 → ℝ) u
              - (![1, -1, -1, 1] : Fin 4 → ℝ) v))) / 2 := by
      simp only [ssEdgeVec, if_neg hkne, hs4, hc, Pi.smul_apply, smul_eq_mul]
      ring
    have hs2 : Real.sqrt ((1 : ℝ) / 2) * Real.sqrt ((1 : ℝ) / 2) = 1 / 2 :=
      Real.mul_self_sqrt (by norm_num)
    have hdd : (((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v))
          * (((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v)) = 4 := by
      rw [← pow_two]; exact hdiff
    have hcd : (c * (((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v)))
          * (c * (((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v))) = 1 := by
      have hring : (c * (((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v)))
            * (c * (((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v)))
          = (c * c) * (((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v)
            * ((![1, -1, -1, 1] : Fin 4 → ℝ) u - (![1, -1, -1, 1] : Fin 4 → ℝ) v)) := by ring
      rw [hring, hdd, hc2]
      norm_num
    rw [hentry, hA1, spF_sq_split, hs2, hcd]
    norm_num
  · rw [if_neg hpos]
    have hentry : (ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v kstar) = 0 := by
      simp only [ssEdgeVec, if_neg hkne]
      have hnple : sgnK4Adj u v / 2 ≤ 0 := by
        have hle : sgnK4Adj u v ≤ 0 := le_of_not_gt hpos
        rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
        linarith
      rw [Real.sqrt_eq_zero_of_nonpos hnple, zero_mul, zero_div]
    rw [hentry, zero_mul]

theorem spF_sgnK4_sum_edgeVec_dot :
    ∑ u, ∑ v, ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v
        ⬝ᵥ ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v
      = 1 := by
  have hrw : ∀ u v : Fin 4,
      (ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v
        ⬝ᵥ ssEdgeVec sgnK4Adj sgnK4Adj_isSymm u v)
      = if 0 < sgnK4Adj u v then (1 / 8 : ℝ) else 0 :=
    fun u v => spF_sgnK4_edgeVec_dot u v
  rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl
    (fun v _ => hrw u v))]
  simp [Fin.sum_univ_four, sgnK4Adj]
  norm_num

/-! ## The nonpositive fixture `cfSgAdj`: the projector trio's and the
deviation identity's `hnn` fences -/

/-- The nonpositive fixture (the shape of the tail QA's `sg`, defined
locally here): `A₀₁ = A₁₂ = -2`, `A₀₂ = 1`, so
`L = -(1,-2,1)(1,-2,1)ᵀ` — a signed Laplacian with a two-dimensional
kernel and every eigenvalue `≤ 0`. -/
def cfSgAdj : Matrix (Fin 3) (Fin 3) ℝ := !![0, -2, 1; -2, 0, -2; 1, -2, 0]

theorem cfSgAdj_isSymm : cfSgAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [cfSgAdj]

theorem cfSgAdj_not_nonneg : ¬ (∀ i j : Fin 3, 0 ≤ cfSgAdj i j) := by
  intro h
  have h01 : (0 : ℝ) ≤ cfSgAdj 0 1 := h 0 1
  have e : cfSgAdj 0 1 = -2 := by simp [cfSgAdj]
  rw [e] at h01
  norm_num at h01

/-- **Isolation (the `hnn` fences at the nonpositive fixture):**
symmetric, not nonnegative. -/
theorem spF_cfSg_isolation_QA :
    cfSgAdj.IsSymm ∧ ¬ (∀ i j : Fin 3, 0 ≤ cfSgAdj i j) :=
  ⟨cfSgAdj_isSymm, cfSgAdj_not_nonneg⟩

theorem quadForm_neg' {W : Type} [Fintype W] (M : Matrix W W ℝ) (x : W → ℝ) :
    quadForm (-M) x = -quadForm M x := by
  simp only [quadForm, Matrix.neg_mulVec, Matrix.dotProduct_neg]

theorem cfSg_laplacian :
    laplacian cfSgAdj = -(rankOne (![1, -2, 1] : Fin 3 → ℝ)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, cfSgAdj, rankOne, Fin.sum_univ_three] <;>
    norm_num

theorem cfSg_quadForm_self :
    quadForm (laplacian cfSgAdj) (![1, -2, 1] : Fin 3 → ℝ) = -36 := by
  rw [cfSg_laplacian, quadForm_neg', rankOne_quadForm]
  have hd : (![1, -2, 1] : Fin 3 → ℝ) ⬝ᵥ (![1, -2, 1] : Fin 3 → ℝ) = 6 := by
    norm_num [Matrix.dotProduct, Fin.sum_univ_three]
  rw [hd]
  norm_num

theorem cfSg_quadForm_nonpos_any (y : Fin 3 → ℝ) :
    quadForm (laplacian cfSgAdj) y ≤ 0 := by
  rw [cfSg_laplacian, quadForm_neg', rankOne_quadForm]
  exact neg_nonpos.2 (sq_nonneg _)

theorem cfSg_eigval_nonpos (k : Fin 3) :
    eigvalOf (laplacian cfSgAdj)
        (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k ≤ 0 := by
  rw [← quadForm_eigvecOf_self
    (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k]
  exact cfSg_quadForm_nonpos_any _

/-- Every edge vector of the nonpositive fixture is identically zero:
zero-eigenvalue coordinates drop by definition, and at every other
coordinate `√λ_k` of a negative eigenvalue is junk-zero, making the
entry a division by zero. -/
theorem cfSg_edgeVec_zero (u v : Fin 3) :
    ssEdgeVec cfSgAdj cfSgAdj_isSymm u v = 0 := by
  funext k
  simp only [Pi.zero_apply]
  by_cases h0 : eigvalOf (laplacian cfSgAdj)
      (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k = 0
  · simp [ssEdgeVec, h0]
  · have hlt : eigvalOf (laplacian cfSgAdj)
        (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k < 0 :=
      lt_of_le_of_ne (cfSg_eigval_nonpos k) h0
    simp only [ssEdgeVec, if_neg h0]
    rw [Real.sqrt_eq_zero_of_nonpos hlt.le, div_zero]

theorem cfSg_exists_nonzero :
    ∃ k : Fin 3, eigvalOf (laplacian cfSgAdj)
        (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k ≠ 0 := by
  by_contra hall
  push_neg at hall
  have hres := quadForm_eigvalOf
    (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) (![1, -2, 1] : Fin 3 → ℝ)
  rw [cfSg_quadForm_self,
    Finset.sum_congr rfl (fun k _ => by rw [hall k, zero_mul])] at hres
  norm_num at hres

theorem cfSg_lap_mulVec (y : Fin 3 → ℝ) :
    (laplacian cfSgAdj).mulVec y
      = ((![1, -2, 1] : Fin 3 → ℝ) ⬝ᵥ y)
        • (- (![1, -2, 1] : Fin 3 → ℝ)) := by
  rw [cfSg_laplacian, Matrix.neg_mulVec, rankOne_mulVec, smul_neg]

theorem cfSg_imageProjector_ne_zero :
    imageProjector cfSgAdj cfSgAdj_isSymm ≠ 0 := by
  intro h0
  obtain ⟨kstar, hk⟩ := cfSg_exists_nonzero
  have hdiag : imageProjector cfSgAdj cfSgAdj_isSymm kstar kstar = 1 := by
    simp [imageProjector, Matrix.diagonal_apply, if_neg hk]
  have e := congrFun (congrFun h0 kstar) kstar
  rw [hdiag] at e
  norm_num at e

/-- **Fence (`sum_rankOne_ssEdgeVec`, `hnn`)**: at the nonpositive
fixture every edge vector is zero, so the ordered-pair outer-product sum
is the zero matrix — while the image projector is nonzero (its single
nonzero eigenvalue keeps a diagonal `1`). -/
theorem spF_sum_rankOne_hnn_fence_QA :
    ¬ (∑ e : Fin 3 × Fin 3, rankOne (ssEdgeVec cfSgAdj cfSgAdj_isSymm e.1 e.2)
        = imageProjector cfSgAdj cfSgAdj_isSymm) := by
  have hzero : ∀ e : Fin 3 × Fin 3,
      rankOne (ssEdgeVec cfSgAdj cfSgAdj_isSymm e.1 e.2) = 0 := by
    intro e
    rw [cfSg_edgeVec_zero]
    ext i j; simp [rankOne]
  intro heq
  rw [Finset.sum_eq_zero fun e _ => hzero e] at heq
  exact cfSg_imageProjector_ne_zero heq.symm

theorem cfSg_s_entry_ne_zero (k : Fin 3) :
    (![1, -2, 1] : Fin 3 → ℝ) k ≠ 0 := by
  fin_cases k <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.head_cons]

theorem cfSg_quadForm_proj_pos :
    0 < quadForm (imageProjector cfSgAdj cfSgAdj_isSymm)
        (![1, -2, 1] : Fin 3 → ℝ) := by
  obtain ⟨kstar, hk⟩ := cfSg_exists_nonzero
  have happly : ∀ k : Fin 3,
      (imageProjector cfSgAdj cfSgAdj_isSymm
        *ᵥ (![1, -2, 1] : Fin 3 → ℝ)) k
      = (if eigvalOf (laplacian cfSgAdj)
            (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k = 0
          then (0 : ℝ) else 1)
        * (![1, -2, 1] : Fin 3 → ℝ) k := by
    intro k
    simp [imageProjector, Matrix.mulVec, Matrix.diagonal, Matrix.dotProduct,
      Finset.sum_ite_eq]
  rw [quadForm, Matrix.dotProduct,
    Finset.sum_congr rfl (fun k _ => by rw [happly k])]
  refine Finset.sum_pos' (fun k _ => ?_) ⟨kstar, Finset.mem_univ kstar, ?_⟩
  · by_cases h0 : eigvalOf (laplacian cfSgAdj)
        (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k = 0
    · rw [if_pos h0, zero_mul, mul_zero]
    · rw [if_neg h0, one_mul]
      exact mul_self_nonneg _
  · rw [if_neg hk, one_mul]
    exact mul_self_pos.2 (cfSg_s_entry_ne_zero kstar)

/-- **Fence (`quadForm_imageProjector_eq`, `hnn`)**: at the nonpositive
fixture every edge vector is zero, so the right side vanishes — while
the projector's quadratic form at the sign vector is strictly positive
(the single nonzero eigenvalue keeps the sign vector's coordinate). -/
theorem spF_qf_projector_hnn_fence_QA :
    ¬ (quadForm (imageProjector cfSgAdj cfSgAdj_isSymm) (![1, -2, 1] : Fin 3 → ℝ)
        = ∑ e : Fin 3 × Fin 3, ((![1, -2, 1] : Fin 3 → ℝ)
            ⬝ᵥ ssEdgeVec cfSgAdj cfSgAdj_isSymm e.1 e.2) ^ 2) := by
  intro heq
  have hsum : (∑ e : Fin 3 × Fin 3, ((![1, -2, 1] : Fin 3 → ℝ)
      ⬝ᵥ ssEdgeVec cfSgAdj cfSgAdj_isSymm e.1 e.2) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [cfSg_edgeVec_zero, Matrix.dotProduct_zero]
    simp
  rw [hsum] at heq
  exact absurd heq (ne_of_gt cfSg_quadForm_proj_pos)

theorem cfSg_trace_imageProjector :
    Matrix.trace (imageProjector cfSgAdj cfSgAdj_isSymm) = 1 := by
  obtain ⟨kstar, hk⟩ := cfSg_exists_nonzero
  have honly : ∀ k : Fin 3, eigvalOf (laplacian cfSgAdj)
      (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k ≠ 0 → k = kstar := by
    intro k hkne
    by_contra hne
    exact hne (spF_at_most_one_nonzero
      (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) cfSg_lap_mulVec k kstar hkne hk)
  simp only [imageProjector, Matrix.trace]
  rw [Matrix.diag_diagonal]
  refine (Finset.sum_eq_single kstar ?_ ?_).trans ?_
  · intro k _ hkne
    by_cases h0 : eigvalOf (laplacian cfSgAdj)
        (laplacian_symmetric cfSgAdj cfSgAdj_isSymm) k = 0
    · rw [if_pos h0]
    · exact absurd (honly k h0) hkne
  · intro hcon
    exact absurd (Finset.mem_univ kstar) hcon
  · rw [if_neg hk]

/-- **Fence (`trace_imageProjector_eq`, `hnn`)**: at the nonpositive
fixture the projector keeps exactly one dimension (the rank-one engine:
at most one nonzero eigenvalue; the sign vector witnesses one) —
`trace = 1 ≠ 2 = card - 1`. -/
theorem spF_trace_hnn_fence_QA :
    ¬ (Matrix.trace (imageProjector cfSgAdj cfSgAdj_isSymm)
        = (Fintype.card (Fin 3) : ℝ) - 1) := by
  rw [cfSg_trace_imageProjector]
  norm_num

/-- The sampling probability at the nonpositive fixture is zero at
every pair (every edge vector is zero). -/
theorem cfSg_prob_zero (q : ℝ) (e : Fin 3 × Fin 3) :
    ssProb cfSgAdj cfSgAdj_isSymm q e = 0 := by
  unfold ssProb
  rw [cfSg_edgeVec_zero e.1 e.2, Matrix.dotProduct_zero, mul_zero]
  exact min_eq_right (by norm_num)

theorem cfSg_rankOne_zero : rankOne (0 : Fin 3 → ℝ) = 0 := by
  ext i j; simp [rankOne]

/-- **Fence (`ssSampled_sub_imageProjector`, `hnn`)**: at the
nonpositive fixture the sampled operator is the zero matrix (every
rank-one factor is zero, whatever the weights) and every summand is
zero (the zero rank-one factor absorbs the junk coefficient), so the
deviation identity reads `0 - Π = 0` — refuted by the nonzero
projector. -/
theorem spF_deviation_hnn_fence_QA :
    ¬ (ssSampled cfSgAdj cfSgAdj_isSymm 1 (fun _ => true)
          - imageProjector cfSgAdj cfSgAdj_isSymm
        = ∑ e : Fin 3 × Fin 3,
            ssSummand cfSgAdj cfSgAdj_isSymm 1 e (fun _ => true)) := by
  have hsampled : ssSampled cfSgAdj cfSgAdj_isSymm 1 (fun _ => true) = 0 := by
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [cfSg_edgeVec_zero, cfSg_rankOne_zero, smul_zero]
  have hsummands : (∑ e : Fin 3 × Fin 3,
      ssSummand cfSgAdj cfSgAdj_isSymm 1 e (fun _ => true)) = 0 := by
    refine Finset.sum_eq_zero fun e _ => ?_
    have hpne : ssProb cfSgAdj cfSgAdj_isSymm 1 e ≠ 1 := by
      rw [cfSg_prob_zero]; norm_num
    unfold ssSummand
    rw [if_neg hpne, cfSg_edgeVec_zero, cfSg_rankOne_zero, smul_zero]
  intro heq
  rw [hsampled, hsummands, zero_sub, neg_eq_zero] at heq
  exact cfSg_imageProjector_ne_zero heq

/-! ## The trace identity's `hconn` fence at the delivered disconnected
fixture -/

/-- **Isolation (`hconn` fence at the disconnected fixture):** symmetric,
nonnegative, support graph not connected. -/
theorem spF_disc_isolation_QA :
    connDiscAdj.IsSymm ∧ (∀ i j : Fin 4, 0 ≤ connDiscAdj i j)
      ∧ ¬ (supportGraph connDiscAdj connDiscAdj_isSymm).Connected :=
  foF_disc_isolation_QA

/-- **Fence (`trace_imageProjector_eq`, `hconn`)**: on the disconnected
`K₂ ⊕ K₂` the constants and the component indicator are two
non-parallel kernel vectors, so (the delivered Foster engine) at least
two eigenvalues are zero, `trace Π ≤ 4 - 2 = 2 ≠ 3 = card - 1`. -/
theorem spF_trace_hconn_fence_QA :
    ¬ (Matrix.trace (imageProjector connDiscAdj connDiscAdj_isSymm)
        = (Fintype.card (Fin 4) : ℝ) - 1) := by
  intro heq
  have hne1 : (onesVec (V := Fin 4)) ≠ 0 := by
    intro h0
    have e := congrFun h0 0
    simp [onesVec] at e
  have hne2 : (![1, 1, 0, 0] : Fin 4 → ℝ) ≠ 0 := by
    intro h0
    have e := congrFun h0 0
    simp at e
  have hnp : ¬ ∃ c : ℝ, (onesVec (V := Fin 4))
      = c • (![1, 1, 0, 0] : Fin 4 → ℝ) := by
    rintro ⟨c, hc⟩
    have e2 := congrFun hc (2 : Fin 4)
    simp only [onesVec, Matrix.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val', Matrix.head_cons] at e2
    norm_num at e2
  have h2 := ff_two_kernel_filter_card_ge_two
    (laplacian_symmetric connDiscAdj connDiscAdj_isSymm)
    (laplacian_ones_in_kernel connDiscAdj)
    connDisc_indicator_in_kernel_QA hne1 hne2 hnp
  have hite : ∀ k : Fin 4,
      (if eigvalOf (laplacian connDiscAdj)
          (laplacian_symmetric connDiscAdj connDiscAdj_isSymm) k = 0
        then (0 : ℝ) else 1)
      = 1 - (if eigvalOf (laplacian connDiscAdj)
          (laplacian_symmetric connDiscAdj connDiscAdj_isSymm) k = 0
        then (1 : ℝ) else 0) := by
    intro k
    by_cases h : eigvalOf (laplacian connDiscAdj)
        (laplacian_symmetric connDiscAdj connDiscAdj_isSymm) k = 0 <;> simp [h]
  simp only [imageProjector, Matrix.trace] at heq
  rw [Matrix.diag_diagonal,
    Finset.sum_congr rfl fun k _ => hite k,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_boole] at heq
  simp at heq
  have hge : ((Finset.univ.filter fun k =>
      eigvalOf (laplacian connDiscAdj)
        (laplacian_symmetric connDiscAdj connDiscAdj_isSymm) k = 0).card : ℝ)
      ≥ 2 := by exact_mod_cast h2
  linarith

/-! ## The `hq`/`hpne` fences at the `K₂` fixture -/

/-- **Isolation (the `hq` fences at `K₂`):** the structural clauses are
all genuine. -/
theorem spF_K2_isolation_QA :
    spK2.IsSymm ∧ (∀ i j : Fin 2, 0 ≤ spK2 i j)
      ∧ (supportGraph spK2 spK2_isSymm).Connected :=
  ⟨spK2_isSymm, spK2_nonneg, spK2_connected⟩

theorem spF_K2_vec_ne_zero :
    ssEdgeVec spK2 spK2_isSymm 0 1 ≠ 0 := by
  intro h0
  have hd := ssEdgeVec_dot_K2_QA
  rw [h0, Matrix.dotProduct_zero] at hd
  norm_num at hd

theorem spF_K2_rankOne_ne_zero :
    rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) ≠ 0 := by
  intro h0
  refine spF_K2_vec_ne_zero ?_
  funext i
  have hii := congrFun (congrFun h0 i) i
  simp only [rankOne_apply, Matrix.zero_apply] at hii
  exact mul_self_eq_zero.1 hii

theorem spF_K2_prob_q0 :
    ssProb spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) = 0 := by
  unfold ssProb
  rw [ssEdgeVec_dot_K2_QA]
  norm_num

theorem spF_K2_prob_qm1 :
    ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2) = -1 / 2 := by
  unfold ssProb
  rw [ssEdgeVec_dot_K2_QA]
  norm_num

theorem spF_K2_prob_10_qm1 :
    ssProb spK2 spK2_isSymm (-1) ((1, 0) : Fin 2 × Fin 2) = -1 / 2 := by
  unfold ssProb
  rw [ssEdgeVec_swap, Matrix.neg_dotProduct, Matrix.dotProduct_neg, neg_neg,
    ssEdgeVec_dot_K2_QA]
  norm_num

/-- **Fence (`ssProb_nonneg`, `hq`)**: at `q = -1` the probability is
`min 1 (-1 · 1/2) = -1/2 < 0`. -/
theorem spF_prob_nonneg_hq_fence_QA :
    ¬ (0 ≤ ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2)) := by
  rw [spF_K2_prob_qm1]
  norm_num

/-- **Fence (`ssWeight_nonneg`, `hq`)**: at `q = -1`, the sampled
outcome, the weight is `1 / (-1/2) = -2 < 0`. -/
theorem spF_weight_nonneg_hq_fence_QA :
    ¬ (0 ≤ ssWeight spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2)
        (fun _ => true)) := by
  have hpne : ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2) ≠ 1 := by
    rw [spF_K2_prob_qm1]; norm_num
  unfold ssWeight
  rw [if_neg hpne, spF_K2_prob_qm1]
  simp only [ssDelta, if_true]
  norm_num

/-- **Fence (`integral_bern_center_sq`, `hpne`)**: at `p ≡ 0` (mass
clauses genuine) every outcome's summand is `(δ/0 - 1)² = 1`, so the
integral is `1` while the right side is `(1 - 0)/0 = 0`. -/
theorem spF_bern_sq_hpne_fence_QA :
    ¬ (∫ ω : Fin 1 → Bool,
        ((if ω (0 : Fin 1) then (1 : ℝ) else 0) / (0 : ℝ) - 1) ^ 2
      ∂(bernPMF (fun _ : Fin 1 => (0 : ℝ))
          (fun _ => le_refl (0 : ℝ))
          (fun _ => by norm_num)).toMeasure
      = (1 - (0 : ℝ)) / (0 : ℝ)) := by
  have hf : ∀ ω : Fin 1 → Bool,
      ((if ω (0 : Fin 1) then (1 : ℝ) else 0) / (0 : ℝ) - 1) ^ 2 = 1 := by
    intro ω
    cases hω : ω (0 : Fin 1) <;>
      simp [hω, div_zero]
  have hfun : (fun ω : Fin 1 → Bool =>
        ((if ω (0 : Fin 1) then (1 : ℝ) else 0) / (0 : ℝ) - 1) ^ 2)
      = fun _ => (1 : ℝ) := funext hf
  rw [hfun, integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  norm_num

/-- **Fence (`integral_ssSummand_eq_zero`, `hq`)**: at `q = 0` the
probability is `min 1 0 = 0`, the coefficient `δ/0 - 1` is `-1` on both
outcomes, and the summand is the *constant* `-(v ⊗ v)` — the integral
of a constant against the genuine `Bernoulli(0)` measure is that
constant, nonzero. -/
theorem spF_center_hq_fence_QA :
    ¬ (∫ ω : (Fin 2 × Fin 2) → Bool,
        ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω
      ∂ssMeasure spK2 spK2_isSymm 0 (by norm_num : (0 : ℝ) ≤ 0)
      = 0) := by
  have hp := spF_K2_prob_q0
  have hpne : ssProb spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ≠ 1 := by
    rw [hp]; norm_num
  have hconst : ∀ ω : (Fin 2 × Fin 2) → Bool,
      ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω
        = (-1 : ℝ) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) := by
    intro ω
    unfold ssSummand ssDelta
    rw [if_neg hpne]
    cases hω : ω ((0, 1) : Fin 2 × Fin 2) <;>
      simp only [hω, if_true, if_false, div_zero, zero_sub] <;>
      rw [hp] <;> norm_num
  have hfun : (fun ω : (Fin 2 × Fin 2) → Bool =>
        ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω)
      = fun _ => (-1 : ℝ) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) :=
    funext hconst
  rw [hfun]
  simp only [ssMeasure]
  rw [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  intro hz
  rcases smul_eq_zero.1 hz with h | h
  · norm_num at h
  · exact spF_K2_rankOne_ne_zero h

/-- **Fence (`integral_ssSummand_mul_self`, `hq`)**: at `q = 0` the
left side is the constant `‖v‖² (v ⊗ v) = (1/2)(v ⊗ v) ≠ 0` (the
rank-one idempotence) while the right side's coefficient
`((1 - 0)/0) ‖v‖²` is junk-zero. -/
theorem spF_mul_self_hq_fence_QA :
    ¬ (∫ ω : (Fin 2 × Fin 2) → Bool,
        ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω
          * ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω
      ∂ssMeasure spK2 spK2_isSymm 0 (by norm_num : (0 : ℝ) ≤ 0)
      = (((1 - ssProb spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2))
            / ssProb spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2))
          * (ssEdgeVec spK2 spK2_isSymm 0 1
              ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1))
        • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1)) := by
  have hp := spF_K2_prob_q0
  have hpne : ssProb spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ≠ 1 := by
    rw [hp]; norm_num
  have hconst : ∀ ω : (Fin 2 × Fin 2) → Bool,
      ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω
        = (-1 : ℝ) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) := by
    intro ω
    unfold ssSummand ssDelta
    rw [if_neg hpne]
    cases hω : ω ((0, 1) : Fin 2 × Fin 2) <;>
      simp only [hω, if_true, if_false, div_zero, zero_sub] <;>
      rw [hp] <;> norm_num
  have hval : ∀ ω : (Fin 2 × Fin 2) → Bool,
      ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω
          * ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω
        = (1 / 2 : ℝ) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) := by
    intro ω
    rw [hconst ω, smul_mul_assoc, Matrix.mul_smul, smul_smul,
      rankOne_mul_self, ssEdgeVec_dot_K2_QA]
    norm_num
  have hfun : (fun ω : (Fin 2 × Fin 2) → Bool =>
        ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω
          * ssSummand spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2) ω)
      = fun _ => (1 / 2 : ℝ) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) :=
    funext hval
  rw [hfun]
  simp only [ssMeasure]
  rw [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  have hR0 : (((1 - ssProb spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2))
        / ssProb spK2 spK2_isSymm 0 ((0, 1) : Fin 2 × Fin 2))
      * (ssEdgeVec spK2 spK2_isSymm 0 1
          ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1))
      • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) = 0 := by
    rw [hp, sub_zero, div_zero, zero_mul, zero_smul]
  rw [hR0]
  intro hz
  rcases smul_eq_zero.1 hz with h | h
  · norm_num at h
  · exact spF_K2_rankOne_ne_zero h

/-- **Fence (`ssVariance_coeff_nonneg`, `hq`)**: at `q = -1` the
coefficient is `((1 + 1/2)/(-1/2)) · (1/2) = -3/2 < 0`. -/
theorem spF_coeff_nonneg_hq_fence_QA :
    ¬ (0 ≤ ((1 - ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2))
            / ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2))
          * (ssEdgeVec spK2 spK2_isSymm 0 1
              ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1)) := by
  rw [spF_K2_prob_qm1, ssEdgeVec_dot_K2_QA]
  norm_num

/-- **Fence (`quadForm_ssVariance_nonneg`, `hq`)**: at `q = -1` and
`x = v_{01}` both nonzero ordered pairs contribute
`((1-p)/p) ‖v‖² ‖v‖⁴ = (-3)(1/2)(1/4)`, for a total of `-3/4 < 0`. -/
theorem spF_qf_variance_hq_fence_QA :
    ¬ (0 ≤ quadForm (ssVariance spK2 spK2_isSymm (-1))
        (ssEdgeVec spK2 spK2_isSymm 0 1)) := by
  intro hle
  rw [quadForm_ssVariance_eq, Fintype.sum_prod_type] at hle
  simp only [Prod.fst, Prod.snd, Fin.sum_univ_two] at hle
  have hd10 : (ssEdgeVec spK2 spK2_isSymm 0 1)
      ⬝ᵥ (ssEdgeVec spK2 spK2_isSymm 1 0) = -1 / 2 := by
    have hsw : ssEdgeVec spK2 spK2_isSymm 1 0
        = -(ssEdgeVec spK2 spK2_isSymm 0 1) :=
      ssEdgeVec_swap spK2 spK2_isSymm 1 0
    rw [hsw, Matrix.dotProduct_neg, ssEdgeVec_dot_K2_QA]
    norm_num
  have h00 : (((1 - ssProb spK2 spK2_isSymm (-1) ((0, 0) : Fin 2 × Fin 2))
        / ssProb spK2 spK2_isSymm (-1) ((0, 0) : Fin 2 × Fin 2))
      * (ssEdgeVec spK2 spK2_isSymm 0 0 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 0))
      * ((ssEdgeVec spK2 spK2_isSymm 0 1)
          ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 0) ^ 2 = 0 := by
    simp [ssEdgeVec_self, Matrix.dotProduct_zero]
  have h11 : (((1 - ssProb spK2 spK2_isSymm (-1) ((1, 1) : Fin 2 × Fin 2))
        / ssProb spK2 spK2_isSymm (-1) ((1, 1) : Fin 2 × Fin 2))
      * (ssEdgeVec spK2 spK2_isSymm 1 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 1 1))
      * ((ssEdgeVec spK2 spK2_isSymm 0 1)
          ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 1 1) ^ 2 = 0 := by
    simp [ssEdgeVec_self, Matrix.dotProduct_zero]
  have h01 : (((1 - ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2))
        / ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2))
      * (ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1))
      * ((ssEdgeVec spK2 spK2_isSymm 0 1)
          ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1) ^ 2 = -3 / 8 := by
    rw [spF_K2_prob_qm1, ssEdgeVec_dot_K2_QA]
    norm_num
  have h10 : (((1 - ssProb spK2 spK2_isSymm (-1) ((1, 0) : Fin 2 × Fin 2))
        / ssProb spK2 spK2_isSymm (-1) ((1, 0) : Fin 2 × Fin 2))
      * (ssEdgeVec spK2 spK2_isSymm 1 0 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 1 0))
      * ((ssEdgeVec spK2 spK2_isSymm 0 1)
          ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 1 0) ^ 2 = -3 / 8 := by
    have hsw : ssEdgeVec spK2 spK2_isSymm 1 0
        = -(ssEdgeVec spK2 spK2_isSymm 0 1) :=
      ssEdgeVec_swap spK2 spK2_isSymm 1 0
    rw [spF_K2_prob_10_qm1, hsw, Matrix.neg_dotProduct, Matrix.dotProduct_neg,
      neg_neg, ssEdgeVec_dot_K2_QA]
    norm_num
  rw [h00, h11, h01, h10] at hle
  norm_num at hle

/-- **Fence (`quadForm_ssLaplacian_nonneg`, `hq`)**: at `q = -1`, the
sampled outcome, `x = ![1,-1]`, both ordered pairs carry weight
`1/p = -2` and contribute `(w/2) · 1 · (±2)² = -4` each: total
`-8 < 0`. -/
theorem spF_qf_laplacian_hq_fence_QA :
    ¬ (0 ≤ quadForm (ssLaplacian spK2 spK2_isSymm (-1) (fun _ => true))
        (![1, -1] : Fin 2 → ℝ)) := by
  intro hle
  have hprob01 : ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2)
      = -1 / 2 := spF_K2_prob_qm1
  have hprob10 : ssProb spK2 spK2_isSymm (-1) ((1, 0) : Fin 2 × Fin 2)
      = -1 / 2 := spF_K2_prob_10_qm1
  have hprobdiag : ∀ a : Fin 2,
      ssProb spK2 spK2_isSymm (-1) ((a, a) : Fin 2 × Fin 2) = 0 := by
    intro a
    unfold ssProb
    rw [ssEdgeVec_self, Matrix.dotProduct_zero, mul_zero]
    exact min_eq_right (by norm_num)
  have hw01 : ssWeight spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2)
      (fun _ => true) = -2 := by
    have hpne : ssProb spK2 spK2_isSymm (-1) ((0, 1) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hprob01]; norm_num
    unfold ssWeight
    rw [if_neg hpne, hprob01]
    simp only [ssDelta, if_true]
    norm_num
  have hw10 : ssWeight spK2 spK2_isSymm (-1) ((1, 0) : Fin 2 × Fin 2)
      (fun _ => true) = -2 := by
    have hpne : ssProb spK2 spK2_isSymm (-1) ((1, 0) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hprob10]; norm_num
    unfold ssWeight
    rw [if_neg hpne, hprob10]
    simp only [ssDelta, if_true]
    norm_num
  have hwdiag : ∀ a : Fin 2,
      ssWeight spK2 spK2_isSymm (-1) ((a, a) : Fin 2 × Fin 2)
        (fun _ => true) = 0 := by
    intro a
    have hpne : ssProb spK2 spK2_isSymm (-1) ((a, a) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hprobdiag a]; norm_num
    unfold ssWeight
    rw [if_neg hpne, hprobdiag a]
    simp only [ssDelta, if_true, div_zero]
  have hA01 : spK2 0 1 = 1 := by simp [spK2]
  have hA10 : spK2 1 0 = 1 := by simp [spK2]
  have hA00 : spK2 0 0 = 0 := by simp [spK2]
  have hA11 : spK2 1 1 = 0 := by simp [spK2]
  have hxdiff01 : (![1, -1] : Fin 2 → ℝ) 0 - (![1, -1] : Fin 2 → ℝ) 1 = 2 := by
    norm_num [Matrix.cons_val_zero, Matrix.head_cons]
  have hxdiff10 : (![1, -1] : Fin 2 → ℝ) 1 - (![1, -1] : Fin 2 → ℝ) 0 = -2 := by
    norm_num [Matrix.cons_val_zero, Matrix.head_cons]
  have hval : quadForm (ssLaplacian spK2 spK2_isSymm (-1) (fun _ => true))
      (![1, -1] : Fin 2 → ℝ) = -8 := by
    rw [show ssLaplacian spK2 spK2_isSymm (-1) (fun _ => true)
        = ∑ e : Fin 2 × Fin 2, ((ssWeight spK2 spK2_isSymm (-1) e
            (fun _ => true) / 2 * spK2 e.1 e.2)
          • rankOne (ssEdgeDiff e.1 e.2)) from rfl,
      spF_quadForm_finset_sum, Fintype.sum_prod_type]
    simp only [Prod.fst, Prod.snd, Fin.sum_univ_two, quadForm_smul,
      rankOne_quadForm, dotProduct_ssEdgeDiff]
    rw [hw01, hw10, hwdiag 0, hwdiag 1, hA01, hA10, hA00, hA11,
      hxdiff01, hxdiff10, sub_self ( (![1,-1] : Fin 2 → ℝ) 0),
      sub_self ( (![1,-1] : Fin 2 → ℝ) 1)]
    norm_num
  linarith


end CoreFences

section StructuralPins
/-! ## The structural lemmas' positive pins (2026-09-07)

The compiler-derived consumption census found all nine of this
module's sampled-Laplacian structural lemmas among the library's
never-consumed — the machinery under `matrix_bernstein`'s one real
theorem consumer (`Derived.SparsificationTail`), pinned here for the
first time at the `spK2` fixture, at the natural unsaturated budget
`q = 1` (pair probability `1/2`, inverse-probability weights exactly
`2`/`0`), with the sampled Laplacian's quadratic-form VALUE computed
through the definitions (`8` at the alternating vector — the all-true
outcome doubles the true Laplacian, the estimator's exact behavior at
half-probability sampling; the diagonal pairs contribute zero through
the vanishing voltage difference alone).
-/

/-- Pin 1: `imageProjector_isSymm` consumed at the fixture, with the
off-diagonal entry equality derived THROUGH the symmetry theorem. -/
theorem spp_proj_symm_QA :
    (imageProjector spK2 spK2_isSymm).IsSymm
      ∧ imageProjector spK2 spK2_isSymm 0 1
          = imageProjector spK2 spK2_isSymm 1 0 := by
  exact ⟨imageProjector_isSymm spK2 spK2_isSymm,
    (imageProjector_isSymm spK2 spK2_isSymm).apply 0 1⟩

/-- Pin 2: `imageProjector_mul_self` consumed — the diagonal entries'
idempotence read THROUGH the theorem (each diagonal entry is `0` or
`1`, eigen-index dependent; both square to themselves). -/
theorem spp_proj_idem_QA :
    (imageProjector spK2 spK2_isSymm * imageProjector spK2 spK2_isSymm) 0 0
      = imageProjector spK2 spK2_isSymm 0 0
    ∧ (imageProjector spK2 spK2_isSymm * imageProjector spK2 spK2_isSymm) 1 1
      = imageProjector spK2 spK2_isSymm 1 1 := by
  constructor <;> rw [imageProjector_mul_self spK2 spK2_isSymm]

/-- Pin 3: `quadForm_imageProjector_nonneg` at the unit vector. -/
theorem spp_proj_quad_nonneg_QA :
    0 ≤ quadForm (imageProjector spK2 spK2_isSymm) ![1, 0] :=
  quadForm_imageProjector_nonneg spK2 spK2_isSymm ![1, 0]

/-- Pin 4: `l2OpNorm_imageProjector_le` at the fixture. -/
theorem spp_proj_norm_QA :
    ‖imageProjector spK2 spK2_isSymm‖ ≤ 1 :=
  l2OpNorm_imageProjector_le spK2 spK2_isSymm

/-- Pin 5: `ssSampled_isSymm` at the natural unsaturated budget
`q = 1`, at every outcome (the hypothesis set discharged at the
fixture). -/
theorem spp_sampled_symm_QA (ω : (Fin 2 × Fin 2) → Bool) :
    (ssSampled spK2 spK2_isSymm 1 ω).IsSymm :=
  ssSampled_isSymm spK2 spK2_isSymm spK2_nonneg 1 ω

/-- Pin 6: `indepFun_ssSummand` at the two distinct ordered pairs of
`K₂`, budget `q = 1` — the matrix-concentration `h_indep` clause's
design fact, consumed at the fixture's own measure. -/
theorem spp_summand_indep_QA :
    ProbabilityTheory.IndepFun
      (fun ω : (Fin 2 × Fin 2) → Bool =>
        ssSummand spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) ω)
      (fun ω : (Fin 2 × Fin 2) → Bool =>
        ssSummand spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) ω)
      (ssMeasure spK2 spK2_isSymm 1 (by norm_num : (0 : ℝ) ≤ 1)) :=
  indepFun_ssSummand spK2 spK2_isSymm 1 (by norm_num : (0 : ℝ) ≤ 1)
    (by decide)

/-- The unsaturated probability pin: `p = min 1 (1 · 1/2) = 1/2`. -/
theorem spp_prob_half_QA :
    ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) = 1/2 := by
  rw [ssProb, ssEdgeVec_dot_K2_QA]
  norm_num

/-- The sampled weight at the kept outcome: `δ/p = 1/(1/2) = 2` — the
inverse-probability reweighting exact. -/
theorem spp_weight_true_QA :
    ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
      (fun _ => true) = 2 := by
  rw [ssWeight, if_neg (by rw [spp_prob_half_QA]; norm_num),
    spp_prob_half_QA]
  simp [ssDelta]

/-- The sampled weight at the missed outcome: `δ/p = 0/(1/2) = 0`. -/
theorem spp_weight_false_QA :
    ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
      (fun _ => false) = 0 := by
  rw [ssWeight, if_neg (by rw [spp_prob_half_QA]; norm_num),
    spp_prob_half_QA]
  simp [ssDelta]

/-- Pin 7: `ssWeight_nonneg` at both outcomes, THROUGH the theorem
(the values `2`/`0` above make the nonnegativity nontrivial). -/
theorem spp_weight_nonneg_QA :
    0 ≤ ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
        (fun _ => true)
      ∧ 0 ≤ ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
        (fun _ => false) :=
  ⟨ssWeight_nonneg spK2 spK2_isSymm (by norm_num : (0 : ℝ) ≤ 1) _ _,
    ssWeight_nonneg spK2 spK2_isSymm (by norm_num : (0 : ℝ) ≤ 1) _ _⟩

/-- Pin 8: `ssLaplacian_isSymm` at `q = 1`, every outcome. -/
theorem spp_lap_symm_QA (ω : (Fin 2 × Fin 2) → Bool) :
    (ssLaplacian spK2 spK2_isSymm 1 ω).IsSymm :=
  ssLaplacian_isSymm spK2 spK2_isSymm 1 ω

/-- Pin 9: `quadForm_ssLaplacian_nonneg` at the kept outcome and the
alternating vector — the sampled Laplacian's PSD through the theorem. -/
theorem spp_lap_quad_nonneg_QA :
    0 ≤ quadForm (ssLaplacian spK2 spK2_isSymm 1 (fun _ => true))
        ![1, -1] :=
  quadForm_ssLaplacian_nonneg spK2 spK2_isSymm spK2_nonneg
    (by norm_num : (0 : ℝ) ≤ 1) _ _

/-- The swapped pair's unsaturated probability (through the delivered
swapped leverage pin). -/
theorem spp_prob_half_swapped_QA :
    ssProb spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) = 1/2 := by
  rw [ssProb, ssEdgeVec_dot_K2_swapped_QA]
  norm_num

/-- The swapped pair's weight at the kept outcome. -/
theorem spp_weight_true_swapped_QA :
    ssWeight spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2)
      (fun _ => true) = 2 := by
  rw [ssWeight, if_neg (by rw [spp_prob_half_swapped_QA]; norm_num),
    spp_prob_half_swapped_QA]
  simp [ssDelta]

/-- Pin 9's numeric reading: at the all-true outcome and budget `q = 1`
each off-diagonal pair contributes weight `2` halved by the ordered
factor, so the sampled Laplacian is exactly TWICE the true one and the
alternating vector's form is `2 · 4 = 8` (the diagonal pairs
contribute zero through the vanishing voltage difference alone). The
value exercises the weights, the `1/2` ordered-pair factor, and
`rankOne` together — load-bearing on the sampled-Laplacian definition's
exact shape. -/
theorem spp_lap_quad_value_QA :
    quadForm (ssLaplacian spK2 spK2_isSymm 1 (fun _ => true))
        ![1, -1] = 8 := by
  have hadd : ∀ M N : Matrix (Fin 2) (Fin 2) ℝ,
      quadForm (M + N) ![1, -1]
        = quadForm M ![1, -1] + quadForm N ![1, -1] := by
    intro M N
    simp [quadForm, Matrix.add_mulVec, Matrix.add_dotProduct]
  have hterm : ∀ e : Fin 2 × Fin 2,
      quadForm ((ssWeight spK2 spK2_isSymm 1 e (fun _ => true) / 2
          * spK2 e.1 e.2) • rankOne (ssEdgeDiff e.1 e.2))
          (![1, -1] : Fin 2 → ℝ)
        = (ssWeight spK2 spK2_isSymm 1 e (fun _ => true) / 2
            * spK2 e.1 e.2)
          * ((![1, -1] : Fin 2 → ℝ) e.1
              - (![1, -1] : Fin 2 → ℝ) e.2) ^ 2 := by
    intro e
    rw [quadForm_smul, rankOne_quadForm, dotProduct_ssEdgeDiff]
  have hexpand : ssLaplacian spK2 spK2_isSymm 1 (fun _ => true)
      = ((ssWeight spK2 spK2_isSymm 1 ((0, 0) : Fin 2 × Fin 2)
            (fun _ => true) / 2 * spK2 0 0) • rankOne (ssEdgeDiff 0 0))
        + ((ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
            (fun _ => true) / 2 * spK2 0 1) • rankOne (ssEdgeDiff 0 1))
        + (((ssWeight spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2)
            (fun _ => true) / 2 * spK2 1 0) • rankOne (ssEdgeDiff 1 0))
          + ((ssWeight spK2 spK2_isSymm 1 ((1, 1) : Fin 2 × Fin 2)
            (fun _ => true) / 2 * spK2 1 1) • rankOne (ssEdgeDiff 1 1))) := by
    rw [ssLaplacian, Fintype.sum_prod_type]
    simp [Fin.sum_univ_two]
  have hA01 : spK2 0 1 = 1 := by simp [spK2]
  have hA10 : spK2 1 0 = 1 := by simp [spK2]
  rw [hexpand, hadd, hadd, hadd,
    hterm ((0, 0) : Fin 2 × Fin 2), hterm ((0, 1) : Fin 2 × Fin 2),
    hterm ((1, 0) : Fin 2 × Fin 2), hterm ((1, 1) : Fin 2 × Fin 2),
    spp_weight_true_QA, spp_weight_true_swapped_QA]
  simp [spK2]
  norm_num

end StructuralPins

end SparsificationQA
