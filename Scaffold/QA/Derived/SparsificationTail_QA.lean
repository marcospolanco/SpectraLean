/-
  SparsificationTail_QA.lean

  QA for `Scaffold.Derived.SparsificationTail` (the assembly slice of the
  leverage-score sparsification program, Step 1 Slice 3): the K₂ fixtures
  pin the exact deviation identity, its norm at the classical constant
  `1 = 1/q`, the tight norm→quadratic-form transfer, and both tail
  theorems' interface instances; the fences isolate the connectivity
  hypothesis of the Foster budget (refuted on a disconnected graph,
  alongside the connectivity-free positive on the same fixture) and the
  nonempty-event side of the tail bound.

  Falsification content, per the load-bearing-growth policy:

  - **The deviation identity is pinned entrywise-visible**: at the K₂
    all-true outcome the four ordered pairs evaluate to
    `0 + (v_e v_eᵀ) + (v_e v_eᵀ) + 0` (the guard's junk-zero at loop
    pairs included), so a wrong guard, weight, or projector identity
    breaks the value.
  - **The deviation norm equals `1 = 1/q` exactly** — the summed
    pointwise bound's classical constant attained at a real outcome,
    tight both sides (the lower side through the eigenvector witness).
  - **The transfer lemma's constant is tight** at the same fixture:
    the deviation's quadratic form at the edge vector equals
    `t · (v ⬝ᵥ v) = 1 · 1/2` with equality, not slack.
  - **Connectivity is load-bearing where the budget needs it**: on the
    two-component zero graph the leverage budget is `0 ≠ card − 1`,
    while the tail theorem (which needs no connectivity) still applies
    with an identically-zero deviation.

  QA does not prove the `matrix_bernstein` axiom; it checks the
  assembly's interfaces and the deterministic pieces' values. All proofs
  are real Lean proofs (no `sorry`/`admit`).
-/

import Scaffold.Derived.SparsificationTail

namespace SparsificationTailQA

open MeasureTheory ProbabilityTheory SpectralGraphTheory
open Scaffold.Derived.SparsificationTail
open scoped BigOperators Matrix Matrix.L2OpNorm

/-! ## The `K₂` fixture -/

/-- The unit edge `K₂` (as in `Sparsification_QA`). -/
def spK2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

theorem spK2_isSymm : spK2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [spK2]

theorem spK2_nonneg : ∀ i j, 0 ≤ spK2 i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [spK2]

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

theorem spK2_R01 : effectiveResistance spK2 0 1 = 1 :=
  effectiveResistance_eq spK2 spK2_isSymm spK2_nonneg spK2_connected
    ⟨![1, 0], spK2_pot01, by norm_num [Matrix.cons_val_zero]⟩

theorem ssEdgeVec_dot_K2 :
    ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1
      = 1 / 2 := by
  rw [ssEdgeVec_dotProduct_self spK2 spK2_isSymm spK2_nonneg spK2_connected
    0 1]
  have hw : spK2 0 1 = 1 := by simp [spK2]
  rw [spK2_R01, hw]
  norm_num

theorem ssProb_K2_01 (q : ℝ) :
    ssProb spK2 spK2_isSymm q ((0, 1) : Fin 2 × Fin 2)
      = min 1 (q / 2) := by
  simp only [ssProb, ssEdgeVec_dot_K2]
  ring_nf

theorem ssProb_K2_10 (q : ℝ) :
    ssProb spK2 spK2_isSymm q ((1, 0) : Fin 2 × Fin 2)
      = min 1 (q / 2) := by
  have hswap : ssEdgeVec spK2 spK2_isSymm 1 0
      = -(ssEdgeVec spK2 spK2_isSymm 0 1) := ssEdgeVec_swap spK2 spK2_isSymm 1 0
  have hdot : ssEdgeVec spK2 spK2_isSymm 1 0 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 1 0
      = 1 / 2 := by
    rw [hswap]
    have : (-(ssEdgeVec spK2 spK2_isSymm 0 1 : Fin 2 → ℝ))
        ⬝ᵥ (-(ssEdgeVec spK2 spK2_isSymm 0 1))
        = ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1 := by
      rw [Matrix.neg_dotProduct, Matrix.dotProduct_neg, neg_neg]
    rw [this, ssEdgeVec_dot_K2]
  simp only [ssProb, hdot]
  ring_nf

theorem rankOne_zero_eq : rankOne ((0 : Fin 2 → ℝ)) = 0 := by
  ext i j; simp [rankOne]

/-- The `K₂` rank-one norm pin, lower side (the eigenvector witness). -/
theorem rankOne_norm_ge_K2 :
    1 / 2 ≤ ‖rankOne (ssEdgeVec spK2 spK2_isSymm 0 1)‖ := by
  obtain ⟨i, hi⟩ := exists_eigvalOf_eq_of_mulVec_eq_smul
    (rankOne_isSymm (ssEdgeVec spK2 spK2_isSymm 0 1))
    (by
      intro h
      have : ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1
          = 0 := by rw [h, Matrix.dotProduct_zero]
      rw [ssEdgeVec_dot_K2] at this
      norm_num at this)
    (rankOne_mulVec (ssEdgeVec spK2 spK2_isSymm 0 1)
      (ssEdgeVec spK2 spK2_isSymm 0 1))
  have habs := Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.abs_eigvalOf_le_l2OpNorm
    (rankOne_isSymm (ssEdgeVec spK2 spK2_isSymm 0 1)) i
  have hval : (ssEdgeVec spK2 spK2_isSymm 0 1) ⬝ᵥ
      (ssEdgeVec spK2 spK2_isSymm 0 1) = 1 / 2 := ssEdgeVec_dot_K2
  rw [hi, hval, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] at habs
  exact habs

/-- **The rank-one norm pinned two-sided at the `K₂` edge vector**:
`‖v_e v_eᵀ‖ = 1/2` exactly. -/
theorem rankOne_norm_K2 :
    ‖rankOne (ssEdgeVec spK2 spK2_isSymm 0 1)‖ = 1 / 2 := by
  refine le_antisymm ?_ rankOne_norm_ge_K2
  have h := l2OpNorm_rankOne_le (ssEdgeVec spK2 spK2_isSymm 0 1)
  rw [ssEdgeVec_dot_K2] at h
  exact h

/-! ## The deviation identity and its norm -/

/-- **The deviation identity pinned at `K₂`, `q = 1`, all-true**: the
sampled operator minus the projector is exactly `2 • (v_e v_eᵀ)` at the
single edge's rank-one term — every piece of the identity (the guard,
the reweighting `δ/p = 2`, the junk-zero loop pairs) visible in the
four-term evaluation. -/
theorem ssSampled_deviation_K2 :
    ssSampled spK2 spK2_isSymm 1 (fun _ => true) - imageProjector spK2 spK2_isSymm
      = (2 : ℝ) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) := by
  rw [ssSampled_sub_imageProjector spK2 spK2_isSymm spK2_nonneg 1
    (fun _ => true)]
  have t00 : ssSummand spK2 spK2_isSymm 1 ((0, 0) : Fin 2 × Fin 2)
      (fun _ => true) = 0 := by
    have hv : ssEdgeVec spK2 spK2_isSymm 0 0 = 0 := ssEdgeVec_self spK2 spK2_isSymm 0
    have hp : ssProb spK2 spK2_isSymm 1 ((0, 0) : Fin 2 × Fin 2) = 0 := by
      simp only [ssProb, hv, Matrix.dotProduct_zero, mul_zero]
      norm_num
    have hne : ssProb spK2 spK2_isSymm 1 ((0, 0) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hp]; norm_num
    simp only [ssSummand, if_neg hne, hv, rankOne_zero_eq, smul_zero]
  have t11 : ssSummand spK2 spK2_isSymm 1 ((1, 1) : Fin 2 × Fin 2)
      (fun _ => true) = 0 := by
    have hv : ssEdgeVec spK2 spK2_isSymm 1 1 = 0 := ssEdgeVec_self spK2 spK2_isSymm 1
    have hp : ssProb spK2 spK2_isSymm 1 ((1, 1) : Fin 2 × Fin 2) = 0 := by
      simp only [ssProb, hv, Matrix.dotProduct_zero, mul_zero]
      norm_num
    have hne : ssProb spK2 spK2_isSymm 1 ((1, 1) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hp]; norm_num
    simp only [ssSummand, if_neg hne, hv, rankOne_zero_eq, smul_zero]
  have t01 : ssSummand spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
      (fun _ => true)
      = rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) := by
    have hp : ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) = 1 / 2 := by
      rw [ssProb_K2_01]; norm_num
    have hne : ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hp]; norm_num
    have hc : ssDelta ((0, 1) : Fin 2 × Fin 2) (fun _ => true)
        / ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) - 1 = 1 := by
      rw [hp]; simp [ssDelta]; norm_num
    simp only [ssSummand, if_neg hne]
    rw [hc, one_smul]
  have t10 : ssSummand spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2)
      (fun _ => true)
      = rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) := by
    have hp : ssProb spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) = 1 / 2 := by
      rw [ssProb_K2_10]; norm_num
    have hne : ssProb spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hp]; norm_num
    have hc : ssDelta ((1, 0) : Fin 2 × Fin 2) (fun _ => true)
        / ssProb spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) - 1 = 1 := by
      rw [hp]; simp [ssDelta]; norm_num
    have hv : ssEdgeVec spK2 spK2_isSymm 1 0
        = -(ssEdgeVec spK2 spK2_isSymm 0 1) := ssEdgeVec_swap spK2 spK2_isSymm 1 0
    simp only [ssSummand, if_neg hne]
    rw [hc, one_smul, hv, rankOne_neg]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, t00, t01, t10, t11, add_zero, zero_add]
  exact (two_smul ℝ (rankOne (ssEdgeVec spK2 spK2_isSymm 0 1))).symm

/-- **The deviation norm is exactly `1 = 1/q`** at the `K₂` all-true
outcome — the pointwise bound `‖X_e ω‖ ≤ 1/q` summed to a real two-pair
deviation at its exact classical value, tight both sides. -/
theorem ssSampled_deviation_norm_K2 :
    ‖ssSampled spK2 spK2_isSymm 1 (fun _ => true)
      - imageProjector spK2 spK2_isSymm‖ = 1 := by
  rw [ssSampled_deviation_K2, norm_smul, rankOne_norm_K2]
  norm_num

/-! ## The quadratic-form transfer at the fixture -/

/-- **The projector's quadratic form at the edge vector** — the `K₂`
instance of the Slice-2 identity `qF(Π) x = ∑_e (x ⬝ᵥ v_e)²` (that
theorem's first consumer): `1/2` by the four-pair evaluation. -/
theorem quadForm_imageProjector_K2 :
    quadForm (imageProjector spK2 spK2_isSymm)
        (ssEdgeVec spK2 spK2_isSymm 0 1) = 1 / 2 := by
  rw [quadForm_imageProjector_eq spK2 spK2_isSymm spK2_nonneg]
  have hv00 : ssEdgeVec spK2 spK2_isSymm 0 0 = 0 := ssEdgeVec_self spK2 spK2_isSymm 0
  have hv11 : ssEdgeVec spK2 spK2_isSymm 1 1 = 0 := ssEdgeVec_self spK2 spK2_isSymm 1
  have hv10 : ssEdgeVec spK2 spK2_isSymm 1 0
      = -(ssEdgeVec spK2 spK2_isSymm 0 1) := ssEdgeVec_swap spK2 spK2_isSymm 1 0
  have t00 : (ssEdgeVec spK2 spK2_isSymm 0 1) ⬝ᵥ (ssEdgeVec spK2 spK2_isSymm 0 0)
      = 0 := by rw [hv00, Matrix.dotProduct_zero]
  have t11 : (ssEdgeVec spK2 spK2_isSymm 0 1) ⬝ᵥ (ssEdgeVec spK2 spK2_isSymm 1 1)
      = 0 := by rw [hv11, Matrix.dotProduct_zero]
  have t10 : (ssEdgeVec spK2 spK2_isSymm 0 1) ⬝ᵥ (ssEdgeVec spK2 spK2_isSymm 1 0)
      = -(1 / 2 : ℝ) := by
    rw [hv10, Matrix.dotProduct_neg, ssEdgeVec_dot_K2]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, t00, t10, t11, ssEdgeVec_dot_K2]
  norm_num

/-- **The sampled operator's quadratic form at the edge vector**:
`qF(S) v = 1` at the `K₂` all-true outcome (the deviation `1/2` on top
of the projector's `1/2`). -/
theorem quadForm_ssSampled_K2 :
    quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true))
        (ssEdgeVec spK2 spK2_isSymm 0 1) = 1 := by
  have hEq : ssSampled spK2 spK2_isSymm 1 (fun _ => true)
      = (2 : ℝ) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1)
        + imageProjector spK2 spK2_isSymm := by
    rw [← ssSampled_deviation_K2, sub_add_cancel]
  rw [hEq, quadForm_add, quadForm_smul, rankOne_quadForm,
    quadForm_imageProjector_K2, ssEdgeVec_dot_K2]
  norm_num

/-- **The transfer lemma is tight at `K₂`**: the deviation's quadratic
form at the edge vector equals `t · (v ⬝ᵥ v) = 1 · 1/2` exactly — the
`‖M‖ ≤ t → |xᵀMx| ≤ t xᵀx` bound is attained, not slack. -/
theorem transfer_tight_K2 :
    quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true)
        - imageProjector spK2 spK2_isSymm) (ssEdgeVec spK2 spK2_isSymm 0 1)
      = 1 * (ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1) := by
  rw [ssSampled_deviation_K2, quadForm_smul, rankOne_quadForm,
    ssEdgeVec_dot_K2]
  norm_num

/-- The transfer instance through the theorem itself at the same
fixture (the additive statement's both sides pinned to the tight
value). -/
theorem transfer_instance_K2 :
    |quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true))
        (ssEdgeVec spK2 spK2_isSymm 0 1)
      - quadForm (imageProjector spK2 spK2_isSymm)
        (ssEdgeVec spK2 spK2_isSymm 0 1)|
      ≤ 1 * (ssEdgeVec spK2 spK2_isSymm 0 1 ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1) := by
  have h := abs_quadForm_le_of_l2OpNorm_le (t := (1 : ℝ))
    (by rw [← ssSampled_deviation_norm_K2]) (ssEdgeVec spK2 spK2_isSymm 0 1)
  have hqf : quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true))
      (ssEdgeVec spK2 spK2_isSymm 0 1)
      - quadForm (imageProjector spK2 spK2_isSymm)
        (ssEdgeVec spK2 spK2_isSymm 0 1)
      = quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true)
        - imageProjector spK2 spK2_isSymm) (ssEdgeVec spK2 spK2_isSymm 0 1) :=
    (quadForm_sub_matrix _ _ _).symm
  rw [hqf]
  exact h

/-! ## The tail theorems' interface instances -/

/-- **The tail bound instantiated at `K₂`** (the interface pin; the
event side is nonempty by the exact-norm pin below). -/
theorem norm_tail_K2 :
    ssMeasure spK2 spK2_isSymm 1 (by norm_num : (0 : ℝ) ≤ 1)
        {ω | ‖ssSampled spK2 spK2_isSymm 1 ω
          - imageProjector spK2 spK2_isSymm‖ ≥ 1}
      ≤ ENNReal.ofReal (2 * ((Fintype.card (Fin 2) : ℝ))
        * Real.exp (-((1 : ℝ) ^ 2) / (2 / 1 + 2 * 1 / (3 * 1)))) :=
  sparsification_norm_tail spK2 spK2_isSymm spK2_nonneg 1 one_pos 1 zero_le_one

/-- **The quadratic-form tail instantiated at `K₂`** (interface pin). -/
theorem quadForm_tail_K2 :
    ssMeasure spK2 spK2_isSymm 1 (by norm_num : (0 : ℝ) ≤ 1)
        {ω | ∃ x : Fin 2 → ℝ, (1 : ℝ) * (x ⬝ᵥ x)
          < |quadForm (ssSampled spK2 spK2_isSymm 1 ω) x
            - quadForm (imageProjector spK2 spK2_isSymm) x|}
      ≤ ENNReal.ofReal (2 * ((Fintype.card (Fin 2) : ℝ))
        * Real.exp (-((1 : ℝ) ^ 2) / (2 / 1 + 2 * 1 / (3 * 1)))) :=
  sparsification_quadForm_tail spK2 spK2_isSymm spK2_nonneg 1 one_pos 1
    zero_le_one

/-- **The event side is real**: the all-true outcome is in the norm
event at `t = 1` — the bound is about a nonempty event, not a straw. -/
theorem norm_event_nonempty_K2 :
    (fun _ => true) ∈ {ω : (Fin 2 × Fin 2) → Bool |
      ‖ssSampled spK2 spK2_isSymm 1 ω
        - imageProjector spK2 spK2_isSymm‖ ≥ 1} := by
  simp only [Set.mem_setOf_eq]
  rw [ssSampled_deviation_norm_K2]

/-! ## The disconnected fence (obligation 3) -/

/-- The zero adjacency on two vertices: two components. -/
def spZero : Matrix (Fin 2) (Fin 2) ℝ := 0

theorem spZero_isSymm : spZero.IsSymm :=
  Matrix.IsSymm.ext fun _ _ => by simp [spZero]

theorem spZero_nonneg : ∀ i j, 0 ≤ spZero i j := by
  intro i j; simp [spZero]

theorem laplacian_zero_eq : laplacian spZero = 0 := by
  ext i j
  simp [laplacian, degreeMatrix, deg, spZero]

theorem eigvalOf_laplacian_zero (k : Fin 2) :
    eigvalOf (laplacian spZero) (laplacian_symmetric spZero spZero_isSymm) k
      = 0 := by
  rw [← quadForm_eigvecOf_self (laplacian_symmetric spZero spZero_isSymm) k]
  have hq0 : ∀ y : Fin 2 → ℝ, quadForm (laplacian spZero) y = 0 := by
    intro y
    rw [laplacian_zero_eq]
    simp [quadForm]
  exact hq0 _

theorem ssEdgeVec_zero (u v : Fin 2) :
    ssEdgeVec spZero spZero_isSymm u v = 0 := by
  funext k
  simp only [ssEdgeVec, eigvalOf_laplacian_zero k]
  rfl

/-- **The disconnected fence**: on the two-component zero graph the
leverage budget is `0`, not `card V − 1 = 1` — connectivity is
load-bearing at the Foster budget corollary exactly as its own scope
note records (the tail theorem above needs no connectivity; the
*interpretation* of the budget does). -/
theorem budget_fence_disconnected_K2 :
    ¬ (∑ u, ∑ v, ssEdgeVec spZero spZero_isSymm u v
          ⬝ᵥ ssEdgeVec spZero spZero_isSymm u v
        = (Fintype.card (Fin 2) : ℝ) - 1) := by
  have hzero : ∀ u v : Fin 2, ssEdgeVec spZero spZero_isSymm u v
      ⬝ᵥ ssEdgeVec spZero spZero_isSymm u v = 0 := by
    intro u v
    rw [ssEdgeVec_zero, Matrix.dotProduct_zero]
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  rw [hcard]
  simp only [hzero, Finset.sum_const_zero]
  norm_num

/-- **The tail theorem is connectivity-free**: at the disconnected zero
graph the deviation is identically zero (every summand is the zero
rank-one factor), so the assembly does not depend on connectivity
anywhere — the positive companion of the fence above. -/
theorem deviation_zero_disconnected :
    ssSampled spZero spZero_isSymm 1 (fun _ => true)
      - imageProjector spZero spZero_isSymm = 0 := by
  have hS : ssSampled spZero spZero_isSymm 1 (fun _ => true) = 0 := by
    simp only [ssSampled, ssEdgeVec_zero, rankOne_zero_eq, smul_zero,
      Finset.sum_const_zero]
  have hProj : imageProjector spZero spZero_isSymm = 0 := by
    ext i j
    simp [imageProjector, eigvalOf_laplacian_zero]
  rw [hS, hProj, sub_zero]

end SparsificationTailQA
