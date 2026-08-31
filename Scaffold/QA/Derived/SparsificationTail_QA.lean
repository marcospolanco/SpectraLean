/-
  SparsificationTail_QA.lean

  QA for `Scaffold.Derived.SparsificationTail` (the assembly slice of
  the leverage-score sparsification program, Step 1 Slice 3): the K₂ fixtures
  pin the exact deviation identity, its norm at the classical constant
  `1 = 1/q`, the tight norm→quadratic-form transfer, and both tail
  theorems' interface instances; the fences isolate the connectivity
  hypothesis of the Foster budget (refuted on a disconnected graph,
  alongside the connectivity-free positive on the same fixture) and the
  nonempty-event side of the tail bound. The `(1±ε)` section pins the
  multiplicative refinement: the edge vector's order-independent `im Π`
  membership, the engine identity, the tight ε = 1 two-sided instance,
  failure-event nonemptiness at ε = 1/2, the *un-guarded pointwise
  refutation* at the all-false outcome (the cone hypothesis is
  load-bearing), and both new theorems' interface instances (the
  budget's `log 8 ≤ 300/32` discharged from `add_one_le_exp`). The
  graph-vector section pins the textbook form on the sampled Laplacian
  (raw pins, a two-route correspondence join, the tight `ε = 1`
  instance) and fences the transport engines' nonnegativity hypothesis
  on a signed fixture with a nonpositive spectrum. The closed-form
  budget section (2026-08-31) pins the GNN-facing `sparsificationBudget`
  at exact-`e` designs, proves the `max 1` floor load-bearing, pins
  minimality, and joins the closed form to the hand-chosen `q = 100`.

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

/-! ## The `(1±ε)` multiplicative refinement (the follow-on delivery) -/

/-- **The edge vector is `im Π`-coordinate**: the projector fixes it —
proved *order-independently* (at a zero-eigenvalue basis index the edge
vector's entry vanishes by its own definition, so both sides are `0`;
elsewhere the projector acts as the identity). No K₂ spectrum pin is
needed, so the fact survives any eigenbasis ordering. -/
theorem imageProjector_mulVec_ssEdgeVec_K2 :
    imageProjector spK2 spK2_isSymm *ᵥ
      (ssEdgeVec spK2 spK2_isSymm 0 1)
      = ssEdgeVec spK2 spK2_isSymm 0 1 := by
  funext k
  have hstep : (imageProjector spK2 spK2_isSymm *ᵥ
      (ssEdgeVec spK2 spK2_isSymm 0 1)) k
      = (if eigvalOf (laplacian spK2)
            (laplacian_symmetric spK2 spK2_isSymm) k = 0
          then (0 : ℝ) else 1)
        * ssEdgeVec spK2 spK2_isSymm 0 1 k := by
    simp [imageProjector, Matrix.mulVec, Matrix.diagonal, Matrix.dotProduct,
      Finset.sum_ite_eq]
  rw [hstep]
  by_cases h : eigvalOf (laplacian spK2)
      (laplacian_symmetric spK2 spK2_isSymm) k = 0
  · rw [if_pos h]
    have hv : ssEdgeVec spK2 spK2_isSymm 0 1 k = 0 := by simp [ssEdgeVec, h]
    rw [hv, mul_zero]
  · rw [if_neg h, one_mul]

/-- **The engine lemma's first instance**: at the edge vector the
projector's quadratic form is exactly the squared norm — `1/2 = 1/2`,
joined to the existing independent pin of the same value by the
four-pair route (`quadForm_imageProjector_K2`). -/
theorem quadForm_imageProjector_eq_of_mulVec_K2 :
    quadForm (imageProjector spK2 spK2_isSymm)
        (ssEdgeVec spK2 spK2_isSymm 0 1)
      = ssEdgeVec spK2 spK2_isSymm 0 1
          ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1 :=
  quadForm_imageProjector_eq_of_mulVec_eq spK2 spK2_isSymm _
    imageProjector_mulVec_ssEdgeVec_K2

/-- **The tight `(1±ε)` instance at `ε = 1`**: at the all-true outcome
both multiplicative bounds hold at the edge vector — and the upper side
is *attained with equality* (`qF(S) v = 1 = (1+1)·(1/2)`), consistent
with the deviation norm being exactly `1 = 1/q` there (the transfer is
tight, as `transfer_tight_K2` records). -/
theorem multiplicative_bounds_tight_K2 :
    (1 - (1 : ℝ)) * (ssEdgeVec spK2 spK2_isSymm 0 1
        ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1)
      ≤ quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true))
          (ssEdgeVec spK2 spK2_isSymm 0 1)
    ∧ quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true))
          (ssEdgeVec spK2 spK2_isSymm 0 1)
      ≤ (1 + (1 : ℝ)) * (ssEdgeVec spK2 spK2_isSymm 0 1
          ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1) := by
  rw [quadForm_ssSampled_K2, ssEdgeVec_dot_K2]
  norm_num

/-- **The failure event is real**: at `ε = 1/2` the all-true outcome is
in the multiplicative failure event, witnessed by the edge vector —
`qF(S) v = 1 > (3/2)·(1/2) = 3/4`, the hand value. -/
theorem multiplicative_event_nonempty_K2 :
    (fun _ => true) ∈ {ω : (Fin 2 × Fin 2) → Bool |
      ∃ x : Fin 2 → ℝ, imageProjector spK2 spK2_isSymm *ᵥ x = x ∧
        ((1 - 1 / 2) * (x ⬝ᵥ x)
            > quadForm (ssSampled spK2 spK2_isSymm 1 ω) x ∨
          quadForm (ssSampled spK2 spK2_isSymm 1 ω) x
            > (1 + 1 / 2) * (x ⬝ᵥ x))} := by
  simp only [Set.mem_setOf_eq]
  refine ⟨ssEdgeVec spK2 spK2_isSymm 0 1,
    imageProjector_mulVec_ssEdgeVec_K2, Or.inr ?_⟩
  rw [quadForm_ssSampled_K2, ssEdgeVec_dot_K2]
  norm_num

/-! ### The cone fence: the `im Π` restriction is load-bearing -/

/-- **At the all-false outcome nothing is sampled**: `S = 0` — both
cross-pair weights are `δ/p = 0` (the `δ`'s vanish), and the loop pairs'
rank-one factors are the zero matrix whatever the junk coefficient. -/
theorem ssSampled_allFalse_K2 :
    ssSampled spK2 spK2_isSymm 1 (fun _ => false) = 0 := by
  have hw01 : ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
      (fun _ => false) = 0 := by
    have hp : ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
        = 1 / 2 := by rw [ssProb_K2_01]; norm_num
    have hne : ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hp]; norm_num
    rw [ssWeight, if_neg hne, hp, ssDelta]
    norm_num
  have hw10 : ssWeight spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2)
      (fun _ => false) = 0 := by
    have hp : ssProb spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2)
        = 1 / 2 := by rw [ssProb_K2_10]; norm_num
    have hne : ssProb spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) ≠ 1 := by
      rw [hp]; norm_num
    rw [ssWeight, if_neg hne, hp, ssDelta]
    norm_num
  have hloop : ∀ u : Fin 2,
      ssWeight spK2 spK2_isSymm 1 (u, u) (fun _ => false)
        • rankOne (ssEdgeVec spK2 spK2_isSymm u u) = 0 := by
    intro u
    rw [ssEdgeVec_self, rankOne_zero_eq, smul_zero]
  have h01 : ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
        (fun _ => false)
        • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1) = 0 := by
    rw [hw01, zero_smul]
  have h10 : ssWeight spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2)
        (fun _ => false)
        • rankOne (ssEdgeVec spK2 spK2_isSymm 1 0) = 0 := by
    rw [hw10, zero_smul]
  rw [ssSampled, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, hloop, h01, h10, add_zero, zero_add]

/-- **The un-guarded pointwise claim is false** — the cone hypothesis
fenced: at the all-false outcome *no* quadratic form is positive, so
the multiplicative lower bound fails at `onesVec`
(`(1/2)·2 = 1 > 0 = qF(S) ones`). The tail's `im Π` restriction is
what makes the multiplicative reading sound; without it the statement
is refuted at a real outcome. -/
theorem multiplicative_guard_fence_K2 :
    ¬ (∀ x : Fin 2 → ℝ, (1 - 1 / 2) * (x ⬝ᵥ x)
        ≤ quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => false)) x) := by
  intro h
  have h1 := h (fun _ => (1 : ℝ))
  rw [ssSampled_allFalse_K2, quadForm, Matrix.zero_mulVec,
    Matrix.dotProduct_zero] at h1
  norm_num at h1

/-! ### The two new theorems' interface instances -/

/-- **The multiplicative tail instantiated at `K₂`** (interface pin,
`q = 1`, `ε = 1/2`; the event side is nonempty by the exact pin above). -/
theorem multiplicative_tail_K2 :
    ssMeasure spK2 spK2_isSymm 1 (by norm_num : (0 : ℝ) ≤ 1)
        {ω | ∃ x : Fin 2 → ℝ, imageProjector spK2 spK2_isSymm *ᵥ x = x ∧
          ((1 - 1 / 2) * (x ⬝ᵥ x)
              > quadForm (ssSampled spK2 spK2_isSymm 1 ω) x ∨
            quadForm (ssSampled spK2 spK2_isSymm 1 ω) x
              > (1 + 1 / 2) * (x ⬝ᵥ x))}
      ≤ ENNReal.ofReal (2 * ((Fintype.card (Fin 2) : ℝ))
        * Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 / 1 + 2 * (1 / 2) / (3 * 1)))) :=
  sparsification_multiplicative_tail spK2 spK2_isSymm spK2_nonneg 1 one_pos
    (1 / 2) (by norm_num)

/-- **The budget corollary instantiated at `K₂`** (interface pin,
`ε = 1/2`, `δ = 1/2`, `q = 100`): the budget hypothesis
`(8/3)·log 8/(1/4) ≤ 100` is discharged by `log 8 ≤ 300/32` (itself
from `add_one_le_exp` at `224/32` — `8 = 7 + 1 ≤ exp 7 ≤ exp 9.375`),
driving the failure measure to `≤ 1/2`. -/
theorem budget_tail_K2 :
    ssMeasure spK2 spK2_isSymm 100 (by norm_num : (0 : ℝ) ≤ 100)
        {ω | ∃ x : Fin 2 → ℝ, imageProjector spK2 spK2_isSymm *ᵥ x = x ∧
          ((1 - 1 / 2) * (x ⬝ᵥ x)
              > quadForm (ssSampled spK2 spK2_isSymm 100 ω) x ∨
            quadForm (ssSampled spK2 spK2_isSymm 100 ω) x
              > (1 + 1 / 2) * (x ⬝ᵥ x))}
      ≤ ENNReal.ofReal (1 / 2) := by
  have hlog8 : Real.log (8 : ℝ) ≤ 300 / 32 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (8 : ℝ) = 224 / 32 + 1 := by norm_num
      _ ≤ Real.exp (224 / 32) := Real.add_one_le_exp _
      _ ≤ Real.exp (300 / 32) := Real.exp_le_exp.mpr (by norm_num)
  have hbudget : (8 / 3) * Real.log (2 * ((Fintype.card (Fin 2) : ℝ)) / (1 / 2))
        / (1 / 2) ^ 2 ≤ 100 := by
    have hcard : ((Fintype.card (Fin 2) : ℝ)) = 2 := by simp
    rw [hcard]
    have h8 : (2 : ℝ) * 2 / (1 / 2) = 8 := by norm_num
    rw [h8]
    have hnorm : (8 / 3 : ℝ) * Real.log 8 / (1 / 2) ^ 2
        = (32 / 3) * Real.log 8 := by
      field_simp
      ring
    rw [hnorm]
    linarith [hlog8]
  exact sparsification_multiplicative_budget spK2 spK2_isSymm spK2_nonneg
    (1 / 2) (by norm_num) (by norm_num) (1 / 2) (by norm_num) 100
    (by norm_num : (0 : ℝ) < 100) hbudget

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

/-! ## The graph-vector form (the follow-on delivery)

The textbook sentence: `xᵀL̃(ω)x` vs `xᵀLx` for every graph vector, no
`im Π` restriction — the transport is on the cone by construction.
Pins: the raw Laplacian energy `4` and the raw sampled-Laplacian form
`8` (per-pair `A`-arithmetic), the transport isometry instance, the
correspondence joined by two independent routes (the raw `8` against
the sampled operator's own evaluation through the claim-A dot values),
the tight `ε = 1` instance (`8 = 2·4` attained), failure-event
nonemptiness at `ε = 1/2`, both interface pins, and the **signed-fixture
fences** — one fixture (`A = !![0,−2,1; −2,0,−2; 1,−2,0]`,
`L = −rankOne ![1,−2,1]`) refuting the transport isometry (`−36 < 0`) and
claim A (junk-zero transport against `√(1/2) ≠ 0`) when `hnn` is
dropped: nonnegativity is load-bearing on both new engines. -/

/-- Local copy of the sum-split helper (private in the module). -/
private theorem quadForm_finset_sum {V : Type} [Fintype V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (M : ι → Matrix V V ℝ) (x : V → ℝ) :
    quadForm (∑ i, M i) x = ∑ i, quadForm (M i) x := by
  have hadd : ∀ P Q : Matrix V V ℝ,
      quadForm (P + Q) x = quadForm P x + quadForm Q x := by
    intro P Q
    show x ⬝ᵥ ((P + Q) *ᵥ x) = x ⬝ᵥ (P *ᵥ x) + x ⬝ᵥ (Q *ᵥ x)
    rw [Matrix.add_mulVec, Matrix.dotProduct_add]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [quadForm]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]

/-- The graph-vector fixture `x = e₀ − e₁`. -/
def spx : Fin 2 → ℝ := ![1, -1]

theorem quadForm_laplacian_K2 :
    quadForm (laplacian spK2) spx = 4 := by
  rw [laplacian_quadForm spK2 spK2_isSymm spx]
  simp only [Fin.sum_univ_two, spK2, spx]
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

theorem ssTransport_iso_K2 :
    ssTransport spK2 spK2_isSymm spx ⬝ᵥ ssTransport spK2 spK2_isSymm spx
      = 4 := by
  rw [← quadForm_laplacian_eq_ssTransport spK2 spK2_isSymm spK2_nonneg spx,
    quadForm_laplacian_K2]

theorem ssWeight_K2_01 :
    ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) (fun _ => true) = 2 := by
  have hp : ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) = 1 / 2 := by
    rw [ssProb_K2_01]; norm_num
  have hne : ssProb spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2) ≠ 1 := by
    rw [hp]; norm_num
  rw [ssWeight, if_neg hne, hp]
  simp [ssDelta]

theorem ssWeight_K2_10 :
    ssWeight spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) (fun _ => true) = 2 := by
  have hp : ssProb spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) = 1 / 2 := by
    rw [ssProb_K2_10]; norm_num
  have hne : ssProb spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2) ≠ 1 := by
    rw [hp]; norm_num
  rw [ssWeight, if_neg hne, hp]
  simp [ssDelta]

/-- **The raw sampled-Laplacian pin**: `xᵀL̃x = 8` by the per-pair
evaluation of the definition (weights `2` at the two cross pairs,
coefficient `W/2 · A`, differences `2`), pure `A`-arithmetic. -/
theorem quadForm_ssLaplacian_K2 :
    quadForm (ssLaplacian spK2 spK2_isSymm 1 (fun _ => true)) spx = 8 := by
  rw [ssLaplacian, quadForm_finset_sum, Fintype.sum_prod_type]
  have hloop : ∀ u : Fin 2,
      quadForm ((ssWeight spK2 spK2_isSymm 1 (u, u) (fun _ => true) / 2
          * spK2 u u) • rankOne (ssEdgeDiff u u)) spx = 0 := by
    intro u
    have h0 : spK2 u u = 0 := by fin_cases u <;> simp [spK2]
    simp only [h0, mul_zero, zero_smul]
    simp [quadForm]
  have t01 : quadForm ((ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
        (fun _ => true) / 2 * spK2 0 1) • rankOne (ssEdgeDiff 0 1)) spx = 4 := by
    rw [quadForm_smul, rankOne_quadForm, dotProduct_ssEdgeDiff, ssWeight_K2_01]
    norm_num [spK2, spx, Matrix.cons_val_zero, Matrix.head_cons]
  have t10 : quadForm ((ssWeight spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2)
        (fun _ => true) / 2 * spK2 1 0) • rankOne (ssEdgeDiff 1 0)) spx = 4 := by
    rw [quadForm_smul, rankOne_quadForm, dotProduct_ssEdgeDiff, ssWeight_K2_10]
    norm_num [spK2, spx, Matrix.cons_val_zero, Matrix.head_cons]
  simp only [Fin.sum_univ_two, hloop, t01, t10]
  norm_num

/-- **The correspondence instance** (theorem route). -/
theorem ssLaplacian_corr_K2 :
    quadForm (ssLaplacian spK2 spK2_isSymm 1 (fun _ => true)) spx
      = quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true))
          (ssTransport spK2 spK2_isSymm spx) :=
  quadForm_ssLaplacian_eq spK2 spK2_isSymm spK2_nonneg 1 _ spx

theorem sqrt_half_mul_two : Real.sqrt ((1 : ℝ) / 2) * 2 = Real.sqrt 2 := by
  have h1 : Real.sqrt ((1 : ℝ) / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (show (0 : ℝ) ≤ 1 by norm_num) 2, Real.sqrt_one]
  rw [h1, div_mul_eq_mul_div, one_mul,
    div_eq_iff (by positivity : (Real.sqrt (2 : ℝ)) ≠ 0)]
  exact (Real.mul_self_sqrt (by norm_num)).symm

theorem ssTransport_dot_ssEdgeVec_K2_01 :
    ssTransport spK2 spK2_isSymm spx ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 0 1
      = Real.sqrt 2 := by
  have h := ssTransport_dot_ssEdgeVec spK2 spK2_isSymm spK2_nonneg
    (by simp [spK2] : (0 : ℝ) < spK2 0 1) spx
  rw [h]
  have hA : spK2 0 1 = 1 := by simp [spK2]
  have hdx : spx 0 - spx 1 = 2 := by
    norm_num [spx, Matrix.cons_val_zero, Matrix.head_cons]
  rw [hA, hdx, sqrt_half_mul_two]

theorem ssTransport_dot_ssEdgeVec_K2_10 :
    ssTransport spK2 spK2_isSymm spx ⬝ᵥ ssEdgeVec spK2 spK2_isSymm 1 0
      = -(Real.sqrt 2) := by
  rw [ssEdgeVec_swap]
  rw [Matrix.dotProduct_neg, ssTransport_dot_ssEdgeVec_K2_01]

/-- **The second route**: `qF(S) c = 8` through the sampled operator's
own definition with the claim-A dot values — independent of the
correspondence theorem. -/
theorem quadForm_ssSampled_ssTransport_K2 :
    quadForm (ssSampled spK2 spK2_isSymm 1 (fun _ => true))
        (ssTransport spK2 spK2_isSymm spx) = 8 := by
  rw [ssSampled, quadForm_finset_sum, Fintype.sum_prod_type]
  have hloop : ∀ u : Fin 2,
      quadForm ((ssWeight spK2 spK2_isSymm 1 (u, u) (fun _ => true))
        • rankOne (ssEdgeVec spK2 spK2_isSymm u u))
        (ssTransport spK2 spK2_isSymm spx) = 0 := by
    intro u
    rw [ssEdgeVec_self]
    simp only [rankOne_zero_eq, smul_zero]
    simp [quadForm]
  have t01 : quadForm ((ssWeight spK2 spK2_isSymm 1 ((0, 1) : Fin 2 × Fin 2)
        (fun _ => true)) • rankOne (ssEdgeVec spK2 spK2_isSymm 0 1))
        (ssTransport spK2 spK2_isSymm spx) = 4 := by
    rw [quadForm_smul, rankOne_quadForm, ssWeight_K2_01,
      ssTransport_dot_ssEdgeVec_K2_01]
    have hs : (Real.sqrt 2) * (Real.sqrt 2) = 2 := by
      exact Real.mul_self_sqrt (by norm_num)
    rw [sq, hs]
    norm_num
  have t10 : quadForm ((ssWeight spK2 spK2_isSymm 1 ((1, 0) : Fin 2 × Fin 2)
        (fun _ => true)) • rankOne (ssEdgeVec spK2 spK2_isSymm 1 0))
        (ssTransport spK2 spK2_isSymm spx) = 4 := by
    rw [quadForm_smul, rankOne_quadForm, ssWeight_K2_10,
      ssTransport_dot_ssEdgeVec_K2_10]
    have hs : (-(Real.sqrt 2)) * (-(Real.sqrt 2)) = 2 := by
      rw [neg_mul_neg]
      exact Real.mul_self_sqrt (by norm_num)
    rw [sq, hs]
    norm_num
  simp only [Fin.sum_univ_two, hloop, t01, t10]
  norm_num

/-- **The tight `ε = 1` graph instance**: the raw pins give
`xᵀL̃x = 8 = (1+1)·4 = (1+ε)xᵀLx` attained with equality — a pure-data
join falsifying wrong constants in either definition. -/
theorem graph_bounds_tight_K2 :
    (1 - (1 : ℝ)) * quadForm (laplacian spK2) spx
        ≤ quadForm (ssLaplacian spK2 spK2_isSymm 1 (fun _ => true)) spx
    ∧ quadForm (ssLaplacian spK2 spK2_isSymm 1 (fun _ => true)) spx
      ≤ (1 + (1 : ℝ)) * quadForm (laplacian spK2) spx := by
  rw [quadForm_ssLaplacian_K2, quadForm_laplacian_K2]
  norm_num

/-- **The failure event is real** at `ε = 1/2`: `8 > (3/2)·4 = 6`. -/
theorem graph_event_nonempty_K2 :
    (fun _ => true) ∈ {ω : (Fin 2 × Fin 2) → Bool |
      ∃ x : Fin 2 → ℝ, (1 - 1 / 2) * quadForm (laplacian spK2) x
          > quadForm (ssLaplacian spK2 spK2_isSymm 1 ω) x ∨
        quadForm (ssLaplacian spK2 spK2_isSymm 1 ω) x
          > (1 + 1 / 2) * quadForm (laplacian spK2) x} := by
  simp only [Set.mem_setOf_eq]
  refine ⟨spx, Or.inr ?_⟩
  rw [quadForm_ssLaplacian_K2, quadForm_laplacian_K2]
  norm_num

/-- **The graph tail instantiated at `K₂`** (interface pin). -/
theorem graph_tail_K2 :
    ssMeasure spK2 spK2_isSymm 1 (by norm_num : (0 : ℝ) ≤ 1)
        {ω : (Fin 2 × Fin 2) → Bool |
          ∃ x : Fin 2 → ℝ, (1 - 1 / 2) * quadForm (laplacian spK2) x
              > quadForm (ssLaplacian spK2 spK2_isSymm 1 ω) x ∨
            quadForm (ssLaplacian spK2 spK2_isSymm 1 ω) x
              > (1 + 1 / 2) * quadForm (laplacian spK2) x}
      ≤ ENNReal.ofReal (2 * ((Fintype.card (Fin 2) : ℝ))
        * Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 / 1 + 2 * (1 / 2) / (3 * 1)))) :=
  sparsification_graph_tail spK2 spK2_isSymm spK2_nonneg 1 one_pos
    (1 / 2) (by norm_num)

/-- **The graph budget instantiated at `K₂`** (interface pin, `ε = δ = 1/2`,
`q = 100`; the budget hypothesis discharged by `log 8 ≤ 300/32`). -/
theorem graph_budget_K2 :
    ssMeasure spK2 spK2_isSymm 100 (by norm_num : (0 : ℝ) ≤ 100)
        {ω : (Fin 2 × Fin 2) → Bool |
          ∃ x : Fin 2 → ℝ, (1 - 1 / 2) * quadForm (laplacian spK2) x
              > quadForm (ssLaplacian spK2 spK2_isSymm 100 ω) x ∨
            quadForm (ssLaplacian spK2 spK2_isSymm 100 ω) x
              > (1 + 1 / 2) * quadForm (laplacian spK2) x}
      ≤ ENNReal.ofReal (1 / 2) := by
  have hlog8 : Real.log (8 : ℝ) ≤ 300 / 32 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (8 : ℝ) = 224 / 32 + 1 := by norm_num
      _ ≤ Real.exp (224 / 32) := Real.add_one_le_exp _
      _ ≤ Real.exp (300 / 32) := Real.exp_le_exp.mpr (by norm_num)
  have hbudget : (8 / 3) * Real.log (2 * ((Fintype.card (Fin 2) : ℝ)) / (1 / 2))
        / (1 / 2) ^ 2 ≤ 100 := by
    have hcard : ((Fintype.card (Fin 2) : ℝ)) = 2 := by simp
    rw [hcard]
    have h8 : (2 : ℝ) * 2 / (1 / 2) = 8 := by norm_num
    rw [h8]
    have hnorm : (8 / 3 : ℝ) * Real.log 8 / (1 / 2) ^ 2
        = (32 / 3) * Real.log 8 := by
      field_simp
      ring
    rw [hnorm]
    linarith [hlog8]
  exact sparsification_graph_budget spK2 spK2_isSymm spK2_nonneg
    (1 / 2) (by norm_num) (by norm_num) (1 / 2) (by norm_num) 100
    (by norm_num : (0 : ℝ) < 100) hbudget

/-! ## The signed fixture and the fences -/

open MeasureTheory ProbabilityTheory SpectralGraphTheory
open scoped BigOperators Matrix Matrix.L2OpNorm

/-- The signed fixture: `A₀₁ = A₁₂ = −2`, `A₀₂ = 1`, so
`L = −(1,−2,1)(1,−2,1)ᵀ` — a signed Laplacian with a two-dimensional
kernel (containing non-constant vectors) and eigenvalue `−6`. -/
def sg : Matrix (Fin 3) (Fin 3) ℝ := !![0, -2, 1; -2, 0, -2; 1, -2, 0]

theorem sg_isSymm : sg.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [sg]

theorem sg_laplacian :
    laplacian sg = -(rankOne ![1, -2, 1]) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, degreeMatrix, deg, sg, rankOne, Fin.sum_univ_three] <;>
    norm_num

theorem quadForm_neg {W : Type} [Fintype W] (M : Matrix W W ℝ) (x : W → ℝ) :
    quadForm (-M) x = -quadForm M x := by
  simp only [quadForm, Matrix.neg_mulVec, Matrix.dotProduct_neg]

theorem sg_quadForm_nonpos (y : Fin 3 → ℝ) :
    quadForm (laplacian sg) y ≤ 0 := by
  rw [sg_laplacian, quadForm_neg, rankOne_quadForm]
  have hs : 0 ≤ (y ⬝ᵥ (![1, -2, 1] : Fin 3 → ℝ)) ^ 2 := sq_nonneg _
  nlinarith [hs]

theorem sg_eigval_nonpos (k : Fin 3) :
    eigvalOf (laplacian sg) (laplacian_symmetric sg sg_isSymm) k ≤ 0 := by
  rw [← quadForm_eigvecOf_self (laplacian_symmetric sg sg_isSymm) k]
  exact sg_quadForm_nonpos _

/-- **The transport is junk-zero at the signed fixture** — every
eigenvalue is nonpositive, so `√λ_k = 0` for every `k`. -/
theorem sg_ssTransport_zero (x : Fin 3 → ℝ) :
    ssTransport sg sg_isSymm x = 0 := by
  funext k
  simp only [ssTransport, Pi.zero_apply,
    Real.sqrt_eq_zero_of_nonpos (sg_eigval_nonpos k), zero_mul]

/-- **The isometry fence**: without nonnegativity the transport isometry
fails — `xᵀLx = −36 < 0 = ‖c(x)‖²` at `x = (1,−2,1)`. -/
theorem sg_iso_fence :
    ¬ (quadForm (laplacian sg) ![1, -2, 1]
        = ssTransport sg sg_isSymm ![1, -2, 1]
          ⬝ᵥ ssTransport sg sg_isSymm ![1, -2, 1]) := by
  rw [sg_ssTransport_zero, Matrix.dotProduct_zero]
  have hq : quadForm (laplacian sg) ![1, -2, 1] = -36 := by
    rw [sg_laplacian, quadForm_neg, rankOne_quadForm]
    have hd : (![1, -2, 1] : Fin 3 → ℝ) ⬝ᵥ (![1, -2, 1] : Fin 3 → ℝ) = 6 := by
      simp [Matrix.dotProduct, Fin.sum_univ_three]
      norm_num
    rw [hd]
    norm_num
  rw [hq]
  norm_num

/-- **The claim-A fence**: without nonnegativity the transport–edge-vector
identity fails at the positive pair `(0, 2)` — the transport is junk-zero
while `√(A₀₂/2)·(x₀ − x₂) = √(1/2) ≠ 0`. -/
theorem sg_claimA_fence :
    ¬ (ssTransport sg sg_isSymm (![1, 0, 0] : Fin 3 → ℝ)
          ⬝ᵥ ssEdgeVec sg sg_isSymm 0 2
        = Real.sqrt (sg 0 2 / 2)
          * ((![1, 0, 0] : Fin 3 → ℝ) 0 - (![1, 0, 0] : Fin 3 → ℝ) 2)) := by
  rw [sg_ssTransport_zero, Matrix.zero_dotProduct]
  intro h
  have hpos : (0 : ℝ) < sg 0 2 := by
    simp [sg, Matrix.cons_val_zero, Matrix.head_cons]
  have h2 : (0 : ℝ) < Real.sqrt (sg 0 2 / 2) :=
    Real.sqrt_pos_of_pos (by positivity)
  have hev : (![1, 0, 0] : Fin 3 → ℝ) 0 - (![1, 0, 0] : Fin 3 → ℝ) 2 = 1 := by
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hev, mul_one] at h
  linarith

/-! ## The closed-form sampling budget (Track A, 2026-08-31)

`proposals/spectral-graph-sparsification-gnn-training.md`: the budget
corollaries take `q` as a hypothesis; `sparsificationBudget` *outputs*
the minimal natural `q`. The pins below fix the formula's value at
exact-`e` designs (where `log` collapses through `Real.log_exp`), prove
the `max 1` floor load-bearing at a sub-unit `2n/δ` (the ceiling alone
would be `0`, killing the `0 < q` clause), pin minimality at the same
design through `sparsificationBudget_min` itself, and join the closed
form to this file's own hand-chosen `q = 100` — plus the interface
instance of the plug-in theorem at `K₂`. All of the pins are
axiom-free (standard three); the interface instance honestly carries
`matrix_bernstein` with the theorem it applies. -/

/-- The exact-`e` design: at `n = 3`, `δ = 6/e`, `ε = 1/√3` the budget
formula evaluates to exactly `8` (`2n/δ = e` so `log = 1`, `ε² = 1/3`)
— a wrong `8/3`, a wrong `2n` factor, or a wrong ceiling breaks the
value. -/
theorem budget_e_design_QA :
    sparsificationBudget 3 (1 / Real.sqrt 3) (6 / Real.exp 1) = 8 := by
  have hε2 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hr : (2 : ℝ) * ((3 : ℕ) : ℝ) / (6 / Real.exp 1) = Real.exp 1 := by
    field_simp
    ring
  unfold sparsificationBudget
  rw [hr, Real.log_exp, hε2]
  have hval : (8 / 3 : ℝ) * 1 / (1 / 3) = 8 := by norm_num
  rw [hval, Nat.ceil_ofNat]
  norm_num

/-- A second exact-`e` design, scaling check: at `n = 1`, `δ = 2/e³`,
`ε = 1/√3` the budget is exactly `24` (`2n/δ = e³` so `log = 3`) — the
formula tracks the log argument, not a constant. -/
theorem budget_exp3_design_QA :
    sparsificationBudget 1 (1 / Real.sqrt 3) (2 / Real.exp 3) = 24 := by
  have hε2 : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hr : (2 : ℝ) * ((1 : ℕ) : ℝ) / (2 / Real.exp 3) = Real.exp 3 := by
    field_simp
  unfold sparsificationBudget
  rw [hr, Real.log_exp, hε2]
  have hval : (8 / 3 : ℝ) * 3 / (1 / 3) = 24 := by norm_num
  rw [hval, Nat.ceil_ofNat]
  norm_num

/-- The `max 1` floor is load-bearing: at `n = 1`, `ε = 1/2`, `δ = 10`
the ratio `2n/δ = 1/5 ≤ 1` has nonpositive log, so the ceiling alone is
`0` and only the floor keeps the `0 < q` clause every budget theorem
needs. -/
theorem budget_floor_QA : sparsificationBudget 1 (1 / 2) 10 = 1 := by
  have hlog : Real.log ((2 : ℝ) * ((1 : ℕ) : ℝ) / 10) ≤ 0 :=
    Real.log_nonpos (by norm_num) (by norm_num)
  have hq2 : (0 : ℝ) < (1 / 2) ^ 2 := by norm_num
  have hB : (8 / 3 : ℝ) * Real.log ((2 : ℝ) * ((1 : ℕ) : ℝ) / 10)
      / (1 / 2) ^ 2 ≤ 0 := by
    rw [div_le_iff₀ hq2, zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hlog
  unfold sparsificationBudget
  rw [Nat.ceil_eq_zero.2 hB]
  norm_num

/-- Minimality pinned at the exact-`e` design: the budget inequality
fails at `q = 7`, so — through `sparsificationBudget_min` — the closed
form's output `8` is the true minimum among naturals, not merely a
valid choice. -/
theorem budget_minimal_e_design_QA :
    ¬ ((8 / 3 : ℝ) * Real.log (2 * ((3 : ℕ) : ℝ) / (6 / Real.exp 1))
        / (1 / Real.sqrt 3) ^ 2 ≤ 7) := by
  intro h
  have h8 := sparsificationBudget_min (n := 3) (1 / Real.sqrt 3)
    (6 / Real.exp 1) (by norm_num : (0 : ℕ) < 7) h
  rw [budget_e_design_QA] at h8
  omega

/-- The closed form joined to this file's own hand budget: for the
`K₂` parameters (`n = 2`, `ε = δ = 1/2`) the certified minimal budget
is at most the `q = 100` the `budget_tail_K2` pin hand-discharged above
(same `log 8 ≤ 300/32` route) — the closed form certifies the hand
choice after the fact. -/
theorem budget_closedForm_le_hand_QA :
    sparsificationBudget 2 (1 / 2) (1 / 2) ≤ 100 := by
  have hlog8 : Real.log (8 : ℝ) ≤ 300 / 32 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    calc (8 : ℝ) = 224 / 32 + 1 := by norm_num
      _ ≤ Real.exp (224 / 32) := Real.add_one_le_exp _
      _ ≤ Real.exp (300 / 32) := Real.exp_le_exp.mpr (by norm_num)
  refine max_le (by omega) (Nat.ceil_le.2 ?_)
  have hcard : (2 : ℝ) * ((2 : ℕ) : ℝ) = 4 := by norm_num
  rw [hcard]
  have hr : (4 : ℝ) / (1 / 2) = 8 := by norm_num
  rw [hr]
  have hnorm : (8 / 3 : ℝ) * Real.log 8 / (1 / 2) ^ 2
      = (32 / 3) * Real.log 8 := by
    field_simp
    ring
  rw [hnorm]
  have htop : (32 / 3 : ℝ) * (300 / 32) = 100 := by norm_num
  calc (32 / 3 : ℝ) * Real.log 8
      ≤ (32 / 3) * (300 / 32) :=
        mul_le_mul_of_nonneg_left hlog8 (by norm_num)
    _ = 100 := htop

/-- Interface pin: the plug-in theorem applies at the `K₂` fixture with
only `(ε, δ)` supplied — the budget hypothesis is discharged by the
closed form itself. CONDITIONAL ON `matrix_bernstein` (via
`sparsification_graph_budget`), reported honestly by
`#print axioms`. -/
theorem budget_closedForm_K2 :
    ssMeasure spK2 spK2_isSymm
        ((sparsificationBudget (Fintype.card (Fin 2)) (1 / 2) (1 / 2) : ℝ))
        (Nat.cast_pos.2
          (sparsificationBudget_pos (Fintype.card (Fin 2)) (1 / 2) (1 / 2))).le
        {ω | ∃ x : Fin 2 → ℝ, (1 - 1 / 2) * quadForm (laplacian spK2) x
            > quadForm (ssLaplacian spK2 spK2_isSymm
                ((sparsificationBudget (Fintype.card (Fin 2))
                  (1 / 2) (1 / 2) : ℝ)) ω) x ∨
          quadForm (ssLaplacian spK2 spK2_isSymm
                ((sparsificationBudget (Fintype.card (Fin 2))
                  (1 / 2) (1 / 2) : ℝ)) ω) x
            > (1 + 1 / 2) * quadForm (laplacian spK2) x}
      ≤ ENNReal.ofReal (1 / 2) :=
  sparsification_graph_budget_closedForm spK2 spK2_isSymm spK2_nonneg
    (1 / 2) (by norm_num) (by norm_num) (1 / 2) (by norm_num)

end SparsificationTailQA
