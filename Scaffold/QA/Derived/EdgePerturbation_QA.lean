/-
  EdgePerturbation_QA.lean

  Purpose
  -------
  QA for the centered Bernoulli edge-perturbation tail
  (`Scaffold/Derived/EdgePerturbationTail.lean`, the `matrix_hoeffding`
  consumer of `proposals/matrix-hoeffding-spectral-gap-estimation.md`).

  The tail theorems are conditional on the `matrix_hoeffding` axiom; these
  lemmas do not prove that axiom. What they pin, on the `K₂` fixture:

  - the variance statistic exactly: `∑_e L_e² = 4 • (e₀−e₁)(e₀−e₁)ᵀ` and
    `‖∑_e L_e²‖ = 8`, both sides by independent routes (the rank-one norm
    pin `‖(e₀−e₁)(e₀−e₁)ᵀ‖ = 2` is proved two-sided through the action
    bound, not assumed);
  - the design's arithmetic at a concrete outcome: the all-true outcome at
    `p ≡ ½` sums to exactly the unit edge Laplacian, whose quadratic form
    at `e₀` is `1`;
  - the tail instance in closed form (`4 exp(−1/16)`);
  - the degenerate zero-weight graph: the tail event is empty at `t > 0`;
  - the load-bearing interval fence: at `p ≡ 2` (outside `[0, 1]`) the
    semidefinite bound clause is *refuted* — the design's only hypothesis
    is not decorative;
  - the sign-free witness: the semidefinite clause holds verbatim at a
    negative weight, where the naive expectation (PSD edge blocks) fails;
  - the concentration → subspace-stability pipeline's QA (the drift
    section): the packaging identity pinned by two independent routes on
    `K₂` (raw weight-space arithmetic vs the design's own Laplacian-space
    pin — a wrong `laplacian_sum`/`laplacian_smul` breaks exactly one),
    the variance statistic on the three-path (`∑ₑ L_e² = 4 • L(P₃)`,
    `‖·‖ = 12`, through the rank-one squares and the pinned `λ₃ = 3`), the
    per-outcome stack (every edge survives at `p ≡ ¼` — same support graph
    in every outcome), and the closed-form Fiedler-line drift instance
    `μ {‖rotation‖ ≥ 1} ≤ 6 exp(−1/24)`. The drift instance is
    conditional on the `matrix_hoeffding` axiom via the drift theorem,
    not a proof of it.
-/

import Scaffold.Derived.EdgePerturbationTail
import Scaffold.Derived.EdgePerturbationDrift
import Scaffold.QA.SpectralGraph.Fiedler_QA

open MeasureTheory ProbabilityTheory SpectralGraphTheory
open SpectralGraphTheory.QA
open Scaffold.Derived.EdgePerturbationTail
open Scaffold.Derived.EdgePerturbationDrift
open Scaffold.Mathlib.Probability.BernoulliProduct
open Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent
open Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.QA.Derived.EdgePerturbation

/-! ## The `K₂` fixture -/

/-- The unit edge `K₂`. -/
def epK2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = j then 0 else 1

/-- The uniform-half inclusion probabilities. -/
noncomputable def epHalf : (Fin 2 × Fin 2) → ℝ := fun _ => 1 / 2

theorem epHalf_mem (e) : 0 ≤ epHalf e ∧ epHalf e ≤ 1 := by
  constructor <;> norm_num [epHalf]

theorem epHalf_nonneg : ∀ e, 0 ≤ epHalf e := fun e => (epHalf_mem e).1

theorem epHalf_le_one : ∀ e, epHalf e ≤ 1 := fun e => (epHalf_mem e).2

/-- The K₂ edge vector `v = e₀ − e₁`. -/
def epVec : Fin 2 → ℝ := ![1, -1]

/-! ## The variance statistic, pinned -/

/-- The K₂ edge blocks: `(0,0)` and `(1,1)` have weight `0` (zero blocks);
the two off-diagonal ordered pairs have the same rank-one Laplacian. -/
theorem perturbEdgeLap_epK2_facts :
    perturbEdgeLap epK2 (0, 0) = 0
      ∧ perturbEdgeLap epK2 (1, 1) = 0
      ∧ perturbEdgeLap epK2 (0, 1) = rankOne epVec
      ∧ perturbEdgeLap epK2 (1, 0) = rankOne epVec := by
  have hv01 : (Pi.single 0 1 - Pi.single 1 1 : Fin 2 → ℝ) = epVec := by
    funext i
    fin_cases i <;> simp [epVec]
  have hv10 : (Pi.single 1 1 - Pi.single 0 1 : Fin 2 → ℝ) = -epVec := by
    funext i
    fin_cases i <;> simp [epVec]
  have hw01 : epK2 0 1 = 1 := by simp [epK2]
  have hw10 : epK2 1 0 = 1 := by simp [epK2]
  have hw00 : epK2 0 0 = 0 := by simp [epK2]
  have hw11 : epK2 1 1 = 0 := by simp [epK2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [perturbEdgeLap]
    rw [hw00, zero_smul]
  · simp only [perturbEdgeLap]
    rw [hw11, zero_smul]
  · simp only [perturbEdgeLap]
    rw [hw01, hv01, one_smul]
  · simp only [perturbEdgeLap]
    rw [hw10, hv10, rankOne_neg, one_smul]

/-- **The variance statistic of the design on `K₂`, exactly**: the summed
edge-block squares are `4 • v vᵀ` (two ordered pairs, each squaring to
`2 • v vᵀ` at `v ⬝ᵥ v = 2`). -/
theorem epK2_variance_sum :
    ∑ e : Fin 2 × Fin 2, perturbEdgeLap epK2 e * perturbEdgeLap epK2 e
      = (4 : ℝ) • rankOne epVec := by
  obtain ⟨h00, h11, h01, h10⟩ := perturbEdgeLap_epK2_facts
  have hsq01 : perturbEdgeLap epK2 (0, 1) * perturbEdgeLap epK2 (0, 1)
      = (2 : ℝ) • rankOne epVec := by
    rw [h01, rankOne_mul_self]
    have hvv : epVec ⬝ᵥ epVec = 2 := by
      simp [Matrix.dotProduct, epVec]
      norm_num
    rw [hvv]
  have hsq10 : perturbEdgeLap epK2 (1, 0) * perturbEdgeLap epK2 (1, 0)
      = (2 : ℝ) • rankOne epVec := by
    rw [h10, rankOne_mul_self]
    have hvv : epVec ⬝ᵥ epVec = 2 := by
      simp [Matrix.dotProduct, epVec]
      norm_num
    rw [hvv]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have h00' : perturbEdgeLap epK2 (0, 0) * perturbEdgeLap epK2 (0, 0) = 0 := by
    rw [h00, zero_mul]
  have h11' : perturbEdgeLap epK2 (1, 1) * perturbEdgeLap epK2 (1, 1) = 0 := by
    rw [h11, zero_mul]
  simp only [h00', h11', hsq01, hsq10]
  module

/-- The rank-one norm pin, two-sided: `‖v vᵀ‖ = v ⬝ᵥ v = 2` at
`v = e₀ − e₁`. The upper side is `l2OpNorm_rankOne_le`; the lower side is
the action bound `l2OpNorm_mulVec_le` at `v` itself, where
`v vᵀ *ᵥ v = (v ⬝ᵥ v) • v = 2 • v`. -/
theorem epK2_rankOne_norm : ‖rankOne epVec‖ = 2 := by
  have hvv : epVec ⬝ᵥ epVec = 2 := by
    simp [Matrix.dotProduct, epVec]
    norm_num
  refine le_antisymm ?_ ?_
  · have h := l2OpNorm_rankOne_le epVec
    rw [hvv] at h
    exact h
  · have hact := l2OpNorm_mulVec_dotProduct_le (rankOne epVec) epVec
    rw [rankOne_mulVec, hvv] at hact
    have hlhs : ((2 : ℝ) • epVec) ⬝ᵥ ((2 : ℝ) • epVec) = 8 := by
      simp only [Matrix.dotProduct, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_two,
        epVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      norm_num
    rw [hlhs] at hact
    have hnn : 0 ≤ ‖rankOne epVec‖ := norm_nonneg _
    have hfac : (‖rankOne epVec‖ - 2) * (‖rankOne epVec‖ + 2)
        = ‖rankOne epVec‖ * ‖rankOne epVec‖ - 4 := by ring
    nlinarith [hact, hnn, hfac]

/-- **The variance norm pin**: `‖∑_e L_e²‖ = 8` on `K₂`. -/
theorem epK2_variance_norm :
    ‖∑ e : Fin 2 × Fin 2, perturbEdgeLap epK2 e * perturbEdgeLap epK2 e‖ = 8 := by
  rw [epK2_variance_sum, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num),
    epK2_rankOne_norm]
  norm_num

/-! ## The design's arithmetic at a concrete outcome -/

/-- At the all-true outcome and uniform-half probabilities, the centered
sum is exactly the unit edge Laplacian (each off-diagonal ordered pair
contributes `(1 − ½) • v vᵀ`, the zero-weight pairs nothing). -/
theorem epK2_perturbSum_allTrue :
    ∑ e : Fin 2 × Fin 2, perturbSummand epK2 epHalf e (fun _ => true)
      = rankOne epVec := by
  have hv01 : (Pi.single 0 1 - Pi.single 1 1 : Fin 2 → ℝ) = epVec := by
    funext i; fin_cases i <;> simp [epVec]
  have hv10 : (Pi.single 1 1 - Pi.single 0 1 : Fin 2 → ℝ) = -epVec := by
    funext i; fin_cases i <;> simp [epVec]
  have hev : ∀ i j : Fin 2,
      perturbSummand epK2 epHalf (i, j) (fun _ => true)
        = (if (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) then (1 : ℝ) / 2 else 0)
          • rankOne epVec := by
    intro i j
    rw [perturbSummand, perturbEdgeLap, epHalf]
    fin_cases i <;> fin_cases j <;>
      simp [epK2, epHalf, hv01, hv10, rankOne_neg, one_smul] <;>
      try (congr 1; norm_num)
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, hev]
  norm_num
  rw [← add_smul, show ((1 : ℝ) / 2) + ((1 : ℝ) / 2) = 1 from by norm_num,
    one_smul]

/-! ## The tail instance in closed form -/

/-- **The quadratic-form tail on `K₂` at `p ≡ ½`, `t = 1`, `x = e₀`, in
closed form**: `μ {1 · 1 ≤ |xᵀ S(ω) x|} ≤ 4 exp(−1/16)` — the dimension
factor `2 · 2`, the variance `8` in the exponent's denominator `2 · 8`.
Assembled from the pinned variance norm (`epK2_variance_norm`). CONDITIONAL ON
THE `matrix_hoeffding` AXIOM (instantiated, not re-proved). -/
theorem epK2_quadForm_tail_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool |
          (1 : ℝ) * (![1, 0] : Fin 2 → ℝ) ⬝ᵥ ![1, 0]
            ≤ |quadForm (∑ e : Fin 2 × Fin 2, perturbSummand epK2 epHalf e ω)
                ![1, 0]|}
      ≤ ENNReal.ofReal (4 * Real.exp (-((1 : ℝ) ^ 2) / 16)) := by
  have htail := edgePerturbation_quadForm_tail epK2 epHalf epHalf_nonneg
    epHalf_le_one 1 zero_le_one ![1, 0] (by
      intro h
      have h0 := congrFun h 0
      norm_num at h0)
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((1 : ℝ) ^ 2) / 16) := by
    ring
  rw [show (4 : ℝ) * Real.exp (-((1 : ℝ) ^ 2) / 16)
      = 2 * 2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * 8)) from hRHS.symm]
  exact htail

/-! ## The degenerate zero-weight graph -/

/-- On the zero-weight graph every edge block vanishes, so the tail event
is empty at `t > 0` — the bound holds with measure exactly `0`. -/
theorem epZero_event_empty_QA {x : Fin 2 → ℝ} (hx : x ≠ 0) {t : ℝ} (ht : 0 < t) :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool |
          t * (x ⬝ᵥ x) ≤ |quadForm (∑ e : Fin 2 × Fin 2,
            perturbSummand 0 epHalf e ω) x|} = 0 := by
  have hzero : ∀ (e : Fin 2 × Fin 2) (ω : (Fin 2 × Fin 2) → Bool),
      perturbSummand (0 : Matrix (Fin 2) (Fin 2) ℝ) epHalf e ω
        = (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
    intro e ω
    simp [perturbSummand, perturbEdgeLap, zero_smul]
  have hsum : ∀ ω : (Fin 2 × Fin 2) → Bool,
      ∑ e : Fin 2 × Fin 2, perturbSummand (0 : Matrix (Fin 2) (Fin 2) ℝ)
        epHalf e ω = 0 := by
    intro ω
    simp [hzero]
  have hempty : {ω : (Fin 2 × Fin 2) → Bool |
      t * (x ⬝ᵥ x) ≤ |quadForm (∑ e : Fin 2 × Fin 2,
        perturbSummand (0 : Matrix (Fin 2) (Fin 2) ℝ) epHalf e ω) x|} = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    have hCx : 0 < x ⬝ᵥ x := dotProduct_self_pos_of_ne_zero hx
    have h1 : quadForm (∑ e : Fin 2 × Fin 2,
        perturbSummand (0 : Matrix (Fin 2) (Fin 2) ℝ) epHalf e ω) x = 0 := by
      rw [hsum ω]
      simp [quadForm]
    rw [h1, abs_zero]
    exact iff_of_false (not_le.2 (mul_pos ht hCx)) (fun h => h)
  rw [hempty, measure_empty]

/-! ## The load-bearing interval fence -/

/-- The all-false outcome's centered coefficient at `p e = 2` is `-2`, so
`X_e² = 4 • L_e²` exceeds the bound `L_e²` (the difference evaluates to
`-6 • v vᵀ`, whose quadratic form at `v` is `-24`): the semidefinite
clause *fails* — `p ∈ [0, 1]` is load-bearing, not decorative. -/
theorem epK2_interval_fence_QA :
    ¬ (perturbEdgeLap epK2 (0, 1) * perturbEdgeLap epK2 (0, 1)
      - perturbSummand epK2 (fun _ => (2 : ℝ)) (0, 1) (fun _ => false)
        * perturbSummand epK2 (fun _ => (2 : ℝ)) (0, 1) (fun _ => false)).PosSemidef := by
  intro hpsd
  have hv := hpsd.2 epVec
  have h01 : perturbEdgeLap epK2 (0, 1) = rankOne epVec :=
    perturbEdgeLap_epK2_facts.2.2.1
  have hvv : epVec ⬝ᵥ epVec = 2 := by
    simp [Matrix.dotProduct, epVec]
    norm_num
  have hL : perturbEdgeLap epK2 (0, 1) * perturbEdgeLap epK2 (0, 1)
      = (2 : ℝ) • rankOne epVec := by
    rw [h01, rankOne_mul_self, hvv]
  have hs : perturbSummand epK2 (fun _ => (2 : ℝ)) (0, 1) (fun _ => false)
      = (-2 : ℝ) • rankOne epVec := by
    rw [perturbSummand, h01, if_neg (by decide)]
    congr 1
    ring
  have hprod : perturbSummand epK2 (fun _ => (2 : ℝ)) (0, 1) (fun _ => false)
        * perturbSummand epK2 (fun _ => (2 : ℝ)) (0, 1) (fun _ => false)
      = ((-2 : ℝ) * (-2)) • (rankOne epVec * rankOne epVec) := by
    rw [hs, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hfin : perturbEdgeLap epK2 (0, 1) * perturbEdgeLap epK2 (0, 1)
      - perturbSummand epK2 (fun _ => (2 : ℝ)) (0, 1) (fun _ => false)
        * perturbSummand epK2 (fun _ => (2 : ℝ)) (0, 1) (fun _ => false)
      = (-6 : ℝ) • rankOne epVec := by
    rw [hL, hprod, rankOne_mul_self, hvv, smul_smul, ← sub_smul]
    congr 1
    ring
  rw [hfin, Matrix.smul_mulVec_assoc, rankOne_mulVec, hvv, smul_smul] at hv
  have hv' : 0 ≤ epVec ⬝ᵥ (((-6 : ℝ) * 2) • epVec) := hv
  have hval : epVec ⬝ᵥ (((-6 : ℝ) * 2) • epVec) = -24 := by
    have hunfold : epVec ⬝ᵥ (((-6 : ℝ) * 2) • epVec)
        = ((-6 : ℝ) * 2) * (epVec ⬝ᵥ epVec) := by
      simp only [Matrix.dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring_nf
    rw [hunfold, hvv]
    ring
  rw [hval] at hv'
  linarith

/-! ## The sign-free witness -/

/-- The semidefinite clause holds verbatim at a *negative* weight: the
edge block `-1 • v vᵀ` is not positive semidefinite, but its square is —
the design genuinely needs no sign hypothesis on the weights. -/
theorem epNeg_clause_QA (ω : (Fin 2 × Fin 2) → Bool) :
    (perturbEdgeLap (Matrix.of fun i j => if (i, j) = (0, 1) ∨ (i, j) = (1, 0)
        then (-1 : ℝ) else 0) (0, 1)
      * perturbEdgeLap (Matrix.of fun i j => if (i, j) = (0, 1) ∨ (i, j) = (1, 0)
        then (-1 : ℝ) else 0) (0, 1)
      - perturbSummand (Matrix.of fun i j => if (i, j) = (0, 1) ∨ (i, j) = (1, 0)
        then (-1 : ℝ) else 0) epHalf (0, 1) ω
        * perturbSummand (Matrix.of fun i j => if (i, j) = (0, 1) ∨ (i, j) = (1, 0)
        then (-1 : ℝ) else 0) epHalf (0, 1) ω).PosSemidef :=
  perturbSummand_sq_le _ epHalf epHalf_nonneg epHalf_le_one (0, 1) ω

/-! ## The concentration → subspace-stability pipeline -/

/-! ## The K₂ packaging identity, two routes -/

/-- **Route A (raw weight-space):** at the all-true outcome and
uniform-half probabilities, the weight-space perturbation *is* `K₂`'s
adjacency — each off-diagonal ordered pair contributes
`(1 − ½) · 1`, nothing else. -/
theorem epK2_perturbWeight_allTrue :
    perturbWeight epK2 epHalf (fun _ => true) = epK2 := by
  have hfin2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k
    fin_cases k <;> simp
  have h01ne : (0 : Fin 2) ≠ 1 := by decide
  have h10ne : (1 : Fin 2) ≠ 0 := by decide
  ext i j
  rcases hfin2 i with rfl | rfl
  all_goals rcases hfin2 j with rfl | rfl
  all_goals first
    | (rw [perturbWeight_apply_diag]; simp [epK2, epHalf])
    | (rw [perturbWeight_apply_of_ne (hij := h01ne)];
        (simp [epK2, epHalf]; try norm_num))
    | (rw [perturbWeight_apply_of_ne (hij := h10ne)];
        (simp [epK2, epHalf]; try norm_num))

/-- **Route A (raw Laplacian):** the Laplacian of `K₂` is the rank-one
edge block, entrywise. -/
theorem epK2_lap_eq_rankOne : laplacian epK2 = rankOne epVec := by
  have hdeg : ∀ i : Fin 2, deg epK2 i = 1 := by
    intro i
    fin_cases i <;> simp [deg, epK2, Fin.sum_univ_two]
  have hfin2 : ∀ k : Fin 2, k = 0 ∨ k = 1 := by
    intro k
    fin_cases k <;> simp
  ext i j
  rcases hfin2 i with rfl | rfl
  all_goals rcases hfin2 j with rfl | rfl
  all_goals
    simp only [laplacian, Matrix.sub_apply, degreeMatrix, hdeg]
  all_goals simp [epK2, rankOne_apply, epVec]

/-- **The packaging identity's two routes agree at the fixture**: the
weight-space route (`perturbWeight` then `laplacian`, raw above) and
the design route (the identity theorem joined to the existing
Laplacian-space pin `epK2_perturbSum_allTrue`) both compute
`rankOne epVec`. A wrong `laplacian_sum`/`laplacian_smul`/edge-block
join breaks exactly one route. -/
theorem epK2_packaging_twoRoute_QA :
    laplacian (perturbWeight epK2 epHalf (fun _ => true)) = rankOne epVec := by
  rw [epK2_perturbWeight_allTrue, epK2_lap_eq_rankOne]

theorem epK2_packaging_designRoute_QA :
    laplacian (perturbWeight epK2 epHalf (fun _ => true))
      = ∑ e : Fin 2 × Fin 2, perturbSummand epK2 epHalf e (fun _ => true) :=
  laplacian_perturbWeight _ _ _

/-! ## The P₃ line-drift instance -/

/-- The uniform-quarter inclusion probabilities. -/
noncomputable def epQuarter : (Fin 3 × Fin 3) → ℝ := fun _ => 1 / 4

theorem epQuarter_nonneg : ∀ e, 0 ≤ epQuarter e := fun e => by
  norm_num [epQuarter]

theorem epQuarter_le_one : ∀ e, epQuarter e ≤ 1 := fun e => by
  norm_num [epQuarter]

/-- The two edge vectors of the path, in `Pi.single` spelling so the
`laplacian_edgeAdj` join is definitional. -/
def epV01 : Fin 3 → ℝ := Pi.single 0 1 - Pi.single 1 1
def epV12 : Fin 3 → ℝ := Pi.single 1 1 - Pi.single 2 1

theorem epV01_dot : epV01 ⬝ᵥ epV01 = 2 := by
  (simp [Matrix.dotProduct, epV01, Fin.sum_univ_three]; try norm_num)

theorem epV12_dot : epV12 ⬝ᵥ epV12 = 2 := by
  (simp [Matrix.dotProduct, epV12, Fin.sum_univ_three]; try norm_num)

theorem path3Adj_eq_edges :
    path3Adj = edgeAdj 0 1 1 + edgeAdj 1 2 1 := by
  have hfin3 : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by
    intro k
    fin_cases k <;> simp
  ext i j
  rcases hfin3 i with rfl | rfl | rfl
  all_goals rcases hfin3 j with rfl | rfl | rfl
  all_goals
    simp [path3Adj, edgeAdj_apply, Matrix.add_apply, Matrix.of_apply,
      Fin.val_two]

theorem lap_path3_eq_rankOne_sum :
    laplacian path3Adj = rankOne epV01 + rankOne epV12 := by
  rw [path3Adj_eq_edges, laplacian_add, laplacian_edgeAdj, laplacian_edgeAdj,
    one_smul, one_smul]
  simp only [epV01, epV12]

theorem epP3_edgeLap_facts :
    perturbEdgeLap path3Adj (0, 1) = rankOne epV01
      ∧ perturbEdgeLap path3Adj (1, 0) = rankOne epV01
      ∧ perturbEdgeLap path3Adj (1, 2) = rankOne epV12
      ∧ perturbEdgeLap path3Adj (2, 1) = rankOne epV12 := by
  have hw : path3Adj 0 1 = 1 ∧ path3Adj 1 0 = 1 ∧ path3Adj 1 2 = 1
      ∧ path3Adj 2 1 = 1 := by
    refine ⟨by simp [path3Adj], by simp [path3Adj], ?_, ?_⟩ <;>
      simp [path3Adj, Fin.val_two]
  obtain ⟨w01, w10, w12, w21⟩ := hw
  have hv10 : (Pi.single 1 1 - Pi.single 0 1 : Fin 3 → ℝ) = -epV01 := by
    funext x
    fin_cases x <;> simp [epV01, Pi.single_apply]
  have hv21 : (Pi.single 2 1 - Pi.single 1 1 : Fin 3 → ℝ) = -epV12 := by
    funext x
    fin_cases x <;> simp [epV12, Pi.single_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [perturbEdgeLap, w01, one_smul]
    simp only [epV01]
  · rw [perturbEdgeLap, w10, one_smul, hv10, rankOne_neg]
  · rw [perturbEdgeLap, w12, one_smul]
    simp only [epV12]
  · rw [perturbEdgeLap, w21, one_smul, hv21, rankOne_neg]

/-- The variance statistic on the path: the four edge pairs each
square to `2 • v vᵀ`, collecting to `4 • L(P₃)`. -/
theorem epP3_variance_sum :
    ∑ e : Fin 3 × Fin 3, perturbEdgeLap path3Adj e * perturbEdgeLap path3Adj e
      = (4 : ℝ) • laplacian path3Adj := by
  obtain ⟨h01, h10, h12, h21⟩ := epP3_edgeLap_facts
  have hp3 : ∀ e : Fin 3 × Fin 3,
      e = (0, 0) ∨ e = (0, 1) ∨ e = (0, 2) ∨ e = (1, 0) ∨ e = (1, 1)
        ∨ e = (1, 2) ∨ e = (2, 0) ∨ e = (2, 1) ∨ e = (2, 2) := by
    intro e
    rcases e with ⟨a, b⟩
    fin_cases a <;> fin_cases b <;> simp
  have hsq : ∀ e : Fin 3 × Fin 3,
      perturbEdgeLap path3Adj e * perturbEdgeLap path3Adj e
        = if e = (0, 1) ∨ e = (1, 0) then (2 : ℝ) • rankOne epV01
          else if e = (1, 2) ∨ e = (2, 1) then (2 : ℝ) • rankOne epV12
          else 0 := by
    intro e
    rcases hp3 e with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [if_neg (by decide : ¬(((0, 0) : Fin 3 × Fin 3) = (0, 1)
            ∨ ((0, 0) : Fin 3 × Fin 3) = (1, 0))),
        if_neg (by decide : ¬(((0, 0) : Fin 3 × Fin 3) = (1, 2)
            ∨ ((0, 0) : Fin 3 × Fin 3) = (2, 1)))]
      simp [perturbEdgeLap, path3Adj, Fin.val_two]
    · rw [if_pos (Or.inl rfl), h01, rankOne_mul_self, epV01_dot]
    · rw [if_neg (by decide : ¬(((0, 2) : Fin 3 × Fin 3) = (0, 1)
            ∨ ((0, 2) : Fin 3 × Fin 3) = (1, 0))),
        if_neg (by decide : ¬(((0, 2) : Fin 3 × Fin 3) = (1, 2)
            ∨ ((0, 2) : Fin 3 × Fin 3) = (2, 1)))]
      simp [perturbEdgeLap, path3Adj, Fin.val_two]
    · rw [if_pos (Or.inr rfl), h10, rankOne_mul_self, epV01_dot]
    · rw [if_neg (by decide : ¬(((1, 1) : Fin 3 × Fin 3) = (0, 1)
            ∨ ((1, 1) : Fin 3 × Fin 3) = (1, 0))),
        if_neg (by decide : ¬(((1, 1) : Fin 3 × Fin 3) = (1, 2)
            ∨ ((1, 1) : Fin 3 × Fin 3) = (2, 1)))]
      simp [perturbEdgeLap, path3Adj, Fin.val_two]
    · rw [if_neg (by decide : ¬(((1, 2) : Fin 3 × Fin 3) = (0, 1)
            ∨ ((1, 2) : Fin 3 × Fin 3) = (1, 0))),
        if_pos (Or.inl rfl), h12, rankOne_mul_self, epV12_dot]
    · rw [if_neg (by decide : ¬(((2, 0) : Fin 3 × Fin 3) = (0, 1)
            ∨ ((2, 0) : Fin 3 × Fin 3) = (1, 0))),
        if_neg (by decide : ¬(((2, 0) : Fin 3 × Fin 3) = (1, 2)
            ∨ ((2, 0) : Fin 3 × Fin 3) = (2, 1)))]
      simp [perturbEdgeLap, path3Adj, Fin.val_two]
    · rw [if_neg (by decide : ¬(((2, 1) : Fin 3 × Fin 3) = (0, 1)
            ∨ ((2, 1) : Fin 3 × Fin 3) = (1, 0))),
        if_pos (Or.inr rfl), h21, rankOne_mul_self, epV12_dot]
    · rw [if_neg (by decide : ¬(((2, 2) : Fin 3 × Fin 3) = (0, 1)
            ∨ ((2, 2) : Fin 3 × Fin 3) = (1, 0))),
        if_neg (by decide : ¬(((2, 2) : Fin 3 × Fin 3) = (1, 2)
            ∨ ((2, 2) : Fin 3 × Fin 3) = (2, 1)))]
      simp [perturbEdgeLap, path3Adj, Fin.val_two]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_three, hsq]
  simp (config := {decide := true})
  rw [lap_path3_eq_rankOne_sum]
  module

theorem epP3_lap_norm : ‖laplacian path3Adj‖ = 3 := by
  have h := l2OpNorm_eq_max_abs_evals
    (laplacian_symmetric path3Adj path3Adj_symmetric) (by norm_num)
  have h2 : (⟨Fintype.card (Fin 3) - 1, by simp⟩ :
      Fin (Fintype.card (Fin 3))) = ⟨2, by norm_num⟩ :=
    Fin.ext (by simp)
  rw [h2, path3_evals_zero_QA, path3_evals_two_eq_three_QA] at h
  simpa using h

theorem epP3_variance_norm :
    ‖∑ e : Fin 3 × Fin 3, perturbEdgeLap path3Adj e * perturbEdgeLap path3Adj e‖
      = 12 := by
  rw [epP3_variance_sum, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num), epP3_lap_norm]
  norm_num

/-! The perturbed-graph stack at every outcome -/

theorem epP3_perturbed_apply (ω : (Fin 3 × Fin 3) → Bool) (i j : Fin 3) :
    (path3Adj + perturbWeight path3Adj epQuarter ω) i j
      = path3Adj i j * ((1 / 2 : ℝ)
          + (if ω (i, j) then (1 : ℝ) else 0)
          + (if ω (j, i) then (1 : ℝ) else 0)) := by
  have hsymm : path3Adj j i = path3Adj i j := by
    simp only [path3Adj, Matrix.of_apply, or_comm]
  by_cases hij : i = j
  · subst hij
    have hd : path3Adj i i = 0 := by
      simp only [path3Adj, Matrix.of_apply]
      split
      · exfalso
        rename_i h
        omega
      · rfl
    simp only [Matrix.add_apply, perturbWeight_apply_diag, hd]
    simp
  · rw [Matrix.add_apply, perturbWeight_apply_of_ne (hij := hij), hsymm]
    simp only [epQuarter]
    ring

theorem epP3_factor_pos (ω : (Fin 3 × Fin 3) → Bool) (i j : Fin 3) :
    0 < (1 / 2 : ℝ)
      + (if ω (i, j) then (1 : ℝ) else 0)
      + (if ω (j, i) then (1 : ℝ) else 0) := by
  cases h1 : ω (i, j) <;> cases h2 : ω (j, i) <;> simp [h1, h2] <;> norm_num

theorem epP3_perturbed_nonneg (ω : (Fin 3 × Fin 3) → Bool) (i j : Fin 3) :
    0 ≤ (path3Adj + perturbWeight path3Adj epQuarter ω) i j := by
  rw [epP3_perturbed_apply]
  exact mul_nonneg (path3Adj_nonneg i j) (le_of_lt (epP3_factor_pos ω i j))

theorem epP3_supportGraph (ω : (Fin 3 × Fin 3) → Bool) :
    supportGraph (path3Adj + perturbWeight path3Adj epQuarter ω)
      (path3Adj_symmetric.add (perturbWeight_isSymm path3Adj epQuarter ω))
      = supportGraph path3Adj path3Adj_symmetric := by
  ext i j
  rw [supportGraph_adj, supportGraph_adj]
  constructor
  · rintro ⟨hij, hpos⟩
    refine ⟨hij, ?_⟩
    rw [epP3_perturbed_apply] at hpos
    by_contra hA
    push_neg at hA
    have hle : path3Adj i j * ((1 / 2 : ℝ)
        + (if ω (i, j) then (1 : ℝ) else 0)
        + (if ω (j, i) then (1 : ℝ) else 0))
        ≤ 0 * ((1 / 2 : ℝ)
          + (if ω (i, j) then (1 : ℝ) else 0)
          + (if ω (j, i) then (1 : ℝ) else 0)) :=
      mul_le_mul_of_nonneg_right hA (le_of_lt (epP3_factor_pos ω i j))
    linarith
  · rintro ⟨hij, hpos⟩
    exact ⟨hij, by
      rw [epP3_perturbed_apply]
      exact mul_pos hpos (epP3_factor_pos ω i j)⟩

theorem epP3_hgap : (1 : ℝ) + 1
      ≤ evals (laplacian_symmetric path3Adj path3Adj_symmetric) ⟨2, by norm_num⟩
      - evals (laplacian_symmetric path3Adj path3Adj_symmetric)
        ⟨1, by norm_num⟩ := by
  rw [path3_evals_two_eq_three_QA, path3_evals_one_eq_one_QA]
  norm_num

/-- **The Fiedler-line drift instance on the path, in closed form**: at
`p ≡ ¼` (every edge weight stays in `[1/2, 5/2]·(its base value) > 0`,
so every outcome keeps the path connected with the same support graph)
and `t = δ = 1` (the gap discharge `1 + 1 ≤ λ₃ − λ₂ = 3 − 1`), the
rotation of the Fiedler line under random edge resampling exceeds `1`
with probability at most `6 exp(−1/24)` — the dimension factor
`2 · 3`, the variance norm `12` in the exponent's denominator
`2 · 12`. CONDITIONAL ON THE `matrix_hoeffding` AXIOM (instantiated
via the drift theorem, not re-proved). -/
theorem epP3_fiedlerLine_drift_QA :
    (bernPMF epQuarter epQuarter_nonneg epQuarter_le_one).toMeasure
      {ω : (Fin 3 × Fin 3) → Bool |
        ‖(initialProjector (laplacian (path3Adj
              + perturbWeight path3Adj epQuarter ω))
            (laplacian_symmetric (path3Adj
              + perturbWeight path3Adj epQuarter ω)
              (path3Adj_symmetric.add
                (perturbWeight_isSymm path3Adj epQuarter ω))) ⟨1, by norm_num⟩
          - initialProjector (laplacian (path3Adj
              + perturbWeight path3Adj epQuarter ω))
            (laplacian_symmetric (path3Adj
              + perturbWeight path3Adj epQuarter ω)
              (path3Adj_symmetric.add
                (perturbWeight_isSymm path3Adj epQuarter ω)))
              ⟨0, by norm_num⟩)
        - (initialProjector (laplacian path3Adj)
            (laplacian_symmetric path3Adj path3Adj_symmetric)
            ⟨1, by norm_num⟩
          - initialProjector (laplacian path3Adj)
            (laplacian_symmetric path3Adj path3Adj_symmetric)
            ⟨0, by norm_num⟩)‖ ≥ (1 : ℝ) / 1}
      ≤ ENNReal.ofReal (6 * Real.exp (-((1 : ℝ)) / 24)) := by
  have h := edgePerturbation_fiedlerLine_drift path3Adj path3Adj_symmetric
    epQuarter epQuarter_nonneg epQuarter_le_one path3Adj_nonneg
    epP3_perturbed_nonneg path3_supportGraph_connected
    (fun ω => by rw [epP3_supportGraph ω]; exact path3_supportGraph_connected)
    (by simp) 1 one_pos 1 zero_le_one epP3_hgap
  rw [epP3_variance_norm] at h
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by norm_num
  rw [hcard] at h
  have hRHS : 2 * 3 * Real.exp (-((1 : ℝ) ^ 2) / (2 * 12))
      = 6 * Real.exp (-((1 : ℝ)) / 24) := by
    have h1 : -((1 : ℝ) ^ 2) / (2 * 12) = -((1 : ℝ)) / 24 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at h
  simpa using h

end Scaffold.QA.Derived.EdgePerturbation
