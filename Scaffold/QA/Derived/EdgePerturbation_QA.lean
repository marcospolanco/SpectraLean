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
    negative weight, where the naive expectation (PSD edge blocks) fails.
-/

import Scaffold.Derived.EdgePerturbationTail

open MeasureTheory ProbabilityTheory SpectralGraphTheory
open Scaffold.Derived.EdgePerturbationTail
open Scaffold.Mathlib.Probability.BernoulliProduct
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

end Scaffold.QA.Derived.EdgePerturbation
