/-
  EdgePerturbationTail.lean

  Purpose
  -------
  `matrix_hoeffding`'s first theorem consumer: the centered Bernoulli
  edge-perturbation tail, assembled on the deterministic design of
  `GraphTheory/EdgePerturbation.lean`
  (`proposals/matrix-hoeffding-spectral-gap-estimation.md`, Step 1).

  - `matrix_hoeffding_quadForm`: the generic quadratic-form corollary of
    the repaired axiom — a fixed *nonzero* test vector's quadratic form
    of the random sum concentrates in the norm tail's bound (the
    `x = 0` degeneration is genuinely excluded: there every outcome
    satisfies `t · 0 ≤ |xᵀ 0 x|`, so the event is all of `Ω` and no
    exponential bound can hold).
  - `edgePerturbation_norm_tail`: the assembly at the design —
    `μ {‖∑_e (δ_e − p_e) • L_e‖ ≥ t} ≤ 2 d exp(−t²/(2 ‖∑_e L_e²‖))`,
    with the `Fin n` summand transport by `Fintype.equivFin` +
    `Equiv.sum_comp` (the sparsification assembly's Finding-B pattern).
  - `edgePerturbation_quadForm_tail`: the same bound for the failure of
    the additive quadratic-form approximation at a fixed nonzero vector.

  The two tail theorems are **conditional on the `matrix_hoeffding`
  axiom** (Tropp 2012, Theorem 1.4, as repaired 2026-08-28 with the
  `[Nonempty V]` guard) and must never be described as foundationally
  proved; `#print axioms` reports the dependency honestly. Every
  hypothesis clause of the axiom is discharged by a proved lemma in the
  engine module.

  QA: `Scaffold/QA/Derived/EdgePerturbation_QA.lean`.
-/

import Scaffold.Mathlib.GraphTheory.EdgePerturbation
import Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding

open MeasureTheory ProbabilityTheory
open SpectralGraphTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open Scaffold.Mathlib.Probability.Concentration.Matrix
open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Derived.EdgePerturbationTail

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ## The generic quadratic-form corollary -/

section QuadForm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- **The quadratic-form pullback of the matrix-Hoeffding tail**: for a
fixed nonzero test vector, `t (x ⬝ᵥ x) ≤ |xᵀ (∑ X i ω) x|` can only hold
where `t ≤ ‖∑ X i ω‖` (the norm→form domination
`abs_quadForm_le_of_l2OpNorm_le`, contraposed through measure
monotonicity). CONDITIONAL ON THE `matrix_hoeffding` AXIOM at exactly its
clause set. The nonzero guard is load-bearing: at `x = 0` the event is
all of `Ω` and the statement is false for large `t`. -/
theorem matrix_hoeffding_quadForm {n : ℕ} [Nonempty V]
    {X : Fin n → Ω → Matrix V V ℝ} {A : Fin n → Matrix V V ℝ}
    (h_meas : ∀ i, StronglyMeasurable (X i))
    (h_indep : ∀ i j, i ≠ j → IndepFun (X i) (X j) μ)
    (h_herm : ∀ i ω, (X i ω).IsHermitian)
    (h_bound : ∀ i ω, Matrix.PosSemidef (A i * A i - X i ω * X i ω))
    (t : ℝ) (ht : 0 ≤ t) (x : V → ℝ) (hx : x ≠ 0) :
    μ {ω | t * (x ⬝ᵥ x) ≤ |quadForm (∑ i, X i ω) x|}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ i, A i * A i‖))) := by
  refine le_trans (measure_mono ?_)
    (matrix_hoeffding h_meas h_indep h_herm h_bound t ht)
  intro ω hω
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_le] at hcon
  have hle : |quadForm (∑ i, X i ω) x| ≤ ‖∑ i, X i ω‖ * (x ⬝ᵥ x) :=
    abs_quadForm_le_of_l2OpNorm_le (le_refl _) x
  have hCx : 0 < x ⬝ᵥ x := dotProduct_self_pos_of_ne_zero hx
  have hprod : 0 < (t - ‖∑ i, X i ω‖) * (x ⬝ᵥ x) :=
    mul_pos (by linarith) hCx
  have hexp : (t - ‖∑ i, X i ω‖) * (x ⬝ᵥ x)
      = t * (x ⬝ᵥ x) - ‖∑ i, X i ω‖ * (x ⬝ᵥ x) := by ring
  simp only [Set.mem_setOf_eq] at hω
  linarith

end QuadForm

/-! ## The edge-perturbation assembly -/

section Assembly

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- **The centered edge-perturbation norm tail** — `matrix_hoeffding`
assembled at the Bernoulli edge design: on the product-Bernoulli space at
inclusion probabilities `p ∈ [0, 1]`, the spectral norm of the summed
centered edge-Laplacian perturbation obeys the classical exponential tail
against the deterministic variance statistic `‖∑_e L_e²‖`. No hypothesis
on the weight matrix `A` (the design is sign-free). CONDITIONAL ON THE
`matrix_hoeffding` AXIOM: all four hypothesis clauses are proved
(`stronglyMeasurable_perturbSummand`, `indepFun_perturbSummand`,
`perturbSummand_isSymm`, `perturbSummand_sq_le`). -/
theorem edgePerturbation_norm_tail [Nonempty V]
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool | ‖∑ e : V × V, perturbSummand A p e ω‖ ≥ t}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ e : V × V,
          perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  haveI hprob : IsProbabilityMeasure (bernPMF p hp0 hp1).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hmeas : ∀ i : Fin (Fintype.card (V × V)),
      StronglyMeasurable fun ω : (V × V) → Bool =>
        perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω :=
    fun i => stronglyMeasurable_perturbSummand A p _
  have hindep : ∀ i j : Fin (Fintype.card (V × V)), i ≠ j →
      IndepFun (fun ω : (V × V) → Bool =>
          perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω)
        (fun ω : (V × V) → Bool =>
          perturbSummand A p ((Fintype.equivFin (V × V)).symm j) ω)
        (bernPMF p hp0 hp1).toMeasure :=
    fun i j hij => indepFun_perturbSummand A p hp0 hp1 _ _
      ((Fintype.equivFin (V × V)).symm.injective.ne hij)
  have hherm : ∀ (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool),
      (perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω).IsHermitian :=
    fun i ω => isHermitian_of_isSymm (perturbSummand_isSymm A p _ ω)
  have hbound : ∀ (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool),
      Matrix.PosSemidef
        (perturbEdgeLap A ((Fintype.equivFin (V × V)).symm i)
          * perturbEdgeLap A ((Fintype.equivFin (V × V)).symm i)
          - perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω
            * perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω) :=
    fun i ω => perturbSummand_sq_le A p hp0 hp1 _ ω
  have hmain := matrix_hoeffding
    (μ := (bernPMF p hp0 hp1).toMeasure)
    (X := fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
      perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω)
    (A := fun i => perturbEdgeLap A ((Fintype.equivFin (V × V)).symm i))
    hmeas hindep hherm hbound t ht
  have hsum : ∀ ω : (V × V) → Bool,
      ∑ i : Fin (Fintype.card (V × V)),
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω) i ω
      = ∑ e : V × V, perturbSummand A p e ω := fun ω =>
    Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => perturbSummand A p e ω)
  have hseteq : {ω : (V × V) → Bool |
      ‖∑ i : Fin (Fintype.card (V × V)),
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω) i ω‖ ≥ t}
      = {ω : (V × V) → Bool | ‖∑ e : V × V, perturbSummand A p e ω‖ ≥ t} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    exact Iff.of_eq (congrArg (fun S : Matrix V V ℝ => ‖S‖ ≥ t) (hsum ω))
  rw [hseteq] at hmain
  have hvar : ∑ i : Fin (Fintype.card (V × V)),
      (fun i => perturbEdgeLap A ((Fintype.equivFin (V × V)).symm i)) i
        * (fun i => perturbEdgeLap A ((Fintype.equivFin (V × V)).symm i)) i
      = ∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e :=
    Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => perturbEdgeLap A e * perturbEdgeLap A e)
  rw [hvar] at hmain
  exact hmain

/-- **The centered edge-perturbation quadratic-form tail** — the same
exponential bound for the failure of the additive quadratic-form
approximation at a fixed nonzero vector:
outside a set of the bound's measure, `|xᵀ (∑_e (δ_e − p_e) • L_e) x| <
t · (x ⬝ᵥ x)`. CONDITIONAL ON THE `matrix_hoeffding` AXIOM (the norm tail
above, transferred by the norm→form domination). -/
theorem edgePerturbation_quadForm_tail [Nonempty V]
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (t : ℝ) (ht : 0 ≤ t) (x : V → ℝ) (hx : x ≠ 0) :
    (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          t * (x ⬝ᵥ x) ≤ |quadForm (∑ e : V × V, perturbSummand A p e ω) x|}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ e : V × V,
          perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  refine le_trans (measure_mono ?_)
    (edgePerturbation_norm_tail A p hp0 hp1 t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  simp only [Set.mem_setOf_eq, not_le] at hcon
  have hle : |quadForm (∑ e : V × V, perturbSummand A p e ω) x|
      ≤ ‖∑ e : V × V, perturbSummand A p e ω‖ * (x ⬝ᵥ x) :=
    abs_quadForm_le_of_l2OpNorm_le (le_refl _) x
  have hCx : 0 < x ⬝ᵥ x := dotProduct_self_pos_of_ne_zero hx
  have hprod : 0 < (t - ‖∑ e : V × V, perturbSummand A p e ω‖) * (x ⬝ᵥ x) :=
    mul_pos (by linarith) hCx
  have hexp : (t - ‖∑ e : V × V, perturbSummand A p e ω‖) * (x ⬝ᵥ x)
      = t * (x ⬝ᵥ x) - ‖∑ e : V × V, perturbSummand A p e ω‖ * (x ⬝ᵥ x) := by
    ring
  linarith

end Assembly

end Scaffold.Derived.EdgePerturbationTail
