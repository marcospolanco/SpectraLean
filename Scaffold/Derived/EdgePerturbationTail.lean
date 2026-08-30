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

  The eigenvalue-level packaging (the proposal's namesake application):
  the tail transferred to the sorted spectrum through the *proved* Weyl
  inequality.

  - `edgePerturbation_eval_tail`: every Laplacian eigenvalue of the
    resampled graph concentrates around the base graph's —
    `μ {|λᵢ(L(A+E_ω)) − λᵢ(L A)| ≥ t} ≤ 2 d exp(−t²/(2‖∑_e L_e²‖))`
    at every sorted index.
  - `edgePerturbation_eval_lower_tail`: the one-sided gap-survival form
    `μ {λᵢ(L(A+E_ω)) ≤ λᵢ(L A) − t} ≤ …` — the "random resampling does
    not destroy the spectral gap" statement.
  - `edgePerturbation_lambda2_lower_tail`: the λ₂-spelled corollary at
    the `lambda2` interface, for Fiedler/Cheeger-facing consumers.
  - `edgePerturbation_quadForm_uniform_tail`: the uniform
    (existential-x) quadratic-form packaging — outside a set of the
    bound's measure, `|xᵀ L(E_ω) x| < t (x ⬝ᵥ x)` for *every* nonzero
    vector simultaneously (the proposal's priced sup-over-x residual;
    the `x ≠ 0` guard is load-bearing — at `x = 0` the un-guarded event
    is all of `Ω`).

  The Cheeger-window packaging (2026-08-28, the standing handoff's named
  conductance/Cheeger-level consumer of the λ₂ tail): the first join of
  the edge-perturbation concentration family to the Cheeger center.

  - `edgePerturbation_lambda2_cheeger_floor`: the resampled graph's
    algebraic connectivity stays above the Cheeger-driven floor
    `d · φ(G)² / 2 − t` outside the λ₂ tail's bound.
  - `edgePerturbation_connectivity_bracket`: the two-sided window —
    both Cheeger directions (through the engine pair
    `cheeger_lower_bound_laplacian`/`cheeger_upper_bound_laplacian`)
    load-bearing on one statement: leaving the window
    `[d·φ²/2 − t, 2dφ + t]` implies leaving the eigenvalue tail event.

  The normalized (irregular) window packaging (2026-08-29, the degree
  sandwich's named consumer) and its algorithm-facing capstone:

  - `edgePerturbation_normalized_cheeger_floor` and
    `edgePerturbation_normalized_connectivity_bracket`: the irregular
    siblings at `λ₂(L_sym G_ω)`, assembled through the degree sandwich.
  - `edgePerturbation_fiedler_sweep_cut_tail`: the swept-Fiedler-cut
    consumer — outside the bracket's tail set, every admissible outcome
    is *connected* and carries an explicit swept level set of its own
    Fiedler sweep vector at `conductance² ≤ 2 · (2·dmax·φ + t)/dmin`
    (the floor's positivity feeding the connectivity transfer, the
    ceiling the sweep extraction — the window family completed into an
    algorithmic output).

  The degree tail (the scalar sibling, `hoeffding_inequality`'s first
  theorem consumer — 2026-08-29,
  `proposals/hoeffding-inequality-degree-concentration.md`):

  - `edgePerturbation_degree_tail`: the per-vertex degree-deviation
    tail `μ {|deg G_ω v − deg A v| ≥ t} ≤ 2 exp(−t²/(2 S_v))` at the
    variance statistic `S_v = ∑ₑ w_v(e)²` — the complementary
    concentration the window family's honesty notes name as missing
    (the λ₂/norm tails carry zero degree information,
    `L(E_ω)·1 = 0` identically).
  - `edgePerturbation_degree_tail_all`: the all-vertices union bound,
    stated at the exact per-vertex sum — the first step toward
    *deriving* the admissibility window rather than hypothesizing it.

  The Bernstein twin (the variance-adaptive degree tail, 2026-08-29,
  the same proposal's priced follow-on — `bernstein_inequality`'s and
  `bernstein_bounded_variance`'s first theorem consumers):

  - `edgePerturbation_degree_tail_bernstein`: the per-vertex tail at
    the *true* variance statistic `σ²_v = ∑ₑ w_v(e)² p e (1 − p e)` and
    a magnitude budget `M ≥ |w_v(e)|`:
    `μ {|dev| ≥ t} ≤ 2 exp(−t²/(2 σ²_v + 2Mt/3))` — strictly sharper
    than the Hoeffding twin at interior sampling probabilities
    (`σ²_v ≤ S_v/4`), pinned numerically in the QA.
  - `edgePerturbation_degree_tail_bernstein_budget`: the budget form at
    any supplied variance budget `σ²_v ≤ Vbud`.

  The admissibility dissolution (2026-08-29, the degree-concentration
  proposal's priced follow-on — the window family's first measured
  event with *no* admissibility conjunct):

  - `perturbAdmissible_of_degDev_lt`: the degree-window transfer — base
    degrees in the shrunk window `[dmin + s, dmax − s]` plus
    per-vertex deviations strictly below `s` put the outcome inside the
    admissibility window (nonnegativity from the pair design condition
    `p e + p eᵀ ≤ 1`, degrees from the shrunk window).
  - `edgePerturbation_normalized_connectivity_bracket_unconditional`:
    the union of the delivered bracket with the all-vertices degree
    tail — leaving the two-sided normalized-connectivity window is
    bounded by the window tail at `t` plus the degree tail at `s`,
    with no conditioning event. Conditional on `matrix_hoeffding`
    *and* `hoeffding_inequality` together — the family's only
    two-axiom member.
  - `edgePerturbation_normalized_cheeger_floor_unconditional` and
    `edgePerturbation_fiedler_sweep_cut_tail_unconditional`: the
    dissolution completed across the family (same day, the follow-on
    the bracket's delivery priced) — the floor and the
    algorithm-facing swept-cut capstone made unconditional at the same
    decomposition, so every window-family measured event now reads
    without a conditioning conjunct (each two-axiom:
    `matrix_hoeffding` via the window theorem, `hoeffding_inequality`
    via the degree tail).

  The tail theorems are **conditional on the `matrix_hoeffding`
  axiom** (Tropp 2012, Theorem 1.4, as repaired 2026-08-28 with the
  `[Nonempty V]` guard) and must never be described as foundationally
  proved; the two Hoeffding degree tails are conditional on the *scalar*
  `hoeffding_inequality` theorem (Vershynin 2018, Theorem 2.2.2 — proved
  locally since the 2026-08-30 Hoeffding retirement) exactly as its own
  delivery record states; the two Bernstein twin tails ride the
  `bernstein_inequality` (Vershynin 2018, Theorem 2.8.1) and
  `bernstein_bounded_variance` (Wainwright 2019, Theorem 2.15)
  **theorems, themselves proved locally since the 2026-08-30
  repair-and-retirement (Errata §8) — the twin tails are hard crust,
  with no axiom contact (`#print axioms` verified)**; and the
  unconditional bracket members (the dissolution family) are conditional
  on `matrix_hoeffding` alone — their other engine,
  `hoeffding_inequality`, having been proved in the same
  retirement — each via its own sub-theorem.
  Every hypothesis clause of all four axioms is discharged by a proved
  lemma in the engine module. The transfer side is *proved* hard crust:
  the Weyl inequality (retired from axiom 2026-08-20), the packaging
  identity `laplacian_perturbWeight`, `laplacian_add`, `evals_congr`,
  and the degree-linearity package `deg_add`/`deg_sum` behind
  `deg_resampled`.

  QA: `Scaffold/QA/Derived/EdgePerturbation_QA.lean`.
-/

import Scaffold.Mathlib.GraphTheory.EdgePerturbation
import Scaffold.Mathlib.GraphTheory.Cheeger
import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl

open MeasureTheory ProbabilityTheory
open SpectralGraphTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open Scaffold.Mathlib.Probability.Concentration.Matrix
open Scaffold.Mathlib.Probability.Concentration.Scalar
open Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation
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
clause set (the 2026-08-30 repaired set, including the centering clause
`h_mean` — Errata §9; the hypothesis is threaded through unchanged from
the axiom). The nonzero guard is load-bearing: at `x = 0` the event is
all of `Ω` and the statement is false for large `t`. -/
theorem matrix_hoeffding_quadForm {n : ℕ} [Nonempty V]
    {X : Fin n → Ω → Matrix V V ℝ} {A : Fin n → Matrix V V ℝ}
    (h_meas : ∀ i, StronglyMeasurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n =>
      (inferInstance : MeasurableSpace (Matrix V V ℝ))) X μ)
    (h_herm : ∀ i ω, (X i ω).IsHermitian)
    (h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (h_bound : ∀ i ω, Matrix.PosSemidef (A i * A i - X i ω * X i ω))
    (t : ℝ) (ht : 0 ≤ t) (x : V → ℝ) (hx : x ≠ 0) :
    μ {ω | t * (x ⬝ᵥ x) ≤ |quadForm (∑ i, X i ω) x|}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 * ‖∑ i, A i * A i‖))) := by
  refine le_trans (measure_mono ?_)
    (matrix_hoeffding h_meas h_indep h_herm h_mean h_bound t ht)
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
`matrix_hoeffding` AXIOM: all five hypothesis clauses are proved
(`stronglyMeasurable_perturbSummand`, `iIndepFun_perturbSummand`,
`perturbSummand_isSymm`, `integral_perturbSummand_eq_zero` — the
centering, added by the 2026-08-30 Errata §9 repair — and
`perturbSummand_sq_le`). -/
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
  have hindep : iIndepFun (fun _ : Fin (Fintype.card (V × V)) =>
      (inferInstance : MeasurableSpace (Matrix V V ℝ)))
      (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
        perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω)
      (bernPMF p hp0 hp1).toMeasure :=
    iIndepFun_perturbSummand A p hp0 hp1
  have hherm : ∀ (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool),
      (perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω).IsHermitian :=
    fun i ω => isHermitian_of_isSymm (perturbSummand_isSymm A p _ ω)
  have hmean : ∀ (i : Fin (Fintype.card (V × V))),
      ∫ ω : (V × V) → Bool,
        perturbSummand A p ((Fintype.equivFin (V × V)).symm i) ω
        ∂(bernPMF p hp0 hp1).toMeasure = 0 :=
    fun i => integral_perturbSummand_eq_zero A p hp0 hp1 _
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
    hmeas hindep hherm hmean hbound t ht
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

/-! ## The eigenvalue-level packaging -/

section Eigenvalue

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- **The eigenvalue-level edge-perturbation tail** — the norm tail
transferred to the sorted spectrum through the *proved* Weyl inequality:
at every sorted index `i`, the resampled graph's Laplacian eigenvalue
concentrates around the base graph's,
`μ {t ≤ |λᵢ(L(A+E_ω)) − λᵢ(L A)|} ≤ 2 d exp(−t²/(2‖∑_e L_e²‖))`.

The transfer: on the complement of the tail event the packaging identity
`laplacian_perturbWeight` reads the norm bound as `‖L(E_ω)‖`, Weyl (a
theorem here since 2026-08-20, not an axiom) bounds the eigenvalue
displacement by that norm, and `laplacian_add`/`evals_congr` join the
two Laplacian spellings. CONDITIONAL ON THE `matrix_hoeffding` AXIOM via
the norm tail alone; the Weyl side is proved. -/
theorem edgePerturbation_eval_tail (hA : A.IsSymm)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (i : Fin (Fintype.card V)) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        t ≤ |evals (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) i
          - evals (laplacian_symmetric A hA) i|}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  refine le_trans (measure_mono ?_)
    (edgePerturbation_norm_tail A p hp0 hp1 t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hlt
  have hE := perturbWeight_isSymm A p ω
  have hL := laplacian_symmetric A hA
  have hLE := laplacian_symmetric (perturbWeight A p ω) hE
  have hwy := weyl_inequality (laplacian A) (laplacian (perturbWeight A p ω))
    hL hLE i
  rw [show ‖laplacian (perturbWeight A p ω)‖
      = ‖∑ e : V × V, perturbSummand A p e ω‖ from by
        rw [laplacian_perturbWeight]] at hwy
  rw [evals_congr (laplacian_symmetric (A + perturbWeight A p ω)
      (hA.add hE)) (hL.add hLE) (laplacian_add A (perturbWeight A p ω)) i]
    at hω
  have hnorm : ‖∑ e : V × V, perturbSummand A p e ω‖ < t := lt_of_not_ge hlt
  linarith

/-- **The one-sided gap-survival tail** — the same exponential bound for
the event that resampling *depresses* the `i`-th Laplacian eigenvalue by
more than `t`: `μ {λᵢ(L(A+E_ω)) ≤ λᵢ(L A) − t} ≤ 2 d exp(…)`. The
complement reading is the field-standard robustness statement: with
probability at least `1 − 2 d exp(−t²/(2‖∑_e L_e²‖))`, every eigenvalue
(in particular λ₂ — the algebraic-connectivity certificate) stays within
`t` of its base value from below. Derived from `edgePerturbation_eval_tail`
by event inclusion (`λ' ≤ λ − t` implies `t ≤ |λ' − λ|`).
CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the two-sided tail. -/
theorem edgePerturbation_eval_lower_tail (hA : A.IsSymm)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (i : Fin (Fintype.card V)) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        evals (laplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) i
          ≤ evals (laplacian_symmetric A hA) i - t}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  refine le_trans (measure_mono ?_)
    (edgePerturbation_eval_tail A p hA hp0 hp1 i t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- **The λ₂ gap-survival corollary** — the one-sided tail at the
`lambda2` interface (the Fiedler-facing spelling, `2 ≤ card V`): under
random edge resampling, the algebraic connectivity of the resampled
graph stays above `lambda2 A − t` outside a set of measure at most
`2 d exp(−t²/(2‖∑_e L_e²‖))`. Join with `lambda2_pos_of_connected` for
the connectivity-robustness reading. CONDITIONAL ON THE
`matrix_hoeffding` AXIOM via the one-sided tail. -/
theorem edgePerturbation_lambda2_lower_tail (hA : A.IsSymm)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        lambda2 (A + perturbWeight A p ω) (hA.add (perturbWeight_isSymm A p ω))
          hcard ≤ lambda2 A hA hcard - t}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  have h := edgePerturbation_eval_lower_tail A p hA hp0 hp1 ⟨1, by omega⟩ t ht
  simpa [lambda2] using h

/-- **The uniform quadratic-form tail** — the existential-vector
packaging (complement reading: outside a set of the bound's measure,
`|xᵀ L(E_ω) x| < t (x ⬝ᵥ x)` for *every* nonzero vector `x`
simultaneously). The event inclusion is the norm→form domination
contraposed: a witnessing `x ≠ 0` forces `‖L(E_ω)‖ ≥ t` through
`abs_quadForm_le_of_l2OpNorm_le` and the packaging identity
`laplacian_perturbWeight`.

The `x ≠ 0` guard is load-bearing, not decorative: at `x = 0` the
membership condition is `t · 0 ≤ |0|` — always true — so the un-guarded
existential event is all of `Ω` and no exponential bound can hold (the
QA fence `epK2_uniform_guard_fence_QA` refutes the un-guarded form in
proved arithmetic). CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the
norm tail alone. -/
theorem edgePerturbation_quadForm_uniform_tail
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool | ∃ x : V → ℝ, x ≠ 0 ∧
        t * (x ⬝ᵥ x) ≤ |quadForm (laplacian (perturbWeight A p ω)) x|}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  refine le_trans (measure_mono ?_)
    (edgePerturbation_norm_tail A p hp0 hp1 t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hlt
  obtain ⟨x, hx0, hx⟩ := hω
  have hnorm : ‖∑ e : V × V, perturbSummand A p e ω‖ < t := lt_of_not_ge hlt
  rw [show laplacian (perturbWeight A p ω)
      = ∑ e : V × V, perturbSummand A p e ω from laplacian_perturbWeight A p ω]
    at hx
  have hle : |quadForm (∑ e : V × V, perturbSummand A p e ω) x|
      ≤ ‖∑ e : V × V, perturbSummand A p e ω‖ * (x ⬝ᵥ x) :=
    abs_quadForm_le_of_l2OpNorm_le (le_refl _) x
  have hCx : 0 < x ⬝ᵥ x := dotProduct_self_pos_of_ne_zero hx0
  have hprod : 0 < (t - ‖∑ e : V × V, perturbSummand A p e ω‖) * (x ⬝ᵥ x) :=
    mul_pos (by linarith) hCx
  have hexp : (t - ‖∑ e : V × V, perturbSummand A p e ω‖) * (x ⬝ᵥ x)
      = t * (x ⬝ᵥ x) - ‖∑ e : V × V, perturbSummand A p e ω‖ * (x ⬝ᵥ x) := by
    ring
  linarith

end Eigenvalue

/-! ## The Cheeger window -/

section CheegerWindow

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- **The Cheeger-driven connectivity floor under random edge
resampling** — on a `d`-regular connected-enough base graph, the
resampled graph's algebraic connectivity stays above the Cheeger floor
`d · φ(G)² / 2 − t` outside a set of the λ₂ tail's measure:
`μ {λ₂(L(A+E_ω)) ≤ d·φ(A)²/2 − t} ≤ 2 d exp(−t²/(2‖∑_e L_e²‖))`.

The composition: the proved `cheeger_lower_bound_laplacian` puts the
base `λ₂` above the floor, so the floor-crossing event is inside the
delivered λ₂ lower-tail event (`edgePerturbation_lambda2_lower_tail`) —
a pure `measure_mono`. This is the conductance/Cheeger-level consumer
the eigenvalue tail's delivery record priced: the expansion certificate
of the base graph survives random resampling at the concentration
bridge's own confidence. CONDITIONAL ON THE `matrix_hoeffding` AXIOM via
the lower tail alone; the Cheeger side is proved hard crust. -/
theorem edgePerturbation_lambda2_cheeger_floor (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        lambda2 (A + perturbWeight A p ω) (hA.add (perturbWeight_isSymm A p ω)) hcard
          ≤ d * (cheegerConstant A) ^ 2 / 2 - t}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  refine le_trans (measure_mono ?_)
    (edgePerturbation_lambda2_lower_tail A p hA hp0 hp1 hcard t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hfloor := cheeger_lower_bound_laplacian A hA hnonneg d hd hdpos hcard
  linarith

/-- **The connectivity bracket** — the two-sided Cheeger window under
random edge resampling: leaving `[d·φ²/2 − t, 2 d φ + t]` implies leaving
the two-sided eigenvalue tail event, so
`μ {λ₂(L(A+E_ω)) ≤ d·φ²/2 − t ∨ 2dφ + t ≤ λ₂(L(A+E_ω))}
≤ 2 d exp(−t²/(2‖∑_e L_e²‖))` — the same constant as the one-sided tail,
because the window *contains* the eigenvalue ball `[λ₂ − t, λ₂ + t]`.

Both Cheeger directions are load-bearing on the inclusion: the floor
side consumes `cheeger_lower_bound_laplacian` (`d·φ²/2 ≤ λ₂`), the
ceiling side `cheeger_upper_bound_laplacian` (`λ₂ ≤ 2dφ`) — a wrong
constant on either side breaks the corresponding half of the
`measure_mono`. The transfer to the spectrum is the proved-Weyl
`edgePerturbation_eval_tail` at index 1. CONDITIONAL ON THE
`matrix_hoeffding` AXIOM via the two-sided tail; both Cheeger sides
proved. -/
theorem edgePerturbation_connectivity_bracket (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (d : ℝ) (hd : ∀ i, deg A i = d) (hdpos : 0 < d)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        lambda2 (A + perturbWeight A p ω) (hA.add (perturbWeight_isSymm A p ω)) hcard
          ≤ d * (cheegerConstant A) ^ 2 / 2 - t
        ∨ 2 * (d * cheegerConstant A) + t
          ≤ lambda2 (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω)) hcard}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  have hfloor := cheeger_lower_bound_laplacian A hA hnonneg d hd hdpos hcard
  have hceil := cheeger_upper_bound_laplacian A hA hnonneg d hd hdpos hcard
  refine le_trans (measure_mono ?_)
    (edgePerturbation_eval_tail A p hA hp0 hp1 ⟨1, by omega⟩ t ht)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rcases hω with hlow | hhigh
  · have h1 : lambda2 (A + perturbWeight A p ω)
          (hA.add (perturbWeight_isSymm A p ω)) hcard
        ≤ lambda2 A hA hcard - t := by linarith
    show t ≤ |(lambda2 (A + perturbWeight A p ω)
          (hA.add (perturbWeight_isSymm A p ω)) hcard : ℝ)
        - lambda2 A hA hcard|
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have h1 : lambda2 A hA hcard + t
        ≤ lambda2 (A + perturbWeight A p ω)
            (hA.add (perturbWeight_isSymm A p ω)) hcard := by linarith
    show t ≤ |(lambda2 (A + perturbWeight A p ω)
          (hA.add (perturbWeight_isSymm A p ω)) hcard : ℝ)
        - lambda2 A hA hcard|
    rw [abs_of_nonneg (by linarith)]
    linarith

end CheegerWindow

/-! ## The normalized (irregular) Cheeger window

The irregular sibling of the Cheeger window above, assembled from the
same λ₂ tail through the degree eigenvalue sandwich
(`GraphTheory.VariationalTransfer`, 2026-08-29) and the irregular
Cheeger pair: a high-probability window on the *normalized* algebraic
connectivity `λ₂(L_sym G_ω)` of the resampled graph under random edge
resampling, on arbitrary symmetric nonnegative positive-degree base
graphs — no regularity.

The resampling design's degrees are random, and the centered design
(`perturbSummand`) makes them genuinely so: no design restriction
preserves the tail (it consumes the centered design), and the norm tail
carries zero degree information (`L(E_ω) · 1 = 0` identically — the
Laplacian of any symmetric matrix kills the constants). The window
therefore carries its admissibility **event-internally**: the measured
set intersects with the outcomes whose resampled graph stays a
nonnegative weighted graph with degrees in the base graph's window
`[dmin, dmax]` (`perturbAdmissible`). The complement reading: outside a
set of the bound's measure, every admissible outcome keeps
`λ₂(L_sym G_ω)` inside `((dmin·φ²/2 − t)/dmax, (2·dmax·φ + t)/dmin)`.

Sandwich-side consumption (the assembly's Step-0 design verdict): the
floor side runs the sandwich's *lower* side at the perturbed degree
*ceiling* — a depressed normalized eigenvalue with degrees bounded
above forces a depressed combinatorial eigenvalue, into the delivered
λ₂ lower tail — and the ceiling side the *upper* side at the degree
*floor*. The floor theorem's window constant divides by `dmax`; the
bracket's ceiling by `dmin`. Both Cheeger directions are load-bearing
on the bracket's inclusion, and the admissibility window is
proof-load-bearing (the sandwich's `hnn`/`hd` clauses on the perturbed
graph are exactly the window conjuncts); no dropped-window refutation
fixture exists at fixture scale — at the junk outcomes the normalized
Laplacian degenerates to the identity, whose `λ₂ = 1` keeps the
un-windowed floor condition false on `K₂`-shaped fixtures (recorded
honestly in the QA section, and — since the 2026-08-29 corner audit —
*proved* there: `normalizedLaplacian_eq_one_of_forall_deg_nonpos` and
`evals_one` pin the identity junk on the shelf, with both the
zero-degree and the negative-degree corners witnessed in
`EdgePerturbation_QA.lean`'s cornerAudit section). -/

section NormalizedCheegerWindow

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- The admissibility window of the irregular Cheeger window: the
outcomes whose resampled graph stays a nonnegative weighted graph with
degrees in the base graph's window `[dmin, dmax]`. Nonnegativity and
the degree floor are the exact hypothesis clauses the irregular Cheeger
pair and the degree sandwich need on the perturbed graph; the degree
ceiling is the sandwich's lower-side constant. -/
def perturbAdmissible (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (dmin dmax : ℝ) (ω : (V × V) → Bool) : Prop :=
  (∀ i j, 0 ≤ (A + perturbWeight A p ω) i j) ∧
    (∀ i, dmin ≤ deg (A + perturbWeight A p ω) i) ∧
      ∀ i, deg (A + perturbWeight A p ω) i ≤ dmax

/-- **The normalized Cheeger floor under random edge resampling** — on
a symmetric nonnegative positive-degree base graph with degrees in
`[dmin, dmax]` (`0 < dmin`), the resampled graph's *normalized* algebraic
connectivity stays above `(dmin · φ(A)²/2 − t) / dmax` outside a set of
the λ₂ tail's measure, on the outcomes whose resampled degrees stay in
the same window:
`μ {ω admissible ∧ λ₂(L_sym G_ω) ≤ (dmin·φ²/2 − t)/dmax}
≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))`.

The composition: on the admissible outcomes the sandwich's lower side
(`div_le_secondEval_normalizedLaplacian`) turns a depressed normalized
eigenvalue into a depressed combinatorial one, and the new engine
`cheeger_lower_bound_laplacian_of_degree_window` puts the base `λ₂`
above the same floor — a pure `measure_mono` into the delivered λ₂
lower tail. CONDITIONAL ON THE `matrix_hoeffding` AXIOM via the lower
tail alone; the Cheeger and sandwich sides are proved hard crust. -/
theorem edgePerturbation_normalized_cheeger_floor (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmin dmax : ℝ) (hdmin : ∀ i, dmin ≤ deg A i) (hpos : 0 < dmin)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        perturbAdmissible A p dmin dmax ω ∧
        secondEval (normalizedLaplacian (A + perturbWeight A p ω))
            (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) hcard
          ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  refine le_trans (measure_mono ?_)
    (edgePerturbation_lambda2_lower_tail A p hA hp0 hp1 hcard t ht)
  rintro ω ⟨⟨hnn', hdmin', hdmax'⟩, hlow⟩
  simp only [Set.mem_setOf_eq]
  have hd' : ∀ i, 0 < deg (A + perturbWeight A p ω) i :=
    fun i => lt_of_lt_of_le hpos (hdmin' i)
  obtain ⟨i₀⟩ := ‹Nonempty V›
  have hdmaxpos : 0 < dmax := lt_of_lt_of_le (hd' i₀) (hdmax' i₀)
  have hsand := div_le_secondEval_normalizedLaplacian
    (A + perturbWeight A p ω) (hA.add (perturbWeight_isSymm A p ω))
    hnn' hd' dmax hdmax' hcard
  have h2 := hsand.trans hlow
  rw [div_le_div_iff₀ hdmaxpos hdmaxpos] at h2
  have h3 := le_of_mul_le_mul_right h2 hdmaxpos
  have h4 := cheeger_lower_bound_laplacian_of_degree_window A hA hnn hd
    dmin hdmin hpos hcard
  linarith

/-- **The normalized connectivity bracket** — the two-sided irregular
Cheeger window under random edge resampling: leaving
`[(dmin·φ(A)²/2 − t)/dmax, (2·dmax·φ(A) + t)/dmin]` implies leaving the
two-sided eigenvalue tail at the *same* constant (the window contains
the sandwich-scaled eigenvalue ball), on the admissible outcomes:
`μ {ω admissible ∧ (λ₂(L_sym G_ω) ≤ floor ∨ ceiling ≤ λ₂(L_sym G_ω))}
≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))`.

Both sides are load-bearing on the inclusion — the floor through the
sandwich's lower side at `dmax` plus the new window-Cheeger floor
engine, the ceiling through the sandwich's upper side at `dmin` plus
the window-Cheeger ceiling engine — and a wrong `dmin`/`dmax` pairing
breaks the corresponding half. CONDITIONAL ON THE `matrix_hoeffding`
AXIOM via the two-sided tail; Cheeger and sandwich sides proved. -/
theorem edgePerturbation_normalized_connectivity_bracket (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmin dmax : ℝ) (hdmin : ∀ i, dmin ≤ deg A i) (hpos : 0 < dmin)
    (hdmax : ∀ i, deg A i ≤ dmax)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        perturbAdmissible A p dmin dmax ω ∧
        (secondEval (normalizedLaplacian (A + perturbWeight A p ω))
            (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) hcard
          ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax
        ∨ (2 * (dmax * cheegerConstant A) + t) / dmin
          ≤ secondEval (normalizedLaplacian (A + perturbWeight A p ω))
              (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                (hA.add (perturbWeight_isSymm A p ω))) hcard)}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  have hfloor := cheeger_lower_bound_laplacian_of_degree_window A hA hnn hd
    dmin hdmin hpos hcard
  have hceil := cheeger_upper_bound_laplacian_of_degree_window A hA hnn hd
    dmax hdmax hcard
  refine le_trans (measure_mono ?_)
    (edgePerturbation_eval_tail A p hA hp0 hp1 ⟨1, by omega⟩ t ht)
  rintro ω ⟨⟨hnn', hdmin', hdmax'⟩, hlow | hhigh⟩
  · simp only [Set.mem_setOf_eq]
    have hd' : ∀ i, 0 < deg (A + perturbWeight A p ω) i :=
      fun i => lt_of_lt_of_le hpos (hdmin' i)
    obtain ⟨i₀⟩ := ‹Nonempty V›
    have hdmaxpos : 0 < dmax := lt_of_lt_of_le (hd' i₀) (hdmax' i₀)
    have hsand := div_le_secondEval_normalizedLaplacian
      (A + perturbWeight A p ω) (hA.add (perturbWeight_isSymm A p ω))
      hnn' hd' dmax hdmax' hcard
    have h2 := hsand.trans hlow
    rw [div_le_div_iff₀ hdmaxpos hdmaxpos] at h2
    have h3 := le_of_mul_le_mul_right h2 hdmaxpos
    have h1 : lambda2 (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω)) hcard
        ≤ lambda2 A hA hcard - t := by linarith
    show t ≤ |(lambda2 (A + perturbWeight A p ω)
          (hA.add (perturbWeight_isSymm A p ω)) hcard : ℝ)
        - lambda2 A hA hcard|
    rw [abs_of_nonpos (by linarith)]
    linarith
  · simp only [Set.mem_setOf_eq]
    have hd' : ∀ i, 0 < deg (A + perturbWeight A p ω) i :=
      fun i => lt_of_lt_of_le hpos (hdmin' i)
    have hsand := secondEval_normalizedLaplacian_le_div
      (A + perturbWeight A p ω) (hA.add (perturbWeight_isSymm A p ω))
      hnn' hd' dmin hdmin' hpos hcard
    have h2 := le_trans hhigh hsand
    rw [div_le_div_iff₀ hpos hpos] at h2
    have h3 := le_of_mul_le_mul_right h2 hpos
    have h1 : lambda2 A hA hcard + t
        ≤ lambda2 (A + perturbWeight A p ω)
            (hA.add (perturbWeight_isSymm A p ω)) hcard := by linarith
    show t ≤ |(lambda2 (A + perturbWeight A p ω)
          (hA.add (perturbWeight_isSymm A p ω)) hcard : ℝ)
        - lambda2 A hA hcard|
    rw [abs_of_nonneg (by linarith)]
    linarith

/-- **The swept-Fiedler-cut consumer of the normalized window** — the
window family's algorithm-facing capstone: under random edge
resampling, outside the bracket's tail set every admissible outcome's
resampled graph is **connected** and carries an explicit swept level
set of *its own* Fiedler sweep vector at

`conductance G_ω S ^ 2 ≤ 2 · (2·dmax·φ(A) + t)/dmin`,

whenever the window's floor numerator is positive (`t < dmin·φ²/2`):

`μ {ω admissible ∧ ¬(connected G_ω ∧ ∃ swept S, conductance² ≤
2·ceiling)} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))`.

The composition — each delivered family load-bearing on one link: the
window *floor's positivity* (the new hypothesis `hfloor`) feeds the
connectivity transfer (`secondEval_normalizedLaplacian_pos_iff_connected`
— a depressed-to-zero eigenvalue would disconnect the resampled graph
and kill the sweep theorem's input), and the window *ceiling* caps the
sweep extraction (`fiedler_sweep_cut_normalized` on the resampled
graph, whose `conductance² ≤ 2 λ₂` is then bounded by `2·ceiling`). A
pure `measure_mono` into the delivered bracket. CONDITIONAL ON THE
`matrix_hoeffding` AXIOM via the bracket; the connectivity transfer
and sweep extraction are proved hard crust.

The floor-positivity guard is proof-load-bearing, not decorative: at
`t ≥ dmin·φ²/2` the window no longer forces `0 < λ₂`, and connectivity
of the resampled graph — the sweep theorem's entry ticket — is lost.
The guard is also *fixture-refuted when dropped*
(`epC4_sweepWindow_unguarded_refuted_QA` in
`Scaffold/QA/Derived/EdgePerturbation_QA.lean`, 2026-08-29): on `C₄`
at window `[1, 2]` the perfect-matching outcomes are
admissible-but-disconnected — their bad-set membership via
`¬connected` is `t`-invariant, so at large `t` the collapsed bound
drops below their atom mass and the un-guarded statement is false in
proved arithmetic. This corrects the original honesty note, whose
"at 2–3 vertices the tail bound exceeds `1`" obstruction had anchored
on the eigenvalue-floor membership route and on fixtures where no
admissible-but-disconnected outcome exists at all. -/
theorem edgePerturbation_fiedler_sweep_cut_tail (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j) (hd : ∀ i, 0 < deg A i)
    (dmin dmax : ℝ) (hdmin : ∀ i, dmin ≤ deg A i) (hpos : 0 < dmin)
    (hdmax : ∀ i, deg A i ≤ dmax)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (t : ℝ) (ht : 0 ≤ t)
    (hfloor : 0 < dmin * cheegerConstant A ^ 2 / 2 - t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        perturbAdmissible A p dmin dmax ω ∧
        ¬ ((supportGraph (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))).Connected ∧
           ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
             ((∃ u : ℝ, ∀ i, i ∈ S ↔
                 u ≤ fiedlerSweepVector (A + perturbWeight A p ω)
                   (hA.add (perturbWeight_isSymm A p ω)) hcard i)
               ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                 fiedlerSweepVector (A + perturbWeight A p ω)
                   (hA.add (perturbWeight_isSymm A p ω)) hcard i ≤ u)) ∧
             conductance (A + perturbWeight A p ω) S ^ 2
               ≤ 2 * ((2 * (dmax * cheegerConstant A) + t) / dmin))}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖))) := by
  refine le_trans (measure_mono ?_)
    (edgePerturbation_normalized_connectivity_bracket A p hA hnn hd dmin dmax
      hdmin hpos hdmax hp0 hp1 hcard t ht)
  rintro ω ⟨hadm, hbad⟩
  refine ⟨hadm, ?_⟩
  by_contra hdisj
  push_neg at hdisj
  obtain ⟨i₀⟩ := ‹Nonempty V›
  have hd' : ∀ i, 0 < deg (A + perturbWeight A p ω) i :=
    fun i => lt_of_lt_of_le hpos (hadm.2.1 i)
  have hdmaxpos : 0 < dmax := lt_of_lt_of_le (hd' i₀) (hadm.2.2 i₀)
  have hfloorpos : 0 < (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax :=
    div_pos hfloor hdmaxpos
  have hpos₂ : 0 < secondEval (normalizedLaplacian (A + perturbWeight A p ω))
      (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) hcard :=
    lt_trans hfloorpos hdisj.1
  have hconn : (supportGraph (A + perturbWeight A p ω)
      (hA.add (perturbWeight_isSymm A p ω))).Connected :=
    (secondEval_normalizedLaplacian_pos_iff_connected
      (A + perturbWeight A p ω)
      (hA.add (perturbWeight_isSymm A p ω)) hadm.1 hd' hcard).1 hpos₂
  obtain ⟨S, hSne, hScne, hlev, hcond⟩ :=
    fiedler_sweep_cut_normalized (A + perturbWeight A p ω)
      (hA.add (perturbWeight_isSymm A p ω)) hadm.1 hd' hcard hconn
  refine hbad ⟨hconn, S, hSne, hScne, hlev, ?_⟩
  have h2c : (2 : ℝ) * secondEval (normalizedLaplacian (A + perturbWeight A p ω))
      (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
        (hA.add (perturbWeight_isSymm A p ω))) hcard
      ≤ 2 * ((2 * (dmax * cheegerConstant A) + t) / dmin) := by linarith
  exact le_trans hcond h2c

end NormalizedCheegerWindow

/-! ## The degree tail — `hoeffding_inequality`'s first theorem consumer

The scalar sibling of the assemblies above, at the *same* centered
Bernoulli edge-resampling design: the per-vertex degree-deviation tail.
Where the λ₂/norm tails control the operator (and carry zero degree
information — `L(E_ω)·1 = 0` identically), this controls the quantity the
irregular window family's admissibility story is made of: the resampled
degrees themselves, `μ {|deg G_ω v − deg A v| ≥ t} ≤ 2 exp(−t²/(2 S_v))`
at the variance statistic `S_v = ∑ₑ w_v(e)²` (both incident ordered
pairs counted — the double count is the design's honest price). No
hypothesis on the weight matrix (the design is sign-free); no dimension
prefactor (the scalar axiom's prefactor is the constant `2`, which
unlike the matrix trio's `2 · card V` never collapses at a degenerate
dimension — no `Nonempty` guard is needed here).
-/

section DegreeTail

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- **The per-vertex degree-deviation tail** — `hoeffding_inequality`
assembled at the degree design of `EdgePerturbation.lean`'s section 5:
on the product-Bernoulli space at inclusion probabilities `p ∈ [0, 1]`,
the deviation of any vertex's resampled degree from its base degree
obeys the classical two-sided exponential tail against the deterministic
variance statistic `∑ₑ w_v(e)²`. CONDITIONAL ON THE `hoeffding_inequality`
AXIOM: all four hypothesis clauses are proved at the design
(`measurable_degPerturbSummand`, `indepFun_degPerturbSummand`,
`degPerturbSummand_abs_le`, `integral_degPerturbSummand_eq_zero`). -/
theorem edgePerturbation_degree_tail (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (v : V) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          t ≤ |deg (A + perturbWeight A p ω) v - deg A v|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) := by
  haveI hprob : IsProbabilityMeasure (bernPMF p hp0 hp1).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hmeas : ∀ i : Fin (Fintype.card (V × V)),
      Measurable fun ω : (V × V) → Bool =>
        degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω :=
    fun i => measurable_degPerturbSummand A p v _
  have hindep : iIndepFun (fun _ : Fin (Fintype.card (V × V)) =>
      (inferInstance : MeasurableSpace ℝ))
      (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
        degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω)
      (bernPMF p hp0 hp1).toMeasure :=
    iIndepFun_degPerturbSummand A p hp0 hp1 v
  have hbound : ∀ (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool),
      |degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω|
        ≤ |degPerturbWeight A v ((Fintype.equivFin (V × V)).symm i)| :=
    fun i ω => degPerturbSummand_abs_le A p hp0 hp1 v _ ω
  have hmean : ∀ i : Fin (Fintype.card (V × V)),
      ∫ ω : (V × V) → Bool,
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
        ∂(bernPMF p hp0 hp1).toMeasure = 0 :=
    fun i => integral_degPerturbSummand_eq_zero A p hp0 hp1 v _
  have hmain := hoeffding_inequality
    (μ := (bernPMF p hp0 hp1).toMeasure)
    (X := fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
      degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω)
    (a := fun i => |degPerturbWeight A v ((Fintype.equivFin (V × V)).symm i)|)
    hmeas hindep hbound hmean t ht
  have hsum : ∀ ω : (V × V) → Bool,
      ∑ i : Fin (Fintype.card (V × V)),
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω) i ω
      = deg (A + perturbWeight A p ω) v - deg A v := fun ω => by
    rw [deg_resampled]
    rw [Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => degPerturbSummand A p v e ω)]
    ring
  have hseteq : {ω : (V × V) → Bool |
      t ≤ |∑ i : Fin (Fintype.card (V × V)),
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω) i ω|}
      = {ω : (V × V) → Bool |
          t ≤ |deg (A + perturbWeight A p ω) v - deg A v|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    exact Iff.of_eq (congrArg (fun S : ℝ => t ≤ |S|) (hsum ω))
  rw [hseteq] at hmain
  have hvar : ∑ i : Fin (Fintype.card (V × V)),
      (fun i => |degPerturbWeight A v ((Fintype.equivFin (V × V)).symm i)|) i ^ 2
      = ∑ e, (degPerturbWeight A v e) ^ 2 := by
    rw [Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => |degPerturbWeight A v e| ^ 2)]
    exact Finset.sum_congr rfl fun e _ => sq_abs _
  rw [hvar] at hmain
  exact hmain

/-- **The all-vertices degree-deviation tail** — the union bound over the
vertex set, stated at the exact per-vertex sum (each vertex keeps its own
variance statistic in the exponent). Collapsing to a uniform exponent
`2 |V| exp(−t²/(2B))` needs a per-vertex `0 < S_v ≤ B` (a vertex with
`S_v = 0` is pair-isolated — its deviation is identically zero, but
division-monotonicity is junk there); the collapse is left to consumers
whose graphs satisfy it, and demonstrated numerically in the QA at the
`K₂` fixture where both statistics are equal. CONDITIONAL ON THE
`hoeffding_inequality` AXIOM (the per-vertex tail above, union-bounded). -/
theorem edgePerturbation_degree_tail_all (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          ∃ v, t ≤ |deg (A + perturbWeight A p ω) v - deg A v|}
      ≤ ∑ v : V, ENNReal.ofReal (2 * Real.exp (-(t ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) := by
  have hcover : {ω : (V × V) → Bool |
      ∃ v, t ≤ |deg (A + perturbWeight A p ω) v - deg A v|}
      ⊆ ⋃ v : V, {ω : (V × V) → Bool |
        t ≤ |deg (A + perturbWeight A p ω) v - deg A v|} := by
    intro ω hω
    obtain ⟨v, hv⟩ := hω
    exact Set.mem_iUnion.2 ⟨v, hv⟩
  calc (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          ∃ v, t ≤ |deg (A + perturbWeight A p ω) v - deg A v|}
      ≤ (bernPMF p hp0 hp1).toMeasure
          (⋃ v : V, {ω : (V × V) → Bool |
            t ≤ |deg (A + perturbWeight A p ω) v - deg A v|}) :=
        measure_mono hcover
    _ ≤ ∑ v : V, (bernPMF p hp0 hp1).toMeasure
          {ω : (V × V) → Bool |
            t ≤ |deg (A + perturbWeight A p ω) v - deg A v|} :=
        measure_iUnion_fintype_le _ _
    _ ≤ ∑ v : V, ENNReal.ofReal (2 * Real.exp (-(t ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) :=
        Finset.sum_le_sum
          fun v _ => edgePerturbation_degree_tail A p hp0 hp1 v t ht

end DegreeTail

/-! ## The Bernstein twin — `bernstein_inequality`'s and
`bernstein_bounded_variance`'s first theorem consumers

The variance-adaptive siblings of the degree tails above, at the *same*
centered Bernoulli edge-resampling design: where Hoeffding's denominator
uses only the magnitude range `∑ₑ w_v(e)²`, Bernstein's uses the true
variance `σ²_v = ∑ₑ w_v(e)² p e (1 − p e)` — the quantity the design's
own second-moment engine (`integral_sq_degPerturbSummand`) computes
exactly — plus a linear term `2Mt/3` at a magnitude budget
`M ≥ |w_v(e)|` (the axiom's uniform-bound clause; at any fixture the
budget is the largest incident weight). At interior sampling
probabilities `σ²_v ≤ S_v/4` (each Bernoulli factor contributing
`p (1 − p) ≤ 1/4`), so at moderate `t` the Bernstein bound is strictly
sharper — pinned numerically in the QA (`epK2_bernstein_beats_hoeffding`).

Degenerate-corner analysis (recorded at delivery, 2026-08-29): the
scalar prefactor is again the constant `2`, never collapsing at a
degenerate dimension — no `Nonempty` guard is needed; at `t = 0` the
numerator `−t² = 0` makes the exponent `zero_div`-junk-free (`0/d = 0`,
bound `2 ≥ 1 ≥ μ(·)`) exactly as in the Hoeffding twin; at empty `V`
the theorems are vacuous in `v`; and the derived `0 ≤ M` is discharged
from `hM` at the incident pair `(v, v)`, so no spurious hypothesis is
carried.
-/

section BernsteinTwin

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- **The variance-adaptive per-vertex degree-deviation tail** —
`bernstein_inequality` assembled at the degree design of
`EdgePerturbation.lean`'s section 5: on the product-Bernoulli space at
inclusion probabilities `p ∈ [0, 1]`, the deviation of any vertex's
resampled degree from its base degree obeys the classical
variance-dependent tail against the *true* variance statistic
`σ²_v = ∑ₑ w_v(e)² p e (1 − p e)` and the magnitude budget
`M ≥ |w_v(e)|`. HARD CRUST since the 2026-08-30 Bernstein
repair-and-retirement (Errata §8): every hypothesis clause is proved at
the design (`measurable_degPerturbSummand`,
`indepFun_degPerturbSummand`, the centered bound through
`degPerturbSummand_abs_le` composed with `hM` and the proved zero means,
the variance statistic
through `integral_sq_degPerturbSummand` composed with the centering
`integral_degPerturbSummand_eq_zero`). -/
theorem edgePerturbation_degree_tail_bernstein (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (v : V) {M : ℝ}
    (hM : ∀ e, |degPerturbWeight A v e| ≤ M) (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          t ≤ |deg (A + perturbWeight A p ω) v - deg A v|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2 * p e * (1 - p e)
            + (2 * M * t) / 3))) := by
  haveI hprob : IsProbabilityMeasure (bernPMF p hp0 hp1).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hmeas : ∀ i : Fin (Fintype.card (V × V)),
      Measurable fun ω : (V × V) → Bool =>
        degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω :=
    fun i => measurable_degPerturbSummand A p v _
  have hindep : iIndepFun (fun _ : Fin (Fintype.card (V × V)) =>
      (inferInstance : MeasurableSpace ℝ))
      (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
        degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω)
      (bernPMF p hp0 hp1).toMeasure :=
    iIndepFun_degPerturbSummand A p hp0 hp1 v
  have hmean : ∀ i : Fin (Fintype.card (V × V)),
      ∫ ω : (V × V) → Bool,
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
        ∂(bernPMF p hp0 hp1).toMeasure = 0 :=
    fun i => integral_degPerturbSummand_eq_zero A p hp0 hp1 v _
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (v, v))
  have hbound : ∀ (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool),
      |degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
        - ∫ ω' : (V × V) → Bool,
            degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
          ∂(bernPMF p hp0 hp1).toMeasure| ≤ M :=
    fun i ω => by
      rw [hmean i, sub_zero]
      exact le_trans (degPerturbSummand_abs_le A p hp0 hp1 v _ ω)
        (hM ((Fintype.equivFin (V × V)).symm i))
  have hmain := bernstein_inequality
    (μ := (bernPMF p hp0 hp1).toMeasure)
    (X := fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
      degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω)
    (a := M) hM0 hmeas hindep hbound t ht
  -- the event: the centering drops through the proved zero means
  have hcenter : ∀ ω : (V × V) → Bool,
      ∑ i : Fin (Fintype.card (V × V)),
        (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
          - ∫ ω' : (V × V) → Bool,
              degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
            ∂(bernPMF p hp0 hp1).toMeasure)
      = ∑ i : Fin (Fintype.card (V × V)),
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω := by
    intro ω
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmean i, sub_zero]
  have hsum : ∀ ω : (V × V) → Bool,
      ∑ i : Fin (Fintype.card (V × V)),
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω) i ω
      = deg (A + perturbWeight A p ω) v - deg A v := fun ω => by
    rw [deg_resampled]
    rw [Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => degPerturbSummand A p v e ω)]
    ring
  have hseteq : {ω : (V × V) → Bool |
      t ≤ |∑ i : Fin (Fintype.card (V × V)),
        (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
          - ∫ ω' : (V × V) → Bool,
              degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
            ∂(bernPMF p hp0 hp1).toMeasure)|}
      = {ω : (V × V) → Bool |
          t ≤ |deg (A + perturbWeight A p ω) v - deg A v|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hcenter ω]
    exact Iff.of_eq (congrArg (fun S : ℝ => t ≤ |S|) (hsum ω))
  rw [hseteq] at hmain
  -- the variance sum: each centered second moment is w² p (1 − p)
  have hvar : ∑ i : Fin (Fintype.card (V × V)),
      ∫ ω : (V × V) → Bool,
          (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
            - ∫ ω' : (V × V) → Bool,
                degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
              ∂(bernPMF p hp0 hp1).toMeasure) ^ 2
        ∂(bernPMF p hp0 hp1).toMeasure
      = ∑ e, (degPerturbWeight A v e) ^ 2 * p e * (1 - p e) := by
    have hterm : ∀ i : Fin (Fintype.card (V × V)),
        ∫ ω : (V × V) → Bool,
            (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
              - ∫ ω' : (V × V) → Bool,
                  degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
                ∂(bernPMF p hp0 hp1).toMeasure) ^ 2
          ∂(bernPMF p hp0 hp1).toMeasure
        = (degPerturbWeight A v ((Fintype.equivFin (V × V)).symm i)) ^ 2
          * p ((Fintype.equivFin (V × V)).symm i)
          * (1 - p ((Fintype.equivFin (V × V)).symm i)) := by
      intro i
      have hfn : (fun ω : (V × V) → Bool =>
          (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
            - ∫ ω' : (V × V) → Bool,
                degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
              ∂(bernPMF p hp0 hp1).toMeasure) ^ 2)
          = fun ω : (V × V) → Bool =>
            (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω) ^ 2 := by
        funext ω
        rw [hmean i, sub_zero]
      rw [hfn]
      exact integral_sq_degPerturbSummand A p hp0 hp1 v _
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    exact Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => (degPerturbWeight A v e) ^ 2 * p e * (1 - p e))
  rw [hvar] at hmain
  exact hmain

/-- **The budget form of the variance-adaptive degree tail** —
`bernstein_bounded_variance` assembled at the same design: any supplied
variance budget `Vbud` dominating the true statistic `σ²_v` and the
same magnitude budget `M` give the tail with `2 Vbud` in place of
`2 σ²_v`. HARD CRUST since the 2026-08-30 Bernstein
repair-and-retirement (Errata §8; the budget relaxation is honest by
monotonicity of the exponent — pinned numerically in the QA). -/
theorem edgePerturbation_degree_tail_bernstein_budget (hp0 : ∀ e, 0 ≤ p e)
    (hp1 : ∀ e, p e ≤ 1) (v : V) {M Vbud : ℝ}
    (hM : ∀ e, |degPerturbWeight A v e| ≤ M)
    (hvar : ∑ e, (degPerturbWeight A v e) ^ 2 * p e * (1 - p e) ≤ Vbud)
    (t : ℝ) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          t ≤ |deg (A + perturbWeight A p ω) v - deg A v|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * Vbud + (2 * M * t) / 3))) := by
  haveI hprob : IsProbabilityMeasure (bernPMF p hp0 hp1).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hmeas : ∀ i : Fin (Fintype.card (V × V)),
      Measurable fun ω : (V × V) → Bool =>
        degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω :=
    fun i => measurable_degPerturbSummand A p v _
  have hindep : iIndepFun (fun _ : Fin (Fintype.card (V × V)) =>
      (inferInstance : MeasurableSpace ℝ))
      (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
        degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω)
      (bernPMF p hp0 hp1).toMeasure :=
    iIndepFun_degPerturbSummand A p hp0 hp1 v
  have hmean : ∀ i : Fin (Fintype.card (V × V)),
      ∫ ω : (V × V) → Bool,
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
        ∂(bernPMF p hp0 hp1).toMeasure = 0 :=
    fun i => integral_degPerturbSummand_eq_zero A p hp0 hp1 v _
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (v, v))
  have hbound : ∀ (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool),
      |degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
        - ∫ ω' : (V × V) → Bool,
            degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
          ∂(bernPMF p hp0 hp1).toMeasure| ≤ M :=
    fun i ω => by
      rw [hmean i, sub_zero]
      exact le_trans (degPerturbSummand_abs_le A p hp0 hp1 v _ ω)
        (hM ((Fintype.equivFin (V × V)).symm i))
  have hvarax : ∑ i : Fin (Fintype.card (V × V)),
      ∫ ω : (V × V) → Bool,
          (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
            - ∫ ω' : (V × V) → Bool,
                degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
              ∂(bernPMF p hp0 hp1).toMeasure) ^ 2
        ∂(bernPMF p hp0 hp1).toMeasure
      ≤ Vbud := by
    have hterm : ∀ i : Fin (Fintype.card (V × V)),
        ∫ ω : (V × V) → Bool,
            (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
              - ∫ ω' : (V × V) → Bool,
                  degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
                ∂(bernPMF p hp0 hp1).toMeasure) ^ 2
          ∂(bernPMF p hp0 hp1).toMeasure
        = (degPerturbWeight A v ((Fintype.equivFin (V × V)).symm i)) ^ 2
          * p ((Fintype.equivFin (V × V)).symm i)
          * (1 - p ((Fintype.equivFin (V × V)).symm i)) := by
      intro i
      have hfn : (fun ω : (V × V) → Bool =>
          (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
            - ∫ ω' : (V × V) → Bool,
                degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
              ∂(bernPMF p hp0 hp1).toMeasure) ^ 2)
          = fun ω : (V × V) → Bool =>
            (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω) ^ 2 := by
        funext ω
        rw [hmean i, sub_zero]
      rw [hfn]
      exact integral_sq_degPerturbSummand A p hp0 hp1 v _
    rw [Finset.sum_congr rfl (fun i _ => hterm i),
      Equiv.sum_comp (Fintype.equivFin (V × V)).symm
        (fun e : V × V => (degPerturbWeight A v e) ^ 2 * p e * (1 - p e))]
    exact hvar
  have hmain := bernstein_bounded_variance
    (μ := (bernPMF p hp0 hp1).toMeasure)
    (X := fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
      degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω)
    (a := M) (v := Vbud) hM0 hmeas hindep hbound hvarax t ht
  have hcenter : ∀ ω : (V × V) → Bool,
      ∑ i : Fin (Fintype.card (V × V)),
        (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
          - ∫ ω' : (V × V) → Bool,
              degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
            ∂(bernPMF p hp0 hp1).toMeasure)
      = ∑ i : Fin (Fintype.card (V × V)),
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω := by
    intro ω
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmean i, sub_zero]
  have hsum : ∀ ω : (V × V) → Bool,
      ∑ i : Fin (Fintype.card (V × V)),
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω) i ω
      = deg (A + perturbWeight A p ω) v - deg A v := fun ω => by
    rw [deg_resampled]
    rw [Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => degPerturbSummand A p v e ω)]
    ring
  have hseteq : {ω : (V × V) → Bool |
      t ≤ |∑ i : Fin (Fintype.card (V × V)),
        (degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω
          - ∫ ω' : (V × V) → Bool,
              degPerturbSummand A p v ((Fintype.equivFin (V × V)).symm i) ω'
            ∂(bernPMF p hp0 hp1).toMeasure)|}
      = {ω : (V × V) → Bool |
          t ≤ |deg (A + perturbWeight A p ω) v - deg A v|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hcenter ω]
    exact Iff.of_eq (congrArg (fun S : ℝ => t ≤ |S|) (hsum ω))
  rw [hseteq] at hmain
  exact hmain

end BernsteinTwin

/-! ## The admissibility dissolution — the unconditional window family

The window family's recorded honesty note — "the admissibility window
is proof-load-bearing, not fixture-refuted" — stood because every
measured event *conditioned* on `perturbAdmissible`. This section
dissolves that conjunct on both halves at once (the degree-concentration
proposal's priced follow-on, 2026-08-29): the nonnegativity half is
*derived* from the pair design condition `p e + p (e.2, e.1) ≤ 1`
(satisfied with equality by the uniform design `p ≡ ½`) through the
engine lemma `perturbWeight_entry_nonneg`, and the degree half from
base degrees in a shrunk window `[dmin + s, dmax − s]` plus the
delivered all-vertices degree tail: an outcome with every per-vertex
deviation strictly below `s` keeps the resampled degrees in
`[dmin, dmax]`. The result is the family's first measured event with no
admissibility conjunct — the window statement a consumer can read
unconditionally, at the price of one extra tail term.

The same-day completion applies the identical decomposition to the
family's other two members: the floor theorem and the swept-Fiedler-cut
capstone now have their own unconditional forms, so the *whole*
window family — floor, bracket, swept cut — is stated without a
conditioning event. Each is a two-axiom member (`matrix_hoeffding`
through the conditional window theorem, `hoeffding_inequality` through
the degree tail), honestly so; the transfer, the engine lemma, and the
union-bound arithmetic are proved hard crust. -/

section AdmissibilityDissolution

variable (A : WAdj (V := V)) (p : (V × V) → ℝ)

/-- **The degree-window transfer**: base degrees in the shrunk window
`[dmin + s, dmax − s]` plus per-vertex deviations strictly below `s` put
the outcome inside the admissibility window `[dmin, dmax]` — the
nonnegativity conjunct from the pair design condition, the degree
conjuncts from the shrunk window and the strict deviation bound (the
strictness carries `s`'s sign implicitly, so no separate `0 ≤ s`
hypothesis). Load-bearing on the engine lemma `perturbWeight_entry_nonneg`
and the entry formulas: a wrong off-diagonal entry shape breaks the
nonnegativity half exactly. -/
theorem perturbAdmissible_of_degDev_lt (A : WAdj (V := V)) (p : (V × V) → ℝ)
    (hA : A.IsSymm) (hnn : ∀ i j, 0 ≤ A i j) (hp1 : ∀ e, p e ≤ 1)
    (hpd : ∀ e, p e + p (e.2, e.1) ≤ 1)
    (dmin dmax s : ℝ)
    (hdmin : ∀ i, dmin + s ≤ deg A i) (hdmax : ∀ i, deg A i ≤ dmax - s)
    {ω : (V × V) → Bool}
    (hdev : ∀ v, |deg (A + perturbWeight A p ω) v - deg A v| < s) :
    perturbAdmissible A p dmin dmax ω := by
  refine ⟨fun i j => perturbWeight_entry_nonneg A p hA hnn hp1 hpd ω i j,
    ?_, ?_⟩
  · intro v
    have h := abs_lt.1 (hdev v)
    have hdg : deg (A + perturbWeight A p ω) v
        = deg A v + (deg (A + perturbWeight A p ω) v - deg A v) := by ring
    rw [hdg]
    linarith [hdmin v]
  · intro v
    have h := abs_lt.1 (hdev v)
    have hdg : deg (A + perturbWeight A p ω) v
        = deg A v + (deg (A + perturbWeight A p ω) v - deg A v) := by ring
    rw [hdg]
    linarith [hdmax v]

/-- **The unconditional connectivity bracket — the admissibility
dissolution**: the window family's first measured event with *no
admissibility conjunct*. On a symmetric nonnegative base graph whose
degrees sit in the shrunk window `[dmin + s, dmax − s]` (`0 < dmin`), at
the pair design condition, leaving the two-sided
normalized-connectivity window

`[(dmin·φ(A)²/2 − t)/dmax, (2·dmax·φ(A) + t)/dmin]`

has probability at most the window tail at `t` plus the all-vertices
degree tail at `s`:

`μ {λ₂(L_sym G_ω) below floor ∨ above ceiling} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))
  + ∑_v 2 exp(−s²/(2 S_v))`.

The decomposition: every outcome either has some vertex deviation `≥ s`
(the degree tail's event) or has all deviations `< s`, in which case the
transfer helper makes it admissible and the delivered bracket's event
applies. Both tails are load-bearing — the window half through the
sandwich and the irregular Cheeger pair, the degree half through the
degree-design's clause lemmas. CONDITIONAL ON THE `matrix_hoeffding`
AXIOM (via the bracket) AND THE `hoeffding_inequality` AXIOM (via the
degree tail) — the family's only two-axiom member, honestly so: the
dissolution consumes one tail of each kind; the transfer, the engine
lemma, and the degree-window arithmetic are proved hard crust. The
`s = 0` degeneration is harmless (the deviation event becomes all of
`Ω`, the bound vacuous but true); `hcard : 2 ≤ card V` fences the empty
index type. -/
theorem edgePerturbation_normalized_connectivity_bracket_unconditional
    (A : WAdj (V := V)) (p : (V × V) → ℝ) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j)
    (dmin dmax s t : ℝ) (hpos : 0 < dmin) (hs : 0 ≤ s)
    (hdmin : ∀ i, dmin + s ≤ deg A i) (hdmax : ∀ i, deg A i ≤ dmax - s)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hpd : ∀ e, p e + p (e.2, e.1) ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        (secondEval (normalizedLaplacian (A + perturbWeight A p ω))
            (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) hcard
          ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax
        ∨ (2 * (dmax * cheegerConstant A) + t) / dmin
          ≤ secondEval (normalizedLaplacian (A + perturbWeight A p ω))
              (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                (hA.add (perturbWeight_isSymm A p ω))) hcard)}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖)))
        + ∑ v : V, ENNReal.ofReal (2 * Real.exp (-(s ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) := by
  have hd : ∀ i, 0 < deg A i := fun i =>
    lt_of_lt_of_le hpos (le_trans (by linarith) (hdmin i))
  have hdmin' : ∀ i, dmin ≤ deg A i := fun i =>
    le_trans (by linarith) (hdmin i)
  have hdmax' : ∀ i, deg A i ≤ dmax := fun i =>
    le_trans (hdmax i) (by linarith)
  have hsplit : {ω : (V × V) → Bool |
      (secondEval (normalizedLaplacian (A + perturbWeight A p ω))
            (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) hcard
          ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax
        ∨ (2 * (dmax * cheegerConstant A) + t) / dmin
          ≤ secondEval (normalizedLaplacian (A + perturbWeight A p ω))
              (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                (hA.add (perturbWeight_isSymm A p ω))) hcard)}
      ⊆ {ω : (V × V) → Bool |
          perturbAdmissible A p dmin dmax ω ∧
          (secondEval (normalizedLaplacian (A + perturbWeight A p ω))
            (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) hcard
            ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax
          ∨ (2 * (dmax * cheegerConstant A) + t) / dmin
            ≤ secondEval (normalizedLaplacian (A + perturbWeight A p ω))
                (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                  (hA.add (perturbWeight_isSymm A p ω))) hcard)}
        ∪ {ω : (V × V) → Bool |
          ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|} := by
    intro ω hω
    by_cases hdev : ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|
    · exact Or.inr hdev
    · refine Or.inl ⟨?_, hω⟩
      push_neg at hdev
      exact perturbAdmissible_of_degDev_lt A p hA hnn hp1 hpd dmin dmax s
        hdmin hdmax hdev
  calc (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          (secondEval (normalizedLaplacian (A + perturbWeight A p ω))
            (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) hcard
            ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax
          ∨ (2 * (dmax * cheegerConstant A) + t) / dmin
            ≤ secondEval (normalizedLaplacian (A + perturbWeight A p ω))
                (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                  (hA.add (perturbWeight_isSymm A p ω))) hcard)}
      ≤ (bernPMF p hp0 hp1).toMeasure
          ({ω : (V × V) → Bool |
              perturbAdmissible A p dmin dmax ω ∧
              (secondEval (normalizedLaplacian (A + perturbWeight A p ω))
                (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                  (hA.add (perturbWeight_isSymm A p ω))) hcard
                ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax
              ∨ (2 * (dmax * cheegerConstant A) + t) / dmin
                ≤ secondEval (normalizedLaplacian (A + perturbWeight A p ω))
                    (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                      (hA.add (perturbWeight_isSymm A p ω))) hcard)}
            ∪ {ω : (V × V) → Bool |
              ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|}) :=
        measure_mono hsplit
    _ ≤ (bernPMF p hp0 hp1).toMeasure
          {ω : (V × V) → Bool |
            perturbAdmissible A p dmin dmax ω ∧
            (secondEval (normalizedLaplacian (A + perturbWeight A p ω))
              (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                (hA.add (perturbWeight_isSymm A p ω))) hcard
              ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax
            ∨ (2 * (dmax * cheegerConstant A) + t) / dmin
              ≤ secondEval (normalizedLaplacian (A + perturbWeight A p ω))
                  (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                    (hA.add (perturbWeight_isSymm A p ω))) hcard)}
        + (bernPMF p hp0 hp1).toMeasure
          {ω : (V × V) → Bool |
            ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖)))
        + ∑ v : V, ENNReal.ofReal (2 * Real.exp (-(s ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) :=
        add_le_add
          (edgePerturbation_normalized_connectivity_bracket A p hA hnn hd
            dmin dmax hdmin' hpos hdmax' hp0 hp1 hcard t ht)
          (edgePerturbation_degree_tail_all A p hp0 hp1 s hs)

/-- **The unconditional normalized Cheeger floor — the admissibility
dissolution, floor member**: the decomposition's second application.
On a symmetric nonnegative base graph whose degrees sit in the shrunk
window `[dmin + s, dmax − s]` (`0 < dmin`), at the pair design
condition, the *unconditioned* floor event —

`μ {λ₂(L_sym G_ω) ≤ (dmin·φ(A)²/2 − t)/dmax} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))
  + ∑_v 2 exp(−s²/(2 S_v))`.

Every outcome either has some vertex deviation `≥ s` (the degree tail's
event) or has all deviations `< s`, in which case the transfer helper
makes it admissible and the delivered floor theorem's event applies.
CONDITIONAL ON THE `matrix_hoeffding` AXIOM (via the floor) AND THE
`hoeffding_inequality` AXIOM (via the degree tail); the decomposition
is proved hard crust. `s = 0` harmless, `hcard` fences the empty index
type, exactly as in the bracket member. -/
theorem edgePerturbation_normalized_cheeger_floor_unconditional
    (A : WAdj (V := V)) (p : (V × V) → ℝ) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j)
    (dmin dmax s t : ℝ) (hpos : 0 < dmin) (hs : 0 ≤ s)
    (hdmin : ∀ i, dmin + s ≤ deg A i) (hdmax : ∀ i, deg A i ≤ dmax - s)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hpd : ∀ e, p e + p (e.2, e.1) ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (ht : 0 ≤ t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        secondEval (normalizedLaplacian (A + perturbWeight A p ω))
            (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) hcard
          ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖)))
        + ∑ v : V, ENNReal.ofReal (2 * Real.exp (-(s ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) := by
  have hd : ∀ i, 0 < deg A i := fun i =>
    lt_of_lt_of_le hpos (le_trans (by linarith) (hdmin i))
  have hdmin' : ∀ i, dmin ≤ deg A i := fun i =>
    le_trans (by linarith) (hdmin i)
  have hsplit : {ω : (V × V) → Bool |
      secondEval (normalizedLaplacian (A + perturbWeight A p ω))
            (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))) hcard
          ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax}
      ⊆ {ω : (V × V) → Bool |
          perturbAdmissible A p dmin dmax ω ∧
          secondEval (normalizedLaplacian (A + perturbWeight A p ω))
              (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                (hA.add (perturbWeight_isSymm A p ω))) hcard
            ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax}
        ∪ {ω : (V × V) → Bool |
          ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|} := by
    intro ω hω
    by_cases hdev : ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|
    · exact Or.inr hdev
    · refine Or.inl ⟨?_, hω⟩
      push_neg at hdev
      exact perturbAdmissible_of_degDev_lt A p hA hnn hp1 hpd dmin dmax s
        hdmin hdmax hdev
  calc (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          secondEval (normalizedLaplacian (A + perturbWeight A p ω))
              (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                (hA.add (perturbWeight_isSymm A p ω))) hcard
            ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax}
      ≤ (bernPMF p hp0 hp1).toMeasure
          ({ω : (V × V) → Bool |
              perturbAdmissible A p dmin dmax ω ∧
              secondEval (normalizedLaplacian (A + perturbWeight A p ω))
                  (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                    (hA.add (perturbWeight_isSymm A p ω))) hcard
                ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax}
            ∪ {ω : (V × V) → Bool |
              ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|}) :=
        measure_mono hsplit
    _ ≤ (bernPMF p hp0 hp1).toMeasure
          {ω : (V × V) → Bool |
            perturbAdmissible A p dmin dmax ω ∧
            secondEval (normalizedLaplacian (A + perturbWeight A p ω))
                (normalizedLaplacian_symmetric (A + perturbWeight A p ω)
                  (hA.add (perturbWeight_isSymm A p ω))) hcard
              ≤ (dmin * cheegerConstant A ^ 2 / 2 - t) / dmax}
        + (bernPMF p hp0 hp1).toMeasure
          {ω : (V × V) → Bool |
            ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖)))
        + ∑ v : V, ENNReal.ofReal (2 * Real.exp (-(s ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) :=
        add_le_add
          (edgePerturbation_normalized_cheeger_floor A p hA hnn hd
            dmin dmax hdmin' hpos hp0 hp1 hcard t ht)
          (edgePerturbation_degree_tail_all A p hp0 hp1 s hs)

/-- **The unconditional swept-Fiedler-cut tail — the admissibility
dissolution, capstone member**: the decomposition's third application,
completing the window family. At the same shrunk-window/pair-condition
stack plus the floor-positivity guard (`0 < dmin·φ²/2 − t`), the
failure of the good outcome — the resampled graph disconnected, or
connected with no swept level set of its own Fiedler sweep vector at

`conductance G_ω S² ≤ 2 · (2·dmax·φ(A) + t)/dmin`

— is bounded by the window tail at `t` plus the degree tail at `s`,
with **no conditioning event**: an unconditioned high-probability
algorithmic output under random edge resampling. CONDITIONAL ON THE
`matrix_hoeffding` AXIOM (via the swept-cut tail) AND THE
`hoeffding_inequality` AXIOM (via the degree tail); the decomposition
is proved hard crust. The floor-positivity guard remains
proof-load-bearing exactly as in the conditional capstone (its
dropped-guard refutation fixture, `epC4_sweepWindow_unguarded_refuted_QA`,
carries over verbatim: the guard is a hypothesis of both members). -/
theorem edgePerturbation_fiedler_sweep_cut_tail_unconditional
    (A : WAdj (V := V)) (p : (V × V) → ℝ) (hA : A.IsSymm)
    (hnn : ∀ i j, 0 ≤ A i j)
    (dmin dmax s t : ℝ) (hpos : 0 < dmin) (hs : 0 ≤ s)
    (hdmin : ∀ i, dmin + s ≤ deg A i) (hdmax : ∀ i, deg A i ≤ dmax - s)
    (hp0 : ∀ e, 0 ≤ p e) (hp1 : ∀ e, p e ≤ 1)
    (hpd : ∀ e, p e + p (e.2, e.1) ≤ 1) [Nonempty V]
    (hcard : 2 ≤ Fintype.card V) (ht : 0 ≤ t)
    (hfloor : 0 < dmin * cheegerConstant A ^ 2 / 2 - t) :
    (bernPMF p hp0 hp1).toMeasure
      {ω : (V × V) → Bool |
        ¬ ((supportGraph (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))).Connected ∧
           ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
             ((∃ u : ℝ, ∀ i, i ∈ S ↔
                 u ≤ fiedlerSweepVector (A + perturbWeight A p ω)
                   (hA.add (perturbWeight_isSymm A p ω)) hcard i)
               ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                 fiedlerSweepVector (A + perturbWeight A p ω)
                   (hA.add (perturbWeight_isSymm A p ω)) hcard i ≤ u)) ∧
             conductance (A + perturbWeight A p ω) S ^ 2
               ≤ 2 * ((2 * (dmax * cheegerConstant A) + t) / dmin))}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖)))
        + ∑ v : V, ENNReal.ofReal (2 * Real.exp (-(s ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) := by
  have hd : ∀ i, 0 < deg A i := fun i =>
    lt_of_lt_of_le hpos (le_trans (by linarith) (hdmin i))
  have hdmin' : ∀ i, dmin ≤ deg A i := fun i =>
    le_trans (by linarith) (hdmin i)
  have hdmax' : ∀ i, deg A i ≤ dmax := fun i =>
    le_trans (hdmax i) (by linarith)
  have hsplit : {ω : (V × V) → Bool |
      ¬ ((supportGraph (A + perturbWeight A p ω)
              (hA.add (perturbWeight_isSymm A p ω))).Connected ∧
           ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
             ((∃ u : ℝ, ∀ i, i ∈ S ↔
                 u ≤ fiedlerSweepVector (A + perturbWeight A p ω)
                   (hA.add (perturbWeight_isSymm A p ω)) hcard i)
               ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                 fiedlerSweepVector (A + perturbWeight A p ω)
                   (hA.add (perturbWeight_isSymm A p ω)) hcard i ≤ u)) ∧
             conductance (A + perturbWeight A p ω) S ^ 2
               ≤ 2 * ((2 * (dmax * cheegerConstant A) + t) / dmin))}
      ⊆ ({ω : (V × V) → Bool |
            perturbAdmissible A p dmin dmax ω ∧
            ¬ ((supportGraph (A + perturbWeight A p ω)
                  (hA.add (perturbWeight_isSymm A p ω))).Connected ∧
               ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
                 ((∃ u : ℝ, ∀ i, i ∈ S ↔
                     u ≤ fiedlerSweepVector (A + perturbWeight A p ω)
                       (hA.add (perturbWeight_isSymm A p ω)) hcard i)
                   ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                     fiedlerSweepVector (A + perturbWeight A p ω)
                       (hA.add (perturbWeight_isSymm A p ω)) hcard i ≤ u)) ∧
                 conductance (A + perturbWeight A p ω) S ^ 2
                   ≤ 2 * ((2 * (dmax * cheegerConstant A) + t) / dmin))}
          ∪ {ω : (V × V) → Bool |
            ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|}) := by
    intro ω hω
    by_cases hdev : ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|
    · exact Or.inr hdev
    · refine Or.inl ⟨?_, hω⟩
      push_neg at hdev
      exact perturbAdmissible_of_degDev_lt A p hA hnn hp1 hpd dmin dmax s
        hdmin hdmax hdev
  calc (bernPMF p hp0 hp1).toMeasure
        {ω : (V × V) → Bool |
          ¬ ((supportGraph (A + perturbWeight A p ω)
                (hA.add (perturbWeight_isSymm A p ω))).Connected ∧
             ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
               ((∃ u : ℝ, ∀ i, i ∈ S ↔
                   u ≤ fiedlerSweepVector (A + perturbWeight A p ω)
                     (hA.add (perturbWeight_isSymm A p ω)) hcard i)
                 ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                   fiedlerSweepVector (A + perturbWeight A p ω)
                     (hA.add (perturbWeight_isSymm A p ω)) hcard i ≤ u)) ∧
               conductance (A + perturbWeight A p ω) S ^ 2
                 ≤ 2 * ((2 * (dmax * cheegerConstant A) + t) / dmin))}
      ≤ (bernPMF p hp0 hp1).toMeasure
          ({ω : (V × V) → Bool |
              perturbAdmissible A p dmin dmax ω ∧
              ¬ ((supportGraph (A + perturbWeight A p ω)
                    (hA.add (perturbWeight_isSymm A p ω))).Connected ∧
                 ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
                   ((∃ u : ℝ, ∀ i, i ∈ S ↔
                       u ≤ fiedlerSweepVector (A + perturbWeight A p ω)
                         (hA.add (perturbWeight_isSymm A p ω)) hcard i)
                     ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                       fiedlerSweepVector (A + perturbWeight A p ω)
                         (hA.add (perturbWeight_isSymm A p ω)) hcard i ≤ u)) ∧
                   conductance (A + perturbWeight A p ω) S ^ 2
                     ≤ 2 * ((2 * (dmax * cheegerConstant A) + t) / dmin))}
            ∪ {ω : (V × V) → Bool |
              ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|}) :=
        measure_mono hsplit
    _ ≤ (bernPMF p hp0 hp1).toMeasure
          {ω : (V × V) → Bool |
            perturbAdmissible A p dmin dmax ω ∧
            ¬ ((supportGraph (A + perturbWeight A p ω)
                  (hA.add (perturbWeight_isSymm A p ω))).Connected ∧
               ∃ S : Finset V, S.Nonempty ∧ Sᶜ.Nonempty ∧
                 ((∃ u : ℝ, ∀ i, i ∈ S ↔
                     u ≤ fiedlerSweepVector (A + perturbWeight A p ω)
                       (hA.add (perturbWeight_isSymm A p ω)) hcard i)
                   ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                     fiedlerSweepVector (A + perturbWeight A p ω)
                       (hA.add (perturbWeight_isSymm A p ω)) hcard i ≤ u)) ∧
                 conductance (A + perturbWeight A p ω) S ^ 2
                   ≤ 2 * ((2 * (dmax * cheegerConstant A) + t) / dmin))}
        + (bernPMF p hp0 hp1).toMeasure
          {ω : (V × V) → Bool |
            ∃ v, s ≤ |deg (A + perturbWeight A p ω) v - deg A v|} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) * Real.exp (-(t ^ 2) /
          (2 * ‖∑ e : V × V, perturbEdgeLap A e * perturbEdgeLap A e‖)))
        + ∑ v : V, ENNReal.ofReal (2 * Real.exp (-(s ^ 2)
          / (2 * ∑ e, (degPerturbWeight A v e) ^ 2))) :=
        add_le_add
          (edgePerturbation_fiedler_sweep_cut_tail A p hA hnn hd
            dmin dmax hdmin' hpos hdmax' hp0 hp1 hcard t ht hfloor)
          (edgePerturbation_degree_tail_all A p hp0 hp1 s hs)

end AdmissibilityDissolution

end Scaffold.Derived.EdgePerturbationTail
