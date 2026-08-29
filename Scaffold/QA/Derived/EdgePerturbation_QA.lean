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
  - the eigenvalue-level tail's QA (the spectral-gap section): the base
    and perturbed `K₂` spectra pinned exactly (`λ₂ = 2`; `λ₂ = 4` at the
    all-true outcome, where the resampled graph is the weight-`2` edge),
    the Weyl transfer *tight* at that genuine design outcome
    (`|4 − 2| = ‖L(E_ω)‖ = 2`, both sides by independent routes), the
    closed-form eigenvalue/λ₂/uniform-form instances on `K₂` and the
    three-path (`4 exp(−1/16)`, `6 exp(−1/24)`), and the `x = 0` guard
    fence — the un-guarded uniform event is all of `Ω`, refuting the
    un-guarded bound in proved arithmetic at `t = 7`. The tail instances
    are conditional on the `matrix_hoeffding` axiom via the new theorems,
    not proofs of it.
  - the sharpened (matched-threshold) drift interface's QA: the envelope
    arithmetic of the `s/(γ−s)` parametrization pinned in general
    (domination `t ≤ γt/(t+δ)`; same-threshold identity
    `(γt/(t+δ))/(γ−γt/(t+δ)) = t/δ`) and at the concrete naive instance
    `(1, ½)` of `γ = 2`, the closed-form three-path instances at the
    join point (`6 exp(−1/24)`, subspace and line variants) and at the
    non-trivial threshold `2` (`6 exp(−2/27)`), the naive
    delivered-theorem instance at threshold `2` (`6 exp(−1/24)`), and
    the strict-improvement pin `6 exp(−2/27) < 6 exp(−1/24)`. The
    sharpened instances are conditional on the `matrix_hoeffding` axiom
    via the sharpened theorems, not proofs of it.
  - the swept-Fiedler-cut consumer's QA (the sweepWindow section): the
    all-true `K₂` outcome provably *not* in the measured event (its
    resampled graph connected by a raw walk witness, and carrying a
    swept Fiedler cut at `conductance² ≤ 2·λ₂ = 4` — the deterministic
    sweep theorem at the pinned spectrum, well inside the window bound),
    and the closed-form tail instances on `K₂` (`4 exp(−1/4096)`) and
    the three-path (`6 exp(−1/6144)`) at `t = 1/16`, where the floor
    hypothesis `0 < 1/2·φ²/2 − 1/16 = 1/16` genuinely holds. The tail
    instances are conditional on the `matrix_hoeffding` axiom via the
    new theorem, not proofs of it. Honesty note: the floor-positivity
    guard is proof-load-bearing, not fixture-refutable — the same
    junk-measure obstruction as the window family (at 2–3 vertices the
    tail bound exceeds `1`, so no un-guarded instance can be refuted).
  - the degenerate-degree corner audit (the cornerAudit section): the
    parked spike-level finding of the window family's honesty notes
    settled in proved form — at the all-false `K₂` outcome (zero
    degrees) the normalized Laplacian is the identity and its `λ₂` is
    exactly `1` (`evals_one`), *not* the zero matrix's `0` that the
    combinatorial Laplacian's `λ₂ = 0` beside it might suggest — the
    two junk spectra exhibited as one proved contrast; the negative-
    degree corner (the `p ≡ 1` all-false outcome's resampled adjacency
    is the negative edge, degrees `-1 < 0`) lands on the same identity
    junk; the honesty note's floor-condition mechanism ("keeps the
    un-windowed floor condition false") pinned as a proved instance; and
    the `degreeInvSqrt` vanishing iff exercised on both sides at one
    fixture pair. All hard crust, standard three axioms only.
  - the Bernstein twin (the bernsteinTwin section): the
    variance-adaptive degree tails' QA — the true variance statistic
    pinned exactly (`σ²₀ = ½` on `K₂` at the fair coin) with the
    Poisson-trial shape (`∑ w² p = 1`) refuted and the fourfold
    variance reduction pinned as an equation (`σ²₀ = S₀/4`); the
    strict variance-adaptivity improvement *proved*
    (`2 exp(−3/5) < 2 exp(−1/4)`: the Bernstein bound beats the
    delivered Hoeffding bound at the same fixture and threshold); the
    budget relaxation pinned honest (`≤`); and the two closed-form
    conditional tail instances. The hard-crust lemmas are standard
    three axioms only; the two instances honestly carry their
    respective axioms.
-/

import Scaffold.Derived.EdgePerturbationTail
import Scaffold.Derived.EdgePerturbationDrift
import Scaffold.QA.SpectralGraph.Fiedler_QA
import Scaffold.QA.SpectralGraph.Cheeger_QA
import Scaffold.QA.SpectralGraph.IrregularCheeger_QA

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

/-! ## The eigenvalue-level tail -/

/-! ### The `K₂` eigenvalue stack -/

theorem epK2_symmetric : epK2.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [epK2]

theorem epK2_nonneg (i j : Fin 2) : 0 ≤ epK2 i j := by
  fin_cases i <;> fin_cases j <;> simp [epK2]

theorem epK2_diag (i : Fin 2) : epK2 i i = 0 := by
  fin_cases i <;> simp [epK2]

/-- The base λ₂ on `K₂` is exactly `2`: the kernel eigenvalue is `0`
(proved zero-eigenvalue pin at the nonnegative weights) and the trace is
`2` (both degrees `1`), so the sorted second entry is forced. -/
theorem epK2_evals_one_eq_two_QA :
    evals (laplacian_symmetric epK2 epK2_symmetric) ⟨1, by norm_num⟩ = 2 := by
  have h0 : evals (laplacian_symmetric epK2 epK2_symmetric) (0 : Fin 2) = 0 :=
    laplacian_evals_zero epK2 epK2_symmetric epK2_nonneg (by norm_num)
  have hsum := evals_sum_eq_trace (laplacian_symmetric epK2 epK2_symmetric)
  have htrace : (laplacian epK2).trace = 2 := by
    have hdiag : ∀ i : Fin 2, (laplacian epK2) i i = 1 := by
      intro i
      have hdeg : deg epK2 i = 1 := by
        fin_cases i <;> simp [deg, epK2, Fin.sum_univ_two]
      rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal,
        hdeg, epK2_diag i, sub_zero]
    rw [show (laplacian epK2).trace = ∑ i, (laplacian epK2) i i from rfl,
      Finset.sum_congr rfl fun i _ => hdiag i]
    simp [Fin.sum_univ_two]
  rw [htrace] at hsum
  have h2 : ∑ i : Fin 2,
      evals (laplacian_symmetric epK2 epK2_symmetric) i = 2 := hsum
  simp only [Fin.sum_univ_two] at h2
  have h1' : evals (laplacian_symmetric epK2 epK2_symmetric) (1 : Fin 2) = 2 := by
    linarith
  exact h1'

/-- The perturbed graph at the all-true outcome is the weight-`2` edge:
`A + E_ω = 2 • A` entrywise (the raw weight-space route joined to the
existing `perturbWeight` pin). -/
theorem epK2_perturbed_allTrue_eq :
    epK2 + perturbWeight epK2 epHalf (fun _ => true)
      = (2 : ℝ) • epK2 := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    show perturbWeight epK2 epHalf (fun _ => true) i j = epK2 i j from by
      rw [epK2_perturbWeight_allTrue]]
  ring

theorem epK2_perturbed_allTrue_nonneg (i j : Fin 2) :
    0 ≤ (epK2 + perturbWeight epK2 epHalf (fun _ => true)) i j := by
  rw [epK2_perturbed_allTrue_eq]
  simp only [Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [epK2]

/-- The perturbed λ₂ at the all-true outcome is exactly `4` — the same
kernel-plus-trace route at the doubled degree. -/
theorem epK2_perturbed_evals_one_eq_four_QA :
    evals (laplacian_symmetric (epK2 + perturbWeight epK2 epHalf (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => true))))
      ⟨1, by norm_num⟩ = 4 := by
  have h0 := laplacian_evals_zero
    (epK2 + perturbWeight epK2 epHalf (fun _ => true))
    (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => true)))
    epK2_perturbed_allTrue_nonneg (by norm_num)
  have h0' : evals (laplacian_symmetric
      (epK2 + perturbWeight epK2 epHalf (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => true))))
      (0 : Fin 2) = 0 := h0
  have hsum := evals_sum_eq_trace
    (laplacian_symmetric (epK2 + perturbWeight epK2 epHalf (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => true))))
  have htrace :
      (laplacian (epK2 + perturbWeight epK2 epHalf (fun _ => true))).trace
      = 4 := by
    have hdiag : ∀ i : Fin 2, (laplacian epK2) i i = 1 := by
      intro i
      have hdeg : deg epK2 i = 1 := by
        fin_cases i <;> simp [deg, epK2, Fin.sum_univ_two]
      rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal,
        hdeg, epK2_diag i, sub_zero]
    have hdiag2 : ∀ i : Fin 2,
        (laplacian (epK2 + perturbWeight epK2 epHalf (fun _ => true))) i i
        = 2 := by
      intro i
      rw [epK2_perturbed_allTrue_eq, laplacian_smul,
        Matrix.smul_apply, smul_eq_mul, hdiag i]
      ring
    rw [show (laplacian (epK2 + perturbWeight epK2 epHalf (fun _ => true))).trace
        = ∑ i, (laplacian (epK2
            + perturbWeight epK2 epHalf (fun _ => true))) i i from rfl,
      Finset.sum_congr rfl fun i _ => hdiag2 i]
    simp [Fin.sum_univ_two]
    norm_num
  rw [htrace] at hsum
  have h2 : ∑ i : Fin 2,
      evals (laplacian_symmetric (epK2
        + perturbWeight epK2 epHalf (fun _ => true))
        (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
          (fun _ => true)))) i = 4 := hsum
  simp only [Fin.sum_univ_two] at h2
  have h1' : evals (laplacian_symmetric (epK2
      + perturbWeight epK2 epHalf (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
        (fun _ => true)))) (1 : Fin 2) = 4 := by
    linarith
  exact h1'

/-- **The Weyl transfer is tight at a genuine design outcome**: at the
all-true outcome the eigenvalue displacement `|4 − 2|` equals the
perturbation norm `‖L(E_ω)‖ = ‖rankOne epVec‖ = 2` — the two sides
pinned by independent routes (kernel-plus-trace spectra vs the
weight-space packaging pin joined to the two-sided rank-one norm). A
constant mistake anywhere on the transfer path breaks this equality. -/
theorem epK2_weylTight_allTrue_QA :
    |evals (laplacian_symmetric (epK2 + perturbWeight epK2 epHalf (fun _ => true))
        (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => true))))
        ⟨1, by norm_num⟩
      - evals (laplacian_symmetric epK2 epK2_symmetric) ⟨1, by norm_num⟩|
      = ‖laplacian (perturbWeight epK2 epHalf (fun _ => true))‖ := by
  rw [epK2_perturbed_evals_one_eq_four_QA, epK2_evals_one_eq_two_QA,
    epK2_packaging_twoRoute_QA, epK2_rankOne_norm]
  norm_num

/-! ### The closed-form instances -/

/-- **The eigenvalue tail on `K₂` at `p ≡ ½`, `t = 1`, index 1, in closed
form**: `μ {|λ₂(L̃_ω) − 2| ≥ 1} ≤ 4 exp(−1/16)` — the dimension factor
`2 · 2`, the variance norm `8` in the exponent's denominator `2 · 8`.
CONDITIONAL ON THE `matrix_hoeffding` AXIOM (instantiated, not
re-proved). -/
theorem epK2_eval_tail_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool |
        (1 : ℝ) ≤ |evals (laplacian_symmetric (epK2 + perturbWeight epK2 epHalf ω)
              (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω)))
            ⟨1, by norm_num⟩
          - evals (laplacian_symmetric epK2 epK2_symmetric) ⟨1, by norm_num⟩|}
      ≤ ENNReal.ofReal (4 * Real.exp (-((1 : ℝ)) / 16)) := by
  have htail := edgePerturbation_eval_tail epK2 epHalf epK2_symmetric
    epHalf_nonneg epHalf_le_one ⟨1, by norm_num⟩ 1 zero_le_one
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((1 : ℝ)) / 16) := by
    have h1 : -((1 : ℝ) ^ 2) / (2 * 8) = -((1 : ℝ)) / 16 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  simpa using htail

/-- **The λ₂ gap-survival instance on `K₂` at `p ≡ ½`, `t = 2`, in closed
form**: `μ {λ₂(L̃_ω) ≤ 0} ≤ 4 exp(−4/16)` — and the event is provably
nonempty (the all-false outcome kills the edge, where `λ₂ = 0`), so the
bound has genuine content rather than certifying an empty event.
CONDITIONAL ON THE `matrix_hoeffding` AXIOM. -/
theorem epK2_lambda2_lower_tail_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool |
        lambda2 (epK2 + perturbWeight epK2 epHalf ω)
          (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))
          (by norm_num) ≤ lambda2 epK2 epK2_symmetric (by norm_num) - 2}
      ≤ ENNReal.ofReal (4 * Real.exp (-((2 : ℝ)) / 8)) := by
  have htail := edgePerturbation_lambda2_lower_tail epK2 epHalf epK2_symmetric
    epHalf_nonneg epHalf_le_one (by norm_num) 2 (by norm_num)
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((2 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((2 : ℝ)) / 8) := by
    have h1 : -((2 : ℝ) ^ 2) / (2 * 8) = -((2 : ℝ)) / 8 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  simpa [lambda2] using htail

/-- **The uniform quadratic-form tail on `K₂` at `p ≡ ½`, `t = 1`, in
closed form**: the existential-vector event obeys the same
`4 exp(−1/16)`. CONDITIONAL ON THE `matrix_hoeffding` AXIOM. -/
theorem epK2_uniform_tail_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool | ∃ x : Fin 2 → ℝ, x ≠ 0 ∧
        (1 : ℝ) * (x ⬝ᵥ x)
          ≤ |quadForm (laplacian (perturbWeight epK2 epHalf ω)) x|}
      ≤ ENNReal.ofReal (4 * Real.exp (-((1 : ℝ)) / 16)) := by
  have htail := edgePerturbation_quadForm_uniform_tail epK2 epHalf
    epHalf_nonneg epHalf_le_one 1 zero_le_one
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((1 : ℝ)) / 16) := by
    have h1 : -((1 : ℝ) ^ 2) / (2 * 8) = -((1 : ℝ)) / 16 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  simpa using htail

/-- **The `x = 0` guard fence**: without the `x ≠ 0` guard the
existential event is all of `Ω` (`x = 0` always witnesses
`t · 0 ≤ |0|`), so its measure is exactly `1` — while at `t = 7` the
would-be bound `4 exp(−49/16) < 1` (from `4 < 1 + 49/16 ≤ exp(49/16)`).
The un-guarded statement is thereby *refuted* in proved arithmetic: the
guard is load-bearing, not decorative. -/
theorem epK2_uniform_guard_fence_QA :
    ¬ ((bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool | ∃ x : Fin 2 → ℝ,
          (7 : ℝ) * (x ⬝ᵥ x)
            ≤ |quadForm (laplacian (perturbWeight epK2 epHalf ω)) x|}
        ≤ ENNReal.ofReal (4 * Real.exp (-((49 : ℝ) / 16)))) := by
  have huniv : {ω : (Fin 2 × Fin 2) → Bool | ∃ x : Fin 2 → ℝ,
      (7 : ℝ) * (x ⬝ᵥ x)
        ≤ |quadForm (laplacian (perturbWeight epK2 epHalf ω)) x|}
      = Set.univ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨0, by simp [quadForm]⟩
  have h1 : (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool | ∃ x : Fin 2 → ℝ,
        (7 : ℝ) * (x ⬝ᵥ x)
          ≤ |quadForm (laplacian (perturbWeight epK2 epHalf ω)) x|} = 1 := by
    rw [huniv]
    exact measure_univ
  intro hle
  rw [h1] at hle
  have hbound : (4 : ℝ) * Real.exp (-((49 : ℝ) / 16)) < 1 := by
    have hexp : (4 : ℝ) < Real.exp ((49 : ℝ) / 16) :=
      lt_of_lt_of_le (by norm_num) (Real.add_one_le_exp ((49 : ℝ) / 16))
    have hdiv : (4 : ℝ) / Real.exp ((49 : ℝ) / 16) < 1 :=
      (div_lt_one (Real.exp_pos ((49 : ℝ) / 16))).2 hexp
    have hkey : (4 : ℝ) * Real.exp (-((49 : ℝ) / 16))
        = (4 : ℝ) / Real.exp ((49 : ℝ) / 16) := by
      rw [Real.exp_neg, mul_comm, inv_mul_eq_div]
    rw [hkey]
    exact hdiv
  have hlt : ENNReal.ofReal (4 * Real.exp (-((49 : ℝ) / 16)))
      < ENNReal.ofReal 1 :=
    (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hbound
  rw [ENNReal.ofReal_one] at hlt
  exact absurd hle (not_le.2 hlt)

/-! ### The three-path instance -/

/-- **The eigenvalue tail on the three-path at `p ≡ ¼`, `t = 1`, index 2,
in closed form**: `μ {|λ₃(L̃_ω) − 3| ≥ 1} ≤ 6 exp(−1/24)` — the
dimension factor `2 · 3`, the variance norm `12` in the exponent's
denominator `2 · 12`, both pinned in the drift section. CONDITIONAL ON
THE `matrix_hoeffding` AXIOM. -/
theorem epP3_eval_tail_QA :
    (bernPMF epQuarter epQuarter_nonneg epQuarter_le_one).toMeasure
      {ω : (Fin 3 × Fin 3) → Bool |
        (1 : ℝ) ≤ |evals (laplacian_symmetric (path3Adj
              + perturbWeight path3Adj epQuarter ω)
              (path3Adj_symmetric.add (perturbWeight_isSymm path3Adj epQuarter ω)))
            ⟨2, by norm_num⟩
          - evals (laplacian_symmetric path3Adj path3Adj_symmetric)
            ⟨2, by norm_num⟩|}
      ≤ ENNReal.ofReal (6 * Real.exp (-((1 : ℝ)) / 24)) := by
  have htail := edgePerturbation_eval_tail path3Adj epQuarter
    path3Adj_symmetric epQuarter_nonneg epQuarter_le_one ⟨2, by norm_num⟩
    1 zero_le_one
  rw [epP3_variance_norm] at htail
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 3 * Real.exp (-((1 : ℝ) ^ 2) / (2 * 12))
      = 6 * Real.exp (-((1 : ℝ)) / 24) := by
    have h1 : -((1 : ℝ) ^ 2) / (2 * 12) = -((1 : ℝ)) / 24 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  simpa using htail

/-! ## The Cheeger window (K₂) -/

/-! ### The base-graph pins -/

/-- The φ(K₂) = 1 pin, transferred at definitional equality from
`Cheeger_QA`'s independently proved value at its own (identical) edge
fixture — the join point of this section to the Cheeger QA stack. -/
theorem epK2_cheegerConstant : cheegerConstant epK2 = 1 := by
  have h : epK2 = SpectralGraphTheory.QA.edgeAdj := rfl
  rw [h]
  exact SpectralGraphTheory.QA.edge_cheegerConstant

/-- `K₂` is `1`-regular, transferred the same way. -/
theorem epK2_regular : ∀ i, deg epK2 i = 1 := by
  have h : epK2 = SpectralGraphTheory.QA.edgeAdj := rfl
  rw [h]
  exact SpectralGraphTheory.QA.edgeAdj_regular

/-- The base λ₂ on `K₂` at the `lambda2` interface is `2` (the
kernel-plus-trace pin `epK2_evals_one_eq_two_QA` transported). -/
theorem epK2_lambda2_eq_two :
    lambda2 epK2 epK2_symmetric (by norm_num) = 2 := by
  simpa [lambda2] using epK2_evals_one_eq_two_QA

/-- **The engine pair instantiated on `K₂`**: floor
`1·φ²/2 = 1/2 ≤ λ₂ = 2` and ceiling `λ₂ = 2 = 2·(1·φ)` — the ceiling
attained with *equality* (third conjunct), so a wrong constant on either
engine side of `cheeger_{lower,upper}_bound_laplacian` breaks this QA at
the third conjunct, and the two `≤` conjuncts exercise both theorem
instances. -/
theorem epK2_cheeger_window_QA :
    (1 : ℝ) * (cheegerConstant epK2) ^ 2 / 2
      ≤ lambda2 epK2 epK2_symmetric (by norm_num)
      ∧ lambda2 epK2 epK2_symmetric (by norm_num)
        ≤ 2 * ((1 : ℝ) * cheegerConstant epK2)
      ∧ lambda2 epK2 epK2_symmetric (by norm_num)
        = 2 * ((1 : ℝ) * cheegerConstant epK2) := by
  refine ⟨cheeger_lower_bound_laplacian epK2 epK2_symmetric epK2_nonneg 1
      epK2_regular (by norm_num) (by norm_num),
    cheeger_upper_bound_laplacian epK2 epK2_symmetric epK2_nonneg 1
      epK2_regular (by norm_num) (by norm_num), ?_⟩
  rw [epK2_lambda2_eq_two, epK2_cheegerConstant]
  norm_num

/-! ### The all-false outcome stack -/

/-- The all-false outcome kills the edge: the perturbed adjacency is the
zero matrix, entrywise through the design's entry formulas
(`perturbWeight_apply_of_ne`/`perturbWeight_apply_diag` at
`p ≡ ½`). -/
theorem epK2_perturbed_allFalse_eq :
    epK2 + perturbWeight epK2 epHalf (fun _ => false) = 0 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.add_apply, Matrix.zero_apply, perturbWeight_apply_diag,
      epK2_diag i]
    simp [epHalf]
  · rw [Matrix.add_apply, Matrix.zero_apply, perturbWeight_apply_of_ne _ _ _ hij]
    fin_cases i <;> fin_cases j <;> simp [epK2, epHalf] <;> norm_num

theorem epK2_perturbed_allFalse_nonneg (i j : Fin 2) :
    0 ≤ (epK2 + perturbWeight epK2 epHalf (fun _ => false)) i j := by
  rw [epK2_perturbed_allFalse_eq]
  norm_num

/-- λ₂ at the all-false outcome is exactly `0` — the kernel-plus-trace
route at the zero adjacency (kernel eigenvalue `0`, trace `0`). -/
theorem epK2_perturbed_allFalse_lambda2_eq_zero :
    lambda2 (epK2 + perturbWeight epK2 epHalf (fun _ => false))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false)))
      (by norm_num) = 0 := by
  have h0 : evals (laplacian_symmetric
      (epK2 + perturbWeight epK2 epHalf (fun _ => false))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false))))
      (0 : Fin 2) = 0 :=
    laplacian_evals_zero
    (epK2 + perturbWeight epK2 epHalf (fun _ => false))
    (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false)))
    epK2_perturbed_allFalse_nonneg (by norm_num)
  have hsum := evals_sum_eq_trace
    (laplacian_symmetric (epK2 + perturbWeight epK2 epHalf (fun _ => false))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false))))
  have htrace :
      (laplacian (epK2 + perturbWeight epK2 epHalf (fun _ => false))).trace
        = 0 := by
    rw [epK2_perturbed_allFalse_eq]
    have hd0 : degreeMatrix (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
      ext a b
      simp [degreeMatrix, deg]
    rw [laplacian, sub_zero, hd0, Matrix.trace_zero]
  rw [htrace] at hsum
  have h2 : ∑ i : Fin 2,
      evals (laplacian_symmetric
          (epK2 + perturbWeight epK2 epHalf (fun _ => false))
          (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false))))
        i = 0 := hsum
  simp only [Fin.sum_univ_two] at h2
  have h1' : evals (laplacian_symmetric
      (epK2 + perturbWeight epK2 epHalf (fun _ => false))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false))))
      (1 : Fin 2) = 0 := by
    linarith
  simpa [lambda2] using h1'

/-! ### The closed-form Cheeger-window instances -/

/-- **The Cheeger floor tail on `K₂` at `p ≡ ½`, `t = ½`, in closed
form**: `μ {λ₂(L̃_ω) ≤ 1·φ²/2 − ½ = 0} ≤ 4 exp(−1/64)` — the dimension
factor `2 · 2`, the variance norm `8` in the exponent's denominator
`2 · 8`. CONDITIONAL ON THE `matrix_hoeffding` AXIOM (instantiated, not
re-proved). -/
theorem epK2_cheeger_floor_tail_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool |
        lambda2 (epK2 + perturbWeight epK2 epHalf ω)
          (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))
          (by norm_num) ≤ (1 : ℝ) * (cheegerConstant epK2) ^ 2 / 2 - 1 / 2}
      ≤ ENNReal.ofReal (4 * Real.exp (-((1 : ℝ)) / 64)) := by
  have htail := edgePerturbation_lambda2_cheeger_floor epK2 epHalf
    epK2_symmetric epK2_nonneg 1 epK2_regular (by norm_num)
    epHalf_nonneg epHalf_le_one (by norm_num) (1 / 2) (by norm_num)
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((1 : ℝ)) / 64) := by
    have h1 : -((1 / 2 : ℝ) ^ 2) / (2 * 8) = -((1 : ℝ)) / 64 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  exact htail

/-- **Non-vacuity of the floor tail**: the all-false outcome belongs to
the floor event with `λ₂ = 0 = 1·φ²/2 − ½` attained at equality — the
bound has genuine content rather than certifying an empty event (random
resampling really can destroy the connectivity certificate; the tail
prices exactly that risk). -/
theorem epK2_cheeger_floor_nonvacuous_QA :
    (fun _ => false) ∈ {ω : (Fin 2 × Fin 2) → Bool |
        lambda2 (epK2 + perturbWeight epK2 epHalf ω)
          (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))
          (by norm_num) ≤ (1 : ℝ) * (cheegerConstant epK2) ^ 2 / 2 - 1 / 2} := by
  simp only [Set.mem_setOf_eq]
  rw [epK2_perturbed_allFalse_lambda2_eq_zero, epK2_cheegerConstant]
  norm_num

/-- **The connectivity bracket on `K₂` at `p ≡ ½`, `t = ½`, in closed
form**: `μ {λ₂(L̃_ω) ∉ [1·φ²/2 − ½, 2·(1·φ) + ½] = [0, 5/2]}
≤ 4 exp(−1/64)` — the same constant as the one-sided tail (the window
contains the eigenvalue ball). CONDITIONAL ON THE `matrix_hoeffding`
AXIOM. -/
theorem epK2_connectivity_bracket_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool |
        lambda2 (epK2 + perturbWeight epK2 epHalf ω)
          (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))
          (by norm_num) ≤ (1 : ℝ) * (cheegerConstant epK2) ^ 2 / 2 - 1 / 2
        ∨ 2 * ((1 : ℝ) * cheegerConstant epK2) + 1 / 2
          ≤ lambda2 (epK2 + perturbWeight epK2 epHalf ω)
            (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))
            (by norm_num)}
      ≤ ENNReal.ofReal (4 * Real.exp (-((1 : ℝ)) / 64)) := by
  have htail := edgePerturbation_connectivity_bracket epK2 epHalf
    epK2_symmetric epK2_nonneg 1 epK2_regular (by norm_num)
    epHalf_nonneg epHalf_le_one (by norm_num) (1 / 2) (by norm_num)
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((1 : ℝ)) / 64) := by
    have h1 : -((1 / 2 : ℝ) ^ 2) / (2 * 8) = -((1 : ℝ)) / 64 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  exact htail

/-- λ₂ at the all-true outcome is `4` (the weight-`2` edge) — the
existing pinned spectrum at the `lambda2` interface. -/
theorem epK2_perturbed_allTrue_lambda2_eq_four :
    lambda2 (epK2 + perturbWeight epK2 epHalf (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => true)))
      (by norm_num) = 4 := by
  simpa [lambda2] using epK2_perturbed_evals_one_eq_four_QA

/-- **The upper window side fires too**: the all-true outcome sits above
the bracket's ceiling (`λ₂ = 4 ≥ 2·(1·φ) + ½ = 5/2`) — both sides of the
window are witnessed at concrete outcomes of the design (the all-false
outcome below, this one above), so neither disjunct of the bracket event
is vacuous. -/
theorem epK2_bracket_upper_fires_QA :
    (fun _ => true) ∈ {ω : (Fin 2 × Fin 2) → Bool |
        2 * ((1 : ℝ) * cheegerConstant epK2) + 1 / 2
          ≤ lambda2 (epK2 + perturbWeight epK2 epHalf ω)
            (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))
            (by norm_num)} := by
  simp only [Set.mem_setOf_eq]
  rw [epK2_perturbed_allTrue_lambda2_eq_four, epK2_cheegerConstant]
  norm_num

/-! ## The sharpened (matched-threshold) drift interface

The QA for `edgePerturbation_fiedlerSubspace_drift'` /
`edgePerturbation_fiedlerLine_drift'`: the envelope arithmetic pinned
in general and at concrete numerics, the closed-form three-path
instances, and the strict-improvement pin. -/

/-- **Envelope domination**: every valid `(t, δ)` instance of the
delivered `t/δ`-shaped drift family is dominated by the sharpened
parametrization at the same threshold — the exponent `t²` never exceeds
`s²` at `s := γt/(t+δ)`, the sharpened statement's level (the `s/(γ−s)`
threshold of that level is exactly `t/δ`; the companion lemma below).
This is the arithmetic content of "the sharpened form is the envelope
of the delivered family". -/
theorem ep_envelope_domination_QA {γ t δ : ℝ} (ht : 0 ≤ t)
    (hδ : 0 < δ) (hle : t + δ ≤ γ) :
    t ≤ γ * t / (t + δ) := by
  rcases eq_or_lt_of_le ht with rfl | htpos
  · norm_num
  · have hsumpos : (0:ℝ) < t + δ := by linarith
    rw [le_div_iff₀ hsumpos]
    have h := mul_le_mul_of_nonneg_right hle (le_of_lt htpos)
    nlinarith [h]

/-- **Envelope same-threshold identity**: the sharpened level
`s := γt/(t+δ)` sits at exactly the delivered instance's threshold —
`s/(γ−s) = t/δ` — so the domination above is a comparison at one and
the same threshold: together the two lemmas say the sharpened family is
*the* envelope of the `t/δ` family, not merely a subfamily of it. -/
theorem ep_envelope_threshold_QA {γ t δ : ℝ} (hγ : 0 < γ) (ht : 0 ≤ t)
    (hδ : 0 < δ) :
    (γ * t / (t + δ)) / (γ - γ * t / (t + δ)) = t / δ := by
  have hsumpos : (0:ℝ) < t + δ := by linarith
  have hden : γ - γ * t / (t + δ) = γ * δ / (t + δ) := by
    field_simp
    ring
  rw [hden]
  field_simp
  ring

/-- The concrete envelope join: at the naive valid instance
`(t, δ) = (1, ½)` of `γ = 2`, the dominated sharpened level is
`2·1/(1 + ½) = 4/3 ≥ 1` — the general domination lemma at hand values
(a wrong envelope constant breaks exactly this numeric pin). -/
theorem ep_naive_domination_instance_QA :
    (1:ℝ) ≤ 2 * 1 / (1 + 1 / 2) :=
  ep_envelope_domination_QA (γ := 2) (t := 1) (δ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)

/-- The concrete same-threshold join: the envelope point `4/3` of the
naive `(1, ½)` instance sits at exactly its threshold
`(4/3)/(2 − 4/3) = 1/(½) = 2`. -/
theorem ep_naive_threshold_instance_QA :
    ((2:ℝ) * 1 / (1 + 1 / 2)) / (2 - 2 * 1 / (1 + 1 / 2)) = 1 / (1 / 2) :=
  ep_envelope_threshold_QA (γ := 2) (t := 1) (δ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num)

/-- The base three-path gap bound in the sharpened interface's shape:
`γ = 2 ≤ λ₃ − λ₂ = 3 − 1` (the two exact spectrum pins). -/
theorem epP3_hgap_two :
    (2:ℝ) ≤ evals (laplacian_symmetric path3Adj path3Adj_symmetric)
        ⟨2, by norm_num⟩
      - evals (laplacian_symmetric path3Adj path3Adj_symmetric)
        ⟨1, by norm_num⟩ := by
  rw [path3_evals_two_eq_three_QA, path3_evals_one_eq_one_QA]
  norm_num

/-- **The sharpened subspace-drift instance on the path, in closed
form**: at `γ = 2` (the whole base gap) and `s = 1`, the bottom-2
subspace rotation under random edge resampling exceeds
`1/(2−1) = 1` with probability at most `6 exp(−1/24)` — the join
point: the delivered `t/δ` instance's numbers (t = δ = 1) recovered
with the gap consumed inline, and the envelope-optimal split for
threshold `1` at `γ = 2` is exactly `s = 2·1/(1+1) = 1`. CONDITIONAL
ON THE `matrix_hoeffding` AXIOM (instantiated via the sharpened
theorem, not re-proved). -/
theorem epP3_fiedlerSubspace_drift'_QA :
    (bernPMF epQuarter epQuarter_nonneg epQuarter_le_one).toMeasure
      {ω : (Fin 3 × Fin 3) → Bool |
        ‖initialProjector (laplacian (path3Adj
              + perturbWeight path3Adj epQuarter ω))
            (laplacian_symmetric (path3Adj
              + perturbWeight path3Adj epQuarter ω)
              (path3Adj_symmetric.add
                (perturbWeight_isSymm path3Adj epQuarter ω)))
              ⟨1, by norm_num⟩
          - initialProjector (laplacian path3Adj)
            (laplacian_symmetric path3Adj path3Adj_symmetric)
            ⟨1, by norm_num⟩‖ ≥ (1:ℝ) / (2 - 1)}
      ≤ ENNReal.ofReal (6 * Real.exp (-((1:ℝ)) / 24)) := by
  have h := edgePerturbation_fiedlerSubspace_drift' path3Adj
    path3Adj_symmetric epQuarter epQuarter_nonneg epQuarter_le_one
    (by simp) 2 epP3_hgap_two 1 one_pos (by norm_num)
  rw [epP3_variance_norm] at h
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by norm_num
  rw [hcard] at h
  have hRHS : (2:ℝ) * 3 * Real.exp (-((1:ℝ) ^ 2) / (2 * 12))
      = 6 * Real.exp (-((1:ℝ)) / 24) := by
    have h1 : -((1:ℝ) ^ 2) / (2 * 12) = -((1:ℝ)) / 24 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at h
  exact h

/-- **The sharpened Fiedler-line drift instance on the path, in closed
form** (the join point, line variant): at `γ = 2`, `s = 1`, the
Fiedler-line rotation exceeds `1/(2−1) = 1` with probability at most
`6 exp(−1/24)` — the same closed form as the delivered `t/δ`
instance, now with the gap consumed inline. CONDITIONAL ON THE
`matrix_hoeffding` AXIOM (instantiated via the sharpened theorem, not
re-proved). -/
theorem epP3_fiedlerLine_drift'_QA :
    (bernPMF epQuarter epQuarter_nonneg epQuarter_le_one).toMeasure
      {ω : (Fin 3 × Fin 3) → Bool |
        ‖(initialProjector (laplacian (path3Adj
              + perturbWeight path3Adj epQuarter ω))
            (laplacian_symmetric (path3Adj
              + perturbWeight path3Adj epQuarter ω)
              (path3Adj_symmetric.add
                (perturbWeight_isSymm path3Adj epQuarter ω)))
              ⟨1, by norm_num⟩
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
            ⟨0, by norm_num⟩)‖ ≥ (1:ℝ) / (2 - 1)}
      ≤ ENNReal.ofReal (6 * Real.exp (-((1:ℝ)) / 24)) := by
  have h := edgePerturbation_fiedlerLine_drift' path3Adj path3Adj_symmetric
    epQuarter epQuarter_nonneg epQuarter_le_one path3Adj_nonneg
    epP3_perturbed_nonneg path3_supportGraph_connected
    (fun ω => by rw [epP3_supportGraph ω]; exact path3_supportGraph_connected)
    (by simp) 2 epP3_hgap_two 1 one_pos (by norm_num)
  rw [epP3_variance_norm] at h
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by norm_num
  rw [hcard] at h
  have hRHS : (2:ℝ) * 3 * Real.exp (-((1:ℝ) ^ 2) / (2 * 12))
      = 6 * Real.exp (-((1:ℝ)) / 24) := by
    have h1 : -((1:ℝ) ^ 2) / (2 * 12) = -((1:ℝ)) / 24 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at h
  exact h

/-- **The sharpened Fiedler-line drift instance at the non-trivial
threshold `2`**: at `γ = 2`, `s = 4/3` (the envelope point for
threshold `u = 2`: `s = γu/(1+u) = 4/3`, `s/(γ−s) = 2`), the rotation
exceeds `2` with probability at most `6 exp(−2/27)` (the exponent
`(4/3)²/(2·12) = 2/27`). A wrong constant anywhere on the sharpened
statement's parametrization — the threshold `s/(γ−s)`, the tail level
`s`, or the gap consumption `γ` — breaks exactly this closed form.
CONDITIONAL ON THE `matrix_hoeffding` AXIOM (instantiated via the
sharpened theorem, not re-proved). -/
theorem epP3_fiedlerLine_drift'_threshold_two_QA :
    (bernPMF epQuarter epQuarter_nonneg epQuarter_le_one).toMeasure
      {ω : (Fin 3 × Fin 3) → Bool |
        ‖(initialProjector (laplacian (path3Adj
              + perturbWeight path3Adj epQuarter ω))
            (laplacian_symmetric (path3Adj
              + perturbWeight path3Adj epQuarter ω)
              (path3Adj_symmetric.add
                (perturbWeight_isSymm path3Adj epQuarter ω)))
              ⟨1, by norm_num⟩
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
            ⟨0, by norm_num⟩)‖ ≥ (4 / 3 : ℝ) / (2 - 4 / 3)}
      ≤ ENNReal.ofReal (6 * Real.exp (-((2 / 27 : ℝ)))) := by
  have h := edgePerturbation_fiedlerLine_drift' path3Adj path3Adj_symmetric
    epQuarter epQuarter_nonneg epQuarter_le_one path3Adj_nonneg
    epP3_perturbed_nonneg path3_supportGraph_connected
    (fun ω => by rw [epP3_supportGraph ω]; exact path3_supportGraph_connected)
    (by simp) 2 epP3_hgap_two (4 / 3) (by norm_num)
    (by norm_num)
  rw [epP3_variance_norm] at h
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by norm_num
  rw [hcard] at h
  have hRHS : (2:ℝ) * 3 * Real.exp (-((4 / 3 : ℝ) ^ 2) / (2 * 12))
      = 6 * Real.exp (-((2 / 27 : ℝ))) := by
    have h1 : -((4 / 3 : ℝ) ^ 2) / (2 * 12) = -((2 / 27 : ℝ)) := by norm_num
    rw [h1]
    ring
  rw [hRHS] at h
  exact h

/-- **The naive non-envelope instance at the same threshold `2`**: the
*delivered* `t/δ` theorem at the valid but non-envelope split
`(t, δ) = (1, ½)` (constraint `1 + ½ ≤ 2` holds; threshold
`1/(½) = 2`) yields only `6 exp(−1/24)` — the comparison partner for
the strict-improvement pin below. CONDITIONAL ON THE
`matrix_hoeffding` AXIOM. -/
theorem epP3_fiedlerLine_drift_naive_QA :
    (bernPMF epQuarter epQuarter_nonneg epQuarter_le_one).toMeasure
      {ω : (Fin 3 × Fin 3) → Bool |
        ‖(initialProjector (laplacian (path3Adj
              + perturbWeight path3Adj epQuarter ω))
            (laplacian_symmetric (path3Adj
              + perturbWeight path3Adj epQuarter ω)
              (path3Adj_symmetric.add
                (perturbWeight_isSymm path3Adj epQuarter ω)))
              ⟨1, by norm_num⟩
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
            ⟨0, by norm_num⟩)‖ ≥ (1:ℝ) / (1 / 2)}
      ≤ ENNReal.ofReal (6 * Real.exp (-((1:ℝ)) / 24)) := by
  have hgap : (1:ℝ) + 1 / 2
      ≤ evals (laplacian_symmetric path3Adj path3Adj_symmetric)
          ⟨2, by norm_num⟩
        - evals (laplacian_symmetric path3Adj path3Adj_symmetric)
          ⟨1, by norm_num⟩ := by
    rw [path3_evals_two_eq_three_QA, path3_evals_one_eq_one_QA]
    norm_num
  have h := edgePerturbation_fiedlerLine_drift path3Adj path3Adj_symmetric
    epQuarter epQuarter_nonneg epQuarter_le_one path3Adj_nonneg
    epP3_perturbed_nonneg path3_supportGraph_connected
    (fun ω => by rw [epP3_supportGraph ω]; exact path3_supportGraph_connected)
    (by simp) (1 / 2) (by norm_num) 1 zero_le_one hgap
  rw [epP3_variance_norm] at h
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by norm_num
  rw [hcard] at h
  have hRHS : (2:ℝ) * 3 * Real.exp (-((1:ℝ) ^ 2) / (2 * 12))
      = 6 * Real.exp (-((1:ℝ)) / 24) := by
    have h1 : -((1:ℝ) ^ 2) / (2 * 12) = -((1:ℝ)) / 24 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at h
  exact h

/-- **The sharpened interface strictly improves a valid non-envelope
instance at the same threshold**: at threshold `2` on the path, the
sharpened bound `6 exp(−2/27)` is strictly smaller than the naive
`(1, ½)` instance's `6 exp(−1/24)` (proved by strict exp monotonicity
at `1/24 < 2/27`) — the envelope point's exponent `(4/3)²` strictly
dominates the naive `1²`, so matching threshold to tail is a real
strengthening, not a reparametrization. -/
theorem epP3_sharp_improves_QA :
    6 * Real.exp (-((2 / 27 : ℝ))) < 6 * Real.exp (-((1:ℝ)) / 24) := by
  have h : (1:ℝ) / 24 < 2 / 27 := by norm_num
  have hexp : Real.exp (-((2 / 27 : ℝ))) < Real.exp (-((1:ℝ)) / 24) :=
    Real.exp_lt_exp.mpr (by linarith)
  exact mul_lt_mul_of_pos_left hexp (by norm_num)

/-! ## The normalized (irregular) Cheeger window

The irregular window family
(`edgePerturbation_normalized_cheeger_floor`,
`edgePerturbation_normalized_connectivity_bracket`) and the new
window-Cheeger engine pair. The tail instances are CONDITIONAL ON THE
`matrix_hoeffding` AXIOM (instantiated, not re-proved); the engine
instances and the admissibility witnesses are hard crust.

Honesty note on the admissibility window: it is *proof-load-bearing*
(the sandwich's `hnn`/`hd` clauses on the perturbed graph are exactly
the window conjuncts, and the assembly's `measure_mono` has no route
without them), but no dropped-window refutation fixture exists at
fixture scale: at the outcomes the window excludes, the degrees hit
`0` and `normalizedLaplacian` degenerates to the identity
(`degreeInvSqrt = 0⁻¹ = 0`), whose `λ₂ = 1` keeps the un-windowed floor
condition false on `K₂`-shaped fixtures (the floor never exceeds
`dmin·φ²/2 / dmax ≤ 1/4` there). The witnesses below therefore pin
that the window genuinely restricts the outcome space (admissible and
inadmissible outcomes both exist), not that the un-windowed statement
fails. -/

/-- The P₃ degree profile: `1, 2, 1`. -/
theorem epP3_deg (i : Fin 3) :
    deg path3Adj i = if (i : ℕ) = 1 then 2 else 1 := by
  fin_cases i <;> rw [deg, Fin.sum_univ_three] <;> norm_num [path3Adj]

theorem epP3_pos_deg (i : Fin 3) : 0 < deg path3Adj i := by
  rw [epP3_deg i]
  fin_cases i <;> norm_num

theorem epK2_pos_deg (i : Fin 2) : 0 < deg epK2 i := by
  rw [epK2_regular i]
  norm_num

/-- The φ(P₃) = 1 pin, transferred entrywise from the irregular-Cheeger
QA's own path fixture. -/
theorem epP3_cheegerConstant : cheegerConstant path3Adj = 1 := by
  have h : path3Adj = SpectralGraphTheory.QA.icPathAdj := by
    ext i j
    fin_cases i <;> fin_cases j
    <;> simp [path3Adj, SpectralGraphTheory.QA.icPathAdj]
  rw [h]
  exact SpectralGraphTheory.QA.icPathAdj_cheegerConstant

/-- **The window engine pair on `K₂`** (degree window `[1, 1]`): floor
`1·φ²/2 = 1/2 ≤ λ₂ = 2`; ceiling `λ₂ = 2 = 2·(1·φ)` attained with
equality — a wrong constant on either engine side breaks the third
conjunct. -/
theorem epK2_normWindow_engine_QA :
    (1 : ℝ) * (cheegerConstant epK2) ^ 2 / 2
      ≤ lambda2 epK2 epK2_symmetric (by norm_num)
      ∧ lambda2 epK2 epK2_symmetric (by norm_num)
        ≤ 2 * ((1 : ℝ) * cheegerConstant epK2)
      ∧ lambda2 epK2 epK2_symmetric (by norm_num)
        = 2 * ((1 : ℝ) * cheegerConstant epK2) := by
  refine ⟨cheeger_lower_bound_laplacian_of_degree_window epK2
      epK2_symmetric epK2_nonneg epK2_pos_deg 1
      (fun i => by rw [epK2_regular i]) one_pos (by norm_num),
    cheeger_upper_bound_laplacian_of_degree_window epK2
      epK2_symmetric epK2_nonneg epK2_pos_deg 1
      (fun i => by rw [epK2_regular i]) (by norm_num), ?_⟩
  rw [epK2_lambda2_eq_two, epK2_cheegerConstant]
  norm_num

/-- **The window engine pair on the genuinely irregular `P₃`** (degrees
`1, 2, 1`, window `[1, 2]`): floor `1·1²/2 = 1/2 ≤ λ₂(L P₃) = 1` (the
honest slack of the bracket); ceiling `λ₂ = 1 ≤ 2·(2·1) = 4`. -/
theorem epP3_normWindow_engine_QA :
    (1 : ℝ) * (cheegerConstant path3Adj) ^ 2 / 2
      ≤ lambda2 path3Adj path3Adj_symmetric (by norm_num)
      ∧ lambda2 path3Adj path3Adj_symmetric (by norm_num)
        ≤ 2 * ((2 : ℝ) * cheegerConstant path3Adj) := by
  refine ⟨cheeger_lower_bound_laplacian_of_degree_window path3Adj
      path3Adj_symmetric path3Adj_nonneg epP3_pos_deg 1
      (fun i => by rw [epP3_deg i]; fin_cases i <;> norm_num) one_pos
      (by norm_num),
    cheeger_upper_bound_laplacian_of_degree_window path3Adj
      path3Adj_symmetric path3Adj_nonneg epP3_pos_deg 2
      (fun i => by rw [epP3_deg i]; fin_cases i <;> norm_num)
      (by norm_num)⟩

/-- Entry form of the normalized Laplacian on `2×2` matrices (any
adjacency). -/
theorem epK2_normLap_entry (M : Matrix (Fin 2) (Fin 2) ℝ) (i j : Fin 2) :
    normalizedLaplacian M i j
      = (if i = j then (1 : ℝ) else 0)
        - (Real.sqrt (deg M i))⁻¹ * M i j * (Real.sqrt (deg M j))⁻¹ := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply]

/-- The perturbed degree at the all-true outcome is `2` on every vertex. -/
theorem epK2_allTrue_deg (i : Fin 2) :
    deg (epK2 + perturbWeight epK2 epHalf (fun _ => true)) i = 2 := by
  rw [epK2_perturbed_allTrue_eq, deg_smul, epK2_regular i]
  norm_num

/-- **Scale invariance by raw computation**: the normalized Laplacian of
the weight-`2` edge equals that of the unit edge, entrywise (the
normalized Laplacian of a `c`-scaled regular graph is scale-invariant,
pinned here at the concrete `c = 2`). -/
theorem epK2_normLap_allTrue_eq :
    normalizedLaplacian (epK2 + perturbWeight epK2 epHalf (fun _ => true))
      = normalizedLaplacian epK2 := by
  ext i j
  rw [epK2_normLap_entry, epK2_normLap_entry, epK2_allTrue_deg i,
    epK2_allTrue_deg j, epK2_regular i, epK2_regular j]
  have hent : (epK2 + perturbWeight epK2 epHalf (fun _ => true)) i j
      = 2 * epK2 i j := by
    rw [epK2_perturbed_allTrue_eq, Matrix.smul_apply, smul_eq_mul]
  have hss : Real.sqrt (2 : ℝ) * Real.sqrt 2 = 2 := by
    rw [← sq]
    exact Real.sq_sqrt (by norm_num)
  have hpair : (Real.sqrt (2 : ℝ))⁻¹ * (Real.sqrt 2)⁻¹ = 1 / 2 := by
    rw [← mul_inv, hss]
    norm_num
  have hinv : (Real.sqrt 2)⁻¹ * (2 * epK2 i j) * (Real.sqrt 2)⁻¹
      = epK2 i j := by
    have hre : (Real.sqrt 2)⁻¹ * (2 * epK2 i j) * (Real.sqrt 2)⁻¹
        = ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) * (2 * epK2 i j) := by ring
    rw [hre, hpair]
    ring
  rw [hent, hinv, Real.sqrt_one, inv_one, one_mul, mul_one]

/-- λ₂(L_sym) at the all-true outcome is exactly `2` — the
scale-invariance equality joined to the irregular-Cheeger QA's own
`K₂` pin. -/
theorem epK2_normLap_secondEval_allTrue :
    secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf
        (fun _ => true)))
      (normalizedLaplacian_symmetric _
        (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
          (fun _ => true))))
      (by norm_num) = 2 := by
  rw [secondEval_congr
    (normalizedLaplacian_symmetric _
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
        (fun _ => true))))
    (normalizedLaplacian_symmetric epK2 epK2_symmetric)
    epK2_normLap_allTrue_eq (by norm_num)]
  exact SpectralGraphTheory.QA.icEdge_normLap_secondEval

/-- **The admissible-event non-vacuity witness**: the all-true outcome
stays in the window `[1/2, 2]` (entries `2 ≥ 0`, degrees `2`) — the
admissibility conjunct is satisfiable at a real outcome, so the window
family's events are not structurally empty. -/
theorem epK2_normWindow_allTrue_admissible_QA :
    perturbAdmissible epK2 epHalf (1 / 2) 2 (fun _ => true) := by
  refine ⟨fun i j => epK2_perturbed_allTrue_nonneg i j, fun i => ?_,
    fun i => ?_⟩
  · rw [epK2_allTrue_deg i]
    norm_num
  · rw [epK2_allTrue_deg i]

/-- **The complement witness**: the admissible all-true outcome's
normalized connectivity sits strictly inside the window at `t = 1/2` —
neither disjunct of the bracket event fires at a real admissible
outcome (`λ₂(L_sym) = 2` against floor `-1/8` and ceiling `9`); the
theorem's promise holds non-vacuously at a point. -/
theorem epK2_normWindow_inwindow_QA :
    ¬ (secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf
            (fun _ => true)))
          (normalizedLaplacian_symmetric _
            (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
              (fun _ => true))))
          (by norm_num)
        ≤ ((1 / 2 : ℝ) * (cheegerConstant epK2) ^ 2 / 2 - 1 / 2) / 2)
      ∧ ¬ (2 * ((2 : ℝ) * cheegerConstant epK2) + 1 / 2) / (1 / 2)
        ≤ secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf
            (fun _ => true)))
          (normalizedLaplacian_symmetric _
            (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
              (fun _ => true))))
          (by norm_num) := by
  constructor
  · intro hle
    rw [epK2_cheegerConstant] at hle
    have hval := epK2_normLap_secondEval_allTrue
    linarith
  · intro hle
    rw [epK2_cheegerConstant] at hle
    have hval := epK2_normLap_secondEval_allTrue
    linarith

/-- **The window genuinely restricts the outcome space**: the all-false
outcome (degree `0`) is inadmissible at the same window — the degree
floor excludes it. -/
theorem epK2_normWindow_allFalse_inadmissible_QA :
    ¬ perturbAdmissible epK2 epHalf (1 / 2) 2 (fun _ => false) := by
  rintro ⟨hnn', hdmin', hdmax'⟩
  have hdeg : deg (epK2 + perturbWeight epK2 epHalf (fun _ => false))
      (0 : Fin 2) = 0 := by
    rw [epK2_perturbed_allFalse_eq]
    simp [deg]
  have h0 := hdmin' 0
  rw [hdeg] at h0
  norm_num at h0

/-- **The degree ceiling excludes too**: on `P₃` at `p ≡ 1/4`, the
all-true outcome has nonnegative entries (every outcome does, by
`epP3_perturbed_nonneg`) but middle degree `5 > 3` — the ceiling
conjunct is the one that fails. -/
theorem epP3_normWindow_allTrue_degCeiling_QA :
    ¬ perturbAdmissible path3Adj epQuarter (1 / 2) 3 (fun _ => true) := by
  rintro ⟨hnn', hdmin', hdmax'⟩
  have hentry : ∀ j : Fin 3,
      (path3Adj + perturbWeight path3Adj epQuarter (fun _ => true)) 1 j
        = path3Adj 1 j * (5 / 2 : ℝ) := by
    intro j
    rw [epP3_perturbed_apply]
    congr 1
    norm_num
  have hdeg : deg (path3Adj + perturbWeight path3Adj epQuarter
      (fun _ => true)) 1 = 5 := by
    show ∑ j : Fin 3,
        (path3Adj + perturbWeight path3Adj epQuarter (fun _ => true)) 1 j = 5
    simp only [hentry]
    rw [Fin.sum_univ_three]
    norm_num [path3Adj]
  have h1 := hdmax' 1
  rw [hdeg] at h1
  norm_num at h1

/-- **The normalized Cheeger floor tail on `K₂` at `p ≡ ½`, window
`[1/2, 2]`, `t = ½`, in closed form**: `μ {ω admissible ∧
λ₂(L_sym G_ω) ≤ (1/2·φ²/2 − 1/2)/2 = −1/8} ≤ 4 exp(−1/64)` — the
dimension factor `2 · 2`, the variance norm `8` in the exponent's
denominator. CONDITIONAL ON THE `matrix_hoeffding` AXIOM (instantiated,
not re-proved). -/
theorem epK2_normWindow_floor_tail_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool |
        perturbAdmissible epK2 epHalf (1 / 2) 2 ω ∧
        secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf ω))
            (normalizedLaplacian_symmetric _
              (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω)))
            (by norm_num)
          ≤ ((1 / 2 : ℝ) * (cheegerConstant epK2) ^ 2 / 2 - 1 / 2) / 2}
      ≤ ENNReal.ofReal (4 * Real.exp (-((1 : ℝ)) / 64)) := by
  have htail := edgePerturbation_normalized_cheeger_floor epK2 epHalf
    epK2_symmetric epK2_nonneg epK2_pos_deg (1 / 2) 2
    (fun i => by rw [epK2_regular i]; norm_num) (by norm_num)
    epHalf_nonneg epHalf_le_one (by norm_num) (1 / 2) (by norm_num)
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((1 : ℝ)) / 64) := by
    have h1 : -((1 / 2 : ℝ) ^ 2) / (2 * 8) = -((1 : ℝ)) / 64 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  exact htail

/-- **The normalized connectivity bracket on `K₂` at `p ≡ ½`, window
`[1/2, 2]`, `t = ½`, in closed form** — the same constant as the
one-sided tail (the window contains the sandwich-scaled eigenvalue
ball). CONDITIONAL ON THE `matrix_hoeffding` AXIOM. -/
theorem epK2_normWindow_bracket_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool |
        perturbAdmissible epK2 epHalf (1 / 2) 2 ω ∧
        (secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf ω))
            (normalizedLaplacian_symmetric _
              (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω)))
            (by norm_num)
          ≤ ((1 / 2 : ℝ) * (cheegerConstant epK2) ^ 2 / 2 - 1 / 2) / 2
        ∨ (2 * ((2 : ℝ) * cheegerConstant epK2) + 1 / 2) / (1 / 2)
          ≤ secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf ω))
              (normalizedLaplacian_symmetric _
                (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω)))
              (by norm_num))}
      ≤ ENNReal.ofReal (4 * Real.exp (-((1 : ℝ)) / 64)) := by
  have htail := edgePerturbation_normalized_connectivity_bracket epK2
    epHalf epK2_symmetric epK2_nonneg epK2_pos_deg (1 / 2) 2
    (fun i => by rw [epK2_regular i]; norm_num) (by norm_num)
    (fun i => by rw [epK2_regular i]; norm_num)
    epHalf_nonneg epHalf_le_one (by norm_num) (1 / 2) (by norm_num)
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((1 / 2 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((1 : ℝ)) / 64) := by
    have h1 : -((1 / 2 : ℝ) ^ 2) / (2 * 8) = -((1 : ℝ)) / 64 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  exact htail

/-! ## The swept-Fiedler-cut consumer of the normalized window

The algorithm-facing capstone of the window family
(`edgePerturbation_fiedler_sweep_cut_tail`): the volume-weighted sweep
extraction joined to the normalized connectivity window — the chain
concentration → eigenvalue window → connectivity → *the cut the
spectral-partitioning sweep returns*, on the resampled graph, with high
probability. The tail instances are CONDITIONAL ON THE
`matrix_hoeffding` AXIOM (instantiated, not re-proved); the
good-outcome witness and connectivity pin are hard crust.

Honesty note on the floor-positivity guard
(`0 < dmin·φ²/2 − t`): it is *proof-load-bearing* — it is exactly what
the connectivity transfer consumes (`0 < λ₂(L_sym G_ω) ↔ connected`,
and a non-positive floor no longer forces `λ₂ > 0`) — but no
dropped-guard refutation fixture exists at fixture scale: at 2–3
vertices the tail bound exceeds `1`, so the un-guarded measure
statement cannot be refuted by a lower-bound-only argument (the same
junk-measure obstruction the window family recorded). -/

/-- The support graph of the all-true perturbed `K₂` (the weight-`2`
edge) is connected — by a raw two-vertex walk witness, no spectral
route. -/
theorem epK2_allTrue_supportGraph_connected :
    (supportGraph (epK2 + perturbWeight epK2 epHalf (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
        (fun _ => true)))).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  have hadj : (supportGraph (epK2 + perturbWeight epK2 epHalf (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
        (fun _ => true)))).Adj (0 : Fin 2) 1 := by
    rw [supportGraph_adj]
    refine ⟨by decide, ?_⟩
    rw [epK2_perturbed_allTrue_eq, Matrix.smul_apply, smul_eq_mul]
    have h01 : epK2 (0 : Fin 2) 1 = 1 := by simp [epK2]
    rw [h01]
    norm_num
  refine ⟨0, fun v => ?_⟩
  fin_cases v
  · exact ⟨SimpleGraph.Walk.nil⟩
  · exact ⟨SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil⟩

/-- **The good-outcome witness**: the admissible all-true outcome is
provably *not* in the measured event — its resampled graph is connected
and carries a swept Fiedler cut at `conductance² ≤ 2·λ₂ = 4` (the
deterministic sweep theorem at the pinned spectrum), well inside the
window bound `2·((2·(2·φ) + 1/16)/(1/2)) = 16.25`. The theorem's promise
holds non-vacuously at a real admissible outcome; a wrong constant on
the window ceiling or the sweep constant breaks the numeric join. -/
theorem epK2_sweepWindow_allTrue_not_measured_QA :
    ¬ (perturbAdmissible epK2 epHalf (1 / 2) 2 (fun _ => true) ∧
      ¬ ((supportGraph (epK2 + perturbWeight epK2 epHalf (fun _ => true))
            (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
              (fun _ => true)))).Connected ∧
        ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
          ((∃ u : ℝ, ∀ i, i ∈ S ↔
              u ≤ fiedlerSweepVector (epK2 + perturbWeight epK2 epHalf
                (fun _ => true))
                (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
                  (fun _ => true))) (by norm_num) i)
            ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
              fiedlerSweepVector (epK2 + perturbWeight epK2 epHalf
                (fun _ => true))
                (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
                  (fun _ => true))) (by norm_num) i ≤ u)) ∧
          conductance (epK2 + perturbWeight epK2 epHalf (fun _ => true)) S ^ 2
            ≤ 2 * ((2 * ((2 : ℝ) * cheegerConstant epK2) + 1 / 16)
                / (1 / 2)))) := by
  rintro ⟨hadm, hbad⟩
  have hd' : ∀ i, 0 < deg (epK2 + perturbWeight epK2 epHalf
      (fun _ => true)) i := by
    intro i
    rw [epK2_allTrue_deg i]
    norm_num
  obtain ⟨S, hSne, hScne, hlev, hcond⟩ :=
    fiedler_sweep_cut_normalized (epK2 + perturbWeight epK2 epHalf
        (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => true)))
      epK2_perturbed_allTrue_nonneg hd' (by norm_num)
      epK2_allTrue_supportGraph_connected
  rw [epK2_normLap_secondEval_allTrue] at hcond
  refine hbad ⟨epK2_allTrue_supportGraph_connected, S, hSne, hScne, hlev, ?_⟩
  rw [epK2_cheegerConstant]
  linarith

/-- **The swept-Fiedler-cut tail on `K₂` at `p ≡ ½`, window `[1/2, 2]`,
`t = 1/16`, in closed form**: the failure-of-good-outcome event obeys
`4 exp(−1/4096)` — the dimension factor `2·2`, the variance norm `8`,
and the floor hypothesis genuinely holding
(`0 < 1/2·φ²/2 − 1/16 = 1/16`). CONDITIONAL ON THE `matrix_hoeffding`
AXIOM (instantiated, not re-proved). -/
theorem epK2_sweepWindow_tail_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
      {ω : (Fin 2 × Fin 2) → Bool |
        perturbAdmissible epK2 epHalf (1 / 2) 2 ω ∧
        ¬ ((supportGraph (epK2 + perturbWeight epK2 epHalf ω)
              (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))).Connected ∧
          ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
            ((∃ u : ℝ, ∀ i, i ∈ S ↔
                u ≤ fiedlerSweepVector (epK2 + perturbWeight epK2 epHalf ω)
                  (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))
                  (by norm_num) i)
              ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                fiedlerSweepVector (epK2 + perturbWeight epK2 epHalf ω)
                  (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf ω))
                  (by norm_num) i ≤ u)) ∧
            conductance (epK2 + perturbWeight epK2 epHalf ω) S ^ 2
              ≤ 2 * ((2 * ((2 : ℝ) * cheegerConstant epK2) + 1 / 16)
                  / (1 / 2)))}
      ≤ ENNReal.ofReal (4 * Real.exp (-((1 : ℝ)) / 4096)) := by
  have hfloor : (0 : ℝ) < 1 / 2 * (cheegerConstant epK2) ^ 2 / 2 - 1 / 16 := by
    rw [epK2_cheegerConstant]
    norm_num
  have htail := edgePerturbation_fiedler_sweep_cut_tail epK2
    epHalf epK2_symmetric epK2_nonneg epK2_pos_deg (1 / 2) 2
    (fun i => by rw [epK2_regular i]; norm_num) (by norm_num)
    (fun i => by rw [epK2_regular i]; norm_num)
    epHalf_nonneg epHalf_le_one (hcard := by norm_num) (t := 1 / 16)
    (ht := by norm_num) (hfloor := hfloor)
  rw [epK2_variance_norm] at htail
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 2 * Real.exp (-((1 / 16 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-((1 : ℝ)) / 4096) := by
    have h1 : -((1 / 16 : ℝ) ^ 2) / (2 * 8) = -((1 : ℝ)) / 4096 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  exact htail

/-- **The swept-Fiedler-cut tail on the three-path at `p ≡ ¼`, window
`[1/2, 3]`, `t = 1/16`, in closed form**: `6 exp(−1/6144)` — the
dimension factor `2·3`, the variance norm `12`, the floor hypothesis
`0 < 1/2·φ(P₃)²/2 − 1/16 = 1/16` (φ(P₃) = 1 pinned in the normWindow
section). CONDITIONAL ON THE `matrix_hoeffding` AXIOM. -/
theorem epP3_sweepWindow_tail_QA :
    (bernPMF epQuarter epQuarter_nonneg epQuarter_le_one).toMeasure
      {ω : (Fin 3 × Fin 3) → Bool |
        perturbAdmissible path3Adj epQuarter (1 / 2) 3 ω ∧
        ¬ ((supportGraph (path3Adj + perturbWeight path3Adj epQuarter ω)
              (path3Adj_symmetric.add
                (perturbWeight_isSymm path3Adj epQuarter ω))).Connected ∧
          ∃ S : Finset (Fin 3), S.Nonempty ∧ Sᶜ.Nonempty ∧
            ((∃ u : ℝ, ∀ i, i ∈ S ↔
                u ≤ fiedlerSweepVector (path3Adj
                  + perturbWeight path3Adj epQuarter ω)
                  (path3Adj_symmetric.add
                    (perturbWeight_isSymm path3Adj epQuarter ω))
                  (by norm_num) i)
              ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                fiedlerSweepVector (path3Adj
                  + perturbWeight path3Adj epQuarter ω)
                  (path3Adj_symmetric.add
                    (perturbWeight_isSymm path3Adj epQuarter ω))
                  (by norm_num) i ≤ u)) ∧
            conductance (path3Adj + perturbWeight path3Adj epQuarter ω) S ^ 2
              ≤ 2 * ((2 * ((3 : ℝ) * cheegerConstant path3Adj) + 1 / 16)
                  / (1 / 2)))}
      ≤ ENNReal.ofReal (6 * Real.exp (-((1 : ℝ)) / 6144)) := by
  have hfloor : (0 : ℝ) < 1 / 2 * (cheegerConstant path3Adj) ^ 2 / 2
      - 1 / 16 := by
    rw [epP3_cheegerConstant]
    norm_num
  have htail := edgePerturbation_fiedler_sweep_cut_tail path3Adj
    epQuarter path3Adj_symmetric path3Adj_nonneg epP3_pos_deg (1 / 2) 3
    (fun i => by rw [epP3_deg i]; fin_cases i <;> norm_num) (by norm_num)
    (fun i => by rw [epP3_deg i]; fin_cases i <;> norm_num)
    epQuarter_nonneg epQuarter_le_one (hcard := by norm_num) (t := 1 / 16)
    (ht := by norm_num) (hfloor := hfloor)
  rw [epP3_variance_norm] at htail
  have hcard : (Fintype.card (Fin 3) : ℝ) = 3 := by norm_num
  rw [hcard] at htail
  have hRHS : (2 : ℝ) * 3 * Real.exp (-((1 / 16 : ℝ) ^ 2) / (2 * 12))
      = 6 * Real.exp (-((1 : ℝ)) / 6144) := by
    have h1 : -((1 / 16 : ℝ) ^ 2) / (2 * 12) = -((1 : ℝ)) / 6144 := by norm_num
    rw [h1]
    ring
  rw [hRHS] at htail
  exact htail


/-! ### The C₄ dropped-guard refutation of the floor-positivity guard

The honesty note above ("no dropped-guard refutation fixture exists at
fixture scale: at 2–3 vertices the tail bound exceeds `1`") was
over-narrow, and this section corrects it on the record: the obstruction
analysis was anchored on the *eigenvalue-floor* membership route at
2–3-vertex fixtures, where no admissible-but-disconnected outcome
exists at all. The disconnectedness route is different: bad-set
membership via `¬connected` is `t`-invariant, so at a four-vertex
fixture with a one-degree-loosened window the atom mass of a single
admissible-disconnected outcome lower-bounds the measured event at
every `t`, while the bound `2 d exp(−t²/(2‖Σ‖))` collapses as
`t → ∞`. The guard is thereby *fixture-refuted when dropped*, upgrading
it from "proof-load-bearing, unfalsified" — the
`old_cheeger_lower_bound_refuted_QA` failure class. Everything here is
pure hard crust: a refutation proves a negation and cannot consume the
axiom-conditional theorem (`#print axioms` on the headline: exactly the
standard three). -/

theorem rankOne_mul_rankOne_apply (u v : Fin 4 → ℝ) (i j : Fin 4) :
    (rankOne u * rankOne v) i j = (u ⬝ᵥ v) * u i * v j := by
  simp only [Matrix.mul_apply, rankOne_apply, Matrix.dotProduct]
  calc ∑ x : Fin 4, u i * u x * (v x * v j)
      = ∑ x : Fin 4, (u i * v j) * (u x * v x) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = (u i * v j) * ∑ x : Fin 4, u x * v x := by rw [Finset.mul_sum]
    _ = (∑ x : Fin 4, u x * v x) * u i * v j := by ring

theorem dot_single_left (i : Fin 4) (w : Fin 4 → ℝ) :
    (Pi.single i (1 : ℝ)) ⬝ᵥ w = w i := by
  classical
  simp only [Matrix.dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp

theorem dot_single_sub_single (i j : Fin 4) (hij : i ≠ j) :
    (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) ⬝ᵥ
      (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) = (2 : ℝ) := by
  simp [Pi.single_apply, hij]
  ring

/-! ### The C₄ fixture -/

noncomputable def epHalf4 : (Fin 4 × Fin 4) → ℝ := fun _ => 1 / 2

theorem epHalf4_nonneg : ∀ e, 0 ≤ epHalf4 e := fun e => by norm_num [epHalf4]

theorem epHalf4_le_one : ∀ e, epHalf4 e ≤ 1 := fun e => by norm_num [epHalf4]

/-- The 4-cycle adjacency on `Fin 4` (cycle `0 - 1 - 2 - 3 - 0`): the
odd val-sum pairs are exactly the cycle's ordered edge pairs. -/
def epC4 : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i.val + j.val = 1 ∨ i.val + j.val = 3 ∨ i.val + j.val = 5 then 1 else 0

theorem epC4_apply (i j : Fin 4) :
    epC4 i j =
      if i.val + j.val = 1 ∨ i.val + j.val = 3 ∨ i.val + j.val = 5 then 1 else 0 :=
  rfl

theorem epC4_mem (i j : Fin 4) : epC4 i j = 0 ∨ epC4 i j = 1 := by
  by_cases h : i.val + j.val = 1 ∨ i.val + j.val = 3 ∨ i.val + j.val = 5
  · exact Or.inr (by simp [epC4_apply, h])
  · exact Or.inl (by simp [epC4_apply, h])

theorem epC4_symmetric : epC4.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases h : i.val + j.val = 1 ∨ i.val + j.val = 3 ∨ i.val + j.val = 5
  · have h' : j.val + i.val = 1 ∨ j.val + i.val = 3 ∨ j.val + i.val = 5 := by omega
    simp [epC4_apply, h, h']
  · have h' : ¬(j.val + i.val = 1 ∨ j.val + i.val = 3 ∨ j.val + i.val = 5) := by omega
    simp [epC4_apply, h, h']

theorem epC4_nonneg (i j : Fin 4) : 0 ≤ epC4 i j := by
  rcases epC4_mem i j with h | h; all_goals rw [h]; all_goals norm_num

theorem epC4_deg (i : Fin 4) : deg epC4 i = 2 := by
  fin_cases i <;>
    simp only [deg, epC4_apply, Fin.sum_univ_four,
      show ((3 : Fin 4)).val = 3 from rfl] <;> norm_num

theorem epC4_pos_deg (i : Fin 4) : 0 < deg epC4 i := by
  rw [epC4_deg i]; norm_num

/-- The matching outcome: exactly the two edges `{0, 1}` and `{2, 3}`
are kept (both orientations), all other pairs dropped. -/
def epC4ω : (Fin 4 × Fin 4) → Bool :=
  fun e => decide (e.1.val + e.2.val = 1 ∨ e.1.val + e.2.val = 5)

theorem epC4ω_apply (e : Fin 4 × Fin 4) :
    epC4ω e = decide (e.1.val + e.2.val = 1 ∨ e.1.val + e.2.val = 5) := rfl

/-- The resampled adjacency at the matching outcome: the two kept edges
at weight `2` (base weight `1` plus the centered increment `1`), all
other entries `0`. -/
def epC4M : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j =>
    if i.val + j.val = 1 ∨ i.val + j.val = 5 then 2 else 0

theorem epC4M_apply (i j : Fin 4) :
    epC4M i j = if i.val + j.val = 1 ∨ i.val + j.val = 5 then 2 else 0 := rfl

theorem epC4_perturbed_eq :
    epC4 + perturbWeight epC4 epHalf4 epC4ω = epC4M := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.add_apply, perturbWeight_apply_diag]
    have hw : epC4 i i = 0 := by
      simp only [epC4_apply]
      rw [if_neg (by omega)]
    have hM : epC4M i i = 0 := by
      simp only [epC4M_apply]
      rw [if_neg (by omega)]
    rw [hw, hM]
    norm_num [epC4ω_apply, epHalf4]
  · rw [Matrix.add_apply, perturbWeight_apply_of_ne _ _ _ hij]
    have hcomm : j.val + i.val = i.val + j.val := Nat.add_comm j.val i.val
    have hsymω : epC4ω (j, i) = epC4ω (i, j) := by
      simp only [epC4ω_apply, hcomm]
    have hsymA : epC4 j i = epC4 i j := by
      simp only [epC4_apply, hcomm]
    rw [hsymω, hsymA]
    by_cases h : i.val + j.val = 1 ∨ i.val + j.val = 5
    · have hw : epC4 i j = 1 := by
        simp only [epC4_apply]
        rw [if_pos (by omega :
          i.val + j.val = 1 ∨ i.val + j.val = 3 ∨ i.val + j.val = 5)]
      have hω : epC4ω (i, j) = true := by
        simp only [epC4ω_apply]
        exact decide_eq_true h
      have hM : epC4M i j = 2 := by
        simp only [epC4M_apply]
        rw [if_pos h]
      rw [hw, hω, hM]
      norm_num [epHalf4]
    · have hωf : epC4ω (i, j) = false := by
        simp only [epC4ω_apply]
        exact decide_eq_false h
      rw [hωf]
      by_cases h3 : i.val + j.val = 3
      · have hw : epC4 i j = 1 := by
          simp only [epC4_apply]
          rw [if_pos (by omega :
            i.val + j.val = 1 ∨ i.val + j.val = 3 ∨ i.val + j.val = 5)]
        have hM : epC4M i j = 0 := by
          simp only [epC4M_apply]
          rw [if_neg (by omega)]
        rw [hw, hM]
        norm_num [epHalf4]
      · have hw : epC4 i j = 0 := by
          simp only [epC4_apply]
          rw [if_neg (by omega)]
        have hM : epC4M i j = 0 := by
          simp only [epC4M_apply]
          rw [if_neg (by omega)]
        rw [hw, hM]
        norm_num [epHalf4]

theorem epC4M_symmetric : epC4M.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases h : i.val + j.val = 1 ∨ i.val + j.val = 5
  · have h' : j.val + i.val = 1 ∨ j.val + i.val = 5 := by omega
    simp [epC4M_apply, h, h']
  · have h' : ¬(j.val + i.val = 1 ∨ j.val + i.val = 5) := by omega
    simp [epC4M_apply, h, h']

theorem epC4M_nonneg (i j : Fin 4) : 0 ≤ epC4M i j := by
  simp only [epC4M_apply]
  split_ifs <;> norm_num

theorem epC4M_deg (i : Fin 4) : deg epC4M i = 2 := by
  fin_cases i <;> simp only [deg, epC4M_apply, Fin.sum_univ_four,
    show ((3 : Fin 4)).val = 3 from rfl] <;> norm_num

/-! ### The matching outcome: admissible and disconnected -/

/-- The matching outcome is admissible at the window `[1, 2]`: the
resampled adjacency is nonnegative and every degree is `2`. -/
theorem epC4ω_admissible : perturbAdmissible epC4 epHalf4 1 2 epC4ω := by
  refine ⟨fun i j => ?_, fun i => ?_, fun i => ?_⟩
  · rw [epC4_perturbed_eq]
    exact epC4M_nonneg i j
  · rw [epC4_perturbed_eq, epC4M_deg i]
    norm_num
  · rw [epC4_perturbed_eq, epC4M_deg i]

/-- The Laplacian of the resampled adjacency kills the component
indicator `![1, 1, 0, 0]` — the raw kernel computation behind the
disconnectedness witness. -/
theorem epC4M_lap_mulVec :
    (laplacian epC4M).mulVec ![1, 1, 0, 0] = 0 := by
  have hfin4 : ∀ k : Fin 4, k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    intro k
    fin_cases k <;> simp
  funext i
  rw [Matrix.mulVec, Matrix.dotProduct]
  rcases hfin4 i with rfl | rfl | rfl | rfl <;>
    simp only [laplacian, Matrix.sub_apply, degreeMatrix, deg, epC4M_apply,
      epC4M_deg, Fin.sum_univ_four,
      show ((3 : Fin 4)).val = 3 from rfl] <;> norm_num <;> simp

/-- The matching outcome's resampled support graph is exactly the
support graph of the explicit rescaled matrix. -/
theorem epC4ω_supportGraph_eq :
    supportGraph (epC4 + perturbWeight epC4 epHalf4 epC4ω)
        (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 epC4ω))
      = supportGraph epC4M epC4M_symmetric := by
  ext i j
  rw [supportGraph_adj, supportGraph_adj, epC4_perturbed_eq]

/-- The matching outcome's resampled graph is **disconnected**: the two
weight-`2` edges are separate components. Route: the component indicator
is a non-constant Laplacian-kernel vector, contradicting
connectivity ⇒ kernel-is-constants. -/
theorem epC4ω_supportGraph_not_connected :
    ¬ (supportGraph (epC4 + perturbWeight epC4 epHalf4 epC4ω)
        (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 epC4ω))).Connected := by
  intro hconn
  rw [epC4ω_supportGraph_eq] at hconn
  obtain ⟨c, hc⟩ := exists_const_of_laplacian_mulVec_eq_zero epC4M
    epC4M_symmetric epC4M_nonneg hconn epC4M_lap_mulVec
  have h0 : (1 : ℝ) = c := by
    have h : (![1, 1, 0, 0] : Fin 4 → ℝ) 0 = c := by rw [hc]
    simpa using h
  have h2 : (0 : ℝ) = c := by
    have h : (![1, 1, 0, 0] : Fin 4 → ℝ) 2 = c := by rw [hc]
    simpa using h
  linarith


/-! ### The variance statistic: an explicit upper bound and positivity -/

/-- Every single-edge vector of the design has squared norm at most
`2` (exactly `2` off the diagonal, `0` on it). -/
theorem single_sub_single_dot_le_two (i j : Fin 4) :
    (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) ⬝ᵥ
      (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) ≤ (2 : ℝ) := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [dot_single_sub_single i j hij]

/-- The design's variance statistic is bounded: `‖∑ L_e²‖ ≤ 64`, by the
triangle inequality, submultiplicativity, and the rank-one norm bound
`l2OpNorm_rankOne_le`, with every entry weight bounded by `1`. -/
theorem epC4_varNorm_le :
    ‖∑ e : Fin 4 × Fin 4, perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖ ≤ 64 := by
  have hpair : ∀ e : Fin 4 × Fin 4,
      ‖perturbEdgeLap epC4 e‖ ≤ (2 : ℝ) := by
    intro e
    have hle : ‖rankOne (Pi.single e.1 (1 : ℝ) - Pi.single e.2 (1 : ℝ))‖
        ≤ (Pi.single e.1 (1 : ℝ) - Pi.single e.2 (1 : ℝ)) ⬝ᵥ
          (Pi.single e.1 (1 : ℝ) - Pi.single e.2 (1 : ℝ)) :=
      l2OpNorm_rankOne_le _
    have hd : (Pi.single e.1 (1 : ℝ) - Pi.single e.2 (1 : ℝ)) ⬝ᵥ
        (Pi.single e.1 (1 : ℝ) - Pi.single e.2 (1 : ℝ)) ≤ (2 : ℝ) :=
      single_sub_single_dot_le_two e.1 e.2
    have hkey : |epC4 e.1 e.2| * ((Pi.single e.1 (1 : ℝ) - Pi.single e.2 (1 : ℝ)) ⬝ᵥ
        (Pi.single e.1 (1 : ℝ) - Pi.single e.2 (1 : ℝ))) ≤ (2 : ℝ) := by
      rcases epC4_mem e.1 e.2 with h | h
      · rw [h]
        simp
      · rw [h]
        simp only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1), one_mul]
        exact hd
    rw [perturbEdgeLap, norm_smul, Real.norm_eq_abs]
    refine le_trans (mul_le_mul_of_nonneg_left hle (abs_nonneg _)) ?_
    nlinarith [hkey]
  have hsq : ∀ e : Fin 4 × Fin 4,
      ‖perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖ ≤ (4 : ℝ) := by
    intro e
    have := hpair e
    calc ‖perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖
        ≤ ‖perturbEdgeLap epC4 e‖ * ‖perturbEdgeLap epC4 e‖ := norm_mul_le _ _
      _ ≤ (4 : ℝ) := by nlinarith [norm_nonneg (perturbEdgeLap epC4 e)]
  calc ‖∑ e : Fin 4 × Fin 4, perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖
      ≤ ∑ e : Fin 4 × Fin 4, ‖perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖ :=
        norm_sum_le Finset.univ _
    _ ≤ ∑ _e : Fin 4 × Fin 4, (4 : ℝ) := Finset.sum_le_sum fun e _ => hsq e
    _ = 64 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
        norm_num


/-! ### The variance statistic is genuinely nonzero -/

theorem dot_single_sub_single' (i j : Fin 4) :
    (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ)) ⬝ᵥ
      (Pi.single i (1 : ℝ) - Pi.single j (1 : ℝ))
      = if i = j then (0 : ℝ) else (2 : ℝ) := by
  rcases eq_or_ne i j with rfl | hij
  · simp
  · rw [dot_single_sub_single i j hij]
    simp [hij]

/-- The single-edge vector of the design at the pair `e`. -/
def epVec4 (e : Fin 4 × Fin 4) : Fin 4 → ℝ :=
  Pi.single e.1 (1 : ℝ) - Pi.single e.2 (1 : ℝ)

/-- The `(0, 0)` entry of every summand, spelled for literal
enumeration: `w² · (v ⬝ᵥ v) · v 0²`. -/
theorem epC4_summand_entry (e : Fin 4 × Fin 4) :
    (perturbEdgeLap epC4 e * perturbEdgeLap epC4 e) 0 0
      = epC4 e.1 e.2 * epC4 e.1 e.2
        * (if e.1 = e.2 then (0 : ℝ) else (2 : ℝ))
        * (epVec4 e 0) * (epVec4 e 0) := by
  rw [perturbEdgeLap, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.smul_apply, smul_eq_mul, rankOne_mul_rankOne_apply,
    epVec4, dot_single_sub_single' e.1 e.2]
  ring

/-- The `(0, 0)` entry of the variance statistic is `8`: the four
ordered pairs on the edges at vertex `0` each contribute
`1 · 2 · 1 = 2`. -/
theorem epC4_varEntry :
    (∑ e : Fin 4 × Fin 4, perturbEdgeLap epC4 e * perturbEdgeLap epC4 e) 0 0 = 8 := by
  rw [Matrix.sum_apply, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four]
  rw [epC4_summand_entry (0, 0), epC4_summand_entry (0, 1),
    epC4_summand_entry (0, 2), epC4_summand_entry (0, 3),
    epC4_summand_entry (1, 0), epC4_summand_entry (1, 1),
    epC4_summand_entry (1, 2), epC4_summand_entry (1, 3),
    epC4_summand_entry (2, 0), epC4_summand_entry (2, 1),
    epC4_summand_entry (2, 2), epC4_summand_entry (2, 3),
    epC4_summand_entry (3, 0), epC4_summand_entry (3, 1),
    epC4_summand_entry (3, 2), epC4_summand_entry (3, 3)]
  simp only [epC4_apply, epVec4, Pi.single_apply, Pi.sub_apply, Matrix.of_apply,
    show ((3 : Fin 4)).val = 3 from rfl]
  norm_num
  simp
  norm_num

/-- The variance statistic is genuinely nonzero: its `(0, 0)` entry is
`8`, so the norm is positive — the refutation's exponent divides by a
genuinely positive quantity, not a junk `0`. -/
theorem epC4_varNorm_pos :
    0 < ‖∑ e : Fin 4 × Fin 4, perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖ := by
  have hne : (∑ e : Fin 4 × Fin 4, perturbEdgeLap epC4 e * perturbEdgeLap epC4 e) ≠ 0 := by
    intro h
    have hE := epC4_varEntry
    rw [h] at hE
    simp at hE
  exact norm_pos_iff.mpr hne


/-! ### The atom mass -/

/-- The single matching outcome carries mass `(1/2)^16 = 1/65536`
under the product-Bernoulli design at `p ≡ ½`: all sixteen ordered-pair
coordinates flip fairly. -/
theorem epC4ω_mass :
    (bernPMF epHalf4 epHalf4_nonneg epHalf4_le_one).toMeasure {epC4ω}
      = ENNReal.ofReal ((1 : ℝ) / 65536) := by
  have hmeas : MeasurableSet ({epC4ω} : Set ((Fin 4 × Fin 4) → Bool)) :=
    measurableSet_singleton _
  rw [PMF.toMeasure_apply _ _ hmeas, tsum_fintype]
  simp only [Set.indicator_apply]
  rw [Finset.sum_eq_single epC4ω
    (fun ω _ hne => if_neg (by simp [hne]))
    (fun hmem => absurd (Finset.mem_univ _) hmem)]
  rw [if_pos (Set.mem_singleton epC4ω), bernPMF_apply, jointMass]
  have hfac : ∀ e : Fin 4 × Fin 4,
      bern epHalf4 e (epC4ω e) = ENNReal.ofReal ((1 : ℝ) / 2) := by
    intro e
    cases epC4ω e with
    | false =>
        show ENNReal.ofReal (1 - epHalf4 e) = ENNReal.ofReal ((1 : ℝ) / 2)
        rw [epHalf4]
        norm_num
    | true =>
        show ENNReal.ofReal (epHalf4 e) = ENNReal.ofReal ((1 : ℝ) / 2)
        rw [epHalf4]
  rw [Finset.prod_congr rfl (fun e _ => hfac e), Finset.prod_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← ENNReal.ofReal_pow]
  norm_num
  norm_num


/-! ### The headline refutation -/

/-- **The dropped-guard refutation of the swept-Fiedler-cut tail's
floor-positivity hypothesis.** With every other hypothesis of
`edgePerturbation_fiedler_sweep_cut_tail` genuinely satisfied at the C₄
fixture (symmetric nonnegative weights, positive degrees, window
`[1, 2]` containing them, `p ≡ ½`), but with the guard
`0 < dmin·φ²/2 − t` *dropped* (at `t = 9000` it is exactly what fails),
the would-be conclusion is **false in proved arithmetic**: the measured
event contains the matching outcome — admissible (degrees all `2`) and
disconnected, hence failing the connected-conjunct at *every* `t` — so
its measure is at least the atom mass `1/65536`, while the bound
`8 · exp(−9000²/(2‖Σ‖)) ≤ 8/(1 + 9000²/128) < 1/65536` collapses at
large `t`. The membership route is `t`-invariant disconnectedness, not
the eigenvalue floor — which is why the K₂/P₃-scale obstruction
recorded in the honesty note ("at 2–3 vertices the tail bound exceeds
`1`") does not persist at the four-vertex fixture: the guard is
fixture-refuted when dropped, not merely proof-load-bearing. Pure hard
crust: a refutation cannot consume the axiom-conditional theorem. -/
theorem epC4_sweepWindow_unguarded_refuted_QA :
    ¬ ((bernPMF epHalf4 epHalf4_nonneg epHalf4_le_one).toMeasure
        {ω : (Fin 4 × Fin 4) → Bool |
          perturbAdmissible epC4 epHalf4 1 2 ω ∧
          ¬ ((supportGraph (epC4 + perturbWeight epC4 epHalf4 ω)
                (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))).Connected ∧
              ∃ S : Finset (Fin 4), S.Nonempty ∧ Sᶜ.Nonempty ∧
                ((∃ u : ℝ, ∀ i, i ∈ S ↔
                    u ≤ fiedlerSweepVector (epC4 + perturbWeight epC4 epHalf4 ω)
                      (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))
                      (by norm_num) i)
                  ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                    fiedlerSweepVector (epC4 + perturbWeight epC4 epHalf4 ω)
                      (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))
                      (by norm_num) i ≤ u)) ∧
                conductance (epC4 + perturbWeight epC4 epHalf4 ω) S ^ 2
                  ≤ 2 * ((2 * ((2 : ℝ) * cheegerConstant epC4) + 9000) / 1))}
      ≤ ENNReal.ofReal (2 * (4 : ℝ)
          * Real.exp (-((9000 : ℝ) ^ 2)
            / (2 * ‖∑ e : Fin 4 × Fin 4,
                perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖)))) := by
  intro hle
  have hsub : ({epC4ω} : Set ((Fin 4 × Fin 4) → Bool))
      ⊆ {ω : (Fin 4 × Fin 4) → Bool |
          perturbAdmissible epC4 epHalf4 1 2 ω ∧
          ¬ ((supportGraph (epC4 + perturbWeight epC4 epHalf4 ω)
                (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))).Connected ∧
              ∃ S : Finset (Fin 4), S.Nonempty ∧ Sᶜ.Nonempty ∧
                ((∃ u : ℝ, ∀ i, i ∈ S ↔
                    u ≤ fiedlerSweepVector (epC4 + perturbWeight epC4 epHalf4 ω)
                      (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))
                      (by norm_num) i)
                  ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                    fiedlerSweepVector (epC4 + perturbWeight epC4 epHalf4 ω)
                      (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))
                      (by norm_num) i ≤ u)) ∧
                conductance (epC4 + perturbWeight epC4 epHalf4 ω) S ^ 2
                  ≤ 2 * ((2 * ((2 : ℝ) * cheegerConstant epC4) + 9000) / 1))} := by
    intro ω hω
    simp only [Set.mem_singleton_iff] at hω
    subst hω
    exact ⟨epC4ω_admissible,
      fun hgood => epC4ω_supportGraph_not_connected hgood.1⟩
  have hmono : (bernPMF epHalf4 epHalf4_nonneg epHalf4_le_one).toMeasure {epC4ω}
      ≤ (bernPMF epHalf4 epHalf4_nonneg epHalf4_le_one).toMeasure
          {ω : (Fin 4 × Fin 4) → Bool |
            perturbAdmissible epC4 epHalf4 1 2 ω ∧
            ¬ ((supportGraph (epC4 + perturbWeight epC4 epHalf4 ω)
                  (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))).Connected ∧
                ∃ S : Finset (Fin 4), S.Nonempty ∧ Sᶜ.Nonempty ∧
                  ((∃ u : ℝ, ∀ i, i ∈ S ↔
                      u ≤ fiedlerSweepVector (epC4 + perturbWeight epC4 epHalf4 ω)
                        (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))
                        (by norm_num) i)
                    ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                      fiedlerSweepVector (epC4 + perturbWeight epC4 epHalf4 ω)
                        (epC4_symmetric.add (perturbWeight_isSymm epC4 epHalf4 ω))
                        (by norm_num) i ≤ u)) ∧
                  conductance (epC4 + perturbWeight epC4 epHalf4 ω) S ^ 2
                    ≤ 2 * ((2 * ((2 : ℝ) * cheegerConstant epC4) + 9000) / 1))} :=
    measure_mono hsub
  rw [epC4ω_mass] at hmono
  have hcomb : ENNReal.ofReal ((1 : ℝ) / 65536)
      ≤ ENNReal.ofReal (2 * (4 : ℝ)
          * Real.exp (-((9000 : ℝ) ^ 2)
            / (2 * ‖∑ e : Fin 4 × Fin 4,
                perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖))) :=
    hmono.trans hle
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hcomb
  refine absurd hcomb (not_le.mpr ?_)
  have hvar_le : ‖∑ e : Fin 4 × Fin 4,
      perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖ ≤ 64 := epC4_varNorm_le
  have hvar_pos : (0 : ℝ) < ‖∑ e : Fin 4 × Fin 4,
      perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖ := epC4_varNorm_pos
  have hmono2 : Real.exp (-((9000 : ℝ) ^ 2)
      / (2 * ‖∑ e : Fin 4 × Fin 4,
          perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖))
      ≤ Real.exp (-((9000 : ℝ) ^ 2) / 128) := by
    refine Real.exp_le_exp.2 ?_
    have hquot : ((9000 : ℝ) ^ 2 / 128
        ≤ (9000 : ℝ) ^ 2 / (2 * ‖∑ e : Fin 4 × Fin 4,
            perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖)) := by
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 128) (by positivity)]
      have h2 : (2 : ℝ) * ‖∑ e : Fin 4 × Fin 4,
          perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖ ≤ 128 := by linarith
      exact mul_le_mul_of_nonneg_left h2 (sq_nonneg (9000 : ℝ))
    rw [neg_div, neg_div]
    linarith
  have hinv : Real.exp (-((9000 : ℝ) ^ 2) / 128)
      ≤ 1 / (1 + (9000 : ℝ) ^ 2 / 128) := by
    have hexp : (1 : ℝ) + (9000 : ℝ) ^ 2 / 128 ≤ Real.exp ((9000 : ℝ) ^ 2 / 128) := by
      rw [add_comm]
      exact Real.add_one_le_exp _
    have h1 : Real.exp (-((9000 : ℝ) ^ 2) / 128) * Real.exp ((9000 : ℝ) ^ 2 / 128) = 1 := by
      rw [← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 1 + (9000 : ℝ) ^ 2 / 128)]
    calc Real.exp (-((9000 : ℝ) ^ 2) / 128) * (1 + (9000 : ℝ) ^ 2 / 128)
        ≤ Real.exp (-((9000 : ℝ) ^ 2) / 128) * Real.exp ((9000 : ℝ) ^ 2 / 128) :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_nonneg _)
      _ = 1 := by rw [h1]
  have hlt : (2 : ℝ) * 4 * (1 / (1 + (9000 : ℝ) ^ 2 / 128)) < 1 / 65536 := by
    field_simp
    norm_num
  calc (2 : ℝ) * 4 * Real.exp (-((9000 : ℝ) ^ 2)
          / (2 * ‖∑ e : Fin 4 × Fin 4,
              perturbEdgeLap epC4 e * perturbEdgeLap epC4 e‖))
      ≤ (2 : ℝ) * 4 * Real.exp (-((9000 : ℝ) ^ 2) / 128) :=
        by exact mul_le_mul_of_nonneg_left hmono2 (by norm_num)
    _ ≤ (2 : ℝ) * 4 * (1 / (1 + (9000 : ℝ) ^ 2 / 128)) :=
        by exact mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ < 1 / 65536 := hlt

/-! ## The degenerate-degree corner audit

The parked finding of the window family's honesty notes ("the
normalized Laplacian's junk value at zero-degree corners is the
*identity's* spectrum (`λ₂ = 1`), not the zero matrix's — an easy
mistake to make when predicting refutation fixtures in this family"),
recorded there as a spike-level fact on 2026-08-29's window delivery and
settled here as shelf lemmas (`Normalized.degreeInvSqrt_apply_eq_zero_iff`,
`Normalized.normalizedLaplacian_eq_one_of_forall_deg_nonpos`,
`Spectral.evals_one`) plus the audit instances below.

The negative-degree corner is this audit's own addition to the record:
the honesty note had anchored on zero-degree corners, but the
edge-resampling designs at `p ≠ ½` also produce outcomes with
*negative* degrees (negative off-diagonal entries with negative row
sums) — and `Real.sqrt` of a negative number is `0`, so those outcomes
land on the same identity junk. Both corners are witnessed at one
fixture pair. -/

/-- deg at the all-false `p ≡ ½` outcome is `0` — the zero-degree
corner. -/
theorem epK2_perturbed_allFalse_deg (i : Fin 2) :
    deg (epK2 + perturbWeight epK2 epHalf (fun _ => false)) i = 0 := by
  rw [epK2_perturbed_allFalse_eq]
  simp [deg]

/-- The identity degeneration at the fixture: the all-false outcome's
normalized Laplacian is `1`. -/
theorem epK2_allFalse_normLap_eq_one :
    normalizedLaplacian (epK2 + perturbWeight epK2 epHalf (fun _ => false)) = 1 :=
  normalizedLaplacian_eq_one_of_forall_deg_nonpos _
    (fun i => by simp [epK2_perturbed_allFalse_deg i])

/-- **The parked finding, pinned**: `λ₂` of the normalized Laplacian at
the all-false outcome is exactly `1` — the identity's spectrum
(`evals_one` through the proof-irrelevance bridge `secondEval_congr`). -/
theorem epK2_allFalse_normLap_secondEval_eq_one :
    secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf (fun _ => false)))
      (normalizedLaplacian_symmetric _
        (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false))))
      (by norm_num) = 1 := by
  rw [secondEval_congr _
    (show (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm from Matrix.transpose_one)
    epK2_allFalse_normLap_eq_one (by norm_num)]
  exact evals_one _ _

/-- The easy misprediction — the zero matrix's `0` — refuted in proved
form at the same outcome. -/
theorem epK2_allFalse_normLap_secondEval_ne_zero :
    secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf (fun _ => false)))
      (normalizedLaplacian_symmetric _
        (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false))))
      (by norm_num) ≠ 0 := by
  rw [epK2_allFalse_normLap_secondEval_eq_one]
  norm_num

/-- **The spectral contrast in one proved statement**: at the same
all-false outcome, the combinatorial Laplacian's junk spectrum is the
zero matrix's (`λ₂ = 0`, the existing kernel-plus-trace pin) while the
normalized Laplacian's is the identity's (`λ₂ = 1`) — the two corners
the window family's honesty note distinguishes, exhibited side by side
so a future refutation-fixture design cannot conflate them. -/
theorem epK2_allFalse_spectral_contrast_QA :
    lambda2 (epK2 + perturbWeight epK2 epHalf (fun _ => false))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false)))
      (by norm_num) = 0
      ∧ secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf (fun _ => false)))
        (normalizedLaplacian_symmetric _
          (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false))))
        (by norm_num) = 1 :=
  ⟨epK2_perturbed_allFalse_lambda2_eq_zero, epK2_allFalse_normLap_secondEval_eq_one⟩

/-- **The honesty note's floor-condition mechanism, proved**: at the
all-false outcome the un-windowed floor condition — the conclusion-side
membership of `edgePerturbation_normalized_cheeger_floor` with the
admissibility conjunct dropped, at `dmin = dmax = 1`, `φ(K₂) = 1`,
`t = 0` — is false: `1 ≤ 1/2` fails. This is the proved form of "the
identity's `λ₂ = 1` keeps the un-windowed floor condition false on
`K₂`-shaped fixtures". -/
theorem epK2_allFalse_floor_condition_false_QA :
    ¬ (secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epHalf (fun _ => false)))
        (normalizedLaplacian_symmetric _
          (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false))))
        (by norm_num)
      ≤ (1 : ℝ) * (cheegerConstant epK2) ^ 2 / 2 - 0) := by
  rw [epK2_allFalse_normLap_secondEval_eq_one, epK2_cheegerConstant]
  norm_num

/-- The uniform-one inclusion probabilities — the negative-corner
design point (legal: `0 ≤ 1 ≤ 1`). -/
noncomputable def epOne : (Fin 2 × Fin 2) → ℝ := fun _ => 1

theorem epOne_mem (e) : 0 ≤ epOne e ∧ epOne e ≤ 1 := by
  constructor <;> norm_num [epOne]

/-- The negative-degree corner's fixture: at `p ≡ 1` the all-false
outcome's resampled adjacency is the *negative* edge (entrywise through
the design's entry formulas). -/
theorem epK2_perturbed_allFalse_epOne_eq :
    epK2 + perturbWeight epK2 epOne (fun _ => false) = (-1 : ℝ) • epK2 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, perturbWeight_apply_diag,
      epK2_diag i]
    simp [epOne]
  · rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      perturbWeight_apply_of_ne _ _ _ hij]
    fin_cases i <;> fin_cases j <;> simp [epK2, epOne]

/-- The negative corner's degree profile: `-1 < 0` on every vertex. -/
theorem epK2_perturbed_allFalse_epOne_neg_deg (i : Fin 2) :
    deg (epK2 + perturbWeight epK2 epOne (fun _ => false)) i = -1 := by
  rw [epK2_perturbed_allFalse_epOne_eq, deg_smul, epK2_regular i]
  norm_num

/-- The identity degeneration holds at the negative corner too. -/
theorem epK2_allFalse_epOne_normLap_eq_one :
    normalizedLaplacian (epK2 + perturbWeight epK2 epOne (fun _ => false)) = 1 :=
  normalizedLaplacian_eq_one_of_forall_deg_nonpos _
    (fun i => by simp [epK2_perturbed_allFalse_epOne_neg_deg i])

/-- The negative-degree corner's junk spectrum is the identity's too —
`λ₂ = 1` at a resampled adjacency with strictly negative degrees. -/
theorem epK2_allFalse_epOne_normLap_secondEval_eq_one :
    secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epOne (fun _ => false)))
      (normalizedLaplacian_symmetric _
        (epK2_symmetric.add (perturbWeight_isSymm epK2 epOne (fun _ => false))))
      (by norm_num) = 1 := by
  rw [secondEval_congr _
    (show (1 : Matrix (Fin 2) (Fin 2) ℝ).IsSymm from Matrix.transpose_one)
    epK2_allFalse_epOne_normLap_eq_one (by norm_num)]
  exact evals_one _ _

/-- The vanishing iff exercised on both sides at one fixture pair: the
positive-degree base graph keeps a nonzero reciprocal factor, the
all-false outcome's zero-degree adjacency kills it. -/
theorem epK2_degreeInvSqrt_iff_QA (i : Fin 2) :
    degreeInvSqrt epK2 i i ≠ 0
      ∧ degreeInvSqrt (epK2 + perturbWeight epK2 epHalf (fun _ => false)) i i = 0 :=
  ⟨(degreeInvSqrt_apply_eq_zero_iff epK2 i).not.mpr (by
      simp [epK2_regular i]),
    (degreeInvSqrt_apply_eq_zero_iff _ i).mpr
      (by simp [epK2_perturbed_allFalse_deg i])⟩

/-! ## The degree tail (the degreeTail section)

QA for `hoeffding_inequality`'s first theorem consumer
(`Derived/EdgePerturbationTail.lean`'s degreeTail section, the scalar
sibling of the matrix assemblies above). The tail theorems are
conditional on the `hoeffding_inequality` axiom; these lemmas do not
prove that axiom. What they pin, on the `K₂` fixture:

- the variance statistic exactly: `S₀ = 2`, both incident ordered pairs
  counted (a single-counted statistic `1` is refuted — the double count
  is load-bearing in the exponent);
- the degree-deviation identity at the all-true outcome by two
  independent routes (raw weight-space arithmetic — the resampled graph
  is `2 • K₂`, degree `2` — vs the design's own identity, base degree
  plus summed centered summands `1 + ½ + ½`), and at the all-false
  outcome (degree `0`, joined to the corner-audit's existing pin);
- the closed-form tail instance `μ {|dev| ≥ 1} ≤ 2 exp(−1/4)`;
- the *exact* event measure `1/2` — the agreement event of the two
  incident coordinates, computed through the design's own independence
  machinery (`indepFun_coord` + `toMeasure_cyl`), independently of the
  tail theorem — so the bound's slack at fixture scale is on the record
  (`1/2 ≤ 2 exp(−1/4)`), the same junk-measure obstruction the window
  family records honestly;
- the union-bound instance, with the collapse to `4 exp(−1/4)`
  demonstrated numerically (both vertices' statistics equal on `K₂`) and
  the union event's measure pinned `1/2` (both deviations are the same
  function of the coordinates on `K₂` — the union bound double-counts
  there, honestly).
-/

/-- The four ordered-pair weights of vertex `0` on `K₂`: only the two
off-diagonal pairs are incident with nonzero weight. -/
theorem epK2_degWeight_facts :
    degPerturbWeight epK2 0 (0, 0) = 0
      ∧ degPerturbWeight epK2 0 (0, 1) = 1
      ∧ degPerturbWeight epK2 0 (1, 0) = 1
      ∧ degPerturbWeight epK2 0 (1, 1) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [degPerturbWeight, epK2]

/-- The base degree of `K₂` at `0`. -/
theorem epK2_deg_base : deg epK2 0 = 1 := by
  simp [deg, epK2, Fin.sum_univ_two]

/-- **The degree variance statistic on `K₂`, exactly**: both ordered
pairs incident to vertex `0` carry weight `1`, so the sum of squared
weights is `2`. -/
theorem epK2_degree_variance :
    ∑ e : Fin 2 × Fin 2, (degPerturbWeight epK2 0 e) ^ 2 = 2 := by
  obtain ⟨h00, h01, h10, h11⟩ := epK2_degWeight_facts
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [h00, h01, h10, h11]
  ring_nf

/-- The single-counted statistic is refuted: summing the squared weights
over one orientation per edge would give `1`, but the design's statistic
counts both incident ordered pairs and is `2` — the double count is
load-bearing in the tail's exponent. -/
theorem epK2_degree_variance_ne_one :
    ¬ (∑ e : Fin 2 × Fin 2, (degPerturbWeight epK2 0 e) ^ 2 = 1) := by
  rw [epK2_degree_variance]
  norm_num

/-- **Route A (raw weight-space)**: at the all-true outcome the resampled
adjacency is `2 • K₂` (the perturbation is `K₂` itself), whose degree
at `0` is `2`. -/
theorem epK2_degDev_allTrue_raw :
    deg (epK2 + perturbWeight epK2 epHalf (fun _ => true)) 0 = 2 := by
  have hpw : perturbWeight epK2 epHalf (fun _ => true) = epK2 :=
    epK2_perturbWeight_allTrue
  rw [hpw]
  have h2 : (epK2 + epK2 : Matrix (Fin 2) (Fin 2) ℝ) = (2 : ℝ) • epK2 := by
    ext i j
    simp only [Matrix.add_apply, epK2, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    split_ifs <;> ring_nf
  rw [h2, deg_smul, epK2_deg_base]
  ring_nf

/-- The summed centered degree summands at the all-true outcome:
`½ + ½` from the two incident ordered pairs. -/
theorem epK2_degSum_allTrue :
    ∑ e : Fin 2 × Fin 2,
        degPerturbSummand epK2 epHalf 0 e (fun _ => true) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, degPerturbSummand]
  rw [epK2_degWeight_facts.1, epK2_degWeight_facts.2.1,
    epK2_degWeight_facts.2.2.1, epK2_degWeight_facts.2.2.2]
  simp [epHalf]
  norm_num

/-- **Route B (the design's identity)**: the resampled degree through
`deg_resampled` — base degree plus summed centered summands, `1 + 1` —
a wrong deviation identity breaks exactly this route while route A
survives. -/
theorem epK2_degDev_allTrue_identity :
    deg (epK2 + perturbWeight epK2 epHalf (fun _ => true)) 0 = 2 := by
  rw [deg_resampled, epK2_deg_base, epK2_degSum_allTrue]
  norm_num

/-- **Route B at the all-false outcome**: the resampled degree is
`1 − ½ − ½ = 0` through the identity, joined to the corner-audit's
existing raw pin (`epK2_perturbed_allFalse_deg`) — the identity holds
at the other extreme of the design's outcome space. -/
theorem epK2_degDev_allFalse_identity :
    deg (epK2 + perturbWeight epK2 epHalf (fun _ => false)) 0 = 0 := by
  rw [deg_resampled, epK2_deg_base]
  have hsum : ∑ e : Fin 2 × Fin 2,
      degPerturbSummand epK2 epHalf 0 e (fun _ => false) = -1 := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, degPerturbSummand]
    rw [epK2_degWeight_facts.1, epK2_degWeight_facts.2.1,
      epK2_degWeight_facts.2.2.1, epK2_degWeight_facts.2.2.2]
    simp [epHalf]
    norm_num
  rw [hsum]
  ring

/-- The resampled degree of `K₂` at `0` under the uniform-half design is
exactly the sum of the two incident coordinate indicators — the
deviation is `δ₀₁ + δ₁₀ − 1`, taking the values `−1, 0, 1`. -/
theorem epK2_degResampled_eq (ω : (Fin 2 × Fin 2) → Bool) :
    deg (epK2 + perturbWeight epK2 epHalf ω) 0
      = (if ω (0, 1) then (1 : ℝ) else 0)
        + (if ω (1, 0) then (1 : ℝ) else 0) := by
  have h := deg_resampled epK2 epHalf ω 0
  have hsum : ∑ e : Fin 2 × Fin 2, degPerturbSummand epK2 epHalf 0 e ω
      = ((if ω (0, 1) then (1 : ℝ) else 0) - epHalf (0, 1))
        + ((if ω (1, 0) then (1 : ℝ) else 0) - epHalf (1, 0)) := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, degPerturbSummand]
    rw [epK2_degWeight_facts.1, epK2_degWeight_facts.2.1,
      epK2_degWeight_facts.2.2.1, epK2_degWeight_facts.2.2.2]
    simp [epHalf]
  rw [h, hsum, epK2_deg_base]
  simp [epHalf]
  ring

/-- **The closed-form degree tail instance on `K₂`** at `t = 1`:
`μ {|deg G_ω 0 − deg K₂ 0| ≥ 1} ≤ 2 exp(−1/4)` — the scalar axiom's
prefactor `2` (no dimension factor) and the variance statistic `2` in
the denominator `2 · 2`. CONDITIONAL ON THE `hoeffding_inequality` AXIOM
(instantiated, not re-proved). -/
theorem epK2_degree_tail_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool |
          (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) 0 - deg epK2 0|}
      ≤ ENNReal.ofReal (2 * Real.exp (-((1 : ℝ) ^ 2) / 4)) := by
  have htail := edgePerturbation_degree_tail epK2 epHalf epHalf_nonneg
    epHalf_le_one 0 1 zero_le_one
  rw [epK2_degree_variance] at htail
  have hRHS : (2 : ℝ) * Real.exp (-((1 : ℝ) ^ 2) / (2 * 2))
      = 2 * Real.exp (-((1 : ℝ) ^ 2) / 4) := by
    ring
  rw [show 2 * Real.exp (-((1 : ℝ) ^ 2) / 4)
      = 2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * 2)) from hRHS.symm]
  exact htail

/-- The single-coordinate cylinder masses at the fair coin: each incident
coordinate carries mass `½`. -/
theorem epK2_cyl_mass (e : Fin 2 × Fin 2) (b : Bool) :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        ((fun ω : (Fin 2 × Fin 2) → Bool => ω e) ⁻¹' {b})
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  rw [toMeasure_cyl epHalf epHalf_nonneg epHalf_le_one e {b}]
  cases b with
  | true => simp [bern, epHalf]
  | false => simp [bern, epHalf]; ring_nf

/-- **The exact event measure**: the degree-deviation event at `t = 1` on
`K₂` is exactly the agreement event of the two incident coordinates, of
measure `¼ + ¼ = ½` — computed through the design's own independence
machinery (`indepFun_coord` + `toMeasure_cyl`), independently of the tail
theorem. With the closed-form bound above this pins the honest slack
`1/2 ≤ 2 exp(−1/4)` (the same junk-measure obstruction the window family
records: at fixture scale the exponential never drops below the atom
masses, so no wrong-constant refutation exists here — the exactness pins
above carry the falsification content). -/
theorem epK2_degree_event_measure :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool |
          (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) 0 - deg epK2 0|}
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hE : {ω : (Fin 2 × Fin 2) → Bool |
      (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) 0 - deg epK2 0|}
      = ((fun ω : (Fin 2 × Fin 2) → Bool => ω (0, 1)) ⁻¹' {true}
            ∩ (fun ω : (Fin 2 × Fin 2) → Bool => ω (1, 0)) ⁻¹' {true})
        ∪ ((fun ω : (Fin 2 × Fin 2) → Bool => ω (0, 1)) ⁻¹' {false}
            ∩ (fun ω : (Fin 2 × Fin 2) → Bool => ω (1, 0)) ⁻¹' {false}) := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    rw [epK2_degResampled_eq ω, epK2_deg_base]
    cases h1 : ω (0, 1) <;> cases h2 : ω (1, 0) <;> simp [h1, h2]
  have hdisj : Disjoint
      ((fun ω : (Fin 2 × Fin 2) → Bool => ω (0, 1)) ⁻¹' {true}
        ∩ (fun ω : (Fin 2 × Fin 2) → Bool => ω (1, 0)) ⁻¹' {true})
      ((fun ω : (Fin 2 × Fin 2) → Bool => ω (0, 1)) ⁻¹' {false}
        ∩ (fun ω : (Fin 2 × Fin 2) → Bool => ω (1, 0)) ⁻¹' {false}) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_empty_iff_false]
    cases ω (0, 1) <;> simp
  have hm2 : MeasurableSet
      ((fun ω : (Fin 2 × Fin 2) → Bool => ω (0, 1)) ⁻¹' {false}
        ∩ (fun ω : (Fin 2 × Fin 2) → Bool => ω (1, 0)) ⁻¹' {false}) :=
    ((measurable_coord (0, 1)) (Set.toFinite ({false} : Set Bool)).measurableSet).inter
      ((measurable_coord (1, 0)) (Set.toFinite ({false} : Set Bool)).measurableSet)
  have hnee : ((0, 1) : Fin 2 × Fin 2) ≠ (1, 0) := by
    decide
  have hindep := indepFun_coord epHalf epHalf_nonneg epHalf_le_one hnee
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hindep
  have hTT := hindep {true} {true}
    ((Set.toFinite ({true} : Set Bool)).measurableSet)
    ((Set.toFinite ({true} : Set Bool)).measurableSet)
  have hFF := hindep {false} {false}
    ((Set.toFinite ({false} : Set Bool)).measurableSet)
    ((Set.toFinite ({false} : Set Bool)).measurableSet)
  rw [hE, measure_union hdisj hm2, hTT, hFF,
    epK2_cyl_mass (0, 1) true, epK2_cyl_mass (1, 0) true,
    epK2_cyl_mass (0, 1) false, epK2_cyl_mass (1, 0) false]
  rw [← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  ring_nf

/-- **The union-bound instance on `K₂`**: the all-vertices tail at
`t = 1` against the summed bound, collapsed numerically to
`4 exp(−1/4)` (both vertices' variance statistics are `2` — the collapse
that needs per-vertex positivity in general is exact here). CONDITIONAL
ON THE `hoeffding_inequality` AXIOM via the union theorem. -/
theorem epK2_degree_tail_all_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool |
          ∃ v, (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) v
            - deg epK2 v|}
      ≤ ∑ _v : Fin 2, ENNReal.ofReal (2 * Real.exp (-((1 : ℝ) ^ 2) / 4)) := by
  have htail := edgePerturbation_degree_tail_all epK2 epHalf epHalf_nonneg
    epHalf_le_one 1 zero_le_one
  have hvar : ∀ v : Fin 2, ∑ e : Fin 2 × Fin 2, (degPerturbWeight epK2 v e) ^ 2
      = 2 := by
    intro v
    have hc : ∀ w : Fin 2, w = 0 ∨ w = 1 := by
      intro w
      fin_cases w <;> simp
    rcases hc v with rfl | rfl
    · exact epK2_degree_variance
    · rw [Fintype.sum_prod_type]
      simp only [Fin.sum_univ_two, degPerturbWeight, epK2]
      norm_num
  simp only [hvar] at htail
  have hRHS : (2 : ℝ) * Real.exp (-((1 : ℝ) ^ 2) / (2 * 2))
      = 2 * Real.exp (-((1 : ℝ) ^ 2) / 4) := by
    ring
  have hsum : ∑ v : Fin 2,
      ENNReal.ofReal (2 * Real.exp (-((1 : ℝ) ^ 2) / (2 * 2)))
      = ∑ v : Fin 2, ENNReal.ofReal (2 * Real.exp (-((1 : ℝ) ^ 2) / 4)) :=
    Finset.sum_congr rfl fun _ _ => by rw [hRHS]
  rw [hsum] at htail
  exact htail

/-- The union event's measure is also exactly `1/2` — on `K₂` both
vertices' deviations are the same function of the coordinates, so the
existential adds nothing and the union bound double-counts: the honest
slack of the union form is on the record beside the per-vertex one. -/
theorem epK2_degree_event_all_measure :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool |
          ∃ v, (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) v
            - deg epK2 v|}
      = ENNReal.ofReal ((1 : ℝ) / 2) := by
  have hEq : {ω : (Fin 2 × Fin 2) → Bool |
      ∃ v, (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) v
        - deg epK2 v|}
      = {ω : (Fin 2 × Fin 2) → Bool |
          (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) 0
            - deg epK2 0|} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv⟩
      have hc : ∀ w : Fin 2, w = 0 ∨ w = 1 := by
        intro w
        fin_cases w <;> simp
      rcases hc v with rfl | rfl
      · exact hv
      · have h1 : deg epK2 1 = 1 := by simp [deg, epK2, Fin.sum_univ_two]
        have h2 : deg (epK2 + perturbWeight epK2 epHalf ω) 1
            = (if ω (0, 1) then (1 : ℝ) else 0)
              + (if ω (1, 0) then (1 : ℝ) else 0) := by
          have h := deg_resampled epK2 epHalf ω 1
          have hsum : ∑ e : Fin 2 × Fin 2, degPerturbSummand epK2 epHalf 1 e ω
              = ((if ω (0, 1) then (1 : ℝ) else 0) - epHalf (0, 1))
                + ((if ω (1, 0) then (1 : ℝ) else 0) - epHalf (1, 0)) := by
            rw [Fintype.sum_prod_type]
            simp only [Fin.sum_univ_two, degPerturbSummand, degPerturbWeight]
            cases ω (0, 1) <;> cases ω (1, 0) <;>
              simp [epK2, epHalf]
          rw [h, hsum, h1]
          simp [epHalf]
          ring
        rw [epK2_degResampled_eq ω, epK2_deg_base]
        rw [h2, h1] at hv
        exact hv
    · intro hv
      exact ⟨0, hv⟩
  rw [hEq, epK2_degree_event_measure]

/-! ## The Bernstein twin (the bernsteinTwin section)

QA for `bernstein_inequality`'s and `bernstein_bounded_variance`'s first
theorem consumers (`Derived/EdgePerturbationTail.lean`'s bernsteinTwin
section, the variance-adaptive siblings of the degreeTail section
above). The tail theorems are conditional on their respective axioms;
these lemmas do not prove those axioms. What they pin, on the `K₂`
fixture at the fair coin:

- the *true* variance statistic exactly: `σ²₀ = ∑ₑ w² p (1 − p) = ½`,
  with the Poisson-trial shape `∑ₑ w² p = 1` (the dropped-`(1 − p)`
  degeneration) refuted — the centered-vs-uncentered distinction is
  load-bearing in the Bernstein denominator;
- the fourfold variance reduction as an equation: `σ²₀ = S₀/4` where
  `S₀ = ∑ₑ w² = 2` is the Hoeffding twin's range statistic —
  `p (1 − p) = ¼` is sharp at the fair coin, so `σ²_v ≤ S_v/4` holds
  with equality at this fixture;
- the engine's variance integral at an incident pair: `∫ X_e² = ¼`;
- the **strict variance-adaptivity improvement, proved**:
  `2 exp(−3/5) < 2 exp(−1/4)` — the Bernstein bound at the exact
  statistic strictly beats the delivered Hoeffding bound at the same
  fixture and threshold (`t = 1`, `M = 1`), by strict monotonicity of
  `exp` at `1/4 < 3/5`. This is the cross-axiom coherence check:
  variance adaptivity is a real strengthening at moderate `t`, not a
  reparametrization;
- the budget relaxation pinned honest: the budget bound dominates the
  exact-statistic bound;
- the two closed-form conditional tail instances (`2 exp(−3/5)` exact,
  `2 exp(−3/8)` at the budget `Vbud = 1`).
-/

section BernsteinTwin

open Scaffold.Derived.EdgePerturbationTail

/-- **The Bernstein variance statistic on K₂, exactly**: both incident
ordered pairs carry weight `1` at the fair coin `p ≡ ½`, so
`σ² = 2 · ½ · ½ = ½`. -/
theorem epK2_degree_bernstein_variance :
    ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 0 e) ^ 2 * epHalf e * (1 - epHalf e) = 1 / 2 := by
  obtain ⟨h00, h01, h10, h11⟩ := epK2_degWeight_facts
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [h00, h01, h10, h11]
  simp [epHalf]
  norm_num

/-- The Poisson-trial shape is refuted: dropping the `(1 − p)` factor
would give `∑ w² p = 1` at this fixture, but the true variance statistic
is `½` — the centered-vs-uncentered distinction is load-bearing in the
Bernstein denominator. -/
theorem epK2_degree_bernstein_variance_ne_one :
    ¬ (∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 0 e) ^ 2 * epHalf e * (1 - epHalf e) = 1) := by
  rw [epK2_degree_bernstein_variance]
  norm_num

/-- **The fourfold variance reduction, pinned as an equation**: at the
fair coin the Bernstein statistic is exactly the Hoeffding range
statistic over four (`½ = 2/4`) — `p (1 − p) = ¼` is sharp there, so the
general bound `σ²_v ≤ S_v/4` holds with equality at this fixture. -/
theorem epK2_bernstein_variance_quarter :
    ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 0 e) ^ 2 * epHalf e * (1 - epHalf e)
      = (∑ e : Fin 2 × Fin 2, (degPerturbWeight epK2 0 e) ^ 2) / 4 := by
  rw [epK2_degree_bernstein_variance, epK2_degree_variance]
  norm_num

/-- The engine's variance integral pinned at the incident pair:
`∫ X_{(0,1)}² = 1² · ½ · ½ = ¼`. -/
theorem epK2_engine_variance :
    ∫ ω : (Fin 2 × Fin 2) → Bool,
        (degPerturbSummand epK2 epHalf 0 (0, 1) ω) ^ 2
      ∂(bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure = 1 / 4 := by
  rw [integral_sq_degPerturbSummand epK2 epHalf epHalf_nonneg epHalf_le_one 0 (0, 1)]
  rw [epK2_degWeight_facts.2.1]
  simp only [epHalf]
  norm_num

/-- The magnitude bound `M = 1` holds at the fixture: every incident
weight is `0` or `1`. -/
theorem epK2_degree_bernstein_M :
    ∀ e : Fin 2 × Fin 2, |degPerturbWeight epK2 0 e| ≤ 1 := by
  intro e
  unfold degPerturbWeight epK2
  simp only [Matrix.of_apply]
  by_cases h2 : e.1 = e.2 <;> by_cases h1 : (0 : Fin 2) = e.1 ∨ (0 : Fin 2) = e.2 <;>
    simp [h1, h2]

/-- The budget-form variance hypothesis at `Vbud = 1`. -/
theorem epK2_bernstein_budget_var :
    ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 0 e) ^ 2 * epHalf e * (1 - epHalf e) ≤ 1 := by
  rw [epK2_degree_bernstein_variance]
  norm_num

/-- **The closed-form Bernstein degree tail instance on `K₂`** at `t = 1`,
`M = 1`: `μ {|dev| ≥ 1} ≤ 2 exp(−3/5)` — the denominator
`2 σ² + 2Mt/3 = 1 + 2/3 = 5/3`. CONDITIONAL ON THE
`bernstein_inequality` AXIOM (instantiated, not re-proved). -/
theorem epK2_degree_tail_bernstein_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool |
          (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) 0 - deg epK2 0|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(3 / 5 : ℝ))) := by
  have htail := edgePerturbation_degree_tail_bernstein epK2 epHalf epHalf_nonneg
    epHalf_le_one 0 epK2_degree_bernstein_M 1 zero_le_one
  rw [epK2_degree_bernstein_variance] at htail
  have hRHS : (2 : ℝ) * Real.exp (-((1 : ℝ) ^ 2) / (2 * (1 / 2) + (2 * 1 * 1) / 3))
      = 2 * Real.exp (-(3 / 5 : ℝ)) := by
    rw [one_pow]
    norm_num
  rw [hRHS] at htail
  exact htail

/-- **The budget instance** at `Vbud = 1`: the coarser denominator
`2 · 1 + 2/3 = 8/3` gives `2 exp(−3/8)`. CONDITIONAL ON THE
`bernstein_bounded_variance` AXIOM (instantiated, not re-proved). -/
theorem epK2_degree_tail_bernstein_budget_QA :
    (bernPMF epHalf epHalf_nonneg epHalf_le_one).toMeasure
        {ω : (Fin 2 × Fin 2) → Bool |
          (1 : ℝ) ≤ |deg (epK2 + perturbWeight epK2 epHalf ω) 0 - deg epK2 0|}
      ≤ ENNReal.ofReal (2 * Real.exp (-(3 / 8 : ℝ))) := by
  have htail := edgePerturbation_degree_tail_bernstein_budget epK2 epHalf
    epHalf_nonneg epHalf_le_one 0 epK2_degree_bernstein_M (Vbud := 1)
    epK2_bernstein_budget_var 1 zero_le_one
  have hRHS : (2 : ℝ) * Real.exp (-((1 : ℝ) ^ 2) / (2 * 1 + (2 * 1 * 1) / 3))
      = 2 * Real.exp (-(3 / 8 : ℝ)) := by
    rw [one_pow]
    norm_num
  rw [hRHS] at htail
  exact htail

/-- **The strict variance-adaptivity improvement, proved**: the Bernstein
bound at the exact statistic strictly beats the Hoeffding bound at the
same fixture and threshold — `2 exp(−3/5) < 2 exp(−1/4)` because
`1/4 < 3/5` and `exp` is strictly monotone. This is the cross-axiom
coherence check: variance adaptivity is a real strengthening at
moderate `t`, not a reparametrization. Hard crust, standard three
axioms only. -/
theorem epK2_bernstein_beats_hoeffding :
    (2 : ℝ) * Real.exp (-(3 / 5 : ℝ)) < 2 * Real.exp (-((1 : ℝ) / 4)) := by
  have h : (-(3 / 5 : ℝ)) < -((1 : ℝ) / 4) := by norm_num
  have he := Real.exp_lt_exp.mpr h
  exact mul_lt_mul_of_pos_left he zero_lt_two

/-- The budget relaxation is honest (weaker, never stronger): the
budget bound dominates the exact-statistic bound — `3/8 ≤ 3/5` in the
exponent. Hard crust, standard three axioms only. -/
theorem epK2_bernstein_exact_le_budget :
    (2 : ℝ) * Real.exp (-(3 / 5 : ℝ)) ≤ 2 * Real.exp (-(3 / 8 : ℝ)) := by
  have h : (-(3 / 5 : ℝ)) ≤ -(3 / 8 : ℝ) := by norm_num
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h) zero_le_two

end BernsteinTwin

/-! ## The admissibility dissolution (the AdmissibilityDissolution
section)

QA for the window family's first unconditional measured event
(`Derived/EdgePerturbationTail.lean`'s dissolution section, the
degree-concentration proposal's priced follow-on). The unconditional
bracket is conditional on the `matrix_hoeffding` and
`hoeffding_inequality` axioms together; these lemmas do not prove either
axiom. What they pin, on the `K₂` fixture:

- the pair design condition at the uniform designs: `p ≡ ½` satisfies
  it with *equality* (the boundary), `p ≡ 1/10` with slack;
- the boundary entry pin: at `p ≡ ½` the all-false outcome's
  off-diagonal entry is exactly `0` — nonnegative *at* the boundary,
  not strictly inside it (the engine's inequality is tight there);
- the dropped-pair-condition fence: at `p ≡ 9/10` (inside `[0, 1]`,
  violating only the pair condition) the same entry is exactly `−4/5` —
  nonnegativity genuinely fails, the design condition is load-bearing;
- the transfer's positive witness: at `p ≡ 1/10` the all-false
  outcome's deviation is exactly `|−1/5| < 1/2` at both vertices, so
  with base degrees `1` in the shrunk window `[1, 2]` the outcome lands
  inside the admissibility window `[1/2, 5/2]`, the derived degree
  `4/5` pinned by the design's own identity;
- the strictness boundary, coherent: at `p ≡ ½` the all-false outcome's
  deviation is `1 ≥ s = 1/2` — in the degree tail's event, exactly
  where the transfer does not apply — and indeed not admissible;
- the closed-form instance: the *unconditioned* window-exit event
  bounded by `4 exp(−1/4096) + 4 exp(−1/16)` on `K₂` at the
  `p ≡ 1/10` design, window `[1/2, 5/2]`, `s = 1/2`, `t = 1/16`.

The same-day completion (the floor and swept-cut members below) adds:
the all-false disconnectedness witness (the empty resampled graph,
by the kernel-constancy contrapositive); the **strict-containment
witness** — the all-false outcome sits in the unconditional sweep bad
event while provably not admissible, so the dissolution genuinely
enlarges the measured event and the degree-tail term is its honest
price; the good-outcome conjunction at the dissolution's window (the
unconditional bad event is not all of `Ω`); and the two closed-form
instances (`4 exp(−1/4096) + 4 exp(−1/16)` each). -/

section AdmissibilityDissolution

/-- The one-tenth design. -/
noncomputable def epTenth : (Fin 2 × Fin 2) → ℝ := fun _ => 1 / 10

theorem epTenth_nonneg : ∀ e, 0 ≤ epTenth e := by
  intro e; unfold epTenth; norm_num

theorem epTenth_le_one : ∀ e, epTenth e ≤ 1 := by
  intro e; unfold epTenth; norm_num

/-- **The pair design condition at the uniform designs**: `p ≡ ½`
satisfies it with equality (the boundary of the hypothesis), `p ≡ 1/10`
with slack. -/
theorem epHalf_pair : ∀ e : Fin 2 × Fin 2,
    epHalf e + epHalf (e.2, e.1) ≤ 1 := by
  intro e; unfold epHalf; norm_num

theorem epTenth_pair : ∀ e : Fin 2 × Fin 2,
    epTenth e + epTenth (e.2, e.1) ≤ 1 := by
  intro e; unfold epTenth; norm_num

/-- **The boundary entry pin**: at the uniform design `p ≡ ½` the pair
condition is tight, and the all-false outcome's off-diagonal entry is
exactly `0` — nonnegative at the boundary, not strictly inside it
(joined to the corner audit's whole-matrix pin
`epK2_perturbed_allFalse_eq`). -/
theorem epK2_dissolve_entry_allFalse_eq_zero :
    (epK2 + perturbWeight epK2 epHalf (fun _ => false)) 0 1 = 0 := by
  rw [Matrix.add_apply, perturbWeight_apply_of_ne epK2 epHalf
    (fun _ => false) (by norm_num)]
  simp only [epK2, Matrix.of_apply, epHalf]
  norm_num

/-- The engine lemma instantiated at the boundary outcome (hard crust;
the pin above shows its inequality is exactly tight here). -/
theorem epK2_dissolve_engine_allFalse_nonneg :
    0 ≤ (epK2 + perturbWeight epK2 epHalf (fun _ => false)) 0 1 :=
  perturbWeight_entry_nonneg epK2 epHalf epK2_symmetric
    (fun i j => epK2_nonneg i j) epHalf_le_one epHalf_pair
    (fun _ => false) 0 1

/-- **The dropped-pair-condition fence**: at `p ≡ 9/10` (inside
`[0, 1]`, violating only the pair condition `p e + p eᵀ ≤ 1`) the
all-false outcome's off-diagonal entry is exactly `−4/5` —
nonnegativity genuinely fails. The design condition is load-bearing for
the dissolution's nonnegativity half; every *other* hypothesis of the
engine lemma holds at this design point. -/
theorem epK2_dissolve_entry_nineTenth_eq :
    (epK2 + perturbWeight epK2 (fun _ => (9 / 10 : ℝ)) (fun _ => false))
      0 1 = -(4 / 5) := by
  rw [Matrix.add_apply, perturbWeight_apply_of_ne epK2
    (fun _ => (9 / 10 : ℝ)) (fun _ => false) (by norm_num)]
  simp only [epK2, Matrix.of_apply]
  norm_num

theorem epK2_dissolve_pairCond_refuted :
    ¬ 0 ≤ (epK2 + perturbWeight epK2 (fun _ => (9 / 10 : ℝ))
        (fun _ => false)) 0 1 := by
  rw [epK2_dissolve_entry_nineTenth_eq]
  norm_num

/-- The summed centered degree summands at `p ≡ 1/10`, all-false:
`−1/10 − 1/10 = −1/5` at each vertex (both vertices endpoints of both
off-diagonal ordered pairs; the diagonal pairs carry weight `0`). -/
theorem epK2_tenth_degSum_allFalse (v : Fin 2) :
    ∑ e : Fin 2 × Fin 2,
        degPerturbSummand epK2 epTenth v e (fun _ => false) = -(1 / 5) := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, degPerturbSummand, degPerturbWeight, epTenth]
  fin_cases v <;> simp [epK2] <;> norm_num

/-- **The transfer's positive witness**: at `p ≡ 1/10` the all-false
outcome's degree deviation is exactly `|−1/5| < 1/2` at both vertices —
the strict bound the transfer helper needs, at genuine slack. -/
theorem epK2_tenth_degDev_allFalse_lt :
    ∀ v, |deg (epK2 + perturbWeight epK2 epTenth (fun _ => false)) v
      - deg epK2 v| < 1 / 2 := by
  intro v
  rw [deg_resampled, epK2_regular v, epK2_tenth_degSum_allFalse v]
  simp [abs_lt]
  norm_num

/-- **The derived admissibility**, through the transfer helper: base
degrees `1` in the shrunk window `[1, 2]` (`dmin = 1/2`, `dmax = 5/2`,
`s = 1/2`), deviations `1/5 < 1/2` — the outcome lands inside
`[1/2, 5/2]`. -/
theorem epK2_tenth_allFalse_admissible :
    perturbAdmissible epK2 epTenth (1 / 2) (5 / 2) (fun _ => false) := by
  refine perturbAdmissible_of_degDev_lt epK2 epTenth epK2_symmetric
    (fun i j => epK2_nonneg i j) epTenth_le_one epTenth_pair
    (1 / 2) (5 / 2) (1 / 2) ?_ ?_
    epK2_tenth_degDev_allFalse_lt
  · intro i
    rw [epK2_regular i]; norm_num
  · intro i
    rw [epK2_regular i]; norm_num

/-- The derived degree at the witness outcome, by the design's own
identity: base `1` plus deviation `−1/5` gives `4/5`, inside
`[1/2, 5/2]` — a wrong deviation identity breaks exactly this. -/
theorem epK2_tenth_allFalse_deg :
    deg (epK2 + perturbWeight epK2 epTenth (fun _ => false)) 0 = 4 / 5 := by
  rw [deg_resampled, epK2_deg_base, epK2_tenth_degSum_allFalse 0]
  norm_num

/-- **The strictness boundary, coherent**: at `p ≡ ½` the all-false
outcome's deviation is `|−1| = 1 ≥ s = 1/2` — it sits in the degree
tail's event, exactly where the transfer helper does not apply — and
indeed it is *not* admissible (degree `0` below the floor `1/2`). The
helper's strict `< s` is honest, not an artifact. -/
theorem epK2_half_allFalse_inDevEvent :
    ∃ v : Fin 2, 1 / 2
      ≤ |deg (epK2 + perturbWeight epK2 epHalf (fun _ => false)) v
        - deg epK2 v| := by
  refine ⟨0, ?_⟩
  rw [deg_resampled, epK2_deg_base]
  have hsum : ∑ e : Fin 2 × Fin 2,
      degPerturbSummand epK2 epHalf 0 e (fun _ => false) = -1 := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two, degPerturbSummand, degPerturbWeight, epHalf]
    simp [epK2]
    norm_num
  rw [hsum]
  simp [abs_lt]
  norm_num

theorem epK2_half_allFalse_not_admissible :
    ¬ perturbAdmissible epK2 epHalf (1 / 2) (5 / 2) (fun _ => false) := by
  rintro ⟨-, hdmin', -⟩
  have hdeg : deg (epK2 + perturbWeight epK2 epHalf (fun _ => false))
      (0 : Fin 2) = 0 := epK2_perturbed_allFalse_deg 0
  have h0 := hdmin' 0
  rw [hdeg] at h0
  norm_num at h0

/-- The degree variance statistic at both vertices (the delivered
tail's per-vertex statistic `S_v = 2` on `K₂`, all four ordered pairs
enumerated — the ∀-vertex form the closed-form instance's `∑ v`
consumes). -/
theorem epK2_degree_variance' (v : Fin 2) :
    ∑ e : Fin 2 × Fin 2, (degPerturbWeight epK2 v e) ^ 2 = 2 := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, degPerturbWeight]
  fin_cases v <;> simp [epK2] <;> norm_num

/-- **The unconditional bracket in closed form** on `K₂` at the
`p ≡ 1/10` design, window `[1/2, 5/2]`, deviation budget `s = 1/2`,
tail level `t = 1/16`: the *unconditioned* window-exit event is bounded
by `4 exp(−1/4096) + 4 exp(−1/16)` — the window tail (dimension factor
`2 · 2`, variance norm `8`) plus the degree tail (both vertices'
statistic `2`). CONDITIONAL ON THE `matrix_hoeffding` AND
`hoeffding_inequality` AXIOMS (instantiated via the unconditional
bracket, not re-proved) — the family's only two-axiom member. -/
theorem epK2_bracket_unconditional_closedForm_QA :
    (bernPMF epTenth epTenth_nonneg epTenth_le_one).toMeasure
      {ω : Fin 2 × Fin 2 → Bool |
        (secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epTenth ω))
            (normalizedLaplacian_symmetric (epK2 + perturbWeight epK2 epTenth ω)
              (epK2_symmetric.add (perturbWeight_isSymm epK2 epTenth ω)))
            (by norm_num)
          ≤ (1 / 2 * cheegerConstant epK2 ^ 2 / 2 - 1 / 16) / (5 / 2)
        ∨ (2 * ((5 / 2) * cheegerConstant epK2) + 1 / 16) / (1 / 2)
          ≤ secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epTenth ω))
              (normalizedLaplacian_symmetric (epK2 + perturbWeight epK2 epTenth ω)
                (epK2_symmetric.add (perturbWeight_isSymm epK2 epTenth ω)))
              (by norm_num))}
      ≤ ENNReal.ofReal (4 * Real.exp (-(1 / 4096 : ℝ)))
        + ENNReal.ofReal (4 * Real.exp (-(1 / 16 : ℝ))) := by
  have h := edgePerturbation_normalized_connectivity_bracket_unconditional
    epK2 epTenth epK2_symmetric (fun i j => epK2_nonneg i j)
    (1 / 2) (5 / 2) (1 / 2) (1 / 16) (by norm_num) (by norm_num)
    (fun i => by rw [epK2_regular i]; norm_num)
    (fun i => by rw [epK2_regular i]; norm_num)
    epTenth_nonneg epTenth_le_one epTenth_pair (by norm_num)
    (by norm_num)
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  have hvar : ‖∑ e : Fin 2 × Fin 2,
      perturbEdgeLap epK2 e * perturbEdgeLap epK2 e‖ = 8 :=
    epK2_variance_norm
  rw [hcard, hvar] at h
  have hargd : (-((1 / 2 : ℝ) ^ 2) / (2 * 2)) = -(1 / 16 : ℝ) := by norm_num
  have hdegsum : ∑ v : Fin 2, ENNReal.ofReal (2 * Real.exp
      (-((1 / 2 : ℝ) ^ 2) / (2 * ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 v e) ^ 2)))
      = ENNReal.ofReal (4 * Real.exp (-(1 / 16 : ℝ))) := by
    have h0 : ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 (0 : Fin 2) e) ^ 2 = 2 :=
      epK2_degree_variance' 0
    have h1 : ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 (1 : Fin 2) e) ^ 2 = 2 :=
      epK2_degree_variance' 1
    rw [Fin.sum_univ_two, h0, h1, hargd]
    have hA : (0 : ℝ) ≤ 2 * Real.exp (-(1 / 16 : ℝ)) := by positivity
    exact Eq.trans (ENNReal.ofReal_add hA hA).symm
      (congrArg ENNReal.ofReal (by ring))
  rw [hdegsum] at h
  have hargw : (-((1 / 16 : ℝ) ^ 2) / (2 * 8)) = -(1 / 4096 : ℝ) := by
    norm_num
  have hwin : (2 : ℝ) * 2 * Real.exp (-((1 / 16 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-(1 / 4096 : ℝ)) := by rw [hargw]; ring
  rw [hwin] at h
  exact h

/-! ### The dissolution completion (floor and swept cut)

The same decomposition applied to the window family's other two
members (`edgePerturbation_normalized_cheeger_floor_unconditional`,
`edgePerturbation_fiedler_sweep_cut_tail_unconditional`) — the family
completed to unconditional statements throughout. -/

/-- The support graph of the all-false perturbed `K₂` (the empty graph)
is **disconnected** — the kernel-constancy contrapositive at the zero
adjacency: every vector lies in the zero Laplacian's kernel, and the
component indicator `![1, 0]` is not constant. -/
theorem epK2_allFalse_supportGraph_not_connected :
    ¬ (supportGraph (epK2 + perturbWeight epK2 epHalf (fun _ => false))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
        (fun _ => false)))).Connected := by
  intro hconn
  have hf : (laplacian (epK2 + perturbWeight epK2 epHalf (fun _ => false))).mulVec
      (fun i => if (i : Fin 2) = 0 then (1 : ℝ) else 0) = 0 := by
    rw [epK2_perturbed_allFalse_eq]
    have hd0 : degreeMatrix (0 : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
      ext a b
      simp [degreeMatrix, deg]
    rw [laplacian, sub_zero, hd0, Matrix.zero_mulVec]
  obtain ⟨c, hc⟩ := exists_const_of_laplacian_mulVec_eq_zero
    (epK2 + perturbWeight epK2 epHalf (fun _ => false))
    (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => false)))
    epK2_perturbed_allFalse_nonneg hconn hf
  have e0 := congrFun hc (0 : Fin 2)
  have e1 := congrFun hc (1 : Fin 2)
  simp only [] at e0 e1
  norm_num at e0 e1
  linarith

/-- **The strict-containment witness**: the all-false outcome at the
`p ≡ ½` design sits in the *unconditional* sweep bad event (its resampled
graph is disconnected) while being provably *not* admissible — so the
dissolution's measured event genuinely contains outcomes the conditional
theorem's event excludes. The degree-tail term is the honest price of
those outcomes. Hard crust: a negation and a non-membership, no axiom
contact. -/
theorem epK2_sweepUnconditional_strictly_larger_witness_QA :
    (¬ ((supportGraph (epK2 + perturbWeight epK2 epHalf (fun _ => false))
             (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
               (fun _ => false)))).Connected ∧
        ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
          ((∃ u : ℝ, ∀ i, i ∈ S ↔
              u ≤ fiedlerSweepVector (epK2 + perturbWeight epK2 epHalf
                  (fun _ => false))
                (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
                  (fun _ => false))) (by norm_num) i)
            ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
              fiedlerSweepVector (epK2 + perturbWeight epK2 epHalf
                  (fun _ => false))
                (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
                  (fun _ => false))) (by norm_num) i ≤ u)) ∧
          conductance (epK2 + perturbWeight epK2 epHalf (fun _ => false)) S ^ 2
            ≤ 2 * ((2 * ((5 / 2 : ℝ) * cheegerConstant epK2) + 1 / 16)
                / (1 / 2))))
    ∧ ¬ perturbAdmissible epK2 epHalf (1 / 2) (5 / 2) (fun _ => false) := by
  refine ⟨fun hgood => epK2_allFalse_supportGraph_not_connected hgood.1,
    epK2_half_allFalse_not_admissible⟩

/-- **The good-outcome conjunction at the dissolution's window**: the
all-true outcome's resampled graph (the weight-`2` edge) is connected
and carries a swept Fiedler cut at `conductance² ≤ 2·λ₂ = 4`, well
inside the window bound `2·((2·(5/2·φ) + 1/16)/(1/2)) = 81/4` — so the
*unconditional* bad event omits this outcome: it is not all of `Ω`. -/
theorem epK2_sweepUnconditional_allTrue_good_QA :
    (supportGraph (epK2 + perturbWeight epK2 epHalf (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
        (fun _ => true)))).Connected ∧
    ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
      ((∃ u : ℝ, ∀ i, i ∈ S ↔
          u ≤ fiedlerSweepVector (epK2 + perturbWeight epK2 epHalf
              (fun _ => true))
            (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
              (fun _ => true))) (by norm_num) i)
        ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
          fiedlerSweepVector (epK2 + perturbWeight epK2 epHalf
              (fun _ => true))
            (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf
              (fun _ => true))) (by norm_num) i ≤ u)) ∧
      conductance (epK2 + perturbWeight epK2 epHalf (fun _ => true)) S ^ 2
        ≤ 2 * ((2 * ((5 / 2 : ℝ) * cheegerConstant epK2) + 1 / 16)
            / (1 / 2)) := by
  have hd' : ∀ i, 0 < deg (epK2 + perturbWeight epK2 epHalf
      (fun _ => true)) i := by
    intro i
    rw [epK2_allTrue_deg i]
    norm_num
  obtain ⟨S, hSne, hScne, hlev, hcond⟩ :=
    fiedler_sweep_cut_normalized (epK2 + perturbWeight epK2 epHalf
        (fun _ => true))
      (epK2_symmetric.add (perturbWeight_isSymm epK2 epHalf (fun _ => true)))
      epK2_perturbed_allTrue_nonneg hd' (by norm_num)
      epK2_allTrue_supportGraph_connected
  rw [epK2_normLap_secondEval_allTrue] at hcond
  refine ⟨epK2_allTrue_supportGraph_connected, S, hSne, hScne, hlev, ?_⟩
  rw [epK2_cheegerConstant]
  linarith

/-- **The unconditional floor in closed form** on `K₂` at the `p ≡ 1/10`
design, window `[1/2, 5/2]`, deviation budget `s = 1/2`, tail level
`t = 1/16`: the *unconditioned* floor event is bounded by
`4 exp(−1/4096) + 4 exp(−1/16)`. CONDITIONAL ON THE `matrix_hoeffding`
AND `hoeffding_inequality` AXIOMS (instantiated via the unconditional
floor, not re-proved). -/
theorem epK2_floor_unconditional_closedForm_QA :
    (bernPMF epTenth epTenth_nonneg epTenth_le_one).toMeasure
      {ω : Fin 2 × Fin 2 → Bool |
        secondEval (normalizedLaplacian (epK2 + perturbWeight epK2 epTenth ω))
            (normalizedLaplacian_symmetric (epK2 + perturbWeight epK2 epTenth ω)
              (epK2_symmetric.add (perturbWeight_isSymm epK2 epTenth ω)))
            (by norm_num)
          ≤ (1 / 2 * cheegerConstant epK2 ^ 2 / 2 - 1 / 16) / (5 / 2)}
      ≤ ENNReal.ofReal (4 * Real.exp (-(1 / 4096 : ℝ)))
        + ENNReal.ofReal (4 * Real.exp (-(1 / 16 : ℝ))) := by
  have h := edgePerturbation_normalized_cheeger_floor_unconditional
    epK2 epTenth epK2_symmetric (fun i j => epK2_nonneg i j)
    (1 / 2) (5 / 2) (1 / 2) (1 / 16) (by norm_num) (by norm_num)
    (fun i => by rw [epK2_regular i]; norm_num)
    (fun i => by rw [epK2_regular i]; norm_num)
    epTenth_nonneg epTenth_le_one epTenth_pair (by norm_num)
    (by norm_num)
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  have hvar : ‖∑ e : Fin 2 × Fin 2,
      perturbEdgeLap epK2 e * perturbEdgeLap epK2 e‖ = 8 :=
    epK2_variance_norm
  rw [hcard, hvar] at h
  have hargd : (-((1 / 2 : ℝ) ^ 2) / (2 * 2)) = -(1 / 16 : ℝ) := by norm_num
  have hdegsum : ∑ v : Fin 2, ENNReal.ofReal (2 * Real.exp
      (-((1 / 2 : ℝ) ^ 2) / (2 * ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 v e) ^ 2)))
      = ENNReal.ofReal (4 * Real.exp (-(1 / 16 : ℝ))) := by
    have h0 : ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 (0 : Fin 2) e) ^ 2 = 2 :=
      epK2_degree_variance' 0
    have h1 : ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 (1 : Fin 2) e) ^ 2 = 2 :=
      epK2_degree_variance' 1
    rw [Fin.sum_univ_two, h0, h1, hargd]
    have hA : (0 : ℝ) ≤ 2 * Real.exp (-(1 / 16 : ℝ)) := by positivity
    exact Eq.trans (ENNReal.ofReal_add hA hA).symm
      (congrArg ENNReal.ofReal (by ring))
  rw [hdegsum] at h
  have hargw : (-((1 / 16 : ℝ) ^ 2) / (2 * 8)) = -(1 / 4096 : ℝ) := by
    norm_num
  have hwin : (2 : ℝ) * 2 * Real.exp (-((1 / 16 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-(1 / 4096 : ℝ)) := by rw [hargw]; ring
  rw [hwin] at h
  exact h

/-- **The unconditional swept-cut tail in closed form** on `K₂` at the
`p ≡ 1/10` design, window `[1/2, 5/2]`, `s = 1/2`, `t = 1/16`: the
failure-of-good-outcome event (with no conditioning conjunct) is bounded
by `4 exp(−1/4096) + 4 exp(−1/16)`, the floor hypothesis genuinely
holding (`0 < 1/2·φ²/2 − 1/16 = 3/16`). CONDITIONAL ON THE
`matrix_hoeffding` AND `hoeffding_inequality` AXIOMS. -/
theorem epK2_sweepUnconditional_closedForm_QA :
    (bernPMF epTenth epTenth_nonneg epTenth_le_one).toMeasure
      {ω : Fin 2 × Fin 2 → Bool |
        ¬ ((supportGraph (epK2 + perturbWeight epK2 epTenth ω)
              (epK2_symmetric.add (perturbWeight_isSymm epK2 epTenth ω))).Connected ∧
           ∃ S : Finset (Fin 2), S.Nonempty ∧ Sᶜ.Nonempty ∧
             ((∃ u : ℝ, ∀ i, i ∈ S ↔
                 u ≤ fiedlerSweepVector (epK2 + perturbWeight epK2 epTenth ω)
                   (epK2_symmetric.add (perturbWeight_isSymm epK2 epTenth ω))
                   (by norm_num) i)
               ∨ (∃ u : ℝ, ∀ i, i ∈ S ↔
                 fiedlerSweepVector (epK2 + perturbWeight epK2 epTenth ω)
                   (epK2_symmetric.add (perturbWeight_isSymm epK2 epTenth ω))
                   (by norm_num) i ≤ u)) ∧
             conductance (epK2 + perturbWeight epK2 epTenth ω) S ^ 2
               ≤ 2 * ((2 * ((5 / 2 : ℝ) * cheegerConstant epK2) + 1 / 16)
                   / (1 / 2)))}
      ≤ ENNReal.ofReal (4 * Real.exp (-(1 / 4096 : ℝ)))
        + ENNReal.ofReal (4 * Real.exp (-(1 / 16 : ℝ))) := by
  have hfloor : (0 : ℝ) < 1 / 2 * (cheegerConstant epK2) ^ 2 / 2 - 1 / 16 := by
    rw [epK2_cheegerConstant]
    norm_num
  have h := edgePerturbation_fiedler_sweep_cut_tail_unconditional
    epK2 epTenth epK2_symmetric (fun i j => epK2_nonneg i j)
    (1 / 2) (5 / 2) (1 / 2) (1 / 16) (by norm_num) (by norm_num)
    (fun i => by rw [epK2_regular i]; norm_num)
    (fun i => by rw [epK2_regular i]; norm_num)
    epTenth_nonneg epTenth_le_one epTenth_pair (by norm_num)
    (by norm_num) hfloor
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by norm_num
  have hvar : ‖∑ e : Fin 2 × Fin 2,
      perturbEdgeLap epK2 e * perturbEdgeLap epK2 e‖ = 8 :=
    epK2_variance_norm
  rw [hcard, hvar] at h
  have hargd : (-((1 / 2 : ℝ) ^ 2) / (2 * 2)) = -(1 / 16 : ℝ) := by norm_num
  have hdegsum : ∑ v : Fin 2, ENNReal.ofReal (2 * Real.exp
      (-((1 / 2 : ℝ) ^ 2) / (2 * ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 v e) ^ 2)))
      = ENNReal.ofReal (4 * Real.exp (-(1 / 16 : ℝ))) := by
    have h0 : ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 (0 : Fin 2) e) ^ 2 = 2 :=
      epK2_degree_variance' 0
    have h1 : ∑ e : Fin 2 × Fin 2,
        (degPerturbWeight epK2 (1 : Fin 2) e) ^ 2 = 2 :=
      epK2_degree_variance' 1
    rw [Fin.sum_univ_two, h0, h1, hargd]
    have hA : (0 : ℝ) ≤ 2 * Real.exp (-(1 / 16 : ℝ)) := by positivity
    exact Eq.trans (ENNReal.ofReal_add hA hA).symm
      (congrArg ENNReal.ofReal (by ring))
  rw [hdegsum] at h
  have hargw : (-((1 / 16 : ℝ) ^ 2) / (2 * 8)) = -(1 / 4096 : ℝ) := by
    norm_num
  have hwin : (2 : ℝ) * 2 * Real.exp (-((1 / 16 : ℝ) ^ 2) / (2 * 8))
      = 4 * Real.exp (-(1 / 4096 : ℝ)) := by rw [hargw]; ring
  rw [hwin] at h
  exact h

end AdmissibilityDissolution

end Scaffold.QA.Derived.EdgePerturbation
