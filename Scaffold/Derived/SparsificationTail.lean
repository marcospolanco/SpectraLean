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
import Scaffold.Mathlib.GraphTheory.Sparsification
import Scaffold.Mathlib.Probability.Concentration.Matrix.Bernstein

/-!
# The sparsification tail bound (Step 1, Slice 3: the assembly)

`matrix_bernstein`'s first real theorem consumer: the Spielman–Srivastava
deviation tail bound assembled on the delivered sampling design
(`proposals/spectral-sparsification-via-leverage-scores.md`, the Active
priority table's top High row). Every deterministic input is proved hard
crust (Slices 1–2 in `GraphTheory/Sparsification.lean` and
`Probability/BernoulliProduct.lean`, plus that module's Slice-3 sections:
the exact deviation identity, the transferred clause lemmas, the
norm→quadratic-form transfer); the two tail theorems here are
**conditional on the `matrix_bernstein` axiom** (Tropp 2012, Theorem
1.1) and must never be described as foundationally proved — `#print
axioms` reports the dependency honestly.

- `sparsification_norm_tail`: on the product-Bernoulli sampling space,
  the sampled operator's spectral deviation from the image projector
  obeys `μ {‖S(ω) − Π_{im L}‖ ≥ t} ≤ 2 d exp(−t² / (2/q + 2t/(3q)))`
  at the *proved* classical constants `R = 1/q`, `‖Σ‖ ≤ 1/q`.
  No connectivity hypothesis (centering is connectivity-free by design).
- `sparsification_quadForm_tail`: the same bound for the failure of the
  uniform additive quadratic-form approximation
  `|xᵀ S(ω) x − xᵀ Π x| ≤ t (x ⬝ᵥ x)` for every vector — the
  eigen-coordinate pullback of the norm event.
- `sparsification_multiplicative_tail`: the multiplicative refinement on
  `im Π`-coordinate vectors — the field-standard "S is a (1±ε)-sparsifier"
  shape. The failure of the two-sided bound
  `(1−ε)(x ⬝ᵥ x) ≤ xᵀ S(ω) x ≤ (1+ε)(x ⬝ᵥ x)` over vectors the image
  projector fixes obeys the same exponential tail (the additive tail at
  `t = ε`, the conversion legitimate exactly on the cone by
  `quadForm_imageProjector_eq_of_mulVec_eq`).
- `sparsification_multiplicative_budget`: the sample-complexity
  corollary — at `0 < ε ≤ 1`, budget `q ≥ (8/3)·log(2d/δ)/ε²` drives the
  multiplicative failure measure below `δ` (the classical
  `q ~ log n/ε²` sentence, at the Tropp exponent's exact constant).
- `sparsification_graph_tail` / `sparsification_graph_budget`: the
  *graph-vector* form — the textbook sentence `xᵀL̃(ω)x` vs `xᵀLx` for
  every graph vector with **no `im Π` restriction** (the transport is on
  the cone by construction), same tail and same budget through the
  shelf's form correspondence `quadForm_ssLaplacian_eq`.
- `sparsificationBudget` (+ `_pos`, `_le`, `_min`): the **closed-form
  sampling budget** (Track A of
  `proposals/spectral-graph-sparsification-gnn-training.md`) — the
  minimal natural `q` certified for both clauses of the budget
  hypothesis, as pure arithmetic: zero axioms, `#print axioms` at the
  standard three, so a caller supplies only `(n, ε, δ)`.
- `sparsification_graph_budget_closedForm`: the plug-in form — the
  graph-vector guarantee at the computed budget, the budget hypothesis
  discharged by `sparsificationBudget_le` (CONDITIONAL ON THE
  `matrix_bernstein` AXIOM exactly like the budget corollary it
  applies; the *budget arithmetic* is axiom-free). The
  practitioner-facing statement, trust caveat first, is
  `docs/gnn-sparsification-budget.md`.

The `Fin n` summand transport (the Step-0 Finding B) is
`Fintype.equivFin` + `Equiv.sum_comp`; the sum, event, and variance
reconciliation all run through those two.

QA: `Scaffold/QA/Derived/SparsificationTail_QA.lean`.
-/

open MeasureTheory ProbabilityTheory
open SpectralGraphTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open Scaffold.Mathlib.Probability.Concentration.Matrix
open scoped BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.Derived.SparsificationTail

variable {V : Type} [Fintype V] [DecidableEq V]
variable (A : WAdj (V := V)) (hA : A.IsSymm)

/-- **The Spielman–Srivastava deviation tail bound** — `matrix_bernstein`
assembled at the delivered summand family, the program's target
consumer. On the product-Bernoulli sampling space at budget `q`, the
sampled operator's spectral deviation from the image projector obeys the
classical exponential tail at the *proved* constants `R = 1/q`,
`‖Σ‖ ≤ 1/q`:

`μ {‖S(ω) − Π_{im L}‖ ≥ t} ≤ 2 d exp(−t² / (2/q + 2t/(3q)))`, `d = card V`.

CONDITIONAL ON THE `matrix_bernstein` AXIOM (Tropp, "User-friendly tail
bounds for sums of random matrices", FoCM 12(4):389–434, 2012,
Theorem 1.1): the hypothesis clauses are all proved here, but the tail
inequality itself is axiom-backed. The statement needs no connectivity —
centering is connectivity-free by the Slice-2 design. -/
theorem sparsification_norm_tail [Nonempty V] (hnn : ∀ i j, 0 ≤ A i j)
    (q : ℝ) (hq : 0 < q) (t : ℝ) (ht : 0 ≤ t) :
    ssMeasure A hA q hq.le
        {ω | ‖ssSampled A hA q ω - imageProjector A hA‖ ≥ t}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 / q + 2 * t / (3 * q)))) := by
  haveI hprob : IsProbabilityMeasure (ssMeasure A hA q hq.le) :=
    PMF.toMeasure.isProbabilityMeasure _
  have hmeas : ∀ i : Fin (Fintype.card (V × V)),
      StronglyMeasurable fun ω : (V × V) → Bool =>
        ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω :=
    fun i => stronglyMeasurable_ssSummand A hA q _
  have hindep : iIndepFun (fun _ : Fin (Fintype.card (V × V)) =>
      (inferInstance : MeasurableSpace (Matrix V V ℝ)))
      (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
        ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω)
      (ssMeasure A hA q hq.le) :=
    iIndepFun_ssSummand A hA q hq.le
  have hherm : ∀ (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool),
      (ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω).IsHermitian :=
    fun i ω => isHermitian_of_isSymm (ssSummand_isSymm A hA q _ ω)
  have hmean : ∀ i : Fin (Fintype.card (V × V)),
      ∫ ω : (V × V) → Bool,
        ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω
        ∂ssMeasure A hA q hq.le = 0 :=
    fun i => integral_ssSummand_eq_zero A hA q hq _
  have hbound : ∀ (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool),
      ‖ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω‖ ≤ 1 / q :=
    fun i ω => ssSummand_l2OpNorm_le A hA q hq _ ω
  have hmain := matrix_bernstein
    (μ := ssMeasure A hA q hq.le)
    (X := fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
      ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω)
    (R := 1 / q) hmeas hindep hherm hmean hbound t ht
  have hsum : ∀ ω : (V × V) → Bool,
      ∑ i : Fin (Fintype.card (V × V)),
        ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω
      = ssSampled A hA q ω - imageProjector A hA := by
    intro ω
    rw [ssSampled_sub_imageProjector A hA hnn q ω]
    exact Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => ssSummand A hA q e ω)
  have hsum' : ∀ ω : (V × V) → Bool,
      ∑ i : Fin (Fintype.card (V × V)),
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω) i ω
      = ssSampled A hA q ω - imageProjector A hA := fun ω => hsum ω
  have hseteq : {ω : (V × V) → Bool |
      ‖∑ i : Fin (Fintype.card (V × V)),
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω) i ω‖ ≥ t}
      = {ω : (V × V) → Bool |
        ‖ssSampled A hA q ω - imageProjector A hA‖ ≥ t} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    exact Iff.of_eq (congrArg (fun S : Matrix V V ℝ => ‖S‖ ≥ t) (hsum' ω))
  rw [hseteq] at hmain
  have hvar0 : ∑ i : Fin (Fintype.card (V × V)),
      ∫ ω : (V × V) → Bool,
        ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω
          * ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω
        ∂ssMeasure A hA q hq.le
      = ssVariance A hA q := by
    rw [Equiv.sum_comp (Fintype.equivFin (V × V)).symm
      (fun e : V × V => ∫ ω : (V × V) → Bool,
        ssSummand A hA q e ω * ssSummand A hA q e ω ∂ssMeasure A hA q hq.le),
      sum_integral_ssSummand_mul_self A hA q hq]
  have hvar : ∑ i : Fin (Fintype.card (V × V)),
      ∫ ω : (V × V) → Bool,
        (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω) i ω
        * (fun (i : Fin (Fintype.card (V × V))) (ω : (V × V) → Bool) =>
          ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω) i ω
        ∂ssMeasure A hA q hq.le
      = ssVariance A hA q := hvar0
  rw [hvar] at hmain
  refine le_trans hmain ?_
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  refine Real.exp_le_exp.mpr ?_
  rcases eq_or_lt_of_le ht with rfl | htpos
  · simp
  · have h1q : (0 : ℝ) < 1 / q := by positivity
    have hvarle := l2OpNorm_ssVariance_le A hA q hq hnn
    have hEq : (2 : ℝ) * (1 / q) * t / 3 = 2 * t / (3 * q) := by
      field_simp
      ring
    have h2 : (2 : ℝ) * ‖ssVariance A hA q‖ ≤ 2 / q := by
      refine (le_div_iff₀ hq).mpr ?_
      have hk := (le_div_iff₀ hq).mp hvarle
      linarith
    have hdle : (2 : ℝ) * ‖ssVariance A hA q‖ + 2 * (1 / q) * t / 3
        ≤ 2 / q + 2 * t / (3 * q) := by
      rw [hEq]
      linarith
    have hd₂ : (0 : ℝ) < 2 / q + 2 * t / (3 * q) := by
      have h2q : (0 : ℝ) < 2 / q := by positivity
      have h3 : (0 : ℝ) < 2 * t / (3 * q) := by positivity
      linarith
    have hd₁ : (0 : ℝ) < 2 * ‖ssVariance A hA q‖ + 2 * (1 / q) * t / 3 := by
      have h3 : (0 : ℝ) < 2 * (1 / q) * t / 3 := by positivity
      have h4 : (0 : ℝ) ≤ ‖ssVariance A hA q‖ := norm_nonneg _
      linarith
    have key : t ^ 2 / (2 / q + 2 * t / (3 * q))
        ≤ t ^ 2 / (2 * ‖ssVariance A hA q‖ + 2 * (1 / q) * t / 3) := by
      rw [div_le_div_iff₀ hd₂ hd₁]
      exact mul_le_mul_of_nonneg_left hdle (sq_nonneg t)
    rw [neg_div, neg_div]
    exact neg_le_neg key

/-- **The quadratic-form tail** — the eigen-coordinate pullback of the
norm tail: with the same exponential bound, outside a set of the bound's
measure the sampled operator's quadratic form uniformly approximates the
image projector's in the additive form
`|xᵀ S(ω) x − xᵀ Π x| ≤ t · (x ⬝ᵥ x)` for *every* vector. CONDITIONAL
ON THE `matrix_bernstein` AXIOM (the norm tail above, transferred). -/
theorem sparsification_quadForm_tail [Nonempty V] (hnn : ∀ i j, 0 ≤ A i j)
    (q : ℝ) (hq : 0 < q) (t : ℝ) (ht : 0 ≤ t) :
    ssMeasure A hA q hq.le
        {ω | ∃ x : V → ℝ, t * (x ⬝ᵥ x)
          < |quadForm (ssSampled A hA q ω) x
            - quadForm (imageProjector A hA) x|}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(t ^ 2) / (2 / q + 2 * t / (3 * q)))) := by
  refine le_trans (measure_mono ?_)
    (sparsification_norm_tail A hA hnn q hq t ht)
  rintro ω ⟨x, hx⟩
  have hqf : quadForm (ssSampled A hA q ω) x
      - quadForm (imageProjector A hA) x
      = quadForm (ssSampled A hA q ω - imageProjector A hA) x :=
    (quadForm_sub_matrix _ _ _).symm
  have hxdot : (0 : ℝ) < x ⬝ᵥ x := by
    by_contra hcon
    push_neg at hcon
    have hz : x = 0 := by
      by_contra hx0
      exact absurd (dotProduct_self_pos_of_ne_zero hx0) (not_lt.2 hcon)
    rw [hz] at hx
    simp [quadForm] at hx
  have habs := abs_quadForm_le_of_l2OpNorm_le
    (t := ‖ssSampled A hA q ω - imageProjector A hA‖)
    (le_refl _) x
  rw [← hqf] at habs
  simp only [Set.mem_setOf_eq]
  have h2 : t * (x ⬝ᵥ x)
      < ‖ssSampled A hA q ω - imageProjector A hA‖ * (x ⬝ᵥ x) :=
    lt_of_lt_of_le hx habs
  have h3 : t < ‖ssSampled A hA q ω - imageProjector A hA‖ := by
    nlinarith [h2, hxdot]
  exact le_of_lt h3

/-- **The multiplicative sparsifier tail** — the field-standard
statement shape: with the same exponential bound, outside a set of the
bound's measure the sampled operator quadratic-form-approximates the
image projector *multiplicatively* on every `im Π`-coordinate vector,

`(1−ε)(x ⬝ᵥ x) ≤ xᵀ S(ω) x ≤ (1+ε)(x ⬝ᵥ x)`

(the `im Π` restriction is where the conversion is legitimate — by
`quadForm_imageProjector_eq_of_mulVec_eq` the projector's form is the
squared norm exactly there; off the cone the zero-eigenvalue mass makes
the multiplicative reading false, fenced at `K₂` in QA). CONDITIONAL ON
THE `matrix_bernstein` AXIOM (the additive tail above, restricted). -/
theorem sparsification_multiplicative_tail [Nonempty V]
    (hnn : ∀ i j, 0 ≤ A i j) (q : ℝ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ssMeasure A hA q hq.le
        {ω | ∃ x : V → ℝ, imageProjector A hA *ᵥ x = x ∧
          ((1 - ε) * (x ⬝ᵥ x) > quadForm (ssSampled A hA q ω) x ∨
            quadForm (ssSampled A hA q ω) x > (1 + ε) * (x ⬝ᵥ x))}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q)))) := by
  refine le_trans (measure_mono ?_)
    (sparsification_quadForm_tail A hA hnn q hq ε hε.le)
  rintro ω ⟨x, hxmem, hdisj⟩
  simp only [Set.mem_setOf_eq]
  refine ⟨x, ?_⟩
  have hident := quadForm_imageProjector_eq_of_mulVec_eq A hA x hxmem
  have h3 : (0 : ℝ) ≤ x ⬝ᵥ x := by
    have : x ⬝ᵥ x = ∑ i, x i * x i := by
      simp [Matrix.dotProduct]
    rw [this]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h4 : (0 : ℝ) ≤ ε * (x ⬝ᵥ x) := mul_nonneg hε.le h3
  have hgoal : |quadForm (ssSampled A hA q ω) x
      - quadForm (imageProjector A hA) x|
      = |quadForm (ssSampled A hA q ω) x - x ⬝ᵥ x| := by rw [hident]
  rcases hdisj with hlow | hhigh
  · have h2 : x ⬝ᵥ x - quadForm (ssSampled A hA q ω) x > ε * (x ⬝ᵥ x) := by
      have : (1 - ε) * (x ⬝ᵥ x) = x ⬝ᵥ x - ε * (x ⬝ᵥ x) := by ring
      linarith
    rw [hgoal, abs_of_nonpos (by linarith), neg_sub]
    exact h2
  · have h2 : quadForm (ssSampled A hA q ω) x - x ⬝ᵥ x > ε * (x ⬝ᵥ x) := by
      have : (1 + ε) * (x ⬝ᵥ x) = x ⬝ᵥ x + ε * (x ⬝ᵥ x) := by ring
      linarith
    rw [hgoal, abs_of_nonneg (by linarith)]
    exact h2

/-- **The budget corollary** — the sample-complexity sentence: sampling
at budget `q ≥ (8/3)·log(2d/δ)/ε²` (with `d = card V` and
`0 < ε ≤ 1`) drives the probability of the multiplicative sparsifier
failure below `δ`. The `8/3` is exact: the Tropp exponent
`t²/(2/q + 2t/(3q))` at `t = ε` is at least `qε²/(2 + 2ε/3)`, and
`2 + 2ε/3 ≤ 8/3` on the stated regime. CONDITIONAL ON THE
`matrix_bernstein` AXIOM (the multiplicative tail above, evaluated). -/
theorem sparsification_multiplicative_budget [Nonempty V]
    (hnn : ∀ i j, 0 ≤ A i j) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (q : ℝ) (hq : 0 < q)
    (hqbudget : (8 / 3) * Real.log (2 * (Fintype.card V : ℝ) / δ)
      / ε ^ 2 ≤ q) :
    ssMeasure A hA q hq.le
        {ω | ∃ x : V → ℝ, imageProjector A hA *ᵥ x = x ∧
          ((1 - ε) * (x ⬝ᵥ x) > quadForm (ssSampled A hA q ω) x ∨
            quadForm (ssSampled A hA q ω) x > (1 + ε) * (x ⬝ᵥ x))}
      ≤ ENNReal.ofReal δ := by
  have htail := sparsification_multiplicative_tail A hA hnn q hq ε hε
  refine le_trans htail ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hdpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hlog : Real.log (2 * (Fintype.card V : ℝ) / δ)
      ≤ 3 * q * ε ^ 2 / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    have hε2 : 0 < ε ^ 2 := by positivity
    have hb := (div_le_iff₀ hε2).mp hqbudget
    nlinarith [hb]
  have hE : 3 * q * ε ^ 2 / 8
      ≤ ε ^ 2 / (2 / q + 2 * ε / (3 * q)) := by
    have h1 : ε ^ 2 / (2 / q + 2 * ε / (3 * q))
        = ε ^ 2 * q / (2 + 2 * ε / 3) := by
      field_simp
      ring
    have h23 : (0 : ℝ) < 2 + 2 * ε / 3 := by nlinarith [hε]
    have h3 : 2 + 2 * ε / 3 = (2 * 3 + 2 * ε) / 3 := by
      field_simp
    rw [h1, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) h23, h3,
      ← mul_div_assoc, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hnn1 : (0 : ℝ) ≤ 1 - ε := by linarith
    have hc : (0 : ℝ) ≤ q * (ε * ε) * (1 - ε) :=
      mul_nonneg (mul_nonneg hq.le (mul_nonneg hε.le hε.le)) hnn1
    nlinarith [hc]
  have hchain : Real.log (2 * (Fintype.card V : ℝ) / δ)
      ≤ ε ^ 2 / (2 / q + 2 * ε / (3 * q)) := le_trans hlog hE
  have hexp : Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q)))
      ≤ δ / (2 * (Fintype.card V : ℝ)) := by
    have hpos : 0 < 2 * (Fintype.card V : ℝ) / δ :=
      div_pos (mul_pos two_pos hdpos) hδ
    have h1 : Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q)))
        ≤ Real.exp (-Real.log (2 * (Fintype.card V : ℝ) / δ)) := by
      rw [neg_div]
      exact Real.exp_le_exp.mpr (neg_le_neg hchain)
    have h2 : Real.exp (-Real.log (2 * (Fintype.card V : ℝ) / δ))
        = δ / (2 * (Fintype.card V : ℝ)) := by
      rw [Real.exp_neg, Real.exp_log hpos, inv_eq_one_div]
      field_simp
    rw [h2] at h1
    exact h1
  calc (2 : ℝ) * (Fintype.card V : ℝ)
        * Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q)))
      ≤ 2 * (Fintype.card V : ℝ) * (δ / (2 * (Fintype.card V : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = δ := by
      field_simp

/-- **The graph-vector multiplicative sparsifier tail** — the
Spielman–Srivastava statement in its textbook form: with the same
exponential bound, outside a set of the bound's measure the sampled
Laplacian quadratic-form-approximates the base Laplacian *multiplicatively
for every graph vector*,

`(1−ε) xᵀLx ≤ xᵀL̃(ω) x ≤ (1+ε) xᵀLx` for all `x`,

with **no `im Π` cone restriction**: the transport `c(x)` is on the cone
by construction, the transport isometry identifies `xᵀLx` with `‖c(x)‖²`,
and the form correspondence identifies `xᵀL̃x` with `cᵀS c` — so the
additive tail at `t = ε` transfers verbatim (each failure disjunct is a
failure of `|cᵀSc − cᵀΠc| ≤ ε‖c‖²`). CONDITIONAL ON THE
`matrix_bernstein` AXIOM (Tropp, FoCM 2012, Theorem 1.1, via the
delivered additive tail). -/
theorem sparsification_graph_tail [Nonempty V] (hnn : ∀ i j, 0 ≤ A i j)
    (q : ℝ) (hq : 0 < q) (ε : ℝ) (hε : 0 < ε) :
    ssMeasure A hA q hq.le
        {ω | ∃ x : V → ℝ, (1 - ε) * quadForm (laplacian A) x
            > quadForm (ssLaplacian A hA q ω) x ∨
          quadForm (ssLaplacian A hA q ω) x
            > (1 + ε) * quadForm (laplacian A) x}
      ≤ ENNReal.ofReal (2 * (Fintype.card V : ℝ) *
        Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q)))) := by
  refine le_trans (measure_mono ?_)
    (sparsification_quadForm_tail A hA hnn q hq ε hε.le)
  rintro ω ⟨x, hdisj⟩
  simp only [Set.mem_setOf_eq]
  refine ⟨ssTransport A hA x, ?_⟩
  have hIso := quadForm_laplacian_eq_ssTransport A hA hnn x
  have hP := quadForm_imageProjector_eq_of_mulVec_eq A hA (ssTransport A hA x)
    (imageProjector_mulVec_ssTransport A hA x)
  have hCorr := quadForm_ssLaplacian_eq A hA hnn q ω x
  rw [hIso] at hdisj
  rw [hCorr] at hdisj
  have h3 : (0 : ℝ) ≤ ssTransport A hA x ⬝ᵥ ssTransport A hA x := dotProduct_self_nonneg _
  have h4 : (0 : ℝ) ≤ ε * (ssTransport A hA x ⬝ᵥ ssTransport A hA x) := mul_nonneg hε.le h3
  have hgoal : |quadForm (ssSampled A hA q ω) (ssTransport A hA x)
      - quadForm (imageProjector A hA) (ssTransport A hA x)|
      = |quadForm (ssSampled A hA q ω) (ssTransport A hA x)
        - ssTransport A hA x ⬝ᵥ ssTransport A hA x| := by rw [hP]
  rcases hdisj with hlow | hhigh
  · have h2 : ssTransport A hA x ⬝ᵥ ssTransport A hA x
        - quadForm (ssSampled A hA q ω) (ssTransport A hA x)
        > ε * (ssTransport A hA x ⬝ᵥ ssTransport A hA x) := by
      have hring : (1 - ε) * (ssTransport A hA x ⬝ᵥ ssTransport A hA x)
          = ssTransport A hA x ⬝ᵥ ssTransport A hA x - ε * (ssTransport A hA x ⬝ᵥ ssTransport A hA x) := by ring
      linarith
    rw [hgoal, abs_of_nonpos (by linarith), neg_sub]
    exact h2
  · have h2 : quadForm (ssSampled A hA q ω) (ssTransport A hA x)
        - ssTransport A hA x ⬝ᵥ ssTransport A hA x > ε * (ssTransport A hA x ⬝ᵥ ssTransport A hA x) := by
      have hring : (1 + ε) * (ssTransport A hA x ⬝ᵥ ssTransport A hA x)
          = ssTransport A hA x ⬝ᵥ ssTransport A hA x + ε * (ssTransport A hA x ⬝ᵥ ssTransport A hA x) := by ring
      linarith
    rw [hgoal, abs_of_nonneg (by linarith)]
    exact h2

/-- The numeric core of both budget corollaries: the Tropp exponent at
`t = ε` is at least `3qε²/8`, so the budget `q ≥ (8/3)·log(2d/δ)/ε²`
drives `2d·exp(−ε²/(2/q + 2ε/(3q)))` below `δ` (the `8/3` exact; holds
at every `δ > 0`, `δ > 2d` included). -/
private theorem sparsification_budget_core {d ε δ q : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hq : 0 < q)
    (hb : (8 / 3) * Real.log (2 * d / δ) / ε ^ 2 ≤ q) :
    2 * d * Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q))) ≤ δ := by
  have hlog : Real.log (2 * d / δ) ≤ 3 * q * ε ^ 2 / 8 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
    have hε2 : 0 < ε ^ 2 := by positivity
    have hbx := (div_le_iff₀ hε2).mp hb
    nlinarith [hbx]
  have hE : 3 * q * ε ^ 2 / 8 ≤ ε ^ 2 / (2 / q + 2 * ε / (3 * q)) := by
    have h1 : ε ^ 2 / (2 / q + 2 * ε / (3 * q)) = ε ^ 2 * q / (2 + 2 * ε / 3) := by
      field_simp
      ring
    have h23 : (0 : ℝ) < 2 + 2 * ε / 3 := by nlinarith [hε]
    have h3 : 2 + 2 * ε / 3 = (2 * 3 + 2 * ε) / 3 := by
      field_simp
    rw [h1, div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8) h23, h3,
      ← mul_div_assoc, div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
    have hnn1 : (0 : ℝ) ≤ 1 - ε := by linarith
    have hc : (0 : ℝ) ≤ q * (ε * ε) * (1 - ε) :=
      mul_nonneg (mul_nonneg hq.le (mul_nonneg hε.le hε.le)) hnn1
    nlinarith [hc]
  have hchain : Real.log (2 * d / δ)
      ≤ ε ^ 2 / (2 / q + 2 * ε / (3 * q)) := le_trans hlog hE
  have hexp : Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q)))
      ≤ δ / (2 * d) := by
    have hpos : 0 < 2 * d / δ := div_pos (mul_pos two_pos hd) hδ
    have h1 : Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q)))
        ≤ Real.exp (-Real.log (2 * d / δ)) := by
      rw [neg_div]
      exact Real.exp_le_exp.mpr (neg_le_neg hchain)
    have h2 : Real.exp (-Real.log (2 * d / δ)) = δ / (2 * d) := by
      rw [Real.exp_neg, Real.exp_log hpos, inv_eq_one_div]
      field_simp
    rw [h2] at h1
    exact h1
  calc (2 : ℝ) * d * Real.exp (-(ε ^ 2) / (2 / q + 2 * ε / (3 * q)))
      ≤ 2 * d * (δ / (2 * d)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = δ := by
        field_simp

/-- **The graph-vector budget corollary** — the sample-complexity
sentence for the textbook form: at `0 < ε ≤ 1`, `0 < δ`, budget
`q ≥ (8/3)·log(2d/δ)/ε²` (with `d = card V`) drives the probability of
the graph-vector multiplicative failure below `δ`. CONDITIONAL ON THE
`matrix_bernstein` AXIOM (the graph tail above, evaluated through the
shared numeric core). -/
theorem sparsification_graph_budget [Nonempty V] (hnn : ∀ i j, 0 ≤ A i j)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (q : ℝ) (hq : 0 < q)
    (hqbudget : (8 / 3) * Real.log (2 * (Fintype.card V : ℝ) / δ)
      / ε ^ 2 ≤ q) :
    ssMeasure A hA q hq.le
        {ω | ∃ x : V → ℝ, (1 - ε) * quadForm (laplacian A) x
            > quadForm (ssLaplacian A hA q ω) x ∨
          quadForm (ssLaplacian A hA q ω) x
            > (1 + ε) * quadForm (laplacian A) x}
      ≤ ENNReal.ofReal δ := by
  refine le_trans (sparsification_graph_tail A hA hnn q hq ε hε) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hdpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    exact_mod_cast Fintype.card_pos
  exact sparsification_budget_core hdpos hε hε1 hδ hq hqbudget

/-! ### The closed-form sampling budget (Track A)

The budget corollaries above take `q` as a hypothesis the caller must
discharge by hand. These declarations instead *output* the budget:
`sparsificationBudget n ε δ` is the minimal natural `q` satisfying both
clauses (`0 < q` and the inequality), the three certification lemmas
prove exactly that, and `sparsification_graph_budget_closedForm` is the
one-hypothesis-per-side plug-in form of the graph-vector guarantee.
Everything in this section except the plug-in form is pure real
arithmetic — no graph, no measure, no axiom. -/

/-- **The closed-form per-edge sampling budget** — the minimal natural
`q` satisfying both `0 < q` and the certified budget inequality
`(8/3)·log(2n/δ)/ε² ≤ q`, at graph order `n` (instantiate at
`Fintype.card V`), target relative accuracy `ε` (read at `0 < ε ≤ 1`),
and failure probability `δ` (read at `0 < δ`). Pure arithmetic: no
graph, no measure, no axiom. The `max 1` floor is what makes positivity
unconditional — at `2n/δ ≤ 1` the log is nonpositive and the ceiling
alone could be `0`, killing the `0 < q` clause of every budget theorem
(fenced at `n = 1`, `δ = 10` in QA). -/
noncomputable def sparsificationBudget (n : ℕ) (ε δ : ℝ) : ℕ :=
  max 1 (Nat.ceil ((8 / 3) * Real.log (2 * (n : ℝ) / δ) / ε ^ 2))

/-- The budget is positive — the `max 1` floor, unconditionally. -/
theorem sparsificationBudget_pos (n : ℕ) (ε δ : ℝ) :
    0 < sparsificationBudget n ε δ :=
  lt_of_lt_of_le (zero_lt_one) (le_max_left _ _)

/-- The budget meets the certified budget inequality of both budget
corollaries (`sparsification_multiplicative_budget`,
`sparsification_graph_budget`), unconditionally. -/
theorem sparsificationBudget_le (n : ℕ) (ε δ : ℝ) :
    (8 / 3) * Real.log (2 * (n : ℝ) / δ) / ε ^ 2
      ≤ (sparsificationBudget n ε δ : ℝ) :=
  (Nat.le_ceil _).trans (Nat.cast_le.2 (le_max_right _ _))

/-- The budget is *minimal* among naturals: any positive natural `q`
meeting the budget inequality dominates `sparsificationBudget n ε δ`.
Together with `_pos` and `_le` this certifies the closed form as
exactly the minimal certified budget, not merely one valid choice. -/
theorem sparsificationBudget_min (n : ℕ) (ε δ : ℝ) {q : ℕ} (hq : 0 < q)
    (hqbudget : (8 / 3) * Real.log (2 * (n : ℝ) / δ) / ε ^ 2 ≤ (q : ℝ)) :
    sparsificationBudget n ε δ ≤ q :=
  max_le hq (Nat.ceil_le.2 hqbudget)

/-- **The plug-in budget guarantee** — `sparsification_graph_budget`
at `q := ↑(sparsificationBudget (card V) ε δ)`: pass only the graph
hypotheses and `(ε, δ)`; the sampling count comes out of the certified
formula (positivity and budget inequality discharged by
`sparsificationBudget_pos`/`_le`). CONDITIONAL ON THE
`matrix_bernstein` AXIOM — it applies `sparsification_graph_budget`;
the budget *arithmetic* (`sparsificationBudget` and its three lemmas)
is axiom-free, but the guarantee obtained here is exactly as trusted as
that axiom. See `docs/gnn-sparsification-budget.md`. -/
theorem sparsification_graph_budget_closedForm [Nonempty V]
    (hnn : ∀ i j, 0 ≤ A i j) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) :
    ssMeasure A hA ((sparsificationBudget (Fintype.card V) ε δ : ℝ))
        (Nat.cast_pos.2 (sparsificationBudget_pos (Fintype.card V) ε δ)).le
        {ω | ∃ x : V → ℝ, (1 - ε) * quadForm (laplacian A) x
            > quadForm (ssLaplacian A hA
                ((sparsificationBudget (Fintype.card V) ε δ : ℝ)) ω) x ∨
          quadForm (ssLaplacian A hA
                ((sparsificationBudget (Fintype.card V) ε δ : ℝ)) ω) x
            > (1 + ε) * quadForm (laplacian A) x}
      ≤ ENNReal.ofReal δ :=
  sparsification_graph_budget A hA hnn ε hε hε1 δ hδ _
    (Nat.cast_pos.2 (sparsificationBudget_pos (Fintype.card V) ε δ))
    (sparsificationBudget_le (Fintype.card V) ε δ)

end Scaffold.Derived.SparsificationTail
