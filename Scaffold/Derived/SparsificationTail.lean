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
  eigen-coordinate pullback of the norm event (the multiplicative
  refinement on `im Π`-coordinate vectors is a priced follow-on).

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
  have hindep : ∀ i j : Fin (Fintype.card (V × V)), i ≠ j →
      IndepFun (fun ω : (V × V) → Bool =>
          ssSummand A hA q ((Fintype.equivFin (V × V)).symm i) ω)
        (fun ω : (V × V) → Bool =>
          ssSummand A hA q ((Fintype.equivFin (V × V)).symm j) ω)
        (ssMeasure A hA q hq.le) :=
    fun i j hij => indepFun_ssSummand A hA q hq.le
      ((Fintype.equivFin (V × V)).symm.injective.ne hij)
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

end Scaffold.Derived.SparsificationTail
