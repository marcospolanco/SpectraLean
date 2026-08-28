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
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# The i.i.d. product sampling space at a finite distribution

The shelf's second concrete probability space and its first over an
arbitrary finite value type: the product of `n` independent copies of
a `V`-valued random variable with law `q : V → ℝ` (nonnegative,
summing to one), built as a `PMF` (`iidPMF`) and transferred to a
`MeasureTheory.Measure` for Bochner integration.

This is the sampling-space prerequisite named by
`proposals/empirical-stationary-distribution-concentration.md`'s
Step 0 survey (delivered with this module): the survey found no
V-valued i.i.d. measure anywhere in the shelf — the only concrete
probability space was `Probability.BernoulliProduct`'s product
Bernoulli on `ι → Bool` — and the minimal object is exactly that
module's construction with the two-atom Bernoulli factor replaced by
an arbitrary normalized `q`. The arithmetic core
(`Finset.sum_prod_piFinset`, the factorized one- and two-coordinate
marginals) generalizes verbatim; the pinned Mathlib supplies no
coordinate-independence lemma on product measures, so this module
closes that gap at exactly the finite generality the consumers need,
consumer-neutral: no estimator is built here, only the sampling
space and the clause shapes the scalar concentration axioms demand:

- `measurable_indicator_coord` / `indepFun_indicator_coord`: the
  `h_meas` and `h_indep` clauses of `hoeffding_empirical` at the
  `[0, 1]`-valued coordinate indicators;
- `integral_indicator`: the mean clause's arithmetic
  `∫ 1_{ω e = i} ∂μ = q i` — the constant the empirical form's
  internal centering collapses to.

## Scope notes

- The σ-algebra on the sampling space `ι → V` is Mathlib's global
  `MeasurableSpace.pi` over a `[MeasurableSpace V]` carried as an
  instance hypothesis together with `[MeasurableSingletonClass V]`
  (both discharge automatically on `Fin n` vertex types, the shelf's
  fixture idiom).
- Everything here is proved; no axioms are admitted or consumed.
- Junk behavior is bounded by construction hypotheses: outside
  `0 ≤ q` and `∑ q = 1` the joint masses fail to sum to `1` and
  `iidPMF`'s hypotheses cannot be discharged (fenced in QA at
  `q = ![2, 0]`).

QA: `Scaffold/QA/Probability/IIDProduct_QA.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Scaffold.Mathlib.Probability.IIDProduct

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The joint product mass at the factor distribution `q`: the
pointwise product of the coordinate masses. -/
noncomputable def iidMass (q : V → ℝ) (ω : ι → V) : ℝ≥0∞ :=
  ∏ k, ENNReal.ofReal (q (ω k))

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem sum_mass_eq_one {q : V → ℝ} (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1) :
    ∑ v, ENNReal.ofReal (q v) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => hq0 v), hq1, ENNReal.ofReal_one]

omit [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem sum_iidMass_eq_one {q : V → ℝ} (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1) :
    ∑ ω : ι → V, iidMass q ω = 1 := by
  have hpi : (Finset.univ : Finset (ι → V)) = Fintype.piFinset fun _ => Finset.univ := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hpi]
  simp only [iidMass]
  rw [Finset.sum_prod_piFinset (Finset.univ : Finset V) (fun _ v => ENNReal.ofReal (q v))]
  exact Finset.prod_eq_one fun k _ => sum_mass_eq_one hq0 hq1

omit [DecidableEq ι] [DecidableEq V] [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem iidMass_ne_top (q : V → ℝ) (ω : ι → V) : iidMass q ω ≠ ⊤ := by
  have hlt : iidMass q ω < ⊤ := by
    rw [show iidMass q ω = ∏ k, ENNReal.ofReal (q (ω k)) from rfl]
    exact ENNReal.prod_lt_top fun k _ => ENNReal.ofReal_lt_top
  exact hlt.ne

/-- The i.i.d. product PMF on the sampling space `ι → V` at the
factor distribution `q`. The hypotheses `hq0 hq1` are load-bearing:
they are exactly what makes the joint mass a probability mass
function. -/
noncomputable def iidPMF (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1) :
    PMF (ι → V) :=
  PMF.ofFinset (iidMass q) Finset.univ (sum_iidMass_eq_one hq0 hq1)
    (fun _ h => absurd (Finset.mem_univ _) h)

set_option linter.unusedSectionVars false in
omit [MeasurableSpace V] [MeasurableSingletonClass V] in
theorem iidPMF_apply {q : V → ℝ} (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (ω : ι → V) : iidPMF q hq0 hq1 ω = iidMass q ω := rfl

end Product

section Marginal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [Fintype V]

/-- The one-distinguished-coordinate product family (see
`BernoulliProduct.coordG1` for the pattern): an auxiliary atom shape
so that the marginal lemma below can be stated at arbitrary
factorized weights `F` without higher-order-pattern unification
failures. -/
private noncomputable def coordG1 (q : V → ℝ) (e : ι) (F : V → ℝ≥0∞) (i : ι) (v : V) :
    ℝ≥0∞ :=
  if i = e then F v * ENNReal.ofReal (q v) else ENNReal.ofReal (q v)

/-- The two-distinguished-coordinate analogue. -/
private noncomputable def coordG2 (q : V → ℝ) (e e' : ι) (F G : V → ℝ≥0∞) (i : ι) (v : V) :
    ℝ≥0∞ :=
  if i = e then F v * ENNReal.ofReal (q v)
  else if i = e' then G v * ENNReal.ofReal (q v) else ENNReal.ofReal (q v)

omit [Fintype ι] [Fintype V] in
private theorem coordG1_eq (q : V → ℝ) (e : ι) (F : V → ℝ≥0∞) (v : V) :
    coordG1 q e F e v = F v * ENNReal.ofReal (q v) := if_pos rfl

omit [Fintype ι] [Fintype V] in
private theorem coordG1_ne (q : V → ℝ) (e : ι) (F : V → ℝ≥0∞) {i : ι} (h : i ≠ e) (v : V) :
    coordG1 q e F i v = ENNReal.ofReal (q v) := if_neg h

omit [Fintype ι] [Fintype V] in
private theorem coordG2_eq (q : V → ℝ) (e e' : ι) (F G : V → ℝ≥0∞) (v : V) :
    coordG2 q e e' F G e v = F v * ENNReal.ofReal (q v) := by
  rw [coordG2, if_pos rfl]

omit [Fintype ι] [Fintype V] in
private theorem coordG2_eq' (q : V → ℝ) {e e' : ι} (hee : e ≠ e') (F G : V → ℝ≥0∞) (v : V) :
    coordG2 q e e' F G e' v = G v * ENNReal.ofReal (q v) := by
  rw [coordG2, if_neg (Ne.symm hee), if_pos rfl]

omit [Fintype ι] [Fintype V] in
private theorem coordG2_ne (q : V → ℝ) (e e' : ι) (F G : V → ℝ≥0∞) {i : ι}
    (h : i ≠ e) (h' : i ≠ e') (v : V) :
    coordG2 q e e' F G i v = ENNReal.ofReal (q v) := by
  rw [coordG2, if_neg h, if_neg h']

/-- The one-coordinate marginal: summing any factorized weight
against the joint mass collapses to the factor marginal at `e`. This
is the arithmetic core of the product structure. -/
theorem sum_coord_mul (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (e : ι) (F : V → ℝ≥0∞) :
    ∑ ω : ι → V, F (ω e) * iidMass q ω = ∑ v, F v * ENNReal.ofReal (q v) := by
  classical
  have hprod : ∀ ω : ι → V, F (ω e) * iidMass q ω
      = ∏ i, coordG1 q e F i (ω i) := by
    intro ω
    have he : e ∈ (Finset.univ : Finset ι) := Finset.mem_univ e
    calc F (ω e) * iidMass q ω
        = F (ω e) * (ENNReal.ofReal (q (ω e)) * ∏ i ∈ Finset.univ.erase e, ENNReal.ofReal (q (ω i))) := by
          rw [show iidMass q ω = ∏ i, ENNReal.ofReal (q (ω i)) from rfl,
            Finset.mul_prod_erase (Finset.univ : Finset ι) (fun i => ENNReal.ofReal (q (ω i))) he]
      _ = ∏ i, coordG1 q e F i (ω i) := by
          rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
            (fun i => coordG1 q e F i (ω i)) he]
          simp only [coordG1_eq, mul_assoc]
          exact congrArg (fun X => F (ω e) * (ENNReal.ofReal (q (ω e)) * X))
            (Finset.prod_congr rfl fun i hi =>
              (coordG1_ne q e F (Finset.mem_erase.mp hi).1 (ω i)).symm)
  have hpi : (Finset.univ : Finset (ι → V)) = Fintype.piFinset fun _ => Finset.univ := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hpi, Finset.sum_congr rfl (fun ω _ => hprod ω),
    Finset.sum_prod_piFinset (Finset.univ : Finset V) (fun i v => coordG1 q e F i v)]
  have he : e ∈ (Finset.univ : Finset ι) := Finset.mem_univ e
  rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun i => ∑ j, coordG1 q e F i j) he]
  simp only [coordG1_eq]
  rw [Finset.prod_eq_one fun i hi => by
    rw [Finset.sum_congr rfl
        (fun j _ => coordG1_ne q e F (Finset.mem_erase.mp hi).1 j),
      sum_mass_eq_one hq0 hq1], mul_one]

/-- The two-coordinate marginal: independence's arithmetic core — the
joint sum against factorized weights in two distinct coordinates
factorizes as the product of the one-coordinate marginals. -/
theorem sum_coord2_mul (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    {e e' : ι} (hee : e ≠ e') (F G : V → ℝ≥0∞) :
    ∑ ω : ι → V, F (ω e) * G (ω e') * iidMass q ω
      = (∑ v, F v * ENNReal.ofReal (q v)) * (∑ v, G v * ENNReal.ofReal (q v)) := by
  classical
  have hee' : e' ∈ (Finset.univ : Finset ι).erase e :=
    Finset.mem_erase.mpr ⟨Ne.symm hee, Finset.mem_univ _⟩
  have hprod : ∀ ω : ι → V, F (ω e) * G (ω e') * iidMass q ω
      = ∏ i, coordG2 q e e' F G i (ω i) := by
    intro ω
    have he : e ∈ (Finset.univ : Finset ι) := Finset.mem_univ e
    calc F (ω e) * G (ω e') * iidMass q ω
        = (F (ω e) * ENNReal.ofReal (q (ω e))) * ((G (ω e') * ENNReal.ofReal (q (ω e'))) *
            ∏ i ∈ ((Finset.univ : Finset ι).erase e).erase e', ENNReal.ofReal (q (ω i))) := by
          rw [show iidMass q ω = ∏ i, ENNReal.ofReal (q (ω i)) from rfl,
            ← Finset.mul_prod_erase (Finset.univ : Finset ι)
              (fun i => ENNReal.ofReal (q (ω i))) he,
            ← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase e)
              (fun i => ENNReal.ofReal (q (ω i))) hee']
          simp only [mul_comm, mul_assoc, mul_left_comm]
      _ = ∏ i, coordG2 q e e' F G i (ω i) := by
          rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
            (fun i => coordG2 q e e' F G i (ω i)) he]
          simp only [coordG2_eq, mul_assoc]
          rw [← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase e)
            (fun i => coordG2 q e e' F G i (ω i)) hee']
          simp only [coordG2_eq' q hee, mul_comm, mul_assoc, mul_left_comm]
          refine congrArg (fun X => F (ω e) * (G (ω e') *
            (ENNReal.ofReal (q (ω e)) * (ENNReal.ofReal (q (ω e')) * X)))) ?_
          exact Finset.prod_congr rfl fun i hi =>
            (coordG2_ne q e e' F G
              (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
              (Finset.mem_erase.mp hi).1 (ω i)).symm
  have hpi : (Finset.univ : Finset (ι → V)) = Fintype.piFinset fun _ => Finset.univ := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hpi, Finset.sum_congr rfl (fun ω _ => hprod ω),
    Finset.sum_prod_piFinset (Finset.univ : Finset V) (fun i v => coordG2 q e e' F G i v)]
  have he : e ∈ (Finset.univ : Finset ι) := Finset.mem_univ e
  rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun i => ∑ j, coordG2 q e e' F G i j) he]
  simp only [coordG2_eq, mul_assoc]
  rw [← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase e)
    (fun i => ∑ j, coordG2 q e e' F G i j) hee']
  simp only [coordG2_eq' q hee, mul_assoc]
  rw [Finset.prod_eq_one fun i hi => by
    rw [Finset.sum_congr rfl
        (fun j _ => coordG2_ne q e e' F G
          (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
          (Finset.mem_erase.mp hi).1 j),
      sum_mass_eq_one hq0 hq1], mul_one]

end Marginal

section Independence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [Fintype V] [DecidableEq V] [MeasurableSpace V] [MeasurableSingletonClass V]

omit [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] [MeasurableSingletonClass V] in
/-- Measurability of a coordinate projection at the product σ-algebra
(Mathlib's global `MeasurableSpace.pi` over the instance on `V`). -/
theorem measurable_coord (e : ι) :
    Measurable fun ω : ι → V => ω e :=
  measurable_pi_apply e

open scoped Classical in
set_option linter.unusedSectionVars false in
/-- The measure of a coordinate cylinder is the factor mass at that
coordinate. -/
theorem toMeasure_cyl (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (e : ι) (s : Set V) :
    (iidPMF q hq0 hq1).toMeasure ((fun ω : ι → V => ω e) ⁻¹' s)
      = ∑ v, (if v ∈ s then 1 else 0) * ENNReal.ofReal (q v) := by
  have hmeas : MeasurableSet ((fun ω : ι → V => ω e) ⁻¹' s) :=
    (measurable_coord e) (Set.toFinite s |>.measurableSet)
  calc (iidPMF q hq0 hq1).toMeasure ((fun ω : ι → V => ω e) ⁻¹' s)
      = ∑ ω : ι → V, (if ω ∈ (fun ω : ι → V => ω e) ⁻¹' s then iidPMF q hq0 hq1 ω else 0) := by
        rw [PMF.toMeasure_apply (iidPMF q hq0 hq1) _ hmeas, tsum_fintype]
        simp only [Set.indicator_apply]
    _ = ∑ ω : ι → V, (if ω e ∈ s then 1 else 0) * iidMass q ω := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Set.mem_preimage, iidPMF_apply]
        split_ifs <;> simp
    _ = ∑ v, (if v ∈ s then 1 else 0) * ENNReal.ofReal (q v) :=
        sum_coord_mul q hq0 hq1 e (fun v => if v ∈ s then 1 else 0)

open scoped Classical in
/-- Pairwise independence of the coordinate projections — the
independence core at the `V`-valued projections (the indicator lift
below is the clause shape the concentration axioms demand). -/
theorem indepFun_coord (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    {e e' : ι} (hee : e ≠ e') :
    IndepFun (fun ω : ι → V => ω e) (fun ω : ι → V => ω e')
      (iidPMF q hq0 hq1).toMeasure := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hmeas : MeasurableSet ((fun ω : ι → V => ω e) ⁻¹' s
      ∩ (fun ω : ι → V => ω e') ⁻¹' t) :=
    ((measurable_coord e) (Set.toFinite s |>.measurableSet)).inter
      ((measurable_coord e') (Set.toFinite t |>.measurableSet))
  calc (iidPMF q hq0 hq1).toMeasure
        ((fun ω : ι → V => ω e) ⁻¹' s ∩ (fun ω : ι → V => ω e') ⁻¹' t)
      = ∑ ω : ι → V, (if ω ∈ (fun ω : ι → V => ω e) ⁻¹' s
            ∩ (fun ω : ι → V => ω e') ⁻¹' t then iidPMF q hq0 hq1 ω else 0) := by
        rw [PMF.toMeasure_apply (iidPMF q hq0 hq1) _ hmeas, tsum_fintype]
        simp only [Set.indicator_apply]
    _ = ∑ ω : ι → V, ((if ω e ∈ s then 1 else 0) * (if ω e' ∈ t then 1 else 0))
            * iidMass q ω := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h1 : ω e ∈ s <;> by_cases h2 : ω e' ∈ t <;>
          simp [Set.mem_inter_iff, Set.mem_preimage, iidPMF_apply, h1, h2]
    _ = (∑ v, (if v ∈ s then 1 else 0) * ENNReal.ofReal (q v))
        * (∑ v, (if v ∈ t then 1 else 0) * ENNReal.ofReal (q v)) :=
        sum_coord2_mul q hq0 hq1 hee (fun v => if v ∈ s then 1 else 0)
          (fun v => if v ∈ t then 1 else 0)
  rw [toMeasure_cyl q hq0 hq1 e s, toMeasure_cyl q hq0 hq1 e' t]

omit [Fintype ι] [DecidableEq ι] in
/-- Measurability of the coordinate indicator — the `h_meas` clause
shape of `hoeffding_empirical` at this sampling space. -/
theorem measurable_indicator_coord (e : ι) (i : V) :
    Measurable fun ω : ι → V => (if ω e = i then (1 : ℝ) else 0) :=
  (measurable_of_finite (fun v : V => if v = i then (1 : ℝ) else 0)).comp
    (measurable_coord e)

/-- The indicator mass atom of the centering integral. -/
private noncomputable def indicatorMass (q : V → ℝ) (e : ι) (i : V) (ω : ι → V) : ℝ≥0∞ :=
  (if ω e = i then (1 : ℝ≥0∞) else 0) * iidMass q ω

/-- The centering integral: the indicator mean is the factor mass —
the mean clause of `hoeffding_empirical` and the constant that
theorem's internal centering collapses to at this sampling space. -/
theorem integral_indicator (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    (e : ι) (i : V) :
    ∫ ω : ι → V, (if ω e = i then (1 : ℝ) else 0) ∂(iidPMF q hq0 hq1).toMeasure
      = q i := by
  have heval : (∑ v : V, (if v = i then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (q v))
      = ENNReal.ofReal (q i) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [PMF.integral_eq_sum]
  rw [Finset.sum_congr rfl fun ω _ => by
    show ((iidPMF q hq0 hq1) ω).toReal * (if ω e = i then (1 : ℝ) else 0)
        = (indicatorMass q e i ω).toReal
    by_cases hω : ω e = i <;> simp [iidPMF_apply, indicatorMass, hω]]
  have hfin : ∀ a : ι → V, indicatorMass q e i a ≠ ⊤ := by
    intro a
    unfold indicatorMass
    by_cases ha : a e = i
    · rw [if_pos ha, one_mul]
      exact iidMass_ne_top q a
    · rw [if_neg ha, zero_mul]
      simp
  rw [← ENNReal.toReal_sum]
  · rw [show ∑ ω : ι → V, indicatorMass q e i ω
        = ∑ v : V, (if v = i then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (q v) from by
        calc ∑ ω : ι → V, indicatorMass q e i ω
            = ∑ ω : ι → V, (if ω e = i then (1 : ℝ≥0∞) else 0) * iidMass q ω :=
              Finset.sum_congr rfl fun ω _ => rfl
          _ = ∑ v : V, (if v = i then (1 : ℝ≥0∞) else 0) * ENNReal.ofReal (q v) :=
              sum_coord_mul q hq0 hq1 e (fun v => if v = i then 1 else 0)]
    rw [heval, ENNReal.toReal_ofReal (hq0 i)]
  · exact fun a _ => hfin a

/-- Pairwise independence of the coordinate indicators — the exact
`h_indep` clause shape of `hoeffding_empirical` at this sampling
space. -/
theorem indepFun_indicator_coord (q : V → ℝ) (hq0 : ∀ v, 0 ≤ q v) (hq1 : ∑ v, q v = 1)
    {e e' : ι} (hee : e ≠ e') (i j : V) :
    IndepFun (fun ω : ι → V => (if ω e = i then (1 : ℝ) else 0))
      (fun ω : ι → V => (if ω e' = j then (1 : ℝ) else 0))
      (iidPMF q hq0 hq1).toMeasure :=
  (indepFun_coord q hq0 hq1 hee).comp
    (measurable_of_finite (fun v : V => if v = i then (1 : ℝ) else 0))
    (measurable_of_finite (fun v : V => if v = j then (1 : ℝ) else 0))

end Independence

end Scaffold.Mathlib.Probability.IIDProduct
