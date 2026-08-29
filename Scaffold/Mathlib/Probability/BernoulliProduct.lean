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
import Mathlib.Analysis.CStarAlgebra.Matrix
import Scaffold.Mathlib.Probability.Concentration.Matrix.Basic

/-!
# The independent-Bernoulli product sampling space

The shelf's first concrete probability space: the product-Bernoulli
measure on `ι → Bool` at a parameter vector `p : ι → ℝ` with
`0 ≤ p i ≤ 1`, built as a `PMF` (`bernPMF`) and transferred to a
`MeasureTheory.Measure` for Bochner integration.

This is the sampling-space slice (Step 1, Slice 1) of the
leverage-score sparsification program
(`proposals/spectral-sparsification-via-leverage-scores.md`): the
delivered interfaces are exactly the clause shapes the matrix
concentration axioms' hypothesis sets demand at a concrete measure —

- `indepFun_coord` / `indepFun_coord_matrix`: pairwise `IndepFun` of
  coordinate projections (and of matrix-valued functions of single
  coordinates) — the `h_indep` clause of `matrix_bernstein`;
- `integral_delta` / `integral_coord_smul` /
  `integral_coord_center_smul`: the Bernoulli centering arithmetic
  `∫ δ_e ∂μ = p e` at the scalar, and its matrix lifts
  `∫ (δ_e) • M = p e • M` and
  `∫ ((δ_e / p e) - 1) • M = 0` at `p e ≠ 0` — the `h_mean` clause;
- `stronglyMeasurable_coord_matrix` / `measurable_coord_matrix`: the
  `h_meas` clause at the spectral-norm topology and at the shelf's
  product σ-algebra on matrices.

The same object is the i.i.d.-sampling prerequisite named by
`proposals/empirical-stationary-distribution-concentration.md`'s
Step 0, so the module is deliberately consumer-neutral: no sparsifier
is built here, only the sampling space.

## Scope notes

- This is not a general measure-theory development: only the finite
  product-Bernoulli space is constructed, by direct ∑-∏ arithmetic
  (`Finset.sum_prod_piFinset`) — the pinned Mathlib supplies no
  coordinate-independence lemma on product measures, and this module
  closes that gap at exactly the finite generality the consumers need.
- Everything here is proved; no axioms are admitted or consumed.
- Junk behavior is bounded by construction hypotheses: `bern p i b =
  ofReal (if b then p i else 1 - p i)` clamps nonpositive masses to
  `0` through `ENNReal.ofReal`, so outside `0 ≤ p i ≤ 1` the joint
  masses simply fail to sum to `1` and `bernPMF`'s hypotheses cannot
  be discharged (fenced in QA at `p = ![2]`).
- The σ-algebra on `ι → Bool` is Mathlib's global `MeasurableSpace.pi`
  instance over `Bool`'s discrete one; no new measurable-space
  structure is introduced.

QA: `Scaffold/QA/Probability/BernoulliProduct_QA.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix.L2OpNorm

namespace Scaffold.Mathlib.Probability.BernoulliProduct

section Product

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Per-coordinate Bernoulli mass: `ofReal (p i)` at `true` and
`ofReal (1 - p i)` at `false`. Junk outside `0 ≤ p i ≤ 1`: the
`ofReal` clamp maps negative masses to `0`, so the mass normalization
`∑ b, bern p i b = 1` (and hence `bernPMF`) fails there. -/
noncomputable def bern (p : ι → ℝ) (i : ι) (b : Bool) : ℝ≥0∞ :=
  ENNReal.ofReal (if b then p i else 1 - p i)

/-- The joint product mass: the pointwise product of the coordinate
masses. -/
noncomputable def jointMass (p : ι → ℝ) (ω : ι → Bool) : ℝ≥0∞ := ∏ i, bern p i (ω i)

omit [DecidableEq ι] in
theorem jointMass_ne_top (p : ι → ℝ) (ω : ι → Bool) : jointMass p ω ≠ ⊤ := by
  have hlt : jointMass p ω < ⊤ := by
    rw [show jointMass p ω = ∏ i, bern p i (ω i) from rfl]
    exact ENNReal.prod_lt_top fun i _ => by
      have hb : bern p i (ω i) = ENNReal.ofReal (if ω i then p i else 1 - p i) := rfl
      rw [hb]
      exact ENNReal.ofReal_lt_top
  exact hlt.ne

omit [Fintype ι] [DecidableEq ι] in
theorem sum_bern_eq_one (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) (i : ι) :
    ∑ b, bern p i b = 1 := by
  have hb : (Finset.univ : Finset Bool) = {false, true} := by
    ext b; cases b <;> simp
  have hF : bern p i false = ENNReal.ofReal (1 - p i) := rfl
  have hT : bern p i true = ENNReal.ofReal (p i) := rfl
  rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton, hF, hT,
    ← ENNReal.ofReal_add (by linarith [hp1 i]) (by linarith [hp0 i]),
    show (1 - p i) + p i = 1 from by ring, ENNReal.ofReal_one]

theorem sum_jointMass_eq_one (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    ∑ ω, jointMass p ω = 1 := by
  have hpi : (Finset.univ : Finset (ι → Bool)) = Fintype.piFinset fun _ => Finset.univ := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hpi]
  simp only [jointMass]
  rw [Finset.sum_prod_piFinset (Finset.univ : Finset Bool) (fun i b => bern p i b)]
  exact Finset.prod_eq_one fun i _ => sum_bern_eq_one p hp0 hp1 i

/-- The product-Bernoulli PMF on the sampling space `ι → Bool`. The
hypotheses `hp0 hp1` are load-bearing: they are exactly what makes the
joint mass a probability mass function. -/
noncomputable def bernPMF (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    PMF (ι → Bool) :=
  PMF.ofFinset (jointMass p) Finset.univ (sum_jointMass_eq_one p hp0 hp1)
    (fun _ h => absurd (Finset.mem_univ _) h)

theorem bernPMF_apply (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (ω : ι → Bool) : bernPMF p hp0 hp1 ω = jointMass p ω := rfl

end Product

section Marginal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The one-distinguished-coordinate product family: an auxiliary
atom shape so that the marginal lemma below can be stated at arbitrary
factorized weights `F` without higher-order-pattern unification
failures. -/
private noncomputable def coordG1 (p : ι → ℝ) (e : ι) (F : Bool → ℝ≥0∞) (i : ι) (b : Bool) :
    ℝ≥0∞ :=
  if i = e then F b * bern p e b else bern p i b

/-- The two-distinguished-coordinate analogue. -/
private noncomputable def coordG2 (p : ι → ℝ) (e e' : ι) (F G : Bool → ℝ≥0∞) (i : ι) (b : Bool) :
    ℝ≥0∞ :=
  if i = e then F b * bern p e b
  else if i = e' then G b * bern p e' b else bern p i b

omit [Fintype ι] in
private theorem coordG1_eq (p : ι → ℝ) (e : ι) (F : Bool → ℝ≥0∞) (b : Bool) :
    coordG1 p e F e b = F b * bern p e b := if_pos rfl

omit [Fintype ι] in
private theorem coordG1_ne (p : ι → ℝ) (e : ι) (F : Bool → ℝ≥0∞) {i : ι} (h : i ≠ e) (b : Bool) :
    coordG1 p e F i b = bern p i b := if_neg h

omit [Fintype ι] in
private theorem coordG2_eq (p : ι → ℝ) (e e' : ι) (F G : Bool → ℝ≥0∞) (b : Bool) :
    coordG2 p e e' F G e b = F b * bern p e b := by
  rw [coordG2, if_pos rfl]

omit [Fintype ι] in
private theorem coordG2_eq' (p : ι → ℝ) (e e' : ι) (hee : e ≠ e') (F G : Bool → ℝ≥0∞) (b : Bool) :
    coordG2 p e e' F G e' b = G b * bern p e' b := by
  rw [coordG2, if_neg (Ne.symm hee), if_pos rfl]

omit [Fintype ι] in
private theorem coordG2_ne (p : ι → ℝ) (e e' : ι) (F G : Bool → ℝ≥0∞) {i : ι}
    (h : i ≠ e) (h' : i ≠ e') (b : Bool) :
    coordG2 p e e' F G i b = bern p i b := by
  rw [coordG2, if_neg h, if_neg h']

/-- The one-coordinate marginal: summing any factorized weight against
the joint mass collapses to the Bernoulli marginal at `e`. This is the
arithmetic core of the product structure. -/
theorem sum_coord_mul (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (e : ι) (F : Bool → ℝ≥0∞) :
    ∑ ω, F (ω e) * jointMass p ω = ∑ b, F b * bern p e b := by
  classical
  have hprod : ∀ ω : ι → Bool, F (ω e) * jointMass p ω
      = ∏ i, coordG1 p e F i (ω i) := by
    intro ω
    have he : e ∈ (Finset.univ : Finset ι) := Finset.mem_univ e
    calc F (ω e) * jointMass p ω
        = F (ω e) * (bern p e (ω e) * ∏ i ∈ Finset.univ.erase e, bern p i (ω i)) := by
          rw [show jointMass p ω = ∏ i, bern p i (ω i) from rfl,
            Finset.mul_prod_erase (Finset.univ : Finset ι) (fun i => bern p i (ω i)) he]
      _ = ∏ i, coordG1 p e F i (ω i) := by
          rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
            (fun i => coordG1 p e F i (ω i)) he]
          simp only [coordG1_eq, mul_assoc]
          exact congrArg (fun X => F (ω e) * (bern p e (ω e) * X))
            (Finset.prod_congr rfl fun i hi =>
              (coordG1_ne p e F (Finset.mem_erase.mp hi).1 (ω i)).symm)
  have hpi : (Finset.univ : Finset (ι → Bool)) = Fintype.piFinset fun _ => Finset.univ := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hpi, Finset.sum_congr rfl (fun ω _ => hprod ω),
    Finset.sum_prod_piFinset (Finset.univ : Finset Bool) (fun i b => coordG1 p e F i b)]
  have he : e ∈ (Finset.univ : Finset ι) := Finset.mem_univ e
  rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun i => ∑ j, coordG1 p e F i j) he]
  simp only [coordG1_eq]
  rw [Finset.prod_eq_one fun i hi => by
    rw [Finset.sum_congr rfl
        (fun j _ => coordG1_ne p e F (Finset.mem_erase.mp hi).1 j),
      sum_bern_eq_one p hp0 hp1 i], mul_one]

/-- The two-coordinate marginal: independence's arithmetic core — the
joint sum against factorized weights in two distinct coordinates
factorizes as the product of the one-coordinate marginals. -/
theorem sum_coord2_mul (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {e e' : ι} (hee : e ≠ e') (F G : Bool → ℝ≥0∞) :
    ∑ ω, F (ω e) * G (ω e') * jointMass p ω
      = (∑ b, F b * bern p e b) * (∑ b, G b * bern p e' b) := by
  classical
  have hee' : e' ∈ (Finset.univ : Finset ι).erase e :=
    Finset.mem_erase.mpr ⟨Ne.symm hee, Finset.mem_univ _⟩
  have hprod : ∀ ω : ι → Bool, F (ω e) * G (ω e') * jointMass p ω
      = ∏ i, coordG2 p e e' F G i (ω i) := by
    intro ω
    have he : e ∈ (Finset.univ : Finset ι) := Finset.mem_univ e
    calc F (ω e) * G (ω e') * jointMass p ω
        = (F (ω e) * bern p e (ω e)) * ((G (ω e') * bern p e' (ω e')) *
            ∏ i ∈ ((Finset.univ : Finset ι).erase e).erase e', bern p i (ω i)) := by
          rw [show jointMass p ω = ∏ i, bern p i (ω i) from rfl,
            ← Finset.mul_prod_erase (Finset.univ : Finset ι)
              (fun i => bern p i (ω i)) he,
            ← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase e)
              (fun i => bern p i (ω i)) hee']
          simp only [mul_comm, mul_assoc, mul_left_comm]
      _ = ∏ i, coordG2 p e e' F G i (ω i) := by
          rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
            (fun i => coordG2 p e e' F G i (ω i)) he]
          simp only [coordG2_eq, mul_assoc]
          rw [← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase e)
            (fun i => coordG2 p e e' F G i (ω i)) hee']
          simp only [coordG2_eq' p e e' hee, mul_comm, mul_assoc, mul_left_comm]
          refine congrArg (fun X => F (ω e) * (G (ω e') *
            (bern p e (ω e) * (bern p e' (ω e') * X)))) ?_
          exact Finset.prod_congr rfl fun i hi =>
            (coordG2_ne p e e' F G
              (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
              (Finset.mem_erase.mp hi).1 (ω i)).symm
  have hpi : (Finset.univ : Finset (ι → Bool)) = Fintype.piFinset fun _ => Finset.univ := by
    ext ω; simp [Fintype.mem_piFinset]
  rw [hpi, Finset.sum_congr rfl (fun ω _ => hprod ω),
    Finset.sum_prod_piFinset (Finset.univ : Finset Bool) (fun i b => coordG2 p e e' F G i b)]
  have he : e ∈ (Finset.univ : Finset ι) := Finset.mem_univ e
  rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
    (fun i => ∑ j, coordG2 p e e' F G i j) he]
  simp only [coordG2_eq, mul_assoc]
  rw [← Finset.mul_prod_erase ((Finset.univ : Finset ι).erase e)
    (fun i => ∑ j, coordG2 p e e' F G i j) hee']
  simp only [coordG2_eq' p e e' hee, mul_assoc]
  rw [Finset.prod_eq_one fun i hi => by
    rw [Finset.sum_congr rfl
        (fun j _ => coordG2_ne p e e' F G
          (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
          (Finset.mem_erase.mp hi).1 j),
      sum_bern_eq_one p hp0 hp1 i], mul_one]

end Marginal

section Independence

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The δ_e-weighted mass: the scalar centering integrand's mass-side
atom. -/
private noncomputable def deltaMass (p : ι → ℝ) (e : ι) (ω : ι → Bool) : ℝ≥0∞ :=
  (if ω e then (1 : ℝ≥0∞) else 0) * jointMass p ω

omit [Fintype ι] [DecidableEq ι] in
/-- Measurability of a coordinate projection at the product σ-algebra
(Mathlib's global `MeasurableSpace.pi` over `Bool`'s discrete one). -/
theorem measurable_coord (e : ι) :
    Measurable fun ω : ι → Bool => ω e :=
  measurable_pi_apply e

open scoped Classical in
/-- The measure of a coordinate cylinder is the Bernoulli mass at that
coordinate. -/
theorem toMeasure_cyl (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (e : ι) (s : Set Bool) :
    (bernPMF p hp0 hp1).toMeasure ((fun ω : ι → Bool => ω e) ⁻¹' s)
      = ∑ b, (if b ∈ s then 1 else 0) * bern p e b := by
  have hmeas : MeasurableSet ((fun ω : ι → Bool => ω e) ⁻¹' s) :=
    (measurable_coord e) (Set.toFinite s |>.measurableSet)
  calc (bernPMF p hp0 hp1).toMeasure ((fun ω : ι → Bool => ω e) ⁻¹' s)
      = ∑ ω, (if ω ∈ (fun ω : ι → Bool => ω e) ⁻¹' s then bernPMF p hp0 hp1 ω else 0) := by
        rw [PMF.toMeasure_apply (bernPMF p hp0 hp1) _ hmeas, tsum_fintype]
        simp only [Set.indicator_apply]
    _ = ∑ ω, (if ω e ∈ s then 1 else 0) * jointMass p ω := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        rw [Set.mem_preimage, bernPMF_apply]
        split_ifs <;> simp
    _ = ∑ b, (if b ∈ s then 1 else 0) * bern p e b :=
        sum_coord_mul p hp0 hp1 e (fun b => if b ∈ s then 1 else 0)

open scoped Classical in
/-- Pairwise independence of the coordinate projections — the exact
shape of the matrix concentration axioms' `h_indep` clause at the
scalar codomain (the matrix lift is `indepFun_coord_matrix` below). -/
theorem indepFun_coord (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {e e' : ι} (hee : e ≠ e') :
    IndepFun (fun ω : ι → Bool => ω e) (fun ω : ι → Bool => ω e')
      (bernPMF p hp0 hp1).toMeasure := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have hmeas : MeasurableSet ((fun ω : ι → Bool => ω e) ⁻¹' s
      ∩ (fun ω : ι → Bool => ω e') ⁻¹' t) :=
    ((measurable_coord e) (Set.toFinite s |>.measurableSet)).inter
      ((measurable_coord e') (Set.toFinite t |>.measurableSet))
  calc (bernPMF p hp0 hp1).toMeasure
        ((fun ω : ι → Bool => ω e) ⁻¹' s ∩ (fun ω : ι → Bool => ω e') ⁻¹' t)
      = ∑ ω, (if ω ∈ (fun ω : ι → Bool => ω e) ⁻¹' s
            ∩ (fun ω : ι → Bool => ω e') ⁻¹' t then bernPMF p hp0 hp1 ω else 0) := by
        rw [PMF.toMeasure_apply (bernPMF p hp0 hp1) _ hmeas, tsum_fintype]
        simp only [Set.indicator_apply]
    _ = ∑ ω, ((if ω e ∈ s then 1 else 0) * (if ω e' ∈ t then 1 else 0))
            * jointMass p ω := by
        refine Finset.sum_congr rfl fun ω _ => ?_
        by_cases h1 : ω e ∈ s <;> by_cases h2 : ω e' ∈ t <;>
          simp [Set.mem_inter_iff, Set.mem_preimage, bernPMF_apply, h1, h2]
    _ = (∑ b, (if b ∈ s then 1 else 0) * bern p e b)
        * (∑ b, (if b ∈ t then 1 else 0) * bern p e' b) :=
        sum_coord2_mul p hp0 hp1 hee (fun b => if b ∈ s then 1 else 0)
          (fun b => if b ∈ t then 1 else 0)
  rw [toMeasure_cyl p hp0 hp1 e s, toMeasure_cyl p hp0 hp1 e' t]

/-- The centering integral at the scalar codomain: the Bernoulli mean
`∫ δ_e ∂μ = p e`, the scalar core of the matrix concentration axioms'
`h_mean` clause. -/
theorem integral_delta (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (e : ι) :
    ∫ ω : ι → Bool, (if ω e then (1 : ℝ) else 0) ∂(bernPMF p hp0 hp1).toMeasure
      = p e := by
  have heval : (∑ b : Bool, (if b then (1 : ℝ≥0∞) else 0) * bern p e b)
      = ENNReal.ofReal (p e) := by
    have hb : (Finset.univ : Finset Bool) = {false, true} := by
      ext b; cases b <;> simp
    rw [hb, Finset.sum_insert (by simp), Finset.sum_singleton]
    simp [bern]
  rw [PMF.integral_eq_sum]
  rw [Finset.sum_congr rfl fun ω _ => by
    show ((bernPMF p hp0 hp1) ω).toReal * (if ω e then (1 : ℝ) else 0)
        = (deltaMass p e ω).toReal
    cases hω : ω e <;> simp [bernPMF_apply, deltaMass, hω]]
  have hfin : ∀ a : ι → Bool, deltaMass p e a ≠ ⊤ := by
    intro a
    unfold deltaMass
    cases ha : a e <;> simp [ha, jointMass_ne_top p]
  rw [← ENNReal.toReal_sum]
  · rw [show ∑ ω : ι → Bool, deltaMass p e ω
        = ∑ b : Bool, (if b then (1 : ℝ≥0∞) else 0) * bern p e b from by
        calc ∑ ω : ι → Bool, deltaMass p e ω
            = ∑ ω : ι → Bool, (if ω e then (1 : ℝ≥0∞) else 0) * jointMass p ω :=
              Finset.sum_congr rfl fun ω _ => rfl
          _ = ∑ b : Bool, (if b then (1 : ℝ≥0∞) else 0) * bern p e b :=
              sum_coord_mul p hp0 hp1 e (fun b => if b then 1 else 0)]
    rw [heval, ENNReal.toReal_ofReal (hp0 e)]
  · exact fun a _ => hfin a

/-- The second-moment companion of `integral_delta`: the centered
Bernoulli square integrates to the variance `∫ (δ_e − p e)² ∂μ =
p e (1 − p e)` — the scalar core of the `bernstein_inequality` axiom's
variance clause at any design built from centered Bernoulli factors.
Through the pointwise expansion `(δ − p)² = δ • (1 − 2p) + p²` (δ² = δ),
linearity, and `integral_delta` itself: a wrong Bernoulli mean or a
wrong centering breaks exactly this. Added 2026-08-29 for the
Bernstein-twin delivery
(`proposals/hoeffding-inequality-degree-concentration.md`). -/
theorem integral_sq_delta_sub (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (e : ι) :
    ∫ ω : ι → Bool, ((if ω e then (1 : ℝ) else 0) - p e) ^ 2
        ∂(bernPMF p hp0 hp1).toMeasure = p e * (1 - p e) := by
  haveI : IsProbabilityMeasure (bernPMF p hp0 hp1).toMeasure :=
    PMF.toMeasure.isProbabilityMeasure _
  have hexp : ∀ ω : ι → Bool,
      ((if ω e then (1 : ℝ) else 0) - p e) ^ 2
        = (if ω e then (1 : ℝ) else 0) • (1 - 2 * p e) + p e * p e := by
    intro ω
    cases h : ω e <;> simp [h] <;> ring
  have heq : (fun ω : ι → Bool => ((if ω e then (1 : ℝ) else 0) - p e) ^ 2)
      = fun ω : ι → Bool =>
          (if ω e then (1 : ℝ) else 0) • (1 - 2 * p e) + p e * p e :=
    funext hexp
  rw [heq, integral_add
    (f := fun ω : ι → Bool => (if ω e then (1 : ℝ) else 0) • (1 - 2 * p e))
    (g := fun _ : ι → Bool => p e * p e) Integrable.of_finite (integrable_const _)]
  rw [integral_smul_const, integral_delta p hp0 hp1 e]
  have hc : ∫ (_ : ι → Bool), p e * p e ∂(bernPMF p hp0 hp1).toMeasure = p e * p e := by
    rw [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  rw [hc, smul_eq_mul]
  ring

end Independence

section IIndep

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Classical in
/-- The mass of a finite coordinate-cylinder intersection — the
finite-family generalization of `toMeasure_cyl` (its `|T| = 1` case)
and the engine for the coordinates' mutual independence below. -/
theorem toMeasure_cyl_inter (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (T : Finset ι) (A : ι → Set Bool) :
    (bernPMF p hp0 hp1).toMeasure (⋂ i ∈ T, (fun ω : ι → Bool => ω i) ⁻¹' A i)
      = ∏ i ∈ T, ∑ b, (if b ∈ A i then (1 : ℝ≥0∞) else 0) * bern p i b := by
  have hmeas : MeasurableSet (⋂ i ∈ T, (fun ω : ι → Bool => ω i) ⁻¹' A i) :=
    Set.Finite.measurableSet (Set.toFinite _)
  rw [PMF.toMeasure_apply (bernPMF p hp0 hp1) _ hmeas, tsum_fintype]
  simp only [Set.indicator_apply, Set.mem_iInter, Set.mem_preimage]
  have hpt : ∀ ω : ι → Bool,
      (if ∀ i ∈ T, ω i ∈ A i then bernPMF p hp0 hp1 ω else 0)
        = ∏ i, ((if i ∈ T then (if ω i ∈ A i then (1 : ℝ≥0∞) else 0) else 1)
            * bern p i (ω i)) := by
    intro ω
    by_cases hall : ∀ i ∈ T, ω i ∈ A i
    · rw [if_pos hall, bernPMF_apply,
        show jointMass p ω = ∏ i, bern p i (ω i) from rfl, Finset.prod_mul_distrib]
      have hone : (∏ i : ι, if i ∈ T then (if ω i ∈ A i then (1 : ℝ≥0∞) else 0) else 1) = 1 :=
        Finset.prod_eq_one fun i _ => by
          by_cases hi : i ∈ T
          · rw [if_pos hi, if_pos (hall i hi)]
          · rw [if_neg hi]
      rw [hone, one_mul]
    · push_neg at hall
      obtain ⟨i₀, hi₀T, hi₀A⟩ := hall
      have hzero : ∏ i, ((if i ∈ T then (if ω i ∈ A i then (1 : ℝ≥0∞) else 0) else 1)
          * bern p i (ω i)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
        rw [if_pos hi₀T, if_neg hi₀A, zero_mul]
      rw [if_neg (fun h => hi₀A (h i₀ hi₀T)), hzero]
  rw [Finset.sum_congr rfl (fun ω _ => hpt ω),
    show (Finset.univ : Finset (ι → Bool)) = Fintype.piFinset fun _ => Finset.univ from by
      ext ω; simp [Fintype.mem_piFinset],
    Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
      (fun i b => (if i ∈ T then (if b ∈ A i then (1 : ℝ≥0∞) else 0) else 1) * bern p i b)]
  have houter : ∏ i : ι, ∑ b : Bool,
      ((if i ∈ T then (if b ∈ A i then (1 : ℝ≥0∞) else 0) else 1) * bern p i b)
      = ∏ i ∈ T, ∑ b : Bool,
      ((if i ∈ T then (if b ∈ A i then (1 : ℝ≥0∞) else 0) else 1) * bern p i b) := by
    refine (Finset.prod_subset (Finset.subset_univ T) fun i _ hi => ?_).symm
    simp only [if_neg hi, one_mul]
    exact sum_bern_eq_one p hp0 hp1 i
  rw [houter]
  exact Finset.prod_congr rfl fun i hi => by
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [if_pos hi]

/-- Mutual independence of the coordinate projections — the repaired
`h_indep` clause shape of the concentration axioms at the
BernoulliProduct design (the pairwise `indepFun_coord` above is its
two-point consequence, kept for the refutation records). -/
theorem iIndepFun_coord (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    iIndepFun (fun _ : ι => (inferInstance : MeasurableSpace Bool))
      (fun (i : ι) (ω : ι → Bool) => ω i) (bernPMF p hp0 hp1).toMeasure := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro T sets hsets
  rw [toMeasure_cyl_inter p hp0 hp1 T sets]
  exact Finset.prod_congr rfl fun i _ => (toMeasure_cyl p hp0 hp1 i (sets i)).symm

/-- Mutual independence is inherited by injectively reindexed
families (uniform codomain — the shape every design consumer needs). -/
theorem iIndepFun_of_injective {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ι ι' γ : Type*} {mγ : MeasurableSpace γ}
    {f : ι → Ω → γ} (hf : iIndepFun (fun _ : ι => mγ) f μ) (e : ι' → ι)
    (he : Function.Injective e) :
    iIndepFun (fun _ : ι' => mγ) (fun x : ι' => f (e x)) μ := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hf ⊢
  intro T' sets' hsets'
  set A : ι → Set γ := fun j =>
    if h : ∃ k, e k = j ∧ k ∈ T' then sets' h.choose else Set.univ with hA
  have hAeq : ∀ (k : ι') (hk : k ∈ T'), A (e k) = sets' k := by
    intro k hk
    have hex : ∃ k', e k' = e k ∧ k' ∈ T' := ⟨k, rfl, hk⟩
    show (if h : ∃ k', e k' = e k ∧ k' ∈ T' then sets' h.choose else Set.univ) = sets' k
    rw [dif_pos hex]
    have hke : hex.choose = k := he hex.choose_spec.1
    rw [hke]
  have hAmeas : ∀ j ∈ T'.image e, MeasurableSet (A j) := by
    intro j hj
    show MeasurableSet (if h : ∃ k, e k = j ∧ k ∈ T' then sets' h.choose else Set.univ)
    by_cases hex : ∃ k, e k = j ∧ k ∈ T'
    · rw [dif_pos hex]; exact hsets' _ hex.choose_spec.2
    · rw [dif_neg hex]; exact MeasurableSet.univ
  have himage : (⋂ k ∈ T', (f (e k)) ⁻¹' sets' k)
      = ⋂ j ∈ T'.image e, (f j) ⁻¹' A j := by
    ext ω
    simp only [Set.mem_iInter, Set.mem_preimage]
    constructor
    · intro h j hj
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      have h1 : A (e k) = sets' k := hAeq k hk
      rw [h1]
      exact h k hk
    · intro h k hk
      have h1 : A (e k) = sets' k := hAeq k hk
      have h2 : f (e k) ω ∈ A (e k) := h (e k) (Finset.mem_image_of_mem (f := e) hk)
      rw [h1] at h2
      exact h2
  have hmass := hf (T'.image e) (sets := A) hAmeas
  rw [himage, hmass, Finset.prod_image (fun a _ b _ hab => he hab)]
  exact Finset.prod_congr rfl fun k hk => by rw [hAeq k hk]


/-- Mutual independence at an arbitrary measurable codomain with all
single-coordinate factors measurable, for summand families factoring
through injectively-distinct single coordinates — the repaired
`h_indep` clause shape at the scalar layer (the degree-tail design). -/
theorem iIndepFun_coord_apply (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {γ : Type*} {mγ : MeasurableSpace γ}
    {ι' : Type*} [Fintype ι'] (e : ι' → ι) (he : Function.Injective e)
    (F : ι' → Bool → γ) (hF : ∀ k, Measurable (F k)) :
    iIndepFun (fun _ : ι' => mγ)
      (fun (k : ι') (ω : ι → Bool) => F k (ω (e k))) (bernPMF p hp0 hp1).toMeasure :=
  (iIndepFun_of_injective (iIndepFun_coord p hp0 hp1) e he).comp F hF

/-- Mutual independence at the matrix codomain, for summand families
factoring through injectively-distinct single coordinates — the
repaired `h_indep` clause shape at the matrix layer (the sparsification
and edge-perturbation designs). -/
theorem iIndepFun_coord_matrix (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {ι' : Type*} [Fintype ι'] (e : ι' → ι) (he : Function.Injective e)
    (F : ι' → Bool → Matrix V V ℝ) :
    iIndepFun (fun _ : ι' => (inferInstance : MeasurableSpace (Matrix V V ℝ)))
      (fun (k : ι') (ω : ι → Bool) => F k (ω (e k))) (bernPMF p hp0 hp1).toMeasure :=
  (iIndepFun_of_injective (iIndepFun_coord p hp0 hp1) e he).comp F
    (fun k => measurable_of_finite (F k))

end IIndep


section MatrixLayer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq ι] [Fintype V] [DecidableEq V] in
/-- The matrix layer's transfer target: a matrix-valued function of
the single coordinate `ω e` is `StronglyMeasurable` at the
`Matrix.L2OpNorm` topology, via Mathlib's
`StronglyMeasurable.of_finite` — a topology-only route, decisive here
because the shelf's matrix σ-algebra is a hand-rolled product instance
with no registered `BorelSpace` bridge. This is the `h_meas` clause
shape of `matrix_bernstein` at single-coordinate summand families. -/
theorem stronglyMeasurable_coord_matrix (F : Bool → Matrix V V ℝ) (e : ι) :
    StronglyMeasurable fun ω : ι → Bool => F (ω e) :=
  StronglyMeasurable.of_finite

omit [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V] in
/-- The same transfer at the shelf's matrix product σ-algebra
(`Concentration.Matrix.Basic.instMeasurableSpaceMatrixPi`): the
composition of the measurable coordinate projection with a function out
of the finite discrete type `Bool`. -/
theorem measurable_coord_matrix (F : Bool → Matrix V V ℝ) (e : ι) :
    Measurable fun ω : ι → Bool => F (ω e) :=
  (measurable_of_finite F).comp (measurable_coord e)

omit [Fintype V] [DecidableEq V] in
/-- Pairwise independence transferred to the matrix codomain: the
`h_indep` clause at the matrix layer, for summand families that factor
through single coordinates — the shape the sparsification summand
design produces. -/
theorem indepFun_coord_matrix (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (F G : Bool → Matrix V V ℝ) {e e' : ι} (hee : e ≠ e') :
    IndepFun (fun ω : ι → Bool => F (ω e)) (fun ω : ι → Bool => G (ω e'))
      (bernPMF p hp0 hp1).toMeasure :=
  (indepFun_coord p hp0 hp1 hee).comp (measurable_of_finite F) (measurable_of_finite G)

/-- The matrix centering building block: the scalar Bernoulli factor
`δ_e` smuling a fixed matrix integrates to the mean smul, through
`integral_smul_const` joined to the scalar `integral_delta`. This is
the `h_mean` clause's arithmetic at the matrix codomain. -/
theorem integral_coord_smul (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (e : ι) (M : Matrix V V ℝ) :
    ∫ ω : ι → Bool, (if ω e then (1 : ℝ) else 0) • M ∂(bernPMF p hp0 hp1).toMeasure
      = p e • M := by
  rw [integral_smul_const, integral_delta p hp0 hp1 e]

/-- The centered affine combination integrates to zero at `p e ≠ 0`:
the exact `h_mean` clause shape for the (unguarded) rank-one sampling
summand `(δ_e / p e - 1) • (v ⊗ v)` of the Spielman–Srivastava design.
Saturated edges (`p e = 1`), whose summand must instead be guarded to
zero by the Step-1 Slice 2 design decision, are not this lemma's
concern — nor are degenerate `p e = 0` parameters, at which the
conclusion is refuted in QA. -/
theorem integral_coord_center_smul (p : ι → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {e : ι} (hpne : p e ≠ 0) (M : Matrix V V ℝ) :
    ∫ ω : ι → Bool, ((if ω e then (1 : ℝ) else 0) / p e - 1) • M
      ∂(bernPMF p hp0 hp1).toMeasure = 0 := by
  rw [integral_smul_const]
  have hint : ∫ ω : ι → Bool, ((if ω e then (1 : ℝ) else 0) / p e - 1)
      ∂(bernPMF p hp0 hp1).toMeasure = 0 := by
    have h1 : ∫ ω : ι → Bool, (1 : ℝ) ∂(bernPMF p hp0 hp1).toMeasure = 1 := by
      rw [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
    have hfint : Integrable (fun ω : ι → Bool => (if ω e then (1 : ℝ) else 0) / p e)
        (bernPMF p hp0 hp1).toMeasure := Integrable.of_finite
    have hgint : Integrable (fun _ : ι → Bool => (1 : ℝ))
        (bernPMF p hp0 hp1).toMeasure := Integrable.of_finite
    rw [integral_sub hfint hgint, integral_div, integral_delta p hp0 hp1 e, h1,
      div_self hpne, sub_self]
  rw [hint, zero_smul]

end MatrixLayer

end Scaffold.Mathlib.Probability.BernoulliProduct
