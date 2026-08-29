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
import Scaffold.Mathlib.Probability.BernoulliProduct
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein
import Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Matrix.Bernstein
import Scaffold.Mathlib.GraphTheory.Sparsification

/-!
# The pairwise-independence refutations of the concentration axioms' pre-repair shapes

The six concentration axioms were repaired in place on 2026-08-29
(run `20260829T173340Z-run-1`, continued `20260829T195611Z-run-1`):
their `h_indep` clauses hypothesized only *pairwise* `IndepFun`, and
pairwise independence does not suffice for Hoeffding/Chernoff bounds.

This file proves that defect in hypothesis form. The witness family is
the fifteen nonempty Walsh characters of the fair `BernoulliProduct`
on `Fin 4 → Bool` — the subset-product signs `walsh v ω = ∏_{i ∈ v}
(-1)^{ω i}`, indexed by the nonzero `v : Fin 4 → Bool`. They are
pairwise independent under the fair coin (proved here through the
xor-translation group action on the sixteen atoms, which forces all
four joint sign cells to a common mass `q` with `4q = 1`), they are
centered (each integrates to zero by a coordinate-flip involution),
and bounded by `1`; but their sum is `15` on the all-false atom
(mass `1/16`) and `-1` elsewhere, so every concentration tail event
of the old statements contains an atom of mass `1/16` while the
old bounds fall below `1/16` (proved with elementary arithmetic from
`e^{1/2} ≥ 3/2` and `e ≥ 9/4`).

The six refutations (one per repaired axiom):

* `old_hoeffding_inequality_pairwise_refuted_QA` — bound
  `2 exp(-15²/30) < 1/16` against event mass `1/16`;
* `old_bernstein_inequality_pairwise_refuted_QA` — the internal
  variance is the true `15`, bound `2 exp(-15²/40) < 1/16`;
* `old_bernstein_bounded_variance_pairwise_refuted_QA` — the budget
  form at the same true variance;
* `old_hoeffding_empirical_pairwise_refuted_QA` — the `[0,1]`-valued
  affine images at threshold `1/2`, bound `2 exp(-2·15·(1/2)²) < 1/16`;
* `old_matrix_hoeffding_pairwise_refuted_QA` — the rank-one lift
  `walsh v ω • E` on `V = Fin 2` at the idempotent `E` with `‖E‖ = 1`
  (via `‖Eᴴ E‖ = ‖E‖²`), bound `4 exp(-15²/30) < 1/16`;
* `old_matrix_bernstein_pairwise_refuted_QA` — the same lift's
  centered form, bound `4 exp(-15²/40) < 1/16`.

These are refutation records, not validations: they prove the
*pre-repair* statements false (in the same hypothesis form as the
2026-08-28 degenerate-dimension refutations in
`Scaffold/QA/Concentration/Matrix_QA.lean`) and thereby justify the
`iIndepFun` repair; they say nothing about the repaired axioms'
truth, which remains the cited literature's to establish.
-/

open MeasureTheory ProbabilityTheory
open Scaffold.Mathlib.Probability.BernoulliProduct
open scoped ENNReal BigOperators Matrix Matrix.L2OpNorm

namespace Scaffold.QA.Concentration.PairwiseIndependence


noncomputable def wFair : Fin 4 → ℝ := fun _ => 1 / 2

theorem wFair_nonneg : ∀ i, 0 ≤ wFair i := by intro i; unfold wFair; norm_num
theorem wFair_le_one : ∀ i, wFair i ≤ 1 := by intro i; unfold wFair; norm_num

noncomputable def wPMF : PMF (Fin 4 → Bool) :=
  bernPMF wFair wFair_nonneg wFair_le_one
noncomputable def wμ : Measure (Fin 4 → Bool) := wPMF.toMeasure

instance : IsProbabilityMeasure wμ := PMF.toMeasure.isProbabilityMeasure _

def allF : Fin 4 → Bool := fun _ => false

/-- The ±1 sign of a coin. -/
def wsgn : Bool → ℝ := fun b => if b then -1 else 1

/-- The Walsh character at support-vector `v`: the product of the signs
of the coins in `v`'s support. -/
def walsh (v ω : Fin 4 → Bool) : ℝ := ∏ i, if v i then wsgn (ω i) else 1

/-! ### Atom-level facts -/

theorem xor_xor (a b : Bool) : xor (xor a b) b = a := by cases a <;> cases b <;> rfl
theorem xor_self (a : Bool) : xor a a = false := by cases a <;> rfl

theorem wbern (i : Fin 4) (b : Bool) : bern wFair i b = ENNReal.ofReal ((1 : ℝ) / 2) := by
  cases b with
  | false =>
      show ENNReal.ofReal (1 - wFair i) = ENNReal.ofReal ((1 : ℝ) / 2)
      rw [wFair]
      norm_num
  | true =>
      show ENNReal.ofReal (wFair i) = ENNReal.ofReal ((1 : ℝ) / 2)
      rw [wFair]

theorem wmass (ω : Fin 4 → Bool) : (wPMF ω : ℝ≥0∞) = ENNReal.ofReal ((1 : ℝ) / 16) := by
  have h1 : (wPMF ω : ℝ≥0∞) = (jointMass wFair ω : ℝ≥0∞) := rfl
  rw [h1, jointMass, Finset.prod_congr rfl (fun i _ => wbern i (ω i)),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

open scoped Classical in
theorem wμ_sum (S : Set (Fin 4 → Bool)) (hm : MeasurableSet S) :
    wμ S = ∑ ω : Fin 4 → Bool, if ω ∈ S then (ENNReal.ofReal ((1 : ℝ) / 16)) else 0 := by
  classical
  have h1 : wμ = (wPMF).toMeasure := rfl
  rw [h1, PMF.toMeasure_apply wPMF S hm, tsum_fintype]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Set.indicator_apply, wmass ω]

open scoped Classical in
theorem wμ_singleton : wμ ({allF} : Set (Fin 4 → Bool)) = ENNReal.ofReal ((1 : ℝ) / 16) := by
  have hmeas : MeasurableSet ({allF} : Set (Fin 4 → Bool)) :=
    measurableSet_singleton _
  have h1 : wμ = wPMF.toMeasure := rfl
  rw [h1, PMF.toMeasure_apply _ _ hmeas, tsum_fintype]
  simp only [Set.indicator_apply]
  rw [Finset.sum_eq_single allF
    (fun ω _ hne => if_neg (by simp [hne]))
    (fun hmem => absurd (Finset.mem_univ _) hmem)]
  rw [if_pos (Set.mem_singleton allF), wmass allF]

/-! ### The xor translation -/

def bxor (ω u : Fin 4 → Bool) : Fin 4 → Bool := fun i => xor (ω i) (u i)

theorem bxor_invol (ω u : Fin 4 → Bool) : bxor (bxor ω u) u = ω := by
  funext i
  exact xor_xor (ω i) (u i)

theorem bxor_self (ω : Fin 4 → Bool) : bxor ω ω = allF := by
  funext i
  exact xor_self (ω i)

theorem bxor_bij (u : Fin 4 → Bool) : Function.Bijective (fun ω => bxor ω u) := by
  refine Function.bijective_iff_has_inverse.2 ⟨fun ω => bxor ω u, fun ω => bxor_invol ω u,
    fun ω => bxor_invol ω u⟩

/-- The single-coordinate flip vector. -/
def flipAt (i : Fin 4) : Fin 4 → Bool := fun j => if j = i then true else false

theorem walsh_mul (v ω u : Fin 4 → Bool) :
    walsh v (bxor ω u) = walsh v ω * walsh v u := by
  unfold walsh bxor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hvi : v i = true
  · cases ω i <;> cases u i <;> simp [wsgn, hvi]
  · simp [wsgn, hvi]

theorem walsh_allF (v : Fin 4 → Bool) : walsh v allF = 1 :=
  Finset.prod_eq_one fun i _ => by
    by_cases hvi : v i = true <;> simp [walsh, wsgn, hvi, allF]

theorem walsh_triv_char (ω : Fin 4 → Bool) : walsh allF ω = 1 :=
  Finset.prod_eq_one fun i _ => by
    simp [walsh, allF]

theorem walsh_sq (v ω : Fin 4 → Bool) : walsh v ω * walsh v ω = 1 := by
  have h := walsh_mul v ω ω
  rw [bxor_self] at h
  rw [← h, walsh_allF]

theorem walsh_dichotomy (v ω : Fin 4 → Bool) : walsh v ω = 1 ∨ walsh v ω = -1 := by
  have h : (walsh v ω) ^ 2 = 1 := by rw [sq]; exact walsh_sq v ω
  exact sq_eq_one_iff.mp h

theorem walsh_flipAt_neg (v : Fin 4 → Bool) (i : Fin 4) (hvi : v i = true) :
    walsh v (flipAt i) = -1 := by
  have hi : i ∈ (Finset.univ : Finset (Fin 4)) := Finset.mem_univ i
  have hone : (∏ j ∈ Finset.univ.erase i, (if v j then wsgn (flipAt i j) else 1)) = 1 :=
    Finset.prod_eq_one fun j hj => by
      have hf : flipAt i j = false := if_neg (Finset.mem_erase.mp hj).1
      rw [hf]
      by_cases hvj : v j = true <;> simp [hvj, wsgn]
  have hmain : (if v i then wsgn (flipAt i i) else 1) = -1 := by
    rw [hvi]
    simp [wsgn, flipAt]
  calc walsh v (flipAt i)
      = (if v i then wsgn (flipAt i i) else 1) *
          ∏ j ∈ Finset.univ.erase i, (if v j then wsgn (flipAt i j) else 1) := by
        rw [walsh, Finset.mul_prod_erase (Finset.univ : Finset (Fin 4))
          (fun j => if v j then wsgn (flipAt i j) else 1) hi]
    _ = -1 * 1 := by rw [hone, hmain]
    _ = -1 := by norm_num

theorem walsh_flipAt_one (w : Fin 4 → Bool) (i : Fin 4) (hwi : w i = false) :
    walsh w (flipAt i) = 1 :=
  Finset.prod_eq_one fun j _ => by
    by_cases hji : j = i
    · rw [hji]
      exact if_neg (by simp [hwi])
    · by_cases hwj : w j = true
      · rw [if_pos hwj]
        simp [wsgn, flipAt, hji]
      · rw [if_neg hwj]

/-! ### Reindexing, mean-zero -/

theorem wsum_bxor {M : Type*} [AddCommMonoid M] (u : Fin 4 → Bool)
    (g : (Fin 4 → Bool) → M) :
    ∑ ω : Fin 4 → Bool, g (bxor ω u) = ∑ ω : Fin 4 → Bool, g ω :=
  Fintype.sum_bijective _ (bxor_bij u) (fun ω => g (bxor ω u)) g (fun _ => rfl)

theorem walsh_sum_zero (v : Fin 4 → Bool) (hv : v ≠ allF) :
    ∑ ω : Fin 4 → Bool, walsh v ω = 0 := by
  obtain ⟨i₀, hi₀⟩ : ∃ i, v i = true := by
    by_contra hcon
    push_neg at hcon
    apply hv
    funext i
    cases hvb : v i with
    | false => rfl
    | true => exact absurd hvb (hcon i)
  have hidx : ∑ ω : Fin 4 → Bool, walsh v ω = ∑ ω : Fin 4 → Bool, -walsh v ω := by
    rw [← wsum_bxor (flipAt i₀) (walsh v)]
    exact Finset.sum_congr rfl fun ω _ => by
      rw [walsh_mul, walsh_flipAt_neg v i₀ hi₀, mul_neg_one]
  have h2 : ∑ ω : Fin 4 → Bool, -walsh v ω = -∑ ω : Fin 4 → Bool, walsh v ω :=
    Finset.sum_neg_distrib
  rw [hidx, h2]
  linarith

theorem walsh_mean_zero (v : Fin 4 → Bool) (hv : v ≠ allF) :
    ∫ ω : Fin 4 → Bool, walsh v ω ∂wμ = 0 := by
  classical
  have hw : wμ = wPMF.toMeasure := rfl
  rw [hw, PMF.integral_eq_sum]
  have hre : ∀ ω : Fin 4 → Bool, ((wPMF ω).toReal • walsh v ω) = (1 / 16 : ℝ) * walsh v ω := by
    intro ω
    rw [smul_eq_mul, wmass ω]
    norm_num
  rw [Finset.sum_congr rfl (fun ω _ => hre ω), ← Finset.mul_sum]
  rw [walsh_sum_zero v hv, mul_zero]

/-! ### The total sum over all sixteen characters -/

theorem walsh_total_sum (ω : Fin 4 → Bool) :
    ∑ v : Fin 4 → Bool, walsh v ω = ∏ i, (if ω i then (0 : ℝ) else 2) := by
  classical
  have hpt : ∀ v : Fin 4 → Bool,
      walsh v ω = ∏ i, (fun b => if b then wsgn (ω i) else 1) (v i) := fun v => rfl
  rw [Finset.sum_congr rfl (fun v _ => hpt v),
    show (Finset.univ : Finset (Fin 4 → Bool)) = Fintype.piFinset fun _ => Finset.univ from by
      ext v; simp [Fintype.mem_piFinset],
    Finset.sum_prod_piFinset (Finset.univ : Finset Bool)
      (fun i b => if b then wsgn (ω i) else 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases ω i <;> simp [wsgn, Fin.sum_univ_two]

theorem walsh_total_sum_allF : ∑ v : Fin 4 → Bool, walsh v allF = 16 := by
  rw [walsh_total_sum]
  have hf : ∀ i : Fin 4, (if allF i then (0 : ℝ) else 2) = 2 := by
    intro i; simp [allF]
  rw [Finset.prod_congr rfl (fun i _ => hf i), Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num

theorem walsh_total_sum_of_ne (ω : Fin 4 → Bool) (hω : ω ≠ allF) :
    ∑ v : Fin 4 → Bool, walsh v ω = 0 := by
  rw [walsh_total_sum, Finset.prod_eq_zero_iff.mpr]
  obtain ⟨i₀, hi₀⟩ : ∃ i, ω i = true := by
    by_contra hcon
    push_neg at hcon
    apply hω
    funext i
    cases hvb : ω i with
    | false => rfl
    | true => exact absurd hvb (hcon i)
  exact ⟨i₀, Finset.mem_univ i₀, by simp [hi₀]⟩

/-! ### Exponential numerics -/

theorem exp_half_ge : (3 / 2 : ℝ) ≤ Real.exp (1 / 2) := by
  have h := Real.add_one_le_exp (1 / 2)
  linarith

theorem pow_le_pow_left' {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) (n : ℕ) : a ^ n ≤ b ^ n :=
  pow_le_pow_left₀ ha h n

theorem exp_half_pow_ge (n : ℕ) : ((3 / 2 : ℝ) ^ n) ≤ Real.exp ((n : ℝ) / 2) := by
  rw [show ((n : ℝ) / 2) = (1 / 2) * (n : ℝ) from by ring, Real.exp_mul, Real.rpow_natCast]
  exact pow_le_pow_left' (by norm_num : (0 : ℝ) ≤ 3 / 2) exp_half_ge n

theorem exp_one_ge : (9 / 4 : ℝ) ≤ Real.exp 1 := by
  have h2 : Real.exp 1 = Real.exp (1 / 2) * Real.exp (1 / 2) := by
    rw [← Real.exp_add]
    ring_nf
  rw [h2]
  nlinarith [exp_half_ge]

theorem exp_nat_ge (n : ℕ) : ((9 / 4 : ℝ) ^ n) ≤ Real.exp ((n : ℝ)) := by
  rw [show ((n : ℝ)) = 1 * (n : ℝ) from by ring, Real.exp_mul, Real.rpow_natCast]
  exact pow_le_pow_left' (by norm_num : (0 : ℝ) ≤ 9 / 4) exp_one_ge n

theorem exp_75_gt : (64 : ℝ) < Real.exp (15 / 2) := by
  have h := exp_half_pow_ge 15
  norm_num at h
  linarith

theorem exp_5625_gt : (64 : ℝ) < Real.exp (45 / 8) := by
  have h5 := exp_nat_ge 5
  have h58 : (13 / 8 : ℝ) ≤ Real.exp (5 / 8) := by
    have := Real.add_one_le_exp (5 / 8)
    linarith
  have hsplit : Real.exp (45 / 8) = Real.exp 5 * Real.exp (5 / 8) := by
    rw [← Real.exp_add]
    ring_nf
  have hcomb : (9 / 4 : ℝ) ^ 5 * (13 / 8 : ℝ) ≤ Real.exp 5 * Real.exp (5 / 8) :=
    mul_le_mul h5 h58 (by positivity) (le_of_lt (Real.exp_pos 5))
  have hval : (9 / 4 : ℝ) ^ 5 * (13 / 8 : ℝ) = 767637 / 8192 := by norm_num
  rw [hval] at hcomb
  have hgt : (64 : ℝ) < 767637 / 8192 := by norm_num
  rw [hsplit]
  linarith

theorem exp_tail_lt {x c : ℝ} (hE : (64 : ℝ) < Real.exp x) (hc : c ≤ 4) :
    c * Real.exp (-x) < 1 / 16 := by
  have hpos : 0 < Real.exp x := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_iff₀ hpos]
  have h4 : (4 : ℝ) < (1 / 16) * Real.exp x := by
    rw [show (1 / 16 : ℝ) * Real.exp x = Real.exp x / 16 from by field_simp,
      lt_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    linarith
  linarith

theorem exp_bound_75 (c : ℝ) (hc : c = 4 ∨ c = 2) :
    c * Real.exp (-(15 / 2 : ℝ)) < 1 / 16 := by
  refine exp_tail_lt exp_75_gt ?_
  rcases hc with h | h <;> rw [h]; norm_num

theorem exp_bound_5625 (c : ℝ) (hc : c = 4 ∨ c = 2) :
    c * Real.exp (-(45 / 8 : ℝ)) < 1 / 16 := by
  refine exp_tail_lt exp_5625_gt ?_
  rcases hc with h | h <;> rw [h]; norm_num

/-! ### Cells, the ±1 independence helper, and pairwise independence -/

theorem coin_exists (v : Fin 4 → Bool) (hv : v ≠ allF) : ∃ i, v i = true := by
  by_contra hcon
  push_neg at hcon
  apply hv
  funext i
  cases hvb : v i with
  | false => rfl
  | true => exact absurd hvb (hcon i)

theorem walsh_measurable (v : Fin 4 → Bool) : Measurable (walsh v) := by
  have hfactor : ∀ i : Fin 4,
      StronglyMeasurable (fun ω : Fin 4 → Bool => if v i then wsgn (ω i) else 1) :=
    fun i =>
      ((measurable_of_finite (fun b : Bool => if v i then wsgn b else 1)).comp
        (measurable_coord i)).stronglyMeasurable
  have hsm : StronglyMeasurable (walsh v) :=
    Finset.stronglyMeasurable_prod' Finset.univ (fun i _ => hfactor i)
  exact hsm.measurable

def wcell (v w : Fin 4 → Bool) (σ τ : ℝ) : Set (Fin 4 → Bool) :=
  {ω | walsh v ω = σ ∧ walsh w ω = τ}

theorem wcell_measurable (v w : Fin 4 → Bool) (σ τ : ℝ) :
    MeasurableSet (wcell v w σ τ) :=
  ((walsh_measurable v) (measurableSet_singleton σ)).inter
    ((walsh_measurable w) (measurableSet_singleton τ))

theorem wcell_bxor (v w : Fin 4 → Bool) (σ τ : ℝ) (u : Fin 4 → Bool) :
    wcell v w σ τ = (fun ω : Fin 4 → Bool => bxor ω u) ⁻¹'
      wcell v w (σ * walsh v u) (τ * walsh w u) := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by rw [walsh_mul, h1], by rw [walsh_mul, h2]⟩
  · rintro ⟨h1, h2⟩
    rw [walsh_mul] at h1
    rw [walsh_mul] at h2
    constructor
    · rcases walsh_dichotomy v u with c | c <;> rw [c] at h1 <;>
        nlinarith [walsh_sq v u]
    · rcases walsh_dichotomy w u with c | c <;> rw [c] at h2 <;>
        nlinarith [walsh_sq w u]

theorem wμ_cell_transport (v w : Fin 4 → Bool) (σ τ : ℝ) (u : Fin 4 → Bool) :
    wμ (wcell v w σ τ) = wμ (wcell v w (σ * walsh v u) (τ * walsh w u)) := by
  classical
  have hmS : MeasurableSet ((fun ω : Fin 4 → Bool => bxor ω u) ⁻¹'
      wcell v w (σ * walsh v u) (τ * walsh w u)) := by
    rw [← wcell_bxor]
    exact wcell_measurable v w σ τ
  have hmT : MeasurableSet (wcell v w (σ * walsh v u) (τ * walsh w u)) :=
    wcell_measurable v w _ _
  rw [wcell_bxor, wμ_sum _ hmS, wμ_sum _ hmT]
  exact Fintype.sum_bijective _ (bxor_bij u) _ _ (fun ω => rfl)

theorem wcell_disj_left (v w : Fin 4 → Bool) {σ σ' τ τ' : ℝ} (h : σ ≠ σ') :
    Disjoint (wcell v w σ τ) (wcell v w σ' τ') := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp only [wcell, Set.mem_setOf_eq] at hx1 hx2
  exact h (hx1.1.symm.trans hx2.1)

theorem wcell_disj_right (v w : Fin 4 → Bool) {σ σ' τ τ' : ℝ} (h : τ ≠ τ') :
    Disjoint (wcell v w σ τ) (wcell v w σ' τ') := by
  rw [Set.disjoint_left]
  intro x hx1 hx2
  simp only [wcell, Set.mem_setOf_eq] at hx1 hx2
  exact h (hx1.2.symm.trans hx2.2)

theorem wcells_partition (v w : Fin 4 → Bool) :
    wμ (wcell v w 1 1) + wμ (wcell v w 1 (-1))
      + (wμ (wcell v w (-1) 1) + wμ (wcell v w (-1) (-1))) = 1 := by
  have hd1 : Disjoint (wcell v w 1 1) (wcell v w 1 (-1)) :=
    wcell_disj_right v w (by norm_num)
  have hd2 : Disjoint (wcell v w (-1) 1) (wcell v w (-1) (-1)) :=
    wcell_disj_right v w (by norm_num)
  have hdL : Disjoint (wcell v w 1 1 ∪ wcell v w 1 (-1))
      (wcell v w (-1) 1 ∪ wcell v w (-1) (-1)) := by
    have hA : Disjoint (wcell v w 1 1) (wcell v w (-1) 1 ∪ wcell v w (-1) (-1)) := by
      rw [Set.disjoint_union_right]
      exact ⟨wcell_disj_left v w (by norm_num), wcell_disj_left v w (by norm_num)⟩
    have hB : Disjoint (wcell v w 1 (-1)) (wcell v w (-1) 1 ∪ wcell v w (-1) (-1)) := by
      rw [Set.disjoint_union_right]
      exact ⟨wcell_disj_left v w (by norm_num), wcell_disj_left v w (by norm_num)⟩
    rw [Set.disjoint_union_left]
    exact ⟨hA, hB⟩
  have hunion : (wcell v w 1 1 ∪ wcell v w 1 (-1))
      ∪ (wcell v w (-1) 1 ∪ wcell v w (-1) (-1)) = Set.univ := by
    ext ω
    simp only [Set.mem_union, Set.mem_univ, iff_true]
    rcases walsh_dichotomy v ω with hv | hv <;>
      rcases walsh_dichotomy w ω with hw | hw <;>
      simp [wcell, hv, hw]
  have h1 : wμ (wcell v w 1 1) + wμ (wcell v w 1 (-1))
      = wμ (wcell v w 1 1 ∪ wcell v w 1 (-1)) :=
    (measure_union hd1 (wcell_measurable v w 1 (-1))).symm
  have h2 : wμ (wcell v w (-1) 1) + wμ (wcell v w (-1) (-1))
      = wμ (wcell v w (-1) 1 ∪ wcell v w (-1) (-1)) :=
    (measure_union hd2 (wcell_measurable v w (-1) (-1))).symm
  have h3 : wμ (wcell v w 1 1 ∪ wcell v w 1 (-1))
      + wμ (wcell v w (-1) 1 ∪ wcell v w (-1) (-1))
      = wμ ((wcell v w 1 1 ∪ wcell v w 1 (-1))
        ∪ (wcell v w (-1) 1 ∪ wcell v w (-1) (-1))) :=
    (measure_union hdL ((wcell_measurable v w (-1) 1).union
      (wcell_measurable v w (-1) (-1)))).symm
  rw [h1, h2, h3, hunion, measure_univ]

/-- All four sign cells of a genuinely distinct nontrivial pair carry a
common mass `q` with `4q = 1`. -/
theorem wcell_common_mass {v w u₁ u₂ : Fin 4 → Bool}
    (h1 : walsh v u₁ = -1) (h2 : walsh w u₁ = 1) (h3 : walsh w u₂ = -1) :
    ∃ q : ℝ≥0∞, (4 : ℝ≥0∞) * q = 1 ∧ ∀ σ ∈ ({1, -1} : Set ℝ),
      ∀ τ ∈ ({1, -1} : Set ℝ), wμ (wcell v w σ τ) = q := by
  have T1 : ∀ σ' τ' : ℝ, wμ (wcell v w σ' τ') = wμ (wcell v w (-σ') τ') := by
    intro σ' τ'
    have htr := wμ_cell_transport v w σ' τ' u₁
    rw [h1, h2] at htr
    simp only [mul_neg_one, mul_one] at htr
    exact htr
  have e2 : wμ (wcell v w 1 (-1)) = wμ (wcell v w 1 1) := by
    have hh := wμ_cell_transport v w 1 1 u₂
    rw [h3] at hh
    simp only [one_mul] at hh
    rcases walsh_dichotomy v u₂ with hc | hc
    · rw [hc] at hh
      exact hh.symm
    · rw [hc] at hh
      exact (T1 1 (-1)).trans hh.symm
  refine ⟨wμ (wcell v w 1 1), ?_, ?_⟩
  · have hp := wcells_partition v w
    rw [← T1 1 1, ← T1 1 (-1), e2] at hp
    rw [show (4 : ℝ≥0∞) * wμ (wcell v w 1 1)
          = wμ (wcell v w 1 1) + wμ (wcell v w 1 1)
              + (wμ (wcell v w 1 1) + wμ (wcell v w 1 1)) from by ring]
    exact hp
  · intro σ hσ τ hτ
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
    · rfl
    · exact e2
    · exact (T1 1 1).symm
    · exact (T1 1 (-1)).symm.trans e2

theorem indepFun_sign_fibers {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω')
    [IsProbabilityMeasure ν] {U W : Ω' → ℝ} {q : ℝ≥0∞}
    (hUm : Measurable U) (hWm : Measurable W)
    (hU : ∀ ω, U ω = 1 ∨ U ω = -1) (hW : ∀ ω, W ω = 1 ∨ W ω = -1)
    (hsum : (4 : ℝ≥0∞) * q = 1)
    (hcells : ∀ σ ∈ ({1, -1} : Set ℝ), ∀ τ ∈ ({1, -1} : Set ℝ),
      ν {ω | U ω = σ ∧ W ω = τ} = q) :
    IndepFun U W ν := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  classical
  have hm1 : (1 : ℝ) ∈ ({1, -1} : Set ℝ) := by simp
  have hm2 : (-1 : ℝ) ∈ ({1, -1} : Set ℝ) := by simp
  have hq2 : (2 : ℝ≥0∞) * q * ((2 : ℝ≥0∞) * q) = q := by
    rw [show (2 : ℝ≥0∞) * q * ((2 : ℝ≥0∞) * q) = ((4 : ℝ≥0∞) * q) * q from by ring,
      hsum, one_mul]
  have h4q : (2 : ℝ≥0∞) * q + (2 : ℝ≥0∞) * q = 1 := by rw [← hsum]; ring
  -- set identifications
  have hUfull : ∀ r : Set ℝ, (1 : ℝ) ∈ r → (-1 : ℝ) ∈ r → U ⁻¹' r = Set.univ := by
    intro r h1 h2
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ]
    rcases hU ω with hc | hc
    · rw [hc]; exact iff_of_true h1 trivial
    · rw [hc]; exact iff_of_true h2 trivial
  have hUone : ∀ r : Set ℝ, (1 : ℝ) ∈ r → (-1 : ℝ) ∉ r → U ⁻¹' r = {ω | U ω = 1} := by
    intro r h1 h2
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rcases hU ω with hc | hc
    · rw [hc]; exact iff_of_true h1 rfl
    · rw [hc]; exact iff_of_false h2 (by norm_num)
  have hUminus : ∀ r : Set ℝ, (1 : ℝ) ∉ r → (-1 : ℝ) ∈ r → U ⁻¹' r = {ω | U ω = -1} := by
    intro r h1 h2
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rcases hU ω with hc | hc
    · rw [hc]; exact iff_of_false h1 (by norm_num)
    · rw [hc]; exact iff_of_true h2 rfl
  have hUempty : ∀ r : Set ℝ, (1 : ℝ) ∉ r → (-1 : ℝ) ∉ r → U ⁻¹' r = ∅ := by
    intro r h1 h2
    ext ω
    simp only [Set.mem_preimage, Set.mem_empty_iff_false]
    rcases hU ω with hc | hc
    · rw [hc]; exact iff_false_intro h1
    · rw [hc]; exact iff_false_intro h2
  have hWfull : ∀ r : Set ℝ, (1 : ℝ) ∈ r → (-1 : ℝ) ∈ r → W ⁻¹' r = Set.univ := by
    intro r h1 h2
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ]
    rcases hW ω with hc | hc
    · rw [hc]; exact iff_of_true h1 trivial
    · rw [hc]; exact iff_of_true h2 trivial
  have hWone : ∀ r : Set ℝ, (1 : ℝ) ∈ r → (-1 : ℝ) ∉ r → W ⁻¹' r = {ω | W ω = 1} := by
    intro r h1 h2
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rcases hW ω with hc | hc
    · rw [hc]; exact iff_of_true h1 rfl
    · rw [hc]; exact iff_of_false h2 (by norm_num)
  have hWminus : ∀ r : Set ℝ, (1 : ℝ) ∉ r → (-1 : ℝ) ∈ r → W ⁻¹' r = {ω | W ω = -1} := by
    intro r h1 h2
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    rcases hW ω with hc | hc
    · rw [hc]; exact iff_of_false h1 (by norm_num)
    · rw [hc]; exact iff_of_true h2 rfl
  have hWempty : ∀ r : Set ℝ, (1 : ℝ) ∉ r → (-1 : ℝ) ∉ r → W ⁻¹' r = ∅ := by
    intro r h1 h2
    ext ω
    simp only [Set.mem_preimage, Set.mem_empty_iff_false]
    rcases hW ω with hc | hc
    · rw [hc]; exact iff_false_intro h1
    · rw [hc]; exact iff_false_intro h2
  -- marginal measures
  have hcellmeas : ∀ σ τ : ℝ, MeasurableSet {ω : Ω' | U ω = σ ∧ W ω = τ} := by
    intro σ τ
    have h1 : {ω : Ω' | U ω = σ ∧ W ω = τ} = (U ⁻¹' {σ}) ∩ (W ⁻¹' {τ}) := rfl
    rw [h1]
    exact (hUm (measurableSet_singleton σ)).inter (hWm (measurableSet_singleton τ))
  have hmU1 : ν {ω | U ω = 1} = (2 : ℝ≥0∞) * q := by
    have hset : {ω : Ω' | U ω = 1}
        = {ω | U ω = 1 ∧ W ω = 1} ∪ {ω | U ω = 1 ∧ W ω = -1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hu
        rcases hW ω with h | h
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr ⟨hu, h⟩
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    have hdisj : Disjoint {ω | U ω = 1 ∧ W ω = 1} {ω | U ω = 1 ∧ W ω = -1} :=
      Set.disjoint_left.mpr fun x hx1 hx2 =>
        absurd (Set.mem_setOf_eq.mp hx1).2 (by rw [(Set.mem_setOf_eq.mp hx2).2]; norm_num)
    rw [hset, measure_union hdisj (hcellmeas 1 (-1)),
      hcells 1 hm1 1 hm1, hcells 1 hm1 (-1) hm2, ← two_mul]
  have hmUm : ν {ω | U ω = -1} = (2 : ℝ≥0∞) * q := by
    have hset : {ω : Ω' | U ω = -1}
        = {ω | U ω = -1 ∧ W ω = 1} ∪ {ω | U ω = -1 ∧ W ω = -1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hu
        rcases hW ω with h | h
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr ⟨hu, h⟩
      · rintro (⟨hu, _⟩ | ⟨hu, _⟩) <;> exact hu
    have hdisj : Disjoint {ω | U ω = -1 ∧ W ω = 1} {ω | U ω = -1 ∧ W ω = -1} :=
      Set.disjoint_left.mpr fun x hx1 hx2 =>
        absurd (Set.mem_setOf_eq.mp hx1).2 (by rw [(Set.mem_setOf_eq.mp hx2).2]; norm_num)
    rw [hset, measure_union hdisj (hcellmeas (-1) (-1)),
      hcells (-1) hm2 1 hm1, hcells (-1) hm2 (-1) hm2, ← two_mul]
  have hmW1 : ν {ω | W ω = 1} = (2 : ℝ≥0∞) * q := by
    have hset : {ω : Ω' | W ω = 1}
        = {ω | U ω = 1 ∧ W ω = 1} ∪ {ω | U ω = -1 ∧ W ω = 1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hw
        rcases hU ω with h | h
        · exact Or.inl ⟨h, hw⟩
        · exact Or.inr ⟨h, hw⟩
      · rintro (⟨_, hw⟩ | ⟨_, hw⟩) <;> exact hw
    have hdisj : Disjoint {ω | U ω = 1 ∧ W ω = 1} {ω | U ω = -1 ∧ W ω = 1} :=
      Set.disjoint_left.mpr fun x hx1 hx2 =>
        absurd (Set.mem_setOf_eq.mp hx1).1 (by rw [(Set.mem_setOf_eq.mp hx2).1]; norm_num)
    rw [hset, measure_union hdisj (hcellmeas (-1) 1),
      hcells 1 hm1 1 hm1, hcells (-1) hm2 1 hm1, ← two_mul]
  have hmWm : ν {ω | W ω = -1} = (2 : ℝ≥0∞) * q := by
    have hset : {ω : Ω' | W ω = -1}
        = {ω | U ω = 1 ∧ W ω = -1} ∪ {ω | U ω = -1 ∧ W ω = -1} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_union]
      constructor
      · intro hw
        rcases hU ω with h | h
        · exact Or.inl ⟨h, hw⟩
        · exact Or.inr ⟨h, hw⟩
      · rintro (⟨_, hw⟩ | ⟨_, hw⟩) <;> exact hw
    have hdisj : Disjoint {ω | U ω = 1 ∧ W ω = -1} {ω | U ω = -1 ∧ W ω = -1} :=
      Set.disjoint_left.mpr fun x hx1 hx2 =>
        absurd (Set.mem_setOf_eq.mp hx1).1 (by rw [(Set.mem_setOf_eq.mp hx2).1]; norm_num)
    rw [hset, measure_union hdisj (hcellmeas (-1) (-1)),
      hcells 1 hm1 (-1) hm2, hcells (-1) hm2 (-1) hm2, ← two_mul]
  -- the joint intersections as cells
  have hint : ∀ σ τ : ℝ,
      {ω : Ω' | U ω = σ} ∩ {ω | W ω = τ} = {ω | U ω = σ ∧ W ω = τ} := fun _ _ => rfl
  have hunivsplit : (1 : ℝ≥0∞) = (2 : ℝ≥0∞) * q + (2 : ℝ≥0∞) * q := h4q.symm
  intro s t hs ht
  by_cases h1 : (1 : ℝ) ∈ s
  · by_cases h2 : (-1 : ℝ) ∈ s
    · by_cases h3 : (1 : ℝ) ∈ t
      · by_cases h4 : (-1 : ℝ) ∈ t
        · rw [hUfull s h1 h2, hWfull t h3 h4, Set.univ_inter, measure_univ]
          norm_num
        · rw [hUfull s h1 h2, hWone t h3 h4, Set.univ_inter, measure_univ, hmW1,
            one_mul]
      · by_cases h4 : (-1 : ℝ) ∈ t
        · rw [hUfull s h1 h2, hWminus t h3 h4, Set.univ_inter, measure_univ, hmWm,
            one_mul]
        · rw [hUfull s h1 h2, hWempty t h3 h4, Set.univ_inter, measure_empty,
            measure_univ, mul_zero]
    · by_cases h3 : (1 : ℝ) ∈ t
      · by_cases h4 : (-1 : ℝ) ∈ t
        · rw [hUone s h1 h2, hWfull t h3 h4, Set.inter_univ, hmU1, measure_univ,
            mul_one]
        · rw [hUone s h1 h2, hWone t h3 h4, hint 1 1, hcells 1 hm1 1 hm1, hmU1,
            hmW1, hq2]
      · by_cases h4 : (-1 : ℝ) ∈ t
        · rw [hUone s h1 h2, hWminus t h3 h4, hint 1 (-1), hcells 1 hm1 (-1) hm2,
            hmU1, hmWm, hq2]
        · rw [hUone s h1 h2, hWempty t h3 h4, Set.inter_empty, measure_empty, hmU1,
            mul_zero]
  · by_cases h2 : (-1 : ℝ) ∈ s
    · by_cases h3 : (1 : ℝ) ∈ t
      · by_cases h4 : (-1 : ℝ) ∈ t
        · rw [hUminus s h1 h2, hWfull t h3 h4, Set.inter_univ, hmUm, measure_univ,
            mul_one]
        · rw [hUminus s h1 h2, hWone t h3 h4, hint (-1) 1, hcells (-1) hm2 1 hm1,
            hmUm, hmW1, hq2]
      · by_cases h4 : (-1 : ℝ) ∈ t
        · rw [hUminus s h1 h2, hWminus t h3 h4, hint (-1) (-1),
            hcells (-1) hm2 (-1) hm2, hmUm, hmWm, hq2]
        · rw [hUminus s h1 h2, hWempty t h3 h4, Set.inter_empty, measure_empty,
            hmUm, mul_zero]
    · by_cases h3 : (1 : ℝ) ∈ t
      · by_cases h4 : (-1 : ℝ) ∈ t
        · rw [hUempty s h1 h2, Set.empty_inter, measure_empty, zero_mul]
        · rw [hUempty s h1 h2, Set.empty_inter, measure_empty, zero_mul]
      · by_cases h4 : (-1 : ℝ) ∈ t
        · rw [hUempty s h1 h2, Set.empty_inter, measure_empty, zero_mul]
        · rw [hUempty s h1 h2, Set.empty_inter, measure_empty, zero_mul]

theorem walsh_indepFun_core {v w : Fin 4 → Bool} (i : Fin 4)
    (hvi : v i = true) (hwi : w i = false) (hw : w ≠ allF) :
    IndepFun (walsh v) (walsh w) wμ := by
  obtain ⟨j, hj⟩ := coin_exists w hw
  obtain ⟨q, hq, hcells⟩ := wcell_common_mass (v := v) (w := w)
    (u₁ := flipAt i) (u₂ := flipAt j)
    (walsh_flipAt_neg v i hvi) (walsh_flipAt_one w i hwi) (walsh_flipAt_neg w j hj)
  exact indepFun_sign_fibers wμ (walsh_measurable v) (walsh_measurable w)
    (walsh_dichotomy v) (walsh_dichotomy w) hq hcells

theorem walsh_indepFun {v w : Fin 4 → Bool} (hv : v ≠ allF) (hw : w ≠ allF)
    (hvw : v ≠ w) :
    IndepFun (walsh v) (walsh w) wμ := by
  by_cases hex : ∃ i, v i = true ∧ w i = false
  · obtain ⟨i, hvi, hwi⟩ := hex
    exact walsh_indepFun_core i hvi hwi hw
  · push_neg at hex
    obtain ⟨j, hwj, hvj⟩ : ∃ j, w j = true ∧ v j = false := by
      by_contra hcon
      push_neg at hcon
      refine hvw (funext fun k => ?_)
      cases hwk : w k with
      | true =>
          have hvk : v k = true := Bool.not_eq_false (v k) |>.mp (hcon k hwk)
          simp [hwk, hvk]
      | false =>
          cases hvk : v k with
          | false => simp [hwk, hvk]
          | true => exact absurd (hex k hvk) (by rw [hwk]; simp)
    exact (walsh_indepFun_core (v := w) (w := v) j hwj hvj hv).symm

/-! ### The fifteen nontrivial characters -/

def nzEnum : Fin 15 → (Fin 4 → Bool) :=
  ![
    ![true, false, false, false],
    ![false, true, false, false],
    ![false, false, true, false],
    ![false, false, false, true],
    ![true, true, false, false],
    ![true, false, true, false],
    ![true, false, false, true],
    ![false, true, true, false],
    ![false, true, false, true],
    ![false, false, true, true],
    ![true, true, true, false],
    ![true, true, false, true],
    ![true, false, true, true],
    ![false, true, true, true],
    ![true, true, true, true]]

theorem nzEnum_inj : Function.Injective nzEnum := by decide

theorem nzEnum_ne_allF : ∀ i, nzEnum i ≠ allF := by decide

theorem nzEnum_mem {v : Fin 4 → Bool} (hv : v ≠ allF) : ∃ i, nzEnum i = v := by
  have hfilter : v ∈ (Finset.univ : Finset (Fin 4 → Bool)).filter (fun v => v ≠ allF) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩
  have hsub : Finset.image nzEnum Finset.univ
      ⊆ (Finset.univ : Finset (Fin 4 → Bool)).filter (fun v => v ≠ allF) := by
    intro v hv'
    simp only [Finset.mem_image] at hv'
    obtain ⟨i, -, rfl⟩ := hv'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, nzEnum_ne_allF i⟩
  have hcardI : (Finset.image nzEnum Finset.univ).card = 15 := by
    rw [Finset.card_image_of_injective _ nzEnum_inj, Finset.card_univ, Fintype.card_fin]
  have hcardF : ((Finset.univ : Finset (Fin 4 → Bool)).filter
      (fun v => v ≠ allF)).card = 15 := by
    have hset : (Finset.univ : Finset (Fin 4 → Bool)).filter (fun v => v ≠ allF)
        = Finset.univ \ {allF} := by
      ext v
      simp [Set.mem_singleton_iff]
    rw [hset, Finset.card_sdiff (by simp),
      Finset.card_univ,
      show Fintype.card (Fin 4 → Bool) = 16 from by
        rw [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
          Fintype.card_bool]
        norm_num,
      Finset.card_singleton]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcardI, hcardF])
  rw [← heq] at hfilter
  obtain ⟨i, -, hvi⟩ := Finset.mem_image.mp hfilter
  exact ⟨i, hvi⟩

theorem nzEnum_image : (Finset.univ : Finset (Fin 4 → Bool)).filter (fun v => v ≠ allF)
    = Finset.image nzEnum Finset.univ := by
  ext v
  constructor
  · intro hv
    obtain ⟨-, hv2⟩ := Finset.mem_filter.mp hv
    obtain ⟨i, rfl⟩ := nzEnum_mem hv2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  · intro hv
    obtain ⟨i, -, hvi⟩ := Finset.mem_image.mp hv
    rw [← hvi]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, nzEnum_ne_allF i⟩

def wFam (i : Fin 15) : (Fin 4 → Bool) → ℝ := walsh (nzEnum i)

theorem wFam_sum (ω : Fin 4 → Bool) :
    ∑ i : Fin 15, wFam i ω = if ω = allF then 15 else -1 := by
  have h1 : ∑ i : Fin 15, wFam i ω
      = ∑ v ∈ (Finset.univ : Finset (Fin 4 → Bool)).filter (fun v => v ≠ allF),
          walsh v ω := by
    simp only [wFam]
    rw [nzEnum_image, Finset.sum_image (fun a _ b _ h => nzEnum_inj h)]
  rw [h1]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Fin 4 → Bool)) (fun v => v ≠ allF) (fun v => walsh v ω)
  have htriv : ∑ v ∈ (Finset.univ : Finset (Fin 4 → Bool)).filter
        (fun v => ¬(v ≠ allF)), walsh v ω = 1 := by
    have hsub : (Finset.univ : Finset (Fin 4 → Bool)).filter (fun v => ¬(v ≠ allF))
        ⊆ {allF} := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ] at hv
      simp only [Finset.mem_singleton]
      exact not_ne_iff.mp hv.2
    rw [Finset.sum_subset hsub (fun v hv hout => by
        obtain rfl := Finset.mem_singleton.mp hv
        exact absurd (Finset.mem_filter.mpr
          ⟨Finset.mem_univ allF, not_ne_iff.mpr rfl⟩) hout),
      Finset.sum_singleton, walsh_triv_char]
  rw [htriv] at hsplit
  by_cases hω : ω = allF
  · rw [if_pos hω, hω]
    rw [hω, walsh_total_sum_allF] at hsplit
    linarith
  · rw [if_neg hω]
    rw [walsh_total_sum_of_ne ω hω] at hsplit
    linarith

/-! ### The hypothesis-form refutations -/

theorem ofReal_le_refl {p q : ℝ} (_hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : ENNReal.ofReal p ≤ ENNReal.ofReal q) : p ≤ q := by
  by_contra hlt
  push_neg at hlt
  have hsplit : ENNReal.ofReal p = ENNReal.ofReal q + ENNReal.ofReal (p - q) := by
    rw [← ENNReal.ofReal_add hq (by linarith)]
    ring_nf
  have hpos : ENNReal.ofReal (p - q) ≠ 0 := by
    intro h0
    have hle := ENNReal.ofReal_eq_zero.mp h0
    linarith
  refine h.not_lt ?_
  rw [hsplit]
  exact ENNReal.lt_add_right (ne_of_lt ENNReal.ofReal_lt_top) hpos


theorem wμ_event_ge {S : Set (Fin 4 → Bool)} (hmem : allF ∈ S) :
    ENNReal.ofReal ((1 : ℝ) / 16) ≤ wμ S := by
  rw [← wμ_singleton]
  exact measure_mono (Set.singleton_subset_iff.mpr hmem)

theorem wFam_mem : allF ∈ {ω : Fin 4 → Bool | |∑ i : Fin 15, wFam i ω| ≥ 15} := by
  have hsum := wFam_sum allF
  rw [if_pos rfl] at hsum
  simp only [Set.mem_setOf_eq, hsum]
  norm_num

theorem wFam_meas : ∀ i, Measurable (wFam i) := fun _ => walsh_measurable _

theorem wFam_bound : ∀ i ω, |wFam i ω| ≤ 1 := by
  intro i ω
  rcases walsh_dichotomy (nzEnum i) ω with hc | hc <;>
    simp [wFam, hc]

theorem wFam_mean : ∀ i, ∫ ω : Fin 4 → Bool, wFam i ω ∂wμ = 0 :=
  fun i => walsh_mean_zero _ (nzEnum_ne_allF i)

theorem wFam_pairwise : ∀ i j, i ≠ j → IndepFun (wFam i) (wFam j) wμ :=
  fun i j hij => walsh_indepFun (nzEnum_ne_allF i) (nzEnum_ne_allF j)
    (fun h => hij (nzEnum_inj h))

theorem old_hoeffding_inequality_pairwise_refuted_QA
    (h : wμ {ω : Fin 4 → Bool | |∑ i : Fin 15, wFam i ω| ≥ 15}
      ≤ ENNReal.ofReal (2 * Real.exp (-(15 : ℝ) ^ 2 / (2 * 15)))) : False := by
  have hmono := wμ_event_ge wFam_mem
  have hcontra := hmono.trans h
  have hreal := ofReal_le_refl (by norm_num) (by positivity) hcontra
  have hnum := exp_bound_75 2 (Or.inr rfl)
  have hexp : -(15 : ℝ) ^ 2 / (2 * 15) = -(15 / 2) := by norm_num
  rw [hexp] at hreal
  linarith

theorem walsh_integrable (v : Fin 4 → Bool) : Integrable (walsh v) wμ :=
  Integrable.of_finite

theorem integral_one_wμ : ∫ _ω : Fin 4 → Bool, (1 : ℝ) ∂wμ = 1 := by
  rw [integral_const, measure_univ]
  simp

theorem walsh_sq_integral (v : Fin 4 → Bool) :
    ∫ ω : Fin 4 → Bool, (walsh v ω) ^ 2 ∂wμ = 1 := by
  have h2 : (fun ω : Fin 4 → Bool => (walsh v ω) ^ 2) = fun _ => (1 : ℝ) :=
    funext fun ω => by rw [sq]; exact walsh_sq v ω
  rw [h2, integral_one_wμ]

theorem wFam_var : ∑ i : Fin 15, ∫ ω : Fin 4 → Bool, (wFam i ω) ^ 2 ∂wμ = 15 := by
  have hper : ∀ i : Fin 15, ∫ ω : Fin 4 → Bool, (wFam i ω) ^ 2 ∂wμ = 1 :=
    fun i => walsh_sq_integral _
  rw [Finset.sum_congr rfl (fun i _ => hper i), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  norm_num

theorem old_bernstein_inequality_pairwise_refuted_QA
    (h : wμ {ω : Fin 4 → Bool | |∑ i : Fin 15, (wFam i ω - ∫ ω', wFam i ω' ∂wμ)| ≥ 15}
      ≤ ENNReal.ofReal (2 * Real.exp (-(15 : ℝ) ^ 2 /
        (2 * ∑ i : Fin 15, ∫ ω, (wFam i ω - ∫ ω', wFam i ω' ∂wμ) ^ 2 ∂wμ
          + (2 * 1 * 15) / 3)))) : False := by
  have hmean : ∀ i : Fin 15, ∫ ω', wFam i ω' ∂wμ = 0 := wFam_mean
  simp only [hmean, sub_zero] at h
  rw [wFam_var] at h
  have hmono := wμ_event_ge wFam_mem
  have hcontra := hmono.trans h
  have hreal := ofReal_le_refl (by norm_num) (by positivity) hcontra
  have hnum := exp_bound_5625 2 (Or.inr rfl)
  have hexp : -(15 : ℝ) ^ 2 / (2 * 15 + (2 * 1 * 15) / 3) = -(45 / 8) := by norm_num
  rw [hexp] at hreal
  linarith

theorem old_bernstein_bounded_variance_pairwise_refuted_QA
    (h : wμ {ω : Fin 4 → Bool | |∑ i : Fin 15, (wFam i ω - ∫ ω', wFam i ω' ∂wμ)| ≥ 15}
      ≤ ENNReal.ofReal (2 * Real.exp (-(15 : ℝ) ^ 2 /
        (2 * 15 + (2 * 1 * 15) / 3)))) : False := by
  have hmean : ∀ i : Fin 15, ∫ ω', wFam i ω' ∂wμ = 0 := wFam_mean
  simp only [hmean, sub_zero] at h
  have hmono := wμ_event_ge wFam_mem
  have hcontra := hmono.trans h
  have hreal := ofReal_le_refl (by norm_num) (by positivity) hcontra
  have hnum := exp_bound_5625 2 (Or.inr rfl)
  have hexp : -(15 : ℝ) ^ 2 / (2 * 15 + (2 * 1 * 15) / 3) = -(45 / 8) := by norm_num
  rw [hexp] at hreal
  linarith

/-- The `[0,1]`-valued affine image of a character. -/
noncomputable def wYFam (i : Fin 15) : (Fin 4 → Bool) → ℝ := fun ω => (wFam i ω + 1) / 2

theorem wYFam_bound : ∀ i ω, 0 ≤ wYFam i ω ∧ wYFam i ω ≤ 1 := by
  intro i ω
  rcases walsh_dichotomy (nzEnum i) ω with hc | hc <;>
    simp [wYFam, wFam, hc]

theorem wYFam_measurable : ∀ i, Measurable (wYFam i) :=
  fun _ => ((walsh_measurable _).add measurable_const).div measurable_const

theorem wYFam_pairwise : ∀ i j, i ≠ j → IndepFun (wYFam i) (wYFam j) wμ := by
  intro i j hij
  have hdecomp : IndepFun ((fun x : ℝ => (x + 1) / 2) ∘ wFam i)
      ((fun x : ℝ => (x + 1) / 2) ∘ wFam j) wμ :=
    (wFam_pairwise i j hij).comp (by fun_prop) (by fun_prop)
  exact hdecomp

theorem wYFam_apply (i : Fin 15) (ω : Fin 4 → Bool) :
    wYFam i ω = (wFam i ω + 1) / 2 := rfl

theorem wYFam_mean (i : Fin 15) : ∫ ω, wYFam i ω ∂wμ = 1 / 2 := by
  have hint : Integrable (wFam i) wμ := walsh_integrable _
  have hfun : (fun ω => wYFam i ω) = fun ω => (wFam i ω + 1) / 2 :=
    funext fun ω => wYFam_apply i ω
  rw [hfun, integral_div, integral_add hint (integrable_const _),
    wFam_mean i, integral_one_wμ]
  norm_num

theorem wYFam_sum (ω : Fin 4 → Bool) :
    ∑ i : Fin 15, wYFam i ω = if ω = allF then 15 else 7 := by
  have key : ∑ i : Fin 15, wYFam i ω = (∑ i : Fin 15, wFam i ω + 15) / 2 := by
    simp only [wYFam_apply]
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    ring
  rw [key]
  have h2 := wFam_sum ω
  rcases eq_or_ne ω allF with hω | hω
  · rw [hω, if_pos rfl]
    rw [hω] at h2
    rw [if_pos rfl] at h2
    rw [h2]
    norm_num
  · rw [if_neg hω, h2, if_neg hω]
    norm_num

theorem old_hoeffding_empirical_pairwise_refuted_QA
    (h : wμ {ω : Fin 4 → Bool | |(1 / (15 : ℝ)) * ∑ i : Fin 15, wYFam i ω
          - (1 / (15 : ℝ)) * ∑ i : Fin 15, ∫ ω', wYFam i ω' ∂wμ| ≥ 1 / 2}
      ≤ ENNReal.ofReal (2 * Real.exp (-2 * (15 : ℝ) * (1 / 2) ^ 2))) : False := by
  have hmean : ∀ i : Fin 15, ∫ ω', wYFam i ω' ∂wμ = 1 / 2 := wYFam_mean
  have hsumint : ∑ i : Fin 15, ∫ ω', wYFam i ω' ∂wμ = 15 / 2 := by
    rw [Finset.sum_congr rfl (fun i _ => hmean i)]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    field_simp
  have hval : (1 / (15 : ℝ)) * ∑ i : Fin 15, wYFam i allF
      - (1 / (15 : ℝ)) * ∑ i : Fin 15, ∫ ω', wYFam i ω' ∂wμ = 1 / 2 := by
    have hsum := wYFam_sum allF
    rw [if_pos rfl] at hsum
    rw [hsum, hsumint]
    norm_num
  have hmem : allF ∈ {ω : Fin 4 → Bool | |(1 / (15 : ℝ)) * ∑ i : Fin 15, wYFam i ω
      - (1 / (15 : ℝ)) * ∑ i : Fin 15, ∫ ω', wYFam i ω' ∂wμ| ≥ 1 / 2} := by
    show |(1 / (15 : ℝ)) * ∑ i : Fin 15, wYFam i allF
      - (1 / (15 : ℝ)) * ∑ i : Fin 15, ∫ ω', wYFam i ω' ∂wμ| ≥ 1 / 2
    rw [hval]
    exact le_abs_self (1 / 2)
  have hmono := wμ_event_ge hmem
  have hcontra := hmono.trans h
  have hreal := ofReal_le_refl (by norm_num) (by positivity) hcontra
  have hnum := exp_bound_75 2 (Or.inr rfl)
  have hexp : -2 * (15 : ℝ) * (1 / 2) ^ 2 = -(15 / 2) := by norm_num
  rw [hexp] at hreal
  linarith

/-! ### The matrix pair: the rank-one lift -/

def wE : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then 1 else 0

theorem wE_conj : wEᴴ = wE := by
  ext i j
  simp [wE, Matrix.conjTranspose, Matrix.transpose_apply, and_comm]

theorem wE_symm : wE.IsSymm := by
  show wEᵀ = wE
  ext i j
  simp [wE, Matrix.transpose_apply, and_comm]

theorem wE_herm : wE.IsHermitian := SpectralGraphTheory.isHermitian_of_isSymm wE_symm

theorem wE_mul : wE * wE = wE := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wE, Matrix.mul_apply, Fin.sum_univ_two]

theorem wE_norm : ‖wE‖ = 1 := by
  have hc := Matrix.l2_opNorm_conjTranspose_mul_self wE
  rw [wE_conj, wE_mul] at hc
  have hnn : 0 ≤ ‖wE‖ := norm_nonneg _
  rcases eq_or_lt_of_le hnn with h0 | h0
  · exfalso
    have hle : ‖wE‖ ≤ 0 := by rw [h0]
    have hz : wE = 0 := (norm_le_zero_iff).mp hle
    have h00 : wE 0 0 = 1 := by simp [wE]
    rw [hz] at h00
    simp at h00
  · nlinarith

def wXFam (i : Fin 15) : (Fin 4 → Bool) → Matrix (Fin 2) (Fin 2) ℝ :=
  fun ω => wFam i ω • wE

theorem wXFam_apply (i : Fin 15) (ω : Fin 4 → Bool) :
    wXFam i ω = wFam i ω • wE := rfl

theorem wXFam_herm (i : Fin 15) (ω : Fin 4 → Bool) : (wXFam i ω).IsHermitian := by
  show (wFam i ω • wE)ᴴ = wFam i ω • wE
  rw [Matrix.conjTranspose_smul, wE_conj]
  rfl

theorem wXFam_meas (i : Fin 15) : StronglyMeasurable (wXFam i) :=
  ((wFam_meas i).stronglyMeasurable).smul stronglyMeasurable_const

theorem wXFam_mean (i : Fin 15) : ∫ ω : Fin 4 → Bool, wXFam i ω ∂wμ = 0 := by
  show ∫ ω : Fin 4 → Bool, wFam i ω • wE ∂wμ = 0
  rw [integral_smul_const, wFam_mean i, zero_smul]

theorem wXFam_sq (i : Fin 15) (ω : Fin 4 → Bool) : wXFam i ω * wXFam i ω = wE := by
  show (wFam i ω • wE) * (wFam i ω • wE) = wE
  rw [smul_mul_assoc, Matrix.mul_smul, smul_smul,
    show wFam i ω * wFam i ω = 1 from walsh_sq (nzEnum i) ω, one_smul, wE_mul]

theorem wXFam_psd (i : Fin 15) (ω : Fin 4 → Bool) :
    Matrix.PosSemidef (wE * wE - wXFam i ω * wXFam i ω) := by
  rw [wE_mul, wXFam_sq, sub_self]
  exact Matrix.PosSemidef.zero

theorem wXFam_norm (i : Fin 15) (ω : Fin 4 → Bool) : ‖wXFam i ω‖ ≤ 1 := by
  rw [wXFam_apply, norm_smul, wE_norm, Real.norm_eq_abs, mul_one]
  exact wFam_bound i ω

theorem wXFam_sum_norm (ω : Fin 4 → Bool) :
    ‖∑ i : Fin 15, wXFam i ω‖ = |∑ i : Fin 15, wFam i ω| := by
  have hsum : ∑ i : Fin 15, wXFam i ω = (∑ i : Fin 15, wFam i ω) • wE := by
    show ∑ i : Fin 15, wFam i ω • wE = (∑ i : Fin 15, wFam i ω) • wE
    exact (Finset.sum_smul : (∑ i : Fin 15, wFam i ω) • wE
      = ∑ i : Fin 15, wFam i ω • wE).symm
  rw [hsum, norm_smul, wE_norm, mul_one, Real.norm_eq_abs]

theorem wXmem : allF ∈ {ω : Fin 4 → Bool | ‖∑ i : Fin 15, wXFam i ω‖ ≥ 15} := by
  have hsum := wFam_sum allF
  rw [if_pos rfl] at hsum
  simp only [Set.mem_setOf_eq, wXFam_sum_norm, hsum]
  norm_num

theorem wXvar : ∑ i : Fin 15, ∫ ω : Fin 4 → Bool, wXFam i ω * wXFam i ω ∂wμ
    = (15 : ℝ) • wE := by
  have hper : ∀ i : Fin 15,
      ∫ ω : Fin 4 → Bool, wXFam i ω * wXFam i ω ∂wμ = wE := by
    intro i
    have hfun : (fun ω => wXFam i ω * wXFam i ω) = fun _ => wE :=
      funext fun ω => wXFam_sq i ω
    rw [hfun, integral_const, measure_univ]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hper i),
    show ((15 : ℝ)) = ∑ i : Fin 15, (1 : ℝ) from by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin],
    Finset.sum_smul]
  simp

theorem old_matrix_hoeffding_pairwise_refuted_QA
    (h : wμ {ω : Fin 4 → Bool | ‖∑ i : Fin 15, wXFam i ω‖ ≥ 15}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 2) : ℝ) *
        Real.exp (-(15 : ℝ) ^ 2 / (2 * ‖∑ _i : Fin 15, wE * wE‖)))) : False := by
  have hvar : ∑ i : Fin 15, wE * wE = (15 : ℝ) • wE := by
    rw [wE_mul,
      show ((15 : ℝ)) = ∑ i : Fin 15, (1 : ℝ) from by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin],
      Finset.sum_smul]
    simp
  have hn : ‖∑ i : Fin 15, wE * wE‖ = 15 := by
    rw [hvar, norm_smul, wE_norm, Real.norm_eq_abs, mul_one]
    norm_num
  rw [hn] at h
  have hmono := wμ_event_ge wXmem
  have hcontra := hmono.trans h
  have hreal := ofReal_le_refl (by norm_num) (by positivity) hcontra
  have hnum := exp_bound_75 4 (Or.inl rfl)
  have hexp : -(15 : ℝ) ^ 2 / (2 * 15) = -(15 / 2) := by norm_num
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  rw [hexp, hcard] at hreal
  linarith

theorem old_matrix_bernstein_pairwise_refuted_QA
    (h : wμ {ω : Fin 4 → Bool | ‖∑ i : Fin 15, wXFam i ω‖ ≥ 15}
      ≤ ENNReal.ofReal (2 * (Fintype.card (Fin 2) : ℝ) *
        Real.exp (-(15 : ℝ) ^ 2 /
          (2 * ‖∑ i : Fin 15, ∫ ω : Fin 4 → Bool, wXFam i ω * wXFam i ω ∂wμ‖
            + (2 * 1 * 15) / 3)))) : False := by
  have hn : ‖∑ i : Fin 15, ∫ ω : Fin 4 → Bool, wXFam i ω * wXFam i ω ∂wμ‖ = 15 := by
    rw [wXvar, norm_smul, wE_norm, Real.norm_eq_abs, mul_one]
    norm_num
  rw [hn] at h
  have hmono := wμ_event_ge wXmem
  have hcontra := hmono.trans h
  have hreal := ofReal_le_refl (by norm_num) (by positivity) hcontra
  have hnum := exp_bound_5625 4 (Or.inl rfl)
  have hexp : -(15 : ℝ) ^ 2 / (2 * 15 + (2 * 1 * 15) / 3) = -(45 / 8) := by norm_num
  have hcard : (Fintype.card (Fin 2) : ℝ) = 2 := by simp
  rw [hexp, hcard] at hreal
  linarith


end Scaffold.QA.Concentration.PairwiseIndependence
