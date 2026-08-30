/-\
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
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Integration
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding

/-!
# Bernstein's inequality

Bernstein's tail bound for sums of bounded independent real random
variables with a variance-dependent denominator, stated over an arbitrary
probability measure with Mathlib's `ProbabilityTheory.iIndepFun`.

**Retired from axiom to proved theorem 2026-08-30** by a local Bennett
MGF engine (`bennettQ`, `bennett_mgf`, `mgf_sum_le_bernstein` below):
Bennett's ratio representation, the series bound
`q(v) ≤ 1/(2(1 − v/3))` on `(0, 3)`, the per-variable MGF bound
`E e^{λY} ≤ exp (λ²σ²/(2(1 − λa/3)))`, and the Chernoff assembly at
`λ = t/(V + at/3)` (whose exponent closes at exactly
`−t²/(2V + 2at/3)`), reusing the proved Hoeffding-retirement machinery
`integral_prod_exp_of_iIndepFun` and `markov_tail_of_mgf`.

The retirement is also a **repair** (Errata §8): the admitted statements
hypothesized the *uncentered* bound `|X i ω| ≤ a` while centering
internally, but the cited sources bound the *mean-zero* variables — the
centered variable satisfies only `|X − EX| ≤ 2a`, so the `2at/3` linear
term underpriced the Bennett bound by up to a factor 2. Both statements
now carry the source-faithful centered hypothesis; see the Errata entry
and `proposals/repair-and-retire-bernstein-pair.md` for the refutation
witness and the numerical large-deviation evidence.

`bernstein_iid` remains a derived corollary, not an axiom.
-/

open MeasureTheory ProbabilityTheory Real

namespace Scaffold.Mathlib.Probability.Concentration.Scalar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Integrability safety for the variance statistics in
`bernstein_inequality` and `bernstein_bounded_variance`: on a
probability measure, a measurable uniformly bounded variable has its
centered square integrable, so the variance integrals appearing in both
axioms' conclusions (and the `h_var` clause of the budget form) are
honest — none of them can be the junk `0` of
`MeasureTheory.integral_undef`.

Recorded by the integrability audit of 2026-08-28
(`proposals/audit-scalar-concentration-integrability-hazard.md`, Step
0). QA: `integrable_sq_sub_mean_rademacher_QA` in
`Scaffold/QA/Concentration/Scalar_QA.lean`.
-/
theorem integrable_sq_sub_mean {X : Ω → ℝ} {a : ℝ}
    (h_meas : Measurable X) (h_bound : ∀ ω, |X ω| ≤ a) :
    Integrable (fun ω => (X ω - ∫ ω', X ω' ∂μ) ^ 2) μ := by
  set c : ℝ := ∫ ω', X ω' ∂μ with hc
  have hbdd : ∀ ω, |X ω - c| ≤ |a| + |c| := by
    intro ω
    have hX : |X ω| ≤ |a| := (h_bound ω).trans (le_abs_self a)
    calc |X ω - c| ≤ |X ω| + |c| := abs_sub _ _
      _ ≤ |a| + |c| := add_le_add hX le_rfl
  have hmsub : Measurable fun ω => X ω - c := h_meas.sub measurable_const
  have hm : Measurable fun ω => (X ω - c) ^ 2 := by
    have hmul : Measurable fun ω => (X ω - c) * (X ω - c) := hmsub.mul hmsub
    have heq : (fun ω => (X ω - c) ^ 2) = fun ω => (X ω - c) * (X ω - c) := by
      funext ω; rw [sq]
    rw [heq]; exact hmul
  refine Integrable.mono' (integrable_const ((|a| + |c|) ^ 2)) hm.aestronglyMeasurable ?_
  refine ae_of_all μ fun ω => ?_
  have h1 : |X ω - c| ^ 2 ≤ (|a| + |c|) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (hbdd ω) 2
  simpa [Real.norm_eq_abs, sq_abs] using h1

/-! ## The Bennett engine -/

/-- Bennett's ratio `q(u) = (e^u - 1 - u) / u²`. -/
noncomputable def bennettQ (u : ℝ) : ℝ := (Real.exp u - 1 - u) / u ^ 2

private theorem hasDerivAt_bennettAnti (u s : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun t => ((1 - t) / u + 1 / u ^ 2) * Real.exp (u * t))
      ((1 - s) * Real.exp (u * s)) s := by
  have hE : HasDerivAt (fun t => Real.exp (u * t)) (u * Real.exp (u * s)) s := by
    have h := (hasDerivAt_exp (𝕂 := ℝ) (x := u * s)).comp s
      ((hasDerivAt_id s).const_mul u : HasDerivAt (fun y : ℝ => u * y) (u * 1) s)
    simpa [Function.comp_def, mul_comm, Real.exp_eq_exp_ℝ] using h
  have hA : HasDerivAt (fun t => (1 - t) / u + 1 / u ^ 2) ((0 - 1) / u + 0) s := by
    have h1 : HasDerivAt (fun t => 1 - t) (0 - 1) s :=
      (hasDerivAt_const s (1:ℝ)).sub (hasDerivAt_id s)
    exact ((h1.div_const u).add (hasDerivAt_const s (1 / u ^ 2))).congr_deriv (by ring)
  exact (hA.mul hE).congr_deriv (by field_simp; ring)

/-- The integral representation `q(u) = ∫₀¹ (1 - s) e^{us} ds`. -/
theorem bennettQ_eq_integral {u : ℝ} (hu : u ≠ 0) :
    bennettQ u = ∫ s in (0:ℝ)..1, (1 - s) * Real.exp (u * s) := by
  have hcont : Continuous (fun s : ℝ => (1 - s) * Real.exp (u * s)) := by continuity
  have hint : IntervalIntegrable (fun s : ℝ => (1 - s) * Real.exp (u * s)) volume 0 1 :=
    Continuous.intervalIntegrable (μ := volume) hcont 0 1
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (f := fun s => ((1 - s) / u + 1 / u ^ 2) * Real.exp (u * s))
    (f' := fun s => (1 - s) * Real.exp (u * s)) (fun s _ => hasDerivAt_bennettAnti u s hu) hint
  rw [hFTC]
  simp only [bennettQ]
  have hu2 : u ^ 2 ≠ 0 := pow_ne_zero _ hu
  field_simp
  ring

/-- Monotonicity of Bennett's ratio on the whole line. -/
theorem bennettQ_le {u v : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≤ v) :
    bennettQ u ≤ bennettQ v := by
  rw [bennettQ_eq_integral hu, bennettQ_eq_integral hv]
  have hc1 : Continuous (fun s : ℝ => (1 - s) * Real.exp (u * s)) := by continuity
  have hc2 : Continuous (fun s : ℝ => (1 - s) * Real.exp (v * s)) := by continuity
  refine intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
    (Continuous.intervalIntegrable (μ := volume) hc1 0 1)
    (Continuous.intervalIntegrable (μ := volume) hc2 0 1) (fun s hs => ?_)
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right huv hs.1)) ?_
  linarith [hs.1, hs.2]

/-! ## The series bound -/

private theorem two_mul_three_pow_le_factorial (j : ℕ) : 2 * 3 ^ j ≤ Nat.factorial (j + 2) := by
  induction j with
  | zero => norm_num [Nat.factorial]
  | succ j ih =>
    have h3 : (3:ℕ) ≤ j + 3 := by omega
    have hlast : Nat.factorial (j + 3) = (j + 3) * Nat.factorial (j + 2) := by
      rw [show j + 3 = (j + 2) + 1 from by omega, Nat.factorial_succ]
    calc 2 * 3 ^ (j + 1) = 3 * (2 * 3 ^ j) := by ring
      _ ≤ 3 * Nat.factorial (j + 2) := Nat.mul_le_mul_left _ ih
      _ = Nat.factorial (j + 2) * 3 := Nat.mul_comm _ _
      _ ≤ Nat.factorial (j + 2) * (j + 3) := Nat.mul_le_mul_left _ h3
      _ = Nat.factorial (j + 1 + 2) := by
          rw [show j + 1 + 2 = j + 3 from by omega, hlast]
          exact (Nat.mul_comm _ _).symm

/-- The series representation of Bennett's ratio. -/
theorem hasSum_bennettQ {v : ℝ} (hv : 0 < v) :
    HasSum (fun j => v ^ j / Nat.factorial (j + 2)) (bennettQ v) := by
  have hexphas : HasSum (fun n => v ^ n / Nat.factorial n) (Real.exp v) := by
    simpa [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (𝕂 := ℝ) v
  have hshift : HasSum (fun n => v ^ (n + 2) / Nat.factorial (n + 2))
      (Real.exp v - ∑ i ∈ Finset.range 2, v ^ i / Nat.factorial i) :=
    (hasSum_nat_add_iff' (f := fun n => v ^ n / Nat.factorial n) 2).mpr hexphas
  have hsum2 : ∑ i ∈ Finset.range 2, v ^ i / Nat.factorial i = 1 + v := by
    simp only [Finset.sum_range_succ, Finset.sum_singleton]
    norm_num
  rw [hsum2] at hshift
  have hscaled := HasSum.mul_left ((v ^ 2)⁻¹) hshift
  have hfun : (fun n => (v ^ 2)⁻¹ * (v ^ (n + 2) / Nat.factorial (n + 2)))
      = fun j => v ^ j / Nat.factorial (j + 2) := by
    funext j
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    congr 1
    have hv0 : v ≠ 0 := ne_of_gt hv
    rw [pow_add]
    field_simp
  rw [hfun] at hscaled
  have hval : (v ^ 2)⁻¹ * (Real.exp v - (1 + v)) = bennettQ v := by
    unfold bennettQ
    field_simp
    ring
  rw [hval] at hscaled
  exact hscaled

/-- The series bound: `q(v) ≤ 1/(2(1 − v/3))` on `(0, 3)`. -/
theorem bennettQ_le_inv {v : ℝ} (hv : 0 < v) (hv3 : v < 3) :
    bennettQ v ≤ 1 / (2 * (1 - v / 3)) := by
  have h3 : (0:ℝ) < 3 := by norm_num
  have hv13 : v / 3 < 1 := by rw [div_lt_iff₀ h3]; linarith
  have hgeo := HasSum.mul_left ((1:ℝ) / 2)
    (hasSum_geometric_of_lt_one (div_nonneg hv.le h3.le) hv13)
  have hfun : (fun n => (1 / 2) * (v / 3) ^ n) = fun j => v ^ j / (2 * 3 ^ j) := by
    funext j
    rw [div_pow]
    field_simp
  rw [hfun] at hgeo
  refine le_trans (hasSum_le (fun j => ?_) (hasSum_bennettQ hv) hgeo) ?_
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hv.le j)
    have hfact : (2:ℝ) * 3 ^ j ≤ (Nat.factorial (j + 2) : ℝ) :=
      by exact_mod_cast two_mul_three_pow_le_factorial j
    have hpos1 : (0:ℝ) < 2 * 3 ^ j := by positivity
    have hpos2 : (0:ℝ) < (Nat.factorial (j + 2) : ℝ) := by positivity
    rw [inv_le_inv₀ hpos2 hpos1]
    exact hfact
  · have hpos : (0:ℝ) < 1 - v / 3 := by
      have : v / 3 < 1 := by
        rw [div_lt_iff₀ h3]
        linarith
      linarith
    field_simp

/-! ## The MGF engine -/

/-- The pointwise Bennett bound: for `y ≤ a` and `λ > 0`, `a > 0`,
`e^{λy} ≤ 1 + λy + y² · (e^{λa} − 1 − λa)/a²`. -/
theorem exp_le_add_sq_mul {y a lam : ℝ} (hpos : 0 < lam) (ha : 0 < a) (hya : y ≤ a) :
    Real.exp (lam * y) ≤ 1 + lam * y
      + y ^ 2 * ((Real.exp (lam * a) - 1 - lam * a) / a ^ 2) := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [mul_zero, Real.exp_zero]
    norm_num
  · have hA : 0 ≤ Real.exp (lam * y) - 1 - lam * y := by
      have h := Real.add_one_le_exp (lam * y)
      have h2 : lam * y + 1 = 1 + lam * y := by ring
      rw [h2] at h
      linarith
    have hB : 0 ≤ Real.exp (lam * a) - 1 - lam * a := by
      have h := Real.add_one_le_exp (lam * a)
      have h2 : lam * a + 1 = 1 + lam * a := by ring
      rw [h2] at h
      linarith
    have hne1 : lam * y ≠ 0 := mul_ne_zero (ne_of_gt hpos) hy0
    have hne2 : lam * a ≠ 0 := mul_ne_zero (ne_of_gt hpos) (ne_of_gt ha)
    have hmono : bennettQ (lam * y) ≤ bennettQ (lam * a) :=
      bennettQ_le hne1 hne2 (mul_le_mul_of_nonneg_left hya hpos.le)
    rw [bennettQ, bennettQ] at hmono
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hmono
    -- hmono : (e^{λy} − 1 − λy) * (λ a)² ≤ (e^{λa} − 1 − λa) * (λ y)²
    have hkey : (Real.exp (lam * y) - 1 - lam * y) * a ^ 2
        ≤ (Real.exp (lam * a) - 1 - lam * a) * y ^ 2 := by
      have hlamp : (0:ℝ) < lam ^ 2 := by positivity
      have hcancel : lam ^ 2 * ((Real.exp (lam * y) - 1 - lam * y) * a ^ 2)
          ≤ lam ^ 2 * ((Real.exp (lam * a) - 1 - lam * a) * y ^ 2) := by
        calc lam ^ 2 * ((Real.exp (lam * y) - 1 - lam * y) * a ^ 2)
            = (Real.exp (lam * y) - 1 - lam * y) * (lam * a) ^ 2 := by
              rw [mul_pow]; ring
          _ ≤ (Real.exp (lam * a) - 1 - lam * a) * (lam * y) ^ 2 := hmono
          _ = lam ^ 2 * ((Real.exp (lam * a) - 1 - lam * a) * y ^ 2) := by
              rw [mul_pow]; ring
      by_contra hcon
      have hlt : (Real.exp (lam * a) - 1 - lam * a) * y ^ 2 * lam ^ 2
          < (Real.exp (lam * y) - 1 - lam * y) * a ^ 2 * lam ^ 2 :=
        mul_lt_mul_of_pos_right (lt_of_not_le hcon) hlamp
      nlinarith [hlt]
    calc Real.exp (lam * y)
        = 1 + lam * y + (Real.exp (lam * y) - 1 - lam * y) := by ring
      _ ≤ 1 + lam * y + ((Real.exp (lam * a) - 1 - lam * a) * y ^ 2 / a ^ 2) := by
          refine add_le_add_left ?_ _
          exact (le_div_iff₀ (sq_pos_of_pos ha)).mpr hkey
      _ = 1 + lam * y + y ^ 2 * ((Real.exp (lam * a) - 1 - lam * a) / a ^ 2) := by ring

/-- Bennett's MGF bound: a centered, centered-bounded, measurable variable
satisfies `E exp(λY) ≤ exp(λ² σ² / (2(1 − λa/3)))` for `0 < λ`, `λa < 3`,
where `σ² = ∫ Y²`. -/
theorem bennett_mgf {Y : Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (h_meas : Measurable Y) (h_bound : ∀ ω, |Y ω| ≤ a) (h_mean : ∫ ω, Y ω ∂μ = 0)
    {lam : ℝ} (hlam : 0 < lam) (hla3 : lam * a < 3) :
    ∫ ω, Real.exp (lam * Y ω) ∂μ
      ≤ Real.exp (lam ^ 2 * (∫ ω, (Y ω) ^ 2 ∂μ) / (2 * (1 - lam * a / 3))) := by
  have hint : Integrable Y μ :=
    integrable_of_bounded_measurable (μ := μ) h_meas h_bound
  have hsq : Integrable (fun ω => (Y ω) ^ 2) μ := by
    have h := integrable_sq_sub_mean (μ := μ) h_meas h_bound
    have hfun : (fun ω => (Y ω - ∫ ω', Y ω' ∂μ) ^ 2) = fun ω => (Y ω) ^ 2 := by
      funext ω
      rw [h_mean, sub_zero]
    rwa [hfun] at h
  set c : ℝ := (Real.exp (lam * a) - 1 - lam * a) / a ^ 2 with hc
  have hcnum : 0 ≤ Real.exp (lam * a) - 1 - lam * a := by
    have h := Real.add_one_le_exp (lam * a)
    have h2 : lam * a + 1 = 1 + lam * a := by ring
    rw [h2] at h
    linarith
  -- integrability of the exponential
  have hintexp : Integrable (fun ω => Real.exp (lam * Y ω)) μ := by
    refine integrable_of_bounded_measurable
      (a := Real.exp (lam * a)) (Real.measurable_exp.comp ((h_meas).const_mul lam)) ?_
    intro ω
    have h1 : |Real.exp (lam * Y ω)| ≤ Real.exp (lam * a) := by
      rw [abs_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (abs_le.mp (h_bound ω) |>.2) hlam.le)
    simpa [Real.norm_eq_abs] using h1
  -- the pointwise bound and the monotone step
  have hptwise : ∀ ω, Real.exp (lam * Y ω) ≤ 1 + lam * Y ω + (Y ω) ^ 2 * c :=
    fun ω => exp_le_add_sq_mul hlam ha (abs_le.mp (h_bound ω) |>.2)
  have h2' : Integrable (fun ω : Ω => lam * Y ω) μ := by
    have h2 := hint.mul_const lam
    rwa [show (fun ω : Ω => Y ω * lam) = fun ω => lam * Y ω from
      funext fun ω => mul_comm _ _] at h2
  have hmajint : Integrable (fun ω => 1 + lam * Y ω + (Y ω) ^ 2 * c) μ := by
    exact ((integrable_const (1:ℝ)).add h2').add (hsq.mul_const c)
  have hstep : ∫ ω, Real.exp (lam * Y ω) ∂μ
      ≤ ∫ ω, (1 + lam * Y ω + (Y ω) ^ 2 * c) ∂μ :=
    integral_mono_of_nonneg (ae_of_all μ fun _ => (Real.exp_pos _).le) hmajint
      (ae_of_all μ hptwise)
  have i3 : ∫ ω, (Y ω) ^ 2 * c ∂μ = (∫ ω, (Y ω) ^ 2 ∂μ) * c :=
    integral_mul_right (f := fun ω => (Y ω) ^ 2) (μ := μ) c
  have i12 : ∫ ω, (1:ℝ) + lam * Y ω ∂μ = 1 := by
    have e2' : (∫ ω, (1:ℝ) + lam * Y ω ∂μ) = (∫ ω : Ω, (1:ℝ) ∂μ) + (∫ ω, lam * Y ω ∂μ) :=
      integral_add (integrable_const (1:ℝ)) h2'
    rw [e2', integral_mul_left, h_mean, mul_zero, integral_const]
    simp [measure_univ]
  have hintsplit : ∫ ω, (1 + lam * Y ω + (Y ω) ^ 2 * c) ∂μ
      = 1 + c * (∫ ω, (Y ω) ^ 2 ∂μ) := by
    have e1' : (∫ ω, (1 + lam * Y ω + (Y ω) ^ 2 * c) ∂μ)
        = (∫ ω, (1:ℝ) + lam * Y ω ∂μ) + (∫ ω, (Y ω) ^ 2 * c ∂μ) :=
      integral_add ((integrable_const (1:ℝ)).add h2') (hsq.mul_const c)
    rw [e1', i12, i3]
    ring
  rw [show ∫ ω, (1 + lam * Y ω + (Y ω) ^ 2 * c) ∂μ = 1 + c * (∫ ω, (Y ω) ^ 2 ∂μ) from
    hintsplit] at hstep
  -- the series bound closes c against the claimed exponent
  have hc3 : lam * a / 3 < 1 := by
    have h31 : lam * a < 3 * 1 := by linarith
    rw [div_lt_iff₀ (by norm_num : (0:ℝ) < 3)]
    linarith
  have hq : c ≤ lam ^ 2 / (2 * (1 - lam * a / 3)) := by
    have hbq : bennettQ (lam * a) ≤ 1 / (2 * (1 - lam * a / 3)) :=
      bennettQ_le_inv (mul_pos hlam ha) hla3
    have heq : c = lam ^ 2 * bennettQ (lam * a) := by
      rw [hc]
      unfold bennettQ
      field_simp
      ring
    rw [heq]
    have hrr : lam ^ 2 / (2 * (1 - lam * a / 3))
        = lam ^ 2 * (1 / (2 * (1 - lam * a / 3))) := by field_simp
    rw [hrr]
    exact mul_le_mul_of_nonneg_left hbq (sq_nonneg lam)
  have hfinal : 1 + c * (∫ ω, (Y ω) ^ 2 ∂μ)
      ≤ Real.exp (lam ^ 2 * (∫ ω, (Y ω) ^ 2 ∂μ) / (2 * (1 - lam * a / 3))) := by
    have hvar : 0 ≤ ∫ ω, (Y ω) ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg (Y ω))
    have hstep2 : c * (∫ ω, (Y ω) ^ 2 ∂μ)
        ≤ (lam ^ 2 / (2 * (1 - lam * a / 3))) * (∫ ω, (Y ω) ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_right hq hvar
    have hcomm0 : 1 + c * (∫ ω, (Y ω) ^ 2 ∂μ)
        = c * (∫ ω, (Y ω) ^ 2 ∂μ) + 1 := by ring
    rw [hcomm0]
    refine le_trans (add_le_add_right hstep2 1) ?_
    refine le_trans (Real.add_one_le_exp _) (le_of_eq ?_)
    ring
  calc ∫ ω, Real.exp (lam * Y ω) ∂μ
      ≤ 1 + c * (∫ ω, (Y ω) ^ 2 ∂μ) := hstep
    _ ≤ Real.exp (lam ^ 2 * (∫ ω, (Y ω) ^ 2 ∂μ) / (2 * (1 - lam * a / 3))) := hfinal

/-- The Chernoff exponent identity at `λ = t/(V + at/3)`, stated with `D`
an opaque stand-in for the denominator so every division is by an atom. -/
private theorem exponent_identity (V D t a lam : ℝ) (hDne : D ≠ 0) (hVne : V ≠ 0)
    (hlam : lam = t / D) (hfr : 1 - lam * a / 3 = V / D)
    (hdd : 2 * V + 2 * a * t / 3 = 2 * D) :
    -(lam * t) + lam ^ 2 * V / (2 * (1 - lam * a / 3))
      = -(t ^ 2) / (2 * V + (2 * a * t) / 3) := by
  rw [hfr, hdd]
  have h1 : lam ^ 2 * V / (2 * (V / D)) = lam ^ 2 * D / 2 := by
    field_simp
    ring
  rw [h1, hlam]
  have h2 : -(t / D * t) + (t / D) ^ 2 * D / 2 = -(t ^ 2) / (2 * D) := by
    field_simp
    ring
  rw [h2]

/-- The sum MGF bound at a centered, centered-bounded, mutually
independent family. -/
theorem mgf_sum_le_bernstein {n : ℕ} {Y : Fin n → Ω → ℝ} {a : ℝ} (ha : 0 < a)
    (h_meas : ∀ i, Measurable (Y i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) Y μ)
    (h_bound : ∀ i ω, |Y i ω| ≤ a) (h_mean : ∀ i, ∫ ω, Y i ω ∂μ = 0)
    {lam : ℝ} (hlam : 0 < lam) (hla3 : lam * a < 3) :
    ∫ ω, Real.exp (lam * ∑ i, Y i ω) ∂μ
      ≤ Real.exp (lam ^ 2 * (∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ) / (2 * (1 - lam * a / 3))) := by
  have hexpsum : ∀ ω, Real.exp (lam * ∑ i, Y i ω) = ∏ i, Real.exp (lam * Y i ω) := by
    intro ω
    rw [← Real.exp_sum, Finset.mul_sum]
  calc ∫ ω, Real.exp (lam * ∑ i, Y i ω) ∂μ
      = ∏ i, ∫ ω, Real.exp (lam * Y i ω) ∂μ := by
        rw [integral_congr_ae (ae_of_all μ hexpsum)]
        exact integral_prod_exp_of_iIndepFun h_meas h_indep lam Finset.univ
    _ ≤ ∏ i, Real.exp (lam ^ 2 * (∫ ω, (Y i ω) ^ 2 ∂μ) / (2 * (1 - lam * a / 3))) :=
        Finset.prod_le_prod (fun i _ => integral_nonneg (fun _ => (Real.exp_pos _).le))
          (fun i _ => bennett_mgf ha (h_meas i) (h_bound i) (h_mean i) hlam hla3)
    _ = Real.exp (lam ^ 2 * (∑ i, ∫ ω, (Y i ω) ^ 2 ∂μ) / (2 * (1 - lam * a / 3))) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.sum_div, ← Finset.mul_sum]

/-- **Bernstein's inequality** — a sum of independent variables whose
*centered* values satisfy `|X i ω − E (X i)| ≤ a` obeys the two-sided,
variance-dependent tail bound
`P {|∑ (X i - E (X i))| ≥ t} ≤ 2 exp (-t² / (2 V + 2 a t / 3))`,
where `V = ∑ i Var (X i)` is written with explicit centered integrals.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Cambridge University
  Press, 2018, Theorem 2.8.1, Chapter 2, p. 43.

Statement differences: the source states a one-sided bound for sums of
independent centered variables; we state the two-sided form for the
centered sum (doubling the right-hand side) and write the variance
statistic explicitly instead of through a `let`. **Repaired 2026-08-30**
(Errata §8): the admitted form hypothesized the uncentered bound
`|X i ω| ≤ a`; the source's hypothesis is on the *centered* variables
(`|X i − E X i| ≤ a`), and the centered variable satisfies only
`|X − E X| ≤ 2a` — the uncentered reading materially understates the
Bennett price (MGF-separation witness in
`Scaffold/QA/Concentration/Scalar_QA.lean`).

Retired from axiom to proved theorem 2026-08-30 via the Bennett engine
below; `#print axioms` reads the standard three only.

QA: `bernstein_inequality_zero_QA` and the retirement section
(`bernstein_inequality_rademacher_QA`, the MGF-separation witness) in
`Scaffold/QA/Concentration/Scalar_QA.lean`; the Derived consumers
`edgePerturbation_degree_tail_bernstein` and
`edgePerturbation_degree_tail_bernstein_budget` in
`Scaffold/Derived/EdgePerturbationTail.lean`.
-/
theorem bernstein_inequality {n : ℕ} {X : Fin n → Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω - ∫ ω', X i ω' ∂μ| ≤ a)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, (X i ω - ∫ ω', X i ω' ∂μ)| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) /
        (2 * ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ + (2 * a * t) / 3))) := by
  rcases ht.eq_or_lt with rfl | ht'
  · have hval : (-((0:ℝ) ^ 2) /
        (2 * ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ + (2 * a * 0) / 3)) = 0 := by
      rw [zero_pow, neg_zero, zero_div]
      norm_num
    rw [hval, Real.exp_zero, mul_one]
    refine le_trans (measure_mono (Set.subset_univ _)) ?_
    rw [measure_univ]
    exact ENNReal.one_le_ofReal.mpr (by norm_num)
  -- the main case: t > 0
  obtain ⟨m, hm⟩ : ∃ m : Fin n → ℝ, ∀ i, m i = ∫ ω', X i ω' ∂μ :=
    ⟨fun i => ∫ ω', X i ω' ∂μ, fun i => rfl⟩
  simp only [← hm]
  have hXint : ∀ i, Integrable (X i) μ := by
    intro i
    by_contra hcon
    have hzero : m i = 0 := by rw [hm i]; exact integral_undef hcon
    have hbb : ∀ ω, |X i ω| ≤ a := by
      intro ω
      have hw := h_bound i ω
      rw [show (∫ ω', X i ω' ∂μ) = m i from (hm i).symm, hzero] at hw
      simpa using hw
    exact hcon (integrable_of_bounded_measurable (μ := μ) (h_meas i) hbb)
  have hYmeas : ∀ i, Measurable (fun ω => X i ω - m i) :=
    fun i => (h_meas i).sub measurable_const
  have hYmean : ∀ i, ∫ ω, (X i ω - m i) ∂μ = 0 := by
    intro i
    rw [integral_sub (hXint i) (integrable_const _), hm i, integral_const]
    simp [measure_univ]
  have hYindep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ))
      (fun i ω => X i ω - m i) μ :=
    h_indep.comp (fun i => fun x => x - m i) (fun _ => measurable_id.sub measurable_const)
  have hYbound : ∀ i ω, |X i ω - m i| ≤ a := by
    intro i ω
    have h := h_bound i ω
    rw [hm i]
    exact h
  -- the V = 0 degenerate case
  by_cases hV : ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ = 0
  · have hYae : ∀ i, ∀ᵐ ω ∂μ, X i ω - m i = 0 := by
      intro i
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          0 ≤ ∫ ω, (X i ω - m i) ^ 2 ∂μ :=
        fun i _ => integral_nonneg (fun ω => sq_nonneg _)
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hV i (Finset.mem_univ i)
      have hint2 : Integrable (fun ω => (X i ω - m i) ^ 2) μ := by
        have h := integrable_sq_sub_mean (μ := μ) (hYmeas i) (hYbound i)
        rw [hYmean i] at h
        simpa using h
      refine Filter.Eventually.mono
        ((integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hint2).mp hmem) ?_
      intro ω h2
      exact sq_eq_zero_iff.mp h2
    have hnullsets : ∀ i : Fin n, μ {ω | X i ω - m i ≠ 0} = 0 := by
      intro i
      rw [measure_zero_iff_ae_nmem]
      exact (hYae i).mono (fun ω h => by simp [h])
    have hsub : {ω | |∑ i, (X i ω - m i)| ≥ t}
        ⊆ ⋃ i ∈ (Set.univ : Set (Fin n)), {ω | X i ω - m i ≠ 0} := by
      intro ω hω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      simp only [Set.mem_setOf_eq] at hω
      by_contra hcon
      push_neg at hcon
      have h0 : ∑ i ∈ (Finset.univ : Finset (Fin n)), (X i ω - m i) = 0 :=
        Finset.sum_eq_zero (fun i _ => hcon i (Set.mem_univ i))
      rw [h0] at hω
      simp only [abs_zero] at hω
      exact absurd hω (not_le.mpr ht')
    have hnull : μ (⋃ i ∈ (Set.univ : Set (Fin n)), {ω | X i ω - m i ≠ 0}) = 0 := by
      rw [measure_biUnion_null_iff (Set.to_countable _)]
      exact fun i _ => hnullsets i
    exact (measure_mono_null hsub hnull).le.trans (zero_le _)
  · push_neg at hV
    have hVnn : 0 ≤ ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ :=
      Finset.sum_nonneg fun i _ => integral_nonneg (fun ω => sq_nonneg _)
    have hVpos : 0 < ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ := lt_of_le_of_ne hVnn hV.symm
    -- a must be strictly positive here: a = 0 forces every centered variable to vanish
    have ha' : 0 < a := by
      by_contra hcon
      push_neg at hcon
      have haeq : a = 0 := le_antisymm hcon ha
      have hbd : ∀ i, ∀ ω, X i ω - m i = 0 := by
        intro i ω
        have h := hYbound i ω
        rw [haeq] at h
        exact le_antisymm ((abs_le.mp h).2) (by simpa using (abs_le.mp h).1)
      have hV0 : ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have hfun : (fun ω => (X i ω - m i) ^ 2) = fun _ => (0:ℝ) := by
          funext ω
          rw [hbd i ω]
          norm_num
        rw [hfun, integral_const]
        simp [measure_univ]
      exact absurd hV0 hV
    -- the Chernoff parameter
    set D : ℝ := ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + a * t / 3 with hDdef
    have hD : 0 < D := by
      have hat : (0:ℝ) ≤ a * t / 3 :=
        div_nonneg (mul_nonneg ha ht'.le) (by norm_num : (0:ℝ) ≤ 3)
      rw [hDdef]
      linarith [hVpos, hat]
    set lam : ℝ := t / D with hlamdef
    have hlam : 0 < lam := div_pos ht' hD
    have hla : lam * a < 3 := by
      have hkey : t * a < 3 * (∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + a * t / 3) := by
        have h3 : (0:ℝ) ≤ 3 * ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ :=
          mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
            integral_nonneg (fun ω => sq_nonneg _))
        have hat : (0:ℝ) ≤ a * t / 3 :=
          div_nonneg (mul_nonneg ha ht'.le) (by norm_num : (0:ℝ) ≤ 3)
        nlinarith [h3, hat]
      rw [hlamdef, div_mul_eq_mul_div, div_lt_iff₀ hD]
      exact hkey
    have hfrac : 1 - lam * a / 3 = (∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ) / D := by
      have hDn : D ≠ 0 := ne_of_gt hD
      rw [hlamdef]
      field_simp
      rw [hDdef]
      field_simp
      ring
    -- the two MGF bounds
    have hmgf := mgf_sum_le_bernstein ha' hYmeas hYindep hYbound hYmean hlam hla
    have hmgfneg := mgf_sum_le_bernstein ha' (fun i => (hYmeas i).neg)
      (hYindep.comp (fun _ => fun x => -x) (fun _ => measurable_id.neg))
      (fun i ω => by rw [abs_neg]; exact hYbound i ω)
      (fun i => by rw [integral_neg, hYmean i, neg_zero]) hlam hla
    -- integrability of the two exponentials
    have hSsum : ∀ (s : Finset (Fin n)), Measurable (fun ω => ∑ i ∈ s, (X i ω - m i)) := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => simp [measurable_const]
      | @insert i s hi ih =>
        simp only [Finset.sum_insert hi]
        exact Measurable.add (hYmeas i) ih
    have hSmeas : Measurable (fun ω => ∑ i : Fin n, (X i ω - m i)) := hSsum Finset.univ
    have hSbd : ∀ ω, |∑ i : Fin n, (X i ω - m i)| ≤ ∑ i : Fin n, a := by
      intro ω
      calc |∑ i, (X i ω - m i)| ≤ ∑ i, |X i ω - m i| := by
            simpa [Real.norm_eq_abs] using norm_sum_le (Finset.univ : Finset (Fin n))
              (fun i => X i ω - m i)
        _ ≤ ∑ i, a := Finset.sum_le_sum fun i _ => hYbound i ω
    have hintexp : ∀ l : ℝ, Integrable (fun ω => Real.exp (l * ∑ i, (X i ω - m i))) μ := by
      intro l
      refine integrable_of_bounded_measurable
        (a := Real.exp (|l| * ∑ i : Fin n, a)) (Real.measurable_exp.comp (hSmeas.const_mul l))
        (fun ω => ?_)
      have h1 : |Real.exp (l * ∑ i, (X i ω - m i))| ≤ Real.exp (|l| * ∑ i : Fin n, a) := by
        rw [abs_of_nonneg (Real.exp_pos _).le]
        refine Real.exp_le_exp.mpr ?_
        calc l * ∑ i, (X i ω - m i) ≤ |l * ∑ i, (X i ω - m i)| := le_abs_self _
          _ = |l| * |∑ i, (X i ω - m i)| := abs_mul _ _
          _ ≤ |l| * ∑ i, a := mul_le_mul_of_nonneg_left (hSbd ω) (abs_nonneg _)
      simpa [Real.norm_eq_abs] using h1
    have hintexpneg : Integrable (fun ω => Real.exp (lam * (-(∑ i, (X i ω - m i))))) μ := by
      have h := hintexp (-lam)
      refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [mul_neg, neg_mul]
    have hmgfneg' : ∫ ω, Real.exp (lam * (-(∑ i, (X i ω - m i)))) ∂μ
        ≤ Real.exp (lam ^ 2 * (∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ)
          / (2 * (1 - lam * a / 3))) := by
      have hEq : (fun ω => Real.exp (lam * (-(∑ i, (X i ω - m i)))))
          = (fun ω => Real.exp (lam * ∑ i, (-(X i ω - m i)))) := by
        funext ω
        rw [← Finset.sum_neg_distrib]
      rw [hEq]
      have hVeq : (∑ i : Fin n, ∫ ω, (-(X i ω - m i)) ^ 2 ∂μ)
          = (∑ i : Fin n, ∫ ω, (X i ω - m i) ^ 2 ∂μ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_congr_ae (ae_of_all μ fun ω => by rw [neg_sq])]
      rw [hVeq] at hmgfneg
      exact hmgfneg
    -- Markov on both sides
    have h1 := markov_tail_of_mgf (hintexp lam) hmgf hlam.le t
    have h2 := markov_tail_of_mgf hintexpneg hmgfneg' hlam.le t
    have hsub : {ω | |∑ i, (X i ω - m i)| ≥ t}
        ⊆ {ω | t ≤ ∑ i, (X i ω - m i)} ∪ {ω | t ≤ -(∑ i, (X i ω - m i))} := by
      intro ω hω
      simp only [Set.mem_setOf_eq] at hω
      rcases le_or_lt 0 (∑ i, (X i ω - m i)) with h | h
      · exact Or.inl (by rwa [abs_of_nonneg h] at hω)
      · exact Or.inr (by rwa [abs_of_neg h] at hω)
    have hexpcomb : Real.exp (-(lam * t))
        * Real.exp (lam ^ 2 * (∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ)
          / (2 * (1 - lam * a / 3)))
        = Real.exp (-(t ^ 2) / (2 * ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + (2 * a * t) / 3)) := by
      rw [← Real.exp_add]
      congr 1
      have hdd : 2 * (∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ) + 2 * a * t / 3 = 2 * D := by
        rw [hDdef]
        ring
      exact exponent_identity _ D t a lam (ne_of_gt hD) (ne_of_gt hVpos) hlamdef hfrac hdd
    have hnn : (0:ℝ) ≤ Real.exp (-(t ^ 2)
      / (2 * ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + (2 * a * t) / 3)) := (Real.exp_pos _).le
    calc μ {ω | |∑ i, (X i ω - m i)| ≥ t}
        ≤ μ {ω | t ≤ ∑ i, (X i ω - m i)} + μ {ω | t ≤ -(∑ i, (X i ω - m i))} :=
          le_trans (measure_mono hsub) (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (Real.exp (-(lam * t))
          * Real.exp (lam ^ 2 * (∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ)
            / (2 * (1 - lam * a / 3))))
          + ENNReal.ofReal (Real.exp (-(lam * t))
          * Real.exp (lam ^ 2 * (∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ)
            / (2 * (1 - lam * a / 3)))) :=
          add_le_add h1 h2
      _ = ENNReal.ofReal (2 * Real.exp (-(t ^ 2)
          / (2 * ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + (2 * a * t) / 3))) := by
          rw [hexpcomb, ← ENNReal.ofReal_add hnn hnn, ← two_mul]
/-- **Bernstein's inequality with an explicit variance budget** `v`
dominating the total variance.

Source:
- Wainwright, High-Dimensional Statistics: A Non-Asymptotic Viewpoint,
  Cambridge University Press, 2019, Theorem 2.15, Chapter 2, p. 52.

Statement differences: as in `bernstein_inequality`, plus the budget form
`∑ Var (X i) ≤ v`, which relaxes the denominator monotonically.
**Repaired 2026-08-30** (Errata §8) together with `bernstein_inequality`
(centered bound hypothesis); the previously present `0 ≤ v` clause is
dropped as dead — it is implied by `h_var` and unused by the proof, so
the repaired statement is strictly stronger.

Retired from axiom to proved theorem 2026-08-30.

QA: the retirement section of `Scaffold/QA/Concentration/Scalar_QA.lean`
and the Derived consumer pins in
`Scaffold/QA/Derived/EdgePerturbation_QA.lean`.
-/
theorem bernstein_bounded_variance {n : ℕ} {X : Fin n → Ω → ℝ} {a v : ℝ}
    (ha : 0 ≤ a)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω - ∫ ω', X i ω' ∂μ| ≤ a)
    (h_var : ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ ≤ v)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, (X i ω - ∫ ω', X i ω' ∂μ)| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * v + (2 * a * t) / 3))) := by
  rcases ht.eq_or_lt with rfl | ht'
  · have hval : (-((0:ℝ) ^ 2) / (2 * v + (2 * a * 0) / 3)) = 0 := by
      rw [zero_pow, neg_zero, zero_div]
      norm_num
    rw [hval, Real.exp_zero, mul_one]
    refine le_trans (measure_mono (Set.subset_univ _)) ?_
    rw [measure_univ]
    exact ENNReal.one_le_ofReal.mpr (by norm_num)
  obtain ⟨m, hm⟩ : ∃ m : Fin n → ℝ, ∀ i, m i = ∫ ω', X i ω' ∂μ :=
    ⟨fun i => ∫ ω', X i ω' ∂μ, fun i => rfl⟩
  have hYbound : ∀ i ω, |X i ω - m i| ≤ a := by
    intro i ω
    have h := h_bound i ω
    rw [hm i]
    exact h
  have hYmeas : ∀ i, Measurable (fun ω => X i ω - m i) :=
    fun i => (h_meas i).sub measurable_const
  simp only [← hm] at h_var
  -- second-moment integrability from the centered bound
  have hint2 : ∀ i, Integrable (fun ω => (X i ω - m i) ^ 2) μ := by
    intro i
    have hXint : Integrable (X i) μ := by
      by_contra hcon
      have hzero : m i = 0 := by rw [hm i]; exact integral_undef hcon
      have hbb : ∀ ω, |X i ω| ≤ a := by
        intro ω
        have hw := h_bound i ω
        rw [show (∫ ω', X i ω' ∂μ) = m i from (hm i).symm, hzero] at hw
        simpa using hw
      exact hcon (integrable_of_bounded_measurable (μ := μ) (h_meas i) hbb)
    have hbdd : ∀ ω, |X i ω| ≤ a + |m i| := by
      intro ω
      calc |X i ω| = |(X i ω - m i) + m i| := by
            rw [sub_add_cancel]
          _ ≤ |X i ω - m i| + |m i| := abs_add _ _
          _ ≤ a + |m i| := add_le_add_right (hYbound i ω) _
    have h := integrable_sq_sub_mean (μ := μ) (h_meas i) hbdd
    have hfun : (fun ω => (X i ω - ∫ ω', X i ω' ∂μ) ^ 2) = fun ω => (X i ω - m i) ^ 2 := by
      funext ω
      rw [(hm i).symm]
    rwa [hfun] at h
  by_cases hV0 : ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ = 0
  · -- every centered variable vanishes a.e.; the event is null
    have hYae : ∀ i, ∀ᵐ ω ∂μ, X i ω - m i = 0 := by
      intro i
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          0 ≤ ∫ ω, (X i ω - m i) ^ 2 ∂μ :=
        fun i _ => integral_nonneg (fun ω => sq_nonneg _)
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hV0 i (Finset.mem_univ i)
      refine Filter.Eventually.mono
        ((integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) (hint2 i)).mp hmem) ?_
      intro ω h2
      exact sq_eq_zero_iff.mp h2
    have hnullsets : ∀ i : Fin n, μ {ω | X i ω - m i ≠ 0} = 0 := by
      intro i
      rw [measure_zero_iff_ae_nmem]
      exact (hYae i).mono (fun ω h => by simp [h])
    have hsub2 : {ω | |∑ i, (X i ω - m i)| ≥ t}
        ⊆ ⋃ i ∈ (Set.univ : Set (Fin n)), {ω | X i ω - m i ≠ 0} := by
      intro ω hω
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      simp only [Set.mem_setOf_eq] at hω
      by_contra hcon
      push_neg at hcon
      have h0 : ∑ i ∈ (Finset.univ : Finset (Fin n)), (X i ω - m i) = 0 :=
        Finset.sum_eq_zero (fun i _ => hcon i (Set.mem_univ i))
      rw [h0] at hω
      simp only [abs_zero] at hω
      exact absurd hω (not_le.mpr ht')
    have hnull2 : μ (⋃ i ∈ (Set.univ : Set (Fin n)), {ω | X i ω - m i ≠ 0}) = 0 := by
      rw [measure_biUnion_null_iff (Set.to_countable _)]
      exact fun i _ => hnullsets i
    simp only [← hm]
    exact ((measure_mono_null hsub2 hnull2).le).trans (zero_le _)
  · push_neg at hV0
    have hVnn : 0 ≤ ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ :=
      Finset.sum_nonneg fun i _ => integral_nonneg (fun ω => sq_nonneg _)
    have hVpos : 0 < ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ := lt_of_le_of_ne hVnn hV0.symm
    have h := bernstein_inequality ha h_meas h_indep h_bound t ht
    simp only [← hm] at h ⊢
    have hat : (0:ℝ) ≤ a * t / 3 :=
      div_nonneg (mul_nonneg ha ht) (by norm_num : (0:ℝ) ≤ 3)
    have hXpos : (0:ℝ) < 2 * ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + 2 * a * t / 3 := by
      nlinarith [hVpos, hat]
    have hYpos : (0:ℝ) < 2 * v + 2 * a * t / 3 := by nlinarith [h_var, hVpos, hat]
    have hdiv : (t ^ 2) / (2 * v + 2 * a * t / 3)
        ≤ (t ^ 2) / (2 * ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + 2 * a * t / 3) := by
      rw [div_le_div_iff₀ hYpos hXpos]
      have hXY : (2:ℝ) * ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + 2 * a * t / 3
          ≤ 2 * v + 2 * a * t / 3 := by nlinarith [h_var]
      exact mul_le_mul_of_nonneg_left hXY (sq_nonneg t)
    have hexp : Real.exp (-t ^ 2 / (2 * ∑ i, ∫ ω, (X i ω - m i) ^ 2 ∂μ + 2 * a * t / 3))
        ≤ Real.exp (-t ^ 2 / (2 * v + 2 * a * t / 3)) := by
      rw [neg_div, neg_div]
      exact Real.exp_le_exp.mpr (neg_le_neg hdiv)
    refine h.trans ?_
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hexp (by norm_num))
/-- Bernstein's inequality for identically distributed variables with
common centered second moment `σ_sq`. This is a proved consequence of
`bernstein_inequality`, not an axiom.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Corollary 2.8.3,
  Chapter 2, p. 45.

Statement differences: we state the direct instantiation
`2 exp (-t² / (2 n σ² + 2 a t / 3))` of the general bound; an equivalent
form rescales the numerator to `n t²`. The `h_bound` clause carries the
centered shape of the repaired `bernstein_inequality` (2026-08-30).
-/
theorem bernstein_iid {n : ℕ} {X : Fin n → Ω → ℝ} {a σ_sq : ℝ} (ha : 0 ≤ a)
    (hσ : 0 ≤ σ_sq)
    (h_meas : ∀ i, Measurable (X i))
    (h_indep : iIndepFun (fun _ : Fin n => (inferInstance : MeasurableSpace ℝ)) X μ)
    (h_bound : ∀ i ω, |X i ω - ∫ ω', X i ω' ∂μ| ≤ a)
    (h_var : ∀ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ = σ_sq)
    (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |∑ i, (X i ω - ∫ ω', X i ω' ∂μ)| ≥ t} ≤
      ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / (2 * ((n : ℝ) * σ_sq) + (2 * a * t) / 3))) := by
  have h := bernstein_inequality ha h_meas h_indep h_bound t ht
  rwa [show ∑ i, ∫ ω, (X i ω - ∫ ω', X i ω' ∂μ) ^ 2 ∂μ = (n : ℝ) * σ_sq by
    rw [Finset.sum_congr rfl (fun i _ => h_var i), Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]] at h

end Scaffold.Mathlib.Probability.Concentration.Scalar
