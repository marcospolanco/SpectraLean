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
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Subgaussian random variables

The ψ₂ (subgaussian) size of a real random variable, defined for the
Bochner integral on an arbitrary measure, together with the proved tail
bound for that definition and Hoeffding's lemma bounding that size for
bounded variables.

`subgaussianNorm` is a real definition, not an axiom: it is the infimum of
the admissible MGF bounds. The tail bound about it is a proved theorem;
Hoeffding's lemma in this ψ₂ form was admitted as a cited axiom through
2026-08-29 and was **retired to a proved theorem on 2026-08-30** by the
pointwise-collapse route (see the lemma's docstring): on a probability
measure, boundedness alone puts `a / √(log 2)` in the defining set. The
source's λ-form content — the mean-zero MGF bound that actually carries
Vershynin Lemma 2.6.2 — is proved independently as
`hoeffding_lemma_mgf` in `Hoeffding.lean` (retired from axiom
2026-08-30).

Only the statements with a named downstream consumer are stated;
Vershynin's moment-growth and centering estimates are left out of the
trust boundary until a consumer needs them.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace Scaffold.Mathlib.Probability.Concentration.Scalar

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The ψ₂ (subgaussian) norm of a real random variable `X` under the
measure `μ`: the infimum of all `K > 0` with
`∫ ω, exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2`.

This is the Orlicz/MGF characterization of the subgaussian norm (Vershynin,
*High-Dimensional Probability*, 2nd ed., Proposition 2.5.2); the official
definition (Definition 2.5.1) is the equivalent moment-supremum
`sup_{p ≥ 1} (E |X| ^ p) ^ (1 / p) / √p`, and the two agree up to universal
constant factors. We adopt the MGF form because it composes directly with
integral statements.

If no admissible `K` exists, the index set is empty and the `sInf` is the
junk value `0`; consumers must establish finiteness from hypotheses such
as `hoeffding_lemma`. **Junk-behavior correction (2026-08-22):** the
Bochner integral of a non-integrable function is itself the junk value
`0` (`MeasureTheory.integral_undef`), so a sufficiently heavy-tailed `X`
(non-integrable `exp (X ω ^ 2 / K ^ 2)` at every `K`) places *every*
`K > 0` in the index set — the set is then full, not empty, and the
norm is again `0`. Either way the bare inequality
`subgaussianNorm X μ ≤ K` cannot certify a tail bound: it holds vacuously
when the set is empty (measures of total mass above `2`) and trivially
misleadingly when it is full (heavy tails indistinguishable from
`X = 0`). Consumers must carry the moment integrably — this is exactly
what the proved `subgaussian_tail_bound` below does with its
`h_int`/`h_mom` hypotheses. -/
noncomputable def subgaussianNorm (X : Ω → ℝ) (μ : Measure Ω) : ℝ :=
  sInf {K : ℝ | 0 < K ∧ ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2}

/-- The subgaussian norm is nonnegative: the defining set only contains
positive `K`, so `0` is a lower bound. -/
theorem subgaussianNorm_nonneg (X : Ω → ℝ) (μ : Measure Ω) :
    0 ≤ subgaussianNorm X μ :=
  Real.sInf_nonneg fun K hK => le_of_lt hK.1

/-- A variable that is pointwise zero has subgaussian norm exactly `0` on
a probability measure: every `K > 0` is admissible (`∫ 1 = 1 ≤ 2`), so
the defining set is all of `Set.Ioi 0` and its infimum is `0`. This is
the `a = 0` corner of the bounded-variable bound below. -/
theorem subgaussianNorm_eq_zero_of_forall_eq_zero [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : ∀ ω, X ω = 0) :
    subgaussianNorm X μ = 0 := by
  have hint : ∀ K : ℝ, 0 < K → ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ = 1 := by
    intro K _
    have h1 : (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) = fun _ : Ω => (1 : ℝ) :=
      funext fun ω => by simp [hX ω]
    rw [h1, integral_const, measure_univ]
    simp
  have hmem : ∀ r : ℝ, 0 < r → r ∈ {K : ℝ | 0 < K
      ∧ ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2} := by
    intro r hr
    exact ⟨hr, by rw [hint r hr]; norm_num⟩
  have hbb : BddBelow {K : ℝ | 0 < K ∧ ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2} :=
    ⟨0, fun k hk => le_of_lt hk.1⟩
  have hne : {K : ℝ | 0 < K ∧ ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2}.Nonempty :=
    ⟨1, hmem 1 one_pos⟩
  simp only [subgaussianNorm]
  refine le_antisymm ?_ (Real.sInf_nonneg fun K hK => le_of_lt hK.1)
  exact (Real.sInf_le_iff hbb hne).2
    (fun ε hε => ⟨ε / 2, hmem _ (by positivity), by linarith⟩)

/-- The sharp boundedness-only collapse of the subgaussian norm: on a
probability measure, any `X` with `|X ω| ≤ a` — no centering, no
measurability hypothesis — satisfies `subgaussianNorm X μ ≤ a / √(log 2)`.

The defining set `{K | 0 < K ∧ ∫ exp (X²/K²) ∂μ ≤ 2}` cannot see the
mean of `X`, only its bound: pointwise
`exp (X ω² / K²) ≤ exp (log 2) = 2` at `K = a / √(log 2)`, so the moment
condition holds with equality at the supremum. The constant is the exact
uniform one over all bounded variables — attained by every `X` with
`|X| ≡ a` (at the Rademacher fixture the norm is *exactly*
`1/√(log 2)`, QA `rademacher_norm_eq_QA`), and it strictly improves the
`√6 · a` of `hoeffding_lemma` (since `log 2 ≥ 1/2`, by
`Real.one_sub_inv_le_log_of_pos`). No numeric pins are used anywhere.

The probability-measure instance is load-bearing, exactly as it was for
the admitted statement it retires: at a measure of mass above `1` the
conclusion fails (QA `subgaussianNorm_le_of_bounded_guard_refuted_QA`
refutes it at the mass-`19/10` fixture). Junk-behavior: the proof's
integral step (`integral_mono_of_nonneg`) needs no measurability of `X`;
when the integrand is not ae-strongly-measurable the Bochner integral is
the junk `0` and the conclusion holds a fortiori.

QA: exercised by `subgaussianNorm_le_of_bounded_uncentered_QA` (the
companion at an uncentered variable) and
`subgaussianNorm_le_of_bounded_guard_refuted_QA` (the mass-guard fence)
in `Scaffold/QA/Concentration/Scalar_QA.lean`; its sharpness is pinned by
`rademacher_norm_eq_QA` in the same file. -/
theorem subgaussianNorm_le_of_bounded [IsProbabilityMeasure μ] {X : Ω → ℝ} {a : ℝ}
    (ha : 0 ≤ a) (h_bound : ∀ ω, |X ω| ≤ a) :
    subgaussianNorm X μ ≤ a / Real.sqrt (Real.log 2) := by
  rcases eq_or_lt_of_le ha with rfl | ha0
  · have hX : ∀ ω, X ω = 0 := fun ω =>
      le_antisymm (abs_le.mp (h_bound ω)).2 (by simpa using (abs_le.mp (h_bound ω)).1)
    rw [subgaussianNorm_eq_zero_of_forall_eq_zero hX]
    simp
  · have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
    have hK : (0 : ℝ) < a / Real.sqrt (Real.log 2) := div_pos ha0 (Real.sqrt_pos.2 hL)
    have hKeq : Real.log 2 * (a / Real.sqrt (Real.log 2)) ^ 2 = a ^ 2 := by
      rw [div_pow, Real.sq_sqrt (le_of_lt hL)]
      field_simp
    have hmem : a / Real.sqrt (Real.log 2) ∈ {K : ℝ | 0 < K
        ∧ ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2} := by
      refine ⟨hK, ?_⟩
      have hptw : ∀ ω,
          Real.exp (X ω ^ 2 / (a / Real.sqrt (Real.log 2)) ^ 2) ≤ (2 : ℝ) := by
        intro ω
        obtain ⟨hl, hr⟩ := abs_le.mp (h_bound ω)
        have hX2 : X ω ^ 2 ≤ a ^ 2 := by nlinarith [hl, hr, sq_nonneg (X ω), sq_nonneg a]
        have hle : X ω ^ 2 / (a / Real.sqrt (Real.log 2)) ^ 2 ≤ Real.log 2 := by
          rw [div_le_iff₀ (by positivity : (0 : ℝ) < (a / Real.sqrt (Real.log 2)) ^ 2), hKeq]
          exact hX2
        calc Real.exp (X ω ^ 2 / (a / Real.sqrt (Real.log 2)) ^ 2)
            ≤ Real.exp (Real.log 2) := Real.exp_le_exp.2 hle
          _ = 2 := Real.exp_log (by norm_num : (0 : ℝ) < 2)
      calc ∫ ω, Real.exp (X ω ^ 2 / (a / Real.sqrt (Real.log 2)) ^ 2) ∂μ
          ≤ ∫ _ : Ω, (2 : ℝ) ∂μ :=
            integral_mono_of_nonneg (ae_of_all μ fun _ => (Real.exp_pos _).le)
              (integrable_const _) (ae_of_all μ hptw)
        _ = 2 := by rw [integral_const, measure_univ]; simp
    simp only [subgaussianNorm]
    exact csInf_le ⟨0, fun k hk => le_of_lt hk.1⟩ hmem

set_option linter.unusedVariables false in
/-- Hoeffding's lemma: a random variable bounded by `a` with mean zero on
a *probability* measure is `(√6 · a)`-subgaussian.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Cambridge University
  Press, 2018, Lemma 2.6.2, Chapter 2, p. 32.

Statement differences: the source states the MGF form
`E exp(λX) ≤ exp(λ²a²/2)`; we state it through `subgaussianNorm`. The
constant is ours, derived: the source's λ-form gives the two-sided tail
`P {|X| ≥ x} ≤ 2 exp (-x² / (2a²))`, and layer-cake integration of
`Y = exp (X²/K²)` at `K² = 6a²` yields `E Y ≤ 1 + 2/(K²/(2a²) − 1) = 2`
exactly at `K = √6 · a`. (Vershynin's Proposition 2.5.2 records the
equivalence of the two characterizations only up to unspecified
constants.)

Statement history: admitted through 2026-08-28 as
`subgaussianNorm X μ ≤ a` with **no** measure constraint, this shape was
**materially false in two independent ways**, both found by the
integrability audit
(`proposals/audit-scalar-concentration-integrability-hazard.md`,
Step 0) and both refuted in QA
(`Scaffold/QA/Concentration/Scalar_QA.lean`):

1. **Wrong constant.** On the fair-coin probability measure, the
   Rademacher variable `±1` with `a = 1` satisfies every hypothesis
   genuinely (`∫ X = 0` for real), but the defining set only contains
   `K` with `K² ≥ 1/log 2`, so the norm is `1/√(log 2) ≈ 1.20 > 1`
   (`old_hoeffding_lemma_refuted_constant_QA`: the norm is at least
   `6/5`). No junk values are involved — this refutes the constant `1`
   on well-behaved probability spaces.
2. **Missing mass guard.** On the mass-`19/10` rescaling of the same
   measure (mean still genuinely `0`), the defining set's threshold
   `1/√(log (2/M))` grows without bound as the mass `M` approaches `2`
   from below — the norm is `> 4` there
   (`old_hoeffding_lemma_refuted_guard_QA`), so **no** finite constant
   rescues the statement without a probability-measure hypothesis.

**Retirement (2026-08-30):** proved locally by the pointwise-collapse
route (`proposals/retire-hoeffding-lemma-pointwise-collapse.md`), at the
unchanged public statement. The proof routes through the sharper
companion `subgaussianNorm_le_of_bounded` (`≤ a / √(log 2)`, no
centering) plus `1/√(log 2) ≤ √6` (from `log 2 ≥ 1/2`). The finding the
retirement records: at the `√6 · a` constant this statement never
carried the source's λ-form content — the defining set sees only the
bound `|X ω| ≤ a` and the mass, so boundedness alone proves it. The
mean-zero hypothesis is retained purely for statement stability of the
retired shape; the source's actual mean-zero λ-form content is proved
independently as `hoeffding_lemma_mgf` in `Hoeffding.lean`.

Junk safety: the proof needs no measurability of `X` (the integral step
is `integral_mono_of_nonneg`, valid for any `X`; junk-zero integrals
only shrink the left side), and both recorded junk mechanisms collapse
the norm *downward* while the conclusion is an upper bound.

QA: exercised by `subgaussian_norm_zero_QA` (the `≤ √6 * 0 = 0` half of
`subgaussianNorm (fun _ => 0) μ = 0`),
`hoeffding_lemma_rademacher_QA` (the retired statement instantiated at
the same Rademacher fixture that refutes the old constant — hard crust
since this retirement), and the retirement section's
`rademacher_norm_eq_QA` /
`subgaussianNorm_le_of_bounded_guard_refuted_QA` in
`Scaffold/QA/Concentration/Scalar_QA.lean`. -/
theorem hoeffding_lemma {X : Ω → ℝ} {a : ℝ} [IsProbabilityMeasure μ]
    (ha : 0 ≤ a) (h_bound : ∀ ω, |X ω| ≤ a) (h_mean : ∫ ω, X ω ∂μ = 0) :
    subgaussianNorm X μ ≤ √6 * a := by
  have hL : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  refine le_trans (subgaussianNorm_le_of_bounded ha h_bound) ?_
  rcases eq_or_lt_of_le ha with rfl | ha0
  · simp
  · have h6L : (1 : ℝ) ≤ 6 * Real.log 2 := by linarith
    have hkey : (1 : ℝ) / Real.sqrt (Real.log 2) ≤ Real.sqrt 6 := by
      rw [div_le_iff₀ (Real.sqrt_pos.2 hL)]
      calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (6 * Real.log 2) := Real.sqrt_le_sqrt h6L
        _ = Real.sqrt 6 * Real.sqrt (Real.log 2) :=
            Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 6) (Real.log 2)
    calc a / Real.sqrt (Real.log 2)
        = a * ((1 : ℝ) / Real.sqrt (Real.log 2)) := div_eq_mul_one_div _ _
      _ ≤ a * Real.sqrt 6 := mul_le_mul_of_nonneg_left hkey (le_of_lt ha0)
      _ = Real.sqrt 6 * a := mul_comm _ _

/-- Tail bound for a random variable with a subgaussian moment bound: if
`exp (X ω ^ 2 / K ^ 2)` is integrable with integral at most `2`, then the
two-sided tail obeys `μ {|X| ≥ t} ≤ 2 exp (-t² / (2K²))`.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Cambridge University
  Press, 2018, Proposition 2.5.2 (ii), Chapter 2, p. 29.

Statement history: this was admitted as an axiom through 2026-08-22 with
hypotheses `(hK : 0 ≤ K) (h_sub : subgaussianNorm X μ ≤ K)`. That shape is
materially false, in two independent ways, both rooted in junk values
(the retirement survey of 2026-08-22 confirmed both against this pin and
refuted the old shape in QA with its hypotheses proved satisfied at
`3 • δ₀`, where the defining set is empty, `sInf ∅ = 0` makes `h_sub`
vacuous, and the conclusion `3 ≤ 2` fails):
1. `Real.sInf_empty` makes the norm-hypothesis vacuous whenever no `K`
   satisfies the moment condition (e.g. any measure of total mass above
   `2`);
2. `MeasureTheory.integral_undef` makes the *integral itself* junk-zero
   for non-integrable MGFs, so heavy-tailed variables satisfy the defining
   condition at every `K` and the norm is `0` — the old conclusion would
   claim subgaussian tails for heavy-tailed variables even under a
   probability measure.
The repair states the moment integrably (`h_int`, `h_mom`), which is
exactly the hypothesis content Markov's inequality consumes, and drops
the meaningless `K = 0` branch (its bound evaluated to the junk-dependent
`2 * exp 0 = 2`). The conclusion, including the `2K²` constant, is
unchanged: monotone transfer of the moment from `K` to `√2 · K` (the
`Real.exp_half` square-root bridge) composes with Markov's inequality
`MeasureTheory.mul_meas_ge_le_integral_of_nonneg` at
`exp (t² / (2K²))`.

The `K = sInf` boundary case that a literal retirement would have faced
does not arise in the repaired statement: the hypotheses never mention
the `sInf`, so no limiting argument is needed.

QA: exercised by `subgaussian_tail_bound_zero_QA` (constant-zero
variable), `subgaussian_tail_bound_instance_QA` (constant-1 variable at
`K = 2`, `t = 1`, with the moment genuinely bounded via
`Real.log_two_gt_d9`), and the refutation family
`old_subgaussian_tail_bound_*_QA` in
`Scaffold/QA/Concentration/Scalar_QA.lean`.
-/
theorem subgaussian_tail_bound {X : Ω → ℝ} {K : ℝ} (hK : 0 < K)
    (h_int : Integrable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ)
    (h_mom : ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2) (t : ℝ) (ht : 0 ≤ t) :
    μ {ω | |X ω| ≥ t} ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * K ^ 2))) := by
  have hK2 : 0 < K ^ 2 := by positivity
  have h2K : (0 : ℝ) < 2 * K ^ 2 := by positivity
  -- pointwise domination at the half scale
  have hptw : ∀ ω, Real.exp (X ω ^ 2 / (2 * K ^ 2)) ≤ Real.exp (X ω ^ 2 / K ^ 2) := by
    intro ω
    refine Real.exp_le_exp.2 ?_
    rw [div_le_div_iff₀ h2K hK2]
    nlinarith [sq_nonneg (X ω), hK2]
  -- ae-strong-measurability via the square-root bridge `exp (x / 2) = √(exp x)`
  have hcomp : (fun ω => Real.exp (X ω ^ 2 / (2 * K ^ 2)))
      = fun ω => Real.sqrt (Real.exp (X ω ^ 2 / K ^ 2)) := by
    funext ω
    rw [← Real.exp_half, div_div, mul_comm (K ^ 2) 2]
  have hf2s : AEStronglyMeasurable (fun ω => Real.exp (X ω ^ 2 / (2 * K ^ 2))) μ := by
    rw [hcomp]
    exact continuous_sqrt.comp_aestronglyMeasurable h_int.aestronglyMeasurable
  -- integrability at the half scale
  have hf2i : Integrable (fun ω => Real.exp (X ω ^ 2 / (2 * K ^ 2))) μ :=
    h_int.mono' hf2s (ae_of_all μ fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _))] using hptw ω)
  -- moment at the half scale
  have hf2mom : ∫ ω, Real.exp (X ω ^ 2 / (2 * K ^ 2)) ∂μ ≤ 2 :=
    le_trans
      (integral_mono_of_nonneg (ae_of_all μ fun _ => le_of_lt (Real.exp_pos _)) h_int
        (ae_of_all μ hptw)) h_mom
  -- Markov's inequality at the half scale
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (f := fun ω => Real.exp (X ω ^ 2 / (2 * K ^ 2)))
    (ae_of_all μ fun _ => le_of_lt (Real.exp_pos _)) hf2i
    (Real.exp (t ^ 2 / (2 * K ^ 2)))
  have hmark' := le_trans hmark hf2mom
  -- the tail event is contained in Markov's event
  have hsub : {ω | |X ω| ≥ t}
      ⊆ {x | Real.exp (t ^ 2 / (2 * K ^ 2)) ≤ Real.exp (X x ^ 2 / (2 * K ^ 2))} := by
    intro ω hω
    refine Real.exp_le_exp.2 ?_
    rw [div_le_div_iff₀ h2K h2K]
    have hneg : -|X ω| ≤ t := le_trans (neg_nonpos.mpr (abs_nonneg (X ω))) ht
    have ht2 : t ^ 2 ≤ |X ω| ^ 2 := sq_le_sq' (a := t) (b := |X ω|) hneg hω
    rw [sq_abs (X ω)] at ht2
    exact mul_le_mul_of_nonneg_right ht2 (le_of_lt h2K)
  have hmono : μ {ω | |X ω| ≥ t}
      ≤ μ {x | Real.exp (t ^ 2 / (2 * K ^ 2)) ≤ Real.exp (X x ^ 2 / (2 * K ^ 2))} :=
    measure_mono hsub
  -- integrability forces Markov's event to have finite measure
  have hfin : μ {x | Real.exp (t ^ 2 / (2 * K ^ 2)) ≤ Real.exp (X x ^ 2 / (2 * K ^ 2))} < ∞ := by
    have h := hf2i.measure_norm_ge_lt_top (Real.exp_pos (t ^ 2 / (2 * K ^ 2)))
    rw [show {x : Ω | Real.exp (t ^ 2 / (2 * K ^ 2))
          ≤ ‖(fun x => Real.exp (X x ^ 2 / (2 * K ^ 2))) x‖}
        = {x : Ω | Real.exp (t ^ 2 / (2 * K ^ 2)) ≤ Real.exp (X x ^ 2 / (2 * K ^ 2))} from by
      ext x
      simp only [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _))]] at h
    exact h
  -- conclude in ENNReal
  rw [← ENNReal.ofReal_toReal (ne_of_lt hfin)] at hmono
  refine le_trans hmono ?_
  apply ENNReal.ofReal_le_ofReal
  rw [neg_div, Real.exp_neg,
    mul_comm (2 : ℝ) (Real.exp (t ^ 2 / (2 * K ^ 2)))⁻¹, inv_mul_eq_div,
    le_div_iff₀ (Real.exp_pos (t ^ 2 / (2 * K ^ 2))), mul_comm]
  exact hmark'

end Scaffold.Mathlib.Probability.Concentration.Scalar
