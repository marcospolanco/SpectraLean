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
bound for that definition and the admitted (cited) Hoeffding lemma that
Scaffold currently consumes.

`subgaussianNorm` is a real definition, not an axiom: it is the infimum of
the admissible MGF bounds. The tail bound about it is a proved theorem;
Hoeffding's lemma (bounded zero-mean variables have small ψ₂ size)
remains an explicit axiom with a citation.

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

/-- Hoeffding's lemma: a random variable bounded by `a` with mean zero is
`a`-subgaussian.

Source:
- Vershynin, High-Dimensional Probability, 2nd ed., Cambridge University
  Press, 2018, Lemma 2.6.2, Chapter 2, p. 32.

Statement differences: the source states the MGF form
`E exp(λX) ≤ exp(λ²a²/2)`; we state it through `subgaussianNorm`, whose MGF
characterization is equivalent up to universal constants
(Proposition 2.5.2), so the conclusion may lose an absolute constant
relative to the source.

QA: exercised, together with `subgaussianNorm_nonneg`, by
`subgaussian_norm_zero_QA` in `Scaffold/QA/Concentration/Scalar_QA.lean`
(it supplies the `≤ 0` half of `subgaussianNorm (fun _ => 0) μ = 0`; the
`≥ 0` half is the proved `subgaussianNorm_nonneg`). Before the
2026-08-22 retirement it also fed the old axiom-shaped
`subgaussian_tail_bound`; the proved theorem no longer consumes it.
-/
axiom hoeffding_lemma {X : Ω → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (h_bound : ∀ ω, |X ω| ≤ a) (h_mean : ∫ ω, X ω ∂μ = 0) :
    subgaussianNorm X μ ≤ a

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
