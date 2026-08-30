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
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Scaffold.Mathlib.Probability.Concentration.Matrix.Basic
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent

/-!
# The matrix master bound

The first proved slice of the matrix concentration retirement route
(`proposals/matrix-master-bound-first-slice.md`): the Laplace-transform
step that every matrix concentration proof consumes — Tropp's
Proposition 3.1, in its two-sided spectral-norm form — together with its
deterministic engine, the trace-exponential spectral identity.

Tropp, J. A., "User-friendly tail bounds for sums of random matrices",
Foundations of Computational Mathematics 12(4):389–434, 2012,
Proposition 3.1 (the Laplace transform bound), §3.

The deterministic core:

- `trace_exp_smul_eq_sum_exp_eigvalOf`: for real-symmetric `M` and any
  scale `θ`, `tr (exp (θ • M)) = ∑ i, exp (θ · λᵢ(M))` — the
  exponential-spectral trace identity. The pinned Mathlib lists the
  trace/determinant exponential identities as open TODOs in
  `Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean`; the proof
  here conjugates through the spectral theorem's unitary diagonalization,
  mirroring the shelf's exp-free sibling `eigvalOf_sum_eq_trace`.
- `exp_smul_eigvalOf_le_trace_exp`: every eigenvalue's exponential is a
  single summand of the (nonnegative) trace sum.

The probabilistic core:

- `measure_mul_le_lintegral`: Markov's inequality on the lower integral
  (no integrability hypothesis — honest for unbounded summands).
- `matrix_master_bound`: for strongly measurable symmetric-matrix-valued
  `Y`, `θ ≥ 0`, any `t`,
  `μ {‖Y‖ ≥ t} ≤ e^{−θt} (E tr e^{θY} + E tr e^{−θY})`, the two
  expectations written as lower integrals.

Degenerate corner, checked before stating: at `V = ∅`, `t = 0` the
two-sided master bound is false (the tail event is all of `Ω` while both
trace sums are empty sums) — the same corner class the admitted matrix
concentration axioms carry `[Nonempty V]` for (Errata-class, repaired
2026-08-28). The guard is present here at birth and fenced in QA
(`master_bound_fin0_unguarded_refuted_QA`).

What is *not* here: the sum-MGF step (Tropp's Theorem 6.1, Lieb's
concavity) that would retire `matrix_hoeffding`/`matrix_bernstein`/
`matrix_azuma_hoeffding` outright — genuinely deeper, multi-run, and
gated on an operator decision between admitting the analytic core and
proving it. Nothing in this module is an axiom.
-/

open MeasureTheory Real
open SpectralGraphTheory
open scoped Matrix ENNReal

namespace Scaffold.Mathlib.Probability.Concentration.Matrix

/-! ### The deterministic trace-exponential identity -/

section TraceExp

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The trace-exponential spectral identity, θ-scaled form: for a real
symmetric `M`, the trace of the exponential of `θ • M` is the sum of the
exponentials of the scaled eigenvalues. At `θ = 1` this is the spectral
trace identity for the matrix exponential (the identity the pinned
Mathlib lists as an open TODO beside its determinant sibling).

Route: the spectral theorem's unitary diagonalization
`M = U * diagonal λ * star U`, pulled through `θ • _` (scalar actions
commute with matrix products), the conjugation law of the exponential
(`Matrix.exp_conj`), and the diagonal exponential
(`Matrix.exp_diagonal`), with the trace cycling `U⁻¹` away — exactly the
proof shape of the shelf's exp-free sibling `eigvalOf_sum_eq_trace`. -/
theorem trace_exp_smul_eq_sum_exp_eigvalOf (M : Matrix V V ℝ) (hM : M.IsSymm) (θ : ℝ) :
    (NormedSpace.exp ℝ (θ • M)).trace = ∑ i, Real.exp (θ * eigvalOf M hM i) := by
  have hst := (isHermitian_of_isSymm hM).spectral_theorem (A := M) (n := V)
  have hc1 : star ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ)
      * ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ) = 1 :=
    unitary.coe_star_mul_self _
  set U : Matrix V V ℝ :=
    ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ) with hUdef
  set D : Matrix V V ℝ :=
    Matrix.diagonal (RCLike.ofReal ∘ (isHermitian_of_isSymm hM).eigenvalues) with hDdef
  have hc2 : ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ)
      * star ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ) = 1 :=
    Matrix.mul_eq_one_comm.mp hc1
  have hUinv : U⁻¹ = star U := Matrix.inv_eq_right_inv hc2
  have hUunit : IsUnit U :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.UnitaryGroup.det_isUnit _)
  -- θ • M = U * (θ • D) * star U
  have hsmulD : θ • M = U * (θ • D) * star U := by
    rw [hst]
    simp only [Matrix.smul_mul, Matrix.mul_smul]
  -- exp conjugates
  have hconj : NormedSpace.exp ℝ (U * (θ • D) * star U)
      = U * NormedSpace.exp ℝ (θ • D) * star U := by
    rw [← hUinv]
    exact Matrix.exp_conj ℝ U (θ • D) hUunit
  -- exp of the diagonal
  have hexpD : NormedSpace.exp ℝ (θ • D)
      = Matrix.diagonal (fun i => Real.exp (θ * eigvalOf M hM i)) := by
    rw [hDdef, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
    ext i j
    by_cases h : i = j
    · subst h
      simp [Real.exp_eq_exp_ℝ, eigvalOf, Matrix.diagonal_apply]
    · simp [Matrix.diagonal_apply, h]
  calc (NormedSpace.exp ℝ (θ • M)).trace
      = (U * NormedSpace.exp ℝ (θ • D) * star U).trace := by rw [hsmulD, hconj]
    _ = (NormedSpace.exp ℝ (θ • D)).trace := by
        rw [Matrix.trace_mul_cycle, hc1, Matrix.one_mul]
    _ = ∑ i, Real.exp (θ * eigvalOf M hM i) := by
        rw [hexpD, Matrix.trace_diagonal]

/-- The trace-exponential is nonnegative: it is a sum of exponentials. -/
theorem trace_exp_nonneg (M : Matrix V V ℝ) (hM : M.IsSymm) (θ : ℝ) :
    0 ≤ (NormedSpace.exp ℝ (θ • M)).trace := by
  rw [trace_exp_smul_eq_sum_exp_eigvalOf M hM θ]
  exact Finset.sum_nonneg fun i _ => Real.exp_nonneg _

/-- Each eigenvalue's exponential is dominated by the trace of the
exponential, at any scale `θ` and any index — the deterministic half of
the master bound's inclusion step. -/
theorem exp_smul_eigvalOf_le_trace_exp (M : Matrix V V ℝ) (hM : M.IsSymm) (θ : ℝ) (i : V) :
    Real.exp (θ * eigvalOf M hM i) ≤ (NormedSpace.exp ℝ (θ • M)).trace := by
  rw [trace_exp_smul_eq_sum_exp_eigvalOf]
  exact Finset.single_le_sum
    (f := fun i => Real.exp (θ * eigvalOf M hM i))
    (fun j _ => Real.exp_nonneg _) (Finset.mem_univ i)

end TraceExp

/-! ### Measurability of the trace-exponential -/

section Meas

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The trace-exponential is continuous in the matrix argument: the
matrix exponential is continuous (at the locally-convex l∞ operator
norm instances, whose topology is the canonical product topology on
matrices), scalar multiplication is continuous, and the trace is a
finite sum of entries. -/
theorem continuous_trace_exp (V) [Fintype V] [DecidableEq V] (θ : ℝ) :
    Continuous (fun M : Matrix V V ℝ => (NormedSpace.exp ℝ (θ • M)).trace) := by
  have hexp : Continuous (fun M : Matrix V V ℝ => NormedSpace.exp ℝ M) := by
    letI : NormedRing (Matrix V V ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix V V ℝ) := Matrix.linftyOpNormedAlgebra
    exact NormedSpace.exp_continuous
  have hsmul : Continuous (fun M : Matrix V V ℝ => θ • M) := continuous_const_smul θ
  have htr : Continuous (fun M : Matrix V V ℝ => M.trace) := by
    simp only [Matrix.trace]
    exact continuous_finset_sum _ fun i _ => continuous_apply_apply i i
  exact htr.comp (hexp.comp hsmul)

/-- The trace-exponential of a strongly measurable matrix-valued
function is strongly measurable — the hypothesis under which the master
bound's Markov step applies. -/
theorem stronglyMeasurable_trace_exp {Ω : Type} [MeasurableSpace Ω]
    {Y : Ω → Matrix V V ℝ} (hY : StronglyMeasurable Y) (θ : ℝ) :
    StronglyMeasurable (fun ω => (NormedSpace.exp ℝ (θ • Y ω)).trace) := by
  exact (continuous_trace_exp V θ).comp_stronglyMeasurable hY

end Meas

/-! ### Markov's inequality on the lower integral -/

section Markov

variable {Ω : Type} [MeasurableSpace Ω]

/-- Markov's inequality on the lower integral: for a measurable
`f : Ω → ℝ≥0∞` and any `c`, the threshold set's measure scaled by `c` is
dominated by `∫⁻ f`. No integrability hypothesis (the statement is
about the lower integral), and `c = 0` is allowed (trivially true). -/
theorem measure_mul_le_lintegral (μ : Measure Ω) (f : Ω → ℝ≥0∞) (hf : Measurable f)
    (c : ℝ≥0∞) :
    c * μ {ω | c ≤ f ω} ≤ ∫⁻ ω, f ω ∂μ := by
  have hs : MeasurableSet {ω | c ≤ f ω} := measurableSet_le measurable_const hf
  have hle : (fun ω => {ω | c ≤ f ω}.indicator (fun _ => c) ω) ≤ f := by
    intro ω
    by_cases h : ω ∈ {ω | c ≤ f ω}
    · simp only [Set.indicator_of_mem h]
      exact h
    · simp only [Set.indicator_of_not_mem h, zero_le]
  calc c * μ {ω | c ≤ f ω}
      = ∫⁻ ω, {ω | c ≤ f ω}.indicator (fun _ => c) ω ∂μ := by
        rw [lintegral_indicator hs, setLIntegral_const]
    _ ≤ ∫⁻ ω, f ω ∂μ := lintegral_mono hle

end Markov

/-! ### The master bound -/

section Master

variable {V : Type} [Fintype V] [DecidableEq V]

open scoped Matrix.L2OpNorm in
/-- The norm–eigenvalue attainment bridge: on a nonempty index type,
every threshold below the operator norm is attained by some eigenvalue
in absolute value. At `V = ∅` this fails for `t = 0` — the master
bound's degenerate corner, fenced as
`master_bound_fin0_unguarded_refuted_QA`. -/
theorem exists_abs_eigvalOf_ge [Nonempty V] {M : Matrix V V ℝ} (hM : M.IsSymm)
    {t : ℝ} (ht : t ≤ ‖M‖) : ∃ j : V, t ≤ |eigvalOf M hM j| := by
  set S : Finset ℝ := (Finset.univ : Finset V).image (fun i => |eigvalOf M hM i|) with hSdef
  have hne : S.Nonempty := Finset.image_nonempty.2 Finset.univ_nonempty
  have hj0 : |eigvalOf M hM (Classical.arbitrary V)| ∈ S :=
    Finset.mem_image_of_mem _ (Finset.mem_univ _)
  have hnn : (0 : ℝ) ≤ S.max' hne := le_trans (abs_nonneg _) (Finset.le_max' S _ hj0)
  have hle : ‖M‖ ≤ S.max' hne :=
    Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent.l2OpNorm_le_of_abs_eigvalOf_le
      hM hnn fun i => Finset.le_max' S _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  have hmem : S.max' hne ∈ S := Finset.max'_mem S hne
  obtain ⟨j, _, hjmax⟩ := Finset.mem_image.mp hmem
  exact ⟨j, le_trans (le_trans ht hle) (hjmax ▸ le_refl _)⟩

open scoped Matrix.L2OpNorm in
/-- **Matrix master bound** — Tropp's Proposition 3.1, the two-sided
spectral-norm form: for a strongly measurable symmetric-matrix-valued
`Y`, any scale `θ ≥ 0` and threshold `t`,

`μ {ω | t ≤ ‖Y ω‖} ≤ e^{−θt} (E tr e^{θY} + E tr e^{−θY})`,

with the expectations written as lower integrals (no integrability
hypothesis: the trace-exponential is nonnegative). This is the
Laplace-transform step every matrix concentration proof consumes; the
still-admitted `matrix_hoeffding`/`matrix_bernstein`/
`matrix_azuma_hoeffding` ride it together with the (not yet available)
sum-MGF step.

Source: Tropp, J. A., "User-friendly tail bounds for sums of random
matrices", Foundations of Computational Mathematics 12(4):389–434,
2012, Proposition 3.1, §3 — stated there in the one-sided
extreme-eigenvalue form; the two-sided spectral-norm form is the union
bound over both extremes, exactly the shape the shelf's admitted matrix
axioms take.

Statement differences: Tropp's `inf_θ` is left to the consumer (the
parameter `θ` is fixed here); the expectations are lower integrals of
the nonnegative trace-exponential, so no integrability hypothesis is
needed. The `[Nonempty V]` guard is load-bearing at `V = ∅`, `t = 0`
(the empty-sum trace makes the bound `0` against the full-space event)
— the corner the admitted matrix axioms were repaired for on
2026-08-28, fenced here at birth.

QA: exercised end-to-end at the constant design
`master_bound_diag_constant_QA`, with the degenerate corner fenced by
`master_bound_fin0_unguarded_refuted_QA` (both in
`Scaffold/QA/Concentration/Matrix_QA.lean`). -/
theorem matrix_master_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [Nonempty V] {Y : Ω → Matrix V V ℝ} (hY : ∀ ω, (Y ω).IsSymm)
    (h_meas : StronglyMeasurable Y) {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ) :
    μ {ω | t ≤ ‖Y ω‖} ≤
      ENNReal.ofReal (Real.exp (-(θ * t))) *
        (∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace) ∂μ +
         ∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ ((-θ) • Y ω)).trace) ∂μ) := by
  have hm1 : Measurable (fun ω => (NormedSpace.exp ℝ (θ • Y ω)).trace) :=
    (stronglyMeasurable_trace_exp h_meas θ).measurable
  have hm2 : Measurable (fun ω => (NormedSpace.exp ℝ ((-θ) • Y ω)).trace) :=
    (stronglyMeasurable_trace_exp h_meas (-θ)).measurable
  have hgmeas : Measurable (fun ω => ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace
      + (NormedSpace.exp ℝ ((-θ) • Y ω)).trace)) :=
    (hm1.add hm2).ennreal_ofReal
  have hgsum : ∀ ω, ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace
      + (NormedSpace.exp ℝ ((-θ) • Y ω)).trace)
      = ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace)
        + ENNReal.ofReal ((NormedSpace.exp ℝ ((-θ) • Y ω)).trace) :=
    fun ω => ENNReal.ofReal_add (trace_exp_nonneg _ (hY ω) θ)
      (trace_exp_nonneg _ (hY ω) (-θ))
  -- the inclusion: on the norm event, the trace-exponential pair dominates e^{θt}
  have hincl : {ω | t ≤ ‖Y ω‖} ⊆ {ω | ENNReal.ofReal (Real.exp (θ * t))
      ≤ ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace
        + (NormedSpace.exp ℝ ((-θ) • Y ω)).trace)} := by
    intro ω hω
    obtain ⟨j, hj⟩ := exists_abs_eigvalOf_ge (hY ω) hω
    rcases le_or_lt 0 (eigvalOf (Y ω) (hY ω) j) with hsign | hsign
    · have hlam : t ≤ eigvalOf (Y ω) (hY ω) j := by rwa [abs_of_nonneg hsign] at hj
      refine le_trans (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlam hθ))) ?_
      refine le_trans (ENNReal.ofReal_le_ofReal
        (exp_smul_eigvalOf_le_trace_exp (Y ω) (hY ω) θ j)) ?_
      rw [hgsum ω]
      exact le_add_of_nonneg_right (by simp)
    · have hlam : t ≤ -eigvalOf (Y ω) (hY ω) j := by rwa [abs_of_neg hsign] at hj
      refine le_trans (ENNReal.ofReal_le_ofReal
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hlam hθ))) ?_
      have hsymm : θ * -eigvalOf (Y ω) (hY ω) j = -θ * eigvalOf (Y ω) (hY ω) j := by ring
      rw [hsymm]
      refine le_trans (ENNReal.ofReal_le_ofReal
        (exp_smul_eigvalOf_le_trace_exp (Y ω) (hY ω) (-θ) j)) ?_
      rw [hgsum ω]
      exact le_add_of_nonneg_left (by simp)
  -- Markov and the final arithmetic
  have hcpos : 0 < ENNReal.ofReal (Real.exp (θ * t)) := ENNReal.ofReal_pos.2 (Real.exp_pos _)
  have hmk := measure_mul_le_lintegral μ _ hgmeas (ENNReal.ofReal (Real.exp (θ * t)))
  have hmono : μ {ω | t ≤ ‖Y ω‖} ≤ μ {ω | ENNReal.ofReal (Real.exp (θ * t))
      ≤ ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace
        + (NormedSpace.exp ℝ ((-θ) • Y ω)).trace)} := measure_mono hincl
  have hkey : ENNReal.ofReal (Real.exp (θ * t)) * μ {ω | t ≤ ‖Y ω‖}
      ≤ ∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace
        + (NormedSpace.exp ℝ ((-θ) • Y ω)).trace) ∂μ :=
    le_trans (mul_le_mul_left' hmono _) hmk
  have hint : ∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace
        + (NormedSpace.exp ℝ ((-θ) • Y ω)).trace) ∂μ
      = ∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace) ∂μ
        + ∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ ((-θ) • Y ω)).trace) ∂μ := by
    rw [lintegral_congr hgsum]
    exact lintegral_add_left (hm1.ennreal_ofReal) (fun ω =>
      ENNReal.ofReal ((NormedSpace.exp ℝ ((-θ) • Y ω)).trace))
  have hcc : ENNReal.ofReal (Real.exp (θ * t))
      * ENNReal.ofReal (Real.exp (-(θ * t))) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.exp (θ * t)), ← Real.exp_add]
    have hz : θ * t + -(θ * t) = 0 := by ring
    rw [hz, Real.exp_zero, ENNReal.ofReal_one]
  calc μ {ω | t ≤ ‖Y ω‖}
      = (ENNReal.ofReal (Real.exp (-(θ * t)))
          * ENNReal.ofReal (Real.exp (θ * t))) * μ {ω | t ≤ ‖Y ω‖} := by
        rw [mul_comm (ENNReal.ofReal (Real.exp (-(θ * t))))
          (ENNReal.ofReal (Real.exp (θ * t))), hcc, one_mul]
    _ = ENNReal.ofReal (Real.exp (-(θ * t)))
        * (ENNReal.ofReal (Real.exp (θ * t)) * μ {ω | t ≤ ‖Y ω‖}) := by ring
    _ ≤ ENNReal.ofReal (Real.exp (-(θ * t)))
        * (∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace) ∂μ
          + ∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ ((-θ) • Y ω)).trace) ∂μ) := by
        refine (ENNReal.mul_le_mul_left
          ((ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
          ENNReal.ofReal_ne_top).mpr ?_
        rw [← hint]
        exact hkey

end Master

end Scaffold.Mathlib.Probability.Concentration.Matrix
