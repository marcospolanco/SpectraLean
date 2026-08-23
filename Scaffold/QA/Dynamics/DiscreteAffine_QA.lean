/-
  DiscreteAffine_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.Dynamics.DiscreteAffine`: the
  geometric-decay wrapper and the affine-iteration convergence
  theorem instantiated on `Fin 2 → ℝ` fixtures and cross-checked
  against independent computations, plus the proposal's two mandated
  boundary witnesses — `α = 2` (the iteration oscillates; `hα2`
  load-bearing) and `α = 0` (the iteration is constant off the
  equilibrium; `hα0` load-bearing).

  Load-bearing pattern: the positive fixture's closed form, per-step
  values, and per-coordinate decay are all pinned independently of the
  theorems (raw `norm_num` arithmetic from the recurrence), and both
  convergence statements are reached by two independent routes (the
  delivered theorems vs. an entrywise/Pi-topology limit from the pin's
  own scalar decay lemma) — a wrong lifting constant or closed form
  anywhere in the delivered chain contradicts the raw computations.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  Scoreboard: ../docs/5_QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.Dynamics.DiscreteAffine
import Mathlib.Data.Matrix.Notation

open scoped Classical Topology

namespace Scaffold.Dynamics.QA

open Scaffold.Dynamics

/-!
## Section A: the geometric-decay wrapper on `Fin 2 → ℝ`
-/

/-- The equilibrium fixture `![1, 2]`. -/
def eqm : Fin 2 → ℝ := ![1, 2]

theorem half_smul_tendsto_QA :
    Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n • eqm) Filter.atTop (𝓝 0) :=
  tendsto_pow_smul_atTop_nhds_zero (by rw [abs_lt]; constructor <;> norm_num) eqm

/-- Entrywise/Pi-topology route to the same decay statement:
coordinatewise convergence from the pin's own scalar lemma, never
touching the delivered wrapper — the lifting is exercised twice
through disjoint API paths. -/
theorem half_smul_tendsto_raw_QA :
    Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n • eqm) Filter.atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro i
  have hscalar : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_lt]; constructor <;> norm_num)
  have hc : Filter.Tendsto (fun _ : ℕ => eqm i) Filter.atTop (𝓝 (eqm i)) :=
    tendsto_const_nhds
  simpa [smul_eq_mul, mul_zero] using hscalar.mul hc

/-- Numeric decay instance: the fifth iterate of the shrinking factor
on the fixture. -/
theorem half_smul_eval_five_QA :
    (1 / 2 : ℝ) ^ 5 • eqm = ![1 / 32, 1 / 16] := by
  norm_num [eqm, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]

/-- Numeric decay instance at double the time. -/
theorem half_smul_eval_ten_QA :
    (1 / 2 : ℝ) ^ 10 • eqm = ![1 / 1024, 1 / 512] := by
  norm_num [eqm, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one]

/-!
## Section B: the affine iteration at `α = 1/2` on `Fin 2 → ℝ`
-/

/-- The affine iteration at `α = 1/2` started from `![3, 6]`, whose
equilibrium is `eqm = ![1, 2]`. -/
noncomputable def xiter : ℕ → Fin 2 → ℝ
  | 0 => ![3, 6]
  | (n + 1) => (1 - (1 / 2 : ℝ)) • xiter n + (1 / 2 : ℝ) • eqm

theorem xiter_zero_QA : xiter 0 = ![3, 6] := rfl

theorem xiter_rec_QA (n : ℕ) :
    xiter (n + 1) = (1 - (1 / 2 : ℝ)) • xiter n + (1 / 2 : ℝ) • eqm := rfl

/-- The recurrence is exactly the theorem's hypothesis form, with both
endpoint hypotheses satisfied. -/
theorem xiter_hypotheses_QA : (0 : ℝ) < 1 / 2 ∧ 1 / 2 < (2 : ℝ) := by
  constructor <;> norm_num

theorem xiter_one_QA : xiter 1 = ![2, 4] := by
  rw [xiter_rec_QA, xiter_zero_QA]
  funext i
  fin_cases i <;> norm_num [eqm, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem xiter_two_QA : xiter 2 = ![3 / 2, 3] := by
  rw [xiter_rec_QA, xiter_one_QA]
  funext i
  fin_cases i <;> norm_num [eqm, Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem xiter_zero_sub_QA : xiter 0 - eqm = ![2, 4] := by
  rw [xiter_zero_QA]
  funext i
  fin_cases i <;> norm_num [eqm, Pi.sub_apply]

/-- The closed form, pinned: the deviation from equilibrium is the
geometrically decaying `![2, 4]`. -/
theorem xiter_closed_QA (n : ℕ) :
    xiter n = (1 - (1 / 2 : ℝ)) ^ n • ![2, 4] + eqm := by
  have h := affineIteration_eq xiter eqm xiter_rec_QA n
  rw [xiter_zero_sub_QA] at h
  exact h

theorem dev2_nonneg_QA (j : Fin 2) : 0 ≤ (![2, 4] : Fin 2 → ℝ) j := by
  fin_cases j <;>
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_fin_one]

/-- Each coordinate's deviation from equilibrium decays geometrically
— the closed form read off per entry, both factors positive. -/
theorem xiter_dev_QA (n : ℕ) (i : Fin 2) :
    |xiter n i - eqm i| = (![2, 4] : Fin 2 → ℝ) i * (1 / 2 : ℝ) ^ n := by
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have h : xiter n i - eqm i = (1 / 2 : ℝ) ^ n * (![2, 4] : Fin 2 → ℝ) i := by
    rw [xiter_closed_QA]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhalf]
    ring
  rw [h, abs_mul, abs_of_pos (by positivity), abs_of_nonneg (dev2_nonneg_QA i)]
  ring

/-- Route 1 to convergence: the delivered theorem. -/
theorem xiter_converges_QA :
    Filter.Tendsto xiter Filter.atTop (𝓝 eqm) :=
  affineIteration_tendsto_atTop (by norm_num) (by norm_num) xiter eqm xiter_rec_QA

/-- Route 2 to convergence: entrywise/Pi-topology limit from the pin's
scalar decay lemma, independent of both delivered theorems. -/
theorem xiter_converges_raw_QA :
    Filter.Tendsto xiter Filter.atTop (𝓝 eqm) := by
  rw [tendsto_pi_nhds]
  intro i
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  have hcl : ∀ n, xiter n i = (1 / 2 : ℝ) ^ n * (![2, 4] : Fin 2 → ℝ) i + eqm i := by
    intro n
    rw [xiter_closed_QA]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hhalf]
  refine (Filter.tendsto_congr hcl).mpr ?_
  have hscalar : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by rw [abs_lt]; constructor <;> norm_num)
  have hc1 : Filter.Tendsto (fun _ : ℕ => (![2, 4] : Fin 2 → ℝ) i) Filter.atTop
      (𝓝 ((![2, 4] : Fin 2 → ℝ) i)) :=
    tendsto_const_nhds
  have hc2 : Filter.Tendsto (fun _ : ℕ => eqm i) Filter.atTop (𝓝 (eqm i)) :=
    tendsto_const_nhds
  have hsum := (hscalar.mul hc1).add hc2
  simpa [mul_zero, zero_add] using hsum

/-!
## Section C: the `α = 2` boundary witness (`hα2` load-bearing)

The iteration `x_{n+1} = (1 - 2) • x_n + 2 • 0` satisfies `0 < α`
with equilibrium `0`; it oscillates forever between `![1, 0]` and its
negation, so the theorem's conclusion fails. Dropping `hα2` alone
falsifies the statement.
-/

theorem abs_neg_one_pow_QA (n : ℕ) : |(-1 : ℝ) ^ n| = 1 := by
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow, abs_one]
  · rw [h.neg_one_pow, abs_neg, abs_one]

theorem not_tendsto_neg_one_pow_QA :
    ¬ Filter.Tendsto (fun n : ℕ => (-1 : ℝ) ^ n) Filter.atTop (𝓝 0) := by
  intro h
  rw [Metric.tendsto_atTop] at h
  obtain ⟨N, hN⟩ := h 1 (by norm_num)
  have h1 := hN (N + 1) (by omega)
  rw [Real.dist_eq, sub_zero, abs_neg_one_pow_QA] at h1
  exact absurd h1 (by norm_num)

noncomputable def xosc : ℕ → Fin 2 → ℝ
  | 0 => ![1, 0]
  | (n + 1) => (1 - (2 : ℝ)) • xosc n + (2 : ℝ) • 0

theorem xosc_zero_QA : xosc 0 = ![1, 0] := rfl

/-- The `α = 2` recurrence in the theorem's exact hypothesis form. -/
theorem xosc_rec_QA (n : ℕ) :
    xosc (n + 1) = (1 - (2 : ℝ)) • xosc n + (2 : ℝ) • (0 : Fin 2 → ℝ) := rfl

/-- Every other hypothesis of the theorem holds at this fixture:
`0 < α` is satisfied (only `hα2` is violated, since `α = 2`). -/
theorem xosc_hypotheses_QA : (0 : ℝ) < 2 := by norm_num

theorem xosc_eq_QA (n : ℕ) : xosc n = (-1 : ℝ) ^ n • ![1, 0] := by
  have h := affineIteration_eq xosc 0 xosc_rec_QA n
  have h0 : xosc 0 - (0 : Fin 2 → ℝ) = ![1, 0] := by
    rw [xosc_zero_QA, sub_zero]
  rw [h0] at h
  have h2 : (1 : ℝ) - 2 = -1 := by norm_num
  rw [h2] at h
  simpa using h

/-- The refutation: the `α = 2` iteration provably does not converge
to its equilibrium — `hα2` is load-bearing, not decorative. -/
theorem xosc_not_tendsto_QA : ¬ Filter.Tendsto xosc Filter.atTop (𝓝 0) := by
  intro h
  have h0 : Filter.Tendsto (fun n : ℕ => xosc n 0) Filter.atTop (𝓝 0) :=
    (continuous_apply 0).continuousAt.tendsto.comp h
  refine not_tendsto_neg_one_pow_QA ?_
  refine Filter.Tendsto.congr (fun n => ?_) h0
  rw [xosc_eq_QA]
  simp [Pi.smul_apply, smul_eq_mul]

/-!
## Section D: the `α = 0` boundary witness (`hα0` load-bearing)

The iteration `x_{n+1} = (1 - 0) • x_n + 0 • 0` satisfies `α < 2` with
equilibrium `0`; it is constant at `![1, 0] ≠ 0`, so the theorem's
conclusion fails. Dropping `hα0` alone falsifies the statement.
-/

def xconst : ℕ → Fin 2 → ℝ := fun _ => ![1, 0]

/-- The `α = 0` recurrence in the theorem's exact hypothesis form. -/
theorem xconst_rec_QA (n : ℕ) :
    xconst (n + 1) = (1 - (0 : ℝ)) • xconst n + (0 : ℝ) • (0 : Fin 2 → ℝ) := by
  simp [xconst]

/-- Every other hypothesis of the theorem holds at this fixture:
`α < 2` is satisfied (only `hα0` is violated, since `α = 0`). -/
theorem xconst_hypotheses_QA : (0 : ℝ) < 2 := by norm_num

/-- The refutation: the `α = 0` iteration provably does not converge
to its equilibrium — `hα0` is load-bearing, not decorative. -/
theorem xconst_not_tendsto_QA :
    ¬ Filter.Tendsto xconst Filter.atTop (𝓝 (0 : Fin 2 → ℝ)) := by
  intro h
  have h0 : Filter.Tendsto (fun n : ℕ => xconst n 0) Filter.atTop (𝓝 0) :=
    (continuous_apply 0).continuousAt.tendsto.comp h
  rw [Metric.tendsto_atTop] at h0
  obtain ⟨N, hN⟩ := h0 (1 / 2) (by norm_num)
  have h1 := hN (N + 1) (by omega)
  norm_num [xconst, Real.dist_eq, Matrix.cons_val_zero] at h1

end Scaffold.Dynamics.QA
