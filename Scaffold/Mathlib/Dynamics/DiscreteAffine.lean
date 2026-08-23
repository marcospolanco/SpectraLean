/-
  DiscreteAffine.lean

  Purpose
  -------
  Discrete-time finite-vector dynamics: the geometric-decay wrapper for
  scalar powers acting on a vector, and the convergence theorem for
  linear affine iterations toward an equilibrium.

  This module is the delivered interface of
  `proposals/discrete-affine-convergence.md` (the Active priority
  table's High row of 2026-08-23/24, `sgt-gaps.md` item 2 — the
  external `spectral-proof` clean-sheet rewrite project's named
  consumer), and it opens the discrete-affine slice of
  `docs/6_SGT_BACKLOG.md` item 5 ("Graph-dynamical systems"):
  consensus maps, synchronization, and general graph semigroups remain
  gated as before. Per that proposal's own scope note, the statements
  carry no graph structure — hence this standalone `Dynamics` area
  rather than the event-driven `GraphTheory/Dynamics.lean`, whose
  purpose (time-varying Laplacian perturbation blocks for the derived
  persistence example) is different.

  Everything here is proved hard crust from the pinned Mathlib; there
  are no Scaffold axioms above the standard three. The two load-bearing
  pin lemmas (located by the proposal's Step-0-style survey,
  re-verified against the pin on delivery):

  - `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`
    (`Mathlib/Analysis/SpecificLimits/Normed.lean:197`): `r ^ n → 0`
    for `|r| < 1` — the entire geometric-decay core.
  - `Filter.Tendsto.smul_const`
    (`Mathlib/Topology/Algebra/MulAction.lean:109`): a convergent
    scalar sequence acting on a fixed vector converges to the limit
    acting on that vector — the scalar-to-vector lifting step.

  Statement-shape decision (recorded before stating): the theorems are
  stated for an arbitrary real normed space `E`, not only for
  `V → ℝ` at `Fintype V`. The proofs never use finiteness or a
  coordinate decomposition, the proposal's requested finite-vector
  shape is the `E := V → ℝ` instance, and QA instantiates exactly
  that case. This follows the shelf's generality precedent
  (`GraphTheory.Tikhonov` Section 5's symmetric-matrix carrier).
-/

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.MulAction

open scoped Topology

namespace Scaffold.Dynamics

/-!
## 1. The finite-vector geometric decay wrapper

QA: `Scaffold.QA.Dynamics.DiscreteAffine_QA` (`half_smul_tendsto_QA`,
`half_smul_tendsto_raw_QA`).
-/

/-- Geometric decay acting on a fixed vector: for `|r| < 1`, the
sequence `r ^ n • x` converges to `0`. The proposal's Step 1
(`sgt-gaps.md` item 2): the pin's scalar fact
`tendsto_pow_atTop_nhds_zero_of_abs_lt_one` lifted to vectors through
`Filter.Tendsto.smul_const`. Valid in any real normed space; the
consumer's finite-vector form is the `E := V → ℝ` instance. -/
theorem tendsto_pow_smul_atTop_nhds_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {r : ℝ} (hr : |r| < 1) (x : E) :
    Filter.Tendsto (fun n : ℕ => r ^ n • x) Filter.atTop (𝓝 0) := by
  simpa [zero_smul] using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr).smul_const x

/-!
## 2. The affine-iteration convergence theorem

QA: `Scaffold.QA.Dynamics.DiscreteAffine_QA` (`xiter_closed_QA`,
`xiter_dev_QA`, `xiter_converges_QA`, `xiter_converges_raw_QA`,
`xosc_not_tendsto_QA`, `xconst_not_tendsto_QA`).
-/

/-- The closed form of a linear affine iteration
`x_{n+1} = (1 - α) • x_n + α • e`: the deviation from the equilibrium
`e` decays geometrically, `x_n - e = (1 - α) ^ n • (x_0 - e)`. Pure
module algebra (induction on the recurrence); no topology. -/
theorem affineIteration_eq {E : Type*} [AddCommGroup E] [Module ℝ E] {α : ℝ}
    (x : ℕ → E) (e : E) (hrec : ∀ n, x (n + 1) = (1 - α) • x n + α • e) :
    ∀ n, x n = (1 - α) ^ n • (x 0 - e) + e := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [hrec, ih, smul_add, smul_smul, add_assoc, ← add_smul]
      have h1 : (1 : ℝ) - α + α = 1 := by ring
      rw [h1, one_smul]
      congr 1
      rw [mul_comm, ← pow_succ]

/-- Convergence of a linear affine iteration to its equilibrium: for
`0 < α < 2`, any sequence satisfying `x_{n+1} = (1 - α) • x_n + α • e`
converges to `e`. The proposal's Step 2: the closed form
`affineIteration_eq` plus geometric decay of `(1 - α) ^ n` (note
`|1 - α| < 1` is exactly `0 < α < 2`). Both endpoint hypotheses are
load-bearing — QA refutes the conclusion at `α = 2` (oscillation,
`xosc_not_tendsto_QA`) and at `α = 0` (constancy off the equilibrium,
`xconst_not_tendsto_QA`). -/
theorem affineIteration_tendsto_atTop {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (x : ℕ → E) (equilibrium : E)
    (hrec : ∀ n, x (n + 1) = (1 - α) • x n + α • equilibrium) :
    Filter.Tendsto x Filter.atTop (𝓝 equilibrium) := by
  have hr : |1 - α| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  refine (Filter.tendsto_congr (affineIteration_eq x equilibrium hrec)).mpr ?_
  have h := tendsto_pow_smul_atTop_nhds_zero hr (x 0 - equilibrium)
  simpa [zero_add] using h.add tendsto_const_nhds

end Scaffold.Dynamics
