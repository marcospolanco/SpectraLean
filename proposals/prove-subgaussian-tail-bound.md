# Proposal: Prove the Subgaussian Tail Bound

**Status:** Proposed 2026-08-22, not yet surveyed against the pinned
Mathlib tree by an actual Lean session — the findings below come from
reading the axiom and a repository-wide grep for the ingredients, not
from a spike. This document authorizes no Lean changes, axiom removals,
or records edits on its own; a run must still open its own Step 0 before
touching `Subgaussian.lean`.

Assessed from
`Scaffold/Mathlib/Probability/Concentration/Scalar/Subgaussian.lean`
(`subgaussianNorm`, `hoeffding_lemma`, `subgaussian_tail_bound`) and the
pinned Mathlib's `MeasureTheory/Integral/Bochner.lean` and
`MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean`.

## Why this axiom, not one of the other nine

Ten axioms remain (`docs/5_QA_SCOREBOARD.md`). The Cheeger hard
direction is out of scope for a "low-hanging" search —
`discharge-perturbation-axioms.md` already calls it known-hard, not
merely unexplored. The three matrix-valued concentration axioms
(`matrix_hoeffding`, `matrix_bernstein`, `matrix_azuma_hoeffding`) need
trace-exponential machinery (Golden–Thompson, Lieb's concavity) that
`spectral-graph-sparsification.md` already found "neither remotely
available" in this pin — not a place to start. The two sum-of-variables
axioms (`hoeffding_inequality`, `bernstein_inequality`) look tempting
because Mathlib has real MGF machinery
(`ProbabilityTheory.IndepFun.mgf_add`), but their hypothesis is only
**pairwise** independence
(`∀ i j, i ≠ j → IndepFun (X i) (X j) μ`), while the standard proof
needs the MGF of a sum of more than two variables to factor into a
product — `IndepFun.mgf_add` is two-at-a-time, and pairwise independence
does not generally give the mutual independence a finite induction over
more than two terms would need. That mismatch needs its own Step 0
before anyone touches either axiom; it is not scoped by this proposal.

`subgaussian_tail_bound` has none of these problems: it is a
single-variable statement (no independence hypothesis of any kind), and
its "distribution" is Scaffold's own `subgaussianNorm`, already a real
definition (an `sInf`), not itself axiomatized.

## The finding

`subgaussianNorm X μ := sInf {K : ℝ | 0 < K ∧ ∫ ω, exp(X ω ^ 2 / K ^ 2) ∂μ ≤ 2}`.
The target axiom is exactly the "moment condition implies tail bound"
direction of Vershynin's Proposition 2.5.2 (the definition's own
docstring already cites this proposition for `hoeffding_lemma`'s
constant-loss disclaimer) — the *easier* of that proposition's two
directions; the reverse (tail bound implies a moment bound) is not
needed here and should not be attempted as a shortcut.

The route is direct Markov's inequality on the nonnegative function
`ω ↦ exp(X ω ^ 2 / K ^ 2)`, applied at the tail event
`{ω | t^2/K^2 ≤ X ω ^ 2 / K^2}`:

- **Markov's inequality itself is on the shelf**, general-measure, no
  probability-measure instance required (this file's `μ` carries none):
  `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` (`Integral/
  Bochner.lean:1646`) — `ε * (μ {x | ε ≤ f x}).toReal ≤ ∫ x, f x ∂μ` for
  `f` a.e.-nonnegative and integrable. Applied at
  `f := fun ω => exp(X ω ^ 2 / K ^ 2)` and
  `ε := exp(t^2/K^2)`, this gives almost exactly the target after
  converting `.toReal`/`ENNReal.ofReal` and the event
  `{|X ω| ≥ t} = {X ω ^ 2 ≥ t^2}` (`sq_le_sq'`/`abs_le` territory, not
  free but routine).
- **The real plumbing is getting from `h_sub : subgaussianNorm X μ ≤ K`
  to the two facts Markov's inequality needs at that exact `K`**:
  integrability of `exp(X² / K²)` and the bound `∫ exp(X²/K²) ≤ 2`.
  Neither is handed to us — the hypothesis only bounds an infimum, and
  the defining set's witnesses are at whatever `K'` happen to satisfy
  the moment condition, not necessarily at `K` itself. Two small lemmas
  close this gap, and both are genuine (if short) proofs, not
  one-liners:
  1. **Monotonicity in `K`.** If `K' ≤ K` (both positive) then
     `X ω ^ 2 / K ^ 2 ≤ X ω ^ 2 / K'^2` pointwise (dividing a
     nonnegative quantity by a larger positive number), hence
     `exp(X²/K²) ≤ exp(X²/K'²)` pointwise (`Real.exp_le_exp` +
     monotonicity of division), hence `∫ exp(X²/K²) ≤ ∫ exp(X²/K'²)`
     (`MeasureTheory.integral_mono_ae` or `integral_mono_of_nonneg`,
     needing integrability of the dominating function — see below) —
     so the defining set `{K : 0 < K ∧ ∫ exp(X²/K²) ≤ 2}` is
     upward-closed once one point is known integrable-and-bounded.
  2. **Reaching the exact target `K` from `sInf ≤ K`.** If `K` equals
     the infimum exactly and the infimum is not itself attained, no
     finite `K'` in the defining set is `≤ K`, so upward-closure alone
     does not immediately place `K` in the set — this needs a limiting
     argument (approach `K` from above by set members and use
     `MeasureTheory.integral_mono_ae`'s dominated-convergence-adjacent
     machinery, or `Filter.Tendsto` continuity of `K ↦ ∫ exp(X²/K²)` at
     `K`, to transfer the `≤ 2` bound to the limit). If `K` is strictly
     above the infimum, a single witness `K' ∈ (subgaussianNorm X μ, K]`
     plus monotonicity suffices and the limiting case does not arise.
     Record whichever route is actually taken; do not assume the easy
     (strict-inequality) case covers the axiom's exact hypothesis
     (`≤`, not `<`).
  3. **Integrability transfers the same way**: `exp(X²/K²)` is
     dominated pointwise by `exp(X²/K'²)` for `K ≥ K' > 0`, so
     integrability at a witness `K'` gives integrability at `K` via
     `MeasureTheory.Integrable.mono'` — needed before Markov's
     inequality's own `hf_int` hypothesis can be discharged, and before
     the monotonicity step above can invoke `integral_mono_ae` (which
     itself needs an integrable dominating function).

None of this is exotic — it is finite real-analysis plumbing around an
`sInf`, structurally similar to how `retire-sherman-morrison.md` found
its rank-one specialization to be "real, but not hard" work rather than
a free corollary. Treat it the same way here: real, self-contained,
Mathlib-only, but not a one-line `exact`.

## Scope

1. **Step 0 (mandatory, not done by this document):** open a Lean
   session, confirm `mul_meas_ge_le_integral_of_nonneg`'s exact current
   signature against this pin (cited above from a text search, not a
   compiled check), and spike the two small lemmas above in a scratch
   file before touching the public module. Record the actual route
   taken for the `K = sInf` boundary case (§ finding, point 2) — it is
   the one genuinely open question this proposal does not resolve in
   advance.
2. Prove `subgaussian_tail_bound` at its **existing name, hypotheses,
   and conclusion** — no restatement, per this repo's standing Step 1
   contract (see `discharge-perturbation-axioms.md`'s Step 1 section for
   the precedent).
3. QA: the existing `subgaussian_tail_bound_zero_QA` fixture should
   still exercise the proved theorem unchanged; add one more instance
   with a genuinely nonzero `K`/`t` pair where the bound is not trivially
   satisfied (avoid a second vacuous-or-degenerate witness).
4. Update the scoreboard, `index/sources/vershynin_hdp.md` (already the
   citation source for this axiom's Chapter 2 material — this becomes
   its first proved-not-axiom row for this specific statement), and the
   explicit axiom count.

## Acceptance criteria

- No `axiom`, `sorry`, or `admit` introduced.
- The proved theorem's module and its QA elaborate directly; standard
  hygiene checks (`lint_axioms`, `check_citations`,
  `check_markdown_links`) and a full `lake build` pass.
- Axiom count decreases by one.
- The delivery record states explicitly which route closed the
  `K = sInf` boundary case (§ finding, point 2), since this proposal
  does not resolve it in advance.

## Non-goals

- `hoeffding_lemma` is a different axiom in the same file with a
  similar `subgaussianNorm`-mediated shape; it is *not* scoped by this
  proposal even though it looks adjacent — it goes the other direction
  (a bounded, zero-mean variable *has* small `subgaussianNorm`, i.e. the
  harder direction of the Proposition 2.5.2 equivalence this proposal
  deliberately avoids) and would need its own Step 0.
- `hoeffding_inequality` / `bernstein_inequality` (the pairwise-vs-mutual
  independence question above) are explicitly out of scope here.
