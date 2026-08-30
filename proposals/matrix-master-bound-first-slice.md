# The Matrix Master Bound: Retirement Route, First Slice

**Status:** COMPLETE (Lean delivered 2026-08-30 by run
`20260830T202747Z-run-1`, independently re-verified by the operator at
commit `0a1cb8c`; records ladder written 2026-08-30 by run
`20260830T221307Z-run-1`)
**Type:** Trust-surface reduction (priority item 4) — the first proved
slice of the matrix concentration retirement route; zero new axioms
(count stays 5)

## Summary

The retirement of the three admitted matrix concentration axioms
(`matrix_hoeffding`, `matrix_bernstein`, `matrix_azuma_hoeffding` —
axioms 5 → 2 if the route completes) needs two engines. This slice
delivers the first as **pure hard crust**: Tropp's Proposition 3.1, the
Laplace-transform master bound that every matrix concentration proof
consumes, in its two-sided spectral-norm form

```lean
theorem matrix_master_bound {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [Nonempty V] {Y : Ω → Matrix V V ℝ} (hY : ∀ ω, (Y ω).IsSymm)
    (h_meas : StronglyMeasurable Y) {θ : ℝ} (hθ : 0 ≤ θ) (t : ℝ) :
    μ {ω | t ≤ ‖Y ω‖} ≤
      ENNReal.ofReal (Real.exp (-(θ * t))) *
        (∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ (θ • Y ω)).trace) ∂μ +
         ∫⁻ ω, ENNReal.ofReal ((NormedSpace.exp ℝ ((-θ) • Y ω)).trace) ∂μ)
```

together with its deterministic core, the trace-exponential spectral
identity `tr (exp (θ•M)) = ∑ i, exp (θ·λᵢ(M))` for real-symmetric `M` —
the identity the pinned Mathlib's own
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` lists as an
open TODO beside its determinant sibling (verified absent before this
delivery). The proof conjugates through the spectral theorem's unitary
diagonalization, `Matrix.exp_conj`, and `Matrix.exp_diagonal` — the
exp-carrying extension of the shelf's `eigvalOf_sum_eq_trace` route.

The second engine — the sum-MGF step (Tropp's Theorem 6.1, Lieb's
concavity of the trace exponential, `E tr e^{H+X} ≤ tr e^{H + log E e^X}`)
— is **not** here: it is genuinely deeper, multi-run, and gated on an
operator decision between admitting the analytic core and proving it.
That gate is the route's standing handoff.

## Why this slice, and what it is load-bearing on

- **Every** matrix concentration retirement step consumes this bound:
  Hoeffding, Bernstein, and Azuma proofs alike are Chernoff assemblies
  over the Laplace-transform step. The scalar retirement pattern
  (engine before statement: `hoeffding_lemma_mgf` → the tail
  statements; `bennett_mgf` → the Bernstein pair) applied to the
  matrix side starts here.
- `trace_exp_smul_eq_sum_exp_eigvalOf` is load-bearing on the exact
  spectral-theorem route: a wrong conjugation, a wrong diagonal
  exponential, or a wrong eigenvalue spelling breaks the identity's
  value at the QA fixture, where it is pinned against an independent
  diagonal-route computation.
- `exists_abs_eigvalOf_ge` (the norm–eigenvalue attainment bridge) is
  load-bearing on `l2OpNorm_le_of_abs_eigvalOf_le` — the same operator-
  norm bridge the shelf's Weyl retirement built — and fails at exactly
  the degenerate corner the fence below records.
- The Markov step is stated on the **lower integral** with no
  integrability hypothesis — honest for unbounded summands, the same
  idiom the admitted matrix axioms' `ℝ≥0∞` statements use.

## Degenerate-corner analysis (recorded before the statement landed)

The §5 hazard-class check ran at design time, and found the same corner
class the 2026-08-28 matrix-trio repair did:

- **Empty index type:** at `V = ∅`, `Y ≡ 0`, `θ = 0`, `t = 0`, the tail
  event is all of `Ω` (`0 ≤ ‖0‖` trivially) while both trace sums are
  **empty** sums — the bound reads `1 ≤ 0`. The `[Nonempty V]` guard is
  present at birth, and the corner is fenced in QA
  (`master_bound_fin0_unguarded_refuted_QA`, the un-guarded conclusion
  deriving `False`) — the same `Fin 0` refutation shape the repaired
  axioms carry, closed here through the vacuous instantiation of
  `l2OpNorm_le_of_abs_eigvalOf_le` (at `V = ∅` no eigenvalue can
  attain a nonnegative threshold, so `exists_abs_eigvalOf_ge` — and
  with it the inclusion step — genuinely needs nonemptiness).
- **Measure mass:** the bound is monotone in `μ` on both sides (no
  normalization is used or needed); no probability-measure guard is
  required, and none is imposed.
- **Junk integrals:** the only integrals are **lower** integrals of a
  nonnegative measurable function (`trace_exp_nonneg` supplies
  nonnegativity from the eigenvalue sum); `lintegral` has no
  junk-value mechanism, so the §5 junk-integral hazard class does not
  reach this statement.
- **`θ = 0`:** allowed (`0 ≤ θ`): the bound degenerates to
  `μ {t ≤ ‖Y‖} ≤ 1 + 1` — true, and the statement does not pretend
  otherwise.

## Delivered

1. **Shelf**
   (`Scaffold/Mathlib/Probability/Concentration/Matrix/MasterBound.lean`,
   all proved, zero axioms): the deterministic section
   (`trace_exp_smul_eq_sum_exp_eigvalOf`, `trace_exp_nonneg`,
   `exp_smul_eigvalOf_le_trace_exp`), the measurability section
   (`continuous_trace_exp` — at the locally-convex `l∞` operator-norm
   instances, whose topology is the canonical product topology;
   `stronglyMeasurable_trace_exp`), the Markov helper
   (`measure_mul_le_lintegral`), the attainment bridge
   (`exists_abs_eigvalOf_ge`), and `matrix_master_bound` itself.
2. **QA** (`Scaffold/QA/Concentration/Matrix_QA.lean`'s MasterBoundQA
   section, +5, 3167 → 3172): the diagonal fixture `diag (0, 2)` with
   eigenvalues pinned by trace and determinant **independent of the
   new identity**; the trace-exponential computed directly by the
   diagonal route (`trace_exp_diag_direct_QA`, any scale `w`); the
   identity's value joined to that pin at `θ = 1` and `θ = −1` (a
   wrong eigen-expansion breaks the agreement); the two-sided norm pin
   `‖diagD‖ = 2`; the **constant-design instance**
   `master_bound_diag_constant_QA` (`Y ≡ diagD`, `θ = 1`, `t = 2`: the
   tail event all of `Ω`, the bound computing to
   `e^{−2}((1+e²) + (1+e^{−2}))` and proved **≥ 1** — the `e²` term
   pays for itself, the instance non-vacuous); and the
   `Fin 0` un-guarded refutation fence.
3. **Records:** this proposal, the `proposals/README.md` Delivered row,
   README/radar QA syncs (3172), the probability-concentration index
   map's master-bound section, the Tropp source index's Proposition 3.1
   row, both map stat stamps + regenerated SVG, the scoreboard
   verification row, the execution plan, and the activity log.

## Verification

The Lean was delivered by run `20260830T202747Z-run-1` and
independently re-verified by the operator (commit `0a1cb8c`):

- `lake build` clean (2407/2407 targets);
  `check_build_completeness.py` — 130 source files, 130 fresh
  artifacts, 0 stale, 0 missing, exit 0.
- **`#print axioms` on all 13 new declarations** (8 shelf + 5 QA) via
  `wip/verify_masterbound.lean`: every one exactly
  `propext, Classical.choice, Quot.sound` — pure hard crust, zero new
  axiom contact.
- `lint_axioms` unchanged at 5 (both findings the pre-existing
  allowlisted PF pair — no axiom surface touched); `check_citations`
  and `check_markdown_links` pass; `sorry`/`admit` sweep on both
  touched files clean.

The records ladder (this run) re-ran the docs-side ladder:
scoreboard regeneration (**3172/5/0**), `lint_axioms`,
`check_citations`, `check_markdown_links`, map-freshness after the
3167 → 3172 stamp sync in both map files, and build-completeness
confirmation on the unchanged tree.

## What is deliberately not here

The sum-MGF step (Lieb-class). Retiring the matrix trio outright needs
`E tr e^{θY}` bounded by a deterministic quantity — Tropp's Theorem 6.1
via Lieb's concavity, or an equivalent exchangeable-pair/moment method.
That machinery is a genuine multi-run program, and the choice between
admitting its analytic core (Golden–Thompson/Lieb as cited axioms —
`icebox/`'s Golden-Thompson candidate is exactly this) and proving it
is an operator decision, not a default. Until then the trio stays
admitted, honestly: every conditional Derived tail remains conditional
on its own axiom and must never be described as foundationally proved.

## Follow-ons (priced, not owed)

- **Step 2 — the sum-MGF gate:** the operator decision above; only
  after it can a second bounded slice be scoped.
- **A `θ`-optimization interface** over the master bound (Tropp's
  `inf_θ` collapsed to the consumer's variance statistic) — cheap once
  a consumer names its statistic, per the named-consumer rule.
