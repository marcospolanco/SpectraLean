# The Retirement of `primitive_power_tendsto` — the Doeblin/Dobrushin Contraction Route

**Status:** COMPLETE (same-run proposal, delivered 2026-09-02 by run
`20260902T052318Z-run-1`, session `ses_f9f72cfc9ffeqGbyE8xuzCFttV`)  
**Type:** Trust-surface reduction (priority item 4) — one of the five
admitted axioms converted to a proved theorem at its **unchanged
statement**; axiom count 5 → 4.

## Summary

`primitive_power_tendsto` (admitted 2026-08-24,
`proposals/primitive-power-convergence.md`) stated: powers of a
primitive row-stochastic matrix converge entrywise to the rank-one
stationary projector, `(P ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` at any nonnegative
mass-one stationary `π`. Its docstring's "Replacement path" note
recorded that "no dedicated local proof route is currently priced" —
retirement would come from upstream Mathlib or from a stronger local
Perron–Frobenius suite (spectral projectors, periodicity
decomposition), itself unpriced.

That pricing missed an elementary route that needs **no**
Perron–Frobenius machinery at all — the classical
**Doeblin/Dobrushin coefficient contraction**:

1. Primitivity supplies a strictly positive power `Q = P^m`
   (`Matrix.IsPrimitive`'s own definition), and finiteness supplies
   `δ > 0` with every entry of `Q` `≥ δ`
   (`exists_pos_le_of_finite`).
2. Splitting each row as `δ` (a uniform part) plus a remainder of row
   mass `1 - |V|·δ`, every entry of `Q *ᵥ y` lands in the *common*
   interval `[δ·∑y + (1-|V|δ)·inf y, δ·∑y + (1-|V|δ)·sup y]` — the
   uniform part shifts all entries equally, leaving only the
   remainder's convex-combination spread. Hence the entrywise range
   contracts: `range (Q *ᵥ y) ≤ (1 - |V|δ) · range y`
   (`entryRange_mulVec_le_of_pos_entries`, the headline engine
   lemma).
3. Iterating over `q` blocks with plain stochastic non-expansiveness
   on the `t mod m` remainder gives
   `range (P^t *ᵥ x) ≤ ρ^(t/m) · range x` for `ρ = 1 - |V|δ ∈ [0, 1)`
   (`entryRange_pow_mul_le`); `|V|δ ≤ 1` falls out of row
   stochasticity itself.
4. The π-pairing is invariant (`π ⬝ᵥ (P^t *ᵥ x) = π ⬝ᵥ x` by
   stationarity, `Matrix.dotProduct_mulVec`), and — being a convex
   combination of the entries — it lies inside the same (vanishing)
   range interval as every entry. So
   `|(P^t *ᵥ x) i − π ⬝ᵥ x| ≤ ρ^(t/m) · range x → 0`, uniformly in
   `i`: a direct ε–N convergence proof in the Π topology.

`#print axioms` on the retired statement: exactly `propext,
Classical.choice, Quot.sound`.

## Why this, and why now

- **Priority item 4** (reduce the explicit trust surface): a whole
  axiom eliminated, and with it the *conditional* status of the entire
  directed mixing layer — `pageRank_powerIteration`,
  `pageRank_entrywise_tendsto`, `pageRank_walk_tendsto`
  (`GraphTheory.DirectedMixing`), and both generic corollaries
  (`primitive_entrywise_tendsto`, `primitive_vecMul_tendsto`) are now
  hard crust at unchanged statements (`#print axioms` on all of them:
  the standard three — 41 audited declarations in total via
  `wip/primpow_axcheck.lean`).
- **The mechanism is reusable, not bespoke**: `entrySup`/`entryInf`/
  `entryRange` and the contraction land as public lemmas — the same
  Dobrushin-contraction family the undirected uniform-`t_mix`
  delivery built its submultiplicativity class on, now available for
  any stochastic matrix action. The `P₂` periodicity fence
  (`P2_no_limit_QA`) stays live against the (now proved) statement's
  hypothesis set: `hprim` remains exactly what separates convergence
  from oscillation.
- **Honest scope after the retirement** (recorded in the module
  docstring): the statement still carries **no rate clause**; the
  proof's byproduct rate `ρ^(t/m)` is the Doeblin bound — explicit
  but typically far from sharp. The *sharp* `|λ₂|`-type rate still
  needs the complex spectral theory of non-symmetric matrices and
  remains a separate future admission gated on a named consumer.
- **Selection context**: no High rows in the Active table (all
  Low/blocked on human decisions); the standing queue's named items
  are consumer-less (reverse TV → χ²) or operator-gated
  (log-Sobolev adoption, the Python bridge, matrix master-bound
  Step 2 — Lieb concavity); the prior milestone (the cycle family)
  is delivered and steward-verified.

## The delivery

### Shelf (`Scaffold/Mathlib/LinearAlgebra/PrimitiveConvergence.lean`)

- The `Doeblin` section (public, `[Fintype V]`-scoped, the pure range
  lemmas `omit [DecidableEq V]`-decorated): `entrySup`/`entryInf`/
  `entryRange` with the membership/nonnegativity interface; the
  interval lemmas (`mulVec_le_entrySup`, `entryInf_le_mulVec`,
  `entryInf_le_dotProduct`, `dotProduct_le_entrySup` — convex
  combinations stay in range); **stochastic non-expansiveness**
  `entryRange_mulVec_le`; **the contraction**
  `entryRange_mulVec_le_of_pos_entries` (no nonnegativity hypothesis
  needed — the coefficient `Q i j − δ ≥ 0` comes from the entries
  bound itself); the power plumbing (`pow_nonneg_entries`,
  `pow_row_sum` — the sum form of `pow_mulVec_one`, which moved ahead
  of the engine for dependency order — and
  `vecMul_pow_eq_of_vecMul_eq`); `exists_pos_le_of_finite`; and the
  block iteration `entryRange_pow_mul_le`.
- **`primitive_power_tendsto`**: `axiom` → `theorem` at the identical
  statement and binder set, proof as above; the module docstring's
  trust-boundary section rewritten as the retirement record.

### QA (`Scaffold/QA/SpectralGraph/DirectedMixing_QA.lean`, Section E; +19, 3618 → 3637)

On the strictly positive row-stochastic fixture
`Qd = !![3/4, 1/4; 1/4, 3/4]` (min entry `1/4`, so the Doeblin
coefficient is `ρ = 1 − 2·(1/4) = 1/2`) with the antisymmetric test
vector `yd = ![1, −1]` (range `2`) and the uniform stationary `ud`:

- **The contraction attained exactly**: `range (Qd *ᵥ yd) = 1 =
  (1 − 2·(1/4)) · 2` — the strongest QA shape a bound theorem can
  have, load-bearing on the exact coefficient (a wrong constant —
  `1 − δ` alone, or `1 − |V|δ` at a wrong cardinality — breaks the
  pin).
- **The exact closed form** `Qd ^ t *ᵥ yd = (1/2)^t • yd` (induction
  through `Matrix.mulVec_smul`), giving the **iterated contraction
  attained at every time** and the raw closed-form tendsto to zero,
  independent of the theorem.
- **The theorem's instance** at the fixture, joined to the closed form
  at the zero limit (`ud ⬝ᵥ yd = 0`).
- **The wrong-δ refutation fence**: a pretend `δ = 1/2` (larger than
  the true min entry) would claim zero range after one step —
  `1 ≤ 0` at the pinned values — with the entries-bound hypothesis
  exactly what fails (`Qd 0 1 = 1/4 < 1/2`, proved).
- Bookkeeping: the retired axiom's `-- @refutes` tag removed from
  `mass_one_unsat_card_zero_QA` (tags name only currently admitted
  axioms; the lemma stays as the corner record), the `lint_axioms.py`
  allowlist entry for the axiom removed, and the file/module
  docstrings de-staled (the Section A/D lemmas and `DirectedMixing`'s
  three theorems are hard crust now, and their notes say so).

## Verification

- Spike first (`wip/primpow_spike.lean` — the engine, the retired
  statement under a primed name (the axiom still occupied the name),
  the full QA section, and the audit, iterated to zero errors/zero
  warnings before any shelf edit).
- `lake env lean` zero errors/zero warnings on all three touched
  modules (`PrimitiveConvergence.lean`, `DirectedMixing_QA.lean`,
  `DirectedMixing.lean` — the last docstring-only); the QA module's
  elaboration met the documented stale-olen boundary once
  (QA-imports-shelf), remediated by building the shelf target first.
- Explicit `lake build` targets ✔ on all three.
- **`#print axioms` via `wip/primpow_axcheck.lean` on 41
  declarations** — the 17 new engine members, the retired theorem, the
  7 formerly-conditional consumers, and 16 QA members — **every one
  exactly `propext, Classical.choice, Quot.sound`**: the directed
  mixing layer's admitted-axiom contact is zero.
- **Full `lake build` ✔ immediately followed by
  `check_build_completeness.py` — 133 source files, 133 fresh
  artifacts, 0 stale, 0 missing, exit 0.**
- `lint_axioms` exit 0 — and the count line now reads **4 current
  axioms** (`matrix_azuma_hoeffding`, `matrix_bernstein`,
  `matrix_hoeffding`, `perron_frobenius`), the only remaining finding
  the allowlisted-confirmed `perron_frobenius` corner.
- `check_refutation_independence` (9-tag clean — the tenth tag was
  this axiom's, removed with the retirement);
  `check_public_reachability` clean (63 repo modules);
  `check_citations` ("All axioms have proper citations!");
  `check_markdown_links` clean; `check_backlog_freshness` clean;
  scoreboard regenerated (**3637/4/0**).

## What is deliberately not here

- **A sharp rate.** The proof's `ρ^(t/m)` is the Doeblin bound;
  sharp `|λ₂|`-type rates still need non-symmetric complex spectral
  theory, gated on a named consumer exactly as before.
- **Operator-norm convergence** (only Π/entrywise topology), unchanged
  from the admission's scope.
- **`perron_frobenius`'s retirement** — a genuinely different
  statement (irreducible case, Perron data), with no comparable
  elementary route known; its allowlisted degenerate corner stands.

## Technique findings (for the next run)

- **`Finset.univ.eq_empty_or_nonempty` poisons later elaboration.**
  Dot notation on the unqualified `Finset.univ` leaves a postponed
  *stuck* `Fintype ?m` instance that surfaces as an unrelated-looking
  error several declarations or obtains later ("typeclass instance
  problem is stuck … often due to metavariables" at a line far from
  the cause). Fix: ascribe — `Finset.eq_empty_or_nonempty
  (Finset.univ : Finset V)`.
- **`Finset.le_sup'`/`inf'_le` take the function first** in this pin:
  `Finset.le_sup' (fun i => y i) (Finset.mem_univ i)`; `le_inf'`
  additionally takes `Finset.univ_nonempty` explicitly. The older
  remembered shapes (membership alone) produce confusing "expected
  Type" errors.
- **`(Finset.sum_mul).symm` and kin fail with "invalid field
  notation, type is not of the form (C …)"** when the lemma's other
  arguments are still metavariables — write `by rw [Finset.sum_mul]`
  in calc steps instead.
- **`by`-block arguments need `show`-typed goals** when sibling
  arguments pin the implicit variables: `exists_pow_lt_of_lt_one
  (show 0 < ε / D by positivity) (show ρ < 1 by linarith)` — a bare
  `(by linarith)` elaborates against `?y < 1` and fails vacuously or
  leaves stuck metavars.
- **`pow_succ` vs `pow_succ'` pick the association.** In
  `(A ^ (t+1)) *ᵥ v = A *ᵥ (A ^ t *ᵥ v)`, only `pow_succ'`
  (`a^(n+1) = a * a^n`) matches `Matrix.mulVec_mulVec`'s
  `(M * N) *ᵥ v = M *ᵥ (N *ᵥ v)`; `pow_succ` strands a matrix
  commutation goal that is false in general.
- **`lt_or_eq_of_le (h : 0 ≤ x)` yields `0 = x` in the equality
  branch** — `rw [h]` hunts for a `0` pattern and fails on
  numeral-bearing goals; `rw [← h]` is the robust direction.
- **`fin_cases` on `Fin 2` leaves raw `⟨0, ⋯⟩` literals** that
  `norm_num [def]` evaluates but `simp only [def]` does not — vector
  and matrix literal evaluation goes through `norm_num`, and
  `(norm_num [yd]; try linarith)` covers both the closed and the
  hypothesis-carrying case shapes (a bare `; linarith` errors with
  "no goals" when norm_num closes the goal first).
- **`omit [DecidableEq V] in` must precede the docstring** (docstring
  between the omit line and the theorem parses; docstring before the
  omit line does not) — confirming the earlier recorded finding.
- **Matrix-power lemmas need `[DecidableEq V]`** (the `Monoid
  (Matrix V V ℝ)` instance carries it) while the pure range engine
  does not — splitting the section and omitting per-declaration keeps
  both warning-free.
- **`Metric.dist_eq` does not exist in this pin** — `Real.dist_eq`
  (`dist x y = |x − y|`).
