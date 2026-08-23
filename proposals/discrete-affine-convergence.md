# Proposal: Discrete Affine-Control Convergence on Finite Vector Spaces

**Status:** **COMPLETE** — both steps delivered in one run on 2026-08-23
(run `20260823T194800Z-run-1`), per this document's own operating
instruction that one run comfortably covers both steps. Zero new
axioms; every declaration composes pinned-Mathlib lemmas (`#print
axioms` reads only the standard three on all three public theorems and
all 25 QA declarations). See "Delivery record" at the end. Original
assessment text follows.

**Assessment:** proposed 2026-08-23/24, priority **High**. `sgt-gaps.md`
item 2, from the independent `spectral-proof` clean-sheet rewrite
project, asks for a finite-dimensional discrete-time convergence
wrapper. Unlike Tikhonov Phase 2 and Heat Phase C (both extensions of
already-delivered Scaffold interfaces), this opens genuinely new scope:
`docs/6_SGT_BACKLOG.md` item 5 ("Graph-dynamical systems") explicitly
gates "consensus maps, synchronization" separately from the heat
semigroup, and states "Consensus maps, synchronization, and general
graph semigroups remain gated" even after the heat-semigroup instance
opened. This proposal is that gate's resolution: a real external
consumer naming the exact interface it needs.

## The claim this document is answering

Not "is this hard" — it is not. The two facts requested are
undergraduate-level: `r^n → 0` for `|r| < 1` (a one-line Mathlib
citation) and a linear affine-iteration convergence theorem (a handful
of lines once the geometric fact is in hand). The question is scope
hygiene: this repository already surveyed and **iceboxed** a
superficially similar-sounding request —
[`icebox/lyapunov-stability-formalization-gap.md`](../icebox/lyapunov-stability-formalization-gap.md)
— for continuous-time ODE trajectory stability, finding neither
Scaffold nor the pinned Mathlib has real ODE-trajectory machinery for
that case. **This request is not that gap.** It is explicitly
discrete-time (`xₙ₊₁ = ...`, a recurrence, not a differential
equation), over a finite-dimensional space (`V → ℝ` for `Fintype V`),
with the base geometric-decay fact already sitting in the pinned
Mathlib. No ODE existence/uniqueness apparatus, no continuous
trajectory, no topology beyond finite Euclidean space is needed. This
document exists to record that distinction explicitly so a future
reader does not conflate this with the iceboxed item.

## The ask, precisely (per `sgt-gaps.md`)

A finite-vector wrapper around the standard scalar fact `r^n → 0` for
`|r| < 1`, suitable for functions `V → ℝ` with finite `V`:

```lean
Filter.Tendsto (fun n : ℕ => r ^ n • x) Filter.atTop (nhds 0)
```

under `|r| < 1`. A companion affine-iteration theorem is welcome:

```lean
xₙ₊₁ = (1 - α) • xₙ + α • equilibrium
```

converges to `equilibrium` for `0 < α` and `α < 2`. The requester's own
framing: "this is textbook finite-dimensional dynamics, and it lets the
rewrite state the controlled transient without rebuilding topology over
finite function spaces."

## Why this axis

`docs/6_SGT_BACKLOG.md` item 5 lists "consensus maps, synchronization"
as gated pending a named SGT consumer, distinct from the heat-semigroup
instance already opened for `reversibility-and-heat-semigroup.md`.
`sgt-gaps.md`'s item 2 is that named consumer for the discrete-affine
half specifically — narrower than "consensus maps" in general (it does
not ask for graph-structured consensus dynamics, network topology, or
synchronization; it asks for scalar/vector geometric decay and one
linear affine-iteration fact, with no graph adjacency structure
anywhere in the statement). This proposal should be read as opening
exactly that narrow slice, not the full "consensus maps, synchronization,
general graph semigroups" gate — those remain gated as before, per the
same discipline `docs/6_SGT_BACKLOG.md`'s 2026-08-19 heat-semigroup note
used ("this opens only the heat-semigroup instance").

## What's already on the shelf

A survey of the pinned Mathlib (2026-08-23/24) and Scaffold:

| Piece needed | Where it lives | Covers |
| --- | --- | --- |
| `r^n → 0` for `\|r\| < 1`, scalar | `Mathlib.Analysis.SpecificLimits.Normed`: `tendsto_pow_atTop_nhds_zero_of_abs_lt_one` | The entire geometric-decay core — already proved, already in the pin |
| Finite-vector smul convergence | **Absent as a named lemma**, but immediate: `Filter.Tendsto.smul` (scalar limit) applied to any constant `x : V → ℝ`, or termwise via `Fintype.tendsto_iff` if a per-entry statement is needed | The genuinely new (but trivial) wrapper this proposal delivers |
| Affine-iteration closed form | **Absent.** `xₙ = (1-α)ⁿ • (x₀ - equilibrium) + equilibrium` by induction, then the geometric-decay fact above applied to `(1-α)ⁿ` under `\|1-α\| < 1 ⟺ 0 < α < 2` | The proposal's second deliverable |
| Continuous-time ODE trajectory calculus | **Iceboxed**, `icebox/lyapunov-stability-formalization-gap.md` | **Not needed here** — this request is discrete-time; the icebox finding does not apply |

## Build order

### Step 1: The finite-vector geometric decay wrapper

```lean
theorem tendsto_pow_smul_atTop_nhds_zero {V : Type*} [Fintype V]
    {r : ℝ} (hr : |r| < 1) (x : V → ℝ) :
    Filter.Tendsto (fun n : ℕ => r ^ n • x) Filter.atTop (nhds 0)
```

Route: `tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr` gives `r^n → 0` in
`ℝ`; `Filter.Tendsto.smul_const` (or the finite-dimensional
`Pi`-space instance of scalar-times-constant continuity) lifts it to
the constant vector `x`. Essentially a one-line composition; the exact
Mathlib API for lifting a scalar limit to a fixed-vector smul in a
finite-dimensional `Pi` space should be confirmed before stating (a
short Step-0-style check, not a separate step).

### Step 2: The affine-iteration convergence theorem

```lean
theorem affineIteration_tendsto_atTop {V : Type*} [Fintype V]
    {α : ℝ} (hα0 : 0 < α) (hα2 : α < 2)
    (x : ℕ → V → ℝ) (equilibrium : V → ℝ)
    (hrec : ∀ n, x (n + 1) = (1 - α) • x n + α • equilibrium) :
    Filter.Tendsto x Filter.atTop (nhds equilibrium)
```

Route: prove the closed form `x n = (1 - α)^n • (x 0 - equilibrium) +
equilibrium` by induction on `hrec` (pure algebra), then apply Step 1
at `r := 1 - α` (`|1 - α| < 1` from `0 < α < 2`) to the `x 0 -
equilibrium` term and conclude via `Filter.Tendsto.add`/`const`.

## QA plan

- Positive witness: a small fixture (`Fin 2` or `Fin 3`) with a
  concrete `α` and `equilibrium`, the iterated sequence computed for a
  few steps and shown numerically approaching `equilibrium`.
- Boundary witness: `α = 2` (the excluded endpoint) refuted — the
  iteration oscillates rather than converging (`1 - α = -1`, the
  geometric factor has modulus exactly `1`), confirming `hα2` is
  load-bearing, not decorative.
- Boundary witness: `α ≤ 0` refuted similarly if a natural counterexample
  exists (`α = 0` is degenerate — the iteration is constant at `x 0`,
  which only converges to `equilibrium` if `x 0 = equilibrium`; worth a
  witness showing this is genuinely a failure of the general claim).

## Operating instructions for an autonomous run

- One run should comfortably cover both steps — this is small,
  well-scoped, textbook material with no open sub-problems, unlike this
  repository's harder discharge programs.
- **No new axioms.** Everything composes Mathlib's existing geometric-decay
  lemma and finite-dimensional continuity/limit API.
- Survey the exact lifting lemma (scalar `Tendsto` to constant-vector
  `smul` in a `Fintype`-indexed `Pi` space) before Step 1 states
  anything, per this repository's standing rule.
- Do not read this proposal as opening the full "consensus maps,
  synchronization, general graph semigroups" gate in
  `docs/6_SGT_BACKLOG.md` item 5 — only the narrow discrete-affine slice
  `sgt-gaps.md` item 2 actually names. If a future request asks for
  graph-structured consensus dynamics, that needs its own named-consumer
  resolution, not an extension of this one.

## Open next step

None — delivered and closed. (Opening text, retained: authorized to
begin immediately — a real external named consumer with no operator
decision pending, per the resolution recorded above.)

## Delivery record (2026-08-23)

Delivered in the new `Scaffold.Mathlib.Dynamics.DiscreteAffine`
(namespace `Scaffold.Dynamics`) and `Scaffold/QA/Dynamics/
DiscreteAffine_QA.lean`, all proved, zero new axioms (count stays 9),
QA 1546 → 1571 (+25, a new `Dynamics` QA domain).

- **Module placement** — a new `Scaffold/Mathlib/Dynamics/` area, not
  the event-driven `GraphTheory/Dynamics.lean`: the statements carry
  no graph structure (this document's own scope note), and that
  module's purpose (time-varying Laplacian perturbation blocks for the
  derived persistence example) is different. Minimal imports (two
  Mathlib analysis/topology files); the umbrella `Scaffold.lean`
  imports it and its docstring records the new slice.
- **Step 1** — `tendsto_pow_smul_atTop_nhds_zero`: `r ^ n • x → 0`
  for `|r| < 1`, exactly the ask, proved in one composed line — the
  pin's `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`
  (`Analysis/SpecificLimits/Normed.lean:197`) lifted through the pin's
  `Filter.Tendsto.smul_const` (`Topology/Algebra/MulAction.lean:109`;
  the survey's "exact Mathlib API should be confirmed" clause
  discharged: `smul_const` is the lifting lemma, and the `0 • x = 0`
  endpoint closes by `zero_smul`).
- **Step 2** — `affineIteration_tendsto_atTop` under
  `hα0 : 0 < α`, `hα2 : α < 2`, with the closed form factored out as
  its own public theorem `affineIteration_eq`
  (`x_n = (1−α)^n • (x_0 − e) + e`, pure module induction, no
  topology), then Step 1 at `r = 1 − α` (`|1−α| < 1` from the pair by
  `abs_lt` + `linarith`) plus `Tendsto.add`/`const`. The consumer's
  exact conclusion shape `Tendsto x atTop (𝓝 equilibrium)`.
- **Statement-shape decision recorded before stating** — all three
  theorems are stated at a general real normed space `E` (the
  closed form at `[AddCommGroup E] [Module ℝ E]` only): the proofs
  never use finiteness or coordinates, the drafted `V → ℝ` /
  `Fintype V` shape is the `E := V → ℝ` instance, and QA instantiates
  exactly that instance — the Tikhonov Section-5 generality precedent.
- **QA (+25, four sections)** — Section A: the decay wrapper by two
  routes (theorem vs. entrywise `tendsto_pi_nhds` +
  per-coordinate `Tendsto.mul` from the pin's scalar lemma — the
  lifting exercised through disjoint API paths) and numeric decay
  instances (`(1/2)^5 • eqm = ![1/32, 1/16]`, `(1/2)^10 • eqm =
  ![1/1024, 1/512]`). Section B: the positive fixture at `α = 1/2`
  (`x_0 = ![3,6]`, `e = ![1,2]`) with the recurrence in the theorem's
  exact hypothesis form, both endpoint hypotheses exhibited, per-step
  values (`![2,4]`, `![3/2,3]`), the closed form pinned from the
  public `affineIteration_eq`, per-coordinate geometric decay
  `|x_n i − e i| = ![2,4] i · (1/2)^n`, and convergence by the two
  independent routes. Section C: the `α = 2` fence — the closed form
  `xosc n = (−1)^n • ![1,0]` through the public theorem, the scalar
  ε-δ refutation (`(−1)^n ↛ 0` at `ε = 1`), and the **proved
  non-convergence** `xosc_not_tendsto_QA`, with `0 < α` still
  satisfied (exactly `hα2` isolated). Section D: the `α = 0` fence —
  constant `![1,0] ≠ 0` **provably not converging** to the
  equilibrium, with `α < 2` still satisfied (exactly `hα0`
  isolated). Both fences follow this document's QA plan verbatim, and
  the two fixtures are complementary: each violates exactly one
  hypothesis while satisfying the other.
- **Pin-technique notes (recorded for future runs)** — the left-dotted
  `Filter.Tendsto.congr` runs `f₁ → f₂`; extracting the reverse
  direction needs the `Filter.tendsto_congr` iff's `.mpr` (namespaced
  under `Filter` at this pin). The affine-induction's `← add_smul`
  fires only after `add_assoc` reassociates `(a + b) + c` — the
  `b + c` subterm is otherwise not a syntactic subterm. Bare
  `![2, 4] i` in a standalone ascription defaults to `ℕ` (the
  recorded numeric-default trap re-hit); ascribe
  `(![2, 4] : Fin 2 → ℝ)`. `norm_num` does not close `|(1:ℝ)/2| < 1`
  directly — `rw [abs_lt]; constructor <;> norm_num` does.
  `Metric.tendsto_atTop`'s ε-δ form is the clean refutation engine
  for non-convergence (`rw` the `dist` away, then `absurd`).
- **Verification** — spike first (`wip/dac_spike.lean`, five rounds to
  green, the fixes becoming the trap list above) then transfer;
  `lake env lean` on the module and the QA file — zero errors, zero
  warnings each; explicit `lake build` targets both ✔;
  `#print axioms` via `wip/dac_axcheck.lean` on all 28 declarations —
  `propext, Classical.choice, Quot.sound` only; full `lake build` ✔
  (2253 targets); `lint_axioms` (**9**, unchanged), `check_citations`,
  `check_markdown_links` pass; scoreboard regenerated
  (**1571/9/0**, idempotent). Backlog item 5's discrete-affine slice
  recorded as opened (consensus maps/synchronization remain gated, per
  this document's scope note).
