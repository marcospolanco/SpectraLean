# Proposal: Discrete Affine-Control Convergence on Finite Vector Spaces

**Status:** Proposed — 2026-08-23/24, priority **High**. `sgt-gaps.md`
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

Authorized to begin immediately — this is a real external named
consumer with no operator decision pending, per the resolution recorded
above.
