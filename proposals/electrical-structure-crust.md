# Proposal: Grow the Crust Through Electrical Structure

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-17. Authorizes no Lean changes, axiom admissions, document rewrites,
or external publication.

Companion to [Prove One Named Inequality](prove-cheeger-easy-direction.md).
That proposal argues for *shrinking the mushy center*; this one takes the
opposite premise — the center stays fixed — and asks where the hard crust
should grow. The two are independent and either may be adopted alone.

Assessed from the repository as of this date: `Scaffold/Mathlib/GraphTheory/Spectral.lean`,
`docs/6_SGT_BACKLOG.md` (items 3, 4, 7), `docs/7_SGT_RADAR.md`, and the
Mathlib pin in `lakefile.lean` (v4.14.0).

## Recommendation

Grow the crust into **combinatorial and electrical structure** — the radar's
axis 6, currently scored 0.5 and described as entirely absent.

## Why this axis

It is the one major SGT neighborhood whose core theorems are provable with
**no axioms at all**. This is structural, not accidental: Cheeger, Weyl,
Davis–Kahan, and interlacing are hard to formalize because they are
inequalities requiring real analysis. Electrical network theory is largely
algebra — linear solves, energy identities, completing the square. It is the
largest theorem-dense region reachable without touching the mushy center.

It also composes with the repository's strongest existing asset. The proved
Dirichlet identity `laplacian_quadForm` (`Spectral.lean:531`),

```
quadForm (laplacian A) x = (∑ i, ∑ j, A i j * (x i - x j)^2) / 2
```

*is* the electrical energy. Every resistance theorem below is a consumer of
that single identity. This satisfies the center-out policy in
[Strategy](../docs/1_STRATEGY.md) on its merits — it builds on the most
load-bearing proved statement in the repository rather than beside it — and
it answers backlog item 7's gate by naming the consumers up front.

## Build order

### 1. Connectivity and the kernel characterization (the hinge)

`laplacian_ones_in_kernel` (`Spectral.lean:127`) gives one direction; the
converse is absent, and `Spectral.lean` has no notion of connectivity at all.
The needed statement: for a connected graph, `ker (laplacian A)` is *exactly*
the constants.

Proof path: from the Dirichlet identity, `quadForm L f = 0` forces
`f i = f j` across every edge of positive weight; propagate along walks.

Build this first regardless of what follows. It is load-bearing well beyond
this proposal — effective-resistance well-definedness, `λ₂ > 0`, any Fiedler
interface (backlog item 4), and any mixing-time statement (item 5) all
depend on it.

### 2. Effective resistance by the potential equation

The Mathlib pin (v4.14.0) has no Moore–Penrose pseudoinverse, so define
resistance by the equation it solves rather than by `L⁺`:

```
IsEffectiveResistance A u v r  ↔  ∃ f, laplacian A *ᵥ f = e u - e v ∧ f u - f v = r
```

Well-definedness is a corollary of step 1: two solutions differ by a kernel
element, which is constant, so `f u - f v` is unique. This introduces no new
Mathlib dependency and sidesteps the pseudoinverse gap rather than waiting on
it.

### 3. The energy identity

`R u v = quadForm (laplacian A) f` — one step from `laplacian_quadForm` and
the defining equation. Near-free corollaries: symmetry `R u v = R v u`,
nonnegativity, and `R u u = 0`.

### 4. Rayleigh monotonicity and the Dirichlet principle

Adding conductance never increases effective resistance; `1/R` is the
minimum energy over potentials normalized by `f u - f v = 1`. Both are
completing-the-square arguments over the energy identity.

### 5. Foster's theorem (gated stretch)

`∑ over edges, A i j * R i j = n - 1` for connected graphs. Requires a
rank/trace fact not currently present; admit as a slice only after steps 1–4
land, and do not admit it as an axiom.

**Net effect:** five to six proved theorems, axiom count unchanged at 18,
axis 6 moving off 0.5 on genuine usable coverage.

## Second recommendation: `SimpleGraph` adapters

Cheaper, and it is the crust that makes the rest of the crust *importable*.
The radar already records this as the standing interoperability deviation:
the representation is matrix-first, and no Mathlib user holds a `WAdj` — they
hold a `SimpleGraph V`.

Deliver `SimpleGraph.toWAdj` with proved `deg = G.degree`, symmetry, and
`boundary S` equal to the edge count across the cut. Unglamorous, but it
converts every theorem already in the repository into something an outside
user can call, and it is the prerequisite that makes
[the traction plan](../docs/traction-plan.md) executable at all. Highest
compounding multiplier available.

## What not to grow

- **QA breadth on modules that already have it.** `Exhaustive_QA` is past
  the point of diminishing returns; further sweeps add declarations, not
  assurance.
- **Axis 8 (adjacent systems).** Deliberately gated, and the gate is
  correct.

## Open next step

Scope step 1 — the connectivity/kernel characterization — in detail: the
connectivity predicate to adopt (native or `SimpleGraph.Connected` via the
adapter), and the walk-propagation argument's Lean shape.
