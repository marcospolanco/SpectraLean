# Proposal: Electrical Flows, Thomson's Principle, and Rayleigh Monotonicity

**Status:** Proposed; **priority:** High. Requested 2026-08-18 as the
center-to-ICP follow-on to the delivered electrical-structure crust. This
document authorizes no Lean changes, axiom admissions, commits, clean-room
copying, or external publication on its own.

Companion to [Grow the Crust Through Electrical
Structure](electrical-structure-crust.md), whose six delivered steps provide
effective resistance, potential solvability and uniqueness, the energy
identity, and the one-sided Dirichlet bound with zero admitted axioms. This
proposal turns that potential-based API into a routing object: an electrical
unit flow with a conservation law and a minimum-energy guarantee.

Assessed from `Scaffold/Mathlib/GraphTheory/{Spectral,Electrical,
SimpleGraphAdapter}.lean`, `Scaffold/QA/SpectralGraph/EffectiveResistance_QA.lean`,
[Strategy](../docs/1_STRATEGY.md)'s center-out and load-bearing tests,
[Traction Plan](../docs/traction-plan.md)'s initial audience, and the public
sources below.

## Clean-room boundary

This planning document is not itself exportable: it contains internal
prioritization, repository paths, and delivery history. If counsel approves a
new public repository, restate the program independently from the public
electrical-network results cited below. Do not copy this proposal or consult
the ignored `spectral-proof/` area when recreating the theorem statements or
proofs.

## Recommendation

Formalize a finite electrical-flow interface and prove:

1. a unit-demand potential induces a unit flow satisfying Kirchhoff
   conservation;
2. the flow's dissipated energy equals effective resistance;
3. **Thomson's principle:** the electrical unit flow minimizes energy among
   all unit flows with the same source and sink; and
4. **Rayleigh monotonicity:** increasing edge conductances cannot increase
   effective resistance.

The ICP-facing result is concise:

> Adding network capacity cannot worsen the certified energy cost of
> electrical routing.

## Why this is High

The traction plan chooses Lean and Mathlib contributors as the initial
audience and names effective-resistance-based routing or load-balancing as the
strongest concrete integration problem. The current module proves resistance
through potentials, but it does not yet expose a flow that a routing proof can
consume. This proposal closes exactly that gap.

It also satisfies the center-out leverage test unusually well:

- **zero new trust:** every target should be proved from finite sums, ordered
  fields, and the existing zero-axiom electrical module;
- **load-bearing depth:** the proof depends on the exact Laplacian sign
  convention, unit-demand equation, symmetry, support graph, energy identity,
  and effective-resistance agreement theorem;
- **reusable interface:** flows, divergence, energy, and monotonicity are
  useful to routing, random walks, network comparison, sparsification, and
  future load-balancing analyses;
- **outside-facing demonstration:** a small capacity-reinforcement theorem is
  more legible to an adopter than another isolated matrix lemma; and
- **upstream shape:** Mathlib already has graph Laplacians but, per the dated
  coverage map, lacks graph-native electrical resistance and flow theory.

This ranks above the current Medium items for the next autonomous milestone:
Fiedler Phase B inherits the admitted Cheeger hard direction, while the full
mixing-time program is broader and requires new Markov/metric infrastructure.

## Calibration

Three sharp edges, each detailed in place below where it bears on a specific
definition or proof step — summarized here so a reader sees all three before
touching any code, not scattered as surprises across the document:

- **Orientation direction.** Scaffold's weights `A i j` are conductances, not
  resistances. `A ≤ B` must yield
  `effectiveResistance B u v ≤ effectiveResistance A u v` — the inequality
  runs the *other* way if stated in resistance terms. Reversing it is a
  statement bug, not a notation choice; see "Public scientific anchors"
  below.
- **The zero-conductance trap.** Lean's `x / 0 = 0` convention means an
  unguarded energy formula lets a competitor flow route current through a
  zero-conductance pair for free, which makes Thomson's principle false, not
  merely inelegant. The `IsFlowOn` support condition exists specifically to
  close this; see "Zero conductances" under "Representation decisions."
- **The `1/2` double-counting factor.** Flows are represented on ordered
  pairs, so every undirected edge is summed twice; the factor is mandatory,
  not cosmetic, and QA must contain a fixture that fails without it. See
  "Directed-pair double counting" under "Representation decisions."

None of these are reasons to expect new axioms — the "zero new trust" claim
in "Why this is High" still stands — they are reasons a correct-looking
proof could silently prove the wrong statement if any one of them is missed.

## Public scientific anchors

- Peter G. Doyle and J. Laurie Snell, *Random Walks and Electric Networks*,
  MAA, 1984; freely redistributed 2006 edition:
  [author-hosted PDF](https://math.dartmouth.edu/~doyle/docs/walks/walks.pdf).
  Section 1.3.5, “Currents minimize energy dissipation” (PDF pp. 47–50),
  defines unit flows and proves Thomson's principle. Section 1.4.1,
  “Rayleigh's Monotonicity Law” (PDF pp. 51–54), derives monotonicity from
  Thomson's principle.
- Russell Lyons and Yuval Peres, *Probability on Trees and Networks*,
  Cambridge University Press, 2016:
  [author-hosted book page and corrected editions](https://rdlyons.pages.iu.edu/prbtree/).
  Chapter 2 treats electrical networks, Thomson's principle, and Rayleigh
  monotonicity in conductance notation.

These sources use both resistance and conductance conventions. Scaffold's
weights `A i j` are **conductances**. Therefore `A ≤ B` must yield
`effectiveResistance B u v ≤ effectiveResistance A u v`; reversing this
orientation is a statement bug, not a cosmetic notation choice.

## Current substrate

The needed inner results are already proved:

- `laplacian_mulVec_apply`: pointwise weighted divergence;
- `laplacian_quadForm`: Dirichlet energy as a weighted squared-difference
  sum;
- `exists_laplacian_mulVec_eq_single_sub_single`: a unit-demand potential
  exists on a connected graph;
- `laplacian_mulVec_eq_zero_iff_forall_reachable`: kernel vectors are
  componentwise constant;
- `quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single`: a unit-demand
  solution's energy is its voltage drop;
- `effectiveResistance_eq_quadForm`: the resistance equals the harmonic
  potential's energy;
- `effectiveResistance_ge_sq_div_quadForm`: the already-proved one-sided
  Dirichlet inequality; and
- `SimpleGraph.toWAdj` / `supportGraph`: both interoperability directions.

The missing object is the edge flow itself.

## Representation decisions

Make these decisions explicitly before writing the public API. The recommended
first representation is matrix-shaped because it composes directly with
`WAdj`, `Matrix.mulVec`, and finite sums:

```lean
abbrev EdgeFlow (V : Type) := Matrix V V ℝ

def electricalCurrent (A : WAdj) (f : V → ℝ) : EdgeFlow V :=
  fun i j => A i j * (f i - f j)

def flowDivergence (θ : EdgeFlow V) (i : V) : ℝ :=
  ∑ j, θ i j
```

Use named predicates rather than burying validity hypotheses in every theorem:

```lean
def IsFlowOn (A : WAdj) (θ : EdgeFlow V) : Prop :=
  (∀ i j, θ i j = -θ j i) ∧
  (∀ i j, A i j = 0 → θ i j = 0)

def IsUnitFlow (A : WAdj) (u v : V) (θ : EdgeFlow V) : Prop :=
  IsFlowOn A θ ∧
  (fun i => flowDivergence θ i) = Pi.single u 1 - Pi.single v 1
```

Names may change to match Mathlib conventions after the required survey, but
the semantics may not drift.

### Zero conductances

Flow energy divides squared current by conductance. It must therefore be total
without treating a zero-conductance pair as a free route. Use an explicit
zero branch together with the `IsFlowOn` support condition:

```lean
noncomputable def flowEnergy (A : WAdj) (θ : EdgeFlow V) : ℝ :=
  (∑ i, ∑ j, if A i j = 0 then 0 else (θ i j) ^ 2 / A i j) / 2
```

The support predicate is load-bearing: without it, a nonzero current on a
zero-conductance pair contributes zero energy and makes Thomson's principle
false.

### Directed-pair double counting

Flows are represented on ordered pairs, so every undirected edge occurs
twice. The factor `1/2` in `flowEnergy` is mandatory. QA must contain a fixture
that would fail if this factor were omitted.

### Graph hypotheses

The first theorem shapes should require:

- symmetric weights;
- nonnegative weights;
- connected support graph; and
- valid supported antisymmetric competitor flows.

Do not generalize to disconnected graphs until the connected theorem and its
QA are complete. The current total `effectiveResistance` has a documented
junk value off its solvable domain, so an over-general statement could silently
prove a fact about the fallback rather than resistance.

## Build order

### 0. Survey and pin the representation

Before editing Lean, search the pinned Mathlib for finite network-flow,
divergence, circulation, antisymmetric-edge-function, and energy definitions.
Update [Mathlib Coverage Map](../docs/8_MATHLIB_COVERAGE_MAP.md) if the dated
claim that graph-native electrical structure is absent is stale.

Choose between `Matrix V V ℝ` and a function on oriented `supportGraph` edges.
Prefer the matrix form unless the survey reveals an upstream oriented-edge API
that materially reduces the proof and conversion cost. Record the choice and
its zero-edge semantics before stating a theorem.

#### Decision (recorded 2026-08-19, before any Lean in this program)

**Survey of the pinned Mathlib (v4.14.0), re-run 2026-08-19:**

- No network-flow, max-flow/min-cut, or circulation declaration anywhere
  (`networkflow|network_flow|maxflow|maxFlow|min_cut|circulation`: zero hits).
- No graph-native divergence: the only `Divergence` material is the box- and
  measure-integral divergence *theorem* on `ℝⁿ`-style domains
  (`Analysis/BoxIntegral/DivergenceTheorem.lean`,
  `MeasureTheory/Integral/DivergenceTheorem.lean`) — analysis on continua,
  with nothing discrete or finite-graph.
- No electrical-network API: zero hits for `electric`, `Kirchhoff`, or
  `Thomson`; the `Rayleigh` hits are number theory and the Rayleigh
  *quotient* (`Analysis/InnerProductSpace/Rayleigh.lean` — operator
  theory, unrelated to monotonicity); no `conductance`, no `resistance`.
  Confirms the coverage map's electrical row (absent) — row evidence
  extended with the flow/divergence specifics, same date.
- The only oriented-edge API is `SimpleGraph.Dart` (a bundled `V × V` with
  an adjacency proof; `symm`, `edge`, counting uses). It carries no flow,
  divergence, or energy API, and a dart-indexed flow would force converting
  `WAdj` weights through `supportGraph` (which drops self-loop weights by
  looplessness) at every interface, with no upstream consumer of the
  conversion. No `Matrix.IsAntiSymm` exists in the pin, so antisymmetry is
  stated as a plain quantifier in `IsFlowOn` as proposed.

**Decision:** the matrix representation `EdgeFlow V := Matrix V V ℝ` exactly
as sketched above (`electricalCurrent`, `flowDivergence`, `IsFlowOn`,
`IsUnitFlow` at the proposal's semantics; divergence stated as the function
equality `flowDivergence θ = Pi.single u 1 − Pi.single v 1`, which is the
sketch's `(fun i => flowDivergence θ i) = …` in curried form). Zero-edge
semantics: support is the `IsFlowOn` second conjunct (current may not ride a
zero-conductance ordered pair); `flowEnergy` (step 2) takes the explicit
zero branch with the mandatory `1/2` ordered-pair factor. **Target module:**
a focused new `Scaffold.Mathlib.GraphTheory.ElectricalFlow` importing
`GraphTheory.Electrical` — `Electrical.lean` keeps its resistance scope
bounded, and the flow interface has its own growth path (energy, Thomson,
monotonicity).

**Step 1 delivered 2026-08-19 (same run, after this decision):**
`electricalCurrent_antisymm`, `electricalCurrent_eq_zero_of_weight_eq_zero`,
`flowDivergence_electricalCurrent`
(`flowDivergence (electricalCurrent A f) = laplacian A *ᵥ f`),
`isFlowOn_electricalCurrent`, and the headline
`isUnitFlow_electricalCurrent` (a unit-demand potential induces a unit
flow), plus QA `SpectralGraph/ElectricalFlow_QA.lean` (see the delivery
notes in the execution plan). No new axioms; steps 2–5 not started.

**Step 2 delivered 2026-08-19 (separate run):** `flowEnergy` defined
exactly as pinned above (explicit zero branch, mandatory `1/2`
ordered-pair factor), with `flowEnergy_electricalCurrent`
(the energy agreement with `quadForm (laplacian A) f`),
`flowEnergy_nonneg`, and
`flowEnergy_electricalCurrent_eq_effectiveResistance` (a unit-demand
current dissipates exactly the resistance it routes, on a connected
graph). QA delivered the mandatory double-counting fixture (raw
ordered-pair sum computes to `2 ≠ 1` = the Dirichlet energy on the unit
edge, so omitting the `1/2` factor would break the agreement
numerically — QA plan item 4), the deferred energy-level zero-edge
refutation (QA plan item 5: the step-1 phantom's zero energy pinned,
plus a Thomson-breaking refinement — an antisymmetric unit-divergence
flow routing through zero-conductance pairs on a
real-edge-plus-isolated-vertex network dissipates `0 < 1` = the real
resistance, and is excluded by the support conjunct alone), the energy
values of QA plan items 1 and 3 (`1` on the edge, `2` on the path,
each cross-checked against independently computed Dirichlet energies
and pinned resistance values), and a hypothesis-set witness (below).
No new axioms; steps 3–5 not started.

**Statement-shape deviation (recorded):** the proposal said the
agreement proof "must use nonnegative weights and handle zero weights
explicitly." The zero weights are handled explicitly — the termwise
identity matches the zero branch to the vanishing weight — but the
*nonnegativity hypothesis is not needed*: on a nonzero conductance the
algebra `(c·x)²/c = c·x²` is pure field algebra. `flowEnergy_electricalCurrent`
is therefore stated at **symmetry-only** strength (that is what
`laplacian_quadForm` requires). QA witnesses both sides of this claim:
the agreement instantiates on a symmetric *negative*-weight network
(both sides compute to `-1`), where `flowEnergy_nonneg` — which does
hypothesize nonnegativity — provably fails. QA plan item 2 (capacity
increase `1 → 2`) belongs to step 4 and was not started.

**Step 3 delivered 2026-08-19 (separate run):** Thomson's principle —
`effectiveResistance_le_flowEnergy`
(`effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow
`θ` on a connected graph with symmetric nonnegative conductances) —
proved exactly by the proposed route: the difference `d = θ − ι`
between the competitor and the unit-demand potential's current is a
flow (`isFlowOn_sub`) with zero divergence
(`flowDivergence_sub` + the Kirchhoff bridge + the demand equation),
the superposition lemma
`flowEnergy_add_of_flowDivergence_eq_zero` adds `d`'s energy to `ι`'s
(discrete integration by parts kills the cross term: Ohm's law turns
it into `∑ i j, (f i − f j) * d i j`, whose row sums vanish by zero
divergence and whose column sums are the negated row sums by
antisymmetry), and `flowEnergy_nonneg` discards it; `ι`'s energy is the
resistance by the step-2 identity. No `sInf` packaging, per the
proposal's instruction — attainment is witnessed by the constructed
electrical flow. **Statement-shape deviation (recorded):** the
superposition lemma is stated with **no hypotheses on `A` at all** —
not even the symmetry the proposal's proof sketch assumed throughout:
only the perturbation's flow properties (support, antisymmetry, zero
divergence) enter, since Ohm's law needs no symmetry to cancel one
conductance. QA (18 new declarations): attainment at the edge
(`1 = 1`) and — the step-3-specific witness — at the *split* current on
the triangle `K₃` (`R = 2/3` = the current's energy, both computed from
the raw definitions, the current genuinely splitting `2/3`/`1/3` across
the two routes); a **strict competitor** (the detour unit flow around
the two-edge path: valid `IsUnitFlow` with all conjuncts computed,
energy `2`, Thomson instantiated as `2/3 < 2` — the inequality is not
vacuous on a network with competing routes); and the superposition
decomposition composed (`2 = 2/3 + 4/3`, all three energies computed
independently of the lemma). No new axioms; steps 4–5 not started.

**Step 4 delivered 2026-08-19 (separate run):** Rayleigh monotonicity
in conductance form — `effectiveResistance_le_of_le`: for two connected
symmetric nonnegative networks with entrywise `A ≤ B`,
`effectiveResistance B u v ≤ effectiveResistance A u v`, with the
conductance orientation exactly as the calibration section binds (the
QA **orientation guard** refutes the reverse direction numerically on
the capacity-increase fixture: `1 ≤ 1/2` is false). Route exactly as
proposed, through two new reusable interfaces: `isFlowOn_of_le`
(flow-space growth — a flow supported on `A` is a flow on every
`B ≥ A ≥ 0`; support load-bearing: a `B`-zero entry above a
nonnegative `A` entry squeezes the latter to zero, so the transferred
current carries nothing there) and `flowEnergy_le_of_le` (raising
conductances lowers dissipated energy — termwise `θ²/B ≤ θ²/A` on
nonzero branches since every denominator increased; support load-bearing
a second time on the `A i j = 0 < B i j` branch, where the `B`-term
would otherwise exceed the zeroed `A`-branch — the same zero-conductance
trap as steps 2–3, now guarding the comparison). The headline composes
them: the `A`-unit-demand potential's current is a unit flow *on `B`*
(growth + the Kirchhoff bridge), Thomson's principle on `B` bounds
`R_B` by its `B`-energy, the comparison bounds that by its `A`-energy,
and the step-2 identity evaluates it as `R_A` — load-bearing on
solvability, the Kirchhoff bridge, support, Thomson, and the energy
identity. Connectivity of both graphs is hypothesized, per the
proposal's initial-shape instruction; the optional adapter deriving
`supportGraph B`'s connectivity from `A`'s and `A ≤ B` was **not**
attempted (kept non-blocking, as the proposal requires; it is the
natural packaging companion if step 5's reinforcement theorem wants a
one-hypothesis shape). QA (20 new declarations): the proposal's QA item
2 — conductance `1 → 2` on the unit edge, the resistance decrease
`1 → 1/2` certified from an independent potential witness, monotonicity
instantiated, the decrease certified strict, and the orientation guard;
the competitor transfer instantiated on computed objects (the
`edgeAdj`-current is a unit flow on `edge2Adj`, cross-network energy
`1/2 ≤ 1` computed from the raw definitions on both sides); and a
partial increase on the triangle — one edge's conductance doubled,
resistance strictly `2/3 → 2/5`, the new value pinned by the
independent potential `![2/5, 0, 1/5]`. No new axioms; step 5 not
started.

### 1. Electrical current and Kirchhoff conservation

Add the flow definitions and prove:

- `electricalCurrent_antisymm` for symmetric `A`;
- `electricalCurrent_eq_zero_of_weight_eq_zero`;
- `flowDivergence_electricalCurrent`, namely
  `flowDivergence (electricalCurrent A f) = laplacian A *ᵥ f`; and
- `isUnitFlow_electricalCurrent` whenever
  `laplacian A *ᵥ f = eᵤ - eᵥ`.

This is the smallest independently useful slice. It turns the existing
potential equation into a routing conservation theorem without introducing
variational machinery.

### 2. Energy agreement

Prove that electrical-current energy agrees with the Laplacian quadratic form:

```lean
flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f
```

The proof must use nonnegative weights and handle zero weights explicitly. For
a unit-demand potential, derive:

```lean
flowEnergy A (electricalCurrent A f) = effectiveResistance A u v
```

This is load-bearing on the exact `1/2` convention in both the current energy
and `laplacian_quadForm`.

### 3. Thomson's principle

For every valid unit flow `θ` from `u` to `v`, prove:

```lean
effectiveResistance A u v ≤ flowEnergy A θ
```

Recommended proof: obtain the electrical unit current `ι` from the existing
unit-demand potential and set `d = θ - ι`. Both flows have the same divergence,
so `d` is divergence-free. Expand
`flowEnergy A (ι + d)`; discrete integration by parts makes the cross term
zero, and the remaining `flowEnergy A d` is nonnegative.

Do not package this first as an `sInf` equality. The universal inequality plus
the already-constructed attaining electrical flow is the smaller, more usable
API. An infimum corollary may follow only if a named consumer needs it.

### 4. Rayleigh monotonicity in conductance form

For two connected symmetric nonnegative conductance matrices with
entrywise `A ≤ B`, prove:

```lean
effectiveResistance B u v ≤ effectiveResistance A u v
```

Use the electrical unit flow for `A` as a competitor in `B`. Its `B`-energy is
at most its `A`-energy because every denominator increased; Thomson's principle
for `B` supplies the other inequality.

Initially require connectivity for both graphs. A later convenience theorem may
derive connectivity of `supportGraph B` from connectivity of `supportGraph A`
and `A ≤ B`, but that adapter lemma must not block the headline theorem.

### 5. ICP proof example

Add one short downstream theorem or QA fixture phrased as capacity
reinforcement:

```lean
-- schematic
effectiveResistance (increaseConductance A i j δ) u v
  ≤ effectiveResistance A u v
```

The example should use `SimpleGraph.toWAdj` or a small weighted matrix and be
short enough for release documentation. It must remain a theorem in Lean, not
an informal numerical claim.

## QA and falsification plan

QA must be independent enough to expose convention errors:

1. **Single edge:** compute its electrical current, divergence, energy, and
   resistance as `1`.
2. **Capacity increase:** compare weight `1` with weight `2`; certify resistance
   decreases from `1` to `1/2` and instantiate Rayleigh monotonicity.
3. **Path:** compute the unit flow and energy `2`, exercising the sum over more
   than one edge.
4. **Double-counting guard:** prove the raw ordered-pair sum is twice the
   intended energy on the single edge.
5. **Zero-edge support guard:** construct an antisymmetric matrix carrying
   current on a zero-weight pair and show why dropping `IsFlowOn` would give a
   spurious zero-energy competitor.
6. **Symmetry guard:** use an asymmetric weight matrix to show that
   `electricalCurrent` need not be antisymmetric without `A.IsSymm`.

No QA proof may contain `sorry` or `admit`, and QA demonstrates the interface
relative to its proved dependencies; it is not evidence imported from the
quarantined application.

## Deferred

- Multicommodity flow, congestion ratios, oblivious routing, and competitive
  analysis. These are outer application work and need separate consumer-driven
  proposals after the single-commodity interface is credible.
- Infinite networks, recurrence/transience, and measure-theoretic flows.
- Randomized rounding or executable routing algorithms. The current library is
  noncomputable and the traction plan explicitly excludes a general engineering
  audience until an extraction path exists.
- Moore–Penrose-pseudoinverse formulas. The pinned Mathlib lacks the required
  pseudoinverse API, and the potential/flow route is already sufficient.
- A full effective-resistance metric package and triangle inequality. Useful,
  but not needed for the routing-energy and monotonicity demonstration.
- An `sInf`/`argmin` packaging of Thomson's principle unless an actual consumer
  needs that exact shape.

## Operating instructions for an autonomous run

- One numbered build step per run; step 3 may be split if the discrete
  integration-by-parts lemma deserves its own reusable interface.
- **No new axioms.** If the proof route encounters missing elementary algebra,
  finite-sum, or order machinery, prove the bridge locally or record the exact
  blocker; do not admit Thomson or Rayleigh as assumptions.
- Survey Mathlib before defining the flow representation and correct the
  coverage map if needed.
- Directly elaborate every changed module and its closest QA consumer, then run
  the standard hygiene suite and full build.
- Keep the flow module narrow. Do not begin multicommodity routing or mixing
  time in the same run.
- Record all statement-shape deviations, especially conductance orientation,
  zero-edge semantics, and the `1/2` double-counting factor.
- Do not copy source, names, comments, or proof ideas from `spectral-proof/`.

## Acceptance criteria

- A neutral public flow API with explicit antisymmetry, support, divergence,
  and energy semantics.
- A proved Kirchhoff bridge from unit-demand potentials to unit flows.
- A proved energy identity for electrical current.
- A proved Thomson minimum-energy inequality and an attaining electrical flow.
- A proved conductance-form Rayleigh monotonicity theorem with the correct
  inequality direction.
- Capacity-reinforcement QA that can serve as the release's short proof example.
- Negative-witness QA for zero-edge support, symmetry, and double counting.
- No new `axiom`, `sorry`, or `admit`; changed modules, QA, hygiene scripts, and
  `lake build` all pass.
- Scoreboard, SGT index, radar evidence, execution plan, and this proposal's
  delivery record updated only after verified milestones land.

## Open next step

Run build step 0 only: survey the pinned Mathlib, choose and document the flow
representation, and identify the exact target module (`GraphTheory.Electrical`
extension versus a focused `GraphTheory.ElectricalFlow`). Do not begin Lean
implementation until that representation decision is recorded.
