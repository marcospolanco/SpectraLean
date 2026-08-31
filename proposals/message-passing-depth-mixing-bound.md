# Proposal: Certified Message-Passing Depth Bounds from Mixing (Over-Squashing)

**Status:** Proposed. New Lean derivation from already-proved primitives;
no new axioms.

**Provenance:** New-capability menu item #2, chosen by the operator
2026-08-30 alongside item #3 (`spectral-graph-sparsification-gnn-training.md`).

## The capability

Over-squashing in deep GNNs — the phenomenon where a fixed-width hidden
representation cannot faithfully carry the combinatorially-growing
information from a node's `r`-hop neighborhood — is understood in the ML
literature (Topping et al. 2021, "Understanding over-squashing and
bottlenecks on graphs via curvature") as fundamentally a bottleneck/mixing
phenomenon: the sensitivity of node `v`'s representation after `r` rounds
of message passing to node `u`'s initial features is controlled by
quantities like `(P^r)_{uv}` — a power of the propagation operator — which
is exactly the object random-walk mixing-time theory bounds.

This proposal derives a certified **lower bound on the number of
message-passing rounds needed** before information originating at node `x`
can produce more than a stated noise threshold `ε` of influence on node
`y`'s aggregated representation — an "over-squashing floor," directly
usable as an architecture-design tool: *given this graph's certified
spectral gap, you need at least this many layers for node `y` to receive a
detectable signal from node `x`.*

## Honest scope: what this bounds and what it doesn't

This targets the **linearized, mean-aggregation propagation operator** —
repeated application of the random-walk transition matrix, which is what a
linear GCN-style layer computes up to a learned weight matrix and
nonlinearity at each step — not a full nonlinear, multi-channel GNN with
learned weights and activations. This is the same scope the influential
over-squashing analyses actually use in their core argument (Topping et
al.'s own Jacobian bound is a bound on the *linearized* operator); real
GNNs' nonlinearities and learned weights can only be related to this linear
backbone, not fully captured by it. State this plainly in the delivered
docstring — do not imply the bound covers a trained nonlinear network's
exact behavior.

Also: the bound below uses a single **global** mixing rate `r` for the
whole graph, not a per-node-pair bottleneck measure. The ML literature's
sharper bottleneck notion is often stated per-pair via commute time or
effective resistance (Scaffold already has `effectiveResistance` — see
Deferred below); this proposal's deliverable is the weaker, immediately
buildable global-rate version.

## Why this is buildable now: the mixing engine already exists

`chiSquareDistance_le_of_connected`
(`Scaffold/Mathlib/GraphTheory/Mixing.lean:859`) already proves, for a
connected graph with positive degrees,

```
χ²(t, x) ≤ r^(2t) · ((π x)⁻¹ − 1)
```

where `π = stationaryVec A` and `χ²(t, x) = chiSquareDistance A t x =
∑ i, (walkDistribution A t x i − π i)² / π i` (definition confirmed at
`Mixing.lean:310`), and `r` bounds `|1 − λ|` over the nonzero eigenvalues
`λ` of the normalized Laplacian — a proved, spectral-gap-driven mixing
rate the caller supplies (the same style of external hypothesis
`davis_kahan_sin_theta`'s `δ` already uses). This is exactly the mixing
bound the over-squashing literature invokes informally; it is already
fully proved here.

## Deliverable

**Step 1 — entrywise extraction (a short new lemma).** `chiSquareDistance`
is literally a sum of nonnegative terms, one per vertex
(`Mixing.lean:310`), so a single term at `y` is bounded by the whole sum
(`Finset.single_le_sum`):

```
(walkDistribution A t x y − π y)² / π y ≤ χ²(t, x) ≤ r^(2t) · ((π x)⁻¹ − 1)
```

hence, after clearing the division and taking square roots (`r ≥ 0`
assumed, matching the sign `chiSquareDistance_le_of_connected`'s rate
naturally has):

```
|walkDistribution A t x y − π y| ≤ r^t · sqrt(π y · ((π x)⁻¹ − 1))
```

**Step 2 — the over-squashing floor (an algebraic inversion).** For a
chosen detection threshold `ε > 0` and `0 ≤ r < 1`: if

```
t < log( sqrt(π y · ((π x)⁻¹ − 1)) / ε ) / log(1 / r)
```

then `|walkDistribution A t x y − π y| < ε` — after fewer than that many
propagation rounds, a walk started at `x` has provably not moved node
`y`'s mass more than `ε` from its background value. State this as a
theorem (name suggestion: `messagePassingDepth_lowerBound` or
`overSquashing_floor`) taking `chiSquareDistance_le_of_connected`'s
hypotheses plus `ε`, concluding the Step-1 deviation bound at any `t`
below the computed threshold — a genuine "you need at least this many
layers" statement, not a restatement of the mixing bound.

## QA

- A concrete small bottlenecked instance — a barbell/dumbbell graph (two
  dense clusters joined by a single bridge edge, the canonical
  over-squashing example in the ML literature) with a pinned spectrum,
  exhibiting a nontrivial numeric floor: the theorem should certify that a
  specific small `t` is provably insufficient for propagation across the
  bridge.
- A sanity contrast — a well-connected small graph (large spectral gap,
  small `r`) on the same vertex count, showing the floor collapses to a
  small `t`. This demonstrates the bound tracks the intended phenomenon
  rather than being vacuously true everywhere.

## Acceptance criteria

- No new axiom, `sorry`, or `admit`.
- `#print axioms` on the new theorem(s) reads exactly
  `propext, Classical.choice, Quot.sound`.
- The "honest scope" section above appears in the delivered module's
  docstring, not only in this proposal.
- At least the two QA instances above (bottlenecked vs. well-connected),
  each with an independently computable numeric floor.
- Full ladder: `lake build`, `check_build_completeness.py`, `lint_axioms`
  (no new axioms), `check_refutation_independence.py`,
  `check_public_reachability.py`, `check_citations`, `check_markdown_links`,
  map-freshness stats sync, records ladder completed in the same delivery.

## Deferred / out of scope

- A per-node-pair refinement using `effectiveResistance`
  (`Scaffold/Mathlib/GraphTheory/Electrical.lean`) instead of a single
  graph-global rate `r` — the sharper, harder version matching the ML
  literature's per-pair bottleneck framing. A real follow-on, not
  attempted here.
- Extending to nonlinear, multi-channel, learned-weight GNNs — out of
  scope; see "Honest scope" above.
- Exposure via the Python certificate bridge
  (`docs/arch/python-certificate-bridge.md`) — a natural follow-on, not
  part of this proposal.
