# Proposal: Certified Oversmoothing Ceiling from Mixing

**Status:** **COMPLETE** — delivered 2026-08-31 by run
`20260831T025541Z-run-1` (see "Delivery record" below). New Lean
derivation from already-proved primitives; no new axioms.

**Correction (2026-08-30, same day as the original draft):** this document
originally proposed an "over-squashing floor" — a certified *lower* bound
on message-passing rounds needed before information can propagate. That
derivation was mathematically backwards and has been replaced. The error:
`chiSquareDistance_le_of_connected` gives an **upper bound** on mixing
distance that shrinks as `t` grows; an upper bound can only certify that a
quantity is *small*, never that it is *large*. Solved correctly, the same
inequality gives a bound of the opposite kind: *for `t` large enough,
deviation from stationary is guaranteed small* — an **oversmoothing
ceiling** (guaranteed representation collapse after enough layers), not an
over-squashing floor (guaranteed non-propagation before enough layers).
Those are genuinely different claims needing different tools; seeing the
error required for the oversmoothing companion this proposal now delivers.
See "Genuine over-squashing needs a different tool" below for what a
real floor would actually require.

**Provenance:** New-capability menu item #2 (over-squashing), corrected
in place after menu item's own companion request (an oversmoothing bound)
surfaced the direction error. Sibling to
`spectral-graph-sparsification-gnn-training.md` (menu item #3).

## The capability

Oversmoothing in deep GNNs — the phenomenon where, past a certain depth,
every node's representation converges toward the same value regardless of
its neighborhood, destroying the model's ability to distinguish nodes — is
the depth-calibration counterpart to over-squashing: too few layers and
information can't spread; too many and it homogenizes. Both are governed
by the same underlying mixing behavior of the propagation operator, and
Scaffold already has the proved bound for one of the two directions.

This proposal derives a certified **upper bound on the depth at which
oversmoothing is guaranteed** — given a graph's certified spectral gap and
a chosen indistinguishability threshold `ε`, a concrete `t` past which
every node's `t`-step propagated view is guaranteed within `ε` of the
graph's universal stationary value, regardless of where the signal
started. This is directly usable as an architecture-design ceiling: *don't
stack more than this many layers, or you're provably averaging your
signal away.*

## Honest scope: what this bounds and what it doesn't

Same scope note as the over-squashing menu item this corrects: this
targets the **linearized, mean-aggregation propagation operator** —
repeated application of the random-walk transition matrix, what a linear
GCN-style layer computes up to a learned weight matrix and nonlinearity at
each step — not a full nonlinear, multi-channel GNN with learned weights
and activations. State this plainly in the delivered docstring.

The bound uses a single **global** mixing rate `r` for the whole graph,
not a per-node-pair refinement. A sharper, per-pair version is a real
follow-on (see Deferred), not attempted here.

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
`davis_kahan_sin_theta`'s `δ` already uses). This bound is monotonically
decreasing in `t` for `0 ≤ r < 1` — the correct reading is "convergence
guaranteed by time `t`," which is exactly the oversmoothing direction.

## Deliverable

**Step 1 — entrywise extraction (a short new lemma), unchanged from the
original draft.** `chiSquareDistance` is a sum of nonnegative terms, one
per vertex (`Mixing.lean:310`), so a single term at `y` is bounded by the
whole sum (`Finset.single_le_sum`):

```
(walkDistribution A t x y − π y)² / π y ≤ χ²(t, x) ≤ r^(2t) · ((π x)⁻¹ − 1)
```

hence, clearing the division and taking square roots (`0 ≤ r < 1`):

```
|walkDistribution A t x y − π y| ≤ r^t · sqrt(π y · ((π x)⁻¹ − 1))
```

**Step 2 — the oversmoothing ceiling (corrected direction).** Write
`C = sqrt(π y · ((π x)⁻¹ − 1))`. Since `r^t · C` is *decreasing* in `t`,
solving `r^t · C ≤ ε` for the smallest sufficient `t` gives, correctly
this time,

```
t ≥ log(C / ε) / log(1 / r)   ⟹   |walkDistribution A t x y − π y| ≤ ε
```

(dividing by `log(r) < 0` flips the inequality relative to the original
draft's — that flip is the bug that was fixed). State this as a theorem
(name suggestion: `oversmoothing_ceiling` or
`walkDistribution_le_of_depth`), taking `chiSquareDistance_le_of_connected`'s
hypotheses plus `ε`, concluding the Step-1 deviation bound at any `t` at
or above the computed threshold. Applying this at two different starting
points `x₁, x₂` and combining by the triangle inequality gives the
sharper, more legible corollary: *past this depth, the `t`-step views from
any two starting nodes are within `2ε` of each other* — the actual
"representations become indistinguishable" statement oversmoothing papers
state informally.

## QA

- A concrete small graph instance with a pinned spectrum (rate `r`
  computed independently), exhibiting a nontrivial numeric ceiling: the
  theorem should certify a specific depth past which two named starting
  points' distributions are provably within a stated `ε`.
- A sanity contrast — a small graph with a deliberately small spectral gap
  (large `r`, close to 1), showing the ceiling grows large, contrasting
  with a well-mixed instance where it stays small. This demonstrates the
  bound tracks the intended phenomenon (poorly-connected graphs oversmooth
  slower) rather than being a fixed constant.

## Acceptance criteria

- No new axiom, `sorry`, or `admit`.
- `#print axioms` on the new theorem(s) reads exactly
  `propext, Classical.choice, Quot.sound`.
- The "honest scope" section above appears in the delivered module's
  docstring, not only in this proposal.
- At least the two QA instances above, each with an independently
  computable numeric ceiling.
- Full ladder: `lake build`, `check_build_completeness.py`, `lint_axioms`
  (no new axioms), `check_refutation_independence.py`,
  `check_public_reachability.py`, `check_citations`, `check_markdown_links`,
  map-freshness stats sync, records ladder completed in the same delivery.

## Genuine over-squashing needs a different tool

For the record, since the original framing is retracted rather than just
deleted: a real over-squashing *floor* (information provably has not
propagated before `t`) cannot come from an upper bound on aggregate mixing
distance — it needs a lower bound on a specific quantity, which is a
different kind of argument. One buildable route already available on the
shelf: the eigen-component evolution is an *equality*, not an inequality
(`eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix` in
`Mixing.lean`) — the component of the walk along a specific eigenvector
`vᵢ` evolves *exactly* as `(1 − λᵢ)^t` times its initial value. If the
starting point `x`'s point mass has a nonzero, boundable-below component
along a slow-decaying mode (e.g. near the Fiedler value `λ₂`), that
component's magnitude is exactly computable at every `t`, and a floor
follows from *that* — not from `chiSquareDistance`. This is real,
plausible future work, but it is a different derivation with a different
hypothesis structure (a lower bound on an initial eigen-coordinate,
which needs its own argument) — not a corollary of this proposal, and not
attempted here.

## Deferred / out of scope

- A per-node-pair refinement using `effectiveResistance`
  (`Scaffold/Mathlib/GraphTheory/Electrical.lean`) instead of a single
  graph-global rate `r`. A real follow-on, not attempted here.
- Extending to nonlinear, multi-channel, learned-weight GNNs — out of
  scope; see "Honest scope" above.
- A genuine over-squashing floor via the exact eigen-component route
  above — a different, harder proposal if wanted.
- Exposure via the Python certificate bridge
  (`docs/arch/python-certificate-bridge.md`) — a natural follow-on, not
  part of this proposal.

## Delivery record (2026-08-31, run `20260831T025541Z-run-1`)

Delivered as specified, zero new axioms, QA 3225 → 3246 (+21):

- **The shelf** — a new module, `Scaffold/Mathlib/GraphTheory.Oversmoothing.lean`
  (umbrella-imported, 6 proved declarations):
  `stationaryVec_le_one` (the engine making the ceiling constant real),
  the Step-1 **entrywise extraction**
  `walkDistribution_sub_stationaryVec_abs_le`
  (`|ν_t x y − π y| ≤ r^t · √(π y · ((π x)⁻¹ − 1))`, one nonnegative
  χ² summand against the whole sum via `Finset.single_le_sum`, the
  square root closed through `abs_le_of_sq_le_sq`), the Step-2
  **calculus bridge** `pow_mul_le_of_log_threshold` (the corrected
  sign-of-`log` step; `C = 0` — the single-vertex degenerate constant —
  handled trivially), the **ceiling**
  `walkDistribution_sub_stationaryVec_le_of_depth`, the
  **two-start indistinguishability corollary**
  `walkDistribution_sub_walkDistribution_le_of_depth` (within `2ε`
  past the depth), and the **rate monotonicity**
  `oversmoothing_log_threshold_mono`.
- **The QA** (`Mixing_QA.lean`'s oversmoothing section, +21), on the
  triangle at two rate certificates — the proposal's sanity contrast
  delivered as *the same graph, two certificates*, which isolates the
  mechanism (the ceiling depends on the certified rate, not on the
  fixture): the honest `r = 1/2` certifies `ε = 1/8` at **exactly**
  depth 3 — `tri_ceiling_threshold_three_sharp_QA` proves depth 2 does
  *not* satisfy the threshold (`4 < 8·√(2/3)`), so the hypothesis is
  load-bearing — while the deliberately loose `r = 4/5` provably needs
  depth 9 (`tri_ceiling_loose_sharp_QA` excludes 8 via
  `(5/4)⁸ < 32/5 ≤ 8·√(2/3)`); the general monotonicity pinned at the
  fixture; both ceiling instances and the two-start instance with true
  values beside them (`1/12 ≤ 1/8`; `1/8` at exactly half the `2ε`
  bound); the `t = 0` corner soundness instance (threshold `log 1 = 0`
  at `ε` exactly the constant, conclusion the entrywise bound's own
  `t = 0` case); the depth-1 instance at `ε = 1/2`; and every walk law
  by raw literal iteration (`tri_dist_three_zero_QA`,
  `tri_dist_three_one_QA`, `tri_dist_nine_zero_QA` =
  `(85/256, 171/512, 171/512)`), deviations `1/6`, `1/12`, `1/768`.
- **Verification:** spike first (`wip/oversmoothing_spike.lean`, the
  shelf layer and QA section iterated to zero errors/zero warnings
  before any shelf edit — technique findings: `Finset.single_le_sum`
  needs the summand function given explicitly or the `chiSquareDistance`
  defeq check fails under metavariables; `abs_le_of_sq_le_sq'` is the
  `∧`-form in the pinned Mathlib, the plain name gives `|a| ≤ b`;
  `Real.log_le_log` takes positivity of the *first* argument in this
  pin; linarith cannot compare distinct rational atoms, so every
  numeric bridge is discharged by `norm_num` `have`s before `linarith`;
  `rw` at a natural-cast numeral needs `push_cast`/`simpa` bridging);
  `lake env lean` zero errors/zero warnings on both touched modules;
  explicit `lake build` targets ✔; **`#print axioms` via
  `wip/oversmoothing_axcheck.lean` (27 declarations: 6 shelf + 21 QA)
  each exactly `propext, Classical.choice, Quot.sound`**; full
  `lake build` ✔ (2407/2408) + `check_build_completeness.py` — 131
  source files, 131 fresh artifacts, 0 stale, 0 missing; `lint_axioms`
  (5), `check_refutation_independence` (10 tagged, clean),
  `check_public_reachability` (62 modules), `check_citations`,
  `check_markdown_links` pass; scoreboard **3246/5/0**; map freshness
  exit 0 after the stats sync (3225 → 3246 in both map files, SVG
  regenerated; no station's proposal status changed — this proposal has
  no station).

The honest-scope section above appears in the delivered module's
docstring (acceptance criterion), including the bipartite note: graphs
admitting no `r < 1` certificate are outside the ceiling's reach
entirely, as the path fixture's pinned `λ* = 1` no-decay already
records. A priced follow-on from the correction section, **not**
delivered: the genuine over-squashing floor via
`eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix` (the
exact eigen-component equality) — a different derivation with a
different hypothesis structure, still awaiting a consumer.
