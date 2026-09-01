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
- ~~A genuine over-squashing floor via the exact eigen-component route
  above — a different, harder proposal if wanted.~~ **Delivered
  2026-09-01** as the spectral mixing floor (the follow-on delivery
  record below): the exact law-level test-function evolution at
  arbitrary eigenpairs, the TV and χ² floors, the `t_mix` floor gate,
  and the log-form spectral floor — the mixing program's first
  lower-bound family, pure hard crust.
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

## Follow-on delivery record (2026-08-31, run `20260831T072600Z-run-1`): the per-pair `effectiveResistance` refinement

The Deferred section's first item — "a per-node-pair refinement using
`effectiveResistance` … instead of a single graph-global rate" —
delivered as a same-file follow-on, selected per the standing handoff
after the Active table held no actionable rows above the
human-decision gates. Zero new axioms (count stays 5; `#print axioms`
via `wip/pairres_axcheck.lean` on all 30 audited declarations — 11
shelf + 19 QA — every one exactly `propext, Classical.choice,
Quot.sound`). QA 3275 → 3306 (+31, `Mixing_QA.lean`'s per-pair
section).

**Statement design (pinned before any Lean — the deferred item's own
open question):** on a `d`-regular graph the walk law admits the
entrywise eigenbasis expansion
`ν_t x y = ∑_k (1 − λ_k/d)^t u_k(x) u_k(y)` over the *combinatorial*
Laplacian's orthonormal basis (the walk factor is `1 − λ_k/d` because
`P = A/d = 1 − L/d` under regularity; kernel modes carry factor `1`
and reconstruct the stationary weight — the identity is
connectivity-free). Splitting each summand's walk factor as
`(λ_k · (1 − λ_k/d)^t) · (Δx_k/λ_k) · (Δy_k/λ_k)` and applying
Cauchy–Schwarz isolates exactly Foster's spectral resistance weights:
the **four-point contrast bound**
`|(ν_t x₁ y − ν_t x₂ y) − (ν_t x₁ y' − ν_t x₂ y')| ≤ ρ_t · √R(x₁,x₂) · √R(y,y')`
with the hypothesis-shaped mode-rate `λ_k |1 − λ_k/d|^t ≤ ρ_t`, plus
the packaged `2 d r^t` corollary at the family's own `|1 − λ_k/d| ≤ r`
certificate shape (λ_k ≤ 2d through a new Dirichlet-sum engine).

**Two negative statement-design findings, recorded so they are not
re-attempted:** (1) *no single-target pure-resistance form exists* —
`|ν_t x y − π y|` pairs one eigen-coordinate difference against the
pseudoinverse diagonal `∑_k u_k(x)²/λ_k`, which is not a resistance;
verified numerically that this diagonal is not bounded by any incident
resistance on C₆ (`G(0) = 8/9 > 5/6 = R(0, neighbor)`), so the
two-pair contrast is the honest pure-resistance statement. (2) *the
tempting universal polynomial rate is dead*: `sup_λ λ(1−λ/d)^t ≤
d/(t+1)` needs all walk factors nonnegative, i.e. λ ≤ d — but
`λ_max > d` always (`trace L = dn > d(n−1)`), so only the
hypothesis-shaped rate is honest.

**Falsification content:** exact attainment on K₃ at `t = 1` **and**
`t = 2` — the contrast at the adjacent pair is *exactly* the theorem's
bound (`1 = (3/2)·√(2/3)·√(2/3)`, `1/2 = (3/4)·√(2/3)·√(2/3)`; value
pinned by raw walk-law iteration, bound pinned by the pinned
resistance `R = 2/3` and the pinned mode equality
`λ|1−λ/2|^t = 3(1/2)^t`); the packaged corollary's instance with
honest slack (`2·2·(1/2)²·(2/3) = 2/3 ≥ 1/2`); the engine pinned `3 ≤
4` by both the engine and the spectrum cases; and the **C₄
mode-coverage fence** — the rate hypothesis restricted to the mid
modes `λ = 2` (where `ρ = 0` genuinely certifies, the walk factor
being `0`) is refuted by the `t = 1` contrast `1` against the bound
`ρ·√R·√R = 0`, proving the mode quantifier must cover every decaying
mode. The C₄ spectrum `{0,2,4}` itself is derived in QA from the
minimal-polynomial fact `A³ = 4A` (pinned by raw Fin 4 enumeration)
applied at the eigenvector.

**Technique findings (Lean):** the pinned Mathlib's `Finset.mul_sum`
and friends are sensitive to elaboration-order metavars — rewrites
that elaborate cleanly at abstract types can go instance-stuck
in-context, and the robust route is small explicitly-argued helper
lemmas (`sum_sub_help`/`mul_sum_help` in the QA file, the shelf's own
`Finset.sum_congr` chains); `Finset.sum_mul_sq_le_sq_mul_sq` (root
namespace) supplies the sum Cauchy–Schwarz directly, dissolving the
discriminant route entirely; the `4 • M` scalar in statements must be
`(4 : ℝ) • M` — bare `4` elaborates to the ℕ-action on functions and
silently breaks later `rfl`s; `rw [abs_neg]` does not match `|-1/2|`
because `-1 / 2` parses as `(-1)/2` — write `-(1/2)`; a `have :`
ascription over bare numerals defaults to ℕ (`|1 - 3/2| = 1/2` needs
`|(1:ℝ) - 3/2|`); and `d ≤ 2d`-style bounds with a `d ≠ 0`-only
hypothesis should instead carry `0 < d` where positivity of derived
rates is needed.

**Verification:** spike `wip/pairres_spike.lean` (all five parts)
iterated to zero errors/zero warnings before any shelf edit;
`lake env lean` zero errors/zero warnings on both touched modules;
explicit `lake build` targets ✔; `#print axioms` as above; full
`lake build` ✔ (2407/2408) + `check_build_completeness.py` — 131
source files, 131 fresh artifacts, 0 stale, 0 missing, exit 0 (after
the documented single-module mtime remediation); `lint_axioms` (5),
`check_refutation_independence` (10 tagged, clean),
`check_public_reachability` (62 modules), `check_citations`,
`check_markdown_links` pass; scoreboard **3306/5/0**; map freshness
exit 0 after the 3275 → 3306 stats sync in both map files and SVG
regeneration.

The proposal's other deferred items stand unchanged: the genuine
over-squashing floor (consumer-gated), the nonlinear/multi-channel
extension (out of scope), and the Python certificate bridge
(operator-gated). **Status remains COMPLETE** — this record delivers a
deferred follow-on, not a new milestone.

## Follow-on delivery record (2026-09-01, run `20260901T091923Z-run-1`): the genuine over-squashing floor — the spectral mixing floor

The correction section's priced follow-on ("a genuine over-squashing
floor via the exact eigen-component route … a different derivation
with a different hypothesis structure, still awaiting a consumer")
delivered on exactly its own named route. The consumer gate is
discharged by two named consumers: the **oversmoothing ceiling's depth
certificate completed into a two-sided bracket** (the ceiling alone
says "enough layers by `T_hi`"; the floor adds "provably insufficient
before `T_lo`" — a depth *certificate* is two-sided by definition),
and the **`t_mix` objects' missing lower half** — the delivered
`walkMixingTimeFrom` package had only the spectral *ceiling*
(`walkMixingTimeFrom_le_of_connected`), and the classical eigenvalue
*lower* bound on mixing time (Levin–Peres–Wilmer, ch. 12's
distinguishing-statistic technique — chapter-level locator per the
repo convention, to be confirmed against a physical copy) is its
textbook companion. This is the mixing program's first lower-bound
family: every prior delivery is an upper/domination bound, so this is
the first direction-reversed stress test of the same proved
eigenbasis substrate (load-bearing in the falsification sense: a
wrong conjugation constant or similarity orientation that an upper
bound could survive would flip or break a floor — and the QA pins the
floors attained *exactly*).

Zero new axioms (count stays 5; `#print axioms` via
`wip/spectralfloor_axcheck.lean` on all 39 audited declarations —
9 shelf + 30 QA — every one exactly `propext, Classical.choice,
Quot.sound`). QA 3487 → 3517 (+30, `Mixing_QA.lean`'s new
`SpectralFloor` section).

**The shelf:** the TV-toolkit lemma `tvDistance_ge_half_abs_sum` (the
distinguishing-function bound `|(μ−ν)(f)| ≤ 2·TV(μ,ν)` for `‖f‖∞ ≤ 1`,
hypothesis-minimal — no sign or mass assumptions — in `Mixing.lean`'s
TV section; the upper bound's Cauchy–Schwarz conversion has no
reverse, and this is the standard way around that); then
`Oversmoothing.lean`'s new `SpectralFloor` section — the
kernel-orthogonality derivation
`degreeSqrt_onesVec_dotProduct_of_eigenpair` (`μ ≠ 0` forces
`⟨√D·1, v⟩ = 0` through symmetry and `L_sym(√D·1) = 0` — derived, not
assumed, *no connectivity*), the stationary-pairing vanishing at the
conjugated eigenvector, **the exact law-level test-function
evolution** `walkDistribution_dotProduct_degreeInvSqrt_of_eigenpair`
(the deferred item's own engine: pairing the walk law against
`(1/√D)•v` at any genuine `L_sym` eigenpair evolves *exactly*
geometrically at `1 − μ` — an equality, not a bound, at arbitrary
eigenpairs, no `eigvecOf` indexing), **the TV floor**
`walkDistribution_tvDistance_ge_of_eigenpair` —
`(1/2)|1−μ|^t·|v x|/(√D x·c) ≤ TV(ν_t, π)` at a caller-certified sup
bound `c`, no connectivity, no aperiodicity: at `|1−μ| = 1` the floor
never decays, which is the point, exactly the chains no `r < 1`
certificate reaches — **the χ² floor**
`chiSquareDistance_ge_of_eigenpair` —
`(1−μ)^{2t}·(v x)²/(π x·‖v‖²) ≤ χ²(t,x)`, the √D-conjugated initial
centered density pairing with `v` in coordinate exactly
`vol/√D x·v x` and Cauchy–Schwarz extracting that mode's slice of the
Parseval identity — the **`t_mix` floor gate**
`walkMixingTimeFrom_gt_of_tv_gt` (witness existence + `ε < TV_t` ⇒
`t < t_mix(ε,x)`), the strict-direction calculus lemma
`pow_lt_of_lt_log_div` (the downward twin of the ceiling's
`pow_mul_le_of_log_threshold` — dividing by the *negative* `log r`
flips, the mirror of the original draft's recorded error), and the
capstone **log-form spectral floor** `walkMixingTimeFrom_ge_of_eigenpair`
— `⌈log(|v x|/(√D x·2εc))/log(1/|1−μ|)⌉ ≤ t_mix(ε,x)` under
`0 < |1−μ| < 1` and *some* witness at `ε` (existence certified from
above, e.g. by the `r < 1` ceiling; the hypothesis is exactly what
fails on periodic chains, fenced in QA); `hv0 : v ≠ 0` was honestly
dropped from this statement as unneeded (the TV route never uses
`‖v‖`).

**The QA (+30):** on `K₂` at the hand eigenpair `k2G` (eigenvalue `2`,
`|1−μ| = 1`): **both floors attained exactly at every time** — TV
floor `1/2` = the pinned `TV ≡ 1/2`, χ² floor `1` = the pinned
`χ² ≡ 1` — certified non-mixing, tight forever, on the periodic chain
where the ceiling's hypothesis set is empty; the exact-evolution
instance reading `(-1)^m`; and **the witness-existence fence**
(`¬∃T, ∀s ≥ T, TV ≤ 1/4` — proved, not assumed — exhibiting the gate's
hypothesis as exactly what fails at the junk corner `t_mix = 0`).
On the triangle at the hand eigenpair `triG` (eigenvalue `3/2`,
`|1−μ| = 1/2`, conjugated test function `triF = triG/√2` with
`|triF 0|` exactly attaining its own sup bound): the exact-evolution
instance; the TV floor values `(1/2)^{m+1}` beside the pinned truth
`(2/3)·2^{−m}` with the slack proved strict; **the χ² floor attained
exactly at every time** (`2·(1/4)^m`, load-bearing on the eigenpair
constant — a wrong conjugation would miss the exact value); and the
capstones — **the log-form floor hits all three pinned `t_mix` closed
forms exactly** (`⌈log(3/2)/log 2⌉ = 1 = t_mix(1/3)`,
`⌈log 3/log 2⌉ = 2 = t_mix(1/6)`, `⌈log 6/log 2⌉ = 3 = t_mix(1/12)`,
via the strict log inequalities `2 < 3 ≤ 4 < 6 ≤ 8`), completing the
two-sided depth bracket on the same fixture (floor `2` = truth `2` ≤
ceiling `3` at `ε = 1/6`). **Two kernel-mode refutation fences** (χ²
and TV forms): at the *genuine* kernel eigenpair `(0, ![1,1,1])`
every other ingredient is satisfiable, and the dropped-`μ ≠ 0`
statement reads `1 ≤ χ²(2) = 1/8` and `1/2 ≤ TV(2) = 1/6` against the
pinned values — the hypothesis load-bearing in both metrics.

**Technique findings (Lean), recorded for the next lower-bound
proof:** (1) `Pi.single x (1 : ℝ)` under an untyped context leaves
`Pi.single`'s dependent codomain as a metavariable and the smul TC
search then times out — always ascribe the full application
`(Pi.single x (1 : ℝ) : V → ℝ)`; (2) `rw` does not beta-reduce, so
unfolding `walkDensity`/`stationaryVec` by `rw` under an application
leaves a redex the following rewrites cannot match — use `simp only
[def]` (which beta-reduces) or pre-prove `rfl`-bridges
(`have hwd : walkDensity A 0 x y = … := rfl`); (3) `field_simp`
sometimes closes the whole goal (algebraic identity) and sometimes
leaves a pure `√`-atom rearrangement — appending `ring` is then a
*liability* ("no goals"); the robust idiom is `field_simp` alone
first, add `ring` only where the leftover is visible; (4) `rw`'s
trailing `rfl` can close a goal mid-chain (`congr 1` after
`rw [← pow_mul]` was dead) — order congruences after the rewrites
that need them; (5) `Nat.ceil_pos` is an iff in this pin
(`(Nat.ceil_pos).mpr`), and `omega` cannot abstract
`Nat.ceil (r : ℝ)` atoms — derive natural bounds explicitly via
`Nat.le_ceil` + `exact_mod_cast` and finish with `le_antisymm`;
(6) `pow_succ` in this pin is `a^(n+1) = a^n * a` (right factor) —
state helper equations in that order or close with `ring`;
(7) `mul_div_mul_left` takes `(a b) (h : c ≠ 0)` — the value `c` is
implicit and unified from the hypothesis; (8) a `subst` of
`x = z` eliminates whichever side is the later local — reference the
surviving variable, or avoid `subst` and `rw` the equation instead.

**Verification:** spike `wip/spectralfloor_spike.lean` (shelf + QA +
axiom audit) iterated to zero errors/zero warnings before any shelf
edit; explicit `lake build` targets ✔ on both touched modules (only
the module's 3 recorded pre-existing benign `ring_nf` notes — none
new); `lake env lean` clean on both; **`#print axioms` via
`wip/spectralfloor_axcheck.lean` on all 39 audited declarations:
every one exactly `propext, Classical.choice, Quot.sound`**; **full
`lake build` ✔ immediately followed by `check_build_completeness.py`
— 133 source files, 133 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (5, both PF findings allowlisted-confirmed);
`check_refutation_independence` (10-tag clean — no tags added, nothing
here touches an axiom); `check_public_reachability` clean (63 repo
modules); `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**3517/5/0**) with the verification row added;
`check_scaffold_map_freshness` exit 0 after the 3487 → 3517 stats
sync in both map files and SVG regeneration (no proposal status
header changed — a follow-on record, no tier change).

The proposal's remaining deferred items stand unchanged: the
nonlinear/multi-channel extension (out of scope) and the Python
certificate bridge (operator-gated). The genuine over-squashing floor
is **delivered** — the deferred bullet is resolved. **Status remains
COMPLETE** — this record delivers the correction section's priced
follow-on, closing the proposal's own named residual.
