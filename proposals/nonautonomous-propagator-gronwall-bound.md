# Proposal: A Grönwall-Type Bound for the Non-Autonomous Propagator

**Status:** Proposed. Restated in pure-mathematics form 2026-09-07 from
an external request relayed by the operator (not tracked in this
repository — see `.gitignore`); no operational, product, or patent
framing survives into this document, only the underlying mathematical
ask. Authorizes no Lean changes, axiom admissions, document rewrites,
or transit-map edits.

Companion to `docs/6_SGT_BACKLOG.md` item 5 ("Graph-dynamical
systems") — **this proposal sits in the part of that item still
gated**, not the part already opened (see "The gate" below) — and to
[`global-semigroup-contraction.md`](global-semigroup-contraction.md)
(the constant-generator analogue this proposal generalizes to a
time-varying generator) and `Scaffold/Mathlib/Dynamics/
DiscreteAffine.lean` (the existing discrete-time analogue the request's
"current state" description accurately names).

## The claim this document is answering

The relayed request's framing was accurate, unlike the two requests
before it in the same family: **this project's existing discrete-
affine iteration theory (`DiscreteAffine.lean`) genuinely covers only
static, time-independent updates** (`x_{n+1} = (1-α)x_n + αe`, a fixed
`α`), and **no continuous-time non-autonomous (time-varying-generator)
theory exists anywhere in this project** — confirmed by search: the
only continuous-time generator machinery is the constant-generator
heat semigroup (`GraphTheory/Heat.lean`, `NormedSpace.exp`, closed-
form); the only time-varying object is `GraphTheory/Dynamics.lean`'s
*discrete*-time `TimeVaryingGraph := ℕ → Matrix V V ℝ`. The request
asks for a Grönwall-type bound on the adjoint propagator `Φ(t)` of a
time-varying generator `L(t)` (`Φ̇(t) = -L(t)Φ(t)`), measuring how far
`Φ(t)^*` acting on a fixed vector `r` deviates from `r` itself, in
terms of a reference generator `L̂` and a bound `‖L(t) - L̂‖ ≤ η + ρt`
on how far the true generator has drifted from that reference.

**This is a genuinely new capability, not an assembly of existing
Scaffold lemmas** — the first proposal in this relayed family for
which that is true. It is, however, more tractable than it first
appears: the requested bound does **not** require constructing `Φ`
(no ODE existence/uniqueness machinery needed) — it can be stated and
proved as a conditional theorem, exactly the way Mathlib's own
Grönwall lemma is packaged (`Φ` is a hypothesis satisfying the ODE and
an initial condition; the theorem produces the bound for any such
`Φ`). Under that framing, the entire proof reduces to a single,
already-proved Mathlib calculus lemma this project has simply never
used before.

## What's already on the shelf

- **The discrete-time analogue, confirming the request's own "current
  state" claim** — `DiscreteAffine.lean`'s `affineIteration_tendsto_
  atTop`: static-generator convergence only, exactly as described.
- **The operator-norm algebra needed for the estimate** — all three
  already proved: `l2OpNorm_mulVec_le` (`‖M *ᵥ v‖ ≤ ‖M‖ * ‖v‖`,
  `BandDavisKahan.lean:169`), `l2OpNorm_transpose` (`‖Mᵀ‖ = ‖M‖`,
  `BandDavisKahan.lean:1774`), and `Matrix.mulVec_mulVec` (the pinned
  Mathlib identity `(M * N) *ᵥ v = M *ᵥ (N *ᵥ v)`).
- **The entrywise-differentiation-in-`t` idiom** — this project's
  established route for "differentiate a matrix action in time"
  (`heatKernel_mulVec_apply_hasDerivAt_zero`, `heatApply_hasDerivAt`,
  both building a vector-valued `HasDerivAt` from a finite sum of
  scalar `HasDerivAt` facts). The same idiom applies directly to
  differentiating `Φ(t)ᵀ *ᵥ r` from a hypothesized entrywise
  derivative of `Φ`, with no new differentiation technique needed.
- **The constant-generator sibling this generalizes** —
  `global-semigroup-contraction.md`'s Step 1/Step 2 (`‖x − e^{−tL}x‖ ≤
  t‖Lx‖`, itself proposed but not yet operator-adopted): the `η = ρ =
  0`, `L(t) ≡ L̂` degenerate case of this proposal's requested bound
  is *exactly* that companion's order-0 statement. This proposal is
  the genuinely non-autonomous generalization of the same shape of
  fact.

## What's not on the shelf

- **Any continuous-time non-autonomous generator theory.** Confirmed
  gated, not merely absent: `docs/6_SGT_BACKLOG.md` item 5 records
  "consensus maps, synchronization, and general graph semigroups
  remain gated" as of the 2026-08-19 gate-opening note, which opened
  *only* the constant-generator heat-semigroup instance. A time-
  varying generator is squarely "general graph semigroups" — the
  still-gated part of that same backlog item, not an extension of
  what was already opened.
- **Mathlib's variable-boundary calculus fencing theorem, never used
  in this project** — `image_norm_le_of_norm_deriv_right_le_deriv_
  boundary` (`Mathlib.Analysis.Calculus.MeanValue`): given `f`
  continuous on `[a,b]` with right-derivative `f'`, and a
  *differentiable real-valued bound function* `B` with `‖f a‖ ≤ B a`
  and `‖f' x‖ ≤ B' x` pointwise, concludes `‖f x‖ ≤ B x` throughout —
  a strict generalization of the constant-bound mean-value inequalities
  this project already knows about (`norm_image_sub_le_of_norm_deriv_
  le_segment` and its siblings, all constant-`C` only) to an
  *arbitrary* bound function, which is exactly what the request's
  affine-in-`t` error term (`η t + ρt²/2`) needs and a constant-bound
  lemma cannot supply. This is a real, if small, new-Mathlib-area risk
  distinguishing this proposal from `rank-one-edge-perturbation-norm.
  md`/`boundary-outflow-lemma.md`'s pure reassembly of already-proved
  Scaffold lemmas.
- **A uniform contraction hypothesis on the propagator, needed but not
  stated in the request's own formula** — see "The route," below.

## The route: the fencing theorem, plus one hypothesis the request omits

**Framing decision:** state the theorem conditionally. Take `L : ℝ →
Matrix V V ℝ` (the time-varying generator), `L̂ : Matrix V V ℝ` (the
reference), `Φ : ℝ → Matrix V V ℝ` as *hypotheses* — `Φ 0 = 1`, and
for every `t` and every vector `y`, `HasDerivAt (fun s => (Φ s)ᵀ *ᵥ y)
((Φ t)ᵀ *ᵥ (L t *ᵥ y)) t` (the transposed-ODE derivative, in the
entrywise/vector-action form this project already uses, sidestepping
any matrix-valued-derivative abstraction) — rather than constructing
`Φ` from `L` via ODE existence theory. This mirrors exactly how
Mathlib's own `norm_le_gronwallBound_of_norm_deriv_right_le` takes `f`
and its derivative as hypotheses; no Picard–Lindelöf machinery is
needed anywhere in this route.

**The missing hypothesis, found here:** the algebra below only closes
if the adjoint propagator is a uniform contraction, `∀ t, ‖Φ t‖ ≤ 1` —
the direct non-autonomous analogue of the "semigroup contraction
property `‖e^{-sL}‖₂ ≤ 1`" the request's own sibling document (item 1,
the order-`m` generalization) names explicitly as a standing
assumption in the same source material. Without it, the estimate below
picks up an uncontrolled factor of `‖Φ(t)‖` and the requested bound
does not follow from `‖L(t) - L̂‖ ≤ η + ρt` alone. This should be
added as an explicit hypothesis, not silently assumed — the "beyond
the ask" finding this project's proposals routinely surface (matching
`rank-one-edge-perturbation-norm.md`'s `i ≠ j` finding and `boundary-
outflow-lemma.md`'s removed-hypothesis finding, on the opposite side
of the ledger this time: a hypothesis *added*, not removed).

**Derivation**, at `f(t) := r - (Φ t)ᵀ *ᵥ r` (packaged in
`EuclideanSpace ℝ V` exactly as `global-semigroup-contraction.md`'s
Step 2 already does via `norm_euclidean_eq_sqrt`):

1. `f(0) = r - (Φ 0)ᵀ *ᵥ r = r - r = 0` (from `Φ 0 = 1`).
2. `f'(t) = -(Φ t)ᵀ *ᵥ (L t *ᵥ r)` (from the hypothesized derivative,
   negated for the `r - (·)` framing).
3. Split `L t *ᵥ r = L̂ *ᵥ r + (L t - L̂) *ᵥ r` and bound termwise:
   ```
   ‖f' t‖ = ‖(Φ t)ᵀ *ᵥ (L t *ᵥ r)‖
     ≤ ‖(Φ t)ᵀ‖ * ‖L t *ᵥ r‖                     (l2OpNorm_mulVec_le)
     = ‖Φ t‖ * ‖L t *ᵥ r‖                          (l2OpNorm_transpose)
     ≤ ‖L t *ᵥ r‖                                  (the contraction hypothesis)
     ≤ ‖L̂ *ᵥ r‖ + ‖(L t - L̂) *ᵥ r‖                (triangle inequality)
     ≤ ‖L̂ *ᵥ r‖ + ‖L t - L̂‖ * ‖r‖                 (l2OpNorm_mulVec_le)
     ≤ ‖L̂ *ᵥ r‖ + (η + ρ * t) * ‖r‖                (the drift hypothesis)
   ```
4. Take `B(t) := t * ‖L̂ *ᵥ r‖ + ‖r‖ * (η * t + ρ * t ^ 2 / 2)`, an
   explicit polynomial in `t` with `B'(t) = ‖L̂ *ᵥ r‖ + ‖r‖ * (η + ρ *
   t)` — exactly Step 3's bound — and `B(0) = 0 = ‖f 0‖`. Apply
   `image_norm_le_of_norm_deriv_right_le_deriv_boundary` directly:
   `‖f t‖ ≤ B t` for every `t ≥ 0`, which unfolds to exactly the
   requested inequality.

No inequality beyond the operator-norm triangle bounds and the
fencing theorem's own statement is used; the proof is short once the
framing (hypothesis-conditional `Φ`, the added contraction hypothesis,
the explicit `B`) is fixed.

## Scope decision: no ODE existence theory, no new named objects

- **Do not attempt to construct `Φ` from `L`.** Existence and
  uniqueness of solutions to a time-varying linear matrix ODE is a
  substantially larger undertaking (Picard–Lindelöf machinery exists
  in the pinned Mathlib, `Mathlib.Analysis.ODE.PicardLindelof`, but
  adapting it to a matrix-valued, non-Lipschitz-in-the-usual-sense
  linear generator is its own project) and is not needed for the
  requested inequality, which is a property of *any* `Φ` satisfying
  the stated ODE and contraction hypotheses, not a construction.
- **Do not introduce a named `TimeVaryingGraph`-style continuous
  analogue or a persistent `Propagator` definition.** State the
  theorem with `L`, `L̂`, `Φ` as bare hypotheses, matching Mathlib's
  own Grönwall-lemma packaging and this project's `DiscreteAffine.
  lean` precedent (which also takes its recurrence as a hypothesis on
  an arbitrary sequence `x`, not a constructed object).

## Build order

### Step 0: Survey `Mathlib.Analysis.Calculus.MeanValue`'s exact API

Confirm `image_norm_le_of_norm_deriv_right_le_deriv_boundary`'s precise
hypothesis shape against the sketch above (in particular, whether
`ContinuousOn`/`HasDerivWithinAt (Ici x) x` transfers cleanly from a
`HasDerivAt` hypothesis stated for all `t`, or needs an explicit
`.hasDerivWithinAt` restriction step) — the one piece of this proposal
without a Scaffold precedent to clone.

### Step 1: The vector-level bound

```
theorem nonautonomous_propagator_deviation_le
    (L Φ : ℝ → Matrix V V ℝ) (Lhat : Matrix V V ℝ) (r : V → ℝ)
    (η ρ : ℝ) (hΦ0 : Φ 0 = 1)
    (hderiv : ∀ t y, HasDerivAt (fun s => (Φ s)ᵀ *ᵥ y)
      ((Φ t)ᵀ *ᵥ (L t *ᵥ y)) t)
    (hcontract : ∀ t, ‖Φ t‖ ≤ 1)
    (hdrift : ∀ t, ‖L t - Lhat‖ ≤ η + ρ * t)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖r - (Φ t)ᵀ *ᵥ r‖ ≤ t * ‖Lhat *ᵥ r‖ + ‖r‖ * (η * t + ρ * t ^ 2 / 2)
```
(Euclidean norms, via the `WithLp.equiv 2` packaging already
established in `Duhamel.lean`/`global-semigroup-contraction.md`.)
Route: exactly "The route" above, applied on `[0, t]`.

### Deferred and removed

- **ODE existence/uniqueness for `Φ`** — explicitly out of scope (see
  "Scope decision").
- **A sharper bound exploiting a spectral relationship between `L(t)`
  and `L̂`** (e.g. if they commute) — the request asks for the generic
  bound only; a commuting-generator special case would be a separate,
  smaller follow-on if a consumer ever named one.

## QA plan

- A concrete instance where `L(t) := L̂` is genuinely constant
  (`η = ρ = 0`): confirms the bound collapses to exactly `global-
  semigroup-contraction.md`'s order-0 statement, cross-checked against
  that proposal's own K₂ fixture once it lands.
- A concrete affinely-drifting `L(t) := L̂ + t • E` for a fixed
  perturbation matrix `E` on a small fixture (K₂ or the path on 3
  vertices), with `Φ` given a hand-computable closed form if one
  exists at that fixture (e.g. if `L̂` and `E` commute), checked
  against the bound numerically at a specific `t`.
- The contraction-omission fence: a fixture where `‖Φ(t)‖ > 1` for
  some `t`, confirming the conclusion genuinely fails without that
  hypothesis, per this project's standing adversarial-fence discipline
  (`governance/ADVERSARIAL_REVIEW.md`) — the load-bearing status of
  the hypothesis this proposal added beyond the request's own text.

## The gate — Low, both a technical and a governance decision

Two independent reasons this needs an explicit operator decision
before Step 0, not routine treatment:

1. **It opens still-gated territory.** `docs/6_SGT_BACKLOG.md` item 5
   explicitly keeps "general graph semigroups" gated pending a named
   consumer; a time-varying generator is that gated case, not an
   extension of the already-opened constant-generator instance. This
   is a materially different situation from `rank-one-edge-
   perturbation-norm.md`/`boundary-outflow-lemma.md`, both purely
   additive extensions of already-complete, already-opened programs.
2. **It needs a hypothesis the request's own text does not state**
   (the uniform contraction bound on `Φ`) to be true at all. Adding
   load-bearing hypotheses beyond what was asked is the kind of
   judgment call this project's own precedent (`weighted-matrix-tree-
   theorem.md`, `mutual-information-and-data-processing.md`) treats as
   needing sign-off, not something an autonomous run should decide
   unilaterally.

Tracked as **Low — technical and governance decision required** in
`proposals/README.md`'s Active priority table, not Medium.

## Operating instructions for an autonomous run

*(Apply only after the gate above is resolved.)*

- Step 0 (the Mathlib API survey) could be spiked at low cost to
  de-risk the estimate before any adoption decision, exactly as
  `mutual-information-and-data-processing.md`'s Step 1 and `global-
  semigroup-contraction.md`'s Step 0 were both flagged as spikeable
  ahead of adoption; Step 1 itself should wait for the gate.
- **No new axioms.** The entire route stays inside already-proved
  Scaffold operator-norm lemmas plus one already-proved (if previously
  unused) Mathlib calculus lemma; if Step 0's survey finds the exact
  API does not transfer as sketched, stop and record the precise
  obstruction in `docs/6_SGT_BACKLOG.md` rather than reaching for a
  weaker or reworked hypothesis set unilaterally.
- Ship the contraction-omission fence (QA plan above) in the same
  delivery as Step 1, not as a follow-on audit pass.

## Open next step

Blocked on the gate above. Step 0's API survey is low-cost and could
be spiked independently to inform the operator's decision, but Step 1
should not begin without explicit adoption — both for the backlog-gate
reason and the added-hypothesis reason, neither of which an autonomous
run should resolve on its own.
