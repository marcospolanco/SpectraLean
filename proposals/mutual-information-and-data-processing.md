# Proposal: Mutual Information and the Data Processing Inequality

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-09-02 in response to an operator question about whether the
information-theory layer needs more depth to serve an AI-relevant
research direction. Authorizes no Lean changes, axiom admissions,
document rewrites, or transit-map edits.

Companion to [`finite-relative-entropy.md`](finite-relative-entropy.md)
(the KL/entropy layer this proposal extends) and
[`entropy-mixing-pinsker.md`](entropy-mixing-pinsker.md) (the entropy leg
of the mixing cascade — Pinsker, entropy decay, the entropy floor — this
proposal's intended consumer). `docs/6_SGT_BACKLOG.md` item 6
(Thermodynamics / statistical mechanics) records its own named interface
set as **complete** as of 2026-08-22/2026-09-01; this document does not
reopen that item; it proposes new machinery beyond anything it names.

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources (Cover &
Thomas, *Elements of Information Theory*, chapter 2). Do not copy this
proposal verbatim or consult quarantined materials.

Assessed from `Scaffold/Mathlib/InformationTheory/Entropy.lean` (full
read), `Scaffold/Mathlib/GraphTheory/Mixing.lean` and
`Scaffold/Mathlib/GraphTheory/Oversmoothing.lean` (targeted reads for
every `klDiv`-consuming theorem), and a repository-wide plus
pinned-Mathlib-wide search for mutual information, the data processing
inequality, and Kullback–Leibler machinery (results below).

## The claim this document is answering

Not "does this project need a bigger information-theory module" —
the operator conversation this document follows already concluded no,
not generically. The narrower question: **if one AI-relevant extension
is worth building on top of the existing entropy layer, is mutual
information plus the data processing inequality (DPI) the right pick,
and what is the minimal build?** This document answers yes to the first
half and gives the second half a concrete, honestly costed order,
building on a real find: the DPI's hardest classical step is already
most of the way proved on the shelf, not absent.

## Why this axis

`GraphTheory.Oversmoothing.lean` already contains an entropy-floor
theorem, `klDiv_walkDistribution_ge_of_eigenpair` (line 2189): at a
genuine `L_sym` eigenpair with a near-periodic mode (`|1 − μ| = 1`), the
KL divergence of a depth-`t` walk law from stationary is bounded
*below* — mixing cannot happen. `GraphTheory.Mixing.lean` has the
complementary decay direction, `klDiv_walkDistribution_le` (line 3179):
on a connected graph, that same KL divergence is bounded *above* by
`r^(2t) · ((stationaryVec A x)⁻¹ − 1)`, where `r` dominates every
nontrivial spectral-gap factor `|1 − μᵢ|`. Both are already proved, zero
axioms, and both are exactly the ingredients an information-theoretic
statement about oversmoothing needs.

Graph neural networks and other message-passing architectures apply
the same one-step operator repeatedly; over-smoothing — every node's
representation converging to the same fixed point as depth grows,
destroying the signal a downstream task needs — is a named, live
problem in that literature, not a hypothetical. Read as message
passing, `walkDistribution A t x` is the distribution a depth-`t`
process reaches starting from node `x`. If a task's label or input
signal is encoded in the starting node (`X₀`), and depth-`t`
message-passing state is `Xₜ`, the operationally meaningful "how much
of the original signal survives `t` layers" quantity is the mutual
information `I(X₀; Xₜ)`, not the KL divergence to stationary of any
single trajectory. Connecting the two needs one new object (mutual
information) and one identity (below) — not a new proof engine.

## What's already on the shelf

- `klTerm a b`, `klDiv p q`, `shannonEntropy p` — the generic layer
  (`Entropy.lean:89,98,107`), defined for `p q : V → ℝ` on any
  `Fintype V`, junk-safe (`klTerm a b = 0` when `a = 0`, matching the
  standard `0·log 0 := 0` convention).
- `klDiv_nonneg`, `klDiv_eq_zero_iff` — Gibbs' inequality, both
  directions.
- **`sum_klTerm_ge_klTerm`** (`Entropy.lean:373`, "the two-block
  log-sum bound"): for any finite index set `S`,
  `klTerm (∑ i in S, p i) (∑ i in S, q i) ≤ ∑ i in S, klTerm (p i) (q i)`
  — merging terms in a block cannot increase their KL contribution.
  This is the log-sum inequality, already fully proved, and it is
  **the exact primitive the DPI's standard proof needs** (see Route,
  below) — found already on the shelf, not something this proposal
  has to build from scratch.
- `klDiv_walkDistribution_le`, `klDiv_walkDistribution_ge_of_eigenpair`
  — the graph-level decay and floor theorems this proposal's motivating
  corollary would compose (see "Why this axis").

**Not on the shelf, checked directly:** the per-term rescaling identity
`sum_klTerm_ge_klTerm`'s own proof inlines (`hterm`, the `klTerm (c·a)
(c·b) = c · klTerm a b` homogeneity step) is proved *inside* that
theorem's body but never exposed as its own reusable lemma. Extracting
it is this proposal's real Step 1 (below).

## What the pinned Mathlib provides

**Verified absent, not merely uncited.** `Mathlib.InformationTheory`
(the only directory of that name) contains exactly one file,
`Hamming.lean` — Hamming distance and Hamming norm, nothing
probabilistic. No `kullback`, `KLDiv`, `klDiv`, `MutualInfo`, or
`dataProcessing` declaration exists anywhere in the pinned Mathlib
(repository-wide grep, empty result). `Entropy.lean`'s own header
already documents that its KL/entropy layer is original to this
project for the same reason. This proposal inherits that: mutual
information and DPI are being built from scratch in the same idiom,
not imported.

## Scope decision: stay in the explicit finite-vector idiom

`Entropy.lean` works with `p q : V → ℝ` on a `Fintype V`, not Mathlib's
measure-theoretic `MeasureTheory.Measure`/`kernel` layer. This proposal
does the same for mutual information — a joint distribution is
`pxy : X × Y → ℝ` on `Fintype X`, `Fintype Y` (a `Fintype` product,
free) — rather than reaching for `MeasureTheory.kernel` or
`ProbabilityTheory`'s independence machinery. Reasons: (1) it matches
every existing consumer, which works with `walkDistribution : ℕ → V →
(V → ℝ)`, an explicit finite vector, not a measure; (2) it avoids
pulling in a materially heavier dependency for a project whose own
entropy layer deliberately chose the elementary route once already
(`Entropy.lean`'s docstring records choosing the term-wise proof over
the available Mathlib `StrictConcaveOn`/Jensen route for exactly this
kind of idiom-fit reason).

## The route: channel monotonicity of KL divergence

**Core lemma.** For a finite "channel" `K : Y → (Z → ℝ)` with each
`K y` a valid distribution over `Z` (`∀ y, ∀ z, 0 ≤ K y z` and `∀ y, ∑
z, K y z = 1`), and any two distributions `p q : Y → ℝ`:

```
klDiv (fun z => ∑ y, p y * K y z) (fun z => ∑ y, q y * K y z) ≤ klDiv p q
```

Post-processing through the same channel cannot increase KL divergence
between the inputs. The proof decomposes into two already-solved
pieces:

1. **Per output symbol `z`,** apply `sum_klTerm_ge_klTerm` with block
   index `y`, `p_y := p y * K y z`, `q_y := q y * K y z`:
   `klTerm (∑ y, p y·K y z) (∑ y, q y·K y z) ≤ ∑ y, klTerm (p y·K y z)
   (q y·K y z)`. Already proved, zero new work.
2. **Sum over `z` and swap the order of summation** (`Finset.sum_comm`,
   free): for fixed `y`, `∑ z, klTerm (p y · K y z) (q y · K y z) =
   klTerm (p y) (q y) · ∑ z, K y z = klTerm (p y) (q y)` by the
   homogeneity identity (`klTerm (c·a) (c·b) = c · klTerm a b`, with
   `a = p y`, `b = q y`, `c = K y z` varying with `z` — this is exactly
   `sum_klTerm_ge_klTerm`'s own inlined `hterm` step, generalized) and
   `K y` summing to `1`. Summing over `y` gives `klDiv p q` on the
   nose.

Chaining these two steps gives the core lemma exactly, with no
inequality beyond the one already proved. This is a genuinely cheap
extension in this project's own terms — closer to `finite-relative-entropy.md`'s
"term-wise route already on the shelf" than to a
`weighted-matrix-tree-theorem.md`-style two-hard-pieces situation.

**The Data Processing Inequality**, as a corollary for a three-variable
Markov chain `X → Y → Z` (i.e. `Z`'s conditional law given `(X, Y)`
depends only on `Y`, via a channel `K`): fix `x`, apply the core lemma
to `p = P(Y | X = x)` and `q = P(Y)` (the marginal) through the same
channel `K`, giving `klDiv (P(Z | X = x)) (P(Z)) ≤ klDiv (P(Y | X = x))
(P(Y))` for every `x`. Average both sides over `x` weighted by `P(X =
x)` and apply the compensation identity below to convert each side into
a mutual information: `I(X; Z) ≤ I(X; Y)`.

**The compensation identity** (also needed, also cheap — pure `klTerm`
log-splitting, no new inequality): for any reference distribution `r`
over `Y`,
```
∑ x, P(x) · klDiv (P(Y | X = x)) r  =  I(X; Y) + klDiv (P(Y)) r
```
Proof: split `klTerm (P(y|x)) (r y) = P(y|x)·log(P(y|x)/P(y)) +
P(y|x)·log(P(y)/r(y))` termwise (the same `log(a/c) = log(a/b) +
log(b/c)` split `sum_klTerm_ge_klTerm`'s own proof already performs),
sum over `y`, then average over `x`. Since `klDiv (P(Y)) r ≥ 0`
(Gibbs, already proved) for **any** `r`, this immediately gives `I(X;
Y) ≤ ∑ x, P(x) · klDiv (P(Y|X=x)) r` for any reference `r` — in
particular, taking `r = stationaryVec A` and `Y = walkDistribution A t
·` gives the motivating corollary directly from `klDiv_walkDistribution_le`
with no further inequality needed:

```
I(X₀; Xₜ) ≤ E_{x ~ P(X₀)} [klDiv (walkDistribution A t x) (stationaryVec A)]
          ≤ r^(2t) · E_{x ~ P(X₀)} [(stationaryVec A x)⁻¹ − 1]
```

— a genuine, rigorous "the mutual information between the starting
label and the depth-`t` message-passing state decays with depth, at a
rate set by the spectral gap" theorem, following almost entirely from
composing what already exists.

**Alternative route considered and not preferred:** the textbook chain
rule for mutual information (`I(X; Y, Z) = I(X; Y) + I(X; Z|Y) = I(X;
Z) + I(X; Y|Z)`, DPI via `I(X;Z|Y) = 0` on a Markov chain). Rejected
for this project specifically because it needs a new object
(conditional mutual information) and new bookkeeping lemmas before it
reuses anything already proved, where the channel-monotonicity route
above reuses `sum_klTerm_ge_klTerm` directly as its only real content.

## Build order

### Step 1: Extract the homogeneity lemma

```
theorem klTerm_smul_smul {c a b : ℝ} (hc : 0 ≤ c) :
    klTerm (c * a) (c * b) = c * klTerm a b
```
Already implicit in `sum_klTerm_ge_klTerm`'s proof (`hterm`); pull it
out as its own lemma so both that theorem and the channel-monotonicity
lemma below can cite it instead of re-deriving it. Zero new proof
content, pure refactor-and-generalize.

### Step 2: Marginals and mutual information

Define `marginalLeft`/`marginalRight` for `pxy : X × Y → ℝ` (sum over
the other coordinate), then
```
noncomputable def mutualInfo (pxy : X × Y → ℝ) : ℝ :=
  klDiv pxy (fun xy => marginalLeft pxy xy.1 * marginalRight pxy xy.2)
```
`mutualInfo_nonneg` (immediate: `klDiv_nonneg` applied to the joint and
the product-of-marginals, both already-established valid
distributions) and `mutualInfo_eq_zero_iff_indep` (immediate:
`klDiv_eq_zero_iff` specialized — joint equals the product of marginals
is the standard finite-distribution definition of independence).

### Step 3: The channel-monotonicity lemma

The core lemma above: `sum_klTerm_ge_klTerm` per output symbol plus
`Finset.sum_comm` plus Step 1's homogeneity lemma. The one step likely
to need real Lean care is bookkeeping the sum-swap and the channel
row-sum hypothesis cleanly, not inventing new mathematics.

### Step 4: The compensation identity

Pure `klTerm` log-splitting plus averaging, as derived above. Immediate
corollary: `mutualInfo_le` for an arbitrary reference distribution `r`
(via `klDiv_nonneg`), specialized to the DPI corollary and to the
graph-level oversmoothing corollary in Step 6.

### Step 5: The Data Processing Inequality

`I(X; Z) ≤ I(X; Y)` for a Markov chain `X → Y → Z`, from Step 3 applied
per-`x` plus Step 4's averaging identity. The general, citable,
field-standard theorem.

### Step 6: The graph-level corollary (the actual motivating consumer)

`mutualInfo_walkDistribution_le_of_connected` (name TBD): for a
distribution `P(X₀)` over starting vertices and `Xₜ := walkDistribution
A t X₀`, `I(X₀; Xₜ) ≤ r^(2t) · E[(stationaryVec A x)⁻¹ − 1]` directly
from Step 4 plus the already-proved `klDiv_walkDistribution_le`. This
is the theorem that actually reads as "oversmoothing bound," and it
needs no new inequality beyond Steps 1–4 — only assembly.

### Deferred and removed

- **Conditional mutual information as its own object** — not needed by
  the channel-monotonicity route; would only be needed by the rejected
  chain-rule route above.
- **General `n`-variable chain rule for mutual information** — out of
  scope; Step 5's three-variable DPI is what the motivating consumer
  needs.
- **Rényi mutual information / f-divergence generalizations** — a
  separate, larger extension; not proposed here.
- **Continuous / measure-theoretic mutual information** — would need
  Mathlib's `MeasureTheory.kernel` layer this proposal deliberately
  avoids (see "Scope decision"); a different, larger proposal if ever
  wanted.
- **A named "GNN oversmoothing" theorem statement in ML terminology** —
  Step 6 delivers the mathematical content; framing it explicitly in
  message-passing/GNN vocabulary (rather than `walkDistribution`'s
  existing graph-theoretic vocabulary) is a documentation decision, not
  a proof obligation, and is left for whoever adopts this proposal to
  decide against the transit-map/marketing considerations live
  elsewhere in this repository.

## QA plan

- `mutualInfo` positive witness: two dependent binary variables (e.g.
  `X = Y`, encoded as the joint distribution supported on the diagonal)
  giving `mutualInfo = shannonEntropy` of the marginal, checked by hand
  against a small fixture.
- `mutualInfo` zero witness: an explicit product distribution (e.g.
  independent fair coins), `mutualInfo = 0` exactly.
- Channel-monotonicity fence: a fixture where the channel is *not*
  row-stochastic (violates `∀ y, ∑ z, K y z = 1`), confirming the
  hypothesis is load-bearing, not decorative — per this project's
  standing adversarial-fence discipline
  (`governance/ADVERSARIAL_REVIEW.md`), any new theorem should ship
  with this check from delivery, not as a later audit pass.
- DPI equality-case witness: `Y = Z` (the identity channel), confirming
  `I(X;Z) = I(X;Y)` exactly, not merely `≤`.
- Graph-level corollary: instantiate Step 6 on the triangle or `K₂`
  fixtures already used throughout `Mixing_QA.lean`/`Oversmoothing`
  QA, cross-checked against the existing `klDiv_walkDistribution_le`
  numeric pins those files already carry.

## Gate — this needs an operator decision, not routine backlog treatment

`docs/6_SGT_BACKLOG.md` item 6 records its named interface set as
**complete**. No open backlog item or proposal currently names mutual
information or the DPI as a blocking dependency — this document is the
same shape of case `weighted-matrix-tree-theorem.md` made for its own
axis: a strong technical fit (the core lemma is mostly already proved)
and a real but *external* motivation (an AI-relevance narrative, not an
internal blocked consumer), on the strength of a direct operator
question rather than a stated build-order gap. That is enough to
justify writing this document, per this project's own precedent, but
not enough to authorize an autonomous run to begin Step 1 on its own.
An operator should adopt this proposal explicitly (or name a different
consumer for it) before that happens.

## Operating instructions for an autonomous run

*(Apply only after the Gate above is resolved.)*

- One step per run is likely generous here; Steps 1, 2, and 4 are each
  small enough to plausibly combine with adjacent steps in a single
  run — size each run against actual proof friction encountered, not
  against this document's step numbering.
- **No new axioms.** Every piece surveyed above stays inside
  already-proved `Entropy.lean`/`Mixing.lean` machinery plus standard
  `Finset` sum manipulation; if Step 3's sum-swap or Step 5's averaging
  turns out to need something genuinely absent, stop and record the
  precise obstruction in `docs/6_SGT_BACKLOG.md` rather than admitting
  anything.
- Ship each new theorem's adversarial fence (per the QA plan above)
  in the same delivery, not as a follow-on audit — this project's own
  recent history (`adversarial-fences-entropy-family.md`) found the one
  entropy-family delivery that predated this discipline needed a full
  28-fence retrofit; do not repeat that gap here.
- Do not fold Step 6's delivery into `entropy-mixing-pinsker.md`'s own
  record or the mixing-cascade's "complete" status; this is new
  machinery layered on top, not a missing piece of that program.

## Open next step

Blocked on the Gate above, not on any technical prerequisite. Step 1
(extracting the homogeneity lemma) could be spiked at any time at
essentially no cost, but Steps 2 onward should wait for an explicit
adoption decision, or a different named consumer, per this project's
standing "no new machinery ahead of a decision" norm.
