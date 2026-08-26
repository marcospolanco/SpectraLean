# Proposal: The Alon–Boppana Bound for d-Regular Graphs

**Status:** **ADOPTED 2026-08-26** (see the Gate section below for the
recorded decision) — Step 0's tree-ball spike and Step 1 onward are
authorized. Originally proposed 2026-08-22 as a Step 0 survey only,
written up to the same standard as
[`weighted-matrix-tree-theorem.md`](weighted-matrix-tree-theorem.md) — a
costed candidate for an operator decision, not a self-authorizing plan.
That survey's route recommendation (Route A) and build order stand
unchanged by adoption; only the Gate has moved.

## Clean-room boundary

This planning document is internal prioritization and analysis. If counsel
approves a public repository export, restate the technical specifications
independently from standard textbook/survey sources (Hoory–Linial–Wigderson,
Nilli's paper, the original Alon–Boppana attribution). Do not copy this
proposal verbatim or consult quarantined materials.

## The claim this document is answering

Not "is Alon–Boppana true" (it is) or "is it valuable" (every SGT
practitioner would expect it next to the Cheeger/expander machinery this
repo already has — it is the theorem that makes "Ramanujan graph" a
meaningful target rather than an arbitrary label). The question is
narrower: **which proof route is the smallest honest increment from what
Scaffold has already proved, and what exactly is missing before Step 1 can
start?**

An earlier pass at this question wrongly treated closed-walk counting
against the infinite d-regular tree's generating function as *the* standard
proof and concluded the whole theorem was an expensive, foreign-flavored
combinatorics excursion. That is a real proof (it is Alon and Boppana's
original route), but it is not the only one, and not the cheapest one for
this codebase. This document corrects that and re-costs all three known
routes against what is actually on the shelf.

## Why this axis

`docs/6_SGT_BACKLOG.md` item 3 ("Expansion and cut interfaces") is the
natural home — it already lists the proved Cheeger easy direction and the
admitted hard direction as *Have*, with expander-adjacent statement shapes
as *Plan*. **It does not yet name Alon–Boppana as a candidate.** Unlike
`weighted-matrix-tree-theorem.md`, which could point at an existing backlog
gate, this proposal is the first document to name this candidate at all —
so the "named consumer" question below is answered from scratch, not
inherited.

The case for the axis: this repo has built the entire "small spectral gap
⇒ good expansion" direction (Cheeger both directions, `Expander.lean`,
mixing-time bounds) without ever stating the matching *lower* bound on how
small that gap can possibly be. Alon–Boppana is exactly that lower bound
(`λ₂ ≥ 2√(d-1) − o(1)` for d-regular graphs), and it is the standard
companion result taught in the same breath as Cheeger in every SGT course
(Spielman's course, Hoory–Linial–Wigderson's survey) — its absence next to
a working Cheeger/expander toolkit is the single most conspicuous gap in
this repo relative to the field's canon.

## What Scaffold and the pinned Mathlib already provide

A fresh survey (2026-08-22) of `Scaffold/Mathlib/GraphTheory/{Spectral,
Cheeger, Expander, SimpleGraphAdapter}.lean` and
`.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/{AdjMatrix,
Finite, Diam, Metric,StronglyRegular}.lean`, plus a repository-wide search
for `alon`, `boppana`, `nilli`, `ramanujan` (zero hits anywhere, confirmed
absent — this theorem has not been touched at any layer):

| Piece needed | Where it already lives | Covers |
| --- | --- | --- |
| Rayleigh quotient / variational characterization of `λ₂` | `Spectral.lean`, `secondEval_variational` (proved, no axioms) | The engine of the Nilli-style proof: `λ₂ = sup` of the Rayleigh quotient over vectors orthogonal to `onesVec` |
| Cauchy interlacing | `Spectral.lean`, `eigen_interlacing_principal_submatrix` (proved 2026-08-18, no axioms) | The engine of the interlacing-on-balls proof style |
| d-regularity, real-valued, as a per-graph hypothesis | `Cheeger.lean`, `regularNormalizedLaplacian A d` (`d : ℝ` is a hypothesis, not derived) | Exactly the shape Alon–Boppana's statement needs — no new regularity machinery required if this idiom is reused rather than Mathlib's `ℕ`-valued combinatorial one |
| Combinatorial d-regularity, with the constant-eigenvector fact | `AdjMatrix.lean:268` (`SimpleGraph.IsRegularOfDegree`), `AdjMatrix.lean:238` (`IsRegularOfDegree` ⇒ `adjMatrix *ᵥ const a = d * a`, i.e. `λ₁ = d` with the all-ones eigenvector) | Already proved in the pin — was wrongly assumed absent in the earlier pass |
| Graph distance and diameter | `Metric.lean` (`SimpleGraph.dist`), `Diam.lean` (`SimpleGraph.diam`, `ediam`, `dist_le_diam`, `exists_dist_eq_diam`) | Already in the pin — was also wrongly assumed absent in the earlier pass |
| Bridge from `SimpleGraph` to Scaffold's `WAdj`/`Matrix V V ℝ` world | `SimpleGraphAdapter.lean`, `SimpleGraph.toWAdj := adjMatrix ℝ`, roundtrip with `supportGraph` | Makes every fact above reachable from Scaffold's own representation without redefining regularity or distance from scratch |
| Infinite d-regular tree spectral radius `2√(d-1)` (closed form, generating-function route) | **Absent.** Chebyshev polynomials exist in the pin (`RingTheory/Polynomial/Chebyshev.lean`) but nothing connects them to tree walk-counts | Only needed by the trace/moment proof route (Route B below), not by the variational or interlacing routes |
| The Alon–Boppana statement itself, any route, any qualification | **Absent everywhere** — zero hits for `alon`, `boppana`, `nilli`, `ramanujan` in Scaffold, proposals, or docs | The one piece that is genuinely missing regardless of route |

**Correction to the record:** the earlier assessment that "no d-regularity
definition, no distance/diameter machinery" exists anywhere was wrong for
the *Mathlib* layer — both exist and are reachable through the adapter
already built for a different program (`SimpleGraphAdapter.lean`). It was
right that neither exists in Scaffold's *own* idiom yet, and right that no
route avoids doing some new work — but the size of that work is
substantially smaller than first stated.

## Calibration: three proof routes, honestly costed

**Route A — Variational / test-vector (Nilli 1991 and its later
strengthenings).** Use `secondEval_variational` directly:
`λ₂ = sup` of the Rayleigh quotient over vectors orthogonal to `onesVec`.
Pick two vertices at distance close to the diameter, build a radial test
function decaying like `(d-1)^{-r/2}` on the ball around each (this
requires each ball to be tree-like — no short cycles inside it, which for
a *specific* finite graph is a real hypothesis, not automatic, and is
usually phrased via girth or a direct "no cycle within radius r" clause),
combine the two so the result is orthogonal to `onesVec`, and compute its
Rayleigh quotient directly. Yields the diameter-dependent form
`λ₂ ≥ 2√(d-1) − O(1/⌊diam/2⌋)`. **This is the smallest increment from what
is already proved** — it reuses `secondEval_variational` as its entire
linear-algebra engine and `SimpleGraph.dist`/`diam` (already in the pin)
for the geometric side. The genuinely new work is the radial test-vector
construction and its Rayleigh-quotient computation (a real but
self-contained combinatorial calculation, not a new subfield).

**Route B — Trace / moment / walk-counting (the original
Alon–Boppana/Boppana route).** Compare `tr(A^{2k}) = Σλᵢ^{2k}` against a
lower bound on closed walks, itself lower-bounded by the infinite
d-regular tree's closed-walk count (via a covering-map/local-injectivity
argument up to the girth), and separately derive the tree's spectral
radius `2√(d-1)` via a generating-function or Chebyshev-polynomial
argument. **This is the route the earlier assessment (wrongly) treated as
the only option**, and it remains the most expensive: it needs a new
closed-walk-counting layer, a new tree-comparison/covering argument, and a
bridge to the Chebyshev polynomial API that exists in the pin but has never
been connected to graph walks. Not recommended as the first attempt.

**Route C — Interlacing on well-separated balls.** Take several
pairwise-far-apart vertices whose radius-`r` balls are trees (again a real
hypothesis on the specific graph), form the induced subgraph on their
union, and apply `eigen_interlacing_principal_submatrix` (already proved)
to transfer the large eigenvalues of each finite tree-ball back to the
ambient graph's spectrum. Some published generalizations of Alon–Boppana
use exactly this style and describe it as elementary once interlacing is
available — true here, since interlacing is already hard crust. The new
work is the multi-ball packaging (choosing enough well-separated balls and
managing the induced-subgraph bookkeeping across all of them at once),
which is a different shape of new work than Route A's single radial
vector, not obviously cheaper or more expensive without a spike.

**Recommendation: spike Route A first.** It has exactly one proved
dependency (`secondEval_variational`) doing all the linear-algebra work,
the geometric primitives (`dist`, `diam`) are already in the pin, and its
new content — one radial test vector and its Rayleigh quotient — is the
smallest, most self-contained unit of genuinely new work among the three
routes. Route C is the natural fallback if Route A's tree-ball hypothesis
turns out awkward to state in Scaffold's fixed-`V` idiom. Route B should
not be attempted first; it pays for a new combinatorial subfield
(closed-walk counting) that neither Route A nor Route C needs.

## The qualification trap — read before writing any statement

This repository has twice admitted a theorem that was false because it
under-qualified a hypothesis (`old_cheeger_lower_bound_refuted_QA`, the
pre-repair `lambda2_variational`) and named that exact risk again when
scoping `admit-perron-frobenius.md` (declining strict eigenvalue dominance
for imprimitive matrices). Alon–Boppana carries the same risk in a
different shape: **the honest statement is either asymptotic
(`o(1)` as `n → ∞` over a *family* of graphs) or diameter-dependent for a
single graph** (`λ₂ ≥ 2√(d-1) − O(1/⌊diam/2⌋)`, Route A/C's natural output).
An unqualified `λ₂ ≥ 2√(d-1)` for a single finite d-regular graph is false
in general (small graphs and short-diameter graphs violate it trivially —
e.g. `Kₙ` is `(n-1)`-regular with `λ₂ = 0` for the *adjacency* spectrum's
second-largest value in some conventions, and small diameter makes any
`O(1/diam)` error term large enough to swallow the claim). Whichever route
is chosen, **the single-graph diameter-dependent form is the one to state
first**; the asymptotic family form is a corollary once a family with
`diam → ∞` is named, not the default statement to reach for.

## Build order (not authorized to start — see Gate)

### Step 0: This survey (delivered by this document)

Route recommendation recorded above. Before Step 1 begins, spike Route A's
tree-ball hypothesis on a small concrete case (e.g. a Petersen-graph-sized
or small hypercube fixture, `Fin 5`–`Fin 10`) by hand, to get a real cost
estimate for stating "the radius-`r` ball around `v` is a tree" in
Scaffold's fixed-`V`, `Matrix V V ℝ` idiom — this is the one piece neither
this survey nor the pinned Mathlib resolves in advance, mirroring the same
kind of spike `weighted-matrix-tree-theorem.md` required of its own
Route B before commitment.

### Step 1: d-regularity and the constant-eigenvector fact, in Scaffold's own idiom

Reuse `Cheeger.lean`'s existing `d : ℝ` hypothesis pattern rather than
inventing new machinery or importing Mathlib's `ℕ`-valued
`IsRegularOfDegree` directly into the real-valued center. State and prove
`deg A i = d` (constant) ⇒ `onesVec` is an eigenvector of the adjacency
matrix with eigenvalue `d`, and that `d` is in fact the top eigenvalue
(`λ₁ = d`, via `secondEval`/`evals` machinery already on the shelf —
likely a short corollary of existing Perron-type or variational bounds,
to be confirmed at implementation time). QA: a small regular fixture
(e.g. the cycle `Cₙ`, 2-regular) computed by hand.

### Step 2: Distance and diameter, bridged from the adapter

Reuse `SimpleGraph.dist`/`diam` through `supportGraph`/`toWAdj`
(`SimpleGraphAdapter.lean`) rather than redefining distance on `WAdj`
directly. Define what "the radius-`r` ball around `v` is a tree" means
for a specific graph (likely via a girth-style no-short-cycle hypothesis),
informed by Step 0's spike.

### Step 3: The radial test vector and its Rayleigh quotient (the crux)

Construct the test vector, prove it is well-defined and nonzero, compute
its Rayleigh quotient against `secondEval_variational`'s hypotheses.
Likely needs its own sub-decomposition across multiple runs, comparable to
the electrical program's step 4 or the mixing-time program's step 3.

### Step 4: Orthogonality adjustment and the Courant–Fischer application

Combine two test vectors (from two far-apart vertices) into one orthogonal
to `onesVec`, and conclude the diameter-dependent bound via
`secondEval_variational`.

### Step 5: State the honest theorem

The diameter-dependent single-graph form, per "The qualification trap"
above — not an unqualified asymptotic claim.

### Deferred and removed

- **The asymptotic family form** (`o(1)` over an infinite family with
  `diam → ∞`) — a corollary of Step 5, not a build-order step, since it
  needs a named family (e.g. a Ramanujan graph construction) this proposal
  does not supply.
- **Route B's walk-counting/tree-generating-function layer** — explicitly
  not the first attempt; revisit only if Route A's spike (Step 0) finds
  the tree-ball hypothesis intractable in Scaffold's fixed-`V` idiom.
- **Route C as primary** — kept as the named fallback, not pursued unless
  Step 0's spike disfavors Route A.
- **Strict-dominance-style strengthenings, or connecting this to
  Ramanujan-graph *existence* (LPS construction, etc.)** — a much larger,
  separate program; out of scope here.

## QA plan

- Positive/tightness witness: a small regular graph with a known `λ₂`
  close to `2√(d-1)` (a small Ramanujan graph if a concrete one is easy to
  pin — e.g. a complete bipartite or Petersen-graph-family member — or, if
  none is convenient, a cycle `Cₙ` for growing `n` as a 2-regular sanity
  family, since `Cₙ`'s spectrum is closed-form).
- Negative/degenerate witness: a small-diameter d-regular graph (e.g.
  `K_{d+1}`) where the bound's error term is large enough that the
  statement holds only vacuously or trivially — confirming the
  diameter-dependence is load-bearing, not decorative.
- Guard witness: a non-regular graph where the theorem's `d`-regularity
  hypothesis is dropped, checked that no version of the conclusion survives
  (mirrors this repo's standing pattern of a hypothesis-necessity
  refutation, e.g. `strict_dominance_refuted_QA`).

## Gate — ADOPTED 2026-08-26

**Operator decision recorded:** adopted. The "closes the field's most
conspicuous gap next to the existing Cheeger/expander toolkit" case
below is accepted as sufficient; `docs/6_SGT_BACKLOG.md` item 3 has been
updated the same day to name this candidate. Step 0's tree-ball spike
and Step 1 onward may begin under the Operating Instructions below.

The rest of this section is kept verbatim as the record of what was
decided and why.

Same class of gate as `weighted-matrix-tree-theorem.md`, one step stronger:
that proposal could at least point to `docs/6_SGT_BACKLOG.md` item 7
already naming its candidate. This proposal is the *first* document to
name Alon–Boppana anywhere in the repository — axis 3 does not yet list it
as a candidate. Building it now would be general-purpose machinery built
ahead of a named consumer, on the strength of fitting the project's
demonstrated idiom (Route A reuses `secondEval_variational` the same way
Cheeger and Fiedler already do) and closing the field's most conspicuous
gap next to the existing Cheeger/expander toolkit — a real but different
kind of case than "X is blocked." An autonomous run should not begin
Step 1 without this decision recorded here as adopted, and should not add
this candidate to `docs/6_SGT_BACKLOG.md` item 3 unprompted either — that
edit is itself part of the decision, not a routine documentation update.

## Operating instructions for an autonomous run

*(Apply only after the Gate above is resolved.)*

- One step per run; Step 3 will likely need more than one, per this
  repository's standing precedent for its hardest steps.
- **No new axioms.** If Step 3's chosen route turns out to need machinery
  genuinely absent from both Scaffold and Mathlib beyond what this survey
  found, stop and record the precise obstruction in
  `docs/6_SGT_BACKLOG.md` rather than admitting anything.
- Survey Mathlib before each step per this repository's standing rule;
  this document's table may already answer most of it, but re-verify
  before Step 1 in case the pin has changed.
- State Step 5's theorem in the diameter-dependent single-graph form
  first; do not reach for the asymptotic family form as the default.

## Open next step

**Unblocked (2026-08-26).** Step 0's tree-ball spike is the immediate
next action (see "Build order"): spike Route A's tree-ball hypothesis on
a small concrete fixture (`Fin 5`–`Fin 10`) to get a real cost estimate
for stating "the radius-`r` ball around `v` is a tree" in Scaffold's
fixed-`V` idiom, before Step 1 (d-regularity and the constant-eigenvector
fact) begins.
