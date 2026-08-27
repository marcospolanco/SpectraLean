# Proposal: The Alon–Boppana Bound for d-Regular Graphs

**Status: COMPLETE 2026-08-27.** ADOPTED 2026-08-26 (see the Gate
section below for the recorded decision) — Step 0 delivered 2026-08-26
(the tree-ball spike, verdict recorded under "Build order" below),
Step 1 delivered 2026-08-26 (the d-regularity interface), Step 2
delivered 2026-08-26 (the tree-ball interface at module level;
delivery record at the end of this document), Step 3's first
sub-slice delivered 2026-08-27 (the radial test vector and its
normalization; delivery record at the end of this document), Step 3's
second sub-slice delivered 2026-08-27 (the energy half — the numerator;
delivery record at the end of this document), Step 4 delivered
2026-08-27 (the two-vector orthogonalization and the Courant–Fischer
application; delivery record at the end of this document), and
**Step 5 delivered 2026-08-27 (the diameter-dependent single-graph
statement — the program's capstone `alonBoppana_nilli` plus the
classical error shape, the far-apart-to-diameter bridge, and both
priced Step-4 QA residuals; delivery record at the end of this
document). All five steps delivered as pure hard crust, zero new
axioms.** The deferred items below (the asymptotic family form; Route
B's walk-counting layer) remain deferred exactly as recorded.
Originally proposed 2026-08-22 as a Step 0 survey only, written up to
the same standard as
[`weighted-matrix-tree-theorem.md`](weighted-matrix-tree-theorem.md) —
a costed candidate for an operator decision, not a self-authorizing
plan. That survey's route recommendation (Route A) and build order
stand unchanged by adoption; only the Gate has moved.

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

**Step 0 DELIVERED 2026-08-26** (`wip/ab_spike.lean`, run
`20260826T215003Z-run-1`; executed jointly with Step 1 below). The
verdict:

- **The working idiom is BFS level-cardinality equations, not a
  tree-ness predicate.** What Nilli's Rayleigh computation actually
  consumes is `#{z : levE z = j} = 2 (d−1)^j` for `j ≤ k−1`, where
  `levE z = min (dist z x) (dist z y)` is the graph distance to the
  nearer endpoint of the edge — stating "the ball is a tree" any more
  structurally (acyclicity, walk uniqueness) buys nothing for the
  computation and costs far more to discharge. The spike's
  definitions: `levE` (min of two `SimpleGraph.dist`s on
  `supportGraph`), `levClass` (the level filter), `ballE` (the closed
  radius filter, the test vector's support; two balls' `Disjoint` is
  the far-apart condition).
- **Unit cost: one distance value per vertex-level pair.** A distance
  is a one-liner when it is `0` or `1` (`dist_eq_zero_iff_eq_or_not_reachable`,
  `dist_eq_one_iff_adj` + `supportGraph_adj` + an entry computation)
  and a bounded chase when it is ≥ 2: a walk witness for the upper
  bound plus the `0`/`1` case refutations. The walk-witness proof
  needs the Adj proofs pre-named as `have`s and the walk written
  **inline** in `SimpleGraph.dist_le` — a `have`-bound walk is opaque
  to `rfl` on its `length` (`.trans_eq rfl` at the inline cons-term
  reduces by iota, through the embedded proofs).
- **Connectivity amortizes the reachability refutations.** The
  `dist = 0` case split's `¬Reachable` branch is discharged for *all*
  vertices at once by one `SimpleGraph.connected_iff_exists_forall_reachable`
  lemma (`Signed_QA.lean`'s established pattern), after which the
  level-0 cardinality is pure min-zero arithmetic plus the two
  endpoint cases by `dist_self`.
- **The junk-zero trap is real but guarded.** `SimpleGraph.dist`
  returns `0` for unreachable pairs, so on a disconnected graph
  foreign vertices collapse into level 0 — the eventual theorem (or
  its fixtures) must carry connectivity, or the level hypothesis must
  be stated only after a reachability guard. All spike fixtures are
  connected, so the trap never fired; it is recorded for Steps 2–3.
- **`Mathlib.Combinatorics.SimpleGraph.Metric` must be imported
  explicitly** — `Spectral.lean`'s transitive imports do not reach
  `SimpleGraph.dist`.
- **Honest negative fixtures identified.** Q₃ (the cube): every
  edge's level-2 class is provably *not* full (`2 < 2·(3−1)²`) — the
  not-tree-like witness; K₃,₃: no two edges at distance `≥ 2k−1` for
  any usable `k` (diameter 2) — the not-far-apart witness; both are
  exactly where the theorem must *not* apply, the qualification
  trap's QA witnesses. C₈ is the smallest cycle where the full
  hypothesis set holds (two antipodal edges at `k = 2`).

**Cost verdict: Route A is tractable at cycle-scale fixtures and the
level-cardinality form; Steps 2–3 should define `levE`/`levClass` in
the `AlonBoppana.lean` module (not per-fixture) and state the tree-ball
hypothesis as the cardinality equations above.**

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

None — the program is **complete** (Steps 0, 1, 2, 3a, 3b, 4, and 5
all delivered; see the delivery records below). The remaining items on
this document's own record stay as recorded: the asymptotic family
form is a corollary awaiting a *named family* of d-regular graphs
with `diam → ∞` (not supplied here), and Route B's walk-counting
layer stays the explicitly-not-attempted alternative. Natural
follow-on candidates live in `docs/6_SGT_BACKLOG.md` item 3, not in
this proposal.


---

## Delivery record — Step 5 (the diameter-dependent statement; program complete), 2026-08-27

**Run:** `20260827T105501Z-run-1` · **Result:** DELIVERED, pure hard
crust, zero new axioms (count stays 10; `#print axioms` via
`wip/ab5_axcheck.lean` on all 13 audited declarations — 5 public
module + 8 public QA, the private helpers covered transitively —
reads exactly `propext, Classical.choice, Quot.sound`, every one).
QA +9 (`AlonBoppana_QA.lean`'s Step-5 section; 2576 → 2585 by the
generator metric).

**Delivered** in `Scaffold/Mathlib/GraphTheory/AlonBoppana.lean`'s new
`Packaging` section (one import added —
`Mathlib.Combinatorics.SimpleGraph.Diam`, which `Metric` does not
reach transitively):

- **`mul_sqrt_inv_eq_sqrt`** — the `√` plumbing:
  `x * √(x⁻¹) = √x`, hypothesis-free (`Real.sqrt_inv` then
  `Real.div_sqrt` — both junk-safe at `x ≤ 0`, where both sides are
  `0`), so the d-regular-tree decay factor `ρ = √((d−1)⁻¹)` pairs
  with the growth factor `(d−1)` to the spectral radius `√(d−1)`.
- **`distEdge_le_diam`** — the far-apart-to-diameter bridge, the
  piece Step 2 priced and deferred as blocked
  (`dist_le_diam` needs an `ediam ≠ ⊤` supplier): on finite connected
  input, `exists_edist_eq_ediam_of_finite` exhibits the `ediam`
  supremum at an actual vertex pair, where connectivity
  (`edist_ne_top_iff_reachable`) closes it; the four cross-endpoint
  distances each apply `dist_le_diam` and `omega` assembles the min.
- **`alonBoppana_diam_ge`** — the honest diameter bookkeeping:
  `2 (k+1) + 1 ≤ diam` under the far-apart hypothesis, i.e.
  `k + 1 ≤ ⌊diam/2⌋`. Deliberately hypothesis-side: the diameter
  bounds the *range* of usable `k` (the error decreases in `k`); it
  never supplies the tree-ball hypothesis — the qualification trap's
  reading, per this proposal's own warning section.
- **`alonBoppana_nilli`** — the capstone:
  `secondEval (d•1 − A) ≤ d − (1 + 2k√(d−1))/(k+1)` at
  `ρ := √((d−1)⁻¹)`, consuming `twoEdgeVec_secondEval_le` verbatim
  (the `IsDRegular` `d : ℝ` / `IsTreeBall` `d : ℕ` join already
  carried by that interface) with the quotient converted by the
  plumbing lemma and one `field_simp` factorization. As `k → ∞` this
  is Alon–Boppana's `2√(d−1)` barrier, error explicit.
- **`alonBoppana_nilli_classical`** — the classical error shape
  `≤ d − 2√(d−1) + 2√(d−1)/(k+1)` (weaker by exactly `1/(k+1)`,
  stated at the shape the literature quotes), pure field arithmetic
  from the capstone.

**QA** (the Step-5 section of `AlonBoppana_QA.lean`): the **C₈
capstone instance** at `k = 0` (`secondEval (2•1 − C₈) ≤ 2 − 1 = 1` —
the same number as Step 4's instance, now through the `√` packaging,
`√1 = 1` by `norm_num`); the **classical-shape instance** (`≤ 2 − 2 +
2 = 2` — the honest weak-at-small-`k` reading: at the smallest usable
radius the error term swallows the content, exactly the qualification
trap the proposal documents); the **diameter instance**
(`3 ≤ diam (supportGraph C₈)` through the bridge — C₈'s actual
diameter is `4`); the **loop-pair orthogonality fence** (the priced
Step-4 residual, on the new `abP3L` fixture — P₃ plus a loop at
vertex 2, whose support graph provably equals `abP3`'s since
`supportGraph_adj` demands distinct endpoints): the genuine edge's
one-level tree ball holds, the loop's level-0 class is `{2}` (card
`1 ≠ 2 (d−1)⁰`), so `IsTreeBall` fails and the orthogonality
conclusion fails with it (`⟨![1, 1, −1], onesVec⟩ = 1 ≠ 0`) —
`twoEdgeVec_dotProduct_onesVec`'s `htb2` isolated exactly where it
enters; and the **independent engine route at the integer witness**
(the other priced residual): the globally supported
`![1, 1, 0, −1, −1, −1, 0, 1]` is orthogonal to `onesVec` (raw),
has squared norm `6` (raw) and adjacency quadratic form `8` (raw —
the support-`{0,1,3,4,5,7}`²-filtered double sum, every one of the 36
`abC8` entries by `rfl`), so `secondEval_le_rayleigh` at this witness
gives `secondEval (2•1 − C₈) ≤ (2·6 − 8)/6 = 2/3` — strictly stronger
than both theorem routes' `≤ 1`, through a structurally different
vector.

**Verification:** spike first (`wip/ab5_spike.lean`, module side and
QA side iterated to zero errors/warnings before any shelf Lean); `lake
env lean` zero errors/zero warnings on both changed files; explicit
`lake build` targets ✔ (2011/2011 module, 2012/2012 QA — the
stale-olean remediation applied once before the QA elaboration);
`#print axioms` — the standard three only, all 13; **full `lake
build` ✔ (2389/2390, "Build completed successfully") immediately
followed by `check_build_completeness.py` — 113/113 fresh, 0 stale, 0
missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated (**2585/10/0**).

**Technique findings for downstream runs** (recorded from spike
failures): `Real.sqrt_inv` is hypothesis-free and `Real.div_sqrt`
likewise (`x / √x = √x`, junk-safe) — so
`x * √(x⁻¹) = √x` needs no positivity case-split
(`rw [Real.sqrt_inv, ← div_eq_mul_inv, Real.div_sqrt]`); Mathlib's
`SimpleGraph.dist_le_diam` takes the `ediam ≠ ⊤` supply as an
explicit hypothesis, and the finite-attainment route
(`exists_edist_eq_ediam_of_finite` + `edist_ne_top_iff_reachable`) is
the cheap supplier on connected `Fintype` input — the Step-2 blocker
dissolved in six lines; `simp` on a `dist`-shaped goal *rewrites the
goal into* the `dist_eq_zero_iff_eq_or_not_reachable` disjunction and
stalls on connected input (close the `z = x → dist = 0` direction by
`subst` + `exact SimpleGraph.dist_self`, never `simp`); ℕ-min
`min a a = a` is `min_self`, not `min_id`; the if-table route for
vector values on `Fin 8` needs the table stated in the *filter's*
shape (`if z ∈ S then _ else 0`, `S` an explicit insert-literal —
`simp` cannot unfold a named `Finset` def unless it is in the simp
set), with per-case proofs by kernel `rfl` (the decidable
if-conditions and `vecCons` entries both reduce); kernel `rfl` does
NOT evaluate ℝ arithmetic (`(1:ℝ) * (1:ℝ) = 1` is not `rfl` — Cauchy
quotients), which is why the entry-have + `norm_num` recipe exists;
`norm_num` normalizes casts inside proof arguments, and `linarith`
then still sees different atoms — close such goals by `norm_num at h ⊢`
then `exact h` (proof-irrelevance absorbs the proof-argument
differences); and `Finset.sum_subset`-shaped outer filters must be
introduced as type-ascribed `have`s (a bare `rw [Finset.sum_subset
...]` leaves an unresolved set metavariable and fails).

**Program-level closing note.** Every step of Route A landed as pure
hard crust against the proved `secondEval_variational` engine, zero
axioms, exactly as the 2026-08-22 survey priced it. The two deferred
items (the asymptotic family corollary, Route B) stay deferred.

---

## Delivery record — Step 4 (the two-vector orthogonalization), 2026-08-27

**Run:** `20260827T072423Z-run-1` · **Result:** DELIVERED, pure hard
crust, zero new axioms (count stays 10; `#print axioms` via
`wip/ab4_axcheck.lean` on all 34 audited declarations — 17 public
module + 17 public QA, the private helpers covered transitively —
reads exactly `propext, Classical.choice, Quot.sound`, every one).
QA +16 (`AlonBoppana_QA.lean`'s Step-4 section; 2560 → 2576 by the
generator metric).

**Delivered** in `Scaffold/Mathlib/GraphTheory/AlonBoppana.lean`'s new
`TwoEdge` section (no new imports, no umbrella change):

- **`radialVec_sum_eq`** — the equal-mass lemma: under `IsTreeBall`,
  the radial vector's total mass reduces level-by-level to
  `∑_{j≤k} 2 (d−1)^j ρ^j` — a function of `(d, ρ, k)` only, so the
  two edges' vectors have *equal* mass and their difference is
  orthogonal to `onesVec` with no regularity hypothesis at the
  interface level.
- **`twoEdgeVec`** with `twoEdgeVec_apply`,
  **`twoEdgeVec_dotProduct_onesVec`** (= 0 under the two tree balls),
  **`twoEdgeVec_dotProduct_self`** (= `4 (k+1)` under disjoint
  radius-`k` balls — the two 3a denominators add, the cross support
  vanishes by `radialVec_dotProduct_eq_zero_of_disjoint`),
  `twoEdgeVec_ne_zero`.
- **`radialVec_cross_dotProduct_eq_zero`** — the cross-edge
  elimination `⟨f₁, A f₂⟩ = 0` under disjoint radius-`(k+1)` balls:
  a support edge from a radius-`k` vertex of ball 1 lands its head at
  radius `≤ k+1` of ball 1 (3b's own `levE_le_levE_add_one_of_adj`
  — the Lipschitz lemma's first downstream consumer), and the two
  radius-`(k+1)` balls are disjoint — `levE_cross_adj_eq_zero` is
  the False-extractor. **This is where the far-apart threshold
  `(k+1) + (k+1) < distEdge` enters**, at its exact constant.
- **`dotProduct_mulVec_symm`** (the symmetric-matrix swap
  `⟨a, A b⟩ = ⟨b, A a⟩`, by the honest double-sum reindexing +
  `hA.apply`) and **`quadForm_sub`** (`xᵀA(f−g)x = xᵀAfx − 2⟨f, A g⟩
  + xᵀAgx`) — general algebra, consumed by the numerator bound and
  by QA's decomposition route.
- **`twoEdgeVec_quadForm_ge`** — the doubled numerator
  `2·(2 + 4k(d−1)ρ) ≤ xᵀAx` (each 3b bound + the eliminated cross),
  and **`twoEdgeVec_rayleigh_ge`** — the same `(2+4k(d−1)ρ)/(2(k+1))`
  quotient as the single vector (the doubling cancels).
- The engine layer — **`smul_one_sub_isSymm`**,
  **`smul_one_sub_mulVec_onesVec`** (`(d•1 − A) *ᵥ onesVec = 0` from
  Step 1's eigen-equation), **`quadForm_smul_one_sub`**
  (`xᵀ(d•1−A)x = d‖x‖² − xᵀAx`) — and the headline
  **`twoEdgeVec_secondEval_le`**:
  `secondEval (d•1 − A) ≤ d − (2+4k(d−1)ρ)/(2(k+1))` through
  `secondEval_le_rayleigh` (PSD from Step 1's AM–GM domination,
  kernel from the eigen-equation, orthogonality from the equal-mass
  lemma) — **the program's first eigenvalue-level statement**.

**QA** (the Step-4 section): the **C₈ antipodal-pair positive** —
orthogonality both routes (raw `4−4 = 0` by per-vertex enumeration at
the two value oracles — the `(4, 5)` oracle `radial45_val` new, level
1 pinned to `{3, 6}` by adjacency-level facts — vs the theorem);
the **norm `8 = 4(k+1)`** by the theorem through the delivered
antipodal disjointness; the **numerator raw by decomposition**
(`Q(g) = 8` from the 3b pin `Q(f₁) = 6`, its `(4,5)` mirror `6`, and
the cross `⟨f₁, A f₂⟩ = 2` — the two cross edges `(2,3)`/`(6,7)` —
joined by `quadForm_sub`); the **`hfar` fence** at `k = 1` (both
radius-2 tree balls genuine, `distEdge = 3 < 4`, numerator refuted at
`8 < 12` while the norm identity survives — the `(k+1)`-threshold
isolated exactly); the **P₃ overlap fence** (norm identity refuted at
`2 ≠ 4`, ball disjointness isolated); and the **headline instance**
`secondEval (2•1 − abC8) ≤ 2 − 1` at `k = 0`, `IsDRegular abC8 2`
(row sums by rfl-verified entries).

**Verification:** spike first (`wip/ab4_spike.lean` — module side
and QA side iterated to zero errors/zero warnings before any shelf
Lean); `lake env lean` zero errors/zero warnings on both changed
files; explicit `lake build` targets ✔ (2010/2010 module, QA);
`#print axioms` — the standard three only, all 34; **full `lake
build` ✔ (2388/2389, "Build completed successfully") immediately
followed by `check_build_completeness.py` — 113/113 fresh, 0 stale,
0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated idempotent
(**2576/10/0**).

**Technique findings for downstream steps** (recorded from spike
failures): `include hA in` re-includes the section variable with its
original *implicit* binder — for explicit passing declare a local
`(hA : A.IsSymm)` binder instead; `rw` with an equation about a
definition's application (e.g. `abC8 0 0 = 0`) **unfolds the
definition throughout the goal** (motive construction), so later
equation rewrites miss — use `simp only [e0, …]` with have-equations;
`fin_cases` on a bound variable replaces it by the `(fun i => i)
⟨k, ⋯⟩` wrapper — enumerate instead by `rcases (show i = 0 ∨ … by
fin_cases i; all_goals simp_all) with rfl | …` so haves stated at
plain OfNat literals match; `norm_num`/`omega` cannot decide
Fin-literal if-conditions (`(3 : Fin 8) = 4 ∨ …`) — prove the
¬-condition haves by `simp` and rewrite `if_neg`, or state per-vertex
value lemmas rather than if-forms (the P₃ levE oracles are point
lemmas for exactly this reason); in this pin `Matrix.mulVec_one` is
the *row-sum* form and the identity action is `Matrix.one_mulVec`
(`(c • M) *ᵥ v = c • (M *ᵥ v)` is `Matrix.smul_mulVec_assoc`);
`div_le_div_iff` is deprecated to `div_le_div_iff₀`, and
`mul_div_cancel₀` here has shape `b * (a / b) = a` — for `(c*D)/D = c`
use `field_simp`; a `have`-bound walk is still opaque to `rfl` on its
`length` (the Step-0 finding, hit again) — inline the walk in
`SimpleGraph.dist_le`; `Finset.disjoint_right.1 hdis hb₂ hb₁ : False`
takes the two membership proofs with the element implicit; and
width-8 row sums evaluate by `Fin.sum_univ_eight` + per-entry
rfl-haves + `simp only […]` + `norm_num`, where plain `simp [abC8]`
and `norm_num [abC8]` both stop at the recorded vecCons opacity.

**Remaining QA (named, bounded):** the loop-pair orthogonality fence
(the P₃ pair `(0, 1)`/`(2, 2)`: `IsTreeBall` fails at the loop's
one-element level 0 and `⟨g, 1⟩ = 1 ≠ 0` — fixtures and the value
oracles now on file) and an independent engine route to the headline's
conclusion (the integer witness `![1, 1, 0, −1, −1, −1, 0, 1]` with
`R_A = 8/6 = 4/3 ≥ 1`, `R_{2•1−A} = 2/3 ≤ 1` — computed, not yet
formalized). Either fits Step 5's run alongside the packaging.

---

## Delivery record — Step 3, sub-slice 3b (the energy half: the numerator), 2026-08-27

**Run:** `20260827T052400Z-run-1` · **Result:** DELIVERED, pure hard
crust, zero new axioms (count stays 10; `#print axioms` via
`wip/ab3b_axcheck.lean` on all 19 audited declarations — 8 public +
11 QA, the private helpers covered transitively — reads exactly
`propext, Classical.choice, Quot.sound`, every one). QA +11
(`AlonBoppana_QA.lean` extended with the Step-3b section; 2549 → 2560
by the generator metric).

**Delivered** in `Scaffold/Mathlib/GraphTheory/AlonBoppana.lean`'s new
`Energy` section (no new imports, no umbrella change):

- **`levE_le_levE_add_one_of_adj`** — the BFS level function is
  1-Lipschitz along support-graph edges, from a junk-safe adjacency
  triangle (`dist_le_dist_add_one_of_adj`, private: in the reachable
  regime a shortest-walk prefix, in the junk regime a contraposed
  reachability) applied at both endpoints and collapsed by `omega` at
  the min.
- **`exists_levE_parent`** — the parent lemma: every vertex at level
  `≥ 1` has a support-adjacent neighbor exactly one level down
  (`exists_pred_of_one_le_dist`, private: the head of a shortest walk
  to the min-attaining endpoint, the level equality closed by
  Lipschitz from both sides). **No connectivity hypothesis** — this is
  the spike's answer to the recorded hard piece: the cardinality
  equations give level sizes, not edge counts, so the numerator is
  harvested *from below*, one parent edge per interior vertex, and a
  lower bound is all the variational route needs. No strengthening of
  `IsTreeBall` was required.
- **`interiorE`** (levels `1..k`, level 0 excluded) with
  `interiorE_zero`, `interiorE_succ_union`, and the **interior
  level-sum bridge `sum_interiorE_eq_sum_levels`**
  (`sum_ballE_eq_sum_levels`'s pattern at the parent-carrying part of
  the ball, summed over `Finset.Ico 1 (k+1)`).
- **`radialVec_quadForm_ge`** — the headline numerator bound
  `2 + 4 k (d−1) ρ ≤ quadForm A (radialVec …)`, under the existing
  `IsTreeBall` at radius `k+1` plus a `0`-or-`≥ 1` weight discipline
  (`∀ i j, A i j = 0 ∨ 1 ≤ A i j` — each parent edge weighs at least
  `1`), distinct endpoints `x ≠ y`, a genuine edge `A x y ≠ 0`,
  `1 < d`, the normalization `ρ^2 = ((d−1:ℕ):ℝ)⁻¹`, and `0 ≤ ρ`. The
  proof harvests a pairwise-disjoint selection of nonnegative terms of
  the double sum — both orders of the endpoint edge, both orders of
  every interior vertex's parent edge — and collapses each level's
  `2 (d−1)^j ρ^{2j−1}` to exactly `2 (d−1) ρ` (the same
  growth-cancels-decay arithmetic as the 3a denominator, at odd
  powers).
- **`radialVec_rayleigh_ge`** — the Rayleigh-quotient corollary
  joining the numerator bound to the delivered
  `radialVec_dotProduct_self`: `(2 + 4 k (d−1) ρ) / (2 (k+1)) ≤
  rayleigh A (radialVec …)` — Nilli's `(1 + 2 k √(d−1)) / (k+1)`
  before the Step-5 `√` packaging. The exact interface Step 4
  consumes.

**QA** (the Step-3b section of `AlonBoppana_QA.lean`): the **C₈
numerator pin, tight at equality** — `abC8_radial_quadForm_eq_six`
computes `xᵀAx = 6` by enumeration (the radius-1 ball's four
restricted row sums `(2, 2, 1, 1)` weighted by indicator entries,
every matrix entry by `rfl`, no theorem input) against
`abC8_radial_energy_thm` reading `2 + 4·1·1·1 = 6` through
`abC8_isTreeBall` — the routes share no mechanism and the bound is
*attained* (every harvested term visible in the raw number: the
edge's `2` plus the four level-1 parent edges' `4`); the **`k = 0`
pair** both routes (`2 ≤ 2`; `isTreeBall_one_of_connected`'s second
consumer); the **Rayleigh instance** `6/4 ≤ R`; and **three
hypothesis fences**, one per new hypothesis: the **P₃ pseudo-edge**
(`abP3_pseudoEdge_fence`, `hedge` isolated — every other hypothesis
holds at `k = 0`, `d = 2`, `ρ = 1`; the test vector is the indicator
of `{0, 2}`, spans no edge, numerator `0 < 2`), the **half-weight
edge** (`abHalfK2_fractional_fence`, `h01` isolated — numerator
`1/2 + 1/2 = 1 < 2`: a parent edge of fractional weight is exactly
what the from-below harvest cannot price), and the **one-vertex loop
with unreachable partner** (`abLoop2_loop_fence`, `hxy` isolated —
the junk-zero vertex fills the level-0 cardinality equation so
`IsTreeBall` *genuinely holds*, and the numerator is the loop's
single ordered contribution `1 < 2`: distinct endpoints are what make
the selection's `(x, y)` and `(y, x)` two different ordered pairs).

**Verification:** spike first (`wip/ab3b_spike.lean` — module side
and QA side iterated to zero errors/zero warnings before any shelf
Lean); `lake env lean` zero errors/zero warnings on the module and
the QA file; explicit `lake build` targets ✔ (2010/2010, 2011/2011);
`#print axioms` — the standard three only, all 19; **full `lake
build` ✔ (2388/2389, "Build completed successfully") immediately
followed by `check_build_completeness.py` — 113/113 fresh, 0 stale, 0
missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated idempotent (**2560/10/0**, md5-stable).

**Technique findings for downstream steps** (recorded from spike
failures): `choose` in this pin turns *hypothesis binders* into
function arguments — package the choice statement with the hypothesis
inside the ∃-body (`∃ p, (1 ≤ levE z → …)`) and destructure the
conjunction per use, or the parent function takes the hypothesis as
an argument; `Finset.sum_le_sum_of_subset_of_nonneg` takes `∀ i ∈ t,
i ∉ s → 0 ≤ f i` (the `i ∉ s` matters when giving the lemma a
standalone `have` — ascribe the full statement so the Finsets infer);
`Finset.disjoint_right.mpr` takes the *second* set's membership first
and the ¬-side as a `q ∈ s → False` function — `fun q hq2 hq1 => by`
binds membership-then-membership through the ¬-function's unfolding;
`rw [Finset.sum_insert …]`'s residual associativity needs an explicit
`ring` (rw does not auto-close `a + (b + (c + d)) = a + b + c + d`);
an unparenthesized `∑ x ∈ s, body` does not scope a body placed on
the *next line* (parenthesize multi-line summands); `div_le_div_right`
is deprecated to an iff (`div_le_div_iff_of_pos_right hc : a/c ≤ b/c
↔ a ≤ b` — use `.2`); `radialVec_dotProduct_self`'s `2 * (k+1)`
elaborates as `2 * ((k:ℝ) + 1)`, so consumers' denominators should be
stated in that exact shape for `rw` to match; and
`radVec_of_mem_ballE`'s `ρ` is not inferable from the ball membership
alone (pass `(ρ := ρ)`).

---

## Delivery record — Step 3, sub-slice 3a (the radial test vector and its normalization), 2026-08-27

**Run:** `20260827T012700Z-run-1` · **Result:** DELIVERED, pure hard
crust, zero new axioms (count stays 10; `#print axioms` via
`wip/ab3_axcheck.lean` on all 18 audited declarations — 8 public +
10 QA, the two private QA level-oracle helpers covered transitively —
reads exactly `propext, Classical.choice, Quot.sound`, every one). QA
+10 (`AlonBoppana_QA.lean` extended with the Step-3 section; 2539 →
2549 by the generator metric).

**Delivered** in `Scaffold/Mathlib/GraphTheory/AlonBoppana.lean`'s new
`RadialVector` section (no new imports, no umbrella change):

- **`radialVec A hA x y ρ k`** — Nilli's radial test vector: on the
  radius-`k` ball of the edge `(x, y)`, the value `ρ ^ levE z`
  (constant per BFS level, decaying by `ρ` per level), `0` outside.
  The d-regular-tree normalization is carried by consumers as the
  hypothesis `ρ ^ 2 = ((d − 1 : ℕ) : ℝ)⁻¹` — the `√` plumbing stays in
  the Step-5 packaging, exactly where the join to `IsDRegular`'s
  `d : ℝ` idiom is already deferred.
- The interface: `radialVec_apply` (entry form),
  `radialVec_of_mem_ballE`/`radialVec_eq_zero_of_not_mem_ballE`
  (support = `ballE`), `radialVec_left` (the left endpoint always
  carries `1`), `radialVec_ne_zero` (nonvanishing at every radius and
  every `ρ`).
- **`sum_ballE_eq_sum_levels`** — the layer-cake sum bridge: any
  function summed over the radius-`k` ball equals its level-by-level
  sum. The summation form of `ballE_card_eq_sum` (same
  `ballE_succ_union` + pairwise-disjoint induction), stated at a
  function because the squared norm is level-constant but not
  constant.
- **`radialVec_dotProduct_self`** — the headline normalization
  identity: `⟨ρ^{lev}, ρ^{lev}⟩ = 2 (k + 1)` exactly, under
  `IsTreeBall` at radius `k+1` and `ρ ^ 2 = ((d−1 : ℕ) : ℝ)⁻¹`. The
  proof is the per-level collapse `2 (d−1)^j · ρ^{2j} = 2` (geometric
  growth against geometric decay, via `pow_mul` + `mul_pow` +
  `mul_inv_cancel₀`), summed over `k + 1` levels through the bridge.
  **The denominator of Nilli's Rayleigh quotient, computed exactly** —
  the first theorem consumer of the Step-2 level machinery, and
  load-bearing growth in the strategy's sense: a wrong `levE`, a wrong
  `ballE` filter shape, or a wrong `IsTreeBall` equation breaks the
  identity's type or truth. `1 < d` is load-bearing at exactly the
  cancellation step (at `d = 1`, `ρ = 0` is junk-admissible through
  `0⁻¹ = 0` while `(d−1)^j` kills the counts — QA fences it below).

**QA** (the Step-3 section of `AlonBoppana_QA.lean`): the **C₈
squared-norm pin by two independent routes** at `k = 1`, `ρ = 1`,
`d = 2` — `abC8_radial_norm_raw` computes `4` by per-vertex
enumeration (the level-0/level-1 membership oracles
`abC8_levE_zero_iff`/`abC8_levE_one_iff` derived from the delivered
`levClass_zero_eq`/`abC8_levClass_one_eq`, the indicator sum the
set's card by `decide`) while `abC8_radial_norm_thm` obtains the same
number through the identity at `abC8_isTreeBall` — the routes share no
mechanism; the **`k = 0` pair** (the theorem at
`isTreeBall_one_of_connected` — that Step-2 lemma's first consumer —
vs raw enumeration at the level-0 pair, `2 = 2 (0+1)`); the K₂
**`d = 1` degeneracy fence** `abK2_radial_d1_fence` (the tree-ball
predicate holds at `d = 1` — level 1 demanded empty and empty, via
`abK2_levE_zero`: both vertices are endpoints — the normalization
hypothesis holds at `ρ = 0` through `0⁻¹ = 0`, and the vector is
`![1, 1]` at squared norm `2 ≠ 2 (1+1) = 4`: `hd1` isolated exactly
where the module docstring names it).

**Verification:** spike first (`wip/ab3_spike.lean` — module side and
QA side iterated to zero errors/zero warnings before any shelf Lean);
`lake env lean` zero errors/zero warnings on the module and the QA
file; explicit `lake build` targets ✔ (2010/2010, 2011/2011);
`#print axioms` — the standard three only, all 18; **full `lake
build` ✔ (2388/2389, "Build completed successfully") immediately
followed by `check_build_completeness.py` — 113/113 fresh, 0 stale,
0 missing, exit 0** (the run hit the mtime half of the documented
staleness remediation once — a `touch`-and-replay left an artifact
mtime older than source; the artifact-removal rebuild closed it);
`lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated idempotent (**2549/10/0**, md5-stable).

**Technique findings for downstream steps** (recorded from spike
failures): the `2 * a^j * b^j` per-level product needs an explicit
`mul_assoc` *before* `← mul_pow` (the reversed rewrite searches the
right-associated shape and the `2`-headed product is
left-associated); `nsmul_eq_mul` (root, `Mathlib.Data.Nat.Cast`)
converts `Finset.sum_const`'s ℕ-smul to multiplication where
`Nat.smul_one` does not exist; `Finset.sum_subset`'s zero-function
argument should be pre-proved as a named `have` (an inline `by rw`
leaves metavariable-headed membership that unifies with the wrong
side); `intro z (rfl | rfl | …)` is not syntax — `intro z h` then
`rcases h`; `simp` flattens nested `Finset.mem_insert` in *reverse*
insertion order, so iff-helper statements should convert with explicit
`rcases` rather than `simpa` when the disjunct order matters; and
`.le` on an equation rewrites at the equation's own constant (a
`levE = 0` fact gives `≤ 0`, not `≤ 1` — thread with
`.le.trans (Nat.zero_le 1)` or `omega`).

---


## Delivery record — Step 2 (the tree-ball interface), 2026-08-26

**Run:** `20260826T232419Z-run-1` · **Result:** DELIVERED, pure hard
crust, zero new axioms (count stays 10; `#print axioms` via
`wip/ab2_axcheck.lean` on all 38 audited declarations — 18 public +
20 QA — reads exactly `propext, Classical.choice, Quot.sound`, every
one). QA +19 (`AlonBoppana_QA.lean` extended with the Step-2 section;
2520 → 2539 by the generator metric).

**Delivered** in `Scaffold/Mathlib/GraphTheory/AlonBoppana.lean`'s new
`TreeBall` section (the module's second import added —
`Mathlib.Combinatorics.SimpleGraph.Metric`, the Step-0 verdict's
explicit-import requirement):

- **The Step-0 verdict's definitions at module level** (no longer
  per-fixture): `levE` (BFS level from an edge — the min of the two
  endpoint distances on `supportGraph`), `levClass` (the level
  classes), `ballE` (the closed radius filter — the Step-3 test
  vector's support).
- **The junk-zero trap stated, not hidden**: `levE_eq_zero_iff` is
  the honest disconnected form (level 0 collects the endpoints *and*
  every unreachable vertex), from which
  `levE_eq_zero_iff_of_connected` derives the clean form — the
  spike's promised amortization: one connectivity hypothesis
  discharges every reachability refutation.
  `levClass_zero_eq`/`levClass_zero_card`: level 0 is exactly the
  endpoint pair, the `j = 0` cardinality equation free of regularity
  (`isTreeBall_one_of_connected`: the one-level predicate holds at
  every `d`).
- **`IsTreeBall`** — the tree-ball predicate exactly as the Step-0
  verdict priced it: `#{z | levE z = j} = 2 (d−1)^j` for every
  `j < k`. `d : ℕ` with truncated subtraction (`(1−1)^j = 0` — the
  perfect-matching case); the join to `IsDRegular`'s `d : ℝ` idiom is
  the Step-3–5 packaging.
- **The ball algebra and the layer-cake bridge**:
  `ballE_mem_iff` (min-le unpacking), `ballE_zero`, `ballE_mono`,
  `levClass_pairwise_disjoint` (a vertex has one level),
  `ballE_succ_union` (radius `r+1` = radius `r` plus the new level),
  and **`ballE_card_eq_sum`** — under `IsTreeBall` at radius `k+1`,
  the ball of radius `k` has exactly `∑_{j ≤ k} 2 (d−1)^j` vertices
  (induction on the layer-cake decomposition at the pairwise-disjoint
  levels; the `(k+1)` form keeps `k` junk-free). This is the
  normalization input the Step-3 test vector's squared norm consumes.
- **The far-apart condition**: `distEdge` (the least cross-endpoint
  graph distance — the standard "two edges at distance `≥ 2k−1`"
  quantity) and **`ballE_disjoint_of_lt_distEdge`** — every
  cross-endpoint distance exceeding `r + s` makes the two balls
  disjoint, by the connected triangle inequality at all four
  endpoint pairings (a shared vertex bounds one cross distance by
  `r + s`). The load-bearing separation input of Step 4's
  orthogonalization.

**QA** (`AlonBoppana_QA.lean`'s Step-2 section, per this proposal's
QA plan's negative-witness clause as far as it applies before the
theorem exists): the **C₈ positive** — `IsTreeBall abC8 .. 0 1 2 2`
(level 1 pinned to exactly `{2, 7}` by adjacency-level facts only:
`min = 1` forces one distance to be `1`, the neighbors-of-endpoint
exhaustion, `dist_self` killing the endpoint cases), the antipodal
disjointness `Disjoint (ballE .. 0 1 1) (ballE .. 4 5 1)` through the
far-apart theorem at four cross distances ≥ 3 — each proved by
**short-walk exhaustion** (`dist_le_two_cases_of_connected`: a
connected-graph distance ≤ 2 is a self, an adjacency, or a common
neighbor — each refuted by rfl-verified entries; only *lower* bounds
are ever needed, so no walk witnesses at all), and the layer-cake
cardinality by **two independent routes** (direct set enumeration
`ballE .. 1 = {0, 1, 2, 7}` via the neighbor lemmas vs the
geometric-sum theorem through the tree-ball instance — one number,
two constructions). The **C₄ wrap-around negative**:
`¬ IsTreeBall abC4 .. 2 3` — level 2 is demanded at
`2 (d−1)² = 2` vertices and is provably *empty* (every C₄ vertex sits
within level 1 of the edge); the qualification trap's QA witness,
delivered before the theorem it guards. The **threshold-tightness
fence**: at min cross-distance exactly `r + s = 2` (near-antipodal
edges) the radius-1 balls provably *intersect* (vertex `2` in both) —
the strict inequality of the disjointness theorem is load-bearing.

**Verification:** spike first (`wip/ab2_spike.lean` — module side and
QA side iterated to zero errors/zero warnings before any shelf Lean
touched; technique findings recorded below); `lake env lean` zero
errors/zero warnings on the module and the QA file; explicit `lake
build` targets ✔ (2010/2010, 2011/2011); `#print axioms` — the
standard three only, all 38; **full `lake build` ✔ (2388/2389,
"Build completed successfully") immediately followed by
`check_build_completeness.py` — 113/113 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated idempotent (**2539/10/0**, md5-stable). This run also
repaired a latent name typo in the uncommitted Step-1 QA file
(`Finset.sum_univ_two` → `Fin.sum_univ_two`, a nonexistent constant
caught by this run's direct elaboration of the QA file — the exact
failure class `check_build_completeness.py` was built to guard).

**Technique findings for downstream steps** (all recorded from spike
failures, at `Fin 8` scale):

- **`vecCons` at `Fin`-literal columns `≥ 4` is opaque to
  `simp`/`norm_num`** (`Fin.sum_univ_eight` leaves `![..] 5` terms;
  ℝ blocks `decide`). The working route is **evaluation by `rfl`**:
  `abC8_entries` (`∀ i j, abC8 i j = 0 ∨ abC8 i j = 1`, each case
  `first | Or.inl rfl | Or.inr rfl`), per-value facts
  (`have e : abC8 5 1 = 0 := rfl`), and `show ... from rfl` inside
  refutations. Row *sums* at width 8 are therefore not cheaply
  computable — C₈'s 2-regularity is not used by any Step-2
  obligation, and Step 3 should not assume it is.
- **`simp only [levE]` normalizes `min` to `⊓`**, which `omega` does
  not see; use **`unfold levE`** (pure delta) so the `min` survives
  for `omega`.
- **`omega` cannot refute `Fin`-literal disjunctions** (`0 = 7 ∨
  0 = 2` is foreign atoms to it): split the membership iff with
  `constructor`, refute the false side by `rintro (h' | h') <;>
  exact absurd h' (by decide)`, and close the true side by the
  disjunct's `rfl`.
- **The `rcases`-`rfl` substitution from a `fin_cases`-built
  disjunction introduces `(fun i => i) ⟨k, ⋯⟩`-wrapped literals**
  that mismatch hand-written plain-literal facts; state the case
  enumeration as a named `show` (plain literals) and `subst` it, or
  `rw [h]` so the goal's literals come from the statement.
- An **anonymous `⟨_, _⟩` adjacency against `Walk.cons`'s still-
  implicit `G` is unelaborable** (the expected type is a
  metavariable-headed `Adj`): pass a term-typed adjacency fact
  (`abC8_adj`) instead.
- `Nat.eq_zero_or_pos` (not `le.eq_or_lt`, which equates to the
  *bound*), `Finset.disjoint_right` for Finset `Disjoint` goals
  (direct `intro` on `Disjoint` unfolds to the lattice `≤`-form),
  and `h.le` to convert a `dist = 1` pin into the `≤` side of
  `ballE_mem_iff`.

---

## Delivery record — Step 1 (the d-regularity interface), 2026-08-26

**Run:** `20260826T215003Z-run-1` · **Result:** DELIVERED, pure hard
crust, zero new axioms (count stays 10; `#print axioms` via
`wip/ab_axcheck.lean` on all 22 audited declarations — 4 public +
18 QA — reads exactly `propext, Classical.choice, Quot.sound`, every
one). QA +14 (`AlonBoppana_QA.lean` a new file; 2506 → 2520 by the
generator metric).

**Delivered** in the new focused `Scaffold/Mathlib/GraphTheory/AlonBoppana.lean`
(importing `Spectral` only; umbrella import added; the program's home
for Steps 2–5):

- `IsDRegular A d` — regularity as a hypothesis in the shelf's
  `d : ℝ` idiom, exactly as this proposal's Step 1 prescribed (no new
  machinery, no Mathlib `IsRegularOfDegree` import).
- `adjacency_mulVec_onesVec` — `A *ᵥ onesVec = d • onesVec`, a
  row-sum computation hypothesis-free beyond regularity.
- `quadForm_le_of_isDRegular` — the AM–GM row-sum domination
  `xᵀAx ≤ d · (x ⬝ᵥ x)`: entrywise `a i j x i x j ≤ a i j (x i² +
  x j²)/2` (AM–GM at `(x i − x j)² ≥ 0`, multiplied through by the
  nonnegative weight — the step where `hnn` is load-bearing), then
  the symmetric double sum's two halves each `d ‖x‖²` (the row-sum
  identity and the symmetry-reindexed column-sum identity). This is
  the Step-5 engine's domination half in its final form.
- `evals_last_eq_of_isDRegular` — **the top adjacency eigenvalue of a
  d-regular graph is `d`** (`evals hA ⟨card − 1⟩ = d`), from both
  sides, as this step's own text priced: `d` is an eigenvalue
  (`exists_eigvalOf_eq_of_mulVec_eq_smul` at `onesVec`, then
  `eigvalOf_le_evals_last`) and every eigenvalue is dominated
  (`evals_mem_eigvalOf` + `quadForm_eigvecOf_self` + the AM–GM
  domination at the unit eigenvector). The identification is
  load-bearing on the sorted-spectrum API at its extremes — a wrong
  `evals`/`eigvalOf`/`deg` shape breaks one of the two halves.

**QA** (`Scaffold/QA/SpectralGraph/AlonBoppana_QA.lean`, per this
proposal's QA plan's guard-witness clause): the C₄ (2-regular) and K₂
(1-regular) theorem instances joined to **raw entrywise
eigen-equation pins** computed with no theorem input; the
**non-regularity fence** (on P₃ the constant vector is provably not
an adjacency eigenvector for any `c` — `IsDRegular` load-bearing at
the interface's own witness); and the **nonnegativity fence** (the
signed `!![1,-1;-1,1]]` is symmetric and *0-regular* — every
hypothesis but `hnn` — with AM–GM domination refuted at `![1,0]`,
`1 > 0`: `hnn` isolated exactly where it enters). The
positive/tightness and small-diameter witnesses of the QA plan are
Steps 3–5 work (they pin `λ₂`-vs-`2√(d−1)` itself, which needs the
theorem).

**Verification:** spike first (`wip/ab_spike.lean` — module side, QA
side, and the Step-0 tree-ball pricing all green before any shelf
Lean touched); `lake env lean` zero errors/zero warnings on the
module and the QA file; explicit `lake build` targets ✔ (2009/2009,
2010/2010); `#print axioms` — the standard three only, all 22; **full
`lake build` ✔ (2387/2388, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 113/113
fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass after the record
sweep; scoreboard regenerated idempotent (**2520/10/0**, md5-stable).
Technique findings for downstream steps (all recorded from spike
failures): this Mathlib's `Finset.mul_sum`/`sum_mul` naming is
swapped relative to the common convention (`mul_sum` is the
constant-times-sum direction); `pow_two` here reads `a ^ 2 = a * a`
(no `.symm`); the double-sum AM–GM assembly closes by
`← Finset.sum_div` twice (inner then outer) after `←
Finset.sum_add_distrib`; `onesVec ≠ 0` at `1 ≤ card V` by
`Fintype.card_pos_iff` + `congrFun` at a witness.
