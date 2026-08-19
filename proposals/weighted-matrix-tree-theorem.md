# Proposal: The Weighted Matrix-Tree (Kirchhoff) Theorem

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-19 — a candidate for genuinely new machinery, not a routine
build-order step. Authorizes no Lean changes, axiom admissions, document
rewrites, or external publication.

Companion to [Grow the Crust Through Electrical
Structure](electrical-structure-crust.md) (axis 6's foundational program),
[Spielman–Srivastava Sparsification](spectral-graph-sparsification.md)
(Foster's theorem, Phase A — a *different*, already-in-flight route to a
statement this proposal's classical namesake is sometimes used to derive;
see "Relationship to Foster's theorem" below, which this document does not
overstate), `docs/1_STRATEGY.md`'s center-out policy, and
`docs/6_SGT_BACKLOG.md` item 7, which already names this exact candidate
and gates it explicitly — see "Why this axis."

## Clean-room boundary

This planning document is internal prioritization and analysis. If counsel
approves a public repository export, restate the technical specifications
independently from standard textbook sources on algebraic graph theory
(Kirchhoff's original 1847 paper via the modern spectral restatement). Do
not copy this proposal verbatim or consult quarantined materials.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean` (`laplacian`,
`supportGraph`, `laplacian_kernel_eq_span_onesVec`,
`Matrix.IsHermitian.det_eq_prod_eigenvalues`'s existing citation),
`docs/6_SGT_BACKLOG.md` item 7, `docs/7_SGT_RADAR.md` axis 6, and a fresh
survey of `.lake/packages/mathlib/Mathlib/{LinearAlgebra/Matrix/Adjugate,
Combinatorics/SimpleGraph/{Acyclic,Subgraph,IncMatrix}}.lean` plus a
repository-wide search for `matrix.*tree`, `kirchhoff`, `spanningtree`,
and `cauchy.*binet` (results below).

## The claim this document is answering

Not "should we do this now" — the gate below already answers that. The
question is narrower: **if this project builds one more piece of
genuinely new machinery (in the sense of `icebox/`'s three entries — a
missing subfield or a substantial new proof technique, not a routine
build-order step), is there a better candidate than continuous-time
trajectory calculus?** This document is that candidate, written up to the
same standard as an icebox entry plus a concrete build order, so the
comparison and the eventual decision are both on the record.

## Why this axis

`docs/6_SGT_BACKLOG.md` item 7 (Combinatorial and electrical structure)
already names this precisely:

> *"Candidate first slice: the transfer-impedance/Multiplicity-Tree
> statement shape, which consumes the already-proved Laplacian
> adjugate-adjacent infrastructure. **Gated:** admit or define nothing
> here until a named consumer states which identity it needs (per the
> center-out policy, adjacency alone does not justify admission)."*

That gate is not satisfied by this document. No proposal or backlog item
currently states a dependency on the spanning-tree count. This section
exists to give the honest case for the axis anyway, so an operator has
real material to decide against, not just a name in a backlog line.

The case: axis 6 is this project's most active and highest-consumer
neighborhood (effective resistance, Kirchhoff conservation, electrical
flows, Thomson's principle all live here, all delivered without axioms).
The classical Matrix-Tree theorem is the one major result of this
neighborhood's textbook canon not yet even attempted, and it is provable
by the same style of argument as everything already delivered here:
finite determinants, cofactors, and induction over graph structure — not
a foreign kind of math, unlike the trajectory-calculus alternative.

## Relationship to Foster's theorem — do not overstate this

Foster's theorem (`∑` over edges, `conductance · resistance = n − 1`) is
sometimes proved via a Matrix-Tree-derived pseudoinverse-trace identity
in textbooks. **That is not the route this project is taking.**
`spectral-graph-sparsification.md`'s Phase A (currently the active High
item alongside the electrical-flow program) proves Foster directly via
eigenbasis expansion and the one-dimensional kernel characterization —
*no* spanning-tree count, no pseudoinverse. This proposal does not name
Foster's theorem as a consumer and would not change or accelerate that
program if built. The genuine mathematical connection between effective
resistance and spanning-tree ratios (`R u v` relates to a ratio of
weighted 2-forest and spanning-tree counts) is real but is its own,
larger extension — see "Deferred and removed."

## What the pinned Mathlib already provides

| Mathlib declaration | File | Covers |
| --- | --- | --- |
| `SimpleGraph.IsTree` (`Connected` + `IsAcyclic`) | `Acyclic.lean:54` | The combinatorial tree predicate — exists, no need to invent one |
| `SimpleGraph.IsAcyclic` | `Acyclic.lean:50` | No-cycle predicate, used by `IsTree` |
| `Subgraph.IsSpanning` | `Subgraph.lean:140` | Spanning-subgraph predicate |
| `Matrix.adjugate`, `adjugate_apply`, `cramer_apply` | `Adjugate.lean` | Cofactor machinery — the entry-level object the theorem's statement is phrased in terms of |
| `Matrix.IsHermitian.det_eq_prod_eigenvalues` | `Spectrum.lean:125` | The bridge from a cofactor determinant to the eigenvalue product, once the cofactor identity itself is proved |
| `SimpleGraph.incMatrix` (unweighted, `0`/`1`) | `IncMatrix.lean` | Not the oriented (signed) incidence matrix the algebraic proof route needs; would need its own weighted/oriented redefinition |

**Verified absent, not merely uncited** (repository-wide and Mathlib-wide
search, 2026-08-19): no `matrix.*tree`, `kirchhoff`, or `spanningtree`
declaration under any naming anywhere in the pinned Mathlib or in
Scaffold; no Cauchy–Binet formula under any naming
(`cauchy.*binet`/`CauchyBinet`, zero hits); no oriented/signed incidence
matrix. The theorem itself — the identity connecting a spanning-tree
count to a Laplacian cofactor — does not exist at any layer.

## Calibration: two proof routes, honestly costed

**Route A — algebraic, via Cauchy–Binet on the oriented incidence
matrix.** The standard modern proof: with `B` the signed
vertex-edge incidence matrix (weighted, oriented arbitrarily per edge)
so that `L = B · diag(weights) · Bᵀ`, Cauchy–Binet expands the cofactor
determinant as a sum over `(n-1)`-edge subsets of squared sub-determinants,
each of which is `±(product of weights)` if the subset is a spanning
tree and `0` otherwise (a square incidence submatrix is singular iff its
edge set contains a cycle). This is the cleaner proof on paper, but
**Cauchy–Binet itself does not exist in the pinned Mathlib** — this route
pays for two absent pieces, not one, and the oriented incidence matrix
would be new Scaffold infrastructure with no other named use.

**Route B — combinatorial, via deletion–contraction induction.** The
classical elementary proof: `τ(G) = τ(G − e) + w(e) · τ(G / e)` for any
edge `e` (delete-or-contract recursion on the weighted spanning-tree
count), with the same recursion holding for the relevant Laplacian
cofactor under the matching graph operations, so the two satisfy the same
recursion and agree at the base case (no edges: cofactor and tree count
both `0` unless `n = 1`, where both are `1`). This needs no new linear
algebra beyond what is already on the shelf (`adjugate`, `det`), but it
does need a `WAdj`-level notion of edge deletion and edge contraction —
neither currently defined in Scaffold — and an induction whose measure
(edge count) and base cases need care, particularly around what "delete"
does to the vertex set (nothing) versus what "contract" does (merges two
vertices, changing `V` itself, which is awkward in Scaffold's fixed-`V`
`Matrix V V ℝ` representation).

**Recommendation if pursued: Route B, but expect the vertex-merging
awkwardness in contraction to be the real cost driver**, not the
induction structure itself. This mirrors this project's own recorded
experience on `electrical-structure-crust.md`'s step 2 correction:
"judge transport [or in this case, proof route] on cost, not reflex."
Route A trades one hard absent piece (Matrix-Tree) for two (Matrix-Tree
*and* Cauchy–Binet); Route B stays inside Scaffold's fixed-vertex-set
idiom for delete but genuinely breaks it for contract, and that break
should be spiked on a small concrete case before committing to the route.

## Build order

### Step 0: Survey and route decision (do not skip)

Before any definition lands: spike edge contraction on a `Fin 3` or
`Fin 4` fixture by hand (on paper or in a scratch file, not committed) to
get a real cost estimate for Route B's vertex-merging step, since that is
the one piece neither this survey nor the pinned Mathlib resolves in
advance. Record the finding and the chosen route in this document before
Step 1 begins. **This step does not authorize Step 1 to begin on its
own** — see "Gate," below.

### Step 1: Define the weighted spanning-tree count

```
def treeCount (A : WAdj (V := V)) (hA : A.IsSymm) : ℝ :=
  ∑ H ∈ {H : SimpleGraph V | H.IsTree ∧ H ≤ supportGraph A hA}.toFinset,
    ∏ e ∈ H.edgeFinset, A e.out.1 e.out.2  -- exact edge-weight extraction TBD at implementation time
```

Needs a `Fintype`/`Decidable` instance for the tree-subgraph predicate
over `SimpleGraph V` (available since `V` is a `Fintype` and `Adj` is
decidable — reuse the `supportGraphAdjDecidable` pattern
`electrical-structure-crust.md` step 3 already had to add once for the
same underlying reason). QA a hand-computed small case immediately
(`K₃`: three spanning trees, each a single deleted edge; `C₄`: four
spanning trees) as a sanity check on the definition itself before any
theorem is stated about it.

### Step 2: The base identity — any two cofactors of `L` agree

Before the Matrix-Tree identity proper, a smaller, genuinely
Scaffold-idiom lemma is worth having on its own: for connected `A`, every
principal `(n-1)×(n-1)` cofactor of `laplacian A` equals every other one.
Route: `laplacian A * adjugate (laplacian A) = det (laplacian A) • 1 = 0`
(the Laplacian is singular), so every column of `adjugate (laplacian A)`
lies in `ker (laplacian A)ᵀ = ker (laplacian A)` (symmetric) `= span
{onesVec}` (the already-proved `laplacian_kernel_eq_span_onesVec` — this
step's whole reason for being cheap is reusing that theorem directly),
forcing `adjugate (laplacian A)` to be a constant matrix. Zero new
axioms; this is a direct algebraic corollary of center facts already on
the shelf.

### Step 3: The Matrix-Tree identity itself

Prove, for connected `A`: `treeCount A hA = (adjugate (laplacian A)) i i`
for any `i` (well-defined by Step 2). This is the hard step — the
deletion-contraction induction from Route B (or Cauchy-Binet from Route
A, if Step 0's spike favors it instead). Likely needs its own
sub-decomposition across multiple runs, comparable to the electrical
program's step 4 or the mixing-time program's step 3.

### Step 4: The eigenvalue-product corollary

`treeCount A hA = (1/n) * ∏_{i : λᵢ ≠ 0} λᵢ`, via Step 3 plus
`Matrix.IsHermitian.det_eq_prod_eigenvalues` applied to a bordered or
reduced form of the Laplacian (exact bridging lemma TBD; this is the
"free" step once Step 3 lands, per the original motivating observation
that made this axis look cheap before Route A/B's real costs were
surveyed).

### Deferred and removed

- **Foster's theorem via this route** — explicitly not a goal; see
  "Relationship to Foster's theorem." Do not fold this proposal's
  delivery into that proposal's build order.
- **Resistance-as-spanning-tree-ratio** (`R u v` via weighted 2-forest
  counts) — a real, larger extension consuming this proposal's
  machinery plus a new 2-forest-counting layer. Its own proposal if ever
  pursued, not a default continuation.
- **Random spanning-tree sampling algorithms** (Aldous–Broder,
  Wilson's algorithm) — application-layer consumer, out of scope here.
- **The disconnected case** — `treeCount` should be `0` and every
  cofactor should independently be provably `0` (rank deficiency `> 1`);
  worth a QA witness, not a build-order step, since Step 2's argument
  already implies it once specialized.

## QA plan

- Positive witnesses: `K₃` (3), `C₄` (4), the 3-vertex path (1 — a tree
  is its own only spanning tree), each computed by hand against
  `treeCount`'s definition directly, independent of Step 3's theorem.
- Cross-check: the same three fixtures' cofactor values, computed
  directly from `adjugate`, agreeing with `treeCount` per Step 3.
- Negative/structural witness: a disconnected fixture, `treeCount = 0`
  and the relevant cofactor `= 0`, both independently confirming Step 2's
  disconnected corollary.
- Weighted witness (not just `0`/`1` weights): a small graph with
  distinct edge weights, to confirm the product-of-weights definition
  (not merely a count) is what Step 3 actually proves — this is the one
  place a purely combinatorial (unweighted) sanity check would miss a
  real bug.

## Gate — this needs an operator decision, not routine backlog treatment

Per `docs/6_SGT_BACKLOG.md` item 7's own explicit text, reproduced above:
admit or define nothing here until a named consumer states which
identity it needs. This document does not supply that consumer — it is
the honest "if we're going to build new machinery, here is the strongest
candidate" case, not a claim that anything downstream is blocked without
it. Building it now would need the same justification
`admit-perron-frobenius.md` and `prove-courant-fischer.md`'s original
scoping needed: general-purpose machinery built ahead of a named
consumer, on the strength of fitting the project's demonstrated idiom
and its most active axis — a real but different kind of case than "X is
blocked." An autonomous run should not begin Step 1 without this
decision recorded here as adopted.

## Operating instructions for an autonomous run

*(Apply only after the Gate above is resolved.)*

- One step per run; Step 3 will likely need more than one, per the
  electrical and mixing-time programs' own precedent for their hardest
  steps.
- **No new axioms.** If Step 3's chosen route turns out to need
  machinery genuinely absent from both Scaffold and Mathlib (e.g., if
  Route A is chosen and Cauchy–Binet turns out load-bearing rather than
  avoidable), stop and record the precise obstruction in
  `docs/6_SGT_BACKLOG.md` rather than admitting anything — this
  proposal's cost case rests on staying inside existing determinant and
  induction machinery.
- Survey Mathlib before each step per this repository's standing rule;
  update `docs/8_MATHLIB_COVERAGE_MAP.md` if the survey finds something
  this document missed.
- Do not fold this proposal's delivery into `spectral-graph-sparsification.md`'s
  Foster program; they are independent per "Relationship to Foster's
  theorem" above.

## Open next step

Blocked on the Gate above, not on any technical prerequisite — Step 0's
survey/spike may be done at any time (it costs nothing to record), but
Step 1 should not begin until an operator adopts this proposal against
the backlog's explicit "named consumer" requirement, or names one.
