# Proposal: Directed and Asymmetric Graph Operators (Foundational Objects)

**Status:** Proposed; priority **Medium**. Assistant's assessment of
project direction, requested 2026-08-19, promoted from `sgt-gaps.md` item
6. Authorizes no Lean changes, axiom admissions, or external publication.

**The scope decision this needed is resolved.** `docs/1_STRATEGY.md`'s
center-out prioritization now covers directed graphs (2026-08-19, operator
decision on record); `docs/6_SGT_BACKLOG.md` item 8 opened the same day.
This proposal is the first slice under that item — the foundational
directed objects, not the algebraic tool (`admit-perron-frobenius.md`,
already proposed separately) or the magnetic-Laplacian extension (out of
scope here, see Deferred).

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard directed-spectral-graph-theory
sources (Chung 2005). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/GraphTheory/{RandomWalk,Normalized,
Stationary}.lean` (every existing walk/Laplacian construction scoped to
undirected, weighted graphs via the diagonal-similar-to-symmetric trick),
`admit-perron-frobenius.md` (the algebraic tool this proposal's objects
would feed), and `docs/8_MATHLIB_COVERAGE_MAP.md` (no directed-Laplacian
declaration found anywhere in the pinned Mathlib).

## External consumer

PageRank-style directed Markov chains, citation and web-graph analysis,
directed community detection — the widest gap by subject area in this
repository before the 2026-08-19 scope decision (Chung, "Laplacians and
the Cheeger inequality for directed graphs," Annals of Combinatorics 9,
2005 — **citation unverified**, confirm before committed use).

## Recommendation

Define the foundational directed objects and prove their relation back to
the symmetric case, deliberately **not** the full magnetic-Laplacian or
Hermitian-embedding machinery (see Deferred):

1. `WDigraph := Matrix V V ℝ` (nonnegative, no symmetry hypothesis) — the
   directed analogue of `WAdj`. Decide whether this is a genuinely new
   type or `WAdj` reused without the symmetry hypothesis attached at the
   call site; survey which is cheaper before committing (a new type adds
   clarity but duplicates API surface; reusing `WAdj` risks silently
   admitting asymmetric inputs where a theorem assumed symmetry).
2. `outDeg`/`inDeg` (row-sum and column-sum degree, distinct in the
   directed case — the first genuinely new fact this axis needs, since
   `deg` in `WAdj` is defined once because `WAdj` is always symmetric).
3. The **random-walk Laplacian** for a directed graph:
   `L_walk := I - D_out⁻¹ A` (row-normalized), mirroring
   `RandomWalk.transitionMatrix` but without the symmetry that currently
   makes it diagonally similar to a symmetric operator.
4. The **directed normalized Laplacian**, per the cited convention (state
   the exact convention chosen — several inequivalent ones exist in the
   literature, this is the calibration risk below).
5. The relation of each back to the symmetric/undirected case: on a
   symmetric `A`, `outDeg = inDeg = deg`, and the directed constructions
   above should agree definitionally or by a one-line lemma with
   `RandomWalk`'s and `Normalized`'s existing undirected constructions —
   this agreement theorem is the proposal's actual acceptance bar, not
   just "the definitions exist."

## Calibration — the sharp edge this axis has that the undirected one does not

**No symmetric operator exists to restrict to.** Every reason Scaffold's
`evals`/`eigvecOf` toolkit works — real eigenvalues, orthonormal
eigenbasis, Courant–Fischer, Cauchy interlacing — depends on symmetry.
None of it applies to `L_walk` or the directed normalized Laplacian as
defined here; their eigenvalues are generally complex, and there is no
`evals`-style sorted real spectrum. **This proposal does not attempt a
spectral theory for these objects** — it defines them and proves the
algebraic relations above, stopping before any eigenvalue statement. A
directed spectral theory (magnitude bounds on eigenvalues via
Perron–Frobenius, convergence via the second-largest eigenvalue modulus)
is real follow-on work, consuming `admit-perron-frobenius.md`'s algebraic
tool once both exist, but is not scoped here — naming it as a future
consumer is not the same as delivering it, per this table's own
convention elsewhere.

**Normalization convention is a real, underspecified choice.** The
directed normalized Laplacian has multiple inequivalent standard forms in
the literature (Chung's own construction uses the stationary distribution
of the random walk, which requires `admit-perron-frobenius.md`'s
existence/uniqueness result as a *prerequisite*, not a consumer — this
creates a real ordering dependency the backlog note did not originally
flag). **Decide and record** whether this proposal's directed normalized
Laplacian needs Perron–Frobenius as a prerequisite (Chung's convention) or
can use a cheaper convention that avoids the dependency, before writing
the statement — this decision materially changes the build order.

## Build order

### Step 0: Survey and convention decisions (mandatory)

Resolve, in order: (a) new type vs. reused `WAdj` for `WDigraph`; (b)
which directed-normalized-Laplacian convention, and whether it creates a
prerequisite dependency on `admit-perron-frobenius.md`; (c) confirm no
existing Mathlib directed-Laplacian declaration was missed (re-search
`Mathlib.Combinatorics.SimpleGraph.{LapMatrix,Digraph}` specifically,
since `Digraph.Basic` exists in the pin and was not fully surveyed for
this proposal).

### Step 1: `WDigraph`, degrees, and the random-walk Laplacian

Items 1–3 above.

### Step 2: The directed normalized Laplacian

Item 4, per Step 0's convention decision — may be gated on
`admit-perron-frobenius.md` landing first, depending on that decision.

### Step 3: Agreement with the symmetric case

Item 5 — the acceptance bar. Prove each directed construction reduces to
its existing undirected counterpart when `A.IsSymm`.

## QA plan

- Positive witness: a small genuinely directed fixture (e.g., a 3-cycle
  with distinct in/out weights), `outDeg`/`inDeg` computed and shown to
  differ, `L_walk` computed from the definition.
- Agreement witness: the same construction on a symmetric fixture already
  used elsewhere (e.g., the edge or 3-path), checked to agree numerically
  with `RandomWalk`'s or `Normalized`'s existing output.
- Negative witness: a directed fixture where naively reusing an
  undirected lemma (e.g., assuming `outDeg = inDeg`) produces a wrong
  answer, confirming the directed case is genuinely not free.

## Deferred and removed

- **Magnetic Laplacians and Hermitian embeddings** — a real, separate
  slice per `docs/6_SGT_BACKLOG.md` item 8's own note; not folded into
  this proposal.
- **Any directed spectral theory** (eigenvalue bounds, mixing rates for
  directed walks) — explicitly out of scope per Calibration; a follow-on
  proposal once both this and `admit-perron-frobenius.md` exist.
- **PageRank / centrality algorithms** — the named application-ring
  consumer, not delivered here.

## Operating instructions for an autonomous run

- One step per run; Step 0's decisions must be recorded before Step 1.
- **No new axioms.** This proposal is pure definition and algebraic
  relation — if Step 3's agreement proofs need something genuinely
  absent, stop and record the obstruction.
- Coordinate with `admit-perron-frobenius.md` if Step 0 finds Chung's
  convention creates a real prerequisite dependency — do not silently
  reorder without recording why.

## Open next step

Step 0 — unblocked now, no further operator decision required beyond the
one already resolved.
