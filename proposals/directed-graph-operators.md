# Proposal: Directed and Asymmetric Graph Operators (Foundational Objects)

**Status:** In progress (Steps 0–1 delivered 2026-08-22, run
`20260822T181701Z-run-1`, zero new axioms — see the delivery record and
the Step 0 record below). Priority **Medium**. Assistant's assessment of
project direction, requested 2026-08-19, promoted from `sgt-gaps.md` item
6. Authorizes no Lean changes, axiom admissions, or external publication
beyond its own steps.

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

## Step 0 record (2026-08-22, run `20260822T181701Z-run-1`)

All three mandated decisions, made and recorded before any Step 1
statement was written.

**(c) Mathlib re-survey — no directed Laplacian was missed.** Searched
exactly as mandated: `Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean`
is the *undirected* `SimpleGraph` Laplacian (combinatorial only, no
normalization, no directed content); `Mathlib/Combinatorics/Digraph/`
contains only `Basic.lean` (the `Digraph` relation structure,
`completeDigraph`/`emptyDigraph`, `IsSubgraph` — no matrices at all) and
`Orientation.lean`. The only other "Laplacian" mentions in the pin are
`IncMatrix.lean` (incidence) and a determinant-file comment. Perron–
Frobenius re-confirmed absent (the only "Perron" hits are the unrelated
`BoxIntegral` files). The coverage map's rows hold; no correction
needed.

**(a) Carrier decision — reuse; no new type.** `WAdj` is an `abbrev` of
`Matrix V V ℝ` (`Spectral.lean:70`) with *no symmetry at the type
level* — every undirected theorem carries `hA : A.IsSymm` as an explicit
call-site hypothesis, so the reuse risk this proposal named ("silently
admitting asymmetric inputs where a theorem assumed symmetry") is
structurally absent from the shelf: there is no type-level symmetry to
silently drop, and a new `WDigraph` type would be another abbrev of the
same carrier adding API surface with zero safety. **Decision: the
directed axis is stated on `Matrix V V ℝ` directly**, with nonnegativity
and degree-positivity hypotheses attached at call sites exactly where
consumed, mirroring the shelf's convention.

**Discovery (changes Step 1's shape): recommendation items 1 and 3
already exist on the shelf, hypothesis-free.** `deg A i = ∑ j, A i j`
(`Spectral.lean:73`) is the row sum — the *out*-degree — and the general
walk operators `walkTransitionMatrix A = D⁻¹ A` (`Normalized.lean:248`)
and `walkLaplacian A = I − D⁻¹ A` (`Normalized.lean:288`) are defined
with **no symmetry hypothesis**; `walkTransitionMatrix_row_sum`
(row-stochasticity) and `walkLaplacian_mulVec_one_eq_zero`
(conservation) hold for any matrix with positive row sums. The
undirected shelf was already carrying the out-degree walk operators.
Step 1's genuine content is therefore: `inDeg` (the column sum —
genuinely new), the degree-agreement theorems (`outDeg = deg` by `rfl`;
`inDeg = outDeg` under `IsSymm`), the directed handshaking identity
`∑ outDeg = ∑ inDeg`, and QA that certifies the pre-existing walk
operators genuinely apply to asymmetric input — load-bearing in the
falsifiability sense: had `walkTransitionMatrix` secretly been defined
through the symmetrized adjacency (or `deg` through a symmetric sum),
the asymmetric-fixture QA instantiation of
`walkTransitionMatrix_row_sum` would fail.

**(b) Convention decision — the out-degree-symmetrized normalized
Laplacian; no Perron–Frobenius prerequisite.** For Step 2's object the
chosen convention is
`L_dir := I − ½(D_out^{-1/2} A D_out^{-1/2} + D_out^{-1/2} Aᵀ D_out^{-1/2})`:
symmetric by construction, total for any nonnegative matrix with
positive out-degrees, and reducing to `normalizedLaplacian` on the
symmetric cone (both halves coincide there), which keeps Step 3's
agreement bar a one-liner and the whole proposal axiom-free end-to-end
per its own operating instruction. **This is deliberately not Chung's
2005 convention**: Chung's directed Laplacian is built from the Perron
vector (the walk's stationary distribution) and carries the directed
Cheeger inequality; adopting it would make an admitted axiom a
*prerequisite of a definition* — inverting the repo's axiom-minimization
ethos — and would gate Step 2 on `admit-perron-frobenius.md` landing
first. Build-order consequence recorded explicitly (not silently
reordered, per the operating instructions): **the two proposals are now
decoupled.** Perron–Frobenius proceeds on its own named leverage case
(irreducible stationary distributions, PageRank), which never mentioned
the Laplacian; Chung's Perron-vector Laplacian remains available as a
separate, later definition once that axiom exists, alongside this one.
Residual named honestly: the symmetrized operator forfeits Chung's
directed-Cheeger content — any future directed-isoperimetric work must
either adopt Chung's convention there or prove its own bounds.

**Step 3 note (acceptance bar scope):** for the walk operators the
agreement is already materially delivered by Step 1's degree identities
(`outDeg = deg` is `rfl` and `walkTransitionMatrix`/`walkLaplacian` are
the *same* definitions the directed axis uses — there is nothing to
agree); Step 3's remaining content is the normalized-Laplacian
agreement, one line from decision (b).

## Open next step

Step 0 — **delivered 2026-08-22** (record above). Step 1 delivered in
the same run per the record-before-Step-1 requirement (Step 0 produces
no Lean, so the run's one Lean step is Step 1); see the delivery record
below. Next: Step 2 (the directed normalized Laplacian at decision (b)'s
convention).

## Step 1 delivery record (2026-08-22)

**Delivered (zero new axioms; `#print axioms` on all seven public
declarations reads only `propext, Classical.choice, Quot.sound`):**
the new public module `Scaffold/Mathlib/GraphTheory/Directed.lean`
(namespace `SpectralGraphTheory`) — `outDeg` (the row sum, named for
the directed reading), `inDeg` (the column sum — the genuinely new
directed quantity), the definitional identifications `outDeg_eq_deg`
and `inDeg_eq_deg_transpose` (both `rfl`), the symmetric-cone
agreements `inDeg_eq_outDeg_of_isSymm` / `inDeg_eq_deg_of_isSymm`
(the degree brick of the Step-3 acceptance bar — the walk-operator
part of that bar needs no separate theorem, per the Step-0 record:
the directed axis uses the *same* definitions), and directed
handshaking `sum_outDeg_eq_sum_inDeg` (no nonnegativity or symmetry
hypothesis, by `Finset.sum_comm`). The module docstring records the
Step-0 discovery and the carrier decision; the four
`DecidableEq`-free theorems carry `omit` clauses (the linter's own
suggestion) so the module elaborates with zero warnings.

**QA (`Scaffold/QA/SpectralGraph/Directed_QA.lean`, 41 declarations;
`#print axioms` on twelve headline theorems clean):** the
genuinely-directed fixture `dirA = !![0,3,1;1,0,0;1,0,0]` (arcs
0→1 weight 3, 0→2 weight 1, 1→0 and 2→0 weight 1) with a nine-entry
`rfl` table doubling as the nonnegativity exhibit; `outDeg = (4,1,1)`
and `inDeg = (2,3,1)` pinned raw; the transpose identity instantiated
with content (`inDeg dirA 1 = deg dirAᵀ 1 = 3`, both sides computed);
handshaking `6 = 6` by theorem and by both raw routes; the
symmetric-edge agreement witness through the theorems with all three
degree readings pinned raw; **the load-bearing certification** —
`walkTransitionMatrix_row_sum` and `walkLaplacian_mulVec_one_eq_zero`
(pre-existing undirected-shelf theorems) instantiated on the
asymmetric fixture, with row 0's stochasticity recomputed raw
(`(1/4)(0+3+1) = 1`) and an `L_walk` entry computed from `I − P`; and
the two negative witnesses — `outDeg dirA 0 ≠ inDeg dirA 0` (`4 ≠ 2`,
the directed case is genuinely not free) and
`¬ (walkTransitionMatrix dirA).IsSymm` (`P 0 1 = 3/4 ≠ 1 = P 1 0`,
the calibration fact: no symmetric operator to restrict to).

**Pin-specific QA technique (recorded for Step 2's QA):** on this
snapshot, `simp only [outDeg, dirA, Matrix.of_apply,
Fin.sum_univ_three]` (unfolding the *new* degree defs together with
the matrix literal) leaves `Matrix.vecHead (Matrix.vecTail …)` entry
residue on rows/columns beyond index 0, while the same list through
the shelf's `deg` behaves; `show` cannot kernel-reduce `Finset.sum`
(that is why `Fin.sum_univ_three` exists). The deterministic route:
a `rfl`-proved entry table for the fixture, then
`simp only [def, Fin.sum_univ_three]` (sum-split only, no matrix
unfolding) followed by table rewrites and `norm_num`.

**Verification:** `lake env lean` on the module and on the QA file —
zero errors, zero warnings each; explicit target builds of both ✔;
`#print axioms` on the seven public and twelve headline QA theorems ✔
(three standard axioms only); umbrella import added and **full
`lake build` ✔ (2230 targets, "Build completed successfully", zero
errors, detached log + poll)**; `lint_axioms` (9, unchanged),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1295/9/0**; `Directed_QA` a new file row at 41; the
Direct and QA-direct rows and the `lake build` row extended). Records
updated: this record, backlog item 8, the SGT index map (Directed
section), README (counts, proved list, module table), radar (QA axis
count synced 1254/37 → **1295/38**, held at 4.0 with the hold
logged), `proposals/README.md`, the execution plan, and the activity
log.
