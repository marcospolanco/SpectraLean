# Proposal: The Rank-One Edge Perturbation Norm Bound

**Status:** COMPLETE (delivered 2026-09-07, run `20260907T130116Z-run-1`,
session `ses_f840b32f9ffeQquR0Tn6QqpJwb`; Steps 1 and 2 landed together
as the operating instructions priced; the `i = j` fence shipped in the
same delivery as required — see the delivery record below). **Amended
2026-09-07 by the corner audit (run `20260907T200815Z-run-1`): the
`v ≠ 0` clause on the weighted rank-one pair found truth-removable and
removed — both public theorems strengthened to unconditional
statements, the residue sentence corrected (see the corner-audit
record below).** Restated in
pure-mathematics form 2026-09-07 from
an external request relayed by the operator (not tracked in this
repository — see `.gitignore`); no operational, product, or patent
framing survives into this document, only the underlying mathematical
asks.

Companion to `Scaffold/Mathlib/GraphTheory/EdgePerturbation.lean`
(Section 1, "the single-edge algebra" — `edgeAdj`/`laplacian_edgeAdj`,
this proposal's own base layer) and
[`matrix-hoeffding-spectral-gap-estimation.md`](matrix-hoeffding-spectral-gap-estimation.md)
(the probabilistic program that layer was originally built to serve;
this proposal is a purely deterministic sibling, not an extension of
that program — see "Scope decision" below).

## The claim this document is answering

The relayed request's framing was: graph operators are treated as
static in this project, with no interface for a single edge-weight
mutation's effect on operator norm. **That framing does not match this
project's current state.** `EdgePerturbation.lean` already has exactly
the algebraic object the request wants — `edgeAdj i j w` (the graph
that is `w` on edge `{i, j}` and zero elsewhere) and the identity
`laplacian_edgeAdj : laplacian (edgeAdj i j w) = w • rankOne (Pi.single
i 1 - Pi.single j 1)` — under different names, built for a different
purpose (the deterministic hinge of a probabilistic concentration
design, not a standalone perturbation-norm fact). What genuinely is
missing is the **norm computation** on top of that identity: no
declaration in this project states `‖laplacian (edgeAdj i j w)‖ = 2 *
|w|`, and the only existing rank-one norm fact
(`l2OpNorm_rankOne_le`, `Sparsification.lean:189`) is a one-sided
inequality, not the equality the request needs. This document verifies
the missing equality is cheap — a direct generalization of an
already-proved technique to include the scalar weight, plus a witness-
vector argument using an already-proved existence lemma this project
built for an unrelated purpose (`Spectral.lean`'s bottom-eigenvalue
identification).

## What's already on the shelf

- **The single-edge-to-rank-one identity** — `laplacian_edgeAdj`
  (`EdgePerturbation.lean:138`): `laplacian (edgeAdj i j w) = w •
  rankOne (Pi.single i 1 - Pi.single j 1)`, valid at every `i, j, w`
  (including `i = j`, where both sides are the zero matrix). This is
  the entire algebraic content the request's `laplacian_edge_update`
  needs; nothing new to build here.
- **The rank-one operator-norm upper bound** — `l2OpNorm_rankOne_le`
  (`Sparsification.lean:189`): `‖rankOne v‖ ≤ v ⬝ᵥ v`, proved via
  Cauchy–Schwarz on the quadratic form at an arbitrary unit
  eigenvector (`quadForm_eigvecOf_self`, `rankOne_quadForm`,
  `dotProduct_sq_le`, `eigvecOf_inner`) — one-sided only, and without
  the scalar weight `w`.
- **The scalar-scaling identity for the quadratic form** —
  `quadForm_smul_var` (`Spectral.lean`, private): `quadForm (c • M) x
  = c * quadForm M x`, already proved and already the exact fact
  needed to carry `l2OpNorm_rankOne_le`'s Cauchy–Schwarz argument
  through the extra scalar `w`.
- **The witness-eigenvalue existence lemma** — `exists_eigvalOf_eq_of_
  mulVec_eq_smul` (`Spectral.lean:3536`): given `x ≠ 0` and `M *ᵥ x = μ
  • x`, `μ` *is* one of the listed `eigvalOf M hM i` values. Built for
  an unrelated purpose (identifying the Laplacian's bottom eigenvalue
  as exactly `0` via the all-ones eigenvector, `laplacian_evals_zero`)
  but exactly the missing lower-bound ingredient here: it turns "`v` is
  an eigenvector of `rankOne v` at eigenvalue `v ⬝ᵥ v`" (an immediate
  corollary of `rankOne_mulVec`) into "`v ⬝ᵥ v` is a listed
  `eigvalOf`," which the already-proved `abs_eigvalOf_le_l2OpNorm`
  (`Resolvent.lean:135`) then bounds below `‖rankOne v‖` directly.
- **The genuine eigenvalue-scaling machinery gap, already documented
  in this project** — `secondEval_smul_of_pos`'s own docstring
  (`Spectral.lean:2470`) records that a hypothesis-free "`eigvalOf (c
  • M) i = c * eigvalOf M i`" fact for arbitrary symmetric `M` would
  need eigenvalue-multiset scaling machinery absent from the pinned
  Mathlib (`eigenvalues_smul`/`charpoly_smul`), and is deferred as
  future work needing a named consumer. **This proposal does not need
  that machinery and does not trigger that gap** — see "The route"
  below, which stays entirely inside the rank-one case's own explicit
  eigenstructure rather than reaching for a general smul-eigenvalue
  theorem.

## The route: extending `l2OpNorm_rankOne_le`'s own technique, both directions

**Claim.** For `i ≠ j` and any `w : ℝ`,
```
‖laplacian (edgeAdj i j w)‖ = 2 * |w|
```
Route, via `laplacian_edgeAdj` reducing this to `‖w • rankOne v‖ = |w|
* (v ⬝ᵥ v)` at `v := Pi.single i 1 - Pi.single j 1`, then `v ⬝ᵥ v = 2`
(a direct computation: `v` is `1` at `i`, `-1` at `j`, `0` elsewhere,
since `i ≠ j`):

- **Upper bound** (`‖w • rankOne v‖ ≤ |w| * (v ⬝ᵥ v)`): clone
  `l2OpNorm_rankOne_le`'s own proof with the scalar carried through.
  At an arbitrary unit eigenvector `x` of `w • rankOne v`,
  `quadForm (w • rankOne v) x = w * quadForm (rankOne v) x` (by
  `quadForm_smul_var`) `= w * (x ⬝ᵥ v)²` (by `rankOne_quadForm`), so
  `|quadForm (w • rankOne v) x| = |w| * (x ⬝ᵥ v)² ≤ |w| * (v ⬝ᵥ v)` by
  Cauchy–Schwarz (`dotProduct_sq_le` at the unit `x`) — the same three
  lemmas `l2OpNorm_rankOne_le` already cites, plus `quadForm_smul_var`.
  Feed this into `l2OpNorm_le_of_abs_eigvalOf_le`.
- **Lower bound** (`|w| * (v ⬝ᵥ v) ≤ ‖w • rankOne v‖`, the missing
  direction `l2OpNorm_rankOne_le` does not supply): `(w • rankOne v)
  *ᵥ v = w • (rankOne v *ᵥ v) = w • ((v ⬝ᵥ v) • v) = (w * (v ⬝ᵥ v)) •
  v` (by `Matrix.smul_mulVec_assoc` and `rankOne_mulVec`). Since `v ≠
  0` (it has a nonzero entry at `i`), `exists_eigvalOf_eq_of_mulVec_eq_
  smul` gives an index with `eigvalOf (w • rankOne v) _ _ = w * (v ⬝ᵥ
  v)` exactly, and `abs_eigvalOf_le_l2OpNorm` bounds it below the
  norm.

Both directions route entirely through already-proved lemmas across
three files (`Sparsification.lean`, `Spectral.lean`,
`Resolvent.lean`), reused rather than re-derived, and neither touches
the eigenvalue-multiset-scaling gap `secondEval_smul_of_pos`'s
docstring flags as absent — because the argument works with the
rank-one matrix's own explicit `rankOne_mulVec`/quadratic-form
structure directly, not with a generic "scale every eigenvalue by `w`"
theorem.

**A hypothesis the request's own formula omits, found here:** the
equality needs `i ≠ j`. At `i = j`, `laplacian_edgeAdj` gives the zero
matrix on the left (a "loop" is not a cut edge) while `2 * |w|` on the
right is nonzero whenever `w ≠ 0` — the two sides only agree at `i =
j` when `w = 0`. The delivered theorem should carry `i ≠ j` as an
explicit hypothesis; this is the "beyond the ask" precision this
project's proposals routinely surface (paralleling `boundary-outflow-
lemma.md`'s own removed-hypothesis finding on the other side of the
ledger).

## Scope decision: no new definition, no probabilistic content

Two decisions worth recording explicitly:

- **Do not introduce a new `laplacian_edge_update` definition.** The
  request's pseudocode names one, but `laplacian (edgeAdj i j w)` is
  already the identical object under an existing name; adding a
  second name for it would repeat the exact kind of duplication
  `boundary-outflow-lemma.md` flagged (and declined to fix) between
  `partIndicator`/`indicatorVec`. State the theorem directly about
  `laplacian (edgeAdj i j w)`.
- **This is a deterministic fact, not a probabilistic one.** The
  existing `EdgePerturbationTail.lean`/`EdgePerturbationDrift.lean`
  machinery bounds `‖∑ perturbSummand A p e ω‖` under a *random*
  Bernoulli resampling design (Tropp's matrix Bernstein,
  `edgePerturbation_norm_tail`) — a different question (a
  concentration tail over many outcomes) answered with different tools
  (measure theory, independence). This proposal's subadditive bound
  (below) is a plain triangle-inequality fact about a *fixed, known*
  finite sequence of edge-weight changes, with no probability space
  anywhere. The two are complementary, not overlapping: a deterministic
  primitive here could in principle simplify future reasoning about a
  *known* perturbation sequence without invoking the probabilistic
  machinery at all, but this proposal does not build that connection.

## Build order

### Step 1: The single-edge norm equality

```
theorem l2OpNorm_laplacian_edgeAdj (i j : V) (hij : i ≠ j) (w : ℝ) :
    ‖laplacian (edgeAdj i j w)‖ = 2 * |w|
```
Route: `laplacian_edgeAdj` to reduce to `‖w • rankOne v‖`, the two
directions above, and the direct computation `v ⬝ᵥ v = 2` at `v :=
Pi.single i 1 - Pi.single j 1` (`i ≠ j` giving distinct support
points). Natural home: `EdgePerturbation.lean`'s existing "single-edge
algebra" section (immediately after `laplacian_edgeAdj`, line ~150),
since it is a direct continuation of that section's own content.

### Step 2: The subadditive multi-edge bound

```
theorem l2OpNorm_sum_laplacian_edgeAdj_le {ι : Type} (s : Finset ι)
    (e : ι → V × V) (he : ∀ k ∈ s, (e k).1 ≠ (e k).2) (dw : ι → ℝ) :
    ‖∑ k in s, laplacian (edgeAdj (e k).1 (e k).2 (dw k))‖
      ≤ ∑ k in s, 2 * |dw k|
```
Route: the triangle inequality for finite sums (`norm_sum_le`,
standard for any normed space, which `Matrix V V ℝ` under the
`Matrix.L2OpNorm` instance already is) plus Step 1 applied termwise.
Pure assembly — no new inequality beyond Step 1 and `norm_sum_le`.

### Deferred and removed

- **A general "`eigvalOf (c • M) i = c * eigvalOf M i`" theorem for
  arbitrary symmetric `M`** — explicitly out of scope; per
  `secondEval_smul_of_pos`'s own docstring this needs eigenvalue-
  multiset scaling machinery absent from the pinned Mathlib and is
  deferred elsewhere pending a named consumer. Neither step above
  needs it.
- **A named `laplacian_edge_update` definition** — deliberately not
  introduced (see "Scope decision").
- **Connecting this deterministic layer back into
  `EdgePerturbationDrift.lean`'s probabilistic bounds** — plausible
  future work (a deterministic per-outcome bound could sanity-check or
  simplify special cases of the tail machinery) but not proposed here;
  the two stay independent siblings.

## QA plan

- Step 1: a concrete `K₂`/path-graph instance with `w` positive,
  negative, and zero, checked against the raw closed-form `laplacian
  (edgeAdj 0 1 w) = !![w, -w; -w, w]`-style entrywise computation
  already used as a fixture pattern elsewhere in this project's Heat/
  Signed QA sections.
- Step 1 fence: the `i = j` case, confirming the equality genuinely
  fails there at `w ≠ 0` (the omitted-hypothesis finding above),
  matching this project's standing adversarial-fence discipline
  (`governance/ADVERSARIAL_REVIEW.md`).
- Step 2: a small concrete sequence of 2–3 edge updates on a fixed
  small graph, cross-checking the assembled bound's RHS against a
  direct sum computation.

## Gate — Medium, no dependency

Like `boundary-outflow-lemma.md`, this needs no operator sign-off or
technical-direction decision: both steps are self-contained, reuse
only already-proved shelf material across three existing files, and
carry no dependency on any Low-gated proposal. Tracked as **Medium**
in `proposals/README.md`'s Active priority table.

## Operating instructions for an autonomous run

- Both steps are small enough to plausibly combine in a single run.
- **No new axioms.** Everything stays inside already-proved
  `Sparsification.lean`/`Spectral.lean`/`Resolvent.lean`/
  `EdgePerturbation.lean` machinery plus `norm_sum_le`; if either step
  needs something genuinely absent, stop and record the precise
  obstruction in `docs/6_SGT_BACKLOG.md` rather than admitting
  anything.
- Ship the `i = j` fence (QA plan above) in the same delivery as Step
  1, not as a follow-on audit pass.

## Open next step

Ready to pick up immediately — no dependency on any other proposal's
status.

## Delivery record (2026-09-07)

**Delivered at the full designed scope** — both steps plus every QA
item of the QA plan, in one run as the operating instructions priced
("both steps are small enough to plausibly combine in a single run";
"ship the `i = j` fence in the same delivery as Step 1, not as a
follow-on audit pass").

**Step 1, exactly as proposed** (including the `i ≠ j` hypothesis the
proposal's own beyond-the-ask finding requires):
`l2OpNorm_laplacian_edgeAdj (i j : V) (hij : i ≠ j) (w : ℝ) :
‖laplacian (edgeAdj i j w)‖ = 2 * |w|`, in `EdgePerturbation.lean`'s
single-edge-algebra section immediately after `laplacian_edgeAdj`, with
the route exactly as designed: the upper direction
`l2OpNorm_smul_rankOne_le` cloning `l2OpNorm_rankOne_le`'s
Cauchy–Schwarz technique with the scalar carried through the public
`quadForm_smul` (the proposal named the *private*
`Spectral.lean:quadForm_smul_var`; the identical public
`Sparsification.lean:quadForm_smul` is what actually composes — same
statement, no privacy obstacle); the lower direction
`abs_w_mul_dotProduct_self_le_l2OpNorm` through
`Matrix.smul_mulVec_assoc` + `rankOne_mulVec` +
`exists_eigvalOf_eq_of_mulVec_eq_smul` +
`abs_eigvalOf_le_l2OpNorm` — the two for-unrelated-purposes lemmas the
proposal identified, now consumed on a third surface; the packaging
equality `l2OpNorm_smul_rankOne : ‖w • rankOne v‖ = |w| * (v ⬝ᵥ v)` at
`v ≠ 0`; the `Pi.single`↔`ssEdgeDiff` bridge `edgeDiff_eq_ssEdgeDiff`
(via `dotProduct_ssEdgeDiff`, `v ⬝ᵥ v = 2` in one rewrite); and
`smul_rankOne_isSymm`.

**Step 2, exactly as proposed**:
`l2OpNorm_sum_laplacian_edgeAdj_le {ι} (s : Finset ι) (e : ι → V × V)
(he : ∀ k ∈ s, (e k).1 ≠ (e k).2) (dw : ι → ℝ) : ‖∑ k in s,
laplacian (edgeAdj (e k).1 (e k).2 (dw k))‖ ≤ ∑ k in s, 2 * |dw k|` —
`norm_sum_le` (the scoped `NormedAddCommGroup` instance the pinned
Mathlib provides under `Matrix.L2OpNorm`) plus Step 1 termwise. Pure
assembly, no new inequality.

**QA (`EdgePerturbation_QA.lean`'s new `NormPins` section, +15)** —
every item of the QA plan:
- the raw closed form `laplacian (edgeAdj 0 1 w) = !![w, -w; -w, w]` at
  symbolic weight (entrywise, the file's own fixture idiom);
- the value pins through the theorem at **positive, negative, and zero
  weight** (`6`, `10`, `0`), each with the old-machinery route B
  (`epn_K2_norm_of_w`: `laplacian_edgeAdj` + the file's own
  action-bound `epK2_rankOne_norm` — no new theorem consumed) — two
  routes, one value;
- **the `i = j` fence**: the loop Laplacian computed raw as the zero
  matrix (entrywise, not through the identity), and `2 * |3| ≠ 0`
  refuting the dropped-hypothesis statement — the omitted-hypothesis
  finding fenced in the same delivery as required;
- the two-update parallel sequence `(0,1)`, `(1,0)` at weight `3`:
  the raw sum `= 2 • L(edge 0 1 3)` (through the ordered-pair spelling
  symmetry `epn_edgeAdj_comm`) and **the subadditive bound attained
  with equality** (`12 = 12`) — the triangle inequality tight when the
  updates are parallel rank-one blocks on one difference vector;
- the three-edge `Fin 3` sequence (`(0,1)` at `1`, `(1,2)` at `-2`,
  `(0,2)` at `4`): the bound's RHS computed `14`, and the summed
  Laplacian computed **raw entrywise** as `!![5, -1, -4; -1, -1, 2;
  -4, 2, 2]` — note the honest signed degrees (vertex `1`'s row sum is
  `1 + (-2) = -1`): the first draft of this fixture used unsigned
  degrees (`3`) and the elaborator rejected it on the `(1,1)` diagonal
  — the QA caught its own author's arithmetic, which is the point.

**Scope decisions honored**: no `laplacian_edge_update` definition was
introduced (the theorem is stated directly about
`laplacian (edgeAdj i j w)`); no probabilistic content; the deferred
items (the general `eigvalOf (c • M)` scaling theorem, any connection
back into `EdgePerturbationDrift`) remain untouched as recorded.

**Verification.** Spike-first (`wip/epnorm_spike.lean` — green across
fix rounds; traps recorded for future runs: the pinned Mathlib's
`abs_le` is the `¬`-first conjunction `-b ≤ a ∧ a ≤ b`, the opposite of
the shelf-era assumption — the `constructor` bullets swap;
`l2OpNorm_le_of_abs_eigvalOf_le`'s constant clause needs the product's
nonnegativity, not `abs_nonneg` alone; `rw [l2OpNorm_laplacian_edgeAdj
(by norm_num)]` leaves `i j` as metavariables — explicit arguments
required; the `Fin 3` literal-entry reduction goes through
`Matrix.vecHead`/`Matrix.vecTail`, absent from the `cons_val` trio).
Both landed modules elaborate with zero errors/warnings (the 3
`ring_nf` infos in the QA file verified pre-existing at HEAD by
elaborating `git show HEAD:`'s copy). Explicit builds ✔. **22-declaration
axiom audit via `wip/epnorm_axcheck.lean` (7 shelf + 15 QA): every one
exactly `propext, Classical.choice, Quot.sound`** — zero axiom
contact, no `-- @refutes` tags (nothing admitted is consumed). Full
`lake build` + `check_build_completeness.py` — 135/135 fresh, 0 stale,
0 missing, exit 0. `lint_axioms` exit 0 (4 axioms unchanged).
`check_refutation_independence` (24-tag clean).
`check_public_reachability` (63 modules). `check_citations`.
`check_markdown_links`. `check_qa_name_uniqueness` (the new `epn_*`
names collision-free). `check_backlog_freshness` clean. Scoreboard
regenerated (**1369 → 1376 functional / 6698 → 6713 QA / 4 axioms / 0
sorries**) with the verification row. Map freshness exit 0 after the
stats sync in both map data tables + SVG regeneration (49 stations, no
status change — none owed: the EdgePerturbation station's status line
is unchanged, the delivery being a same-status enrichment).

**Remaining risk:** none owed — hard crust only, no axiom disposition
changed, no public statement changed. Honest scope: the equality needs
`i ≠ j` (fenced, not stated at loops); the subadditive bound is the
plain triangle inequality with no improvement at non-parallel sequences
(the three-edge instance's slack is not quantified); ~~the weighted
rank-one equality needs `v ≠ 0` (the zero vector's block is the zero
matrix and the statement is harmlessly false-but-vacuous there)~~
**(corrected 2026-09-07 by the corner audit below: that residue
sentence was wrong — the statement is TRUE at `v = 0`, both sides
provably zero, the clause truth-removable and removed.)**

------

## Corner-audit record (2026-09-07, run `20260907T200815Z-run-1`)

The standing "delivered-but-unfenced surfaces" agenda applied to this
delivery (uncommitted, amendable), its `v ≠ 0` clause having been
named by the previous run's handoff as the next candidate by recency.

**Finding: the clause was truth-removable, and the delivery's own
residue sentence about it was a documentation defect.** The delivery
recorded the weighted rank-one equality's hypothesis as covering a
corner where "the statement is harmlessly false-but-vacuous" — but at
`v = 0` both sides evaluate honestly to zero (`rankOne 0 = 0` entrywise
since `rankOne v i j = v i * v j`; `w • 0 = 0`; `‖0‖ = 0`;
`0 ⬝ᵥ 0 = ∑ i, 0 * 0 = 0`; `|w| * 0 = 0`), so the equality reads
`0 = 0` and is TRUE. The statement was never false at the corner — the
clause was an artifact of the eigenvalue-witness proof route for the
lower bound (`exists_eigvalOf_eq_of_mulVec_eq_smul` needs a nonzero
eigenvector), not of the mathematics. No Errata entry owed (no Lean
statement was ever false; the defect was in the residue prose, exactly
the quantizer audit's "away from zero" class).

**Closed in-run:**

1. **`abs_w_mul_dotProduct_self_le_l2OpNorm` strengthened in place**
   — the `v ≠ 0` hypothesis dropped; the proof gains a zero-corner
   case split (`w • rankOne 0 = 0` and `0 ⬝ᵥ 0 = 0` close the
   degenerate case to `0 ≤ 0`), the nonzero case unchanged.
2. **`l2OpNorm_smul_rankOne` strengthened in place** — the packaging
   equality is now unconditional.
3. **`l2OpNorm_laplacian_edgeAdj`'s proof simplified** — its `hvne`
   helper (nonzeroness of the edge-difference vector) existed only to
   feed the removed clause; deleted. The public statement is unchanged
   (its own `i ≠ j` hypothesis remains load-bearing and fenced —
   `epn_loop_fence`).
4. **The corner pinned in QA** (`EdgePerturbation_QA.lean`'s `NormPins`
   zero-corner section, +4 theorems): `epnZero_eq_QA` instantiates the
   now-unconditional equality AT the degenerate vector (route A),
   `epnZero_eq_raw` computes the same value raw (route B — the zero
   matrix's norm beside the zero dot product, no norm machinery), and
   `epnZero_lower_QA` consumes the unconditional lower bound at the
   value-carrying scale `w = 3` — the degenerate instance is not
   vacuous-by-scale; `epnZero_block` is the raw entrywise companion.

**Proof-trap note for the record:** the spike
(`wip/r1zero_spike.lean`) was green on the first round, but the first
landing attempt inlined `rw […, Matrix.dotProduct, mul_zero]` — the
def-eq unfold leaves the corner sum `∑ i, 0 i * 0 i` unsimplified, so
`mul_zero` fires too early and fails. The robust spelling is the
spike's standalone `have hdot : (0 : V → ℝ) ⬝ᵥ 0 = 0 := by simp
[Matrix.dotProduct]` closed first.

**Verification:** full ladder green — `lake build` + completeness
138/138 fresh, 0 stale, 0 missing (one documented artifact-removal
remediation after `touch`-based elaboration experiments left the
EdgePerturbation olean mtime-stale); 7-declaration axiom audit
(`wip/r1zero_axcheck.lean`: the two strengthened theorems, the
simplified single-edge equality, the four QA pins) — every one exactly
`propext, Classical.choice, Quot.sound`; `lint_axioms` (4 unchanged),
`check_refutation_independence` (24-tag), `check_public_reachability`
(64 modules), `check_citations`, `check_markdown_links`,
`check_qa_name_uniqueness` (`epnZero_*` collision-free),
`check_backlog_freshness`; scoreboard 1381 / 6842 / 4 / 0 with the
verification row; map freshness exit 0 after the 6842 sync. No census
re-run owed — no new or removed shelf declaration; two signatures
strengthened, their consumers unchanged in count, the inert set's zero
stands.

**Residue:** the corner pins sit at the `Fin 2` fixture (the equality
pins are generic in `w` but at the one degenerate vector — there is
only one); the removal covers the two named theorems only (the upper
bound `l2OpNorm_smul_rankOne_le` was already unconditional).
