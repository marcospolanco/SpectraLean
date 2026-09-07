# Proposal: The Rank-One Edge Perturbation Norm Bound

**Status:** Proposed. Restated in pure-mathematics form 2026-09-07 from
an external request relayed by the operator (not tracked in this
repository — see `.gitignore`); no operational, product, or patent
framing survives into this document, only the underlying mathematical
asks. Authorizes no Lean changes, axiom admissions, document rewrites,
or transit-map edits.

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
