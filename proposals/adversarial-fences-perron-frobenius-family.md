# The Perron–Frobenius Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run `20260905T020149Z-run-1`,
session `ses_f90b5fc41ffeyoVZDBjld7GYKp`; see the delivery record).

## Scope

The prior terminal handoff's named top target — "the audit method's
natural next targets, by the standing survey numbers: `PerronFrobenius`
(7 transitive non-QA consumers, whose QA carries the degenerate-corner
findings but has not had a fresh hypothesis-necessity pass)" —
confirmed by this run's own independent reverse-import walk: **7
transitive non-QA consumers** (`PrimitiveConvergence` directly; the
closure adds `IrreducibleStationary`, `PageRank`, `DirectedMixing`,
`Mixing`, `Oversmoothing`, and the `EmpiricalStationary` capstone) —
the highest-ranked unaudited shelf by the standing survey numbers. The
shelf is `Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean`: the
`Matrix.IsIrreducible` definition (combinatorial strong connectivity
through positive-weight directed arcs) and the admitted
`perron_frobenius` axiom (one of the repository's 4 remaining admitted
axioms, Horn–Johnson Theorem 8.4.4). Its QA (`PerronFrobenius_QA.lean`,
676 lines) carries the 2026-08-28 degenerate-cardinality audit's
findings (the card-0 `hex` unsatisfiability and the `Fin 1` singleton
pin, both tagged `-- @refutes`) and the mandated strict-dominance
strengthening refutation — but **zero fence sections**: no
hypothesis-necessity pass has ever been run over the axiom's three
hypothesis clauses, and the `IsIrreducible` definition's
positive-arcs-only convention has no witness.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(sixteen precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger, regular
Cheeger, effective-resistance, electrical-flow, Foster,
sparsification-core, band-projector, Davis–Kahan core, normalized,
variational-transfer, and resolvent) — re-read every declaration's
hypothesis clauses, identify those with no negative witness, and close
each with a hypothesis-form fence (the dropped-hypothesis statement
refuted at a fixture where every other hypothesis is genuine, certified
by pinned-value companions), or record a non-fenceable with its
mechanism.

Consumer case (the leverage): this is the **axiom** shelf of the
directed axis — every directed-input result in the library
(`IrreducibleStationary`'s existence/uniqueness, `PageRank`'s
regularized existence, `DirectedMixing`'s power-iteration theorem,
`Mixing`'s directed layer, `Oversmoothing`'s plain-walk certificates)
reaches nonnegative-matrix spectral theory through exactly this
admission or through the consumers it unlocked. A hypothesis clause
that is not load-bearing here is trust surface the axiom does not need;
a clause that *is* load-bearing now has a machine-checked witness that
it cannot be dropped silently.

## Step-0 findings: the priced fence list

Clause census over the shelf's public surface (the axiom's three
hypothesis clauses; the `IsIrreducible` definition carries no
hypotheses of its own, but its positive-arcs convention is priced as a
definitional witness):

1. **`hnn : ∀ i j, 0 ≤ A i j` (nonnegativity).** No negative witness
   anywhere in the repository — every existing fixture is nonnegative.
   Priced at the new fixture `pfNegDiag = !![-1, 2; 2, -1]]` (Fin 2,
   symmetric, negative diagonal): irreducibility is *genuine* (both
   off-diagonal arcs `2 > 0`), `hex` is genuine (`A 0 1 = 2 > 0`), and
   the dropped-`hnn` statement is refuted through the conjunction of
   the eigen clause and the domination clause: a strictly positive
   eigenvector forces `r = 1` (the two rows sum to
   `(x₀ + x₁) = r (x₀ + x₁)` with `x₀ + x₁ > 0`), while the complex
   spectrum `{1, −3}` (charpoly `(X − 1)(X + 3)`, pinned through the
   2×2 determinant) forces `|−3| = 3 ≤ r` by domination — `3 ≤ 1` is
   false. Every quantity is rational; the fixture needs no irrational
   Perron data. Note the pricing subtlety: the eigen conjuncts *alone*
   are satisfiable at this fixture (`r = 1`, `x = (1, 1)` works — the
   fixture is symmetric with a genuine positive eigenvector), so the
   fence genuinely needs the domination clause to close; a fixture
   killed through the eigen clause alone would leave the domination
   route untested.
2. **`hirr : A.IsIrreducible` (irreducibility).** No negative witness
   anywhere. Priced at the new fixture `pfRed = !![0, 1; 0, 0]]`
   (Fin 2, the nilpotent directed edge): `hnn` is genuine, `hex` is
   genuine (`A 0 1 = 1 > 0`), irreducibility genuinely fails (vertex
   `1` reaches nothing — both row-1 entries are `0`), and the
   dropped-`hirr` statement is refuted through the eigen clause alone:
   `A *ᵥ x = (x₁, 0) = r • x` forces `r x₁ = 0` against `r > 0` and
   `x₁ > 0`. No charpoly needed — the mildest possible kill.
3. **`hex : ∃ i j, 0 < A i j` (nonzero guard).** The degenerate-corner
   audit proved `hex` *unsatisfiable* at `Fintype.card V = 0` (a
   satisfiability statement, tagged `-- @refutes`), but never that the
   clause is *needed* where it fails satisfiably. Priced at the new
   fixture `pfZero1 = !![0]]` (Fin 1, the one-vertex zero matrix):
   `hnn` is genuine, irreducibility is genuine (reflexivity on the
   subsingleton), `hex` genuinely fails (the single entry is `0`), and
   the dropped-`hex` statement is refuted through the eigen clause
   alone: `A *ᵥ x = (0) = r • x` forces `r x₀ = 0` against `r > 0` and
   `x₀ > 0`. This is exactly the corner the module documentation names
   ("the vacuously irreducible 1×1 zero matrix … would otherwise falsify
   `0 < r`") — now a proved fence rather than a docstring warning.
4. **The `IsIrreducible` positive-arcs convention (definitional
   witness).** The definition demands `0 < A a b` steps; that a
   negative entry is not an arc is load-bearing for every consumer that
   reaches the axiom through a signed matrix. Priced as a companion
   witness: `pfNegCycle = !![0, -2; -2, 0]]` (Fin 2, all entries
   nonpositive) is *not* irreducible — vertex `1` has no positive step
   out — so strong connectivity cannot be routed through negative
   weight. Same route as clause 2's irreducibility failure.

**Screened (delivered witnesses, no new fence owed):** the
strict-dominance strengthening (`strict_dominance_refuted_QA`, the
conclusion cannot be *strengthened* — the dual of the hypothesis
necessity questions); the card-0 corner
(`perron_frobenius_hex_unsat_card_zero_QA`); the `Fin 1` singleton
(`perron_frobenius_S1_QA`, the conclusion pinned to hand data where
every hypothesis holds). The axiom's *conclusion* conjuncts are what it
provides; necessity-of-conclusion is not a priceable class (a weaker
conclusion is not false), and the strict-dominance fence already
carries the conclusion-shape question.

**Non-fenceables:** none — the hypothesis surface is exactly three
clauses, each fenced. The `variable` binders (`Fintype`, `DecidableEq`)
are instance arguments, not mathematical hypotheses, and the `Fin 0` /
`Fin 1` corners they govern are screened above.

## Fixtures (all new, all rational)

- `pfNegDiag = !![-1, 2; 2, -1]]` — the `hnn` breaker: symmetric,
  negative diagonal, both arcs positive. Complex spectrum `{1, −3}`
  pinned through the 2×2 determinant (real charpoly
  `(X − 1)(X + C 3)`; complex factorization
  `(X − C (ofReal 1)) (X − C (ofReal (−3)))`).
- `pfRed = !![0, 1; 0, 0]]` — the `hirr` breaker: nonnegative,
  one positive entry, vertex `1` stranded.
- `pfZero1 = !![0]]` — the `hex` breaker: the one-vertex zero matrix.
- `pfNegCycle = !![0, -2; -2, 0]]` — the definitional witness:
  negativity creates no arcs.

## Delivery record

DELIVERED at the full priced scope — QA-only, a pure insertion in
`PerronFrobenius_QA.lean`'s new `AdversarialFences` section: the three
hypothesis-form fences (each tagged `-- @refutes: perron_frobenius`,
each refuting the axiom-minus-one-clause statement shape at a fixture
where the kept clauses are proven genuine) plus the definitional
witness, entry tables, irreducibility/non-irreducibility lemmas,
eigen-row lemmas, the real and complex charpoly factorizations of
`pfNegDiag`, the complex-roots pin, and the pinned-value companions
(the `r = 1` eigen pin at `pfNegDiag`; the stranded-row equations at
`pfRed`; the `r x₀ = 0` collapse at `pfZero1`). Zero axiom contact in
the new fences (`#print axioms` on every new declaration — the
`perron_frobenius` axiom is *refuted in shape*, never consumed; see
Verification). The three new tags take the repository's tag count from
9 to 12, all mechanically checked for refutation independence.

Technique findings recorded for future audits:

1. **An axiom's hypothesis fence needs a kill route through the
   conclusion's own machinery.** The `hnn` fixture's eigen conjuncts
   are satisfiable in isolation (`r = 1`, `x = (1,1)`); only the
   domination clause closes the refutation. Pricing must check *which*
   conjunct does the killing — a fixture killed through one conjunct
   leaves the others' interface untested, which is why the pricing
   above records the kill route per fence.
2. **`Relation.ReflTransGen.cases_head` is the one-step route to
   non-irreducibility witnesses** at 2×2: `ReflTransGen R 1 0` gives
   `1 = 0` (decidable-false) or a first step `0 < A 1 c`, and both
   candidates `c ∈ {0, 1}` die on the pinned row entries — no
   induction over the transitive closure needed.
3. **The `C`-numeral normalization chain extends by one link** (`C 3`
   via `3 = 2 + 1` through the file's existing `C_two` helper), the
   same pattern the original delivery used for `C 2` and `C 4`.

## Verification

Spike first (`wip/pffences_spike.lean`, iterated to zero errors/zero
warnings before any shelf edit); `lake env lean` on the landed module;
explicit `lake build Scaffold.QA.LinearAlgebra.PerronFrobenius_QA`;
`#print axioms` via `wip/pffences_axcheck.lean` on every new
declaration (each exactly `propext, Classical.choice, Quot.sound` —
the fences refute the axiom's dropped-clause shapes without consuming
it); full `lake build` immediately followed by
`check_build_completeness.py`; `lint_axioms`; `check_refutation_independence`
(12-tag clean); `check_public_reachability`; `check_citations`;
`check_markdown_links`; `check_backlog_freshness`; scoreboard
regeneration; `check_scaffold_map_freshness` after the stats sync in
both map data tables. The landing verified as a pure insertion.
