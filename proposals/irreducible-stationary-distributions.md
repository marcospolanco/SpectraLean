# Proposal: Irreducible Stationary Distributions — the First Perron–Frobenius Consumer

**Status:** **DELIVERED 2026-08-24** (run `20260824T024831Z-run-1`) —
Step 0 (this survey) and Step 1 (the module + QA) in one run, per the
directed-operators Steps 0+1 precedent; see the delivery record at the
bottom. Zero new axioms (count stays 9); the five stationary-distribution
theorems are conditional on `perron_frobenius` exactly as this document
specified, the transfer lemmas unconditional.

Assessed from `Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean` (the
admitted axiom's exact clause structure), `Scaffold/Mathlib/GraphTheory/
Normalized.lean` (`walkTransitionMatrix`, its entry form, row
stochasticity, and `*ᵥ 1 = 1`), `Scaffold/Mathlib/GraphTheory/Mixing.lean`
(`stationaryVec`, the deg/vol combinatorial route on the symmetric cone),
the pin's `Matrix.dotProduct_mulVec`/`Matrix.mulVec_transpose`/
`Matrix.mulVec_smul` (all located this session), and `Relation.ReflTransGen`'s
recursor API in the pinned Mathlib.

## The obligation this discharges

`perron_frobenius` was admitted 2026-08-22 with consumers named but not
delivered (its own module docstring: "Irreducible-directed-graph
stationary distributions (existence and uniqueness of a positive
stationary distribution for the row-normalized walk) and PageRank-style
centrality. Per the proposal's one-step discipline these are separate
follow-on proof obligations, not corollaries of this admission."). This
is that first obligation. It is also the strategy's load-bearing-growth
principle applied to the trust surface: the axiom currently has QA
witnesses (fixture instantiation, the imprimitivity fence) but **no
theorem consumer** — nothing downstream whose proof would fail if an
axiom clause were misstated. A stationary-distribution theorem is
exactly that consumer: it consumes clause 5 and clause 6 *structurally*
(see Route), so a wrong eigenvalue-identification or
uniqueness-up-to-scale clause breaks the derivation loudly. And it is
the directed axis' first *theorem*: the existing directed content
(`GraphTheory.Directed`, the PF admission itself) is definitions,
identifications, and calibration witnesses.

## The statement (Step-0 recorded shape)

For `A : WAdj (V := V)` nonnegative, irreducible (`Matrix.IsIrreducible`),
with some positive entry and positive out-degrees, writing
`P = walkTransitionMatrix A`:

1. **Existence with full support:**
   `∃ π, (∀ i, 0 < π i) ∧ (∑ i, π i = 1) ∧ π ᵥ* P = π`.
2. **Uniqueness up to positive scale** (among all nonzero nonnegative
   stationary vectors, not just distributions):
   `σ, τ` nonnegative, nonzero, stationary → `∃ c > 0, τ = c • σ`.
3. **The `∃!` packaging** (the standard textbook statement):
   `∃! π, (∀ i, 0 ≤ π i) ∧ (∑ i, π i = 1) ∧ π ᵥ* P = π` — uniqueness
   among *nonnegative* stationary distributions, with strict positivity
   derived, not hypothesized.
4. **Full-support corollary:** every nonzero nonnegative stationary
   vector is strictly positive — no stationary distribution of an
   irreducible chain can vanish anywhere.

Statement-shape decisions recorded before stating:

- **Carrier is `WAdj`, stationarity is `vecMul` form** (`π ᵥ* P = π`) —
  Mathlib's native left-action, one `Matrix.mulVec_transpose` away from
  the eigenvector form `Pᵀ *ᵥ π = π` that the proof works in.
- **`hdeg : ∀ i, 0 < deg A i` is a hypothesis, not a derivation.** It is
  implied by `hnn + hirr + 2 ≤ card V` (a first arc out of every vertex),
  but deriving it is plumbing; the hypothesis matches the shelf's own
  interface pattern (`walkTransitionMatrix_row_sum`,
  `walkTransitionMatrix_mulVec_one` both take it).
- **Nothing about rates, mixing, or convergence.** Geometric convergence
  needs primitivity (strict dominance), which the axiom deliberately
  does not claim (the `strict_dominance_refuted_QA` fence). Mixing on
  the irreducible directed axis is a separate future obligation gated
  on a primitivity-shaped admission — explicitly not smuggled in here.
- **PageRank is not folded in.** It is the second consumer (needs the
  teleportation/damping construction and a reducible-case argument);
  per the one-step discipline it needs its own document.

## Route (every dependency verified present)

The proof never touches charpoly, rootMultiplicity, or the complex
domination clause — the derivation runs entirely through clauses 5 and 6:

1. **`P` inherits nonnegativity, irreducibility, and a positive entry**
   (entry form `P i j = (deg i)⁻¹ * A i j`; sign pattern preserved by
   the positive row scaling; irreducibility transfer by a private
   `ReflTransGen` congruence lemma — the pin has `mono` for `ReflGen`
   but no congruence for `ReflTransGen`, priced at 4 lines).
2. **`r = 1` from clause 5 alone:** `onesVec` is a nonzero nonnegative
   eigenvector of `P` at eigenvalue `1` (the shelf's
   `walkTransitionMatrix_mulVec_one`), and clause 5 forces every such
   eigenvalue to be the Perron root. No argmax bound, no spectral
   radius.
3. **`s = 1` for the transposed application by the bilinear pairing:**
   `v ⬝ᵥ (P *ᵥ u) = (v ᵥ* P) ⬝ᵥ u = (Pᵀ *ᵥ v) ⬝ᵥ u` (the pin's
   `Matrix.dotProduct_mulVec` then `Matrix.mulVec_transpose`); the left
   side is `v ⬝ᵥ u` (since `r = 1`), the right side is `s • (v ⬝ᵥ u)`,
   and `v ⬝ᵥ u > 0` (both Perron vectors strictly positive,
   `Finset.sum_pos`). Cancel. `Pᵀ`'s irreducibility is the converse of
   `P`'s (a private 2-case induction on `ReflTransGen`; the pin's
   `ReflTransGen.symmetric` is close but needs a symmetric relation,
   which `0 < Aᵀ ·` is not).
4. **Normalization:** `π := (∑ v)⁻¹ • v`; `∑ v > 0`; stationarity
   through `Matrix.mulVec_smul`; positivity through the scalar.
5. **Uniqueness:** any nonzero nonnegative stationary vector is a
   nonnegative eigenvector of `Pᵀ` at eigenvalue `1`, so clause 6 makes
   it `c • v` with `c > 0`; two such are positive multiples of each
   other; equal normalization forces the scale to `1`. Full support
   falls out of `c > 0 ∧ v > 0`.

The two axiom applications are the only axiom contact; everything
between them is elementary hard crust. This is the smallest consumer
shape that exercises both the eigenvalue-identification and
uniqueness clauses.

## QA obligations (all mandatory)

1. **Asymmetric directed fixture** (a genuinely directed walk — on two
   vertices row normalization always symmetrizes, so the star
   `!![0,1,1; 1,0,0; 1,0,0]` on `Fin 3`): the `∃!` instantiated, the
   candidate `(1/2, 1/4, 1/4)` verified **completely raw** (all three
   predicates by hand matrix arithmetic), so the theorem's uniqueness
   identifies its witness with the hand value while the hand route
   independently proves the predicate satisfiable.
2. **Symmetric-cone agreement** (the K₂ edge): the PF-derived unique
   stationary distribution *equals* `Mixing.stationaryVec` (deg/vol) —
   two independent API paths to one value: the axiom route vs. the
   combinatorial route. A disagreement would falsify one of them.
3. **Reducibility fence** (two disjoint edges on `Fin 4`): the
   hypothesis-free `∃!` conclusion **refuted in proved form** — two
   distinct stationary distributions exhibited with `hnn`/`hdeg`
   verified intact — so `hirr` is exercised as a fence, not
   decoration. The scale-uniqueness theorem's hypothesis-free form is
   refuted on the same fixture (the two witnesses are provably not
   scalar multiples).

## Acceptance bar

- The module compiles directly with zero errors/warnings; `#print
  axioms` on the public theorems reads `perron_frobenius` **plus** the
  standard three — reported honestly: these theorems are conditional on
  the axiom, never described as foundationally proved. The transfer
  lemmas (irreducibility congruence/flip, the walk-matrix transfer)
  read only the standard three.
- QA has no `sorry`/`admit`; its axiom-consuming declarations list
  `perron_frobenius`, its raw ones do not.
- Zero new axioms (count stays 9); citation surface unchanged (no new
  axioms; the consumer docstrings cite the source *through* the axiom's
  Horn–Johnson record, no new locators invented).
- `index/map/spectral_graph.md` gains the module's declarations;
  `docs/6_SGT_BACKLOG.md` item 8 records the first consumer delivered,
  PageRank remaining.

## Delivery record

**DELIVERED 2026-08-24 (run `20260824T024831Z-run-1`) — Steps 0+1 in one
run, zero new axioms (count stays 9), QA 1621 → 1715
(`IrreducibleStationary_QA` a new file at 94).**

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/IrreducibleStationary.lean`
(namespace `SpectralGraphTheory`, minimal imports — PerronFrobenius +
Normalized; the umbrella importing it) — the two unconditional transfer
lemmas (`isIrreducible_transpose`: strong connectivity is arc-reversal
invariant, through the private `ReflTransGen` flip induction;
`walkTransitionMatrix_isIrreducible`: positive row scaling preserves the
support digraph, through the private `ReflTransGen` congruence — the pin
has `mono` for `ReflGen` only) and the five axiom-conditional theorems:
`exists_walkPerronVector` (the transposed Perron engine at exactly the
recorded shape), `exists_stationaryVec_of_irreducible`,
`stationaryVec_smul_of_irreducible`,
`existsUnique_stationaryVec_of_irreducible` (the `∃!` among nonnegative
distributions, positivity derived), and `stationaryVec_pos_of_irreducible`
(full support). **The route held exactly as surveyed:** `r = 1` from
clause 5 at `onesVec` (the shelf's `walkTransitionMatrix_mulVec_one`),
the transposed root `s = 1` from the bilinear pairing
(`dotProduct_mulVec` then `mulVec_transpose`, positivity by
`Finset.sum_pos`, cancellation by `mul_right_cancel₀`), uniqueness
through clause 6 twice. No charpoly, no rootMultiplicity, no complex
domination clause — the two axiom applications touch only clauses 5
and 6, as designed.

**QA (+94, `Scaffold/QA/SpectralGraph/IrreducibleStationary_QA.lean`):**
all three mandated witnesses. (1) The asymmetric directed star
`!![0,1,1; 1,0,0; 1,0,0]` on `Fin 3` (two vertices cannot carry an
asymmetric irreducible walk — row normalization symmetrizes): all four
hypotheses hand-verified (the irreducibility by nine explicit
reachability certificates), the walk entries pinned
(`P 0 1 = P 0 2 = 1/2`, `P 1 0 = P 2 0 = 1`), the hand value
`(1/2, 1/4, 1/4)` verified **completely raw** (nonnegativity, mass,
and all three stationarity coordinates against the pinned walk
entries), and `A3_stationary_eq_hand_QA` the load-bearing join: every
stationary distribution of the fixture, however produced, equals the
hand value. (2) The symmetric-cone agreement on `K₂`:
`A2_stationary_eq_stationaryVec_QA` pins the PF-unique distribution
*equal* to `stationaryVec`, the predicate supplied entirely by the
shelf's detailed-balance chain (`stationaryVec_pos`,
`sum_stationaryVec`, `walk_isStationary` flipped through
`mulVec_transpose`) — two independent API paths to one value — with
the combinatorial value computed through its own definition to
`(1/2, 1/2)`. (3) The reducibility fence on two disjoint `Fin 4`
edges: both witnesses' three predicates verified raw, `hnn`/`hdeg`
verified intact, the hypothesis-free `∃!` conclusion refuted in proved
form (two distinct stationary distributions), and the hypothesis-free
scale-uniqueness conclusion refuted on the same fixture (the two
witnesses provably not positive multiples — the scalar forced to `0`
at the shared coordinate, against its positivity). Plus the
full-support instantiation reading exactly the hand values.

**Verification:** spike first (`wip/pfc_spike.lean`, four rounds to
green, the route's survey confirmed verbatim); `lake env lean` on the
module and the QA file — zero errors, zero warnings each; explicit
`lake build` targets both ✔; `#print axioms` via `wip/is_axcheck.lean`
on all 7 public + 12 representative QA declarations — the split
exactly as specified: the 5 axiom-consuming public theorems and the 4
axiom-route QA theorems list `perron_frobenius` + the standard three,
the transfer lemmas and every raw QA lemma only the standard three;
**full `lake build` ✔ (2257 targets, +1, "Build completed successfully";
zero warnings in the changed modules — the log's only Scaffold
diagnostic the documented pre-existing note in untouched
`Derived/ProjectorDrift.lean`)**; `lint_axioms` (**9**, unchanged),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**1715/9/0**, idempotent).

**Pin-technique notes (recorded for future runs):** the scoreboard's
declaration counter is ASCII-only — unicode declaration names (π, ₁)
are silently uncounted, so QA identifiers stay ASCII (`pi3`, `pi4a`);
entry/degree lemmas at literal indices match `rw`/`simp only` freely,
but under `fin_cases` the substituted indices match only
`simp [lemma]` at predicate level — evaluate finite sums through
literal component lemmas assembled by `funext` + `fin_cases` + `exact`
(defeq-closed), never a sum-unfolding simp under `fin_cases`;
`Relation.ReflTransGen.head hstep ih` (goal-directed) builds the
flipped closure where `single`/`trans` combinations cannot (the
relation is inferred from the embedded proof's type, not the goal);
`reflTransGen` tail-case induction with a right-endpoint motive needs
no generalization; `Finset.mul_sum` at this pin has the factored form
on the left (use `←`); `inv_mul_cancel₀` after `← Finset.mul_sum`
needs `exact` (alpha-equivalent binders resist `rw`); IsSymm on
literals through `Matrix.IsSymm.ext`; `div_mul_cancel₀` takes its
value argument first (the recorded Heat trap, re-hit); `omit ... in`
before the docstring (recorded, re-hit); `rw ... at <theorem-name>`
fails — copy into a `have` first; `first | exact` alternatives commit
before embedded `by`-blocks are checked — a structurally-applicable
alternative with a failing embedded proof swallows the branch (the
irreducibility proofs' arc-`have` + named-`exact` structure exists to
defeat this).

**Open follow-ons (not started, per the one-step discipline):** the
PageRank consumer (the teleportation/damping construction, reducible
input — its own document); the symmetric-connected → irreducible
bridge lemma (`SimpleGraph.Connected (supportGraph A) → A.IsIrreducible`
for symmetric nonneg weights — the natural adapter making every
undirected shelf theorem PF-applicable, cheap but scope-creep here);
mixing/rate statements on the directed axis (gated on a
primitivity-shaped admission — the axiom deliberately claims no strict
dominance).
