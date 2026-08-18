# Proposal: Admit Perron–Frobenius for Irreducible Nonnegative Matrices

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-18. Authorizes no Lean changes, axiom admissions, document
rewrites, or external publication.

Assessed from `docs/8_MATHLIB_COVERAGE_MAP.md` (Perron–Frobenius confirmed
absent from the pinned Mathlib — the only "Perron" hits anywhere in the
pin are unrelated `BoxIntegral` files, a different Oskar Perron result),
`docs/1_STRATEGY.md`'s center-out policy and leverage test, the current
axiom list in `Scaffold/Mathlib` (16 explicit axioms, none in this
territory), and `Scaffold/Mathlib/GraphTheory/{RandomWalk,Normalized,
Stationary}.lean` (every existing walk/stationary-distribution result is
scoped to undirected, reversible, weighted graphs).

## Correction before this goes further: this is a scope decision, not a backlog item

Read `docs/1_STRATEGY.md` literally before treating this as routine: "The
near-term center is general SGT: weighted and normalized Laplacians...
Outward work must improve one of those interfaces or make a concrete,
broadly reusable connection." Directed graphs and general (possibly
non-reversible) Markov chains are not named anywhere in the current
backlog or radar's eight axes — every one of them is scoped to undirected
graphs. So this proposal is not "the next item in the queue"; adopting it
is a **deliberate expansion of the center's scope**, and should be
recognized as that decision explicitly, not adopted by momentum because
the math is exciting. The rest of this document argues for making that
decision, but does not make it.

## The finding

Everything Scaffold has built for random walks — `RandomWalk`,
`Normalized`, `Stationary`, and the in-flight `mixing-time-bound.md` —
works only because the walk is on an *undirected, weighted* graph, which
makes the transition matrix diagonally similar to a symmetric operator.
That similarity is the entire reason the `evals`/`eigvecOf` toolkit
applies at all. For a **directed** graph — most graphs an outside user
actually cares about: web graphs, citation networks, asymmetric
consensus/gossip protocols — there is no symmetric operator to restrict
to, and none of that machinery reaches. Symmetric spectral theory and
nonnegative-matrix theory are different toolkits; Scaffold has exactly
one of them. Perron–Frobenius is the other one, and it is completely
absent — from Mathlib and from Scaffold — confirmed by direct search this
session.

## Recommendation

Admit the **irreducible** case only — not the full general (possibly
reducible) theorem, and not the stronger primitive/aperiodic case with
strict eigenvalue dominance. Scope reasons follow in Calibration; this is
the smallest statement that unlocks a real, nameable consumer
(irreducible-directed-graph stationary distributions) without
overclaiming.

## Precise statement

For `A : Matrix V V ℝ`, nonnegative (`∀ i j, 0 ≤ A i j`) and irreducible
(defined below):

- The spectral radius `r` of `A` is a **positive real eigenvalue** of `A`.
- `r` has **algebraic multiplicity one** (simple).
- There is an eigenvector `x` for `r` with `x i > 0` for every `i`
  (strictly positive), and it is **unique up to positive scalar
  multiples** among nonnegative eigenvectors.
- `r` is the **only** eigenvalue of `A` with a nonnegative eigenvector.

Source: Horn, R. & Johnson, C., "Matrix Analysis", 2nd ed., Cambridge
University Press, 2013, Theorem 8.4.4 (Perron–Frobenius for irreducible
nonnegative matrices). Original results: O. Perron, *Zur Theorie der
Matrices*, Math. Ann. 64 (1907); G. Frobenius, *Über Matrizen aus nicht
negativen Elementen*, Sitzungsber. Königl. Preuss. Akad. Wiss. (1912).

**Irreducibility, stated combinatorially:** `A` is irreducible iff every
vertex can reach every other vertex via positive-weight directed edges —
`∀ i j, Relation.ReflTransGen (fun a b => 0 < A a b) i j`. This is the
directed analogue of the `supportGraph`/`SimpleGraph.Connected` pattern
already used for the undirected kernel characterization
(`electrical-structure-crust.md` step 2); the natural next step, if this
proposal is adopted, is a `supportDigraph`-style adapter mirroring
`supportGraph`'s role, rather than a bespoke predicate invented from
scratch.

## Calibration — the classic mistake this statement must not make

**Do not state strict eigenvalue dominance (`r > |λ|` for every other
eigenvalue `λ`) for the irreducible case.** This is the single most common
misstatement of Perron–Frobenius, and this repository has twice now
admitted a false statement by understating exactly this kind of
qualification (`old_cheeger_lower_bound_refuted_QA`, the pre-repair
`lambda2_variational`). Strict dominance over *all* other eigenvalues only
holds when `A` is additionally **primitive** (irreducible and aperiodic —
some power `A^k` is strictly positive everywhere). An irreducible but
imprimitive matrix — the simplest example is a directed cycle's adjacency
matrix — has `h` eigenvalues of modulus exactly `r`, evenly spaced around
the circle of radius `r` (`h` = the period), not just `r` itself. The
statement above only claims `r` is the unique eigenvalue **with a
nonnegative eigenvector**, which is correct for the irreducible case and
does not require primitivity. If a future extension wants strict
dominance (needed for power-iteration convergence rate arguments), it
needs primitivity added as an explicit further hypothesis, admitted or
proved separately — do not fold it into this axiom's statement.

**Do not claim this unlocks mixing-time bounds directly.**
`mixing-time-bound.md` is scoped to reversible walks via the symmetric
spectral-gap route and does not need this axiom. A convergence-rate
argument for general (non-reversible, primitive) chains via power
iteration is a genuinely separate, later proposal, not a corollary of
this one.

## What it would unlock, if adopted

- **General Markov chain stationary distributions.** For an irreducible
  directed weighted graph's row-normalized transition matrix, this gives
  existence and uniqueness of a positive stationary distribution — the
  directed-graph analogue of what `Stationary.lean` already proves for
  the undirected/regular case, currently unreachable there because that
  proof route is spectral-symmetric.
- **PageRank-style centrality, with an existence proof.** The canonical
  application-ring algorithm on directed graphs has no route into this
  backlog at all today; this is the specific gap that closes it.
- **A second, complementary toolkit alongside the existing symmetric one**,
  not a replacement — undirected/reversible work keeps using `evals`;
  directed/general work would use this family instead.

## Scope

1. Formalize irreducibility via directed reachability (above), mirroring
   `supportGraph`'s pattern rather than inventing a new predicate shape.
2. State and admit the axiom exactly as scoped — existence, positivity,
   simplicity, nonnegative-eigenvector uniqueness, at the qualification
   level above. No strict-dominance clause.
3. QA: a positive witness (a small irreducible nonnegative matrix, Perron
   root and eigenvector computed independently) and a **load-bearing
   negative witness for imprimitivity** specifically — a directed cycle's
   adjacency matrix, showing multiple eigenvalues of modulus `r` exist,
   so a future reader cannot mistake the admitted statement for the
   stronger primitive case. This negative witness is the single most
   important QA item in this proposal, given the Calibration section
   above.
4. Update the source index (`index/sources/`), the Mathlib coverage map
   (this closes one of `docs/8_MATHLIB_COVERAGE_MAP.md`'s named-absent
   rows), and the explicit axiom count (17, pending where Woodbury/Sherman–
   Morrison land it first).
5. Do **not** attempt the stationary-distribution or PageRank consumers in
   the same run that admits the axiom — per the standing one-step-per-run
   discipline, and because those are real, separate proof obligations
   this document does not scope.

## Deferred and removed

- **The general (possibly reducible) theorem** — weaker conclusions,
  more case analysis, no named consumer yet. Out of scope.
- **Primitivity and strict eigenvalue dominance** — a real, separate
  extension if power-iteration convergence work is ever wanted; not
  folded into this axiom, per Calibration.
- **Any consumer work** (stationary distributions, PageRank) — named as
  the payoff, not delivered by this proposal. Each needs its own
  follow-on proposal once the axiom exists.

## Acceptance criteria

- The axiom's statement matches Horn & Johnson Theorem 8.4.4 exactly in
  content, at the qualification level scoped above — no strict dominance
  clause.
- QA includes both the positive witness and the imprimitive-cycle
  negative witness before this is considered landed, not as a follow-up.
- `docs/8_MATHLIB_COVERAGE_MAP.md`'s "Perron–Frobenius / nonnegative-matrix
  theory: Absent" row is updated to reflect the new admission, not left
  stale.
- The scope-decision correction at the top of this document is resolved
  explicitly (adopted or declined) before any Lean work starts — this is
  not a default per the leverage test as currently written.
