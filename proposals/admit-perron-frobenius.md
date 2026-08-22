# Proposal: Admit Perron–Frobenius for Irreducible Nonnegative Matrices

**Status:** **DELIVERED 2026-08-22** (run `20260822T211552Z-run-1`) —
the scoped admission, exactly as this document's Scope list and
acceptance criteria specify; see the delivery record at the bottom.
Priority was **Medium**; the scope decision was adopted 2026-08-19
(operator decision on record — see `docs/1_STRATEGY.md`'s center-out
prioritization section). Explicit axioms 9 → 10; no consumer work
(stationary distributions, PageRank remain named follow-ons, per the
one-step-per-run discipline honored below).

Assessed from `docs/8_MATHLIB_COVERAGE_MAP.md` (Perron–Frobenius confirmed
absent from the pinned Mathlib — the only "Perron" hits anywhere in the
pin are unrelated `BoxIntegral` files, a different Oskar Perron result),
`docs/1_STRATEGY.md`'s center-out policy and leverage test, the current
axiom list in `Scaffold/Mathlib` (16 explicit axioms, none in this
territory), and `Scaffold/Mathlib/GraphTheory/{RandomWalk,Normalized,
Stationary}.lean` (every existing walk/stationary-distribution result is
scoped to undirected, reversible, weighted graphs).

## This was a scope decision, not a backlog item — now resolved

Directed graphs and general (possibly non-reversible) Markov chains were
not named anywhere in the backlog or radar's eight axes before this
proposal — every one of them was scoped to undirected graphs, so adopting
this was a deliberate expansion of the center's scope, not routine
backlog work. **Resolved 2026-08-19: adopted.** `docs/1_STRATEGY.md`'s
center-out prioritization section now records the directed axis as in
scope, on the strength of this proposal's own leverage case (below) and
`sgt-gaps.md`'s external-consumer evidence (PageRank-style centrality,
directed community detection). The leverage test itself is unchanged —
adjacency alone still does not justify admission — only the "undirected
only" default is lifted.

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
- The scope decision is resolved (adopted, 2026-08-19, recorded above and
  in `docs/1_STRATEGY.md`) — no longer a precondition, but the axiom
  admission itself still needs an autonomous run directed at this
  proposal specifically, per the standing one-step-per-run discipline.

---

## Delivery record (2026-08-22, run `20260822T211552Z-run-1`)

The scoped admission, delivered exactly per the Scope list and
acceptance criteria above.

**Module:** the new `Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean`
(namespace `Scaffold.LinearAlgebra`), containing the irreducibility
predicate and the single admitted axiom. Explicit axioms 9 → 10;
`Matrix.IsIrreducible` is the only new definition.

**Scope item 1 (irreducibility via directed reachability):** delivered
as a *global* `Matrix.IsIrreducible` — `∀ i j, Relation.ReflTransGen
(fun a b => 0 < A a b) i j`, Fintype-free, mirroring `Matrix.IsSymm`'s
reading surface rather than a bespoke predicate (the `supportDigraph`
adapter this document mused about stays unnecessary: no consumer has
asked for the graph object itself, only the predicate). Statement-shape
note recorded before stating: the def deliberately carries no
`Fintype`, since reachability needs none.

**Scope item 2 (the axiom at the scoped qualification level):**
delivered as `perron_frobenius (hnn) (hirr) (hex)` with the conclusion
packaging exactly the four bullets of the Precise-statement section
plus the spectral-radius content:

- `0 < r` and `∀ i, 0 < x i` with `A *ᵥ x = r • x` — bullet 1
  (together with the domination clause below, this says `r = ρ(A) ∈
  spectrum(A)`);
- `Polynomial.rootMultiplicity r A.charpoly = 1` — bullet 2 (simplicity
  over `ℝ`; multiplicity of a real root is invariant under the
  `ℝ → ℂ` coefficient extension, so this is the algebraic multiplicity);
- the strong H&J uniqueness — every nonzero nonnegative eigenvector,
  *whatever its eigenvalue `μ`*, is `∃ c > 0, y = c • x` — bullet 3;
- `μ = r` as an explicit conjunct — bullet 4 (one derivation from the
  previous clause, stated anyway so each source bullet maps to a
  visible conjunct);
- `∀ z ∈ (charpoly (A.map (algebraMap ℝ ℂ))).roots, |z| ≤ r` — the
  spectral-radius encoding: the pre-edit survey found no matrix
  spectral radius in the pin (`spectralRadius` hits are
  operator-theory/C*-algebra files, the thread the resolvent program
  already found inapplicable to real matrices), so `ρ(A)`'s content is
  stated directly through the complexified charpoly roots.

Two recorded statement differences from H&J, both documented in the
module: (a) the `hex : ∃ i j, 0 < A i j` guard — H&J work at `n ≥ 2`
where irreducibility already forces a positive entry, but over an
arbitrary `Fintype V` the vacuously irreducible 1×1 zero matrix and the
empty type would falsify `0 < r`; `hex` is exactly the missing strength
(implied by `hirr` whenever `2 ≤ card V`), not decoration. (b)
Irreducibility is the combinatorial strong-connectivity form, not
permutation-similarity. **No strict-dominance clause** — the Calibration
section's warning is honored verbatim, and the QA fences it (below).

**Scope item 3 (QA):** `Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`
(36 declarations; zero errors, zero warnings; built explicitly), both
fixtures asymmetric and rational (no irrational Perron data anywhere):

- *Positive witness* `P = !![1,2;1,0]` (primitive, positive diagonal;
  `2 ≠ 1` refutes symmetry): the axiom instantiated and the Perron
  root **derived to be exactly 2** from the eigen-equation on the
  unknown existential witness (`x 1 * (r*r) = x 1 * (r+2)` with
  `x 1 > 0`, positivity killing the `−1` root), the Perron vector
  pinned to a positive multiple of the hand vector `(2,1)`, the
  simplicity clause cross-checked against the hand factorization
  (`charpoly P = (X + C 1) * (X - C 2)` by `det_fin_two`;
  `rootMultiplicity 2 = 1` by `rootMultiplicity_mul_X_sub_C_pow`), the
  complexified charpoly factored with roots exactly `{2, −1}`
  (`roots_mul` + `roots_X_sub_C`), and the **domination clause
  instantiated at both roots** — `|2| ≤ 2`, `|−1| ≤ 2`, the strict
  case of the primitive fixture.
- *The mandated imprimitive negative witness* `D = !![0,4;1,0]` (an
  asymmetric directed 2-cycle — zero diagonal, period 2; `4 ≠ 1`):
  `strict_dominance_refuted_QA` proves the strengthening
  "every eigenvalue other than the Perron root has strictly smaller
  modulus" **false** on `D` — the hand Perron pair `(2, (2,1))`
  satisfies the strengthened hypotheses, the hand eigenpair
  `(−2, (−2,1))` satisfies the eigen-equation, and `|−2| = 2 = r`. The
  refutation consumes no axiom (it targets the *strengthening*, not
  the axiom); meanwhile `perron_frobenius_D_QA` derives the axiom's
  own `r = 2` on the same fixture and `D_axiom_domination_QA`
  instantiates the domination clause at the peripheral root: `|−2| ≤
  2` *with equality* — the admitted statement's weaker conclusion is
  exactly what survives on imprimitive input.
- *Hand/axiom cross-checks:* `P_only_nonneg_eigenvalue_QA` and
  `D_only_nonneg_eigenvalue_QA` prove the only-eigenvalue clause **by
  hand** (eigen-equations + nonnegativity force `μ = 2`, killing the
  `−1`/`−2` roots), and `P_axiom_only_eigenvalue_on_hand_witness_QA`
  feeds the hand Perron eigenvector into the axiom's clause so axiom
  content and fixture content are independently established and
  cross-checked.
- `#print axioms`: the five axiom-consuming QA theorems list exactly
  `perron_frobenius` + the three standard axioms; the eleven hand
  theorems only the standard three.

**Scope items 4–5:** the Horn–Johnson source index gained the Theorem
8.4.4 row (this closes one of the coverage map's named-absent rows,
now updated), the topic map is the new `index/map/linear_algebra.md`
(README row added), and the axiom count records are updated (10). No
stationary-distribution or PageRank work, per item 5.

**Acceptance criteria check:** the statement matches 8.4.4 at the
scoped qualification level with no strict-dominance clause (criterion
1 ✓); both witnesses landed in this run, not as follow-ups
(criterion 2 ✓); the coverage-map row updated (criterion 3 ✓); the
scope decision was resolved 2026-08-19 and the admission happened in a
run directed at this proposal (criterion 4 ✓).

**Verification:** `lake env lean` on the module and QA — zero errors,
zero warnings each; explicit builds of both ✔; `#print axioms` as
above ✔; umbrella import added and **full `lake build` ✔ (2232 targets,
"Build completed successfully", zero errors, detached)**;
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1378/10/0**; `PerronFrobenius_QA` a new file
row at 36, the first LinearAlgebra-domain file).

**Pin-specific QA techniques (for future fixtures):** `open Polynomial`
(plain — name resolution) is what activates `X`/`C` on this pin;
`open scoped Polynomial` does nothing for them (they are defs, not
scoped notation). `fin_cases` leaves eta-expanded indices
(`(fun i => i) ⟨0, ⋯⟩`) that defeat positional `rw`; bridge with an
explicit `show` at the defeq literal goal. `ring` treats `C c` as an
atom, so `C`-numerals must be normalized first — this pin's
`Polynomial.C_mul` points *opposite* to modern Mathlib
(`C (a*b) = C a * C b`), `C_eq_natCast` does not match OfNat literals,
and there is no `C_2`; one-time helpers built from `C_add` + `C_1`
(e.g. `C 2 = 2` by `2 = 1 + 1`) are the robust route. Scalar `2 • x`
over `x : Fin 2 → ℝ` elaborates with `2 : ℕ` absent an annotation —
annotate `(2:ℝ) •` in statements. The applied `algebraMap ℝ ℂ` bridges
to `Complex.ofReal` under `rw` via `Complex.coe_algebraMap` (its LHS is
the *coerced* form), but `Polynomial.map`'s RingHom argument does not
match it — computing the mapped matrix's charpoly directly
(`det_fin_two` + `Matrix.map_apply`) avoids the trap.

**Open next step:** none within this proposal (its scope is complete).
The named follow-ons — irreducible stationary distributions, PageRank —
each need their own proposal, as this document has always said.
