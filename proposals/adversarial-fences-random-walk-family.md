# The Random-Walk Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run
`20260905T044531Z-run-1`, session `ses_f90206573ffepoH8ZpAC23ERiP`;
see the delivery record).

## Scope

The prior terminal handoff's named top target — "the audit method's
natural next targets, by this run's own survey numbers: `RandomWalk`
(5 transitive non-QA consumers, its QA never audited), then
`Stationary` (4) and `IrreducibleStationary`/`Directed` (3 each)" —
confirmed by this run's own independent reverse-import walk: **5
transitive non-QA consumers** (`Stationary` directly; the closure adds
`Mixing`, `Oversmoothing`, `DirectedMixing`, and the derived
`EmpiricalStationary` capstone). The shelf is
`Scaffold/Mathlib/GraphTheory/RandomWalk.lean`: 7 public declarations
(the transition matrix `transitionMatrix = d⁻¹ • A`, the walk
Laplacian `randomWalkLaplacian = 1 - P`, the symmetry pair, the
row-stochasticity theorem, the `rfl` bridge to the Cheeger
normalization, and the scaling bridge to the combinatorial Laplacian).
Everything on the shelf is proved — no axiom — so this is a
theorem-instantiation audit (no `-- @refutes` tags; the fences refute
dropped-hypothesis statement shapes of proved theorems, consuming
nothing admitted).

Its QA (`RandomWalk_QA.lean`, 76 lines) is fully pre-discipline: one
nonnegative fixture (`edgeAdj`, the single edge on `Fin 2`), six
positive-witness theorems, zero negative witnesses, zero fence
sections. `Stationary.lean` — the direct consumer — routes every
walk-mixing interface through this shelf's two hypothesis-bearing
theorem pairs: `randomWalkLaplacian_mulVec_one_eq_zero` (conservation
of mass) consumes `transitionMatrix_row_sum`, and
`transitionMatrix_detailed_balance_uniform` (reversibility at the
uniform measure) consumes `transitionMatrix_symmetric`. A clause that
is not load-bearing here is interface surface the mixing chain does
not need; a clause that *is* load-bearing gets a machine-checked
witness that it cannot be dropped silently.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(eighteen precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger,
regular Cheeger, effective-resistance, electrical-flow, Foster,
sparsification-core, band-projector, Davis–Kahan core, normalized,
variational-transfer, resolvent, Perron–Frobenius, and heat).

## Step-0 findings: the priced fence list

Clause census over the shelf's public surface — five theorems carry
hypotheses, six clauses total across four clause shapes; one theorem
carries none:

1. **`hA : A.IsSymm` of `transitionMatrix_symmetric`.** No negative
   witness anywhere in the repository (the QA's only fixture is
   symmetric). Priced at the new fixture `rwAsymAdj = !![0, 2; 1, 0]]`
   (Fin 2, the asymmetric edge pair): at `d = 1` the transition matrix
   is the adjacency matrix itself (`1⁻¹ • A = A`), so the dropped
   statement dies at the entry pair `(0,1) = 2 ≠ 1 = (1,0)`.
   **Pricing finding (junk-rescue corner):** at `d = 0` the dropped
   statement is *true* — the junk scalar `0⁻¹ = 0` collapses
   `transitionMatrix A 0 = 0`, and the zero matrix is symmetric for
   every `A`. So the unconditional `(transitionMatrix A d).IsSymm`
   fails exactly when `d ≠ 0` ∧ `A` asymmetric; the corner is priced
   as a pinned companion (`transitionMatrix rwAsymAdj 0 = 0`,
   symmetric), recording where junk rescues the dropped statement
   rather than refuting it.
2. **`hd : ∀ i, deg A i = d` of `transitionMatrix_row_sum`.** No
   negative witness. Priced at the delivered `edgeAdj` (genuinely
   `1`-regular) with the *wrong claimed degree* `d = 2`: every row of
   `2⁻¹ • edgeAdj` sums to `2⁻¹ · 1 = 1/2 ≠ 1`. The kept `hdpos : 0 < 2`
   is genuine; the dropped clause genuinely fails (`deg edgeAdj i = 1`
   pinned). No junk anywhere in the kill — pure wrong-constant
   arithmetic.
3. **`hdpos : 0 < d` of `transitionMatrix_row_sum`.** No negative
   witness. **Pricing finding: `d = 0` is the only failure corner.**
   At every genuinely `d`-regular fixture with `d ≠ 0` — including
   *negative* degrees — the dropped statement is true by the same
   algebra the shelf proof uses (`∑ j, d⁻¹ * A i j = d⁻¹ * deg A i =
   d⁻¹ * d = 1`). The only corner where the hypothesis set stays
   satisfiable while the conclusion fails is `d = 0`: the junk
   `0⁻¹ = 0` makes the transition matrix the zero matrix and the row
   sum `0 ≠ 1`. Priced at the new fixture `rwZeroAdj = 0` (the Fin 2
   zero matrix, genuinely `0`-regular: `deg 0 i = ∑ j, 0 = 0`): the
   kept `hd` is genuine, `0 < 0` fails genuinely, and the kill is the
   junk-collapse row sum `0 ≠ 1`. This is the same shape as the
   resolvent audit's headline ("the empty corner is the only `hc`
   failure corner") and the definitional content is worth pinning:
   *the transition matrix of a `0`-regular graph is the zero matrix,
   not a stochastic matrix* — the row-sum interface a Markov consumer
   needs exists only off the `d = 0` corner. The positive half is
   priced as a **proved strengthening companion**
   (`transitionMatrix_row_sum_of_ne_zero`: `d ≠ 0` suffices), making
   the fence+strengthening pair an exact characterization: the dropped
   statement is false precisely via `d = 0`.
4. **`hA : A.IsSymm` of `randomWalkLaplacian_symmetric`.** Same clause
   shape and same fixture as clause 1, but a *different conclusion* —
   `L_rw = 1 - P` inherits the asymmetry through the subtraction (at
   `d = 1`: entry `(0,1)` is `0 - 2 = -2 ≠ -1 = 0 - 1`), so the
   dropped statement dies independently of clause 1's kill. The
   `d = 0` junk-rescue corner pin covers this twin as well
   (`randomWalkLaplacian rwAsymAdj 0 = 1 - 0`, symmetric).
5. **`hd : ∀ i, deg A i = d` of `randomWalkLaplacian_eq_smul_laplacian`.**
   No negative witness. Priced at the delivered `edgeAdj` with claimed
   `d = 2`: the two sides separate at the `(0,0)` entry — the walk
   Laplacian's diagonal is `1 - 2⁻¹ · 0 = 1` while the scaled
   combinatorial Laplacian's is `2⁻¹ · 1 = 1/2` — a `2×` separation,
   `1 ≠ 1/2`. Kept `0 < 2` genuine; dropped clause genuinely fails
   (`edgeAdj` is not `2`-regular).
6. **`hdpos : 0 < d` of `randomWalkLaplacian_eq_smul_laplacian`.** No
   negative witness. Same pricing finding as clause 3: at `d = 0` on
   `rwZeroAdj` the identity's two sides separate maximally —
   `L_rw 0 0 = 1 - 0⁻¹ · 0 = 1` against `0⁻¹ • laplacian 0 = 0` —
   while for every genuinely `d`-regular fixture with `d ≠ 0`
   (negative degrees included) the dropped statement is true by
   `d⁻¹ · d = 1` on the diagonal and homogeneity off it. Priced at
   `rwZeroAdj` with the kept `hd` genuine, plus the proved
   strengthening companion
   (`randomWalkLaplacian_eq_smul_laplacian_of_ne_zero`).

**Non-fenceable, with mechanism:** the remaining public theorem,
`randomWalkLaplacian_eq_regularNormalizedLaplacian`, carries *no
mathematical hypotheses at all* — it is the `rfl` observation that the
walk and Cheeger normalizations coincide definitionally — so there is
no clause to drop (necessity-of-no-hypotheses is not a priceable
class). The `variable` binders (`Fintype`, `DecidableEq`) are instance
arguments, not mathematical hypotheses. Conclusion strengthening is
not priceable per the Perron–Frobenius audit's precedent (a weaker
conclusion is not false).

**Screened:** the QA's six positive witnesses stay (they pin the
interface at the genuine edge fixture); no free-form negative
witnesses exist to reconcile (this file has none — that is the gap).

## Fixtures (two new, one delivered, all rational)

- `rwAsymAdj = !![0, 2; 1, 0]]` — the `hA` breaker (clauses 1, 4):
  asymmetric with both off-diagonal entries nonzero, killed at `d = 1`
  where `1⁻¹ • A = A`; the `d = 0` junk-rescue corner pinned
  alongside.
- `edgeAdj` (delivered, reused at the wrong claimed degree) — the `hd`
  breaker (clauses 2, 5): genuinely `1`-regular, nonnegative,
  symmetric; every kept clause except `hd` genuine at `d = 2`.
- `rwZeroAdj = 0` — the `hdpos` breaker (clauses 3, 6): the Fin 2 zero
  matrix, genuinely `0`-regular; the junk `0⁻¹ = 0` corner where both
  `hdpos`-dropped statements fail and only they fail.

## Delivery record

DELIVERED at the full priced scope — QA-only, a pure insertion
(273/0 in numstat) in `RandomWalk_QA.lean`'s new `AdversarialFences`
section:
all six hypothesis-form fences, the isolation companions
(`rwAsymAdj_not_isSymm`, `rwZeroAdj_deg` as the kept-clause proof,
`edgeAdj_not_two_regular`), the kill pins
(`edgeAdj_transitionMatrix_row_sum_two = 1/2`,
`edgeAdj_randomWalkLaplacian_two_00 = 1` vs
`edgeAdj_smul_laplacian_two_00 = 1/2`,
`rwZeroAdj_transitionMatrix_row_sum_zero = 0`), the junk-corner pins
(`rwAsymAdj_transitionMatrix_zero_eq_zero` with both `d = 0`
junk-rescue symmetry pins; `rwZeroAdj_transitionMatrix_zero_eq_zero`
with the `rwZeroAdj_laplacian_apply = 0` pin), and the two proved
strengthening companions `transitionMatrix_row_sum_of_ne_zero` and
`randomWalkLaplacian_eq_smul_laplacian_of_ne_zero`. 29 declarations
(27 theorems + 2 fixture `def`s); QA 5395 → 5422 (+27 by the generator
metric). Zero axiom contact in the new declarations (`#print axioms`
via `wip/rwfences_axcheck.lean` on all 29 — every one exactly
`propext, Classical.choice, Quot.sound`; no `-- @refutes` tags —
theorem instantiations of an all-proved shelf, nothing admitted
consumed; the 12-tag independence check unchanged and clean).

Technique findings recorded for future audits:

1. **`field_simp` needs no strictness.** Both strengthening
   companions close by the shelf proofs' own routes with `0 < d`
   replaced by `d ≠ 0` — the row-sum proof is verbatim modulo
   `inv_mul_cancel₀`'s argument, and the bridge proof's `field_simp`
   picks the nonzero hypothesis up from context without change. When a
   pricing analysis says a strictness clause is really a nonzeroness
   clause, the strengthening is usually a one-token edit away from the
   original proof, not a new proof.
2. **Bare numeric inverses in statement position elaborate against
   `ℕ`.** `(2⁻¹ • laplacian edgeAdj) 0 0 = 1/2` fails to elaborate
   (`failed to synthesize Inv ℕ`) — the `•`'s scalar elaborates before
   the expected type propagates. Ascribe: `((2:ℝ)⁻¹ • …)`. The same
   goal then needs `inv_eq_one_div` before `norm_num`, which does not
   evaluate `↑2⁻¹` directly (it normalizes `/`, not raw numeral
   inverses) — the resolvent audit's numeric-literal trap class, now
   with the inverse variant recorded.
3. **`open ... in` scopes one command only** — an axcheck file's
   `#print axioms` list needs a bare `open` on its own line, or every
   name after the first fails to resolve at root.

## Verification

Spike first (`wip/rwfences_spike.lean` — the full 29-declaration
delivery, iterated to zero errors/zero warnings; the three fix rounds
were all in recorded trap classes: the `Matrix.` namespace prefix for
`isSymm_one` under `open scoped Matrix`, fixture-name unfolding in
`simp` sets, the `Inv ℕ` literal trap of finding 2, and `inv_eq_one_div`
before `norm_num`); `lake env lean` on the landed module (zero errors,
zero warnings); explicit `lake build
Scaffold.QA.SpectralGraph.RandomWalk_QA` ✔ (2190/2190, the only
warnings the pinned Mathlib's own upstream linter notes); the
29-declaration axiom audit above; **full `lake build` ✔ immediately
followed by `check_build_completeness.py` — 133 source files, 133
fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0
(4 current axioms, unchanged); `check_refutation_independence`
(12-tag clean — no tags touched); `check_public_reachability` clean
(63 repo modules); `check_citations` ("All axioms have proper
citations!"); `check_markdown_links` clean; `check_backlog_freshness`
clean (backlog reviewed-date already current at September 5);
scoreboard regenerated (**5422/4/0**) with the verification row;
map-freshness exit 0 after the 5395 → 5422 stats sync in both map
data tables and SVG regeneration (49 stations, no status change —
none owed: the audit's proposal is not a map station's cited source).
The landing verified as a pure insertion (273/0 in numstat, the
section inserted before `end SpectralGraphTheory.QA`).
