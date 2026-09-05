# The Stationary Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run
`20260905T045658Z-run-1`, session `ses_f90206573ffepoH8ZpAC23ERiP`;
see the delivery record).

## Scope

The prior terminal handoff's named top target — "the audit method's
natural next targets by this run's confirmed survey numbers:
`Stationary` (4 transitive non-QA consumers, QA never audited — now
the top unaudited shelf by that metric)" — confirmed by this run's own
fresh reverse-import walk: **4 transitive non-QA consumers** (`Mixing`,
`Oversmoothing`, `DirectedMixing` directly; the closure adds the
derived `EmpiricalStationary` capstone). The shelf is
`Scaffold/Mathlib/GraphTheory/Stationary.lean`: 9 public theorems —
the row-sum identity, the normalized-Laplacian kernel vector `√deg`,
adjoint-walk stationarity of the degree vector, the detailed-balance
trio (degree-measure, stationary-measure, matrix symmetrizability),
the regular uniform-measure balance, and the two mass-conservation
statements (regular and irregular). Everything is proved — no axiom —
so this is a theorem-instantiation audit (no `-- @refutes` tags).

Its QA (`Stationary_QA.lean`, 259 lines, delivered 2026-08-22 with
`reversibility-and-heat-semigroup.md` Phase A) is pre-discipline:
positive witnesses at the three-vertex path and the single edge, plus
**one free-form negative witness** (`asym_detailed_balance_refuted_QA`
at the asymmetric `asymAdj2 = !![0, 2; 1, 0]]`, refuting a single
instance equation rather than a dropped-hypothesis statement shape)
— never reconciled into the fence discipline.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(nineteen precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger,
regular Cheeger, effective-resistance, electrical-flow, Foster,
sparsification-core, band-projector, Davis–Kahan core, normalized,
variational-transfer, resolvent, Perron–Frobenius, heat, and
random-walk).

## Step-0 findings: the priced fence list

Clause census: 9 theorems, 15 clause instances — `hA` on six
statements, `hd` on seven, `hdpos` on one, plus the hypothesis-free
`mulVec_one_eq_deg`. Thirteen priceable fences, one P4
truth-removable, one vacuous.

1. **`hA` of `normalizedLaplacian_mulVec_sqrtDeg_eq_zero` — P4
   truth-removable, strengthening deliverable.** The shelf proof never
   consumes symmetry: the kernel computation
   `(T A T) *ᵥ √deg = T *ᵥ (A *ᵥ (T *ᵥ √deg)) = T *ᵥ (A *ᵥ 1) =
   T *ᵥ deg = √deg` routes through `mulVec_one_eq_deg` (row sums) and
   the two `hd`-only cancellations. The strengthening — the statement
   with `hA` deleted — is priced as a proved QA companion
   (`normalizedLaplacian_mulVec_sqrtDeg_eq_zero_of_pos_deg`), making
   the P4 claim machine-checked rather than asserted.
2. **`hd` of the same statement — signed canceling-zero-degree row.**
   At genuinely-positive-degree input the junk never bites
   (`degreeInvSqrt` is genuine); at an *isolated* (nonnegative
   zero-degree) vertex the junk cooperates (`√0 = 0`, `0⁻¹ = 0`, and
   the vector entry `√deg i = 0` — inert). The genuine breaker is a
   symmetric row summing to zero through signed edges. Priced at the
   new fixture `stNegAdj = !![0, 1, −1; 1, 0, 0; −1, 0, 0]]` (Fin 3,
   symmetric, degrees `(0, 1, −1)`): the junk `√(−1) = 0`,
   `√0 = 0` collapses `degreeInvSqrt` to `diag(0, 1, 0)`, hence
   `T A T = 0` and `L_sym = 1`, while the kernel vector `√deg =
   (0, 1, 0)` survives on the positive vertex —
   `(L_sym *ᵥ √deg) 1 = 1 ≠ 0`. The same junk-√ collapse the
   normalized audit found at `nfNegEdge`, here killing the *kernel*
   statement through the vector entry rather than the matrix factor.
3. **`hA` of `walkTransitionMatrix_transpose_mulVec_deg`.** At the
   delivered `asymAdj2` (degrees `(2, 1)` positive — `hd` genuine):
   `Pᵀ = (D⁻¹ A)ᵀ = Aᵀ D⁻¹`, so `Pᵀ *ᵥ deg` computes **column** sums
   `(1, 2)` against the degree (row-sum) vector `(2, 1)` — the kill
   mechanism is exactly "row sums ≠ column sums on asymmetric input,"
   pinned at entry 0 (`1 ≠ 2`).
4. **`hd` of the same statement — signed canceling-zero-degree row,
   column-side kill.** `(Pᵀ *ᵥ deg) i = Σ_{j : deg j ≠ 0} A j i`
   (each nonzero-degree term cancels its inverse; zero-degree terms
   are junk-zeroed), so the statement fails exactly when some column
   sum over nonzero-degree rows differs from the row sum. At
   `stNegAdj`: `(Pᵀ *ᵥ deg) 1 = A 1 1 + A 2 1 = 0 ≠ 1 = deg 1` — the
   zero-degree vertex 0 contributes `A 0 1 = 1` to `deg 1` but is
   junk-zeroed from the adjoint product. Nonnegative zero-degree rows
   are inert (their adjacency is identically zero), so the fence needs
   the signed cancelation — the same "symmetric zero-degree rows are
   not inert once signs cancel" mechanism as clause 2, on the
   inversion side.
5. **`hA` of `walk_detailed_balance` — reconciles the delivered
   free-form witness.** `deg i * P i j = A i j` and
   `deg j * P j i = A j i` (the degree weight cancels the row factor),
   so balance is exactly symmetry of `A`. The dropped statement dies
   at `asymAdj2`, pair `(0,1)`: `2 ≠ 1`. The fence's proof consumes
   the delivered `asym_detailed_balance_refuted_QA` — the free-form
   witness is thereby reconciled into the fence discipline.
6. **`hd` of `walk_detailed_balance`.** `deg i * P i j = A i j`
   needs `deg i ≠ 0`; at a zero-degree vertex the junk zeroes the
   left side while the right stays genuine. At `stNegAdj`, pair
   `(0,1)`: `deg 0 * P 0 1 = 0 ≠ 1 = deg 1 * P 1 0`.
7. **`hA` of `walk_detailed_balance_measure`.** Same mechanism as
   clause 5 through the common volume division — at `asymAdj2` (vol
   `3`), pair `(0,1)`: `(2/3) ≠ (1/3)`.
8. **`hd` of `walk_detailed_balance_measure` — needs a
   volume-nonzero fixture.** At `stNegAdj` the volume is
   `0 + 1 + (−1) = 0` and *both* sides of the division junk-collapse
   to `0` — no kill. Priced at the new variant fixture
   `stVolAdj = !![0, 1, −1; 1, 0, 2; −1, 2, 0]]` (symmetric, degrees
   `(0, 3, 1)`, vol `4 ≠ 0`): pair `(0,1)`, left `0` (the junk-zeroed
   zero-degree side) against right `(3/4) · (1/3) = 1/4`.
9. **`hA` of `diagonal_deg_mul_walkTransitionMatrix_isSymm`.** The
   matrix packaging of clause 5: `(D * P) 0 1 = 2 ≠ 1 = (D * P) 1 0`
   at `asymAdj2`.
10. **`hd` of the same statement** — at `stVolAdj`:
    `(D * P) 0 1 = deg 0 * P 0 1 = 0 ≠ 1 = deg 1 * (1/3) * 3 = (D * P) 1 0`.
11. **`hA` of `transitionMatrix_detailed_balance_uniform`.** The
    regular cone's uniform balance is exactly `transitionMatrix`
    symmetry; the RandomWalk audit fenced the engine's own `hA`
    (2026-09-05), this is its consumer statement. At `asymAdj2`,
    `d = 1`, pair `(0,1)`: `(1/2) · 2 = 1 ≠ 1/2 = (1/2) · 1`.
12. **`hd` of `randomWalkLaplacian_mulVec_one_eq_zero`.** The regular
    mass-conservation consumer of `transitionMatrix_row_sum` (whose
    own clauses the RandomWalk audit fenced). Dropped-`hd` dies at the
    delivered `edgeAdj2` at the wrong claimed degree `d = 2`:
    `(L_rw *ᵥ 1) 0 = 1 − 2⁻¹ = 1/2 ≠ 0`.
13. **`hdpos` of the same statement — the `d = 0` junk corner** (the
    RandomWalk audit's finding, transferred to this consumer): at the
    genuinely `0`-regular zero matrix, `L_rw = 1 − 0⁻¹ • 0 = 1` and
    `(L_rw *ᵥ 1) 0 = 1 ≠ 0`.
14. **`hd` of `walkLaplacian_mulVec_one_eq_zero` — the irregular
    mass-conservation statement.** `(L_walk *ᵥ 1) i = 1 − (deg i)⁻¹
    Σ_j A i j` needs `deg i ≠ 0`; at a zero-degree vertex it is
    `1 − 0 = 1`. Priced at the plain zero matrix on `Fin 2`
    (`stZeroAdj`) — the mildest fixture: the walk Laplacian of an
    edgeless graph is the identity, which does not kill constants.
    (The `d = 0` corner of clause 13 is the same mechanism in regular
    dress.)

**Non-fenceables, with mechanisms:** `mulVec_one_eq_deg` carries no
hypotheses (necessity-of-no-hypotheses is not a priceable class);
clause 1's `hA` is P4 truth-removable with the strengthening
delivered (above).

**Strengthening companions (proved, five):** the symmetry-free kernel
statement (clause 1); stationarity and detailed balance at
`∀ i, deg A i ≠ 0` (the shelf proofs' own routes with
`inv_mul_cancel₀` re-keyed — clauses 3/5's positive halves); the
irregular mass conservation at `deg ≠ 0` (direct row-sum computation);
and the regular mass conservation at `d ≠ 0`, transferring the
RandomWalk audit's `transitionMatrix_row_sum_of_ne_zero` finding to
this consumer by a direct computation (no QA-to-QA import needed). The
stationary-measure and symmetrized twins inherit theirs compositionally
from detailed balance (recorded, not re-proved).

## Fixtures (three new, two delivered, all rational)

- `stNegAdj = !![0, 1, −1; 1, 0, 0; −1, 0, 0]]` — the signed
  canceling-zero-degree triangle (degrees `(0, 1, −1)`, vol `0`):
  kills the kernel `hd` (junk-√ collapse, entry 1), the stationarity
  `hd` (column-side junk-zeroing, entry 1), and the degree-measure
  balance `hd` (pair `(0,1)`).
- `stVolAdj = !![0, 1, −1; 1, 0, 2; −1, 2, 0]]` — the volume-nonzero
  variant (degrees `(0, 3, 1)`, vol `4`): kills the stationary-measure
  and symmetrized `hd` clauses (the vol-`0` fixture would
  junk-collapse both sides of the division).
- `stZeroAdj = 0` (Fin 2) — the genuinely `0`-regular zero matrix:
  kills the regular `hdpos` and the irregular `hd` mass-conservation
  clauses.
- `asymAdj2` (delivered) — kills all six fenced `hA` clauses
  (`hd` genuine: degrees `(2, 1)` positive).
- `edgeAdj2` (delivered) at the wrong claimed degree `d = 2` — kills
  the regular `hd` mass-conservation clause.

## Delivery record

DELIVERED at the full priced scope — QA-only, a pure insertion (631/0
in numstat) in `Stationary_QA.lean`'s new `AdversarialFences` section:
all thirteen hypothesis-form fences, the isolation companions
(`stNegAdj_not_deg_pos`, `stVolAdj_not_deg_pos`,
`edgeAdj2_not_two_regular`, plus the delivered `asymAdj2_deg_pos`
already carrying the kept-clause proof for the six `hA` fences), the
kill pins (the `degreeInvSqrt = diag(0,1,0)` junk-√ collapse and
`T A T = 0`; `(Pᵀ *ᵥ deg) 1 = 0` and `= 1` at the two triangles;
`(Pᵀ *ᵥ deg) 0 = 1` and the `P`-entry pins at `asymAdj2`; the vol
pins `0`/`4`/`3`; the wrong-degree and zero-matrix Laplacian entries),
and the five proved strengthening companions. 75 declarations (72
theorems + 3 fixture `def`s); QA 5422 → 5494 (+72 by the generator
metric). Zero axiom contact in the new declarations (`#print axioms`
via `wip/stfences_axcheck.lean` on all 75 — every one exactly
`propext, Classical.choice, Quot.sound`; no `-- @refutes` tags —
theorem instantiations of an all-proved shelf, nothing admitted
consumed; the 12-tag independence check unchanged and clean).

Technique findings recorded for future audits:

1. **The pricing's P4 call was confirmed by the machine.** The kernel
   statement's `hA` was priced truth-removable by reading the proof
   (no `hA` consumption anywhere in its text); the delivered
   strengthening compiles verbatim minus the hypothesis, upgrading
   the claim from "the proof does not seem to use it" to
   machine-checked. Read-then-confirm is cheap and worth it whenever a
   clause looks decorative.
2. **The eta-literal trap is now confirmed on Fin 3**: `fin_cases`
   produces `(fun i => i) ⟨0, ⋯⟩`-shaped indices that defeat literal
   entry lemmas; the `show`-coercion route (re-elaborating the goal
   with clean literals) worked everywhere here, matching the
   normalized audit's recorded idiom.
3. **Vector-level rewriting beats entry-level unfolding for `*ᵥ`
   identities.** The two mass-conservation strengthenings close by
   rewriting the three vector-level facts (`Matrix.sub_mulVec`,
   `Matrix.one_mulVec`, and a funext'd row-sum lemma) rather than
   unfolding `mulVec`/`dotProduct` under a sum — the entry-level route
   left an unsplit `(1 - P) i x` sum that simp could not finish.
4. **A fence statement must actually drop the clause.** The spike's
   first version of the uniform-balance fence kept `A.IsSymm` as a
   hypothesis of the negated statement — refuting nothing (and
   type-checking against a proof by contradiction of the *wrong*
   shape). Writing `¬ (∀ A d i j, …)` with the clause genuinely
   deleted, then instantiating, is the whole content of a
   single-hypothesis fence.

## Verification

Spike first (`wip/stfences_spike.lean` — the full 75-declaration
delivery, iterated to zero errors/zero warnings over four fix rounds,
all in recorded trap classes: the constant-row `vecHead/vecTail`
collapse on the zero rows of `stNegAdj` forcing the named-entry-pin
route, the eta-literal `show`-coercion, the `mul_diagonal`-before-
`diagonal_mul` ordering for right-diagonal products, and the
vector-level route of finding 3); `lake env lean` on the landed
module (zero errors, zero warnings); explicit `lake build
Scaffold.QA.SpectralGraph.Stationary_QA` ✔ (2192/2192, the only
warnings the pinned Mathlib's own upstream linter notes); the
75-declaration axiom audit above; **full `lake build` ✔ immediately
followed by `check_build_completeness.py` — 133 source files, 133
fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0
(4 current axioms, unchanged); `check_refutation_independence`
(12-tag clean — no tags touched); `check_public_reachability` clean
(63 repo modules); `check_citations` ("All axioms have proper
citations!"); `check_markdown_links` clean; `check_backlog_freshness`
clean (backlog reviewed-date already current at September 5);
scoreboard regenerated (**5494/4/0**) with the verification row;
map-freshness exit 0 after the 5422 → 5494 stats sync in both map
data tables and SVG regeneration (49 stations, no status change —
none owed: the audit's proposal is not a map station's cited source).
The landing verified as a pure insertion (631/0 in numstat, the
section inserted before `end SpectralGraphTheory.QA`).
