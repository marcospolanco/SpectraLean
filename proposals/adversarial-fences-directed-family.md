# The Directed Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run
`20260905T083058Z-run-1`, session `ses_f8f51ab63ffejbmt1S6crSM38S`;
see the delivery record).

## Scope

The prior terminal handoff's named next target — "`Directed` (3
transitive non-QA consumers — feeding `FunctionalCalculus`, `Magnetic`,
`Signed`; the last handoff-named unaudited shelf of the pair, a
proportionately small ~4-clause surface)" — confirmed by this run's
own fresh import walk: `Magnetic.lean` and `FunctionalCalculus.lean`
import `Directed` directly, `Signed.lean` via `Magnetic` — **3
transitive non-QA consumers**, the directed axis' degree/operator root.
The shelf is `Scaffold/Mathlib/GraphTheory/Directed.lean`: 12 public
declarations (3 defs — `outDeg`, `inDeg`,
`directedNormalizedLaplacian` — and 9 theorems). Everything on the
shelf is proved — no axiom — so this is a theorem-instantiation audit
(no `-- @refutes` tags; the fences refute dropped-hypothesis statement
shapes of proved theorems, consuming nothing admitted).

Its QA (`Directed_QA.lean`, 613 lines, delivered 2026-08-22) is
pre-discipline: rich positive pinning plus three free-form negative
witnesses (`dirA_outDeg_ne_inDeg`, `dirA_walk_not_isSymm`,
`dirA_Ldir_ne_normalizedLaplacian`, and the calibration
`dirB_not_quadForm_nonneg`), but zero fence sections and zero
per-clause hypothesis-necessity information. The conjugate — the
transfer route for every quadratic-form statement about `L_dir`, the
directed axis' one symmetric operator — carries a positivity clause
whose necessity has never been tested anywhere in the repository.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(twenty-one precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger, regular
Cheeger, effective-resistance, electrical-flow, Foster,
sparsification-core, band-projector, Davis–Kahan core, normalized,
variational-transfer, resolvent, Perron–Frobenius, heat, random-walk,
stationary, irreducible-stationary).

## Step-0 findings: the priced fence list

Clause census over the shelf's public surface — four theorems carry
exactly one hypothesis each; five carry none:

1. **`hA : A.IsSymm` of `inDeg_eq_outDeg_of_isSymm`.** A free-form
   witness exists (`dirA_outDeg_ne_inDeg`, `4 ≠ 2` at vertex 0) but was
   never reconciled into hypothesis form. Priced as a fence at the
   delivered `dirA`, vertex 0: the dropped statement
   `∀ A i, inDeg A i = outDeg A i` dies at `2 ≠ 4`. Isolation: the
   delivered `dirA_not_isSymm` (the dropped clause genuinely fails).
2. **`hA : A.IsSymm` of `inDeg_eq_deg_of_isSymm`.** No negative witness
   anywhere. Same fixture and vertex, different conclusion: the dropped
   statement `∀ A i, inDeg A i = deg A i` dies at `inDeg dirA 0 = 2`
   against `deg dirA 0 = 4` — composed, in the theorem's own proof
   order, from clause 1's kill and the definitional `outDeg_eq_deg`.
3. **`hA : A.IsSymm` of `directedNormalizedLaplacian_eq_normalizedLaplacian`
   (the Step-3 acceptance bar).** A free-form witness exists
   (`dirA_Ldir_ne_normalizedLaplacian`, the `−1 ≠ −3/2` entry
   separation at `(0,1)`) already in hypothesis-refuting shape;
   priced as a fence-form wrapper reconciling it into the discipline.
4. **`hd : ∀ i, 0 < deg A i` of
   `degreeSqrt_mul_directedNormalizedLaplacian_mul_degreeSqrt`.** No
   negative witness anywhere — the audit's genuinely new content.
   Priced at the new fixture `dzA = !![0, 1; 0, 0]]` (arc `0→1`,
   vertex 1 a pure sink: out-degrees `(1, 0)`): the junk
   `√0 · (√0)⁻¹ = 0 · 0⁻¹ = 0` collapse makes
   `degreeInvSqrt dzA = diag(1, 0)`, which zeroes *both* symmetrized
   halves (`S A S = S Aᵀ S = 0`), so `L_dir dzA = 1` and the left side
   `√D · L_dir · √D = diag(1, 0)` has `(0,1)` entry `0` — while the
   right side `D − ½(A + Aᵀ)` keeps the symmetrized arc, `(0,1)` entry
   `−½`. **The symmetrized adjacency survives on the right while the
   junk normalization erases it on the left**: `0 ≠ −(1/2)`.

**The strengthening question (the pricing's central finding).** The
random-walk audit found its `hdpos : 0 < d` clauses secretly
nonzeroness clauses (the `d⁻¹ · d = 1` route holds for every `d ≠ 0`,
negative included) and delivered `_of_ne_zero` strengthening
companions. Does the same weakening hold here — is
`hd : ∀ i, 0 < deg A i` replaceable by `∀ i, deg A i ≠ 0`?
**No.** The route here runs through `Real.sqrt`: the engine identity
`√d · (√d)⁻¹ = 1` holds exactly on `0 < d`; at every `d ≤ 0` the junk
`√d = 0` collapses the product to `0`. Priced at the new fixture
`dzNeg = !![-1, 0; 1, 0]]` (out-degrees `(−1, 1)`, genuinely `≠ 0` at
*every* vertex — the strengthened hypothesis set is genuinely
satisfied): `√(−1) = 0` junk zeroes row/column 0 of the
normalization, `L_dir dzNeg = 1`, and the left side `diag(0, 1)` has
`(0,1)` entry `0` against the right side's `−(1/2)` — the
nonzeroness-strengthened statement is refuted. **So the fence + this
refutation form an exact characterization in the opposite direction
from the random-walk twin: the clause is load-bearing on the whole
non-positive half-line, and no nonzeroness strengthening exists.**
This is the audit's headline discrimination — the walk twin's
`hdpos` was nonzeroness in disguise; the directed conjugate's `hd` is
genuinely positivity, and the `√` in the out-degree normalization is
exactly what makes the difference. A downstream consumer transferring
quadratic forms through the conjugate cannot trade the positivity
hypothesis for nonzeroness.

**Non-fenceable, with mechanism:** the five hypothesis-free theorems —
`outDeg_eq_deg`, `inDeg_eq_deg_transpose` (both `rfl` identities),
`sum_outDeg_eq_sum_inDeg` (handshaking by `Finset.sum_comm`),
`directedNormalizedLaplacian_apply` (the entry form),
`directedNormalizedLaplacian_isSymm` (the hypothesis-free symmetry)
— carry no clause to drop (necessity-of-no-hypotheses is not a
priceable class, per the random-walk audit's precedent). The
`variable` binders (`Fintype`, `DecidableEq`) are instance arguments,
not mathematical hypotheses.

**Screened:** the QA's positive witnesses stay (they pin the interface
at genuine fixtures); `dirA_walk_not_isSymm` is a *definitional*
calibration witness about the shelf's `Normalized`-side objects (not a
clause of any `Directed` theorem — the shelf deliberately states no
walk-symmetry theorem), and `dirB_not_quadForm_nonneg` is a
calibration witness about the `L_dir` operator itself (the shelf
deliberately states no PSD theorem) — both outside the clause surface,
both kept as delivered.

## Fixtures (two new, one delivered, all rational)

- `dirA` (delivered, reused) — the three `hA` breakers: the Fin 3
  genuinely-directed network, asymmetric with positive out-degrees.
- `dzA = !![0, 1; 0, 0]]` — the `hd` breaker: arc `0→1`, vertex 1 a
  pure sink (`deg = (1, 0)`), nonnegative, asymmetric; the junk
  `√0 · (√0)⁻¹` corner where the conjugate's two sides separate.
- `dzNeg = !![-1, 0; 1, 0]]` — the strengthening breaker: signed
  diagonal, out-degrees `(−1, 1)` — genuinely `≠ 0` at every vertex,
  genuinely failing `0 < deg` at vertex 0; the junk `√(−1) = 0`
  half-line corner refuting the nonzeroness-strengthened statement.

## Acceptance bar

- Every priceable clause (all four) carries a hypothesis-form fence in
  a new `AdversarialFences` section of `Directed_QA.lean`, each killed
  at a named fixture with the dropped clause's genuine failure pinned
  (isolation) and every kept clause genuine.
- The two pre-existing free-form witnesses used by fences 1 and 3 are
  explicitly reconciled (the fence wrappers cite them; the section
  header records the reconciliation).
- The strengthening question is settled mechanically: the
  nonzeroness-strengthened conjugate is *refuted* at `dzNeg` (no
  `_of_ne_zero` companion exists — recorded as the finding, not
  skipped).
- QA-only: no axiom touched, no public statement changed, pure
  insertion; `#print axioms` on every new declaration reads exactly
  `propext, Classical.choice, Quot.sound`; no `-- @refutes` tags.
- Full verification ladder after the spike; records ladder updated
  (scoreboard, radar QA row, map tables + SVG, index map, backlog
  note, this file's delivery record).

## Delivery record

DELIVERED at the full priced scope — QA-only, a pure insertion
(301/0 in numstat on `Directed_QA.lean`, plus the header-note
paragraph) in the new `AdversarialFences` section before
`end SpectralGraphTheory.QA`: all four hypothesis-form fences
(`inDeg_eq_outDeg_of_isSymm_hA_fence_QA`,
`inDeg_eq_deg_of_isSymm_hA_fence_QA`,
`directedNormalizedLaplacian_eq_normalizedLaplacian_hA_fence_QA`,
`degreeSqrt_mul_directedNormalizedLaplacian_mul_degreeSqrt_hd_fence_QA`)
plus the strengthening refutation
(`degreeSqrt_mul_directedNormalizedLaplacian_mul_degreeSqrt_ne_zero_refuted_QA`),
the isolation companions (`dzA_not_hd`, `dzNeg_not_hd`,
`dzNeg_deg_ne_zero` as the kept-strengthened-clause proof), and the
mechanism pins (the degree/sqrt/entry pins at both new fixtures, the
`smul_halves_eq_zero` collapse lemmas, the `Ldir_eq_one` collapses,
and the two-sided conjugate separations `conjLHS`/`conjRHS` at
`(0,1)`). 34 declarations (32 theorems + 2 fixture `def`s `dzA`,
`dzNeg`); QA 5728 → 5760 (+32 by the generator metric). Zero axiom
contact in the new declarations (`#print axioms` via
`wip/directfences_axcheck.lean` on all 34 — every one exactly
`propext, Classical.choice, Quot.sound`; no `-- @refutes` tags —
theorem instantiations of an all-proved shelf, nothing admitted
consumed; the 12-tag independence check unchanged and clean).

Technique findings recorded for future audits:

1. **`rw` lists stop at the first failure.** A rewrite chain
   `rw [a, b, add_zero, sub_zero]` fails at `add_zero` (already
   consumed by the earlier `smul_zero` collapse) and never reaches
   `sub_zero` — the error reports the *later* missing lemma while the
   *earlier* one is the culprit. Read `1 - 0 = 1` in the error goal
   as "one more rewrite needed," not "wrong route."
2. **Pins cannot fire under a variable index.** A statement of the
   form `f M i j = if …` with variable `i j` cannot be proved by
   `simp` with concrete-index pins (`√(deg dzA 0) = 1` does not match
   `√(deg dzA i)`); either `fin_cases` both indices first (so the
   pins match the literals, the delivered `dirA_conjLHS_zero_one`
   idiom) or restructure to consume the pins where the indices are
   already literals. The `fin_cases`-produced `⟨0, ⋯⟩` literals *do*
   match statement-literal `0 : Fin 2` in `simp` sets — reducible
   defeq — but only after the case split.
3. **`fin_cases` leaves eta-literals that `rw` cannot match but
   `show` absorbs** (the stationary audit's recorded class, confirmed
   again at `dzNeg_deg_ne_zero`): `deg dzNeg ((fun i => i) ⟨0, ⋯⟩)`
   needs `show deg dzNeg 0 ≠ 0` before the pin rewrites.
4. **`Real.sqrt_eq_zero_of_nonpos` is the half-line junk pin** —
   `√(-1) = 0` in one `rw` + `norm_num`, the negative-degree analogue
   of `Real.sqrt_zero`, and the exact lemma any future audit of a
   `√`-routed normalization at signed fixtures needs.

## Verification

Spike first (`wip/directfences_spike.lean` — the full 34-declaration
delivery, iterated to zero errors/zero warnings in one fix round, all
failures in recorded trap classes: the `rw`-list first-failure trap,
the variable-index pin trap, and the eta-literal `show`-coercion);
`lake env lean` on the landed module (exit 0, no output — zero
errors, zero warnings); explicit `lake build
Scaffold.QA.SpectralGraph.Directed_QA` ✔ (2193/2193, the only
warning the pinned Mathlib's own upstream linter note in
`Stationary.lean`, pre-existing); the 34-declaration axiom audit
above; **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh
artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4
current axioms, unchanged); `check_refutation_independence` (12-tag
clean — no tags touched); `check_public_reachability` clean (63 repo
modules); `check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean
(backlog reviewed-date already current at September 5); scoreboard
regenerated (**5760/4/0**) with the verification row; map-freshness
exit 0 after the 5728 → 5760 stats sync in both map data tables and
SVG regeneration (49 stations, no status change — none owed: the
audit's proposal is not a map station's cited source). The landing
verified as a pure insertion (301/0 in numstat). Records updated:
this file (COMPLETE + delivery record), `proposals/README.md` (new
Delivered row), README (5760), the radar (QA row synced, held 4.5 —
with the prior run's mangled splice in that row's history text
repaired in the same edit), `index/map/spectral_graph.md` (the audit
paragraph in the Directed section), the backlog item-2
falsification-surface note, the scoreboard verification row, both map
data tables + regenerated SVG, the QA file's header note, the
execution plan, and the activity log. Nothing committed; the prior
runs' uncommitted deliveries preserved.
