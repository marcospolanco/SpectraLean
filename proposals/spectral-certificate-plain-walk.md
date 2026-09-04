# The Spectral Certificate for the Plain Walk

**Status:** COMPLETE (delivered 2026-09-03, run `20260903T211920Z-run-1`, session `ses_f96e42945ffexR4Z56PmINSMcE`)  
**Added:** 2026-09-03  
**Axis:** 5 (reusable SGT QA and bridge interfaces) / the mixing program's plain family

## The gap

The plain walk's χ²/TV/entrywise ceiling family
(`chiSquareDistance_le_of_connected`,
`walkDistribution_tvDistance_le_of_connected`,
`walkDistribution_sub_stationaryVec_abs_le`,
`walkDistribution_sub_stationaryVec_le_of_depth`) quantifies over a
caller-supplied rate certificate: `r` with `|1 − μ| ≤ r` for every
nonzero normalized-Laplacian eigenvalue `μ`. On bipartite graphs that
hypothesis set is provably unsatisfiable (`λ_max = 2` mode; fenced at
`path_plain_cert_fenced_QA` and `k2` QA), and the lazy program was
delivered precisely to repair that class — its intrinsic rate
`1 − λ₂/2` needs no certificate, and the lazy entrywise ceiling
(`lazyWalkDistribution_sub_stationaryVec_abs_le`) and χ² headline
(`lazyChiSquareDistance_le_of_connected`) instantiate under
connectivity alone.

On the **complementary class — connected non-bipartite graphs — the
plain family still has no certificate supplier.** The Doeblin/primitivity
route (`walkDistribution_tvDistance_le_of_pos_power`) gives a TV rate
there, but (a) typically loose, and (b) it does not serve the χ²-level
or entrywise ceilings, whose `hrate` interface it does not match. The
plain oversmoothing/message-passing depth ceiling — the non-lazy walk
that message passing actually is — remains caller-opaque on exactly
the class where the plain walk mixes.

This is the standing handoff's named third frontier ("the spectral
certificate route for the plain family — still without a consumer that
the delivered rate does not already serve"). **Consumer gate
discharge:** the named consumer is the plain family's entrywise
oversmoothing ceiling (`Oversmoothing.lean`'s
`walkDistribution_sub_stationaryVec_abs_le` and its depth form) — the
same consumer class the lazy intrinsic rate's delivery named on the
bipartite side; the χ²/TV rate family joins for free off the same
certificate.

## The mathematical content

**The strict signless bound.** On connected symmetric nonnegative
positive-degree input carrying an odd closed walk in the support graph
(the shelf's honest non-bipartite interface — `Odd p.length`,
statement-identical to `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk`'s),
every normalized-Laplacian eigenvalue is `< 2`:

- `μ = 2` with unit eigenvector `v` gives `quadForm (2·1 − L_sym) v = 0`;
- the delivered congruence
  `quadForm_two_sub_normalizedLaplacian_eq` turns this into
  `uᵀ(D + A)u = 0` at `u = D^{-1/2} *ᵥ v`, and the delivered signless
  SOS `quadForm_degreeMatrix_add_eq_half_sum` into
  `∑ i j, A i j (u i + u j)² = 0`;
- nonnegativity forces `u i = −u j` on every support edge (an
  edge-flipping potential);
- the odd closed walk forces `u w = −u w = 0` at its base vertex (walk
  flip-propagation, a `SimpleGraph.Walk` induction);
- connectivity propagates `u = 0` to every vertex (|u| is constant
  along support edges), while `u ≠ 0` because
  `√D *ᵥ u = v` is a unit vector. Contradiction.

This is the classical "bipartite ⟺ `λ_max = 2`" dichotomy's strict
half at the exact interface the primitivity supplier already uses —
no `SimpleGraph.Bipartite` needed (still absent from the pin).

**The certificate.** With `λ₂ := secondEval (L_sym)` and
`λ_max := evals (L_sym) ⟨last⟩`, set `r := max (1 − λ₂) (λ_max − 1)`:

- `0 < λ₂` by the delivered connectivity transfer
  (`secondEval_normalizedLaplacian_pos_of_connected`);
- `λ_max < 2` by the new engine (through `evals_mem_eigvalOf`);
- every nonzero mode satisfies `λ₂ ≤ μ ≤ λ_max` (the delivered
  below-gap plumbing
  `secondEval_le_eigvalOf_normalizedLaplacian_of_ne_zero` plus
  `eigvalOf_le_evals_last`), hence `|1 − μ| ≤ r`, hence `r < 1`.

Two display forms: the `∃ r < 1` certificate (consumable by the whole
existing `hrate`-shaped family) and the `∃ r ∈ (0,1)` inflation variant
— needed because `r = 0` is an honest corner: the loop-weight-one
triangle (`A = J`) has spectrum `{0, 1, 1}` and its walk mixes *exactly*
in one step, so the computed certificate is `0` and depth-form log
thresholds (which divide by `log (1/r)`) must inflate it.

**The joins.** `chiSquareDistance_le_of_connected_of_odd_walk` (χ² at
the computed `max`-rate display, mirroring
`lazyChiSquareDistance_le_of_connected`'s `(1 − λ₂/2)` display), its TV
shadow, and the consumer join
`walkDistribution_sub_stationaryVec_abs_le_of_odd_walk` (entrywise
plain ceiling at the computed rate — no caller certificate).

## QA obligations (fence discipline)

- **Triangle certificate pin**: `r = 1/2` exactly — both `max` branches
  attain (`λ₂ = λ_max = 3/2`, from the existing `tri_eigvalOf_cases`
  trace/sortedness route); the χ² join meets the pinned exact
  attainment `χ²(1) = 1/2`.
- **Looped triangle**: the `r = 0` corner as a real witness (spectrum
  `{0,1,1}` by the eigen-equation route, one-step exact mixing,
  bound attained at `0 = 0`), plus the `(0,1)` inflation instantiated —
  also exercising the loops-are-not-support-edges subtlety on weighted
  input.
- **C₄ unsatisfiability fence**: the alternating mode's `eigvalOf = 2`
  witness (via `exists_eigvalOf_eq_of_mulVec_eq_smul`) forbids every
  `r < 1`; the flip-propagation lemma doubles as the isolation
  companion's every-closed-walk-even mechanism.
- **Strict engine `hnn` fence**: a negative-diagonal triangle (degrees
  positive, support graph the honest triangle, odd walk genuine) whose
  `2·1 − L_sym` quadratic form goes negative — `λ_max > 2` through
  `evals_first_mul_dotProduct_le_quadForm` and the eigenvector shift.
- **Strict engine `hconn` fence**: triangle ⊕ K₂ on `Fin 5` — the odd
  walk genuine in the triangle block, the K₂ block's `μ = 2` mode
  surviving it (block-entry computation), connectivity exactly the
  failure. *If this fixture exceeds a single run's budget it is
  recorded here as a priced follow-on with this mechanism — not
  silently dropped.*

## Zero axiom contact

Everything composes proved shelf theorems only; `#print axioms` audits
via a `wip/` spike are part of the delivery, with the standard three
(`propext, Classical.choice, Quot.sound`) expected on every audited
declaration.

## Step 0 verdict (route decisions, made before stating)

- The engine is stated per-`eigvalOf` (value-level), not through the
  sorted spectrum — the `hrate` interface it feeds is per-`eigvalOf`.
- The certificate carries `hcard : 2 ≤ Fintype.card V` explicitly,
  the `secondEval` idiom (`lambda2`/`secondEval` already carry it); the
  `card = 1` corner has no odd closed walk and no mixing content.
- The certificate's display is the `max` form, not the `sup'`-over-modes
  packaging — `chiSquareDistance_le_of_connected`'s own docstring
  records the `sup'` packaging as "a consumer's business", and this
  delivery is that consumer, choosing the two-branch `max` because both
  branches are separately pinned in QA.


## Delivery record (2026-09-03)

DELIVERED in one run — zero axiom contact (count stays 4; `#print
axioms` via `wip/speccert_axcheck.lean` on all 84 audited declarations
— 9 shelf + 75 QA, fixtures included — every one exactly `propext,
Classical.choice, Quot.sound`; no `-- @refutes` tags, nothing admitted
is consumed). QA 4336 → 4411 (+75 by the generator metric; the 84
declarations include 8 fixture/walk `def`s and the audited shelf).

**Shelf** (`Mixing.lean`'s new "The spectral certificate: intrinsic
rate on non-bipartite input" section, placed between the signless
engine and the lazy decay engine; `Oversmoothing.lean`'s consumer):

- `walk_eq_neg_one_pow_length_mul_of_forall_adj` — the flip-propagation
  lemma (a sign-flipping potential along edges flips along walks,
  `u b = (−1)^{|p|}·u a`), stated at the pure `SimpleGraph` level; the
  engine's parity mechanism, doubling in QA as the every-closed-walk-even
  bipartiteness witness at `C₄`.
- **`eigvalOf_normalizedLaplacian_lt_two_of_odd_walk`** — the strict
  signless engine: connected support graph + an odd closed walk ⟹ every
  normalized-Laplacian eigenvalue is `< 2`. Route: `μ = 2` at a unit
  eigenvector makes `uᵀ(D+A)u = 0` at the unstretched conjugate (the
  delivered congruence + SOS), every support edge forces `u i = −u j`,
  the odd walk forces `u w = 0`, connectivity propagates `u = 0` —
  contradicting `√D *ᵥ u = v` unit. The classical bipartite-dichotomy
  strict half at the primitivity supplier's exact interface
  (`Odd p.length`).
- `evals_normalizedLaplacian_lt_two_of_odd_walk` (sorted form),
  `abs_one_sub_eigvalOf_le_max` (the workhorse: `|1 − μ| ≤ max (1 − λ₂)
  (λ_max − 1)` for every nonzero mode — PSD + below-gap + last-entry
  domination; stated unconditionally, contractive only on the odd-walk
  class), **`exists_lt_one_rate_of_odd_walk`** (the `∃ r < 1`
  certificate: `0 < λ₂` by the connectivity transfer, `λ_max < 2` by the
  engine), `exists_pos_lt_one_rate_of_odd_walk` (the `(0,1)` inflation
  via `(max r 0 + 1)/2` — needed because `r = 0` is an honest corner).
- **`chiSquareDistance_le_max_rate`** and
  `walkDistribution_tvDistance_le_max_rate` — the plain family's
  display twins (the lazy family's intrinsic-rate displays mirrored:
  the plain walk's factors are two-sided in the spectrum, so the
  computed rate is the `max`, unconditionally true, saturating at `1`
  on bipartite input where the certificate theorem is what makes it
  contractive); **`walkDistribution_sub_stationaryVec_abs_le_max_rate`**
  in `Oversmoothing.lean` — the named consumer, the entrywise plain
  ceiling with no caller certificate (the max-rate's nonnegativity
  itself derived: both branches negative would force
  `λ₂ > 1 > λ_max ≥ λ₂`).

**QA** (`Mixing_QA.lean`'s `SpectralCertificate` section, +75): the
triangle's sorted-spectrum pins `evals ⟨1⟩ = evals ⟨2⟩ = 3/2` (cases +
trace + sortedness) giving **the certificate pin `r = 1/2` exact —
both max branches attained**; the max-rate theorem instance and its
**exact attainment** `bound = χ²(1) = 1/2`; the looped triangle
`A = J₃` fixture — **the honest `r = 0` corner**: eigen cases `{0, 1}`
by the eigen-equation route, trace `2`, sorted pins `evals ⟨1⟩ =
evals ⟨2⟩ = 1`, certificate `= 0`, the one-step law exactly stationary
(`∑`-collapse through `sum_walkDistribution`), `χ²(1, x) = 0` attained,
the `(0,1)`-certificate instantiated — and the loops-are-not-edges
subtlety exercised (support graph = the plain triangle); the **C₄
unsatisfiability fence** (the alternating mode's `eigvalOf = 2` via
`exists_eigvalOf_eq_of_mulVec_eq_smul` forbids every `r < 1`) with
isolation (connected, nonnegative, positive degrees genuine; no odd
closed walk exists — `c4_closed_walk_even` by the flip lemma at the
parity function); the strict engine's **`hnn` fence** at
`negDiagTriAdj = !![−1,1,1;1,0,1;1,1,0]]` (degrees `(1,2,2)`, support
triangle, genuine odd walk; the signless form `= −6 < 0` at
`(3,−1,−1)`, `evals_first_mul_dotProduct_le_quadForm` + the
eigenvector shift giving an eigenvalue `> 2`); and its **`hconn`
fence** at `triK2Adj` = triangle ⊕ `K₂` on `Fin 5` (walk-stays-in-block
isolation, the `K₂` block's alternating `μ = 2` mode surviving the
genuine triangle odd walk — connectivity exactly the failure). The
`Fin 5` fixture feared heaviest in the opening record landed in budget.

**Technique findings** (six): (1) the auto-bound-implicit trap — a
file-local `local notation` does not export, and undefined identifiers
in theorem statements silently become auto-bound variables (the spike's
first triangle block elaborated `triL`/`triH` as metas before local
notations were redeclared); (2) the `evals` call shape — `evals` takes
only the symmetry proof (`M` implicit), unlike `eigvalOf` where `M` is
explicit; passing both puts the proof in the index slot and typechecks
into nonsense; (3) `decide` over ℝ stays classical even for
literal-equality goals (`Real.decidableEq` is `Classical.choice`-backed)
— entry tables must close by `rfl` or `simp`, never `decide`; (4) the
wrapper-literal wall again — `fin_cases` produces `(fun i => i) ⟨k, ⋯⟩`
shapes that block `rfl`/`norm_num` on `Fin`-indexed `if`-tables and
vector literals; the reliable routes are `simp [table]` (full) after
`revert`-ing hypotheses, or `match`-defined fixtures whose equations
reduce; (5) `Finset.sum_mul` is stated right-to-left from the natural
reading (`(∑ f) * b = ∑ (f * b)`) — the `.symm` is needed when pulling
a constant out; (6) `Matrix.IsSymm` is a `def` (transpose equality),
not a structure — anonymous constructors fail; use `IsSymm.ext` or a
`show` of the underlying equation.

**Verification:** spike first (`wip/speccert_spike.lean` — the full
84-declaration delivery, iterated to zero errors/zero warnings before
any shelf edit); `lake env lean` on the landed QA module (zero errors,
zero warnings — the three positioned info-level `ring_nf` hints
confirmed pre-existing); explicit `lake build` targets ✔ on
`Mixing`, `Oversmoothing`, and the QA module; **the 84-declaration
axiom audit above**; **full `lake build` ✔ (2412/2413) immediately
followed by `check_build_completeness.py` — 133 source files, 133
fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4
current axioms, unchanged; only the allowlisted-confirmed PF finding);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (**4411/4/0**)
with the verification row. One incident, recovered with no loss: the
first landing of the shelf section misplaced the Oversmoothing consumer
inside `Mixing.lean` and its removal cut the lazy decay-engine sections
— `Mixing.lean` was restored verbatim from `git show HEAD:` (it carried
no other pending changes; verified by an empty `git diff` against HEAD)
and the landing redone with exact anchors; the final file's lazy
sections are byte-identical to HEAD's (diff confirms only the inserted
certificate section). Records updated: this proposal, the scoreboard
verification row, README (4411 + the walks-and-mixing row's certificate
clause), the radar (QA axis synced 4336 → 4411, held 4.5),
`index/map/spectral_graph.md` (the SpectralCertificate section), the
backlog item-8 twenty-second update, both map data tables + regenerated
SVG, the execution plan, and the activity log. Nothing committed; the
prior runs' uncommitted deliveries preserved.

**Remaining risk:** none owed by the delivery — pure hard crust, no
axiom disposition changed, no existing public statement changed (the
consumer joins are new theorems; the caller-certificate family is
untouched and still available). Honest scope: the odd-closed-walk
interface remains weaker than "non-bipartite" (the classical dichotomy
is true but unbundled — unchanged from the primitivity delivery's
recorded state); the computed rate is the two-sided max, typically
loose exactly where `|λ_max − 1|` and `|1 − λ₂|` differ; and the
depth-form oversmoothing join at the computed rate is ~~a composition
of the `(0,1)`-certificate with the existing theorem, recorded here
rather than landed as a separate statement~~ **landed 2026-09-03 as
that separate statement — see the follow-on delivery record below.**

## Follow-on delivery record (2026-09-03): the depth-form join landed

The closing scope note above was discharged the same day by a
dedicated run (`20260903T232202Z-run-1`, session
`ses_f966f94f7ffeVhWzf0ASxaaV11`): **`Oversmoothing.lean`'s
`walkDistribution_sub_stationaryVec_le_of_depth_of_odd_walk`** — the
plain family's first *certificate-free* depth ceiling, stated at the
inflated computed rate `(max (max (1 − λ₂) (λ_max − 1)) 0 + 1)/2`
with the threshold display `log (√(π_y((π_x)⁻¹−1))/ε) / log (1/r*)`.
Design decisions: the rate facts are proved *directly from the
constituents* (`secondEval_normalizedLaplacian_pos_of_connected`'s
`0 < λ₂`, the strict signless engine's `λ_max < 2`, and
`abs_one_sub_eigvalOf_le_max`) rather than obtained from the
existential certificates — so nothing depends on rcases witness
unfolding; and the `_of_odd_walk` suffix is honest, because unlike the
abs twins this statement *cannot* be unconditional — on bipartite
input the computed rate is exactly `1`, the displayed denominator
degenerates to `log 1 = 0`, and the threshold hypothesis degenerates
to junk (fenced, below).

QA +17 (`Mixing_QA.lean`'s `SpectralCertificate` section, 4411 →
4428): the inflated display rate pinned exact at both certificate
fixtures (`tri_inflated_rate_QA` `3/4` against the pinned `r = 1/2`;
`loopTri_inflated_rate_QA` `1/2` — the corner the inflation exists
for); the ceiling instantiated with genuinely verified thresholds at
both — the triangle at `t = 3`, `ε = 1/2` (denominator `log(4/3)`,
threshold `2√(2/3) ≤ 2 ≤ (4/3)³ = 64/27` with the corpus's
`√(2/3) ≤ 1` doing the analytic work, true value `1/24` pinned against
`tri_dist_three_zero_QA`; the computed display costs two layers over
the caller-certificate ceiling's `t = 1` at the same `ε`), the looped
triangle at `t = 1` (denominator `log 2`, the threshold inequality
literally `tri_ceiling_threshold_one_QA` reused — both fixtures have
uniform `π = 1/3` — with the conclusion `0` by exact one-step
mixing); and **the C₄ junk-threshold fence**: the top spectrum entry
pinned `= 2` (the alternating mode through `eigvalOf_le_evals_last`
against the signless `≤ 2` ceiling), the display rate pinned to
saturate at exactly `1`, the two-step law pinned `ν(2) = (1/2, 0,
1/2, 0)` — so the dropped-odd-walk statement's threshold hypothesis
is *junk-satisfiable* (`x/0 = 0 ≤ t` at every `t`) while the
conclusion fails at `(t, x, y, ε) = (2, 0, 0, 1/8)` with `|1/2 − 1/4|
= 1/4 > 1/8` — the junk-division hazard class exercised at the new
display itself, with the isolation cited to the delivered
`c4_fence_isolation_QA` rather than duplicated.

**Technique findings** (three): (1) Lean identifiers cannot contain
the `λ` token — `have hλ2 : ...` is a parse error ("unexpected token
'λ'"; rename to `hl2`), which surfaces far from its cause in long
statements; (2) `rw` will not match a Fin literal `⟨2, _⟩` against
the shelf display's `⟨Fintype.card V - 1, _⟩` (kabstract runs at
reducible transparency, where neither `Fintype.card (Fin 3)` nor
`3 - 1` unfolds) — the repair is an explicit `rfl`-lemma
`⟨Fintype.card (Fin 3) - 1, _⟩ = ⟨2, _⟩` (defeq holds at default
transparency) rewritten in before the corpus-spelled lemmas; `exact`,
by contrast, is forgiving — the whole triangle instance closes across
the literal gap; (3) `((1 : ℕ) : ℝ)` is *not* defeq to `(1 : ℝ)`
(Real.add does not whnf on literals) — close casts with
`exact_mod_cast`, not `exact`.

**Verification:** spike first (`wip/depthjoin_spike.lean` — the full
18-declaration delivery, iterated to zero errors/zero warnings before
any shelf edit; four fix rounds, all small); `lake env lean` on both
landed modules (zero errors/zero warnings; Oversmoothing rebuilt
first so the QA import sees the new theorem; the three positioned
info-level `ring_nf` hints in Mixing_QA confirmed pre-existing);
explicit `lake build` targets ✔ on `Oversmoothing` and the QA module;
**the 18-declaration axiom audit via `wip/depthjoin_axcheck.lean` —
every one exactly `propext, Classical.choice, Quot.sound`**; **full
`lake build` ✔ (2412/2413) immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh
artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4
current axioms, unchanged); `check_refutation_independence` (9-tag
clean — no tags touched); `check_public_reachability` clean (63 repo
modules); `check_citations` clean; `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (**4428/4/0**)
with the verification row; map-freshness after the 4411 → 4428 stats
sync in both map files and SVG regeneration. The landing is a
verified pure insertion in both files (diff checked: zero deletions
against the prior uncommitted state). Nothing committed; the prior
runs' uncommitted deliveries preserved.

## Second follow-on delivery record (2026-09-04): the two-start twin landed

**Status of this record:** DELIVERED (run `20260904T004657Z-run-1`,
session `ses_f9620d93cffeoXAiD38p29dXzt`). The depth-form record's
closing sentence — "the two-start indistinguishability twin at the
computed rate is now a two-line composition … recorded here rather
than landed (no consumer named)" — discharged by the next run, the
consumer gate discharged from the shelf's own evidence: the
caller-certificate twin `walkDistribution_sub_walkDistribution_le_of_depth`
has carried the consumer's name in its own docstring since 2026-08-31
("the corollary oversmoothing papers state informally: … the
node-distinguishing information carried by the starting positions is
gone"), and the computed-rate family's one-start ceiling was landed
for exactly that consumer class. The twin completes the statement
pair at the certificate-free rate.

**Content:** `Oversmoothing.lean`'s
`walkDistribution_sub_walkDistribution_le_of_depth_of_odd_walk` —
the one-start ceiling consumed twice (once per start, each with its
own threshold display) joined by the triangle inequality, `_of_odd_walk`-honest
for the same bipartite reason (the statement is unconditional-shaped
but cannot be unconditional: on bipartite input both thresholds
degenerate to junk simultaneously). Pure insertion after the one-start
theorem, before the caller-certificate twin.

**QA (+6, `Mixing_QA.lean`'s `SpectralCertificate` two-start blocks,
4428 → 4434):** the true two-start values pinned at both certificate
fixtures — the triangle at `t = 3`, `ε = 1/2`, starts `0`/`1`, target
`0`: the certified `2ε = 1` against the true `|1/4 − 3/8| = 1/8`, the
one-start deviations `1/12` and `1/24` in opposite directions summing
to exactly the two-start value (the triangle arithmetic genuinely
exercised); the looped triangle at `t = 1`, every pair of starts: the
true value exactly `0` by one-step mixing, indistinguishable from
step one — and the **`C₄` two-start fence**: both threshold
hypotheses junk-satisfiable at every time (reusing
`c4_depth_threshold_junk_QA`), the conclusion failing for the
*opposite-parity* pair `(x₁, x₂) = (0, 1)` at `(t, y, ε) =
(2, 1, 1/8)` with `|ν(2) 0 1 − ν(2) 1 1| = |0 − 1/2| = 1/2 > 1/4 =
2ε`. The new two-step law pin `c4_dist_two_one_QA` (from `1`:
`(0, 1/2, 0, 1/2)`, the opposite-parity mirror of the corpus's
`c4_dist_two_zero_QA`) supplies the second law. The witness shape is
genuinely two-start and worth recording: same-parity starts coincide
at even times on bipartite input, so the one-start fence's witness
(start `0`, target `0`) cannot refute the two-start statement — the
fence must take opposite parities, a discrimination the one-start
display cannot even express. Isolation cited, not duplicated
(`c4_fence_isolation_QA` already proves every other hypothesis
genuine at `C₄`).

**Technique findings (three):** (1) the auto-bind trap strikes again,
in its recorded form — referencing a file-local notation
(`loopTriL`) from a spike that does not redeclare it silently
elaborates the identifier as a bound variable (the error surfaces far
away, as a `rw` motive failure with the notation generalized in the
local context); the fix is to redeclare the notation or avoid it.
(2) A standalone threshold lemma stated at the natural spelling
(`⟨2, by decide⟩`, `(1 : ℝ)`) cannot be `exact`-ed against the
theorem's display (`⟨Fintype.card V − 1, by omega⟩`, `↑t`) even
across the defeq that holds — the robust idiom (used in the landed
proof) is to inline the threshold discharge as a `refine ?_` goal so
the display elaborates from the theorem itself, then rewrite within
it (`exact_mod_cast` closing casts, per the depth-form record's
finding 3). (3) `norm_num` normalizes `|0 − 1/2|` to `|1/2|` but does
not evaluate the absolute value — the recorded `abs_of_nonneg`
rewrite must come *after* the arithmetic normalization, with
`linarith` closing the now-literal inequality.

**Verification:** spike first (`wip/twostart_spike.lean` — the full
7-declaration delivery, iterated to zero errors/zero warnings before
any shelf edit; two fix rounds, all small and all in the recorded
trap classes); `lake env lean` on both landed modules (zero
errors/zero warnings; the three info-level `ring_nf` hints confirmed
pre-existing — count 3 = 3); explicit `lake build` targets ✔ on
`Oversmoothing` and the QA module; **the 7-declaration axiom audit
via `wip/twostart_axcheck.lean` — every one exactly `propext,
Classical.choice, Quot.sound`**; **full `lake build` ✔ immediately
followed by `check_build_completeness.py` — 133 source files, 133
fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0
(4 current axioms, unchanged); `check_refutation_independence`
(9-tag clean — no tags touched); `check_public_reachability` clean
(63 repo modules); `check_citations` clean; `check_markdown_links`
clean; `check_backlog_freshness` clean; scoreboard regenerated
(**4434/4/0**) with the verification row; map-freshness exit 0 after
the 4428 → 4434 stats sync in both map files and SVG regeneration
(49 stations, no status change — none owed). The landing verified as
pure insertion in both Lean files (zero deletions against the prior
uncommitted state). Nothing committed; the prior runs' uncommitted
deliveries preserved.
