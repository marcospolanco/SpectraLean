# Execution plan

This is the compact, current-state ledger for sustained autonomous work. It is
updated at milestone boundaries; [`AGENT_ACTIVITY.md`](AGENT_ACTIVITY.md)
holds the append-only narrative.

## Active milestone

None — see the delivered milestone below and the standing handoff.
The Ramanujan Expansion Ceiling row (the Active table's only High)
was **delivered this run** and retired to the Delivered table; with
no High rows remaining, the next run falls through to the
Medium-High/Medium rows per priority item 0.

------

## Delivered milestones (most recent first)

**The Ramanujan Expansion Ceiling — `AlonBoppana.lean`'s first theorem
consumer, the Alon–Boppana obstruction composed with the Cheeger hard
direction; `proposals/ramanujan-expansion-ceiling.md` (the Active
table's only High row); run 1, 2026-08-27, run `20260827T220230Z-run-1`;
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/ram_axcheck.lean` on all 13 audited
declarations — 5 module + 8 QA: exactly `propext, Classical.choice,
Quot.sound`, every one — the ceiling consumes two *proved* theorems,
so the whole chain is unconditional). QA 2659 → 2666 (+7 theorem
declarations; the `abC8_half` cut fixture is a `def`).**

**Delivered** in three pieces: (1) the engine in `Spectral.lean`'s
`Lambda2Variational` section — **`secondEval_smul_of_pos`** (the
exact positive-scaling lemma by the variational route: both sides
through `secondEval_variational`, the constraint set of `c • M` as
the positive-scaled image, `sInf` commuting by the two-direction
ping-pong; PSD + kernel hypotheses exactly what both shelf Laplacians
carry; the hypothesis-free generalization stays priced — the pin has
no `eigenvalues_smul`/`charpoly_smul` and no consumer has named it),
`smul_isSymm`, and **`secondEval_congr`** (proof irrelevance across
equal operator spellings — the robust route around the
motive-not-type-correct trap of rewriting matrix equalities under
proof-carrying applications); (2) the composition in
`AlonBoppana.lean`'s new `ExpansionCeiling` section (the file gains
the `Cheeger` import — no cycle): the operator identity
`smul_one_sub_eq_smul_regularNormalizedLaplacian` (`d • 1 − A =
d • L_sym` under regularity) and the headline
**`ramanujan_expansion_ceiling`** — `cheegerConstant A ≤
√(2 (1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))))` at exactly the
Alon–Boppana hypothesis stack, both source theorems consumed verbatim
with `h01 → hnonneg` the only bridge; (3) the QA —
`Variational_QA.lean`'s `ScalingK2` section (the K₂ two-route scaling
pin: raw trace/determinant/sortedness `[0, 6]` vs the lemma joined to
the on-file `λ₂ = 2`, a wrong constant breaking exactly one route;
the negative-`c` fence: sorted spectrum `[-2, 0]`, `0 ≠ -2`, the
`0 < c` hypothesis load-bearing) and `AlonBoppana_QA.lean`'s Step 6
(the C₈ ceiling instance evaluating numerically to `√2` at `k = 0`;
the fixture's actual `φ ≤ 1/4` by the exhibited half-set cut through
`conductance_ge_cheegerConstant` — the independent cut-level route,
non-vacuous with strict slack `1/4 < √2`, never tight; the two-`k`
improvement pinned as arithmetic on the statement's own constants at
`d = 2`, with the honest C₈-hosts-only-`k = 0` note per the on-file
`abC8_far_fence`). Step 0's three checks answered from source
evidence and recorded in the proposal before any shelf Lean
(`IsDRegular` definitionally Cheeger's `hd`; the scaling lemma absent
from shelf and pin, the variational route cheapest; `h01 → hnonneg`
by `Or.elim`). Obstruction scope only — the hard acceptance-bar item:
no tightness or attainment claim anywhere.

**Verification:** spike first (`wip/ram_spike.lean`, every piece to
zero errors/warnings before any shelf Lean; technique findings
recorded in the proposal's delivery record — `λ` is the `fun`
keyword and breaks identifiers; the proof-arg-carrying-application
rewrite trap and its `secondEval_congr` dissolution;
`Matrix.smul_mulVec_assoc`'s direction; `mem_lowerBounds.1` for
`BddBelow` destructuring; def-rewrites needing the `show … from rfl`
equation form; the `Real.sqrt_lt_sqrt` argument order;
`norm_num`'s in-`√` evaluation at `d = 2` leaving `1 < √2`; Finset
literals behaving at width 8 where matrix literals do not; the
stale-olen recurrence at the import boundary); `lake env lean` on all
four touched files — zero errors, warnings exactly at the
pre-existing baselines (Spectral's 8, Variational_QA's 7;
AlonBoppana and its QA clean); explicit `lake build` targets ✔ (all
four); `#print axioms` — the standard three only, all 13; **full
`lake build` ✔ (2400/2401, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 119/119
fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**2666/10/0**). Records updated: the proposal (COMPLETE
header + the delivery record), `proposals/README.md` (the High row
retired to the Delivered table; the Active table now has no High
rows), README (2666; the module-table clause), the radar (axis 4's
evidence clause with the score held at 5.0 per protocol — a
composition of two counted families plus one engine piece, not a new
theorem family; the QA axis synced 2659 → 2666), the scoreboard (a
verification row + the interpretation bullet), backlog item 3 (the
ceiling clause), the index map (the ExpansionCeiling + scaling-engine
sections, 5 rows), this plan, and the activity log. Nothing committed;
the prior runs' uncommitted Slice-3 delivery preserved untouched.

**Remaining risk:** none blocking. The priced follow-ons are recorded
in the proposal: the hypothesis-free general scaling lemma (needs
eigenvalue-multiset machinery the pin lacks — no named consumer), a
`k = 1`-hosting fixture (C₁₂) for instance-level two-`k` QA, and the
asymptotic family corollary (a named d-regular family with
`diam → ∞` — the Alon–Boppana proposal's own deferred item).

**Next milestone (open):** the Active table has no High rows — per
priority item 0 fall through to the Medium-High/Medium rows
(empirical-stationary-distribution Step 0 — its i.i.d.-sampling
prerequisite is delivered; the sampled-Laplacian quadratic-form
consumer; the Fiedler-subspace Davis–Kahan Step-0 check) or the
sparsification follow-ons.

------

## Delivered milestones (most recent first)

**Records repair + Sparsification Step 1, Slice 3 — the assembly +
QA, Step 1 COMPLETE and the program's strategic aim met
(`matrix_bernstein`'s first real theorem consumer); the Active
priority table's then-top High row
(`proposals/spectral-sparsification-via-leverage-scores.md`); run 1,
2026-08-27, run `20260827T193452Z-run-1`; DELIVERED — zero new axioms
(count stays 10; `#print axioms` via `wip/ss3_axcheck.lean` on all 43
audited declarations: 39 — the 14 new module declarations and 25 of 27
QA — exactly `propext, Classical.choice, Quot.sound`; the two Derived
tails and their two QA interface pins carry `matrix_bernstein`,
honestly reported). QA 2632 → 2659 (+27, the new
`Scaffold/QA/Derived/SparsificationTail_QA.lean`).**

**Records repair (first, this run):** the committed Slice-2 delivery
(`d6e62a9`) had exited post-commit before its terminal activity entry
and this plan's Active-block retirement (the recurring records-gap
pattern, fifth instance) — re-verified from scratch (direct
elaboration of both Slice-2 files at zero errors/zero warnings, the
72-declaration axcheck re-read against the committed state), terminal
entry appended, stale block retired, and a delivered-milestone record
written in below.

**Slice 3 delivered** in three pieces: `GraphTheory/Sparsification.lean`'s
new sections (the transfer helpers, the action bound
`l2OpNorm_mulVec_dotProduct_le`, the symmetry-free norm→form transfer
`abs_quadForm_le_of_l2OpNorm_le`, the sampled operator `ssSampled`
with the *exact pointwise* deviation identity `ssSampled ω − Π_{im L}
= ∑_e X_e ω` — the saturation guard mirrored as a deterministic
weight, no null-event caveats — and the Bool-valued summand shape
closing `h_meas`/`h_indep` through the Slice-1 transfer layer); the
new `Scaffold/Derived/SparsificationTail.lean` (umbrella import
added) with **`sparsification_norm_tail`** — `μ {‖S(ω) − Π‖ ≥ t} ≤
2 d exp(−t²/(2/q + 2t/(3q)))` at the *proved* constants, Finding B's
`Fintype.equivFin` + `Equiv.sum_comp` transport, no connectivity
hypothesis — and **`sparsification_quadForm_tail`** (the additive
eigen-coordinate pullback); and the QA (the deviation identity pinned
at K₂ all-true with every piece visible, the deviation norm `= 1 =
1/q` tight both sides, the transfer bound attained with equality,
`quadForm_imageProjector_eq`'s first consumer, both tails' interface
instances, the nonempty-event witness, and the two-sided connectivity
content — the disconnected budget fence beside the connectivity-free
positive). One mid-run build repair: `quadForm_sub` already existed
in AlonBoppana (a different notion) — renamed `quadForm_sub_matrix`
with consumers updated.

**Verification:** spike first (`wip/ss3_spike.lean`, all three pieces
in one file, zero errors/warnings before any shelf Lean; technique
findings recorded in the proposal's Slice-3 record — beta-redex
spelling mirroring for axiom-instantiation rewrites, `Equiv.sum_comp`
direction, `Real.exp_le_exp` iff, reserved `Π` identifier, nlinarith
certificates, the stale-olen recurrence); `lake env lean` zero
errors/zero warnings on all three changed/new files; explicit `lake
build` targets ✔ (2159/2159, 2165/2165, 2166/2166); **full `lake
build` ✔ (2400/2401, "Build completed successfully") immediately
followed by `check_build_completeness.py` — 119/119 fresh, 0 stale, 0
missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2659/10/0**).
Records updated: the proposal (status header — Step 1 COMPLETE with
priced follow-ons — + the Slice-3 delivery record with technique
findings), `proposals/README.md` (the High row downgraded to
Medium-follow-ons with the delivery clause; the Ramanujan row now the
table's only High), README (2659; the Sparsification row extended and
the SparsificationTail row added), the radar (QA axis synced 2632 →
2659 across 62 modules), the scoreboard (two verification rows + the
interpretation bullet), the backlog (the Slice-3 clause), the index
map (the Sparsification + SparsificationTail sections — 21 rows,
closing the inherited gap that Slice 2's declarations had never been
indexed), this plan, and the activity log. Nothing committed; the
prior runs' uncommitted deliveries preserved untouched.

**Remaining risk:** none blocking. The priced follow-ons (the
multiplicative `(1±ε)` refinement on `im Π`-coordinate vectors, the
`q ~ log n/ε²` budget corollary, the graph-vector Laplacian form) and
the Slice-2 set-aside (`ssVariance K₂ 1 = rankOne v_(0,1)` exact
matrix value) are recorded in the proposal. The QA interface pins for
the axiom-conditional tails depend on `matrix_bernstein` by design —
that is the honest structure, not leakage.

**Next milestone (open):** per priority item 0 — the **Ramanujan
Expansion Ceiling** High row (a light, mechanical composition of
`alonBoppana_nilli_classical` + `cheeger_lower_bound` plus one small
`secondEval` scaling lemma — gives `AlonBoppana.lean` its first
theorem consumer); otherwise the Medium-High/Medium rows
(empirical-stationary-distribution Step 0 — its i.i.d.-space
prerequisite is delivered; the sampled-Laplacian quadratic-form
consumer; the Fiedler-subspace Davis–Kahan Step-0 check) or the
sparsification follow-ons.

------

## Delivered milestones (most recent first)

**Sparsification Step 1, Slice 2 — the deterministic SS algebra; the
Active priority table's top High row
(`proposals/spectral-sparsification-via-leverage-scores.md`); run 1,
2026-08-27, run `20260827T161958Z-run-1` (committed as part of
`d6e62a9`; records gap closed retrospectively by run
`20260827T193452Z-run-1` after the delivery session exited
post-commit pre-records — the recurring records-gap pattern, fifth
instance); DELIVERED — pure hard crust, zero new axioms (count stays
10; `#print axioms` via `wip/ss2_axcheck.lean` on all 72 audited
declarations — 48 public module + 24 public QA: exactly `propext,
Classical.choice, Quot.sound`, every one; re-verified against the
committed state by the closing run). QA 2609 → 2632 (+23, the new
`Scaffold/QA/SpectralGraph/Sparsification_QA.lean`).**

**Delivered** in the new `Scaffold/Mathlib/GraphTheory/Sparsification.lean`
(imports Foster, Resolvent, BernoulliProduct; umbrella import added):
the rank-one algebra with the norm bound `‖v vᵀ‖ ≤ v ⬝ᵥ v`, the
polarized bilinear Dirichlet identity, the eigen-coordinate edge
vectors `ssEdgeVec` with `‖v_e‖² = w_e R_eff/2` and the Foster budget
corollary `∑_{u,v} ‖v_e‖² = card V − 1`, the image projector
`imageProjector` with `trace = card V − 1` and the exact projector
identity `∑_e v_e v_eᵀ = Π_{im L}`, the Bernoulli second moment
`E[(δ/p − 1)²] = (1−p)/p`, and the Finding-A-guarded sampling design
(`ssProb`/`ssDelta`/`ssSummand`/`ssMeasure`) with all three
`matrix_bernstein` clause lemmas *proved* at the classical constants
(`∫ X_e = 0` connectivity-free, `‖X_e ω‖ ≤ 1/q` uniformly, `∑_e ∫
X_e X_e = Σ` and `‖Σ‖ ≤ 1/q`) — retiring the Step-0 record's named
residual risk. Full delivery record with technique findings in the
proposal's Slice-2 section; QA with the two-route budget pin, the
two-sided rank-one norm identity, the exact variance coefficient, and
the Finding-A and `q = 0` fences.

**Verification (by the delivery session; re-verified from scratch by
the closing run):** spike first (`wip/ss2_spike.lean`, zero
errors/warnings before any shelf Lean); `lake env lean` zero
errors/zero warnings on both new shelf files; explicit `lake build`
targets ✔ (2159/2159 module, 2160/2160 QA); `#print axioms` all 72 at
the standard three; full `lake build` ✔ (2399/2400) followed by
`check_build_completeness.py` — 117/117 fresh, 0 stale, 0 missing,
exit 0; `lint_axioms` (10), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (2632/10/0). The closing run re-ran the
direct elaborations and the axcheck against the committed state and
this run's end-of-run full build + completeness cover the rest.

**Remaining risk:** Slice 3 (assembly + the proposal's three QA
obligations) — Finding B's `Fin n` edge-enumeration transport, the
norm-event → quadratic-form transfer through the eigen-coordinate
pullback (the statement decision of how `xᵀL̃x` relates to the
eigen-coordinate quadratic form), and the `q`-budget error-shape
calculus. One QA residual recorded in the proposal: the exact matrix
value `ssVariance K₂ 1 = rankOne v_(0,1)` was set aside
(elaboration-quirk cost disproportionate to its QA value; the scalar
coefficient pin carries the falsification content).

------

## Delivered milestones (most recent first)

**Sparsification Step 1, Slice 1 — the sampling-space module; the
Active priority table's top High row (`proposals/spectral-sparsification-via-leverage-scores.md`),
its named next action; run 1, 2026-08-27, run `20260827T142209Z-run-1`;
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/ss1_axcheck.lean` on all 42 audited
declarations — 18 public module + 24 public QA: exactly `propext,
Classical.choice, Quot.sound`, every one). QA 2585 → 2609 (+24, the
new `Scaffold/QA/Probability/BernoulliProduct_QA.lean`, the
`Probability` QA domain's first file).**

**Delivered** in the new
`Scaffold/Mathlib/Probability/BernoulliProduct.lean` (umbrella import
added): the Step-0 spike's proved blueprint promoted — `bernPMF` (the
product-Bernoulli PMF on `ι → Bool`), the marginals
`sum_coord_mul`/`sum_coord2_mul`, the cylinder measures `toMeasure_cyl`,
pairwise `IndepFun` of coordinates **`indepFun_coord`**, the scalar
centering **`integral_delta`** (`∫ δ_e ∂μ = p e`) — **plus the
Step-0 record's named residual risk retired: the matrix-codomain
transfer layer, Lean-untried until this run, now proved**
(`stronglyMeasurable_coord_matrix` via Mathlib's
`StronglyMeasurable.of_finite` — the topology-only `h_meas` route;
`measurable_coord_matrix` at the shelf's matrix pi σ-algebra;
`indepFun_coord_matrix` — the `IndepFun.comp` transfer; and the
centering integrals `integral_coord_smul` /
**`integral_coord_center_smul`** — the exact `h_mean` clause shape
`∫ ((δ_e/p_e) − 1) • M ∂μ = 0` at `p e ≠ 0`). This is the shelf's
first concrete probability space, cross-listed for the
empirical-stationary-distribution Medium-High row's identical
i.i.d.-sampling prerequisite, and the gate on `matrix_bernstein`'s
first structural consumer (Slice 3).

**QA (+24, the `Fin 2 → Bool` four-atom fixture at `p = ![1/2, 1/3]`,
the atom enumeration as the independent raw route):** the four
joint-mass values raw; total mass `1` by two independent routes (the
∑-∏ theorem vs raw enumeration); the marginal and three
cylinder-measure pins; **independence pinned numerically through
`indepFun_coord`** (the intersection measure splits as
`1/2 · 2/3 = 1/3`, joined to the cylinder pins); `∫ δ_1 = 1/3` by two
routes; the matrix-layer clause instances at a concrete
`!![1,2;3,4]` family; the matrix centering pins; and **two proved
fences** — the `[0,1]` bounds load-bearing for the mass normalization
(`p = ![2]` sums to `2 ≠ 1`), and the `p e ≠ 0` centering hypothesis
**refuted at the junk value** (`p = ![0]`: the "centered" integrand
evaluates through `0/0 = 0` to the constant `−M`, so the integral is
`−M ≠ 0` — the conclusion fails, not merely the hypothesis).

**Verification:** spike first (`wip/ss1_spike.lean` — the full module
plus the QA section, both sides to zero errors/warnings before any
shelf Lean; technique findings recorded in the proposal's delivery
record — `ENNReal.ofReal_mul`'s single side condition vs
`ofReal_add`'s two; `congr 1; norm_num` for `ofReal`-equalities; the
rw-position requirement for merge lemmas; the L2OpNorm
`CompleteSpace` probe; the global `MeasurableSpace.pi` instance
dropping the spike's local one; `omit ... in` before docstrings; the
`congrFun`-witness route for atom disequalities at no pi
`DecidableEq`; scalar-type ascription in `(1/2) • M` statements);
`lake env lean` zero errors/zero warnings on both new files; explicit
`lake build` targets ✔ (2042/2042, 2043/2043); `#print axioms` — the
standard three only, all 42; **full `lake build` ✔ (2388→2398/2399,
"Build completed successfully") immediately followed by
`check_build_completeness.py` — 115/115 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2609/10/0** —
the regeneration also repaired the generated-metrics block, which the
uncommitted prior deliveries had left at the committed 2549 while
their verification rows were swept; the working-tree count is now
truthful). Records updated: the proposal (status header + Slice-1
delivery record with technique findings + next action → Slice 2),
`proposals/README.md` (the High row's next action → Slice 2), README
(2609; the module-table row), the radar (QA axis synced 2585 → 2609
across 60 modules; axis 7's sampling-space clause, score held at 4.0
with the protocol reason), the scoreboard (two verification rows +
the repaired metrics block), backlog item 7 (the delivery clause),
the index map (the Sampling Spaces section + 13 declaration rows),
this plan, and the activity log. Nothing committed; the prior runs'
uncommitted Alon–Boppana Step-3b/4/5 deliveries preserved untouched.

**Remaining risk:** Slices 2–3 (the deterministic SS algebra, then
the assembly + QA) remain; Finding A's saturation guard is now a
Slice-2 statement decision with the centering-clause shape it must
fit already delivered; Finding B's `Fin n` edge transport belongs to
Slice 3; the `R = 1/q` / `‖Σ‖ ≤ 1/q` constants are classical values
Slice 2 owns.

**Next milestone (open):** per priority item 0 — sparsification
**Step 1, Slice 2** (the deterministic SS algebra); otherwise the
Medium-High/Medium rows (empirical-stationary-distribution Step 0 —
now cheaper again, its i.i.d.-space prerequisite is *delivered*; the
sampled-Laplacian quadratic-form consumer; the Fiedler-subspace
Davis–Kahan Step-0 check against the delivered Band family).

------

## Delivered milestones (most recent first)

**Sparsification Step 0 — the matrix-Bernstein clause-set survey;
`proposals/spectral-sparsification-via-leverage-scores.md` (the Active
table's top High row); run 1, 2026-08-27, run
`20260827T123751Z-run-1`; selected per priority item 0 as the row's
named next action: DELIVERED — a verdict-plus-spike run, **zero shelf
Lean touched** (QA count unchanged at 2585, axiom count unchanged at
10; `wip/ss0_spike.lean`, 316 lines, is the evidence artifact:
`lake env lean` **zero errors / zero warnings**, exit 0).**

**Verdict: tractable.** Every clause of `matrix_bernstein` has a
discharge route at the classical Spielman–Srivastava design. The
proposal's three named checks, each closed against shelf + pinned-
Mathlib evidence: (1) *centering and boundedness* — the Bochner
centering arithmetic **spike-proved end to end** (`integral_delta`:
`∫ δ_e ∂μ = p e` through `PMF.integral_eq_sum`, the one-coordinate
marginal, and the `≠ ⊤`-guarded `← ENNReal.toReal_sum`); the bounded-
ness value is the classical `R = 1/q`, its deterministic input the
rank-one bound `‖v ⊗ v‖ ≤ ‖v‖²` with two named shelf routes — plus
**two interface findings**: the uniform `∀ ω` in `h_bound` forces a
saturation guard into the Step-1 summand design (a saturated edge's
`δ_e = 0` outcome would violate the bound *pointwise*), and the `Fin n`
summand indexing needs an edge-enumeration transport; (2) *the
leverage normalization* — `Foster.lean`'s `(∑ᵢ∑ⱼ A i j · R i j)/2 =
card V − 1` IS the unordered-pair budget identity the sampling
consumes; the shelf's `leverageScore` needs only a thin `(n−1)`
rescaling; connectivity load-bearing exactly as QA fence 3 expects;
(3) *the infrastructure* — **it did not exist**: no concrete
probability measure anywhere in the shelf, and no pinned-Mathlib lemma
supplies coordinate independence on a product measure — so the spike
**builds and proves it**: the space `ι → Bool` at the product
σ-algebra, the product PMF `bernPMF` via `PMF.ofFinset` with total
mass by the `Finset.sum_prod_piFinset` ∑-∏ swap, the one-/two-
coordinate marginals (`sum_coord_mul`/`sum_coord2_mul` through the
`coordG1`/`coordG2` atom defs), cylinder measures, and the headline
**`indepFun_coord`** — pairwise `IndepFun` of coordinate projections,
the exact shape the `h_indep` clause needs. The matrix-codomain layer
has source-confirmed routes (not spiked): `SimpleFunc.ofFinite` +
`SimpleFunc.stronglyMeasurable` (topology-only — the right route at
the shelf's hand-rolled matrix σ-algebra precisely because no
BorelSpace bridge exists in the pin), `measurable_pi_iff` entrywise,
and the `IndepFun.comp` transfer with `measurable_of_bool`.

**Priced decomposition recorded in the proposal:** Slice 1 the
sampling-space module (deliberately its own slice — the empirical-
stationary-distribution Medium-High row needs the same i.i.d.-sampling
object; cross-proposal leverage named), Slice 2 the deterministic SS
algebra (rank-one norm bound, guarded sampling matrices, the variance
PSD bound `‖Σ‖ ≤ 1/q`, the `∑ v_e⊗v_e = Π_{im L}` identity), Slice 3
assembly + the three QA obligations. Technique findings recorded for
Step 1 (the free-`p` autoBound trap behind every *stuck `Fintype ?m`*
failure; `rw` not rewriting under `∑` binders; HO-pattern metavar
failures at lambda arguments; `Finset.mul_prod_erase` vs `prod_erase`;
`PMF.toMeasure_apply`'s explicit `(p) (s)`; the `toReal_sum` side
condition).

**Verification:** spike `lake env lean wip/ss0_spike.lean` — zero
errors / zero warnings, exit 0 (iterated to green over the session;
the catch record is the proposal's technique-findings paragraph).
No shelf module changed, so the build surface is untouched; the
records sweep (proposal status header + Step-0 delivery record,
`proposals/README.md` High row → Step-1 next action, the OLD
`spectral-graph-sparsification.md` Phase-B blocker note corrected per
the acceptance bar — recording the successor document and the
`Matrix/Bernstein.lean` fact, this plan, the activity log) verified
by `lint_axioms` (10, no issues), `check_citations`, and
`check_markdown_links` after the sweep. Nothing committed; the prior
runs' uncommitted Alon–Boppana Step-4/5 deliveries preserved
untouched.

**Remaining risk:** the matrix-codomain layer and Slice 2's
deterministic bounds are confirmed-route but untried in Lean; the
`R = 1/q` / `‖Σ‖ ≤ 1/q` constants are asserted from the classical
argument, not spike arithmetic (Slice 2 owns them); Finding A's guard
decision shapes the Step-1 statement.

**Next milestone (open):** per priority item 0 — sparsification
**Step 1, Slice 1** (the sampling-space module; spike blueprint on
file); otherwise the Medium-High/Medium rows
(empirical-stationary-distribution Step 0 — now cheaper, its
i.i.d.-space prerequisite is spike-priced; the sampled-Laplacian
quadratic-form consumer; the Fiedler-subspace Davis–Kahan Step-0
check against the delivered Band family).

**The Alon–Boppana bound, Step 5 — the diameter-dependent single-graph
statement; the program COMPLETE; `proposals/alon-boppana-bound.md`
(Gate ADOPTED 2026-08-26); run 1, 2026-08-27, run
`20260827T105501Z-run-1`; selected per priority item 0 as the Active
table's adopted High row's named next action (with the two QA
residuals the Step-4 delivery priced for this run): DELIVERED — pure
hard crust, zero new axioms (count stays 10; `#print axioms` via
`wip/ab5_axcheck.lean` on all 13 audited declarations — 5 public
module + 8 public QA: exactly `propext, Classical.choice, Quot.sound`,
every one). QA 2576 → 2585 (+9, the Step-5 section of
`AlonBoppana_QA.lean`).**

**Delivered** in `GraphTheory/AlonBoppana.lean`'s new `Packaging`
section (one import added — `Mathlib.Combinatorics.SimpleGraph.Diam`):
the `√` plumbing **`mul_sqrt_inv_eq_sqrt`** (`x·√(x⁻¹) = √x`
hypothesis-free, junk-safe at `x ≤ 0`), the far-apart-to-diameter
bridge **`distEdge_le_diam`** (the Step-2 priced `ediam ≠ ⊤` blocker
dissolved: `exists_edist_eq_ediam_of_finite` exhibits the supremum at
a vertex pair, connectivity's `edist_ne_top_iff_reachable` closes),
the honest diameter bookkeeping **`alonBoppana_diam_ge`**
(`2(k+1)+1 ≤ diam`, i.e. `k+1 ≤ ⌊diam/2⌋` — hypothesis-side only,
the tree-ball hypothesis never derived from the diameter, per the
proposal's own qualification-trap warning), the capstone
**`alonBoppana_nilli`** — `secondEval (d•1 − A) ≤ d −
(1 + 2k√(d−1))/(k+1)` at `ρ = √((d−1)⁻¹)`, consuming
`twoEdgeVec_secondEval_le` verbatim (the `IsDRegular` `d : ℝ` /
`IsTreeBall` `d : ℕ` join already carried by that interface) — and
the classical error shape **`alonBoppana_nilli_classical`** (`≤ d −
2√(d−1) + 2√(d−1)/(k+1)`, the single-graph `λ₂ ≥ 2√(d−1) −
O(1/⌊diam/2⌋)` form in Laplacian clothing).

**QA (+9):** the C₈ capstone instance (`secondEval (2•1 − C₈) ≤ 2 −
1 = 1` through the `√` packaging — the same number as Step 4's
instance, non-circularly reached); the classical-shape instance
(`≤ 2 − 2 + 2 = 2` — the honest weak-at-small-`k` reading, the error
term swallowing the content exactly where the qualification trap
demands); the diameter instance (`3 ≤ diam (supportGraph C₈)`);
the **loop-pair fence** (the priced residual 1, on the new `abP3L`
fixture — P₃ plus a loop, whose support graph provably equals
`abP3`'s: the loop's level-0 class is `{2}` of card `1 ≠ 2`, so
`IsTreeBall` fails and the two-vector orthogonality fails with it at
`⟨![1,1,−1], onesVec⟩ = 1 ≠ 0`); and the **independent engine route
at the integer witness** (the priced residual 2: the globally
supported `![1,1,0,−1,−1,−1,0,1]`, orthogonal raw, squared norm `6`
raw, quadratic form `8` raw by the support-filtered double sum with
all 36 entries by `rfl`, gives `secondEval (2•1 − C₈) ≤ 2/3` —
strictly stronger than both theorem routes' `≤ 1`, through a
structurally different vector).

**Verification:** spike first (`wip/ab5_spike.lean`, both sides to
zero errors/warnings before any shelf Lean; the technique findings
recorded in the proposal's delivery record); `lake env lean` zero
errors/zero warnings on both changed files; explicit `lake build`
targets ✔ (2011/2011 module, 2012/2012 QA — the stale-olean
remediation applied once before the QA elaboration); `#print axioms`
— the standard three only, all 13; **full `lake build` ✔ (2389/2390)
immediately followed by `check_build_completeness.py` — 113/113
fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass after the record
sweep; scoreboard regenerated idempotent (**2585/10/0**, md5-stable).
Records updated: the proposal (status header COMPLETE + Step-5
delivery record with technique findings + open-next-step → none),
`proposals/README.md` (the High row retired to the Delivered table;
the sparsification High row promoted to the table's top row with the
named next action; the stale "Active table remains empty" snapshot
annotated as historical), README (2585; the status-paragraph Steps-4–5
clauses — including the Step-4 clause the Step-4 run had left covered
only in the module table; the module-table row now reads program
COMPLETE), the radar (QA axis synced 2576 → 2585; axis 4's evidence
gains the Alon–Boppana clause — the theorem has landed, the axis's
Have column now closes both directions of the expansion–spectrum
relationship), the scoreboard (two verification rows + the
interpretation bullet + the header date), backlog item 3 (the
program-closure update), the index map (the Packaging section + 5
declaration rows), the module and QA docstrings, this plan, and the
activity log. Nothing committed; prior runs' deliveries preserved
untouched.

**Remaining risk:** none for this program — all five steps delivered
as pure hard crust and the proposal records COMPLETE. The deferred
items stay deferred on its own record (the asymptotic family
corollary needs a named d-regular family with `diam → ∞`; Route B's
walk-counting layer was never attempted). Program-level residue
noted for future QA if ever wanted: C₈'s diameter is provably `≥ 3`
(QA) and known to be `4` classically, but the exact pin `= 4` was not
needed for any statement and stays unformalized.

**Next milestone (open):** per priority item 0 — the sparsification
High row's **Step-0 survey** (verify `matrix_bernstein`'s clause set
against the leverage-score sampling argument); otherwise the
Medium-High/Medium rows (empirical-stationary-distribution Step 0;
the sampled-Laplacian quadratic-form consumer; the Fiedler-subspace
Davis–Kahan Step-0 check against the delivered Band family).

------

**The Alon–Boppana bound, Step 4 — the two-vector orthogonalization
and the Courant–Fischer application, the program's first
eigenvalue-level statement; `proposals/alon-boppana-bound.md` (Gate
ADOPTED 2026-08-26); run 1, 2026-08-27, run `20260827T072423Z-run-1`;
selected per priority item 0 as the Active table's adopted High row's
named next action: DELIVERED — pure hard crust, zero new axioms (count
stays 10; `#print axioms` via `wip/ab4_axcheck.lean` on all 34 audited
declarations — 17 public module + 17 public QA: exactly `propext,
Classical.choice, Quot.sound`, every one). QA 2560 → 2576 (+16, the
Step-4 section of `AlonBoppana_QA.lean`).**

**Delivered** in `GraphTheory/AlonBoppana.lean`'s new `TwoEdge`
section (no new imports, no umbrella change): the equal-mass lemma
**`radialVec_sum_eq`** (under `IsTreeBall` both edges' radial vector
masses reduce to the same function of `(d, ρ, k)` — so
**`twoEdgeVec`** is orthogonal to `onesVec` with no regularity at the
interface level), the norm identity **`twoEdgeVec_dotProduct_self`**
(`4 (k+1)` on disjoint radius-`k` balls — the two 3a denominators
add), the cross-edge elimination **`radialVec_cross_dotProduct_eq_zero`**
(consuming 3b's own level-Lipschitz lemma — its first downstream
consumer — plus `(k+1)+(k+1) < distEdge` disjointness, the far-apart
theorem's first theorem consumer beyond disjointness), the expansion
algebra (`dotProduct_mulVec_symm`, `quadForm_sub`), the doubled
numerator bound with its Rayleigh form, the engine layer at
`M = d•1 − A` (PSD and kernel from the Step-1 facts), and the headline
**`twoEdgeVec_secondEval_le`** — `secondEval (d•1 − A) ≤ d −
(2 + 4k(d−1)ρ)/(2(k+1))` through `secondEval_le_rayleigh`.

**QA (+16):** the C₈ antipodal-pair positive — orthogonality by two
routes (raw `4−4` per-vertex enumeration vs the theorem; the `(4,5)`
value oracle and level-1 pin `{3,6}` new), the norm `8 = 4(k+1)` by
the theorem, the numerator raw by decomposition (`8 = 6 + 6 − 2·2`,
the cross's two cross edges explicit), the **`hfar` fence** at `k = 1`
(`8 < 12`, both radius-2 tree balls genuine, the norm identity
surviving — the far-apart threshold isolated at its exact constant),
the **P₃ overlap fence** (`2 ≠ 4`, ball disjointness isolated), and
the **headline instance** `secondEval (2•1 − abC8) ≤ 1`.

**Verification:** spike first (`wip/ab4_spike.lean`, both sides to
zero errors/warnings before any shelf Lean); `lake env lean` zero
errors/zero warnings on both changed files; explicit `lake build`
targets ✔; `#print axioms` — the standard three only, all 34; **full
`lake build` ✔ (2388/2389) immediately followed by
`check_build_completeness.py` — 113/113 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated idempotent
(**2576/10/0**). Records updated: the proposal (status header +
Step-4 delivery record with technique findings + open-next-step →
Step 5), `proposals/README.md` (the High row's next action → Step 5),
README (2576; the module-table clause), the radar (QA axis synced
2560 → 2576), the scoreboard, backlog item 3, the index map, the
module and QA docstrings, this plan, and the activity log. Nothing
committed; prior runs' deliveries preserved untouched.

**Remaining risk:** Step 5 (the diameter-dependent statement) is the
program's last step — the far-apart-to-diameter bridge was priced and
deferred in Step 2 (`dist_le_diam` needs an `edism ≠ ⊤` supplier);
the `d`-join and `√` packaging are recorded as its content. Two named
QA residuals (the loop-pair orthogonality fence; an independent engine
route at the integer witness) are priced with fixtures on file.

**Next milestone (open):** per priority item 0 — Alon–Boppana
**Step 5**, or the sparsification High row's Step-0 survey; otherwise
the Medium-High/Medium rows.

------

**The Alon–Boppana bound, Step 3 sub-slice 3b — the energy half of the
Rayleigh quotient, Nilli's numerator; `proposals/alon-boppana-bound.md`
(Gate ADOPTED 2026-08-26); run 1, 2026-08-27, run
`20260827T052400Z-run-1` (records closed by run
`20260827T072423Z-run-1` after the delivery session exited
post-sweep pre-terminal, the records-gap pattern's fourth instance);
selected per priority item 0 as the Active table's adopted High row's
named next action: DELIVERED — pure hard crust, zero new axioms (count
stays 10; `#print axioms` via `wip/ab3b_axcheck.lean` on all 19 audited
declarations — 8 public + 11 QA: exactly `propext, Classical.choice,
Quot.sound`, every one; re-verified against the final source state by
the closing run). QA 2549 → 2560 (+11, the Step-3b section of
`AlonBoppana_QA.lean`).**

**Delivered** in `GraphTheory/AlonBoppana.lean`'s `Energy` section:
`levE_le_levE_add_one_of_adj` (the BFS level function 1-Lipschitz along
support-graph edges, junk-safe), `exists_levE_parent` (the parent
lemma — every level-`≥ 1` vertex has a support-adjacent neighbor exactly
one level down, no connectivity hypothesis; the from-below harvest that
dissolved the recorded "level sizes, not edge counts" obstruction
without strengthening `IsTreeBall`), `interiorE` with its algebra and
the interior level-sum bridge, the headline **`radialVec_quadForm_ge`**
(`2 + 4 k (d−1) ρ ≤ xᵀAx` under the existing `IsTreeBall` plus a
0-or-`≥ 1` weight discipline, distinct endpoints, a genuine edge), and
the Rayleigh corollary **`radialVec_rayleigh_ge`** joining it to the
3a denominator — Nilli's quotient before the Step-5 `√` packaging. QA:
the C₈ numerator pin tight at equality (raw `6` vs the theorem's
`2 + 4·1·1·1 = 6`), the `k = 0` pair, and three hypothesis fences
(`hedge` at the P₃ pseudo-edge, `h01` at the half-weight edge, `hxy` at
the one-vertex loop whose junk-zero partner keeps `IsTreeBall` honest).

**Verification:** re-run from scratch by the closing run — `lake env
lean` zero errors/zero warnings on both changed files; explicit
`#print axioms` all 19 standard-three; full `lake build` ✔ followed by
`check_build_completeness.py` 113/113 fresh, 0 stale, 0 missing, exit
0; `lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated **2560/10/0** (the closing run's regeneration
also repaired the delivery session's stale generated-metrics block,
left at 2549/2026-08-26 by its verification-row-only sweep). Full
delivery record with technique findings in the proposal; records swept
(README, radar, scoreboard, backlog, index map, `proposals/README.md`
next action → Step 4).

**Remaining risk:** Step 4 (the two-vector orthogonalization) and Step
5 (the diameter-dependent statement) remain; the `IsDRegular`-to-
`IsTreeBall` `d`-join and the `√` packaging stay deferred to Step 5.

------

## Delivered milestones (most recent first)

**The Alon–Boppana bound, Step 3 sub-slice 3a — the radial test vector
and its normalization; `proposals/alon-boppana-bound.md` (Gate ADOPTED
2026-08-26); run 1, 2026-08-27, run `20260827T012700Z-run-1`; selected
per priority item 0 as the Active table's adopted High row's named next
action (Step 3 priced by the proposal itself for sub-decomposition;
this run took the vector + normalization half — the other High row,
sparsification, stays a Step-0 survey that may re-scope it): DELIVERED
— pure hard crust, zero new axioms (count stays 10; `#print axioms`
via `wip/ab3_axcheck.lean` on all 18 audited declarations — 8 public +
10 QA, the two private QA level-oracle helpers covered transitively:
exactly `propext, Classical.choice, Quot.sound`, every one). QA
2539 → 2549 (+10, the Step-3 section of `AlonBoppana_QA.lean`).**

**Delivered** in `GraphTheory/AlonBoppana.lean`'s new `RadialVector`
section (no new imports, no umbrella change): **`radialVec A hA x y ρ
k`** — Nilli's radial test vector, the value `ρ ^ levE z` per BFS level
on the radius-`k` edge ball and `0` outside, the d-regular-tree
normalization carried by consumers as the hypothesis
`ρ ^ 2 = ((d − 1 : ℕ) : ℝ)⁻¹` (the `√` plumbing deliberately deferred
to the Step-5 packaging with the `IsDRegular` `d : ℝ` join); the
interface (`radialVec_apply`, `radialVec_of_mem_ballE`,
`radialVec_eq_zero_of_not_mem_ballE`, `radialVec_left` — the
always-`1` endpoint seed, `radialVec_ne_zero`); **the layer-cake sum
bridge `sum_ballE_eq_sum_levels`** (`ballE_card_eq_sum`'s summation
form at a function); and the headline **`radialVec_dotProduct_self`** —
`⟨ρ^{lev}, ρ^{lev}⟩ = 2 (k + 1)` exactly under `IsTreeBall` at radius
`k+1`: per level, the geometric growth `2 (d−1)^j` cancels the
vector's decay `ρ^{2j}` to exactly `2` — **the denominator of Nilli's
Rayleigh quotient and the first theorem consumer of the Step-2 level
machinery** (load-bearing growth: a wrong `levE`, `ballE` shape, or
`IsTreeBall` equation breaks the identity's type or truth). `1 < d` is
load-bearing at the `mul_inv_cancel₀` cancellation.

**QA (+10):** the **C₈ squared-norm pin `4 = 2 (k+1)` by two
independent routes** — the theorem through `abC8_isTreeBall` vs raw
per-vertex enumeration at the level-membership oracles
(`abC8_levE_zero_iff`/`abC8_levE_one_iff`, derived from the delivered
`levClass_zero_eq`/`abC8_levClass_one_eq`; the indicator sum the set's
card by `decide`) — the routes share no mechanism; the **`k = 0` pair
both routes** (the theorem at `isTreeBall_one_of_connected` — that
Step-2 lemma's first consumer); and the **K₂ `d = 1` degeneracy fence**
(the tree-ball predicate holds at `d = 1` — level 1 demanded empty and
empty — the normalization hypothesis is *junk-satisfiable* at `ρ = 0`
through `0⁻¹ = 0`, and the vector is `![1, 1]` at squared norm
`2 ≠ 2 (1+1) = 4`: `hd1` isolated exactly at the cancellation).

**Verification:** spike first (`wip/ab3_spike.lean`, module side and
QA side iterated to zero errors/zero warnings before any shelf Lean;
technique findings recorded in the proposal's Step-3a delivery record
— the `mul_assoc`-before-`← mul_pow` reassociation at the `2`-headed
per-level product, `nsmul_eq_mul` as the root ℕ-smul converter where
`Nat.smul_one` does not exist, the named-`have` requirement for
`Finset.sum_subset`'s zero function, `intro`-then-`rcases` for
disjunct patterns, the reverse-order `simp` flattening of nested
`Finset.mem_insert`, and `.le` on an equation rewriting at the
equation's own constant); `lake env lean` zero errors/zero warnings on
the module and the QA file; explicit `lake build` targets ✔ (2010/2010,
2011/2011 — the QA elaboration hit the recorded stale-olean trap once
before the module-target rebuild); `#print axioms` — the standard
three only, all 18; **full `lake build` ✔ (2388/2389, "Build completed
successfully") immediately followed by `check_build_completeness.py` —
113/113 fresh, 0 stale, 0 missing, exit 0** (the run hit the mtime
half of the documented staleness remediation once — a `touch`-and-replay
left an artifact older than source; the artifact-removal rebuild closed
it); `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated idempotent (**2549/10/0**, md5-stable). Records updated:
the proposal (status header + Step-3a delivery record with technique
findings + open-next-step → Step 3b), `proposals/README.md` (the High
row's next action → Step 3b), README (**2549** — this sweep also
repaired the committed README's stale Step-1-era count and clauses,
left behind by the Step-2 commit; the status-paragraph and module-table
clauses now cover Steps 1–3a), the radar (QA axis synced 2520 → 2549
with the same drift repair noted), the scoreboard (two verification
rows + the interpretation bullet), the index map (the AlonBoppana
section's Step-3 rows **plus the inherited signed-graphs gap closed**
— the `GraphTheory.Signed` section that the `7ca544b` commit had
omitted, flagged as a bounded records task by the Step-1 run and
delivered here per the standing handoff), backlog item 3 (the Step-3a
update + next → Step 3b), the module and QA docstrings, this plan, and
the activity log. Nothing committed; the prior runs' deliveries
preserved untouched.

**Remaining risk:** the program is 0–3a of 5 steps — the theorem itself
needs the energy half (Step 3b), the two-vector orthogonalization
(Step 4), and the diameter-dependent statement (Step 5). The energy
half's known hard piece is the neighbor-counting structure: the
cardinality equations alone give level sizes, not the level-to-level
edge counts Nilli's numerator consumes, so Step 3b must either count
enough edges from below (each level-`j` vertex has a parent at level
`j−1`) or strengthen `IsTreeBall` — a decision its own spike should
price. C₈'s 2-regularity remains structurally evident but not cheaply
computable at `Fin 8` (the recorded `vecCons` opacity), so no Step-3b
QA should assume it; the `IsDRegular`-to-`IsTreeBall` `d`-join stays
deferred to the Step-5 packaging; the diameter bridge belongs to Step
5. Q₃/K₃,₃ (the theorem-shaped negative witnesses) remain Steps 3b–5
QA.

**Next milestone (open):** per priority item 0 — Alon–Boppana
**Step 3b** (the energy half — the numerator `⟨ρ^{lev}, A ρ^{lev}⟩`
against the level equations; likely its own sub-decomposition, one
sub-slice per run), or the sparsification High row's Step-0 survey;
otherwise the Medium-High/Medium rows (empirical-stationary-
distribution Step 0; the sampled-Laplacian quadratic-form consumer;
the Fiedler-subspace Davis–Kahan Step-0 check against the delivered
Band family).

------

## Delivered milestones (most recent first)

**The Alon–Boppana bound, Step 2 — the tree-ball interface at module
level; `proposals/alon-boppana-bound.md` (Gate ADOPTED 2026-08-26);
run 1, 2026-08-26, run `20260826T232419Z-run-1`; selected per
priority item 0 as the Active table's adopted High row's named next
action from Steps 0+1 (the sparsification High row's next action
remains a Step-0 survey that may re-scope it): DELIVERED — pure hard
crust, zero new axioms (count stays 10; `#print axioms` via
`wip/ab2_axcheck.lean` on all 38 audited declarations — 18 public +
20 QA: exactly `propext, Classical.choice, Quot.sound`, every one).
QA 2520 → 2539 (+19, the Step-2 section of `AlonBoppana_QA.lean`).**

**Delivered** in `GraphTheory/AlonBoppana.lean`'s new `TreeBall`
section (one import added — `Mathlib.Combinatorics.SimpleGraph.Metric`,
the Step-0 verdict's explicit-import requirement): the Step-0
verdict's definitions promoted from per-fixture to module level
(`levE`/`levClass`/`ballE` — BFS levels of an edge against
`SimpleGraph.dist` on `supportGraph`), the junk-zero-honest level-0
iff `levE_eq_zero_iff` with its connected amortization
`levE_eq_zero_iff_of_connected` + `levClass_zero_eq`/`_card` (the
`j = 0` cardinality equation free of regularity;
`isTreeBall_one_of_connected`), the **tree-ball predicate `IsTreeBall`**
(level `j` carries exactly `2 (d−1)^j` vertices for `j < k` — the
working form Nilli's Rayleigh computation consumes, never a structural
tree-ness predicate), the ball algebra (`ballE_mem_iff`, `ballE_zero`,
`ballE_mono`, `levClass_pairwise_disjoint`, `ballE_succ_union`) with
the **layer-cake cardinality bridge `ballE_card_eq_sum`** (ball card =
geometric level sum, by induction at the pairwise-disjoint levels —
the Step-3 test vector's normalization input), and the far-apart
condition `distEdge` + **`ballE_disjoint_of_lt_distEdge`** (every
cross-endpoint distance exceeding `r + s` makes the balls disjoint,
by the connected triangle inequality at all four endpoint pairings —
the Step-4 orthogonalization's load-bearing separation input).

**QA (+19):** the **C₈ full-hypothesis positive** — the tree-ball
instance `IsTreeBall abC8 .. 0 1 2 2` (level 1 pinned to exactly
`{2, 7}` by adjacency-level facts only), the antipodal disjointness
through the far-apart theorem at four cross distances ≥ 3 each proved
by **short-walk exhaustion** (`dist_le_two_cases_of_connected`: a
connected distance ≤ 2 is a self, an adjacency, or a common neighbor,
each refuted by rfl-verified entries — only *lower* bounds are ever
needed, so no walk witnesses at all), and the layer-cake cardinality
by **two independent routes** (direct set enumeration
`ballE .. 1 = {0, 1, 2, 7}` via the neighbor lemmas vs the
geometric-sum theorem through the tree-ball instance); the **C₄
wrap-around negative** `¬ IsTreeBall abC4 .. 2 3` (level 2 demanded at
2 vertices and provably empty — the qualification trap's QA witness,
in place before the theorem it guards); and the
**threshold-tightness fence** (near-antipodal balls at min
cross-distance exactly `r + s` provably intersect at vertex `2` — the
strict inequality of the disjointness theorem load-bearing).

**Verification:** spike first (`wip/ab2_spike.lean`, module side and
QA side iterated to zero errors/zero warnings before any shelf Lean;
technique findings recorded in the proposal's delivery record — the
`vecCons`-at-`Fin`-literal-column-≥4 opacity to `simp`/`norm_num`
with the `rfl`-evaluation route (`abC8_entries`), `simp only [levE]`
normalizing `min` to an `omega`-invisible `⊓` (use `unfold`), `omega`'s
inability to refute `Fin`-literal disjunctions (split the iff and
`decide` the false side), the `(fun i => i) ⟨k, ⋯⟩`-wrapper mismatch
from `fin_cases`-built rfl substitutions (state enumerations as named
plain-literal `show`s and `subst`), and the metavariable-headed-`Adj`
anonymous-constructor failure (term-typed adjacency facts)); `lake
env lean` zero errors/zero warnings on both changed files; explicit
`lake build` targets ✔ (2010/2010, 2011/2011); `#print axioms` — the
standard three only, all 38; **full `lake build` ✔ (2388/2389, "Build
completed successfully") immediately followed by
`check_build_completeness.py` — 113/113 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated idempotent (**2539/10/0**, md5-stable). **This run also
repaired a latent name typo in the uncommitted Step-1 QA file**
(`Finset.sum_univ_two` → `Fin.sum_univ_two`, a nonexistent constant
caught by this run's direct elaboration — the failure class
`check_build_completeness.py` guards). Records updated: the proposal
(status header + Step-2 delivery record with technique findings +
open-next-step → Step 3), `proposals/README.md` (the High row's next
action → Step 3), the scoreboard (two verification rows + the
interpretation bullet), the radar (QA axis synced 2520 → 2539), the
index map (the AlonBoppana section's Step-2 rows), backlog item 3
(the Steps 0–2 update), README (2539; the module-table clause), the
module and QA docstrings, this plan, and the activity log. Nothing
committed; the prior runs' uncommitted deliveries preserved
untouched.

**Remaining risk:** the program is 0–2 of 5 steps — the theorem
itself is Steps 3–5 (Step 3, the radial test vector and its Rayleigh
quotient, is the priced crux and will likely need sub-decomposition
across runs per the proposal's own operating instructions). C₈'s
2-regularity is structurally evident but not cheaply computable at
`Fin 8` (row sums hit the recorded `vecCons` opacity), so Step 3 must
not assume it is; the `IsDRegular`-to-`IsTreeBall` `d`-join
(`d : ℝ` vs `d : ℕ`) is deliberately deferred to the Step-3–5
packaging. The diameter bridge (far-apart ⟹ large `SimpleGraph.diam`)
was priced and dropped this run: `dist_le_diam` needs an `edism ≠ ⊤`
supplier with no cheap route in this pin — it belongs to Step 5,
where the diameter-dependent statement is formulated. Q₃/K₃,₃ (the
not-full/not-far-apart theorem-shaped witnesses) remain Steps 3–5
QA. The inherited signed-graphs index-map gap stands.

**Next milestone (open):** per priority item 0 — Alon–Boppana
**Step 3** (the radial test vector `ρ^{lev}` on `ballE` and its
Rayleigh quotient — one step per run per the proposal's operating
instructions), or the sparsification High row's Step-0 survey;
otherwise the Medium-High/Medium rows (empirical-stationary-
distribution Step 0; the sampled-Laplacian quadratic-form consumer;
the Fiedler-subspace Davis–Kahan Step-0 check against the delivered
Band family).

**The Alon–Boppana bound, Steps 0+1 — the tree-ball spike priced and
the d-regularity interface delivered; `proposals/alon-boppana-bound.md`
(Gate ADOPTED 2026-08-26, commit `d86e181`); run 1, 2026-08-26, run
`20260826T215003Z-run-1`; selected per priority item 0 as the Active
table's top High row (the operator's explicit adoption, all
dependencies surveyed proved, zero new axioms needed, a named next
action — over the sparsification High row, whose next action is a
Step-0 survey that may re-scope it): DELIVERED — pure hard crust,
zero new axioms (count stays 10; `#print axioms` via
`wip/ab_axcheck.lean` on all 22 audited declarations — 4 public +
18 QA: exactly `propext, Classical.choice, Quot.sound`, every one).
QA 2506 → 2520 (+14, `AlonBoppana_QA` a new file).**

**Step 0 (the spike, `wip/ab_spike.lean`):** the tree-ball hypothesis
prices as **BFS level-cardinality equations** `#{z | levE z = j} =
2 (d−1)^j` against `SimpleGraph.dist` on `supportGraph` (`levE` =
min-distance-to-edge-endpoints, `levClass`/`ballE` the filter forms —
ball `Disjoint` is the far-apart condition), *not* a tree-ness
predicate. Unit cost: one distance value per vertex-level pair
(adjacency/self one-liners vs. walk-witness chases — the walk must be
inline in `dist_le`, pre-named Adj `have`s, since a `have`-bound walk
is opaque to `rfl` on its `length`); connectivity amortizes all
reachability refutations into one lemma; the `dist` junk-zero trap
(reachable-`0`) recorded as the Steps 2–3 guard;
`Mathlib.Combinatorics.SimpleGraph.Metric` needs an explicit import.
Honest negative fixtures identified: Q₃ (levels not full), K₃,₃
(edges not far) — the qualification trap's QA witnesses; C₈ the
smallest full-hypothesis cycle. **Verdict recorded in the proposal.**

**Step 1 (the delivery):** the new focused
`GraphTheory/AlonBoppana.lean` (imports `Spectral` only; umbrella
import added; the program's home for Steps 2–5): `IsDRegular` (the
shelf's `d : ℝ` hypothesis idiom, no new machinery),
`adjacency_mulVec_onesVec` (`A *ᵥ onesVec = d • onesVec`, row-sum
only), the **AM–GM row-sum domination** `quadForm_le_of_isDRegular`
(`xᵀAx ≤ d ‖x‖²` — entrywise AM–GM multiplied through nonnegative
weights, the symmetric double sum's halves both `d‖x‖²` via the row-
and column-sum degree identities; `hnn` load-bearing, fenced), and
the **top-eigenvalue identification** `evals_last_eq_of_isDRegular`
(`evals ⟨last⟩ = d` from both sides — the `onesVec` eigenvalue
witness through `exists_eigvalOf_eq_of_mulVec_eq_smul` +
`eigvalOf_le_evals_last`, and domination at the unit eigenvector
through `quadForm_eigvecOf_self` + `evals_mem_eigvalOf`; load-bearing
on the sorted-spectrum API at its extremes). QA (+14): the C₄/K₂
instances joined to raw entrywise eigen-equation pins (no theorem
input), the **P₃ non-regularity fence** (the constant vector provably
not an adjacency eigenvector for any `c` — `IsDRegular` load-bearing
at the interface's own witness), and the **hnn fence** (the signed
`!![1,−1;−1,1]]` is symmetric and *0-regular* — every hypothesis but
`hnn` — with domination refuted at `![1,0]`, `1 > 0`).

**Verification:** spike first (`wip/ab_spike.lean` — module side, QA
side, and the tree-ball pricing all green before any shelf Lean; the
technique findings recorded in the proposal's delivery record: the
pin's swapped `Finset.mul_sum`/`sum_mul` naming, `pow_two`'s
direction, the double-`← Finset.sum_div` assembly, and `onesVec ≠ 0`
at `1 ≤ card V`); `lake env lean` zero errors/zero warnings on both
new files; explicit `lake build` targets ✔ (2009/2009, 2010/2010);
`#print axioms` — the standard three only, all 22; **full `lake
build` ✔ (2387/2388, "Build completed successfully") immediately
followed by `check_build_completeness.py` — 113/113 fresh, 0 stale,
0 missing, exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated idempotent (**2520/10/0**, md5-stable). Records updated:
the proposal (Step-0 verdict + Step-1 delivery record + status
header), `proposals/README.md` (the High row's next action → Step 2),
README (2520; the status-paragraph clause; the module-table row), the
radar (QA axis synced 2506 → 2520 across 59 modules), the scoreboard
(the verification row + the interpretation bullet), the index map
(the AlonBoppana section + 4 declaration rows), backlog item 3 (the
Steps 0+1 update), the module and QA docstrings, this plan, and the
activity log. **Also this run, first: closed the prior signed-graphs
run's records gap** (its terminal activity entry + this plan's
Active-block retirement — the run had committed its full delivery in
`7ca544b` including scoreboard/radar/backlog/README/index/proposal
records, exiting before the terminal entry; this run re-confirmed its
93-declaration axiom audit against the committed state and closed
both records on that evidence — the recurring records-gap pattern,
third instance). Nothing committed; the prior runs' uncommitted
deliveries preserved untouched.

**Remaining risk:** the Alon–Boppana program is 0+1 of 5 steps — the
diameter-dependent theorem itself (Steps 2–5) is future runs; this
delivery's statements are interface-level, and their QA pins are
small-fixture (the theorem-shaped witnesses are Steps 3–5 work per
the proposal's own QA plan). One record gap inherited and flagged:
the signed-graphs delivery (`7ca544b`) is missing its index-map
section (`index/map/spectral_graph.md` has no `Signed` rows — its
117-line index diff covered only the irregular/multiway deliveries);
repairing it is a bounded records task for the next run touching the
index map. The radar's axis scores deliberately unchanged (Step 1 is
interface work; the axis claim moves when the theorem lands).

**Next milestone (open):** per priority item 0 — Alon–Boppana
**Step 2** (the `levE`/`levClass` module-level definitions and the
tree-ball predicate per the Step-0 verdict, one step per run), or the
sparsification High row's Step-0 survey; otherwise the Medium-High/
Medium rows (empirical-stationary-distribution Step 0; the sampled-
Laplacian quadratic-form consumer; the Fiedler-subspace
Davis–Kahan Step-0 check against the delivered Band family).

------

## Delivered milestones (most recent first)

**Signed graphs — the balance theorem via the magnetic π-flux bridge,
plus the switching similarity; `proposals/signed-graphs-balance.md`,
run 1, 2026-08-26, run `20260826T194844Z-run-1` (committed as part of
`7ca544b`; records closed retrospectively by run
`20260826T215003Z-run-1` after the session exited post-commit):
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/sg_axcheck.lean` on all 93 audited
declarations — 32 public (28 `Signed.lean` + 4 `Magnetic.lean`'s new
kernel section) + 61 QA: exactly `propext, Classical.choice,
Quot.sound`, every one; re-confirmed by the closing run against the
committed state). QA 2444 → 2506 (+62, `Signed_QA` a new file).**

Delivered: the new `GraphTheory/Signed.lean` — `signedAdj`/
`signedLaplacian` (`D − A_σ` at a `{±1}` signing `s`, loop-unsigned
by balance itself), `IsBalanced` (switching existence), `signFlux`
(the π-flux potential), the entrywise magnetic join
`magneticLaplacian_signFlux_apply`, the signed Dirichlet energy
identity **derived from the delivered `magnetic_energy`** (the
load-bearing join; real and complex forms), the row-sum identity, the
kernel↔alignment characterization, the walk collapse to a switching
function, the **Harary balance headline**
`isBalanced_iff_exists_ne_zero_mulVec_eq_zero` (on connected symmetric
nonnegative input), positive definiteness under frustration
(`quadForm_pos_of_ne_zero_of_not_isBalanced`), and the switching
similarity `diagonal_mul_signedLaplacian_mul_diagonal` with two-way
eigenpair transfer; plus `Magnetic.lean`'s kernel-at-action-level
section (`magneticLaplacian_mulVec_eq_zero_iff`). QA: the balanced
path (iff both directions, kernel pinned to the switching, energy
pins real+complex), the frustrated triangle (`¬IsBalanced` proved from
the switching equations, kernel trivial two routes), the disconnected
conclusion-level fence, the negative-loop boundary, the `hnn`
mechanism fence, the switching/eigen-transfer pins at the independent
path eigenpair. Records (in `7ca544b`): scoreboard (two verification
rows + interpretation bullet; full build ✔ 2386/2387 + completeness
111/111), radar axis 1 (signed category occupied), backlog, README,
index map, the proposal COMPLETE; the terminal activity entry and
this plan's retirement closed by the next run. Nothing further
committed by the closing run.

------

**The ρ_k partition-minimum packaging — the classical λ_k ≤ 2ρ_k
statement form at the delivered every-family certificate;
`proposals/multiway-expansion.md` (the follow-on delivery record),
run 1, 2026-08-26, run `20260826T181445Z-run-1`; selected per the
empty High/Medium Active table by the center-out policy as the
standing handoff's named top candidate (the multiway hard direction
stays gated on a named consumer): DELIVERED — pure hard crust, zero
new axioms (count stays 10; `#print axioms` via `wip/rho_axcheck.lean`
on all 34 audited declarations — 9 public + 25 QA: exactly `propext,
Classical.choice, Quot.sound`, every one). QA 2422 → 2444 (+22 in
`MultiwayCheeger_QA.lean`, the file 73 → 95 by the generator
metric). Radar axis 4 raised 4.5 → 5.0 at the pre-recorded trigger
(the ρ_k packaging OR the multiway hard direction).**

**Delivered** (a new "The ρ_k packaging: the partition minimum"
section of `GraphTheory/Multiway.lean`; no new imports, no umbrella
change): `IsMultiwayPartition` (nonempty, pairwise disjoint, covering
— the partition predicate the every-family form deliberately did not
need), `maxPartConductance` (the `sSup` of the part-conductance range;
`k = 0` the documented junk value), `finset_univ_sup'_eq_sSup_range`
(the join to the delivered theorems' `sup'` statement shapes — ℝ's
conditional completeness rules out `iSup` syntax, so the packaged
definition is `sSup`-based with the bridge proved once),
`maxPartConductance_const`, `multiwayExpansion A k := sInf` over the
k-way partitions' maxima (the classical ρ_k / k-way expansion
constant; `k > card V` the documented `sInf ∅ = 0` junk,
hypothesis-gated), `multiwayExpansion_le` (the `csInf` bound at
finiteness-supplied `BddBelow`), **attainment**
`exists_isMultiwayPartition_eq_multiwayExpansion` (`Set.Nonempty.csInf_mem`
at the value set's finiteness — a subset of the range over the
Fintype of k-part families; attainment is the packaging's *only* new
content, exactly as priced), the headline **`cheeger_upper_bound_multiway_rhoK`**
(`evals (L_sym) ⟨k−1⟩ ≤ 2 · multiwayExpansion A k` at `2 ≤ k ≤ card V`
with a partition — the classical Lee–Gharan–Trevisan statement form,
the every-family conductance theorem consumed at the attained
minimizer, no new engine), and the existence supplier
`exists_isMultiwayPartition_of_le_card` (injection `Fin k ↪ V` via
`Function.Embedding.nonempty_of_card_le` + complement-absorbing last
part, discharging the headline's `hex` in the common case).

**QA (+22), non-circular:** the C₄ second-eigenvalue pin **λ₂ (L_sym
C₄) = 1 with both sides independent** — `≤ 1` by the counting bridge
`evals_le_of_card_eigvalOf_le` at the kernel witness `√D·1` (through
the shelf supplier `normalizedLaplacian_mulVec_degreeSqrt_onesVec`)
and the raw-entrywise mode `![1,0,−1,0]` at `1`, two distinct
eigenbasis indices; `≥ 1` by the sInf engine
`secondEval_variational_of_ker` at `√D·1` with the entrywise
quadratic-form identity `xᵀL_sym x = ∑xᵢ² − (x₀+x₂)(x₁+x₃)` (every
constraint-set Rayleigh quotient is `‖x‖² + (x₀+x₂)² / ‖x‖² ≥ 1`;
nonemptiness witnessed by the mode at Rayleigh exactly `1`); the
star instance **ρ₂(C₄) = 1/2 exact** (the adjacent-pair partition
witness above, the headline joined to the pinned λ₂ below — a broken
attainment, a wrong constant, or a wrong minimum breaks the
equality); **the minimum is not vacuous** (`ρ₂ = 1/2 < 1 =
maxPartConductance` at the diagonal partition, conductance `4/4 = 1`
computed raw — attainment exercised, not decorated); `ρ₂(K₂) = 1` and
`ρ₃(P₃) = 1` at the pre-existing independent top-eigenvalue pins
(with the P₃ singleton-conductance pins `2/min(2,2)`, `1/min(1,3)`
computed raw); the **empty-set junk fence** — no 3-partition of two
vertices exists (a chosen point per part is an injection `Fin 3 ↪
Fin 2`), so `ρ₃(K₂) = sInf ∅ = 0` (`Real.sInf_empty`, the junk
convention the subgaussian repair documents) — partition-existence
load-bearing, not decorative; and the supplier instance at `3 ≤ 4`.

**Verification:** spike first (`wip/rho_spike.lean`, module side and
QA side iterated to zero errors/warnings before any module touched;
technique findings recorded in the proposal's delivery record — the
`sSup`-of-range shape forced by ℝ's conditional completeness,
`csInf_le`'s `BddBelow` from finiteness, `le_csInf` taking
nonemptiness, `Set.Nonempty.csInf_mem` for attainment, the
`disjoint_insert`/`disjoint_singleton` argument-order pair, the
namespace-reopening trap (a second `namespace
SpectralGraphTheory.MultiwayQA` inside a still-open
`SpectralGraphTheory` lands declarations in the *doubled* namespace),
and `sup'`-H-witnesses blocking `rw` across statements — bounds
derived by `le_trans` at one's own H instead); `lake env lean` —
zero errors/zero warnings on both changed modules; explicit `lake
build` targets ✔ (module 2191/2191, QA 2192/2192; the axcheck hit
the stale-olean trap once — unknown QA identifiers until the explicit
QA-target rebuild, the documented remediation); `#print axioms` via
`wip/rho_axcheck.lean` — the standard three only, all 34; **full
`lake build` ✔ (2385/2386, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 109/109
fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass after the record
sweep; scoreboard regenerated idempotent (**2444/10/0**, md5-stable).
Records updated: the proposal (the follow-on delivery record + the
status header), `proposals/README.md` (the Delivered row; the
natural-candidates paragraph), README (2444; the status-paragraph
clause; the module-table clause; the radar-snapshot table synced),
the radar (QA axis synced 2422 → 2444 across 57 modules; axis 4
raised 4.5 → 5.0 at the pre-recorded trigger with the reason
amended in place), the scoreboard (four verification rows + the
interpretation bullet), the index map (the Multiway section's six
new rows + the intro clause), backlog item 3 (the delivery update;
the residue narrowed to the hard direction alone), the module and
QA docstrings, this plan, and the activity log. Nothing committed;
the prior runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** see the Active milestone block above.

------

## Delivered milestones (most recent first)

**Multiway expansion — the higher-order Cheeger easy direction's
every-family form; `proposals/multiway-expansion.md` (new this
delivery, COMPLETE); opened by run 1, 2026-08-26, run
`20260826T083858Z-run-1` (the Step-0 verdict in the proposal before any
shelf Lean, plus the full spike `wip/mw_spike.lean`), landed by
continuation `20260826T133118Z-run-1` (engine, application layer,
headlines, QA, scoreboard regeneration — session ended before
verification), verified and recorded by continuation
`20260826T165654Z-run-1`; selected per the empty High/Medium Active
table by the center-out policy as the standing handoff's named top
candidate, priced as a multi-run program whose Step-0 dissolved both
obstructions and collapsed it to one delivery: DELIVERED — pure hard
crust, zero new axioms (count stays 10; `#print axioms` via
`wip/mw_axcheck.lean` on all 33 audited declarations — 15 public + 18
QA: exactly `propext, Classical.choice, Quot.sound`, every one,
re-run by the closing run after the final source state). QA
2349 → 2422 (+73, `MultiwayCheeger_QA` a new file).**

**Delivered:** (1) the k-general engine in `Spectral.lean` — the
order-statistics↔counting bridge `evals_le_of_card_eigvalOf_le` (the
shelf had only the two endpoint instances), the general-k subspace
Rayleigh–Ritz engine `evals_le_of_linearIndependent` (a k-dimensional
linearly independent family whose every combination satisfies
`quadForm ≤ t · ‖·‖²` certifies `evals ⟨k−1⟩ ≤ t` — no PSD, no kernel
hypothesis; the k−1 smallest-eigenvalue eigenvectors impose at most k−1
constraints, so a nonzero survivor exists by
`LinearMap.ker_ne_bot_of_finrank_lt`), plus the QA-support spin-offs
`evals_sum_eq_trace` and `exists_eigvalOf_eq_of_mulVec_eq_smul` (the
eigenvalue-witness bridge QA uses to pin spectra without computing
them); (2) the new `GraphTheory/Multiway.lean` (umbrella import; no
other module touched) — `partIndicator`/`multiwayCombination` (the
plain *uncentered* part indicators — the Step-0 verdict: no centering
anywhere), the per-part energy identity
`quadForm_laplacian_partIndicator` (`xᵀLx = boundary`, load-bearing on
`laplacian_quadForm`), the weighted-norm identity, the absorption lemma
`laplacian_quadForm_multiwayCombination_le` (`xᵀLx ≤ 2 ∑ cᵢ²
boundary(Sᵢ)` — each crossing pair pointwise at `(a−b)² ≤ 2a² + 2b²`;
the theorem's constant 2 is exactly this absorption constant), and the
headlines `cheeger_upper_bound_multiway` / `_conductance`
(`evals (L_sym) ⟨k−1⟩ ≤ 2 · maxᵢ boundary(Sᵢ)/vol(Sᵢ)`, resp.
conductance at `2 ≤ k`, for every disjoint nonempty k-family on every
symmetric nonnegative positive-degree graph — the every-family form:
no partition-space attainment, no ρ_k minimum; the delivered irregular
pair is the k = 2 instance); (3) QA at the proposal's six obligations —
the tight k = n equalities on K₂ (`2 = 2·1`, both forms, against the
raw anti-aligned-eigenvector pin) and the all-rational C₄ (`λ₄ = 2
= 2·1` by alternating vector + trace-`4`), the P₃ non-covering family
(the every-family scope exercised), the P₃ k = 3 singleton partition
with `λ₃ = 2` pinned by trace arithmetic + the raw eigenvector
`![1, −√2, 1]` through the new spin-off bridges, the k = 1
zero-constraint edge, absorption pinned at *equality* on both fixtures,
and the C₄ cyclic-pair **overlap fence** — every other hypothesis
verified (φ = 1/2 each, raw), disjointness provably failing, the
dropped conclusion refuted at `2 > 1`.

**Verification (the closing run, from scratch):** `lake env lean` —
zero errors on `Spectral.lean` (8 warnings, all pre-existing in HEAD;
the new engine block adds none), `Multiway.lean`, and the QA file (zero
warnings); explicit `lake build` targets ✔ (the three changed modules);
`#print axioms` via `wip/mw_axcheck.lean` — the standard three only,
all 33; **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 109/109 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass after the record sweep; scoreboard
regenerated idempotent (**2422/10/0**, md5-stable). Records updated:
the proposal (COMPLETE header + delivery record with technique notes),
`proposals/README.md` (the Delivered row; the natural-candidates
paragraph re-ranked), README (2422; the status-paragraph clause; the
module-table clause), the radar (QA axis synced 2349 → 2422 across 57
modules; axis 4's multiway clause — held 4.5 with the explicit
protocol reason and the named 5.0 trigger), the scoreboard (two
verification rows + the interpretation bullet), the index map (the
Multiway section + 4 engine rows + the status line), backlog item 3
(the delivery update + the re-priced residue), this plan, and the
activity log (the continuation run's terminal entry — left unwritten
by its session — plus this run's). Nothing committed; the prior runs'
uncommitted deliveries preserved untouched.

**Next milestone (open):** see the Active milestone block above.

------

## Delivered milestones (most recent first)

**The irregular Fiedler instantiation — the irregular Cheeger family's
algorithm-facing capstone, `cheeger_sweep_cut_normalized` at its first
eigenvector input;
`proposals/irregular-cheeger-variational-transfer.md` (the follow-on
delivery record), run 1, 2026-08-26, run `20260826T064300Z-run-1`;
selected per the empty High/Medium Active table by the center-out
policy as the standing handoff's named *bounded* candidate (the other
named candidate, multiway expansion, priced — in this plan's prior
Active block — as a multi-run program this run deliberately did not
start): DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/ifc_axcheck.lean` on all 23 audited
declarations — 14 public + 9 QA: exactly `propext, Classical.choice,
Quot.sound`, every one). QA 2340 → 2349 (+9 in
`IrregularCheeger_QA.lean`).**

**Delivered** (a new "The irregular Fiedler instantiation" section of
`GraphTheory/VariationalTransfer.lean`; no new imports, no umbrella
change): the normalized-Laplacian Fiedler interface
(`fiedlerIndexNormalized`/`fiedlerIndexNormalized_eigvalOf` — the
`Fiedler.lean` pattern at `L_sym`; `fiedlerVectorNormalized` with the
eigen equation, unit norm, nonvanishing, `quadForm`/`rayleigh` both
`λ₂`) and the sweep vector `fiedlerSweepVector := degreeInvSqrt A *ᵥ u`
(the `D^{-1/2}` pullback — the generalized eigenfunction of `(L, D)`
at `λ₂`, the vector the spectral-partitioning algorithm actually
sorts), with the stretch cancellation `√D f = u`
(`degreeSqrt_mul_degreeInvSqrt`), nonvanishing, and the **constraint
conversion** `fiedlerSweepVector_sum_deg_eq_zero`: the sweep family's
own hypothesis `∑ i, deg A i * f i = 0` *obtained* from the
eigen-orthogonality hinge `eigvecOf_ortho_of_mulVec_eq_zero` at the
true kernel vector `√D·1` (`0 < λ₂` from the delivered connectivity
transfer — connectivity's exact entry point) rather than assumed. The
headline **`fiedler_sweep_cut_normalized`**: on every connected
symmetric nonnegative positive-degree graph with `2 ≤ card V`, an
explicit nonempty proper closed superlevel/sublevel cut **of the sweep
vector itself** with `conductance A S ^ 2 ≤ 2 * λ₂ (L_sym)` — the
classical `√(2λ₂)` scale, exactly the regular family's
`fiedler_sweep_cut` constant `2 lambda2 / d` on the regular cone.
Load-bearing joins: the constraint shape (an unweighted zero-sum shape
would fail the sweep hypothesis), the stretch cancellation and
`fiedlerVectorNormalized_rayleigh` (the spectral side closes at the
eigenvector, not at any hand-built test vector), and the
connectivity-supplied gap.

**QA (+9):** the exact pin `icPathAdj_secondEval_eq_one` — `λ₂ (L_sym
P₃) = 1`, the new `≥ 1` side (`icPathAdj_secondEval_ge_one`) by the
`2 x₁²` sum-of-squares through `secondEval_variational_of_ker` (the
sInf set's nonemptiness witnessed by the concrete eigenpair
`![1, 0, -1]` at Rayleigh exactly `1`; the `≤ 1` eigenpair side
predates the whole Fiedler family — non-circular, and the family's
Cheeger bracket on `P₃` collapses to `1/2 ≤ 1 ≤ 2`); the instances
`ifc_p3_instance_QA` (at the exact pin and the exhaustive
all-cuts-are-`1` pin) and `ifc_edge_instance_QA` (at the pinned
classical `λ₂ = 2`, singleton conductance `1 ≤ 4`); the pullback
algebra raw at the concrete eigenpair (`ifc_pullback_cancel_raw_QA`,
`ifc_pullback_zero_sum_raw_QA` — the latter through the public pairing
identity joined to the file's independent orthogonality pin); and the
connectivity mechanism fenced (`ifc_disc_hinge_fence_QA` with the
block-indicator kernel witness and the degree pins): on the
disconnected fixture `λ₂ = 0` (the file's two-route pin) and a nonzero
kernel eigenvector of `L_sym` pairs to `2 ≠ 0` with `√D·1` —
kernel-ness provably does not supply the hinge (the conclusion-level
statement is not falsifiable there, since a kernel vector's sweep may
find a conductance-`0` component cut — the fence lives at the
mechanism, exactly where the hypothesis enters).

**Verification:** spike first (`wip/ifc_spike.lean` + QA spike
`wip/ifc_qa_spike.lean`, the full routes green before any module
touched; technique findings recorded in the proposal's delivery
record: the scoped `Matrix` notation in standalone files; `le_csInf`
taking the set's nonemptiness in this pin — witnessed by the concrete
eigenpair, itself a meaningful pin; the matrix-literal/degree
evaluation recipe; `Real.sqrt_ne_zero'.mpr`; `linear_combination` for
`√2`-comm rearrangements; unary-minus shaping in scalar lemmas; the
stale-olean rebuild-before-axcheck trap hit once and remediated by the
explicit QA target); `lake env lean` zero errors/zero warnings on both
changed modules; explicit `lake build` targets ✔ (module 2190/2190,
QA 2193/2193); `#print axioms` on all 23 — the standard three only,
re-run after the final source state; **full `lake build` ✔ (2384/2385,
"Build completed successfully") immediately followed by
`check_build_completeness.py` — 107/107 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2349/10/0**,
idempotent by md5). Records updated: the proposal (the follow-on
marked delivered + the Fiedler-instantiation delivery record with
technique findings), `proposals/README.md` (the Delivered row; the
natural-candidates paragraph re-ranked with multiway's multi-run
pricing), README (2349; the module-table clause), the radar (QA axis
synced 2340 → 2349; the axis-4 Fiedler-instantiation clause, held 4.5
with the protocol reason), the scoreboard (two verification rows + the
interpretation bullet), `index/map/spectral_graph.md` (the
Fiedler-instantiation section + 9 declaration rows), backlog item 3
(the update + the multiway pricing), the module and QA docstrings,
this plan, and the activity log. Nothing committed; the prior runs'
uncommitted deliveries preserved untouched.

**Next milestone (open):** see the Active milestone block above.

------

## Delivered milestones (most recent first)

**The volume-weighted sweep-cut extraction — the irregular Cheeger
pair's explicit witness level set, the regular family's attainment
route ported to the volume measure;
`proposals/irregular-cheeger-variational-transfer.md` (the follow-on
delivery record), run 1, 2026-08-26, run `20260826T045752Z-run-1`;
selected per the empty High/Medium Active table by the center-out
policy as the top natural candidate named in the standing handoff:
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/vsc_axcheck.lean` on all 13 audited
declarations — 2 public + 11 QA: exactly `propext, Classical.choice,
Quot.sound`, every one). QA 2330 → 2340 (+10 in
`IrregularCheeger_QA.lean`, the file 166 → 176).**

**Delivered** (two new sections, no new modules, no new imports, no
umbrella change): `sweep_level_extract_vol` — `Cheeger.lean`'s new
`VolumeSweepExtraction` section: for any `y` whose nonempty closed
superlevel sets at positive levels are volume-minority-side with
positive degree-weighted mass, a positive level `t` whose closed
superlevel set `S = {i : t ≤ y i ^ 2}` is nonempty, proper, and
satisfies `conductance A S ^ 2 ≤ E'(y) / ∑ i, deg A i * y i ^ 2` — the
regular extraction's attainment route (`Finset.exists_min_image`) at
the `boundary / vol` ratio (card denominator replaced by the level
set's volume, positivity from `vol_pos_of_pos_deg` at the attained
witness), the degree-weighted layer-cake integration a structural
clone of `coarea_core_vol`'s own proof (`sum_deg_mul_indicatorLE_eq_vol`
the mass side, `sum_pairAbs_eq_two_boundary` the pair side), closed by
the already-degree-weighted Component A `core_sum_abs_sq_sub_sq` and
the minority-volume conversion `min (vol S) (vol Sᶜ) = vol S` (pure
`vol_compl` arithmetic — no `vol_eq_of_regular` anywhere); no `2 ≤
card V` hypothesis (minority at a nonempty level forces the complement
nonempty). And `cheeger_sweep_cut_normalized` —
`VariationalTransfer.lean`'s new irregular-sweep-cut section, placed
with the family: every nonzero degree-weighted zero-sum `f` has a
nonempty proper closed superlevel or sublevel cut of `f` itself — a
member of the sweep family the spectral-partitioning algorithm
actually enumerates — with `conductance A S ^ 2 ≤ 2 * R_{L_sym}(√D
f)`: the volume median feeding the extraction's hypothesis verbatim
for both parts (`minority_{pos,neg}Part_vol`), the product test with
degenerate single-part cases, the fused contraction
(`sum_edgeWeight_sq_posPart_add_sq_negPart_le`) and weighted norm
split (`median_parts_norm_vol`) consumed verbatim, the closing
normalization `2 * R_{L_sym}(√D f) = E'(f) / ∑ deg f²`, and the
`mem_of_{pos,neg}Part_sq` level conversions at the offset `√t` —
exactly the hard direction's own constraint shape. **The whole
delivered `VolumeHardDirection` layer is consumed a second time; it
now carries weight from two theorem families.**

**QA (+10):** the extraction witness *forced* on the genuinely
irregular `P₃` fixture at `y = ![1, 0, 0]` (the level-membership iff
pins the returned set to `{0}`, conductance `1` from the file's
exhaustive-cut pin, the bound `1 ≤ 2/1` both sides computed raw); the
sweep instances on the pair's shared `P₃` cut test vector (the family
characterization proved in-instance — `{0}` superlevel, `{1, 2}`
sublevel the only nonempty proper members — so `1 ≤ 8/3` at the
independently pinned `R = 4/3`: one test object now consumed by both
Cheeger directions *and* the sweep) and on `K₂` (`1 ≤ 4` at the pinned
`R = 2`, both family members characterized); and the degree-weighted
zero-sum fence in proved form (`f = ![1, 2]` on `K₂`: `∑ deg · f = 3
≠ 0`, exactly two nonempty proper swept members each of conductance
`1`, the demanded bound `1 ≤ 2 * (1/5)` with `R = 1/5` computed raw —
refuted for *every* candidate, `horth` isolated exactly).

**Verification:** spike first (`wip/vsc_spike.lean`, both routes green
before any module touched — the per-part extraction on its first
elaboration after one tactic trim; technique findings recorded in the
proposal's delivery record: the
`Fin.exists_eq_zero_or_eq_one_or_eq_two` name gap closed by a local
`fin_cases` clone, entry-fact lemmas replacing depth-2 matrix-literal
`simp only` reductions inside inline `linarith` blocks, `▸`-direction
equality transports at `Fin` cases, and `laplacian_quadForm` needing
its proof argument explicit in `rw`); `lake env lean` zero
errors/zero warnings on both changed public modules and the QA file;
explicit `lake build` targets ✔ (module 2190/2190, QA 2193/2193);
`#print axioms` on all 13 — the standard three only, re-run after the
final source state; **full `lake build` ✔ (2384/2385, "Build completed
successfully") immediately followed by `check_build_completeness.py`
— the fence earned its keep again mid-verification (the QA docstring
edit after its last target build left the artifact STALE under a
passing full build; the documented remediation — the explicit QA
target's real 2193-target re-elaboration, then a fresh full build —
closed it): 107/107 fresh, 0 stale, 0 missing, exit 0**;
`lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2340/10/0**,
idempotent by md5). Records updated: the proposal (the follow-on
marked delivered + the sweep-extraction delivery record),
`proposals/README.md` (the Delivered row; the natural-candidates
paragraph re-ranked), README (2340; the status-paragraph sweep clause;
the module-table clause), the radar (QA axis synced 2330 → 2340; the
axis-4 sweep-extraction clause, held 4.5 with the protocol reason),
the scoreboard (two verification rows + the interpretation bullet),
`index/map/spectral_graph.md` (the VT table row, the extraction
section + row), backlog item 3 (the update), both module docstrings
and the QA header, this plan, and the activity log. Nothing committed;
the prior runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** see the Active milestone block above.

------

## Delivered milestones (most recent first)

**The connectivity transfer — `0 < λ₂(L_sym) ↔ connected`; the
irregular-Cheeger delivery's top priced follow-on;
`proposals/irregular-cheeger-variational-transfer.md` (follow-on
delivery record), run 1, 2026-08-26, run `20260826T024528Z-run-1`;
selected per the empty High/Medium Active table by the center-out
policy as the top natural candidate named in the standing handoff:
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/ctc_axcheck.lean` on all 31 audited
declarations — 7 public + 24 QA: exactly `propext, Classical.choice,
Quot.sound`, every one). QA 2280 → 2330 (+50 in
`IrregularCheeger_QA.lean`, the file 116 → 166).**

**Delivered** (a new "The connectivity transfer" section of
`GraphTheory/VariationalTransfer.lean`; no new imports, no umbrella
change): the algebra layer (`degreeSqrt_mul_normalizedLaplacian` — the
left-multiplied congruence `√D · L_sym = L · D^{-1/2}` — and the
kernel-cone lift
`normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero`),
**the kernel characterization**
`normalizedLaplacian_mulVec_eq_zero_iff` (on connected input the
normalized kernel is exactly the stretched-constant line — the
proposal's named "natural entry" now in iff form, consuming the
electrical program's `laplacian_mulVec_eq_zero_iff_exists_const`), the
**Fiedler mirror** `secondEval_normalizedLaplacian_pos_of_connected`
(the combinatorial `lambda2_pos_of_connected`'s normalized analogue:
PSD pin + sorted + the double-bottom multiplicity pin +
orthonormality contradiction), the **disconnected converse**
`secondEval_normalizedLaplacian_eq_zero_of_not_connected` (component
indicator → combinatorial kernel → cone lift → Gram–Schmidt against
`√D·1` → the delivered `secondEval_le_rayleigh_of_ker` + PSD → `λ₂ =
0` exactly), the **packaged equivalence**
`secondEval_normalizedLaplacian_pos_iff_connected` (algebraic
connectivity *is* connectivity in the volume-weighted world), and the
**Cheeger consumer corollary** `cheegerConstant_pos_of_connected`
(`0 < λ₂ ≤ 2φ` through the delivered easy direction — the pair's
positivity content made explicit on connected irregular graphs).

**QA (+50):** the P₃ positive instance joined to the file's
independent eigenpair bracket (`0 < λ₂ ≤ 1`, non-circular); the K₂
instance joined to the pinned exact `λ₂ = 2` and the corollary joins
(`0 < φ` against pinned `φ = 1` on both fixtures); the kernel iff both
directions on genuinely irregular input (span membership forced to
`c = 1`; `onesVec ∉ ker` through the iff); the **disconnected
two-edge negative witness** with `λ₂ = 0` by **two independent
routes** (the theorem; and raw kernel witness + Gram–Schmidt + engine,
no connectivity statement anywhere); the **`hconn` fence** in proved
form; and the **`hnn` fence on a connected signed fixture**
(`0,2,2;2,0,-1;2,-1,0`) — at the kernel characterization (raw kernel
vector off the stretched line) and at the headline (the engine with a
fixture-specific squares PSD supplier `xᵀLx = (x₀−x₁−x₂)²`: the
shelf's `normalizedLaplacian_psd` needs `hnn`, the engine does not —
`hnn` isolated exactly where it enters).

**Verification:** spike first (`wip/ctc_spike.lean` + QA spike, full
routes green before any module touched; technique findings recorded in
the proposal's delivery record — the protected `Reachable.refl/trans`
constructors, `mul_inv_cancel₀`'s shape, the secondEval `show`-unfold,
the stale-olean rebuild-before-QA trap hit once and remediated, and
if-ladder fixture definitions replacing depth-2 matrix-literal entry
computation); `lake env lean` zero errors/zero warnings on both
changed modules; explicit `lake build` targets ✔ (2190/2190, 2193/
2193); `#print axioms` on all 31 — the standard three only; **full
`lake build` ✔ (2384/2385 targets, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 107/107 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**2330/10/0**, idempotent by md5). Records updated: the proposal (the
follow-on marked delivered + the delivery record),
`proposals/README.md` (the natural-candidates paragraph re-ranked),
README (2330; the module-table clause), the radar (QA axis synced
2280 → 2330; the axis-3 connectivity-transfer clause), the scoreboard
(two verification rows + the review date), `index/map/spectral_graph.md`
(the section + 7 declaration rows), backlog item 3 (the update), this
plan, and the activity log. Nothing committed; the prior runs'
uncommitted deliveries preserved untouched.

**Next milestone (open):** see the Active milestone block above.

------



**Irregular Cheeger hard direction — the volume-weighted coarea/median
program, the proposal COMPLETE (both halves);
`proposals/irregular-cheeger-variational-transfer.md`, opened by run 1
2026-08-25 (`20260825T221207Z-run-1` — intent, Step-0 survey, and the
full Lean drafted before the session was interrupted), verified,
checked, and recorded by continuation run `20260826T010711Z-run-1`;
selected per the empty High/Medium Active table by the center-out
policy as the top natural candidate named in the standing handoff:
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/ich_axcheck.lean` on all 40 audited
declarations — 16 public + 24 QA: exactly `propext, Classical.choice,
Quot.sound`, every one). QA 2249 → 2280 (+31 in
`IrregularCheeger_QA.lean`, the file 85 → 116).**

**Delivered:** `cheeger_lower_bound_normalized` —
`cheegerConstant A ^ 2 / 2 ≤ secondEval (normalizedLaplacian A)` on
arbitrary symmetric nonnegative positive-degree graphs with
`2 ≤ card V` (no regularity, no connectivity, exactly the easy
direction's hypotheses — **the full Cheeger pair now holds in the
volume-weighted measure on every positive-degree weighted graph**):
(1) the `VolumeHardDirection` section of `Cheeger.lean` — the volume
arithmetic (`vol_le_vol_of_subset`, `vol_empty`), the volume median
`exists_median_vol` (the same maximizing-vertex/minimal-member Finset
argument with `vol` replacing `card`), minority conductance at volume
strength `boundary_ge_of_minority_vol` (where `min (vol S) (vol Sᶜ) =
vol S` is pure `vol_compl` arithmetic, no `vol_eq_of_regular`), the
degree-weighted mass side, the layer-cake core `coarea_core_vol`, the
per-part bound `hardDirection_perPart_vol` (the Step-0 finding holding:
the regular family's `core_sum_abs_sq_sub_sq` and fused contraction
are already degree-weighted and consumed verbatim — no regularity
bridge anywhere), the minority parts, and the weighted norm split;
(2) the general-kernel sInf engine `secondEval_variational_of_ker` in
`Spectral.lean` (Courant–Fischer at an arbitrary kernel vector `w` —
the delivered `secondEval_le_rayleigh_of_ker` reused as its hard half,
the new witness half producing an orthogonal candidate at both
`0 < λ₂` and the `λ₂ = 0` double bottom; every future irregular
consumer, whose operator is killed by `√D·1` not `1`, shares it);
(3) `VariationalTransfer.lean` (one new import — Cheeger, acyclic):
`dotProduct_degreeSqrt_mulVec_mixed`/`_onesVec` (the irregular
variational constraint: `√D x ⊥ √D·1` iff `x` has degree-weighted zero
sum), `cheeger_sweep_normalized` (the hard direction at test-vector
level), and the headline. **QA (+31):** the P₃ volume-median pins
(pinned and *forced*), the K₂ coarea equality raw and as a theorem
instance, the sweep on K₂ (`1/2 ≤ 2` against the pinned `λ₂ = 2`) and
on P₃'s cut test vector (`1/2 ≤ 4/3` — the same object the easy
direction consumed; one test object, both bounds of the pair), the
headline **joined to the easy delivery's independently pinned spectral
bracket** (`φ²/2 = 1/2 ≤ λ₂` with the eigenpair-witness `λ₂ ≤ 1` —
non-circular), the K₂ regular recovery at `λ₂ = 2` raw, and the
proved-form fences: minority-drop at the full vertex set (coarea and
boundary lemmas), nonnegativity-drop on the headline (signed adjacency
`!![2,−1;−1,2]]`, `cheegerConstant = −1`, exactly `hnn` isolated).

**Verification:** `lake env lean` — zero errors/zero warnings on all
three public modules and the QA file; `#print axioms` via
`wip/ich_axcheck.lean` on all 40 — the standard three only; **full
`lake build` ✔ (2385 targets, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 107/107 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, no issues),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**2280/10/0**, idempotent by md5). Records updated: the proposal
(status header both-halves COMPLETE + the hard-direction delivery
record), `proposals/README.md` (the Delivered row; the
natural-candidates paragraph re-ranked), README (2280; the
status-paragraph hard-direction clause; the module-table row; the
radar-snapshot table synced to the current scores — a factual repair,
it had drifted since August 22), the radar (axis 4's hard-direction
clause and the retired absent category, held 4.5 with the honest
protocol reason; the QA axis synced 2249 → 2280; the review date), the
scoreboard (two verification rows + the interpretation bullet), the
index map (the `VolumeHardDirection` rows, the
`secondEval_variational_of_ker` engine row, and the
hard-direction table under the VariationalTransfer section), backlog
item 3 (the delivery update), this plan, and the activity log.
Nothing committed; the prior runs' uncommitted deliveries preserved
untouched.

**Next milestone (open):** see the Active milestone block above.

------

## Delivered milestones (most recent first)

**Resolvent identity + general-symmetric avoidance layer — the
consumer stub's two priced follow-ons, the bridge-consumer family
closed; `proposals/hermitian-calculus-consumer-tikhonov-heat.md`,
run 1, 2026-08-25, run `20260825T203027Z-run-1`; selected per the
empty High/Medium Active table by the center-out policy as the top
remaining unblocked bridge follow-on named in the standing handoff
(and this run first closed the prior run's records gap — the
magnetic delivery's terminal activity entry and plan retirement,
both left unwritten when that session exited after committing
`fac3019`): DELIVERED — pure hard crust, zero new axioms (count
stays 10; `#print axioms` via `wip/resid_axcheck.lean` on all 17
audited declarations — 6 public + 11 QA: exactly `propext,
Classical.choice, Quot.sound`, every one). QA 2238 → 2249 (+11 in
`FunctionalCalculus_QA.lean`'s Section G, no new file).**

**Delivered:** the new "The resolvent identity" section of
`GraphTheory/FunctionalCalculus.lean` (one new import — Resolvent,
no cycle; `Tikhonov.lean` untouched): the *general-symmetric normal
equation* `add_smul_one_mul_spectralCalc_tikhonovShrinkage_of_forall_
add_ne_zero` (merely symmetric `M` under spectrum-avoidance
`x + π ≠ 0`; the delivered PSD statement re-derived from it, shape
unchanged), the *general-symmetric resolvent identity* by the
calculus route (`cfc_inv` + `Matrix.nonsing_inv_eq_ring_inverse` at
the additive layer — no determinant anywhere), the headline
`spectralCalc_tikhonovShrinkage_eq_smul_inv` (`f(L) = π • (L + π•1)⁻¹`)
by the matrix-algebra route — a three-layer load-bearing join
consuming the Aug-19 resolvent program's
`isUnit_det_add_smul_one_of_quadForm_nonneg` (its first
FunctionalCalculus consumer) with `laplacian_psd` — the
same-statement second route `'`, and the consumer corollary
`tikhonovMinimizer_eq_smul_inv_mulVec` (`x* = π • ((L+πI)⁻¹ *ᵥ y)`,
the textbook shifted-inverse solve). **QA (+11, Section G on the
shared K₂ fixture):** the raw inverse `!![2/3,1/3;1/3,2/3]]`, both
routes pinned to that same matrix (joined to Section E's calculus
instance), the minimizer three-way join to the hand-solved Gaussian
`tik_K2_eq`, the supplier witnessed (`det = 3`), and the two fences
at the `π = -2` degeneration — the avoidance failure *proved
spectral* (`2 = -π` exhibited as an eigenvalue), the singular
inverse pinned to junk zero, the identity refuted at `1/2 ≠ 0`
(`hπ`/`havoid` exactly isolated per theorem).

**Verification:** spike first (`wip/resid_spike.lean`, all routes
green before any module touched; the catches recorded in the
delivery record — section-scoped QA opens, the explicit
`IsHermitian` argument at concrete types for the spectrum rewrite,
`Matrix.inv_eq_right_inv`'s single-hypothesis shape, the entrywise
smul-slide, the stale-olean rebuild-before-QA-spike trap);
`lake env lean` zero errors/warnings on both changed files; explicit
`lake build` targets ✔ (module 2327/2327, QA 2331/2331);
`#print axioms` on all 17 — the standard three only; **full
`lake build` ✔ (2384/2385 targets, "Build completed successfully")
immediately followed by `check_build_completeness.py` — 107/107
fresh, 0 stale, 0 missing, exit 0** (re-run after the final
docstring edits, same result); `lint_axioms` (10),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**2249/10/0**, idempotent by md5). Records updated: the
proposal (delivery record + family-closed pricing), the prior
magnetic run's terminal records (this run), `proposals/README.md`
(the Delivered row; the progress paragraph; the natural-candidates
paragraph — the family closed, irregular-Cheeger hard now the top
named candidate), README (2249; the status-paragraph clause; the
module-table row), the radar (QA row synced 2216 → 2249 across 56
modules, repairing the stale count the magnetic delivery left), the
scoreboard (two verification rows + the interpretation bullet),
`index/map/spectral_graph.md` (+5 declaration rows + the delivery
paragraph), the module docstring, this plan, and the activity log.
Nothing committed.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the **irregular-Cheeger hard direction** (the
delivered easy direction's own priced follow-on: the volume-weighted
coarea/median program for `φ²/2 ≤ λ₂`), the standing gated
candidates (directed-axis rate; magnetic spectral, each gated on a
named consumer), a named consumer pricing the wide-band minimax
filter designs, or a fresh center-out candidate per
`docs/6_SGT_BACKLOG.md`.
------

## Delivered milestones (most recent first)

**Magnetic heat propagator — the bridge's first complex consumer;
`proposals/hermitian-calculus-consumer-magnetic.md` COMPLETE; run 1,
2026-08-25, run `20260825T180957Z-run-1`; DELIVERED and committed as
`fac3019` (the session exited after committing but before appending
its terminal activity entry and retiring this plan's Active block —
both records closed by the next run, `20260825T203027Z-run-1`, on the
evidence below; no source gap resulted, the commit itself carries the
verification record): DELIVERED — pure hard crust, zero new axioms
(count stays 10; `#print axioms` via `wip/magcfc_axcheck.lean` on all
30 audited declarations — 8 public + 22 accessible QA: exactly
`propext, Classical.choice, Quot.sound`, every one). QA
2216 → 2238 (`MagneticCalculus_QA` a new file).**

**Delivered** (a new section of `GraphTheory/FunctionalCalculus.lean`;
`Magnetic.lean` untouched per the consumer pattern; one new import —
Magnetic): `magneticHeat A Θ t` — the calculus of the delivered
`magneticLaplacian` at `x ↦ e^{-t·x}` through Mathlib's
`RCLike`-generic `cfc` at 𝕜 = ℂ directly, hypothesis-free for any
directed weights and phases; the substantive general lemma
**`cfc_mulVec_eq_smul_of_mulVec_eq_smul`** — the calculus acts at
eigenvalues on EVERY eigenvector, proved by pure matrix algebra
through the unitary diagonalization `Uᴴ * M * U = diagonal λ` with no
eigenspace-completeness machinery (Mathlib's CFC file lacks it; every
downstream complex consumer needs it); the entry form, the
arbitrary-eigenvector action, the basis action (the proposal's literal
ask), time zero, and the semigroup through the generic calculus
algebra. QA +22: the flux pair `K₂` at antisymmetric phase π/2 with
the closed form `½!![1+q, I(1−q); −I(1−q), 1+q]]` at `q = e^{-2t}`
derived on the calculus route and verified by raw matrix arithmetic,
the gauge-characterization cross-check, the diffusion fence
(`magneticHeat … 1 ≠ 1`), and the zero-phase join to the delivered
real `heatKernel`.

**Verification (recorded in the delivery commit and the scoreboard
rows dated 2026-08-25):** full `lake build` ✔ (2385 targets)
immediately followed by `check_build_completeness.py` — 107/107
fresh, 0 stale, 0 missing, exit 0; `lint_axioms` (10),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (2238/10/0). Records updated in that commit: the proposal
(COMPLETE header + delivery record), `proposals/README.md` (the
Delivered row + the progress paragraph naming the resolvent identity
the top remaining unblocked follow-on), README (2238), the scoreboard,
`index/map/spectral_graph.md`, this plan, and the activity log's
in-progress entry.

**Next milestone (selected):** the resolvent identity (the active
block above) — this delivery's own recorded next candidate.
------

## Delivered milestones (most recent first)

**Heat recovered as a functional-calculus instance — the bridge's
falsifiability test at its second consumer, and the reconciliation
with genuine mathematical content; the consumer stub COMPLETE, both
halves delivered; `proposals/hermitian-calculus-consumer-tikhonov-heat.md`,
the Heat half (run 1, 2026-08-25, run `20260825T163517Z-run-1`; the
Tikhonov sibling's own priced follow-on, selected per the empty
High/Medium queue by the center-out policy as the top natural
candidate named in all three standing handoffs — the one-per-delivery
rule's indexing-and-pursuit decision made and recorded in this plan's
active-milestone block at the boundary): DELIVERED — pure hard crust,
zero new axioms (count stays 10; `#print axioms` via
`wip/heatcfc_axcheck.lean` on all 15 new declarations — 4 public +
11 QA: exactly `propext, Classical.choice, Quot.sound`, every one).
QA 2205 → 2216 (+11 in `FunctionalCalculus_QA.lean`'s Section F, no
new file).**

**Delivered:** the "Recovered instances: the heat semigroup" section
of `GraphTheory/FunctionalCalculus.lean` (`Heat.lean` untouched per
the stub's non-goals; one new import — Heat, no cycle; no umbrella
change): the action-equality helper `matrix_eq_of_forall_mulVec_eq`
(matrices are their `mulVec` actions; entries recovered at
`Pi.single j 1`), the headline `heatKernel_eq_spectralCalc_exp`
(`heatKernel A t = spectralCalc (laplacian A) hL (fun x =>
Real.exp (-(t * x)))` under `A.IsSymm` — the two sides built by
independent proof stacks: `Heat.lean`'s from-scratch entrywise
exponential-series machinery against Mathlib's `cfc`, joined at the
shared filter-sum shape — in effect the spectral mapping theorem for
`exp` at real-symmetric matrices, the reconciliation the parent
proposal's Step-0 pricing predicted would carry content where
Tikhonov's was an identity of definitions), and the substantive
second layer `spectralCalc_exp_mul` (the semigroup at the exponential
family through the generic calculus algebra: `cfc_mul` then
`cfc_congr` promoting pointwise `Real.exp_add` from the spectrum,
eigenbasis-free) composed into `heatKernel_mul_heatKernel_of_spectralCalc`
(a second proof technology for `Heat.lean`'s hypothesis-free
`heatKernel_mul_heatKernel`, the `Matrix.exp_add_of_commute` route;
docstring records honestly that this route needs `A.IsSymm` where the
original does not).

**QA (+11, Section F on the same `Tikhonov_QA` K₂ fixture as Section
E — the two consumer reconciliations pinned against one shared,
independently delivered eigenbasis):** the closed form
`!![(1±e^{-2t})/2]` by **two independent routes**
(`fc_heat_K2_calculus_route` through the equality theorem + the
Section-E master lemma vs `fc_heat_K2_series_route` through
`heatKernel_mulVec_eq_sum` + the sign-free outer-product pins — no
`cfc` anywhere on that route); the semigroup at times `1, 2` by
**two independent routes** (`_calculus` through the new chain vs
`_commute` through the delivered law) plus `_pin` (both deliver the
entries `(1±e^{-6})/2`) and `_raw` (the literal closed-form product
check, `Real.exp_add` the only scalar input); time zero preserved
through the calculus; eigenmode decay through the calculus action
interface at both modes (the calculus-side mirror of the series-route
`heatKernel_mulVec_eigvecOf`); and the **nontriviality fence**
`fc_heat_K2_not_one` — `heatKernel K₂ 1 ≠ 1`, entry `(1 - e^{-2})/2
> 0` since `Real.exp_lt_exp` gives `e^{-2} < 1`: diffusion provably
moves mass, refuting any degenerate constant-collapse reading of the
equality theorem.

**Verification:** spike first (`wip/heatcfc_spike.lean` +
`wip/heatcfc_qa_spike.lean`, the full routes green before any module
touched — the catches recorded in the proposal's delivery record:
`Real.exp_add`'s direction at this pin needs `← Real.exp_add` for
the product-to-sum step; the `fin_cases` redex trap in the raw
product lemma closed by `Matrix.mul_apply`/`Fin.sum_univ_two`
pre-rewrites plus per-branch definitional `show`s at numeral indices,
plus a factor-2 correction in the off-diagonal `linear_combination`
certificates); `lake env lean` zero errors/warnings on both changed
files; explicit `lake build` targets ✔ (module 2309/2309, QA
2313/2313); `#print axioms` via `wip/heatcfc_axcheck.lean` on all 15
— the standard three only; **full `lake build` ✔ (2385 targets,
"Build completed successfully") immediately followed by
`check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (**2216/10/0**, idempotent by md5).
Records updated: the proposal (both-halves COMPLETE header + the Heat
delivery record with the pin-technique findings and post-Heat priced
follow-ons), `proposals/README.md` (the Delivered row extended to
both halves; the progress paragraph; the natural-candidates closing
paragraph now headed by the magnetic heat propagator), README (2216;
the status-paragraph bridge clause and the FunctionalCalculus
module-table row extended to the second consumer), the radar (QA axis
synced 2205/55 → 2216/55, held 4.0), the scoreboard (two verification
rows + the interpretation bullet), `index/map/spectral_graph.md`
(+4 declaration rows + the second-consumer reconciliation paragraph),
this plan, and the activity log. Nothing committed; the prior runs'
uncommitted deliveries preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the magnetic heat propagator (the second consumer
stub, now the top named candidate), the resolvent identity (the
consumer stub's priced follow-on), the irregular-Cheeger *hard*
direction, the standing gated candidates (directed-axis rate; magnetic
spectral; a consumer pricing the wide-band minimax filter designs), or
a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.
------

## Delivered milestones (most recent first)

**Tikhonov recovered as a functional-calculus instance — the first
bridge consumer; `proposals/hermitian-calculus-consumer-tikhonov-heat.md`,
the Tikhonov half COMPLETE, Steps 0+1 in one run (run 1, 2026-08-25,
run `20260825T145722Z-run-1`; the first of the two consumer stubs the
previous delivery unblocked, its gate satisfied and its
Tikhonov-vs-Heat choice discharged by the parent proposal's recorded
Step-0 pricing — "the smaller reconciliation gap is Tikhonov's"):
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/tikcfc_axcheck.lean` on all 19 new
declarations — 3 public + 16 QA: exactly `propext, Classical.choice,
Quot.sound`, every one). QA 2189 → 2205 (+16 in
`FunctionalCalculus_QA.lean`'s Section E, no new file).**

**Delivered:** the "Recovered instances" section of
`GraphTheory/FunctionalCalculus.lean` (`Tikhonov.lean` untouched per
the stub's non-goals; no new imports, no umbrella change):
`continuousOn_of_finite_real_spectrum` (the `ContinuousOn` supplier on
the finite real spectrum, via `Finite.instDiscreteTopology` — the
helper every future generic-CFC consumer needs, since `cfc_cont_tac`'s
`fun_prop` cannot discharge spectrum-restricted continuity of
spectral-data functions), the headline
`tikhonovMinimizer_eq_spectralCalc_mulVec` (`x* = f(L) *ᵥ y` at
`f = tikhonovShrinkage π`, **hypothesis-free**, the proof the
definition identity the parent pricing predicted — the bridge's action
form was stated in exactly the minimizer's filter-sum shape), and the
substantive second layer
`add_smul_one_mul_spectralCalc_tikhonovShrinkage` — the normal
equation `(L + π•1) * f(L) = π • 1` **re-derived through Mathlib's
generic CFC algebra** (`cfc_add_const`/`cfc_id'`/`cfc_mul`/`cfc_congr`/
`cfc_const`, reached through `Matrix.IsHermitian.cfc_eq`; the
pointwise `shrink π λ · (λ+π) = π` promoted from the spectrum by
`cfc_congr`, PSD + `0 < π` keeping the division non-junk at spectral
points) — an eigenbasis-free route to a statement the shelf had only
through the eigenbasis expansion: two routes, one nontrivial
statement.

**QA (+16, Section E on the `Tikhonov_QA` K₂ fixture):** the sign-free
structure pins (kernel outer products all `1/2`; `λ = 2` outer
products `±1/2` — no basis-orientation choice surviving anywhere); the
arbitrary-`f` master entrywise lemma `fc_lapK2_calc`
(`f(L) = !![(f 0+f 2)/2, (f 0−f 2)/2; …]`); the calculus instance
pinned to `!![2/3, 1/3; 1/3, 2/3]` at `π = 1`; **the reconciliation
witnessed numerically** — through the equality theorem the calculus
routes `![1,0]` to `![2/3, 1/3]`, exactly the hand-solved Gaussian
value `tik_K2_eq` pinned in the original Tikhonov delivery (two
constructions, one number); the normal equation by **two independent
routes** (`fc_lapK2_normal_calculus` through the public chain vs
`fc_lapK2_normal_hand` through the pinned hand-solved system) plus a
raw matrix-arithmetic check; the kernel-mode action instantiation
(factor exactly `1`); and the **fence at `π = -2`** — the junk
shrinkage `0` at the spectral point `2 = -π` drives `f(L)` to the pure
kernel average and the hypothesis-free normal equation is refuted in
proved form at the `(-1) ≠ 0` entry: `0 < π` load-bearing.

**Verification:** spike first (`wip/tikcfc_spike.lean` +
`wip/tikcfc_qa_spike.lean`, the full routes green before any module
touched; the recurring fixes recorded in the proposal's
pin-technique list — the `IsSelfAdjoint`-ascription requirement for
generic-CFC rewrites, `mul_div_cancel₀`'s order,
`Matrix.algebraMap_matrix_apply` entrywise, the `fin_cases` beta-redex
`show`s, raw-product outer pins); `lake env lean` zero errors/warnings
on both changed files; explicit `lake build` targets ✔ (2301/2301,
2305/2305); `#print axioms` via `wip/tikcfc_axcheck.lean` on all 19 —
the standard three only; **full `lake build` ✔ (2385 targets, "Build
completed successfully") immediately followed by
`check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing,
exit 0** (a mid-verification `touch` tripped the STALE fence exactly
as calibrated; remediated by the documented artifact-removal +
re-elaboration route before the recorded build); `lint_axioms` (10),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**2205/10/0**, idempotent by md5). Records updated: the
proposal (COMPLETE header + delivery record with the pin-technique
list and priced follow-ons — the Heat sibling, the resolvent identity,
the general-symmetric normal equation), `proposals/README.md` (the
Delivered row; the progress paragraph; the natural-candidates closing
paragraph now headed by the Heat half), README (2205; the
FunctionalCalculus module-table row's consumer clause), the radar (QA
axis synced 2189/55 → 2205/55, held 4.0), the scoreboard (two
verification rows + the interpretation bullet),
`index/map/spectral_graph.md` (the FunctionalCalculus section: +3
declaration rows + the reconciliation paragraph), this plan, and the
activity log. Nothing committed.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the **Heat half** of the consumer stub (its own
authorized follow-on), the magnetic heat propagator (the second
consumer stub), the irregular-Cheeger *hard* direction, the standing
gated candidates (directed-axis rate; magnetic spectral; a consumer
pricing the wide-band minimax filter designs), or a fresh center-out
candidate per `docs/6_SGT_BACKLOG.md`.
------

## Delivered milestones (most recent first)

**Hermitian functional-calculus bridge — the Scaffold–Mathlib
consolidation layer for "a function of a symmetric matrix"; the
proposal COMPLETE, Steps 0+1 (all of 1–3) in one run (run 1,
2026-08-25, run `20260825T125600Z-run-1`;
`proposals/hermitian-functional-calculus-bridge.md`, one of the three
untracked Hermitian-calculus proposals left by the previous run's
standing handoff — triaged per that handoff: the two consumer
documents are gated stubs blocked on this bridge's Steps 1–3 and
stayed out of scope; the bridge itself is Medium in its own header and
its own gating condition, an Active table empty of higher rows, was
satisfied — indexed into the Active table this run and pursued):
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/hfc_axcheck.lean` on all 25 audited
declarations — 7 public + 18 QA: exactly `propext, Classical.choice,
Quot.sound`, every one — zero contact with any of the ten admitted
axioms, machine-checked, as the acceptance bar demands). QA
2173 → 2189 (`FunctionalCalculus_QA` a new file at 16 by the generator
metric).**

**Step 0 verdict (recorded before any shelf Lean, in both the
execution plan and the proposal):** (1) ONE `cfc` definition covers
real-symmetric and complex-Hermitian via `[RCLike 𝕜]` — no API split
to bridge, one thin real wrapper suffices and complex consumers use
`cfc` at `𝕜 = ℂ` directly; (2) `Matrix.IsHermitian.cfc` takes a bare
`ℝ → ℝ` function with NO continuity hypothesis (finite spectrum), so
discontinuous-at-a-point filters cannot collide with the domain; (3)
eigenbasis reconciliation is free — `eigvecOf`/`eigvalOf` ARE Mathlib's
`eigenvectorBasis`/`eigenvalues` coerced. One provenance repair: the
proposal's "Assessed from" placed `dotProduct_eigvecOf_filter` in
`Spectral.lean`; it lives in `Tikhonov.lean:194`.

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/FunctionalCalculus.lean`
(namespace `SpectralGraphTheory`; minimal imports Spectral + Tikhonov +
Mathlib's `HermitianFunctionalCalculus`; the umbrella importing it) —
`spectralCalc` (the thin wrapper), `spectralCalc_apply` (the entry
form — the falsifiability anchor), `spectralCalc_mulVec_apply` (the
action form = the shelf's filter-sum vector),
`spectralCalc_mulVec_eigvecOf` (the hypothesis-free eigenvector
action), `dotProduct_eigvecOf_spectralCalc_mulVec` (the coefficient
bridge consuming the Tikhonov workhorse verbatim — Step 3's literal
statement), `spectralCalc_indicator_eq_spectralProjector` (the
recovery of the hand-built projector as a calculus instance), and
`spectralCalc_id`. The module docstring carries the proposal's three
mandated NOT-clauses (not a spectral-theorem re-proof, not an
axiom-retirement path, not a Krylov/Chebyshev replacement).

**QA (+16):** all three mandated obligations — (A) two API paths to
one value on the reused `diag13` fixture (`fc_diag13_calc` for
arbitrary `f` from the entry form + Band_QA's pins, sign-free
summands; the projector route through the recovery theorem; both
pinned to `!![1,0;0,0]`; the f-dependence fence `3 ≠ 9`), (B) the
non-basis eigenvector action (`fc_action_add` generically at
`v_i + v_j`; the `![1,1]` action by two independent routes), (C) the
repeated-eigenvalue boundary on `2 • 1` (`f(2•1) = f 2 • 1` by two
genuinely independent routes — entry form + completeness with no basis
choice anywhere, raw unitary conjugation with no completeness
anywhere) — plus (D) the complex-half elaboration witness
`fcM2c_cfc_id` (`cfc` at `𝕜 = ℂ` through the generic `cfc_id'`),
discharging the gated magnetic consumer's Step-0 precondition with an
artifact.

**Verification:** spike first (`wip/hfc_spike.lean` + `wip/hfc_cx.lean`,
several rounds to green before any module touched); `lake env lean`
zero errors/warnings on both modules; explicit `lake build` targets ✔
(2301/2301, 2304/2304); **full `lake build` ✔ (2385 targets, "Build
completed successfully"; the +~120-target jump over the previous 2264
is the previously-unbuilt Mathlib CFC closure pulled by the new
import, not new Scaffold surface) immediately followed by
`check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (**2189/10/0**, idempotent by md5).
Records updated: the proposal (COMPLETE header + Step-0 verdict +
delivery record with the pin-technique list and priced follow-ons),
`proposals/README.md` (the Medium row retired to Delivered; the
progress paragraph), README (2189; the status-paragraph bridge clause;
the module-table row), the radar (QA axis synced 2173/54 → 2189/55,
held 4.0), the scoreboard (the verification row),
`index/map/spectral_graph.md` (the FunctionalCalculus section + 7
declaration rows), the coverage map (the cross-reference sentence),
the umbrella `Scaffold.lean`, this plan, and the activity log. Nothing
committed; the prior runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the two now-unblocked bridge consumer stubs (each
needing its own indexing-and-pursuit decision), the irregular-Cheeger
*hard* direction, the standing gated candidates (directed-axis rate;
magnetic spectral; a consumer pricing the wide-band minimax filter
designs), or a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.
------

**Hoffman-type independence bound — the Expander Mixing Lemma's first
theorem consumer; the proposal COMPLETE, Steps 0+1 in one run (run 1,
2026-08-25, run `20260825T064753Z-run-1`;
`proposals/expander-independence-number-bound.md`, found committed in
`4e60ce6` but never indexed — the same unindexed-proposal gap class
documented twice in the Active table's history — triaged per the
previous run's explicit standing handoff, header marked Medium-High,
indexed as the table's only High row, pursued per priority item 0):
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/hoffman_axcheck.lean` on all 26 new
declarations — 4 public + 22 QA: exactly `propext, Classical.choice,
Quot.sound`, every one). QA 2152 → 2173 (+21 in `Expander_QA.lean`'s
new Step-5 section, no new file). The strategy's load-bearing-growth
principle executed verbatim: 24 declarations of proved discrepancy
machinery with zero theorem consumers now carry weight.**

**Delivered:** section 8 of `GraphTheory/Expander.lean` (no new
imports, no umbrella change): `IsIndependentSet` (diagonal-inclusive —
the Step-0 verdict-1 reading that collapses the internal cut weight,
defined natively over `WAdj`/`Finset` since the pinned Mathlib has no
independence-number machinery),
`edgeWeight_self_eq_zero_of_isIndependentSet` (the one-line collapse),
`deg_eq_zero_of_isIndependentSet_univ` (the whole-graph corner fence
lemma), and the headline `hoffman_independence_bound`:
`(S.card : ℝ) ≤ μ * (Fintype.card V : ℝ) / (d + μ)` for every
independent set of a symmetric nonnegative `d`-regular positive-degree
network at exactly the mixing lemma's own `μ` hypothesis — the lemma
instantiated at `T = S`, `Real.sqrt_mul_self` at the perfect square,
`div_le_iff₀`/`div_mul_cancel₀` clearing `n`, `nlinarith` cancelling
`|S|` (the `|S| = 0` degenerate case closed as `0 ≤ μn/(d+μ)`),
`le_div_iff₀` + `linear_combination` dividing by `d + μ > 0` with zero
coefficient slack. **Both Step-0 verdicts delivered as proved facts:**
`0 < d` is NOT free (the `2×2` zero-adjacency fence verifies every
other hypothesis *including* independence of `univ` and `μ = 0` exact
via eigen-action spectrum pins, refuting the division-form conclusion
`2 ≤ 0` — `hd` exactly isolated), and the whole-graph corner is a real
fence (`2 = 0` refuted through the corner lemma on the
all-degrees-`2` `C₄`).

**QA (+21):** all four proposal-mandated obligations — (1) both
classical tight cases **attained with equality** at the Step-4-exact
`μ` pins: `C₄`'s opposite pair `2 = 2·4/(2+2)` (the bipartite
Hoffman-equality regime) and `K₃`'s singleton `1 = 1·3/(2+1)` (the
clique regime, the bound pinning the maximum independent set exactly
on the least-expanding fixture), `hμ` discharged from the file's own
pins rather than assumed; (2) the `∅` degenerate instance and the
whole-graph fence pair; (3) the independence hypothesis isolated
(every other hypothesis verified on `C₄`, conclusion refuted at
`univ`, the collapse mechanism pinned blocked — internal cut weights
`8 ≠ 0` and `2 ≠ 0`, the half set's conclusion holding numerically
being exactly why the fence lives at the mechanism); (4) the `d = 0`
fence with its full isolation collection.

**Verification:** spike first (`wip/hoffman_spike.lean`, several
rounds to green before any module touched; the recurring fixes are the
proposal's pin-technique list); `lake env lean` on both changed
modules — zero errors, zero warnings each; explicit `lake build`
targets ✔ (module 2009/2009, QA 2010/2010); `#print axioms` via
`wip/hoffman_axcheck.lean` on all 26 new declarations — the standard
three only; **full `lake build` ✔ (2264 targets, "Build completed
successfully") immediately followed by `check_build_completeness.py` —
104/104 fresh, 0 stale, 0 missing, exit 0** (the mandatory post-build
fence); `lint_axioms` (10), `check_citations`, `check_markdown_links`
pass (re-run after the record sweep); scoreboard regenerated
(**2173/10/0**, idempotent by md5). Records updated: the proposal
(status header COMPLETE + the delivery record with the Step-0
verdicts, pin-technique list, and priced follow-ons),
`proposals/README.md` (the High row retired to Delivered; the progress
paragraph), README (2173; the status paragraph's Hoffman clause; the
module-table row), the radar (QA axis synced 2152/54 → 2173/54 held
4.0; the axis-4 Hoffman clause held 4.5; plus two factual repairs:
the axiom-minimization row-head's stale 9 → 10 and the trend chain's
missing 2026-08-24 up-step, and item 3's stale "admitted Cheeger lower
bound" → proved), the scoreboard (all five verification rows + the
interpretation bullet), `index/map/spectral_graph.md` (the Expander
section header + 4 declaration rows), backlog item 3 (the delivery
update + the same Cheeger-hard staleness repair), this plan, and the
activity log. Nothing committed; the prior runs' uncommitted
deliveries preserved untouched, and the mid-run-appeared untracked
Hermitian-calculus proposals plus the coverage-map's matching edit
left as found (not this run's artifacts; triage recorded above).

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — triaging the three untracked Hermitian-calculus
proposals (this run's observation, the unindexed-proposal precedent),
the irregular-Cheeger *hard* direction, the standing gated candidates
(directed-axis rate; magnetic spectral; a consumer pricing the
wide-band minimax filter designs), or a fresh center-out candidate per
`docs/6_SGT_BACKLOG.md`.
------

**Irregular Cheeger easy direction — the volume-weighted upper bound on
arbitrary positive-degree graphs; `GraphTheory.VariationalTransfer`'s
first theorem consumers; the proposal COMPLETE for the easy direction,
Steps 0+1 in one run (run 1, 2026-08-25, run `20260825T045222Z-run-1`;
`proposals/irregular-cheeger-variational-transfer.md`, found committed
since `6cb2f20` but never indexed in the Active priority table — the
same unindexed-proposal gap class documented twice in that table's
history — indexed at the boundary and pursued per priority item 0):
DELIVERED — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/icv_axcheck.lean` on all 36 new declarations
— 10 public + 26 QA headline: exactly `propext, Classical.choice,
Quot.sound`, every one). QA 2067 → 2152 (`IrregularCheeger_QA` a new
file at 85 by the generator metric). The standing "regular graphs only"
caveat on the Cheeger upper bound is gone, and the never-consumed
`VariationalTransfer` module — built for exactly this consumer — now
carries three.**

**Delivered:** `cheeger_upper_bound_normalized` (in
`VariationalTransfer.lean`, no new modules, no umbrella change):
`secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A` for
symmetric nonnegative positive-degree `A` with `2 ≤ card V` — no
regularity, no connectivity; the regular family recovered on the cone
through `normalizedLaplacian_eq_regularNormalizedLaplacian`. The
route: the degree-stretched cut indicator `√D *ᵥ cutTestVector A S`
(orthogonality to the true kernel vector `√D · onesVec` by the volume
identity `vol S · vol Sᶜ − vol Sᶜ · vol S = 0`, *no regularity*), the
one genuinely new engine lemma `secondEval_le_rayleigh_of_ker`
(`Spectral.lean`; the general-kernel Rayleigh domination — the
delivered onesVec form provably cannot express the route, QA pins
`dotProduct z onesVec = 2 − √2 ≠ 0`), the kernel-vector layer
`normalizedLaplacian_mul_degreeSqrt`/`normalizedLaplacian_mulVec_degreeSqrt_onesVec`
(`Normalized.lean`), and the same Rayleigh quotient `boundary · vol V /
(vol S · vol Sᶜ)` as the regular family with closing arithmetic
verbatim. Supporting: `eigvecOf_ortho_of_mulVec_eq_zero`,
`vol_pos_of_pos_deg` (Spectral).

**QA (+85):** all four proposal-mandated sections — the genuinely
irregular `P₃` fixture (degrees 1, 2, 1): conductance by hand (all six
cuts `1`, constant `1`), the test-vector layer entrywise (orthogonality
by theorem and raw arithmetic; norm `12` by two routes; energy `16` by
**three** independent routes), the spectral side bounded *independently*
through the eigenpair witness `![1, 0, -1]` (`λ₂ ≤ 1`, strictly stronger
than the theorem's `≤ 2` — non-circular) and through the theorem's own
test vector (`≤ 4/3`); the discrimination witness; the `K₂` tight
regular recovery (`2 ≤ 2 · 1`); two proved fences — PSD-drop on the
engine (`diag(−1, 0)`: `0 ≤ −1` false, exactly `hpsd`) and degree-drop
on the headline (all-zero adjacency: `λ₂ = 1 > 0 = 2 · cheegerConstant`,
exactly `hd`).

**Verification:** spike first (`wip/icv_spike.lean`, the whole route
green before any module touched); `lake env lean` zero errors/warnings
on all three public modules and the QA file; explicit `lake build`
targets ✔ (QA 2193/2193); **full `lake build` ✔ (2264 targets, "Build
completed successfully") followed immediately by
`check_build_completeness.py` — 104/104 fresh, 0 stale, 0 missing,
exit 0** (the mandatory post-build fence); `lint_axioms` (10),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**2152/10/0**, idempotent by md5). Records updated: the proposal
(status header + Step-0 record + delivery record with the
pin-technique list and priced follow-ons), `proposals/README.md` (the
High row retired to Delivered; the progress paragraph), README (2152;
the status paragraph's irregular clause; the module-table row), the
radar (QA axis 2067/53 → 2152/54 held 4.0; axis-4's irregular-easy
clause, held 4.5 — the hard direction keeps half the statement
regular-only), the scoreboard (two verification rows),
`index/map/spectral_graph.md` (the VT section's second table + the
Spectral/Normalized engine rows), backlog item 3 (the update), this
plan, and the activity log. Nothing committed; the prior runs'
uncommitted deliveries preserved untouched, and the mid-run-appeared
untracked `proposals/expander-independence-number-bound.md` left as
found.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the irregular-Cheeger *hard* direction (the
delivery's own priced follow-on), triaging the newly-observed untracked
`expander-independence-number-bound.md`, the standing gated candidates
(directed-axis rate; magnetic spectral; a consumer pricing the
wide-band minimax filter designs), or a fresh center-out candidate per
`docs/6_SGT_BACKLOG.md`.
------

## Delivered milestones (most recent first)

**Build-completeness verification — `scripts/check_build_completeness.py`,
the reconciliation fence making "lake build completed successfully"
falsifiable; `proposals/verify-build-completeness.md` (found untracked
and unindexed at run start, its own header marked **High** — indexed
into the Active priority table at that boundary and pursued per
priority item 0); the proposal COMPLETE, Steps 0+1 in one run (run 1,
2026-08-25, run `20260825T032035Z-run-1`): DELIVERED — no Lean, no
axioms, no QA declarations; the most-repeated verification step in
every delivery entry no longer rests on an assumption the incident
proved false. And the fence earned its keep on its very first run: 8
live findings on the real tree, including two never-built QA modules
and a genuine never-rebuilt content edit.**

**Delivered:** `scripts/check_build_completeness.py` (enumerate the
root umbrella plus every `Scaffold/**/*.lean`, exclude ignored
scratch, require a fresh `.lake/build/lib/**/<module>.olean` per
source — MISSING or mtime-STALE (nanosecond compare) fail nonzero
with every offender listed; exits 0/1/2 for complete/incomplete/
operational; `--root` for arbitrary trees; no Lean invocation, no
lakefile parsing, no Lake-internals re-implementation — the trace
files hold only a Lake-internal UInt64 `depHash`). Two decisive
toolchain experiments calibrated the semantics and are recorded in
the docstring: a content-changed source is rebuilt/rewritten by an
explicit target, but a pure `touch` of an up-to-date source is a
no-op (Lake's up-to-date check is content-hash based) — hence STALE
fails closed with an always-terminating remediation (direct rebuild;
else remove the gitignored derived artifact and rebuild once to force
re-elaboration). **Live findings on run 1:** MISSING —
`ProjectionGap_QA.lean` (586 lines) and `Expander_QA.lean` (1,181
lines), both artifact-less, both elaborating clean once built, plus
`Mathlib/Core.lean` (an unimported 2-line legacy re-export shim from
the initial commit); STALE — `Dynamics_QA.lean` (a **genuine
never-rebuilt content edit**: source 08-20, artifact 08-18 — the
incident class caught live), `Mixing_QA.lean`, `SpectralCertificates_QA.lean`
(the same class), and `Subgaussian.lean`/`Entropy_QA.lean` (benign
byte-identical roundtrips, remediated by the documented
artifact-removal route, re-elaborating both). Every remediation was a
real elaboration, so all 103 sources have now been elaborated as-is.
**Ladder wiring, all five documented locations:** `AGENTS.md` §
Verification, `scripts/opencode-pursue`'s `verify_for_commit` (after
`lake build`, so `--commit` fails closed), `scripts/README.md`,
`docs/2_ARCHITECTURE.md` §10, and the `docs/AGENT_ACTIVITY.md` format
block (entries claiming a verified full build must record the check
passing immediately after the build they cite).

**Verification:** the acceptance-bar regression suite in a synthetic
mini-tree — the incident reconstruction (a three-error
`Magnetic_QA.lean` with no artifact) flagged MISSING at exit 1;
explicit-mtime STALE flagged with both timestamps; fresh umbrella +
module counted; `wip/` excluded (5 counted, not 6); usage/bad-root
exit 2; the healed tree exits 0 (documented in the proposal's delivery
record rather than committed as a fixture, per its own either/or).
Full ladder on the real tree in the mandated order: `lake build` ✔ →
**completeness 103/103 fresh, 0 stale, 0 missing, exit 0** →
`lint_axioms` (10 axioms, no issues), `check_citations`,
`check_markdown_links` pass, scoreboard idempotent (md5-stable).
Records updated: the proposal (COMPLETE + delivery record),
`proposals/README.md` (the High row added at the boundary, then
retired to Delivered; the progress paragraph), `AGENTS.md`,
`scripts/opencode-pursue`, `scripts/README.md`,
`docs/2_ARCHITECTURE.md`, the activity-log format block, this plan,
and the activity log. Nothing committed.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the directed-axis *rate* layer (gated on a
separate admission + a named consumer), the magnetic *spectral* layer
(gated on a consumer naming a bound), a named consumer pricing the
wide-band minimax filter designs, the sweep-cut priced follow-ons, or
a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

**Magnetic Laplacian first slice — the directed-native Hermitian
operator, its energy identity, PSD, and gauge characterization; the
proposal COMPLETE, Steps 0+1 across two runs (run 1
`20260825T001310Z-run-1` drafted the module+QA and recorded Step 0
but was interrupted before verification; continuation
`20260825T021040Z-run-1` verified, fixed, wired, and recorded;
`proposals/magnetic-laplacian.md`): DELIVERED — pure hard crust, zero
new axioms (count stays 10; `#print axioms` via `wip/mag_axcheck.lean`
on all 39 accessible declarations: `propext, Classical.choice,
Quot.sound` only, every one). QA 2051 → 2067 (`Magnetic_QA` a new file
at 16 by the generator metric, 30 declarations total). The shelf's
first complex-valued object and the directed axis' third spectral
toolkit: the named external consumer in backlog item 8 ("directed
community detection via the magnetic Laplacian") now has its
mathematical core — the energy/gauge layer — on the shelf.**

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/Magnetic.lean`
(namespace `SpectralGraphTheory`; minimal imports Directed + Spectral;
the umbrella importing it) — `symDeg`/`magneticMatrix`/
`magneticLaplacian` (`M := D_sym − ½(W + Wᴴ)`, `W := A ∘ e^{iΘ}`
entrywise; the Crucoli–Pérez–Bungert–Van Mieghem directed convention),
`hermQuadForm` (the sesquilinear `quadForm` analogue), and: Hermitian
**hypothesis-free** (`magneticLaplacian_isHermitian` — the
Hermitian-part convention's structural payoff, the
`directedNormalizedLaplacian` precedent; `magneticMatrix_isHermitian`
the cone lemma), the action interface `magneticLaplacian_mulVec_apply`,
**the magnetic energy identity** `magnetic_energy` (hypothesis-free;
diagonal split into out-/in-degree halves, cross sums matched termwise
and swap-conjugated), realness (`magnetic_energy_real`,
`magneticQuadForm_im_eq_zero`), **PSD**
(`magneticQuadForm_re_nonneg`), **the balanced-potential gauge
characterization** `magneticQuadForm_eq_zero_iff` (`x*Mx = 0 ↔ x_u =
e^{iΘ_uv} x_v` on positive edges — a frustrated cycle forces the
kernel trivial, flux localization at form level with no complex
spectral theorem anywhere), and the cone agreements
(`magneticLaplacian_zero_phase_apply[_of_isSymm]` — at Θ = 0 the
complexified classical Laplacian of the symmetrized weights, on
symmetric `A` of `laplacian A` itself; `magneticLaplacian_eq_single` —
the classical single-`W` form derived on the symmetric/antisymmetric
cone).

**QA (+16):** all four proposal-mandated sections — (A) the
asymmetric-flux fixture: `W`'s raw entries `−2`/`I`, the operator's
conjugate-pair off-diagonals `1 ± I/2` (Hermitian verified on directed
input), the energy identity pinned at `5` at `![1,1]`, the zero-phase
agreement entrywise against the mapped `laplacian`, the cone
single-`W` form at the `π`-flux pair; (B) the **frustrated-vs-
consistent kernel pair** — the one-`π`-edge triangle's kernel forced
trivial through the gauge conditions (with the positive-definiteness
corollary) against `K₂` at the same flux keeping the antipodal
potential `![1,−1]` in the kernel (the iff's reverse direction,
cross-checked by the raw vanishing energy); (C) the classical bridge —
constants in the zero-phase kernel, the antipodal vector outside it at
energy exactly `4` (the flux is what moved the kernel); (D) the
**nonnegativity fence** — symmetric signed input refutes PSD in proved
form at `−1 < 0`, exactly `hA` isolated.

**Verification (continuation run):** the module elaborated green as
drafted (`lake env lean`, zero diagnostics); the QA's three first-pass
errors fixed in place (two redundant `match` alternatives; one false
numeric pin — the zero-phase energy stated `2` where `norm_num`
correctly forced the true `4`, the numeric-QA failure mode doing its
job) and re-elaborated green; explicit `lake build` targets ✔ (module;
QA 2192/2192); **full root `lake build` ✔ (2264 targets, +1 for the
new module, "Build completed successfully"; zero warnings in the
changed modules — the log's only Scaffold diagnostics the documented
pre-existing set)**; `#print axioms` via `wip/mag_axcheck.lean` on all
39 accessible declarations — the standard three only; `lint_axioms`
(**10**, unchanged), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**2067/10/0**, idempotent). Records updated:
the proposal (status header COMPLETE + the delivery record with the
pin-technique list and priced follow-ons), `proposals/README.md` (the
Delivered row; the progress paragraph and natural-candidates note —
the magnetic slice retired to delivered, the *spectral* layer the new
gated candidate), README (2067; the axiom-count cell's stale 9 → 10
factual fix; the status paragraph's magnetic clause; the module-table
row), the radar (QA axis synced 2051/52 → 2067/53, held 4.0), the
scoreboard (four verification rows + the interpretation bullet),
`index/map/spectral_graph.md` (the Magnetic section + 15 declaration
rows), backlog item 8 (the seventh update), the umbrella
`Scaffold.lean`, this plan, and the activity log. Nothing committed;
the prior runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the directed-axis *rate* layer (gated on a
separate admission + a named consumer), the magnetic *spectral* layer
(gated on a consumer naming a bound), a named consumer pricing the
wide-band minimax filter designs, the sweep-cut priced follow-ons, or
a fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.
**Primitive power convergence — the directed mixing gate opened by
admission; the PageRank power iteration; the proposal COMPLETE, Steps
0+1 in one run (run 1, 2026-08-24, run `20260824T224813Z-run-1`;
`proposals/primitive-power-convergence.md`, new this run and selected
per the empty High/Medium queue by the center-out policy — the
standing handoff's one named candidate whose gate a run *can* clear,
the PageRank module's own statement-shapes section recording power
iteration as exactly this separate future obligation): DELIVERED —
**one new axiom (count 9 → 10, the first *convergence* axiom: Horn &
Johnson §8.5 at the row-stochastic specialization, given-π form, no
rate)**; QA 2021 → 2051 (`DirectedMixing_QA` a new file at 30). The
directed axis' first convergence theorem, and the loop with the
delivered PageRank layer closed: the distribution is unique
(conditional on `perron_frobenius`) *and computable* (conditional on
the new axiom alone — `#print axioms` verifies **zero
`perron_frobenius` contact** in every conditional theorem).**

**Delivered:** the new
`Scaffold/Mathlib/LinearAlgebra/PrimitiveConvergence.lean` —
`Matrix.IsPrimitive` (H&J's positive-power definition verbatim), the
admitted `primitive_power_tendsto` (`(P ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` at
any nonnegative mass-one stationary `π ᵥ* P = π`; row-stochastic
carrier matching the shelf's bridge convention), and the unconditional
transfer layer: `isPrimitive_of_pos` (k = 1),
`reachable_of_pow_pos` + `isIrreducible_of_isPrimitive` (an entry of
a positive power is a sum over walks, so positivity yields a
positive-weight path — load-bearing on `Matrix.IsIrreducible`'s exact
combinatorial shape), `pow_mulVec_one`, and the generic conditional
corollaries `primitive_entrywise_tendsto` (columns of `Pᵗ` → `π`) and
`primitive_vecMul_tendsto` (`ν ᵥ* Pᵗ → π`; the private finite-sum
tendsto induction, the pin having no tendsto-sum lemma). Plus the new
`Scaffold/Mathlib/GraphTheory/DirectedMixing.lean` —
`googleMatrix_isPrimitive` (the teleportation floor is primitivity:
*aperiodicity* derived, strictly stronger than the delivered
irreducibility), **`pageRank_powerIteration`** (the classical
algorithm as a theorem), `pageRank_entrywise_tendsto`,
`pageRank_walk_tendsto`, and `googleMatrix_pow_mulVec_onesVec`.

**QA (+30):** all three proposal-mandated sections — (A) the positive
witness on the reducible fixture: primitivity by theorem route with a
raw floor spot-check, the power iteration at `e₀` with the limit
coefficient pinned raw to the uniform value `1/4`, the second iterate
computed completely raw at `3/16 < 1/4` (the sequence visibly in
motion toward its limit), the entrywise form at a zero-support pair,
and the walk form at the non-uniform start `![1/2, 1/2, 0, 0]`; (B)
the **periodicity refutation**: `P₂ = !![0,1;1,0]` nonnegative,
row-stochastic, *and irreducible* (all proved) with the uniform
distribution verified stationary raw, `P2_not_primitive` (every power
is `1` or `P₂`, both with zero entries), and `P2_no_limit` (the
even/odd subsequences are constantly `e₀`/`e₁` — no limit exists for
any candidate), with `P2_fence_isolation` collecting every other axiom
hypothesis as *verified* — exactly `hprim` isolated, simultaneously
documenting why `perron_frobenius`'s no-dominance scope was the
honest call; (C) the coherence join: the unconditional
`onesVec`-fixing of the powers against the axiom's limit *derives*
the mass fact `π ⬝ᵥ 1 = 1`, cross-checked against the raw sum. One
drafted QA declaration removed as inert (an equality-of-proofs join —
rfl by proof irrelevance; documented in-file why no such lemma can
carry content).

**Verification:** spike first (`wip/ppc_spike.lean`, several rounds
to green; the recurring fixes recorded in the proposal's
pin-technique list); `lake env lean` on both public modules and the
QA file — zero errors, zero warnings each; explicit `lake build`
targets all ✔ (1736/1736, 2195/2195, 2201/2201); `#print axioms` via
`wip/ppc_axcheck.lean` on all 35 declarations — the split exactly as
specified (unconditional: the standard three; convergence theorems:
`+ primitive_power_tendsto`; no `perron_frobenius` anywhere); **full
`lake build` ✔ (2263 targets, +2, "Build completed successfully")**;
`lint_axioms` (**10**), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (**2051/10/0**, idempotent). Records
updated: the proposal (status header COMPLETE + the delivery record
with the pin-technique list and priced follow-ons),
`proposals/README.md` (the Delivered row; the progress paragraph),
README (2051; the status paragraph's convergence-layer clause; two
module-table rows), the coverage map (the PF row's primitive-limit
sentence), the radar (QA axis synced 2021/51 → 2051/52, held 4.0),
the scoreboard (four verification rows + the interpretation bullet),
`index/sources/horn_johnson_matrix_analysis.md` (§8.5 row + notes),
`index/map/linear_algebra.md` (status + declaration rows + consumers
de-staled), `index/map/spectral_graph.md` (the DirectedMixing
section), backlog item 8 (the sixth update), the umbrella
`Scaffold.lean`, this plan, and the activity log. Nothing committed;
the prior runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the directed-axis *rate* layer (gated on a
separate admission + a named consumer), the magnetic-Laplacian slice,
a named consumer pricing the wide-band minimax filter designs, the
sweep-cut priced follow-ons, or a fresh center-out candidate per
`docs/6_SGT_BACKLOG.md`.

**Sweep-cut extraction — the explicit Fiedler level-set cut; backlog
item 4's named strengthening and the Fiedler module header's own
recorded follow-on; the proposal COMPLETE, Steps 0+1 in one run (run 1,
2026-08-24, run `20260824T210106Z-run-1`;
`proposals/sweep-cut-extraction.md`, new this run and selected per the
empty High/Medium queue by the center-out policy — the standing handoff
candidates gated or honestly blocked while the backlog and module
header name exactly this strengthening): DELIVERED — pure hard crust,
zero new axioms (count stays 9; `#print axioms` via
`wip/sweep_axcheck.lean` on all 5 public + 22 QA declarations:
`propext, Classical.choice, Quot.sound` only, every one). QA
1999 → 2021 (+22 across `Cheeger_QA`/`Fiedler_QA`, no new file). The
certified Cheeger cut is now an *explicit swept Fiedler level set* —
the object the spectral-partitioning algorithm actually returns.**

**Delivered:** the new `SweepExtraction` section of
`Scaffold/Mathlib/GraphTheory/Cheeger.lean` (**no new imports**) —
`mem_of_posPart_sq`/`mem_of_negPart_sq` (the level-set conversions: a
superlevel set of `(x−m)⁺²` at `t > 0` *is* a closed superlevel set of
`x` at `m + √t`, and dually), **`sweep_level_extract`** (the per-part
extraction: for any `y` with minority closed superlevel sets — exactly
`coarea_core`'s hypothesis — some level set `S = {i : t ≤ y i²}` at a
positive `t` attains `conductance S² ≤ E'(y)/(d·M)`, by attainment
over the finitely many positive values of `y²`
(`Finset.exists_min_image`), the covering fact that every closed
superlevel set equals one at an attained value (`Finset.min'`), and a
non-strict layer-cake integration cloned from `coarea_core`'s own
proof, closed by Component A), and **`cheeger_sweep_cut`** (the median
assembly: for any `x ⊥ 1 ≠ 0`, a closed superlevel or sublevel set of
`x` itself with `conductance S² ≤ 2·R_{L_sym}(x)` — *the same constant
as `cheeger_sweep`* with the witness an explicit member of the sweep
family; the median parts supply L1's hypothesis verbatim, the product
test picks the part, and the fused contraction + norm split + Step-1a
normalization close). Plus the new Phase C section of
`Scaffold/Mathlib/GraphTheory/Fiedler.lean`: **`fiedler_sweep_cut`** —
on every connected `d`-regular graph, a closed superlevel or sublevel
set of the Fiedler vector with `conductance S² ≤ 2·lambda2/d`, the
algorithm-facing strengthening of `cheeger_cut_existence` composed
through the Phase B Rayleigh bridge. The module header's recorded
follow-on sentence is updated to point at the delivered theorem.

**QA (+22):** all five proposal-mandated witnesses — (1) the L1
extracted set *forced* to `{0}` on `C₄` at `cycPos = ![1,0,0,0]` by
the level-membership iff (the subset route), conductance `1` raw
against bound `4/(2·1) = 2`; (2) the L2 family characterized at
`cycSweepX` (`{0}`/`{2}`/`{0,1,3}`/`{1,2,3}`, all conductance `1`,
honestly inside bound `2·R = 2`, *not* the global optimum `1/2`); (3)
at `cycX2 = ![1,1,−1,−1]` the family is exactly the two dominant
halves and the swept cut **ties the exhaustively computed global
optimum** `1/2` — the two fixtures marking both ends of the sweep's
quality range; (4) the **orthogonality fence refuted in proved form**
at `x = onesVec` (Rayleigh `0`; the constant vector's sweep family has
no nonempty proper member at all, so the hypothesis-free conclusion is
false for *every* candidate); (5) on `K₂` the swept cut identified as
a singleton of conductance `1`, the swept family characterized through
the Fiedler antisymmetry pins (an equal-entries eigenvector would make
the family *empty* — no theorem of this shape could hold), and the
optimality tie `conductance S = cheegerConstant (K₂) = 1`.

**Verification:** spike first (`wip/sweep_spike.lean`, several rounds
to green; the fixes recorded in the proposal's pin-technique list —
`Finset.exists_min'` absent at the pin, the two-step filtered-image
destructuring, `Fintype.sum_prod_type'`'s at-hypothesis direction, the
abs-form `sq_le_sq`, `min`-stranded `norm_num` divisions, the
literal-facts-at-variable-index trap closed by
`eq_univ_iff_forall`/`eq_empty_iff_forall_not_mem`, and
`add_pos`/`hS.elim` replacements); `lake env lean` on both public
modules and both QA files — zero errors, zero warnings each (the
Cheeger module's one line-44 linter note verified present at HEAD);
explicit `lake build` targets all ✔ (2189/2189, 2194/2194, 2196/2196);
`#print axioms` via `wip/sweep_axcheck.lean` on all 27 accessible
declarations — the standard three only; **full `lake build` ✔ (2261
targets, "Build completed successfully")**; `lint_axioms` (**9**,
unchanged), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**2021/9/0**, idempotent). Records updated: the proposal
(status header COMPLETE + the delivery record with the pin-technique
list and priced follow-ons), `proposals/README.md` (the Delivered row;
the progress paragraph), README (2021; the status paragraph's
sweep-extraction clause; the module-table row), the radar (QA axis
synced 1999/51 → 2021/51 and the axis-4 Phase C delivery sentence,
both held), the scoreboard (four verification rows + the
interpretation bullet), `index/map/spectral_graph.md` (3 declaration
rows + the Phase A–C header), backlog item 4 (the Phase C delivery),
the Fiedler module header, this plan, and the activity log. Nothing
committed; the prior runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the standing gated candidates (primitivity-shaped
admission for directed mixing; the honestly-blocked pairwise set
shape; a named consumer pricing the wide-band minimax filter designs),
the sweep-cut proposal's priced follow-ons (the computable sweep
enumeration, gated on a consumer naming what it unlocks; the irregular
conductance shape), or a fresh center-out candidate per
`docs/6_SGT_BACKLOG.md`.

**Resistance metric — the maximum principle, the definiteness residual,
and the triangle inequality; backlog item 7's two named non-gated
residuals; the proposal COMPLETE, Steps 0+1 in one run (run 1,
2026-08-24, run `20260824T192530Z-run-1`;
`proposals/resistance-metric.md`, new this run and selected per the
empty High/Medium queue by the center-out policy — the standing handoff
candidates gated or honestly blocked while backlog item 7 names exactly
these two residuals as the electrical family's remaining unblocked
work): DELIVERED — pure hard crust, zero new axioms (count stays 9;
`#print axioms` via `wip/rm_axcheck.lean` on all 5 public + 28 QA
declarations: `propext, Classical.choice, Quot.sound` only, every one).
QA 1971 → 1999 (`ResistanceMetric_QA` a new file at 28). With the
proved nonnegativity, symmetry, and self-distance laws,
`effectiveResistance` is now a genuine metric on every connected
network — the classical resistance distance.**

**Delivered:** the new "resistance metric" section of
`Scaffold/Mathlib/GraphTheory/Electrical.lean` (**no new imports, no
umbrella change**) — `laplacian_mulVec_eq_single_sub_single_le_max`
(the **maximum principle**, top half: at a max-point outside `{u, v}`
the diffusion form is a sum of nonnegative terms, so the max value
propagates across every positive-weight edge and a walk induction
floods the connected graph — the kernel-characterization argument run
at an inequality, stated over the walk's *start* so cons-peeling
works), `laplacian_mulVec_eq_single_sub_single_min_le` (the min half at
the negated demand), `effectiveResistance_pos_of_ne` (the one-sided
Dirichlet bound at the indicator `e u`: energy
`∑_{j≠u} A u j > 0` from the first cons-edge of any walk to `v`,
voltage difference `1`), `effectiveResistance_eq_zero_iff` (the
definiteness residual), and `effectiveResistance_le_add` (the
**triangle inequality**: the `f + g` demand-superposition, the
polarization `quadForm_laplacian_sub_smul` at `t = −1`, the cross term
`f v − f w ≤ 0` closed by min-confinement + positivity, degenerate
cases through `effectiveResistance_self`). The Step-0 survey's decisive
finding is priced into the route: the eigenbasis route yields only the
**root**-triangle (`R` is a squared Euclidean distance there; the cross
term is what the sharp form must cancel), so the maximum principle is
the mathematical crux, not a convenience.

**QA (+28):** all four proposal-mandated sections — (1) the **equality
case** on the 3-path: the new edge witnesses pin `R(0,1) = R(1,2) = 1`,
joined with the imported `R(0,2) = 2` as the identity `2 = 1 + 1` (any
proof route with a slack constant dies there), plus the degenerate
`v = u` instantiation exercising the theorem's self-distance branch;
(2) the **strict case** on `K₃` through the imported Foster pins
(`2/3 < 4/3`); (3) the confinement/definiteness positive witnesses at
the actual unit-current potential `![2,1,0]` — both confinement halves
instantiated at every vertex, the interior value pinned strictly
between the boundary values, the `iff` consumed off-diagonal
(`R 0 2 ≠ 0` through the forward direction) and on the diagonal; (4)
the **signed fence** — `![0,1,1;1,0,−1;1,−1,0]` (symmetric, support
graph the connected path `1—0—2`, NOT nonnegative, entrywise-if
definition per the `Foster_QA` vecTail note): in-file solution-shape
analysis (`f 1 = f 0`, `f 2 = f 0 − 1` for the `e₀ − e₁` demand, via
the diffusion-form row lemmas) pins the values through the junk-free
branch (`dif_pos` + shape, the shelf's uniqueness needing the
nonnegativity that fails) — `R(0,1) = 0` at distinct vertices
(**definiteness refuted in proved form**), `R(0,2) = 0`, `R(2,1) = −2`,
the **triangle refuted** at `¬(0 ≤ 0 + (−2))`, and **confinement
refuted for every solution** at the interior vertex — with `hA` and
`hconn` verified on the fixture, exactly `hnonneg` isolated for all
three theorems at once.

**Verification:** the module elaborated green after one structural fix
(the walk-induction claim stated over the walk's start — cons-peeling
peels the front edge, so the invariant must be `f s = M → …` not a
statement about the fixed endpoint); the QA after several rounds whose
recurring fixes are recorded in the proposal's pin-technique list (the
`Pi.single`-family ascription trap; `(-f) x` as a function-negation
atom to `linarith`; one rewrite lemma per hypothesis; the matrix
notation vecTail leftover; `Finset.sum_erase_add`/`single_le_sum`
signatures at this pin); `lake env lean` on the module and the QA file
— zero errors, zero warnings each; explicit `lake build` targets both ✔
(2009/2009, 2015/2015); `#print axioms` via `wip/rm_axcheck.lean` on
all 33 declarations — the standard three only; **full `lake build` ✔
(2261 targets, "Build completed successfully"; zero warnings in the
changed modules)**; `lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1999/9/0**,
idempotent). Records updated: the proposal (status header COMPLETE +
the delivery record with the pin-technique list and priced follow-ons),
`proposals/README.md` (the Delivered row; the progress paragraph),
README (1999; the status paragraph's resistance-metric clause; the
module-table row), the radar (QA axis synced 1971/50 → 1999/51 and the
axis-6 delivery sentence, both held), the scoreboard (all four
verification rows + the interpretation bullet),
`index/map/spectral_graph.md` (5 declaration rows), backlog item 7 (the
delivery update), this plan, and the activity log. Nothing committed;
the prior runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the standing gated candidates (primitivity-shaped
admission for directed mixing; the honestly-blocked pairwise set shape;
a named consumer pricing the wide-band minimax filter designs), the
priced resistance-metric follow-ons (the `MetricSpace` packaging, gated
on a consumer naming what it unlocks), or a fresh center-out candidate
per `docs/6_SGT_BACKLOG.md`.

**Cluster-projector symmetric form — the two-sided rank-free constant-2
set-form difference theorem; the proposal COMPLETE, Steps 0+1 in one run
(run 1, 2026-08-24, run `20260824T175747Z-run-1`;
`proposals/cluster-projector-symmetric.md`, new this run and selected
per the empty High/Medium queue as the cluster-projector delivery's
recorded open follow-on — "the two-sided rank-free constant-2 *set*
form composes from the delivered pair but was not re-derived here"; the
two alternative candidates gated on decisions a run cannot make):
DELIVERED — pure hard crust, zero new axioms (count stays 9; `#print
axioms` via `wip/cps_axcheck.lean` on the new public theorem + all 18
new QA declarations: `propext, Classical.choice, Quot.sound` only,
every one). QA 1953 → 1971 (`ClusterProjector_QA` 28 → 46). The
set-valued difference family is complete: product/difference/symmetric
all at arbitrary eigenvalue sets, matching the window family's full
shape.**

**Delivered:** the new SetForm theorem of
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`
(**no new imports**) —
`l2OpNorm_clusterProjector_sub_clusterProjector_le_two_of_symm`:
`‖P_A(S) − P_B(T)‖ ≤ 2‖A−B‖/δ` under both-flank center/radius
membership separation at **two** center/radius pairs (`cS rS` for A's
`S`-cluster, `cT rT` for B's `T`-cluster; statement-shape decision
recorded before stating: a single common center would exclude the QA's
own unequal-rank witness, where an out-of-`S` A-eigenvalue sits between
the clusters), **no rank hypothesis anywhere** — the YWS both-gaps
dimension-freeness at sets. The proof is the priced four-step
composition: the ring identity `P − Q = (I−Q)P − Q(I−P)` (the module's
own private lemma), the complement law `1 − Q_T = Q_{Tᶜ}` at both
residuals, the delivered set-form product bound at both argument orders
(the second moved under `l2OpNorm_transpose`; `clusterProjector_symmetric`'s
`IsSymm` proofs bridged to transpose equations by typed `have`s), and
the triangle inequality — **the constant 2 is exactly that triangle,
with no case split anywhere** (the window sibling needed a private
rank-free pairwise engine plus a trivial-regime split because its
product bound carries `‖A−B‖ < δ`; the set product bound is
unconditional, and that the set route is *easier* is the delivery's
structural finding).

**QA (+18):** all four proposal-mandated sections — (1) the
**unequal-rank non-interval witness** `S = {0,5}` rank 2 on `clusterA`
vs `T = {5}` rank 1 on `bm` (the delivered equal-rank family's
hypothesis exhibited failing on the covered fixture through the rank
supplier), both flanks discharged at `cS = 5/2, rS = 5/2, cT = 5,
rT = 0, δ = 1/2` — the two-pair shape load-bearing (the out-of-`S`
eigenvalue `11` sits between the clusters; no single center covers both
flanks at any radius) — theorem bound `≤ 4` via the imported
`normABm_le` against the independent raw lower `1` at `e₀` (two new
entrywise pins: `P_A({0,5}) = diag(1,1,0)` composing from the exported
`bandClusterA_eq`; `P_bm({5}) = diag(0,1,0)` through the extracted
threshold pair `spBm_four`/`spBm_six`, the latter the two-mode pin at
the second fixture); (2) the ε = 0 attainment through the new theorem
with both flanks genuinely discharged; (3) the **two-sided fence** on
the interior-gap configuration — both `hnear` sides verified, *each*
`hfar` side refuted in proved form at its own interior eigenvalue (the
recorded obstruction configuration itself; `cpQA_fence_hfar_fails`
reused + the new `cpsQA_fence_hfarS_fails`), the hypothesis-free
conclusion refuted at the imported raw lower norm `≥ 1`, the isolation
collected — the two-sidedness itself exercised; (4) the ring-identity
coherence witness pinned entrywise, independent of the private lemma.

**Verification:** the module's theorem green after one fix (the
`rw [l2OpNorm_transpose]` cannot fire unless the transpose is already
syntactically present — the durable structure is an explicit
transpose-equation `have`); the QA after two rounds whose seven
first-pass errors were all one trap — this pin's `le_abs` disjunct
order `b ≤ a ∨ b ≤ -b` with `norm_num` on a false arithmetic goal
normalizing it to a bare `⊢ False` (the display that looks like a
missing contradiction is a wrong-disjunct sign error), plus the
norm-carrying `norm_num at h` over-unfold fixed by explicit RHS
rewrites; `lake env lean` on both modules — zero errors, zero warnings
each; explicit `lake build` targets both ✔ (2193/2193, 2198/2198);
`#print axioms` via `wip/cps_axcheck.lean` on all 19 new declarations —
the standard three only; **full `lake build` ✔ (2261 targets, "Build
completed successfully"; zero warnings in the changed modules — the
log's Scaffold-tree diagnostics the documented pre-existing set, the
docPrime notes upstream Mathlib package replay notes)**; `lint_axioms`
(**9**, unchanged), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1971/9/0**, idempotent). Records updated: the
proposal (status header COMPLETE, the delivery record with the
pin-technique list and open follow-ons), `proposals/README.md` (the
High row retired to the Delivered table; the progress paragraph), README
(1971; the Perturbation row's symmetric-set sentence), the radar (QA
axis synced 1953/50 → 1971/50, held 4.0), the scoreboard (five
verification rows + a new interpretation bullet),
`index/map/perturbation.md` (the section note + declaration row),
`index/sources/davis_kahan_1970.md` (the both-gaps-at-sets mapping
row), this plan, and the activity log. Nothing committed; the prior
runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the standing gated candidates (primitivity-shaped
admission for directed mixing; the honestly-blocked pairwise set shape;
a named consumer pricing the wide-band minimax filter designs), or a
fresh center-out candidate per `docs/6_SGT_BACKLOG.md`.

**Cluster projector — the set-valued spectral projector and its
Davis–Kahan pair; the proposal COMPLETE, Steps 0+1 in one run (run 1,
2026-08-24, run `20260824T161014Z-run-1`;
`proposals/cluster-projector.md`, new this run and selected per the
empty High/Medium queue's recorded handoff — the cluster/symmetric
deliveries' own recorded follow-on, requiring "its own definition +
proposal" exactly as delivered; the two alternative candidates gated
on decisions a run cannot make): DELIVERED — pure hard crust, zero new
axioms (count stays 9; `#print axioms` via `wip/cp_axcheck.lean` on
all 18 public module + 2 set-form + 27 public QA declarations:
`propext, Classical.choice, Quot.sound` only, every one). QA
1925 → 1953 (`ClusterProjector_QA` a new Perturbation-domain file at
28). The projector shelf's interval constraint is gone: consumers
state clusters as sets.**

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/ClusterProjector.lean`
(namespace `SpectralGraphTheory`; minimal imports Spectral + Band; the
umbrella importing it) — the definition
`clusterProjector M hM S := ∑_{λᵢ ∈ S} vᵢvᵢᵀ` (classical decidability,
**junk-free** — a set has no orientation, so none of the band family's
`a ≤ b` guards reappear) with the full interface: the component action
(the mirror of PolyFilter's band form), the **intersection product
law** `P_S * P_T = P_{S ∩ T}` by the *action* route (component action +
basis injectivity + column extraction — load-bearing on the interface
itself rather than an entrywise expansion), idempotence (its diagonal),
disjoint-set orthogonality (its empty intersection), guard-free mode
selection, commutation, capture at sets, the **complement law**
`1 − P_S = P_{Sᶜ}` — the structural fact the window family lacks
(`1 − bandProjector` is not a band projector; this is why the window
difference form needed its separate six-lemma complement engine and
the set form does not), the **band agreement**
`clusterProjector (Set.Ioc a b) = bandProjector a b` (the entire
delivered band family is the interval-set special case), and the
trace/rank supplier (the `rank_bandProjector_eq_card` route). Plus the
new `SetForm` sections of
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`
(+1 import: ClusterProjector): the commutator/shift engine re-run at
membership filters — the **set-form product bound**
`‖Q_T * P_S‖ ≤ ‖A−B‖/δ` and, at equal rank, the **set-form difference
bound** `‖P_A(S) − P_B(T)‖ ≤ ‖A−B‖/δ` under center/radius membership
separation — **no dichotomy, no interior case**: the equal-rank
identity reduces to the one-sided residual and the complement law
rewrites `1 − Q_T = Q_{Tᶜ}` into the product form's own shape. The
YWS-literal *pairwise* set shape is recorded as honestly blocked with
its obstruction named.

**QA (+28):** all four proposal-mandated sections — (1) the
**non-interval witness**: `P_{{0,11}} = diag(1,0,1)` on the imported
`diag(0,5,11)` fixture (a subspace NO window expresses) through a
four-lemma composition (capture at sets, the complement partition, the
singleton pin, the imported threshold pin), with the
idempotence/action/disjointness instantiations and four rank counts
(2/1/2/2) through the trace route; (2) the **non-interval difference
instance** on the new fixture `diag(−1,5,11)` at exact-fit
`c = 11/2, r = 11/2, δ = 1` — the theorem bound `≤ ‖A−B‖/1 ≤ 1` (norm
via the max-abs-eigenvalue bridge at the diagonal difference) joined
with the raw lower `1 ≤ ‖P−Q‖` at `e₀`, both projectors and the
difference pinned entrywise; (3) the ε = 0 attainment at singleton
clusters with the out-of-`T` separation genuinely discharged; (4) the
**`hfar` fence on the interior-gap configuration** — the recorded
obstruction itself (an out-of-`T` eigenvalue inside A's cluster range
at distance `11/2 < 11/2 + 1/2` from `c`) exercised as a hypothesis
fence with ranks equal 2 = 2, `hnear` verified, the hypothesis-free
conclusion refuted at norm ≥ 1, and the isolation collected.

**Verification:** the definition/interface elaborated green after the
filter-instance hygiene was worked out (the sharpest recorded trap:
`Finset.filter` at set-membership elaborates under different
`DecidablePred` instances in definition-unfolded goals versus
`classical`-tactic proofs, so filter-equality rewrites fail on
definition-unfolded filters — the durable fix is the action idiom for
projector proofs and trace-lemma-sourced count pins, both now recorded
in the proposal's pin-technique list; QA-side: simp's normNum fails on
negative real literals and on `abs` goals — explicit
`abs_le`/`le_abs`/`linarith` closes, and entrywise matrix goals need
`simp` (which decides Fin-index ites) before `norm_num`);
`lake env lean` on all three modules — zero errors, zero warnings each
(ClusterProjector's olean built first); explicit `lake build` targets
all ✔ (2010/2010, 2193/2193, 2198/2198); `#print axioms` via
`wip/cp_axcheck.lean` on all 47 accessible declarations — the standard
three only; **full `lake build` ✔ (2261 targets, "Build completed
successfully"; zero warnings in the changed modules)**; `lint_axioms`
(**9**, unchanged), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1953/9/0**, idempotent by md5). Records
updated: the proposal (status header COMPLETE, the full delivery
record with the pin-technique list and the honestly-blocked follow-on),
`proposals/README.md` (the Delivered row; the progress paragraph — the
table empty again), README (1953; the cluster-projector module-table
row; the Perturbation row's set-form sentence), the radar (QA axis
synced 1925/49 → 1953/50, held 4.0), the scoreboard (all four
verification rows + a new interpretation bullet),
`index/map/spectral_graph.md` (the module-list line + the new
section), `index/map/perturbation.md` (the set-form section + 2
declaration rows), `index/sources/davis_kahan_1970.md` (the set-form
mapping row), the umbrella `Scaffold.lean`, this plan, and the activity
log. Nothing committed; the prior runs' deliveries preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — directed-axis mixing/rate work (gated on
primitivity), the pairwise set shape (honestly blocked; needs
eigenvalue-flow machinery), or a named consumer pricing the wide-band
minimax filter designs.

**Band Davis–Kahan symmetric form — the two-sided (both-separations)
constant-2 difference theorem without rank equality; the proposal
COMPLETE, Steps 0+1 in one run (run 1, 2026-08-24, run
`20260824T141936Z-run-1`; `proposals/band-davis-kahan-symmetric.md`,
new this run and added to the Active priority table as its only High
row — the empty High/Medium queue's recorded handoff, the cluster-form
delivery's own first recorded follow-on, and the only named candidate
not gated on a decision a run cannot make): DELIVERED — pure hard
crust, zero new axioms (count stays 9; `#print axioms` via
`wip/bdks_axcheck.lean` on both new public + all 17 public QA
declarations: the standard three only, every one). QA 1908 → 1925
(`BandDavisKahanSymm_QA` a new Perturbation-domain file at 17 by the
generator metric). The delivered difference family's rank obligation
is now optional: consumers holding both pairwise separations state
nothing about multiplicities.**

**Delivered:** the new `SymmetricForm` sections of
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`
(**no new imports**) — the public interface lemma
**`l2OpNorm_transpose`** (`‖Mᵀ‖ = ‖M‖` — absent from the pinned
Mathlib and the shelf; two pairing-characterization applications
around `Matrix.dotProduct_mulVec`/`vecMul_transpose`/`dotProduct_comm`,
closed by `abs_dotProduct_le` + the module's own `l2OpNorm_mulVec_le`)
and the headline
**`l2OpNorm_bandProjector_sub_bandProjector_le_two_of_symm`**
(`‖P_A − P_B‖ ≤ 2‖A − B‖/δ` when *both* out-of-window flanks are
δ-separated pairwise — the YWS both-gaps dimension-freeness with **no
rank hypothesis anywhere**). **The route, exactly the proposal's
worked-through assembly:** the case split at `δ/2 ≤ ‖A−B‖` (trivial
regime via `l2OpNorm_sub_le_one_of_isSymm_idempotent`); in the
contentful regime the private rank-free pairwise product bound
`l2OpNorm_one_sub_bandProjector_mul_bandProjector_le_pairwise` — the
cluster theorem's dichotomy/shrink/engine body minus the identity
conversion, factored once — instantiates at **both argument orders**
(the complement engine's 4th and 5th consumers; the empty-cluster
corner is `P = 0`, not a rank transfer), the ring identity
`P − Q = (I−Q)P − Q(I−P)` plus the transpose move assembles, and
**the constant 2 is exactly that triangle inequality** — no hidden
loss; when ranks genuinely differ, `δ ≤ ‖A − B‖` is forced in-proof
(the honest degradation). One committed-statement correction
recorded: `hsepAB`'s inner hypothesis restated in the family's
conjunction shape over the draft's two-arrow form (a one-line
eta-expansion bridges it to the engine).

**QA (+17, on the *public* cluster fixtures — no new Fin 3 machinery
needed):** (1) the **unequal-rank rank-free witness** — `clusterA`
window `(−1,6]` (rank 2) vs `clusterB` window `(3/2,3]` (rank 1),
both separations discharged on the pinned spectra, ranks pinned 2 ≠ 1
through the supplier (the delivered family's hypothesis exhibited
failing on the covered fixture), raw norm ≥ 1 at `e₀` (B's band action
vanishing through the in-file eigen-equation support pin + component
action + public expansion), bound ≤ 2·7/(1/2) = 28; plus the constant
comparison on the equal-rank rotated fixture (delivered ≤ 1, new ≤ 2,
raw `√(1/10)`); (2) the ε = 0 attainment at genuinely distinct
windows, cross-checked by the imported `bdkc_zeroE_raw`; (3) the
**`hsepAB`-isolated fence** — `Q = 1` through `bandProjector_eq_one`,
`(P − 1) *ᵥ e₁ = −e₁` raw, the hypothesis-free conclusion refuted at
A = B, `hsepBA` provably vacuous-holding — the mirror of the cluster
QA's fence, so both separation sides are now isolated across the QA
family; (4) the **decomposition-coherence witness** — `(I−Q)P *ᵥ e₀`
and `Q(I−P) *ᵥ e₀` computed from imported pins, joined with the
imported raw difference action.

**Verification:** the module's engine ran green on its first complete
pass (two elaboration rounds only, both in QA — the recurring fixes
recorded in the proposal's pin-technique list: `rw ... at` on
conjunction hypotheses silently normalizes them — use `linarith [h,
jin.2]` with inline projections and goal-side per-component rewrites;
`div_le_div_right` deprecated to an iff; `norm_num` does not evaluate
fractional `|9/4|`; `‖0‖` needs `norm_zero` in the chain);
`lake env lean` on the module and the QA file — zero errors, zero
warnings each; explicit `lake build` targets both ✔; `#print axioms`
via `wip/bdks_axcheck.lean` on all 19 accessible declarations —
`propext, Classical.choice, Quot.sound` only; **full `lake build` ✔
(2260 targets, +1 for the new QA module, "Build completed
successfully"; zero warnings in the changed modules)**; `lint_axioms`
(**9**, unchanged), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1925/9/0**, idempotent). Records updated:
the proposal (status header COMPLETE, the full delivery record with
the statement correction and pin-technique list, open follow-ons),
`proposals/README.md` (the Delivered row; the High row retired; the
progress paragraph rewritten — the table empty again), README (1925;
the Perturbation module-table row), the radar (QA axis synced
1908/48 → 1925/49, held 4.0), the scoreboard (all four verification
rows + a new interpretation bullet), `index/map/perturbation.md` (the
symmetric-form rows + 2 declarations), `index/sources/davis_kahan_1970.md`
(the both-gaps mapping row), this plan, and the activity log. Nothing
committed; the prior runs' uncommitted deliveries and the untracked
`docs/scaffold.jpeg` preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — directed-axis mixing/rate work (gated on
primitivity), a set-valued cluster projector (own definition +
proposal), or a named consumer pricing the wide-band minimax filter
designs.

**Band Davis–Kahan cluster form — the eigenvalue-cluster-separated
(pairwise, YWS-Theorem-1-literal) difference theorem, strictly
generalizing the delivered difference form; the proposal COMPLETE,
Steps 0+1 in one run (run 1, 2026-08-24, run `20260824T122219Z-run-1`;
`proposals/band-davis-kahan-cluster.md`, new this run and selected per
the previous run's recorded next handoff — the delivered difference
theorem's own first-named follow-on; the two alternative candidates
gated on decisions a run cannot make): DELIVERED — pure hard crust,
zero new axioms (count stays 9; `#print axioms` via
`wip/bdkc_axcheck.lean` on all 3 public + 37 QA declarations: the
standard three only, every one). QA 1873 → 1908
(`BandDavisKahanCluster_QA` a new Perturbation-domain file at 35 by
the generator metric). The closure-separated difference theorem is now
a special case: the pairwise hypothesis is strictly weaker and covers
configurations the closure form provably cannot reach.**

**Delivered:** new `ClusterForm` sections of
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`
(**no new imports** — the survey found every consumed declaration
already on shelf) — the headline
`l2OpNorm_bandProjector_sub_bandProjector_le_of_pairwise`
(`‖P_A(a₁,b₁] − P_B(a₂,b₂]‖ ≤ ‖A − B‖ / δ` at constant 1 under
*pairwise* separation: every eigenvalue of B outside its window
δ-away from every eigenvalue of A inside its window — the literal YWS
Theorem 1 δ) plus the public capture-equality lemma
`bandProjector_eq_of_forall_mem_iff` (two non-junk windows selecting
the same eigenvalues give the same projector — with window guards
recorded as a committed-statement correction: the unguarded iff-form
is false at reversed junk windows) and the empty-cluster zero lemma
`bandProjector_eq_zero_of_forall_not_mem`. **The route's two new
mathematical facts:** the interior case (a B-eigenvalue strictly
inside A's cluster range, in a gap) forces every A-eigenvalue δ-away
from it, and the eigenvector equation gives `δ ≤ ‖(A−μI)v‖ =
‖(A−B)v‖ ≤ ‖A−B‖` — a projector-free Parseval expansion (F2 with all
components alive) consuming **no Weyl/`evals` bridge**, closing the
trivial regime through `‖P−Q‖ ≤ 1`; the boundary case shrinks A's
window to the cluster range through capture-equality and re-runs the
private complement engine at the cluster-range center/radius, where
the expansion side needs *exactly* the range separation with no slack
(the recorded `+ r` stranding is why the core takes arbitrary `c, r`
— its third load-bearing consumer).

**QA (+35):** all four proposal-mandated sections: (1) the **interior
witness** on the new Fin 3 fixtures `diag(0,5,11)` (window `(−1,6]`,
cluster `{0,5}`) vs `diag(1,2,4)` (window `(0,3]`, cluster `{1,2}`) at
δ = 1 — the closure-separation shape **refuted in proved form**
(`7 ≤ 4` false at the interior 4-mode) while the pairwise hypothesis
discharges, both band projectors pinned entrywise to `diag(1,1,0)`
through an in-file Fin 3 spectral layer (distinct-entry diagonals
force eigenvector support onto single coordinates; orthonormality
forces eigenvalue classes to be singletons), the raw distance exactly
`0` joined with the theorem bound `≤ ‖A−B‖ ≤ 7`; (2) the rotated
two-route witness at the sibling's fixture (bound `≤ 1` against the
imported raw `√(1/10)`); (3) the ε = 0 attainment at genuinely
distinct windows `(−1,2]` vs `(−1/2,5/2]` through the new
capture-equality lemma; (4) the **separation fence** refuted in proved
form (`‖diag(1,−1)‖ ≥ 1 > 0` at A = B) with ranks 1 = 1 and every
guard verified — exactly `hsep` isolated, the mirror of the sibling's
rank fence.

**Verification:** developed in-place in the module (the sibling's
precedent); the elaboration rounds' fixes recorded in the proposal's
pin-technique list (the rw-with-embedded-`by` term trap;
`Finset.min'_le`'s membership-built Nonempty bridged by `congrArg` +
`proof_irrel`; `← sub_mul` for factoring; the `Pi.single` column route
for matrix-from-action equality; `hλ` unparseable because λ is the
lambda keyword; rw auto-closing `le_refl`-trivial branches;
`Finset.sum_eq_single` for literal-free supported-inner products
immune to the `Fin.mk` display trap; one algebra slip — `r + δ` vs
`λmax + δ` — caught by `ring` at elaboration); `lake env lean` on the
module and the QA file — zero errors, zero warnings each; explicit
`lake build` targets both ✔ (2192/2192, 2196/2196); `#print axioms`
via `wip/bdkc_axcheck.lean` on all 40 declarations — `propext,
Classical.choice, Quot.sound` only; **full `lake build` ✔ (2260
targets, +1 for the new QA module, "Build completed successfully";
zero warnings in the changed modules)**; `lint_axioms` (**9**,
unchanged), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1908/9/0**, idempotent). Records updated: the proposal
(status header COMPLETE, the full delivery record with the
pin-technique list and open follow-ons), `proposals/README.md` (the
Delivered row; the progress paragraph rewritten — the table empty
again), README (1908; the Perturbation module-table row; the status
paragraph's cluster sentence), the radar (QA axis synced 1873/47 →
1908/48, held 4.0), the scoreboard (all four verification rows + a
new interpretation bullet), `index/map/perturbation.md` (the
cluster-form rows + 3 declarations), `index/sources/davis_kahan_1970.md`
(the YWS-Theorem-1-literal mapping row), this plan, and the activity
log. Nothing committed; the prior runs' uncommitted deliveries and
the untracked `docs/scaffold.jpeg` preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the two-sided symmetric-gap constant-2 form (own
document), directed-axis mixing/rate work (gated on primitivity), or a
named consumer pricing the wide-band minimax filter designs.

**Band Davis–Kahan difference form — the sin-Θ (subspace-distance)
theorem for band projectors; the equal-rank identity's first consumer;
the proposal COMPLETE, Steps 0+1 in one run (run 1, 2026-08-24, run
`20260824T102440Z-run-1`; `proposals/band-davis-kahan-difference.md`,
new this run and selected per the previous run's recorded next
handoff — the delivered product theorem's own open follow-on, with the
two alternative candidates gated on decisions a run cannot make):
DELIVERED — pure hard crust, zero new axioms (count stays 9; `#print
axioms` via `wip/bdkd_axcheck.lean` on all 5 public + 21 QA
declarations: the standard three only, every one). QA 1852 → 1873
(`BandDavisKahanDiff_QA` a new Perturbation-domain file at 21). The
delivered-but-never-consumed equal-rank identity
`ProjectionGap.l2OpNorm_sub_eq_of_rank_eq` now carries weight, exactly
the falsifiability principle's use case.**

**Delivered:** new sections of
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`
(one new import: ProjectionGap; no umbrella change — the module was
already imported) — the headline pair
`l2OpNorm_bandProjector_sub_bandProjector_le` /
`_le_of_mem`:
`‖P_A(a₁,b₁] − P_B(a₂,b₂]‖ ≤ ‖A − B‖ / δ` at **constant 1** for
equal-rank band projectors under one-sided eigenvalue separation (B's
out-of-window eigenvalues δ-away from A's window closure `[a₁, b₁]`;
the margin corollary `a₂ + δ ≤ a₁`, `b₁ + δ ≤ b₂` discharges it for
contained windows) — the classical Davis–Kahan / YWS-Thm-1
operator-norm difference shape. **The route:** the equal-rank identity
reduces the difference to `‖(I − Q_B) · P_A‖`, and the
commutator/shift engine re-runs verbatim at the complement projector
`Q' = 1 − Q_band(B)` (F1 compression and range invariance reused
unchanged; the master inequality and r-cancellation transfer as-is;
the one genuinely new mathematical fact is the **complement
expansion** — `Q'`-fixed vectors have vanishing in-band components
(from `Q_band *ᵥ z = 0`, extracted by `sub_sub_cancel`), so Parseval
leaves exactly the out-of-band modes the separation bounds). The
bounded A-window is load-bearing exactly as in the product form; the
complement window's unboundedness is harmless (the expansion side
needs only separation, never a containment radius — the precise sense
in which the difference form is *easier* than the half-line product
form the Duhamel route had to work for). Plus the public **rank
supplier** `rank_bandProjector_eq_card` (rank = in-band eigenvalue
count via trace, through the exact `{0,1}` spectrum of a symmetric
idempotent — the new private `eigvalOf_isSymm_idempotent_sq`, apply
`S² = S` to the eigen-equation; the shelf's membership lemma gives
only `[0,1]`, which cannot identify count-nonzero with trace) with
its trace parents — making the equal-rank hypothesis *checkable*
rather than merely statable.

**QA (+21):** all four proposal-mandated sections on the reused
fixtures (`diag13` and the rotated `bdkB` from `BandDavisKahan_QA` by
QA-to-QA import): (1) the positive two-route witness — the rank
equality *supplied through the new supplier* (counts 1 = 1 from the
pinned spectra), separation at δ = 3/4, theorem bound `≤ 1` against
the raw lower `1/√10` (the window-parametric, sign-independent
eigenbasis resolution `Q *ᵥ e₀ = ![9/10, −3/10]` from the `(3,−1)`
direction and the `9/10`/`1/10` coordinate squares, no `eigvecOf`
value assumed), plus the **identity-coherence witness** `bdkd_coherence`
pinning `((I−Q)·P) *ᵥ e₀ = (P−Q) *ᵥ e₀` by two independent raw routes —
the consumed identity's content exhibited numerically; (2) the ε = 0
attainment (A = B, identical windows, separation genuinely holding at
δ = 1/2 via the out-of-window eigenvalue 3) with the independent zero
pin; (3) the margin-corollary instance at B's window `(−2, 3]`, δ = 1
(bound `≤ 3/4` vs raw `1/√10`); (4) the **rank fence** `bdkd_rank_fence`
— A = B = diag13, windows `(3/2, 5/2]` (empty, rank 0) vs `(5/2, 7/2]`
(occupied, rank 1), every other hypothesis verified (`hlo` at
`1 ≤ 5/2 → 1 ≤ 3/2 − 1/2` exact, `hhi` vacuous), the hypothesis-free
conclusion `‖P − Q‖ ≤ 0` refuted with the norm lower-bounded by `1`
at `e₁` — and `bdkd_fence_only_rank_fails` proving the rank equality
the *only* failing hypothesis (exactly `hrank` isolated).

**Verification:** developed in-place in the module (the private
helpers are inaccessible to a separate spike file — the deliberate
cost of the same-module decision, repaid by the engine compiling green
on its first complete pass); the rounds' fixes recorded in the
proposal's pin-technique list (the scalar-position `sub_smul`/`mul_smul`
trap; `sub_mul` being left-subtraction at this pin; the
`Fin.mk`-index typed-`have` bridge; iterative `simp only` for
coefficient cleanup after `if_pos`/`if_neg`; `rw` rewriting only the
first-matched instantiation, so two `norm_euclidean_eq_sqrt` rewrites
where two different packed vectors occur); `lake env lean` on the
module and the QA file — zero errors, zero warnings each; explicit
`lake build` targets both ✔ (2192/2192, 2195/2195); `#print axioms`
via `wip/bdkd_axcheck.lean` on all 26 declarations — `propext,
Classical.choice, Quot.sound` only; **full `lake build` ✔ (2260
targets, +1 for the new QA module, "Build completed successfully";
zero warnings in the changed modules)**; `lint_axioms` (**9**,
unchanged), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1873/9/0**, idempotent). Records updated: the proposal
(status header COMPLETE, the full delivery record with the
pin-technique list and open follow-ons), `proposals/README.md` (the
Delivered row; the progress paragraph rewritten — the table empty
again), README (1873; the Perturbation module-table row), the radar
(QA axis synced 1852/46 → 1873/47, held 4.0), the scoreboard (all
four verification rows + a new interpretation bullet + the previous
product-form bullet de-staled), `index/map/perturbation.md` (the
section extended + 5 declaration rows + the Deferred-Work note
de-staled), `index/sources/davis_kahan_1970.md` (the difference-form
mapping row), backlog item 9 (the difference-form delivery closing the
named program), this plan, and the activity log. Nothing committed;
the prior runs' uncommitted deliveries and the untracked
`docs/scaffold.jpeg` preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the eigenvalue-cluster-separated generalization of
the difference form (own document), directed-axis mixing/rate work
(gated on primitivity), or a named consumer pricing the wide-band
minimax filter designs.

**Band Davis–Kahan — backlog item 9, the bounded-window perturbation
theorem for band projectors; the proposal COMPLETE, Steps 0+1 in one
run (run 1, 2026-08-24, run `20260824T081731Z-run-1`;
`proposals/band-davis-kahan.md`, new this run and added to the Active
priority table as its only High row — the empty High/Medium queue's
recorded handoff, the backlog's own named candidate, and the
Davis–Kahan Step-0/1 survey's named follow-on): DELIVERED — pure hard
crust, zero new axioms (count stays 9; `#print axioms` via
`wip/bdk_axcheck.lean` on all 5 public + 20 QA declarations: the
standard three only, every one). QA 1832 → 1852
(`BandDavisKahan_QA` a new Perturbation-domain file at 20). The Band
module has its first perturbation-theory consumer and the perturbation
area its first Band composition; the PolyFilter component-action
interface is a two-consumer interface.**

**Delivered:** the new
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/BandDavisKahan.lean`
(minimal imports PolyFilter + Duhamel; the umbrella importing it) —
the headline pair `l2OpNorm_bandProjector_mul_bandProjector_le_of_lt` /
`_of_gt`: `‖Q * P‖ ≤ ‖A − B‖ / δ` for the band projectors of two
symmetric matrices on δ-separated windows `(a₁, b₁]`/`(a₂, b₂]`
(interval separation `b₁ + δ ≤ a₂` or `b₂ + δ ≤ a₁`; the center/radius
instantiation `c = (a₁+b₁)/2`, `r = (b₁−a₁)/2` discharged inside by
interval arithmetic), constant 1, no rank hypothesis, no sorted-spectrum
index — by the survey's algebraic commutator/shift route. **The proof's
mathematical content is the r-cancellation**: the naive single-shift
assembly strands `+ r` (the recorded catch that kills the technique at
the half-line window — which is why this and `davis_kahan_sin_theta`
are genuinely different theorems), and the rescue is *range invariance*
(`(A − cI) *ᵥ (P *ᵥ y)` stays in `P`'s range), bounding the compressed
term by `r · ‖Q * P‖ · ‖y‖` so the `r` cancels algebraically:
`(r+δ)‖(Q*P)*ᵥy‖ ≤ (r‖QP‖ + ‖A−B‖)‖y‖` for all `y`, transported
through Duhamel's pairing engine to `δ ‖QP‖ ≤ ‖A−B‖`. Load-bearing on
four delivered layers at once (Band's idempotence and eigenbasis
action, Spectral's Parseval and eigenaction, PolyFilter's band
component action, Duhamel's pairing/norm engine). Both Step-0-priced
shelf gaps landed as public interface lemmas: `l2OpNorm_mulVec_le`
(the vector action bound in the sqrt-packaging, absent from the pinned
Mathlib — through `cstar_norm_def` + `toEuclideanCLM` +
`le_opNorm`) and `mulVec_bandProjector_comm` (the 2026-08-21 survey's
spike-verified commutation, previously unlanded; componentwise through
the eigenbasis).

**QA (+20):** all four proposal-mandated sections on the rotated
fixture `bdkB = !![1, 3/4; 3/4, 3]` (spectrum `{3/4, 13/4}` from trace
`4`/determinant `39/16`, the Band_QA pinning idiom) against `diag13`
reused from `Band_QA` (QA-to-QA import): (1) the positive witness —
raw lower `√(1/10) ≤ ‖Q * P‖` completely independently of the theorem
(`bdk_QPe0_sq`: the filtered action resolved through B's eigenbasis
with per-index band membership from the pinned spectrum and the
surviving coordinate square from the eigen-equation direction
constraint `v j 1 = 3 · v j 0` + unit norm — no `eigvecOf` value
assumed; the norm lower bound through the delivered `l2OpNorm_mulVec_le`
at `e₀`) joined with the theorem's upper bound `≤ 3/4` (the
perturbation norm bounded via the pairing engine's swap trick); (2)
the ε = 0 attainment (disjoint windows on `A = B = diag13`: the
theorem reads `≤ 0`, the norm `= 0` attained, cross-checked by Band's
disjoint-band product law); (3) the fence — identical windows: the
hypothesis-free conclusion **refuted in proved form** (`P * P` = the
nonzero projector `diag(1,0)`, norm `≥ 1` through the action bound,
RHS `= 0`) with every `hsep`-shaped hypothesis exhibited impossible —
the separation exercised as a fence, not decoration; (4) the mirror
`_of_gt` orientation at δ = 1/2 with the same two-route pattern at
`e₁` (bottom-mode constraint `v0 = −(3 · v1)`).

**Verification:** spike first (`wip/bdk_spike.lean`, several rounds to
green — the fixes recorded in the proposal's delivery record as the
pin-technique list: `mulVec_mulVec` takes the vector first and fires
on the first-unified instance; explicit calc steps with fully-applied
arguments to avoid whnf timeouts; norm_num evaluates the ite band
conditions; `le_div_iff₀` both projection directions; the Fin 2
eta-expansion and `linear_combination`-coefficient techniques re-hit
QA-side); `lake env lean` on the module and the QA file — zero errors,
zero warnings each; explicit `lake build` targets both ✔; `#print
axioms` via `wip/bdk_axcheck.lean` on all 25 declarations — `propext,
Classical.choice, Quot.sound` only; **full `lake build` ✔ (2260
targets, +1, "Build completed successfully"; zero warnings in the
changed modules)**; `lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1852/9/0**,
idempotent). Records updated: the proposal (status header COMPLETE,
the delivery record with the trap list and the priced follow-ons),
`proposals/README.md` (the High row retired to the Delivered table;
the progress paragraph rewritten — the table empty again), README
(1852; the proved-list sentence; the module-table row), the radar (QA
axis synced 1832/45 → 1852/46, held 4.0), the scoreboard (all four
verification rows + a new interpretation bullet),
`index/sources/vershynin_hdp.md` (Chapter 4 note: route reference →
the delivered mapping), `index/map/perturbation.md` (new section + 4
declaration rows), backlog item 9 (DELIVERED note with the recorded
follow-on), the umbrella `Scaffold.lean`, this plan, and the activity
log. Nothing committed; the prior runs' uncommitted deliveries and
the untracked `docs/scaffold.jpeg` preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the band Davis–Kahan *difference* form (own
document, consuming the delivered equal-rank identity), directed-axis
mixing/rate work (gated on primitivity), or a backlog-gated item.

**PolyFilter band projection — the Chebyshev layer's second consumer;
the proposal COMPLETE, Steps 0+1 in one run (run 1, 2026-08-24, run
`20260824T064113Z-run-1`; `proposals/polyfilter-band-projection.md`,
new this run and added to the Active priority table as its only High
row — the empty High/Medium queue's recorded handoff, first-named
candidate in all three records, and the Krylov Step-0 survey's own
named follow-on): DELIVERED — pure hard crust, zero new axioms (count
stays 9; `#print axioms` on all 7 public + 30 QA declarations via
`wip/polyfilter_axcheck.lean`: the standard three only), QA 1804 →
1832 (`PolyFilter_QA` a new file at 28 by the generator metric); the
Krylov Chebyshev scalar layer is now a *two-consumer* layer and the
Band module has its first approximation-theory consumer.**

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/PolyFilter.lean`
(namespace `SpectralGraphTheory`; minimal imports Band + Krylov +
Resolvent; the umbrella importing it) — the two component-action
interface lemmas (`eigvecOf_dotProduct_spectralProjector_mulVec`,
`eigvecOf_dotProduct_bandProjector_mulVec` — the
`dotProduct_eigvecOf_mulVec` mirrors at the two projectors, the band
one's `a ≤ b` guard load-bearing for the indicator form and documented
as such: the total definition is the *negated* band at `a > b`), the
**transfer theorem** `aeval_sub_bandProjector_l2OpNorm_le` at exactly
the Step-0 committed hypothesis-form shape (per-eigenvalue filter
quality in, operator norm out), the power instantiation
`powFilter_l2OpNorm_le` (ε = `(t/c)^d`), `chebyshevFilter` + its
closed-form eval lemma, and the **Chebyshev-damped instantiation**
`chebyshevFilter_l2OpNorm_le` (ε = `1/T_d(w(Ltop))`), consuming
`abs_T_eval_le_one`, `one_le_eval_T_of_one_le`, `bandMap` and three of
its four pins — the second consumer of the same scalar layer that
carried Kaniel–Paige. **The survey's decisive structural finding cashed
out in the proof: no eigenvalues of the difference matrix are computed
anywhere** — the Resolvent upper-bridge route (per-mode component
identities + Parseval + `opNorm_le_bound`/`cstar_norm_def`) resolves
the difference's *action* through the eigenbasis. Load-bearing by the
falsifiability test: the transfer theorem consumes the exact shapes of
four delivered layers at once (Krylov's polynomial transfer, the Band
eigenbasis action, Spectral's Parseval, the Resolvent spine) — a
misstatement in any one breaks it loudly.

**QA (+28):** all four proposal-mandated sections on the `diag13`
fixture **reused from `Band_QA`** (the QA-to-QA import precedent — the
spectral analysis, eigenvalue membership, and threshold-projector pins
already proved): (1) exact recovery — the affine filter `(X−1)/2`
drives the engine to `‖p(M) − B_{1,3}‖ = 0`, theorem route (ε = 0 +
`norm_nonneg`) and raw route (both sides pinned entrywise to
`diag(0,1)`, one by the matrix homomorphism laws, one by the
threshold-projector pins); (2) the power filter at `t = 1`, `c = 3`,
every `d` — instantiation, the ε constant **attained** at the low mode
(`p.eval 1 = (1/3)^d`), and the filtered action on the low mode
cross-checked by an independent raw route through the generic
eigenvector action (`![1,0]` an eigenvector by literal computation,
not by the spectral theorem's choice); (3) the Chebyshev-damped filter
at `Lbot = 1`, `t = 2`, `Ltop = 3` — the raw Chebyshev pins `T₁(3) =
3`, `T₂(3) = 17`, `T₁(−1) = −1`, instantiations at `d = 1` (ε = 1/3)
and `d = 2` (ε = 1/17) with the damped values at both modes pinned (ε
attained at the low mode), and the **rate comparison** `1/17 < (2/3)²
= 4/9` — the two instantiations of one engine compared at a single
gap; (4) the fence — the constant filter `1` (perfect in-band) has its
out-of-band quality hypothesis **refuted** at the low mode, and the
hypothesis-free conclusion refuted in proved form (`‖1 − B_{2,3}‖ ≥ 1
> 1/2`, the norm lower-bounded through the fixed unit vector by the
`abs_eigvalOf_le_l2OpNorm` vector technique — no eigenvalue of the
difference computed).

**Verification:** spike first (`wip/polyfilter_spike.lean` — the
transfer engine green on its first complete compile; the fixes
becoming the proposal's recorded trap list, the sharpest being the
`rw`-order-vs-syntactic-appearance interaction at the negated band
conditions — typed `have`s per condition, the PageRank technique —
and the `ℤ`-cast trap's QA face: the module's `(d : ℤ)` instantiated
at literals produces natCast forms the pin's `T_one`/`T_two` cannot
`rw` with — state QA pins in the natCast spelling and bridge with
`push_cast`; the numeric-default trap re-hit at the statement level
(`(1/3)^d` needs `((1:ℝ)/3)^d`)); `lake env lean` on the module and
the QA file — zero errors, zero warnings each; explicit `lake build`
targets both ✔; `#print axioms` via `wip/polyfilter_axcheck.lean` on
all 37 declarations — `propext, Classical.choice, Quot.sound` only;
**full `lake build` ✔ (2259 targets, +1, "Build completed
successfully"; zero warnings in the changed modules)**; `lint_axioms`
(**9**, unchanged), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1832/9/0**, idempotent). Records updated:
the proposal (status header COMPLETE, the full delivery record with
the trap list and the priced follow-ons), `proposals/README.md` (the
High row retired to the Delivered table; the progress paragraph
rewritten — the table empty again), README (1832; the status
paragraph's polyfilter sentence; the module-table row), the radar (QA
axis synced 1804/44 → 1832/45, held 4.0), the scoreboard (all three
verification rows + a new interpretation bullet), the SGT index map
(new section + 7 declaration rows, the module-list line), the
umbrella, this plan, and the activity log. Nothing committed; the
prior runs' uncommitted deliveries and the untracked
`docs/scaffold.jpeg` preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — directed-axis mixing/rate work (gated on
primitivity), backlog item 9's band Davis–Kahan (own proposal + Step
0), or a named consumer pricing the wide-band minimax filter designs.

**PageRank — the second Perron–Frobenius consumer; the proposal
COMPLETE, Steps 0+1 in one run (run 1, 2026-08-24, run
`20260824T045932Z-run-1`; `proposals/pagerank-distributions.md`, new
this run and added to the Active priority table as its only High row
— the empty High/Medium queue's recorded handoff, backlog item 8's
named second consumer, and the PF admission's own follow-on list):
DELIVERED — zero new axioms (count stays 9), QA 1715 → 1804
(`PageRank_QA` a new file at 89 by the generator metric); the
directed axis' stationary theory now reaches **reducible** input,
conditional on `perron_frobenius` exactly as the parent layer.**

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/PageRank.lean`
(namespace `SpectralGraphTheory`; minimal imports IrreducibleStationary
+ Normalized; the umbrella importing it) — the nine unconditional
structural declarations (`googleMatrix` + `_apply` entry form;
`walkTransitionMatrix_nonneg`; `googleMatrix_nonneg`; **the
teleportation floor `googleMatrix_pos`** — `0 < G i j` at every pair
on `[0,1)` with nonempty `V` from the additive `(1−α)·(card V)⁻¹`
alone; the α-free `googleMatrix_row_sum` (affine — survives both
fence endpoints where uniqueness dies); `googleMatrix_deg_eq_one`;
**`googleMatrix_isIrreducible`** — irreducibility *derived*, not
assumed, one `ReflTransGen.single` per pair through the floor; and
the general bridge `walkTransitionMatrix_eq_of_row_sum_one`) and the
three axiom-**conditional** theorems `exists_pageRankVec`,
`existsUnique_pageRankVec` (**no irreducibility hypothesis on the
input** — the entire point), `pageRankVec_pos` — pure compositions
of the same-day `IrreducibleStationary` layer at
`M := googleMatrix A α`, every hypothesis derived structurally, the
conclusion translated through the bridge; **zero new axiom contact**
(the two axiom applications stay inside the delivered engine).

**QA (+89):** all four mandated sections — (1) structural on the
reducible two-edge fixture: all 16 entries pinned (`1/8`/`5/8`), the
floor at a zero-support pair by theorem *and* raw route, row sums
both routes, the bridge instantiated, irreducibility on input whose
own irreducibility provably fails; (2) the reducible-input positive
witness: uniform `(1/4,1/4,1/4,1/4)` verified **completely raw**
with the `∃!` join `A4G_stationary_eq_uniform_QA` — on the very
fixture whose raw walk has two stationary distributions (the
imported fence); (3) the asymmetric star at `α = 1/2`: PageRank
`(4/9, 5/18, 5/18)` verified raw, the join `A3G_eq_hand_QA`, and
`pr3_ne_pi3_QA` — provably distinct from the raw stationary
(teleportation shifts mass to the leaves); (4) both endpoint fences
refuted in proved form, complementary: `α = 1` (`G = P` pinned
entrywise, `∃!` refuted through the imported witnesses, exactly
`hα2` isolated) and `α = -1` on `K₂` (`G = 1` pinned, two distinct
stationary point masses, row stochasticity surviving, exactly `hα`
isolated).

**Verification:** spike first (`wip/pagerank_spike.lean` then
`wip/pagerank_qa_spike.lean`, rounds to green — the fixes recorded in
the proposal's pin-technique list: the annotated `∑ j : V` binder for
constant summands; the constant sum built backwards through
`Finset.mul_sum` (no ℕ-smul cast lemma at the pin); the `∃!`
destructure's explicit grouping; `Fintype.card_pos` inside
`Nat.cast_pos.mpr` stranding a `Fintype ?m` metavariable — isolate in
a typed `have`; the `fin_cases` `Fin.mk`-index literal-lemma trap
re-hit and worked around per the recorded techniques); `lake env lean`
on the module and the QA file — zero errors, zero warnings each;
explicit `lake build` targets both ✔; `#print axioms` via
`wip/pagerank_axcheck.lean` on all 12 public + 85 QA declarations —
the split exactly as specified (3 public + 6 QA theorems list
`perron_frobenius` + the standard three; everything else, fences
included, the standard three only); **full `lake build` ✔ (2258
targets, +1, "Build completed successfully"; zero warnings in the
changed modules)**; `lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1804/9/0**,
idempotent). Records updated: the proposal (status header COMPLETE,
the full delivery record with the trap list and open follow-ons),
`proposals/README.md` (the High row retired to the Delivered table;
the progress paragraph rewritten — the table empty again), README
(1804; the PF-axiom paragraph's second-consumer sentence, clearly
marked conditional; the module-table row), the radar (QA axis synced
1715/43 → 1804/44, held 4.0), the scoreboard (all four verification
rows + a new interpretation bullet), the SGT index map (new section +
12 declaration rows), backlog item 8 (the fifth update — the
named-consumer program fully delivered), the umbrella, this plan, and
the activity log. Nothing committed; the prior run's uncommitted
deliveries and the untracked `docs/scaffold.jpeg` preserved
untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the Chebyshev-filter second consumer (own
document), directed-axis mixing/rate work (gated on primitivity), or
a backlog-gated item.

**Irreducible stationary distributions — the first Perron–Frobenius
consumer; the proposal COMPLETE, Steps 0+1 in one run (run 1,
2026-08-24, run `20260824T024831Z-run-1`;
`proposals/irreducible-stationary-distributions.md`, added to the
Active priority table this run as its only High row — the empty
High/Medium queue's recorded handoff and backlog item 8's own
"unblocked as separate follow-on proposals" note): DELIVERED — zero
new axioms (count stays 9), QA 1621 → 1715
(`IrreducibleStationary_QA` a new file at 94); the directed axis'
first theorem, and the `perron_frobenius` axiom's first theorem
consumer, **conditional on that axiom** exactly as the proposal
specified.**

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/IrreducibleStationary.lean`
(namespace `SpectralGraphTheory`; minimal imports PerronFrobenius +
Normalized; the umbrella importing it) — the unconditional transfer
lemmas `isIrreducible_transpose` (strong connectivity is
arc-reversal invariant, through a private `ReflTransGen` head-induction
flip) and `walkTransitionMatrix_isIrreducible` (positive row scaling
preserves the support digraph, through a private `ReflTransGen`
congruence — the pin has `mono` for `ReflGen` only), and the five
axiom-conditional theorems: `exists_walkPerronVector` (the transposed
Perron engine: a strictly positive vector fixed by `Pᵀ *ᵥ ·`, unique
up to positive scale among nonzero nonnegative fixed vectors — the
walk's Perron root pinned to `1` by the axiom's
eigenvalue-identification clause at `onesVec` through the shelf's
row-stochasticity, the transposed root by the bilinear pairing
`v ⬝ᵥ (P *ᵥ u) = (Pᵀ *ᵥ v) ⬝ᵥ u` via the pin's
`Matrix.dotProduct_mulVec`/`Matrix.mulVec_transpose` — no charpoly,
no complex-domination clause anywhere),
`exists_stationaryVec_of_irreducible` (existence with full support
and normalization), `stationaryVec_smul_of_irreducible` (uniqueness
up to positive scale among all nonzero nonnegative stationary
vectors), `existsUnique_stationaryVec_of_irreducible` (the textbook
`∃!` among nonnegative distributions, positivity derived), and
`stationaryVec_pos_of_irreducible` (full support). Load-bearing per
the strategy's falsifiability test: clauses 5 and 6 consumed
structurally — a misstated either breaks the derivation loudly.

**QA (+94):** all three proposal-mandated witnesses — (1) the
asymmetric directed star `!![0,1,1; 1,0,0; 1,0,0]` on `Fin 3` (two
vertices cannot carry an asymmetric irreducible walk): all four
hypotheses hand-verified (irreducibility by nine explicit
reachability certificates), walk entries pinned, the hand value
`(1/2, 1/4, 1/4)` verified **completely raw** (all three predicates
against pinned walk entries), and the load-bearing join
`A3_stationary_eq_hand_QA`: every stationary distribution of the
fixture, however produced, equals the hand value; (2) the
symmetric-cone `K₂` agreement: `A2_stationary_eq_stationaryVec_QA`
pins the PF-unique distribution *equal* to `stationaryVec`, the
predicate supplied entirely by the shelf's detailed-balance chain
(`stationaryVec_pos`/`sum_stationaryVec`/`walk_isStationary` flipped
through `mulVec_transpose`) — two independent API paths to one value
— with the combinatorial value computed through its own definition to
`(1/2, 1/2)`; (3) the reducibility fence on two disjoint `Fin 4`
edges: both witnesses' predicates verified raw with `hnn`/`hdeg`
verified intact, the hypothesis-free `∃!` conclusion **refuted in
proved form** (two distinct stationary distributions), and the
hypothesis-free scale-uniqueness conclusion refuted on the same
fixture (the scalar forced to `0` against its positivity); plus the
full-support instantiation reading exactly the hand values.

**Verification:** spike first (`wip/pfc_spike.lean`, four rounds to
green — the surveyed route held verbatim; the fixes becoming the
proposal's recorded trap list, the sharpest being: `first | exact`
alternatives commit before embedded `by`-blocks are checked, so a
structurally-applicable alternative with a failing embedded proof
swallows the branch — the irreducibility proofs' arc-`have` +
named-`exact` structure exists to defeat it; the scoreboard's
declaration counter is ASCII-only, so unicode QA identifiers are
silently uncounted — QA names stay ASCII (`pi3`/`pi4a`/`pi4b`), which
moved the file's count 63 → 94; entry/degree lemmas at literal indices
match `rw`/`simp only` freely but under `fin_cases` only
`simp [lemma]` at predicate level — finite sums are evaluated through
literal component lemmas assembled by `funext` + `fin_cases` +
`exact`); `lake env lean` on the module and the QA file — zero
errors, zero warnings each; explicit `lake build` targets both ✔;
`#print axioms` via `wip/is_axcheck.lean` on all 7 public + 12
representative QA declarations — the split exactly as specified (the
5 axiom-consuming public theorems and 4 axiom-route QA theorems list
`perron_frobenius` + the standard three; the transfer lemmas and every
raw QA lemma only the standard three); **full `lake build` ✔ (2257
targets, +1, "Build completed successfully"; zero warnings in the
changed modules — the log's only Scaffold diagnostic the documented
pre-existing unused-variable note in untouched
`Derived/ProjectorDrift.lean`)**; `lint_axioms` (**9**, unchanged),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**1715/9/0**, idempotent). Records updated: the proposal (status
header COMPLETE, the full delivery record with the trap list and the
open follow-ons — PageRank, the symmetric-connected→irreducible
bridge, directed mixing gated on primitivity), `proposals/README.md`
(the High row retired to the Delivered table; the progress paragraph
rewritten — the table empty again), README (1715; the PF-axiom
paragraph's first-consumer sentence, clearly marked conditional; the
module-table row), the radar (QA axis synced 1621/42 → 1715/43, held
4.0), the scoreboard (all four verification rows + a new
interpretation bullet), the SGT index map (new section + 7 declaration
rows), backlog item 8 (the fourth update recording the first named
consumer delivered), the umbrella, this plan, and the activity log.
Nothing committed; the prior run's uncommitted Krylov Step-1c
delivery and the untracked `docs/scaffold.jpeg` preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the PageRank consumer (own document), the
Chebyshev-filter second consumer (own document), or a backlog-gated
item.

**Approximate spectral projection, Step 1c — the final statement + QA;
the proposal COMPLETE (run 1, 2026-08-24, run `20260824T012049Z-run-1`;
`proposals/approximate-spectral-projection.md` Step 1c, the leading
Medium row of the Active priority table — which held no High rows —
the Step-1b run's recorded next handoff, and the proposal's recorded
open next step): DELIVERED — pure hard crust, zero new axioms (count
stays 9), QA 1606 → 1621 (`Krylov_QA` 35 → 50).**

**Delivered:** the new Step-1c section of
`Scaffold/Mathlib/GraphTheory/Krylov.lean` — **`kanielPaige`**, the
program's public mathematical statement at exactly the Step-0 recorded
shape: unit `b` with `u ⬝ᵥ b ≠ 0` as the *only* starting-vector
hypothesis (no hand-supplied `c`/`s`/`g` — the decomposition is
internal via the 1b `exists_unit_decomposition`), the bound in the
classical `tan²φ`/gap form `(Ltop − Lbot) · (1 − (u ⬝ᵥ b)²)/(u ⬝ᵥ b)² /
T_{k−1}(1 + 2γ)²` at `γ = (Ltop − Ltwo)/(Ltwo − Lbot)` — composed from
`kanielPaigeChebyshev` by exactly three identifications (`c = u ⬝ᵥ b`
by orthogonality, `s² = 1 − c²` by the unit norm, `w(Ltop) = 1 + 2γ` by
the band map's closed form at `congr 1` + `field_simp`). The Saad §6
locator attaches to the statement's docstring with the proposal's
clean-room verify-against-the-physical-copy caveat carried verbatim
(the statement is proved, not admitted).

**QA (+15):** the four witnesses the plan names — (1) the final-form
instantiation on `diag(3,1,0)` at `k = 2` with the γ-form Chebyshev
value `T₁(5) = 5` proved raw (`T_one`) *and* equal to the 1b
composite's `(T₁ ∘ w)(3)`, the final bound **proved expression-equal
to the composite's** (both `16/75` — a wrong `γ`-form or inverted
`tan²φ` in the restatement breaks the equality), the raw true gap
`32/241` strictly inside; (2) the `k = 1` degenerate case (`T₀ ≡ 1`
pinned, bound = the plain Rayleigh-gap value `16/3`, the actual gap at
the only Krylov direction computed raw `3 − 43/25 = 32/25 ≤ 16/3`);
(3) the `b = u` tightness (bound `= 0`, the delivered witness's
Rayleigh value pinned to exactly `Ltop` from both sides — theorem
below, raw entrywise ceiling `3y₀² + y₁² ≤ 3(y₀²+y₁²+y₂²)` above);
(4) the `λ₁ = λ₂` guard **refuted in proved form** on the new
top-multiplicity fixture `diag(3,3,0)`: every eigenvalue `∈ {3, 0}`
from the eigen-equation alone, the band `[14/5, 29/10]` containing
neither so `hpar` itself is false (all three orthonormal eigenbasis
vectors would be multiples of `e₁`; `t₀t₁ = 0` against `t₀² = t₁² =
1`), and the hypothesis-free conclusion refuted with every *other*
hypothesis verified — the `k = 1` Krylov space collapsed to the line
`ℝ · b` by the span's own definition, every nonzero vector's Rayleigh
value computed to exactly `8/3` by smul-linearity (not entrywise
sums), so the true gap `1/3` provably exceeds the evaluated bound
`1/4`.

**Verification:** spike first (`wip/krylov1c_spike.lean`, several
rounds to green, all `#print axioms` the standard three — the fixes
becoming the 1c pin-technique record: `mul_div_cancel_left₀` strands
on a `MulDivCancelClass` metavariable inside `rw`, use
`rw [div_eq_iff h]; ring` on a standalone `have`; `zero_smul` not
`smul_zero`; `simp [huu, hgu]` where an explicit dotProduct-smul chain
strands on simp's own normalization; the `Fin 3` nested-if trap re-hit
in dot-product sums — `simp [defs, Matrix.dotProduct,
Fin.sum_univ_three]; norm_num`, plain `simp` deciding the index
equalities); `lake env lean` on the module and the QA file — zero
errors, zero warnings each; explicit `lake build` targets both ✔;
`#print axioms` via `wip/krylov1c_axcheck.lean` on all 16 new
declarations (1 public + 15 QA) — `propext, Classical.choice,
Quot.sound` only; **full `lake build` ✔ (2256 targets, "Build
completed successfully"; zero warnings in the changed modules — the
log's only Scaffold diagnostic the documented pre-existing
unused-variable note in untouched `Derived/ProjectorDrift.lean`)**;
`lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1621/9/0**,
idempotent). Records updated: the proposal (status header COMPLETE,
the Step-1c delivery record with pin-technique notes, open-next-step
closed with the recorded follow-ons), `proposals/README.md` (the
Medium row retired to the Delivered table; the progress paragraph
rewritten — the table now holds no High and no Medium rows), README
(1621; the proved-list sentence + module-table row), the radar (QA
axis count synced 1606/42 → 1621/42, held 4.0), the scoreboard (all
four verification rows, a new interpretation bullet, **and the
pre-existing `-**PLACEHOLDER**-` editing artifact from the 1a run's
bullet insertion repaired**), the SGT index map (+1 declaration row,
the section status note → program COMPLETE), this plan, and the
activity log. Nothing committed; the prior runs' uncommitted
deliveries and the untracked `docs/scaffold.jpeg` preserved untouched.

**Next milestone (open):** the center-out policy with an empty
High/Medium queue — the Chebyshev-filter second consumer (own
document), a PF-consumer proposal, or a backlog-gated item.

**Approximate spectral projection, Step 1b — the spectral discharge
(run 1, 2026-08-23, run `20260823T232953Z-run-1`;
`proposals/approximate-spectral-projection.md` Step 1b, the leading
Medium row of the Active priority table — which holds no High rows —
the Step-1a run's recorded next handoff, and the proposal's recorded
open next step): DELIVERED — pure hard crust, zero new axioms (count
stays 9), QA 1590 → 1606 (`Krylov_QA` 19 → 35).**

**Delivered:** the new `KrylovDischarge` section of
`Scaffold/Mathlib/GraphTheory/Krylov.lean` — the **general-eigenvector
transfer layer** (`eigvec_dotProduct_mulVec`, `_pow_mulVec`,
`_aeval_mulVec`: `u ⬝ᵥ (p(M) g) = (u ⬝ᵥ g) · p(μ)` at any eigenvector
— not tied to `eigvecOf`, discharging `horth`, with one
self-adjointness instance closing `horthM`); the **eigenbasis
component layer** (`eigvecOf_dotProduct_aeval_mulVec` plus the
Parseval/quadratic-form resolution identities
`dotProduct_aeval_mulVec_self`/`quadForm_aeval_mulVec` for polynomial
images — the `hband`/`hbottom` engines); the **affine band map**
(`bandMap Ltwo Lbot` with the closed-form eval, the endpoint pins
`w(Lbot) = −1`/`w(Ltwo) = 1`, the range lemma `|w| ≤ 1` on the band,
the growth pin `1 ≤ w(Ltop)`, and `natDegree = 1` — supplying
`hp₁`/`hdeg`/`hTv` at `T_{k−1} ∘ w`); `exists_unit_decomposition`
(unit `b` along unit `u`: `c² + s² = 1`, `g ⊥ u`, `‖g‖² ≤ 1`, no
Cauchy–Schwarz needed — `1 − c²` is the residual's own squared norm);
and the capstone **`kanielPaigeChebyshev`** — the full skeleton
conclusion with every spectral site discharged from the
eigenbasis-level band hypothesis. **The step's mathematical crux: the
band/parallel dichotomy** — `hpar` states "every eigenvector at an
eigenvalue outside `[Lbot, Ltwo]` is a multiple of `u`"; at `g ⊥ u`
this forces every nonzero eigencomponent of `g` into the band (the
multiplicity-2 shape `u = (v₁+v₂)/√2`, `g = (v₁−v₂)/√2` shows why the
weaker "every eigenvector ⊥ u is in-band" form would *not* suffice),
where `|T ∘ w| ≤ 1` caps the polynomial image's norm through Parseval
and the band floor lower-bounds its form through `quadForm_eigvalOf`,
termwise at `Finset.sum_le_sum`.

**QA (+16):** the band-map pins **two routes** (theorems vs. the hand
closed form `w(μ) = 2μ − 1`; the composed growth pair `1 ≤ w(3) = 5`);
the self-adjointness transfer **two routes** at a non-basis
eigenvector of the 2×2 fixture (`e₁ ⬝ᵥ (M ![3,−5]) = 6`, theorem vs.
hand); the polynomial transfer **two routes** (`e₁ ⬝ᵥ p(M) ![1,−1] =
5`, theorem vs. hand `p(M) = diagM² + 1`); and the centerpiece on the
new 3×3 fixture `diag(3,1,0)` (entrywise-encoded per the recorded
`Fin 3` cons-literal trap): **`diag310_hpar_QA` derives the band
hypothesis from the eigen-equation alone** (below-band vacuous by unit
norm; above-band forcing the band coordinates to vanish), **the
composite instantiated end-to-end** at `b = (3e₁ + 4e₂)/5`, `k = 2`,
with the bound value pinned `= 16/75` through `T₁(w(3)) = 5`, and the
**independent raw route** — the actual Krylov witness `(3, 4/5, 0)`
exhibited as the generator combination `2(Mb) − b` (membership by the
span's own definition) with its Rayleigh value computed raw to
`691/241`, so the true gap `32/241 ≈ 0.133` is *proved* strictly
inside the delivered `16/75 ≈ 0.213`; plus the unit-decomposition
instantiation with both content pins forced (`c = 3/5`, `s² = 16/25`).

**Verification:** spike first (`wip/krylov1b_spike.lean` plus the
`wip/krylov1b_iso.lean` isolation, several rounds to green — the fixes
becoming the recorded trap list: `Polynomial.Chebyshev.T` must be
written in full (`open Polynomial` does not reach it, and an
unresolved `T` **silently auto-bounds a universe variable**, surfacing
as "function expected at T"); `.comp` binds tighter than application
(parenthesize the whole polynomial before it);
`Matrix.dotProduct_sum` absent at the pin (a three-line second-slot
helper); `⟨n,⋯⟩`-form `fin_cases` indices resist `rfl` while
`norm_num` strands `¬⟨2,⋯⟩ = 0` conditions that plain `simp` decides —
on `Fin 3`, entrywise fixtures closed by `simp [...] <;> norm_num`;
`simpa [...] using h` robust against equation-splitting simp;
`C_ne_zero` an iff; `pow_le_pow_left` deprecated for
`pow_le_pow_left₀`; `X_comp` vs `comp_X` — the band-poly collapse
needs the former; `omit ... in` before the docstring, and rejected for
transfer chains that legitimately reach `DecidableEq`);
`lake env lean` on the module and the QA file — zero errors, zero
warnings each; explicit `lake build` targets both ✔; `#print axioms`
via `wip/krylov1b_axcheck.lean` on all 14 new public theorems + the
`bandMap` definition + all 16 new QA declarations — `propext,
Classical.choice, Quot.sound` only; **full `lake build` ✔ (2256
targets, "Build completed successfully"; zero warnings in the changed
modules — the log's Scaffold-tree warnings are the documented
pre-existing set in untouched modules)**; `lint_axioms` (**9**,
unchanged), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1606/9/0**, idempotent). Records updated: the proposal
(status header, the full Step-1b delivery record with the trap list,
open-next-step → 1c), `proposals/README.md` (the Medium row + the
progress paragraph), README (1606; the proved-list sentence + module
table row), the radar (QA axis synced 1590/42 → 1606/42, held 4.0),
the scoreboard (all four verification rows, a new interpretation
bullet), the SGT index map (+13 declaration rows, the section's status
note), this plan, and the activity log. Nothing committed; the prior
runs' uncommitted deliveries and the untracked `docs/scaffold.jpeg`
preserved untouched.

**Next milestone (open):** **Step 1c — the final statement + QA**:
`kanielPaige` at the Step-0 recorded shape (unit `b`, `u ⬝ᵥ b ≠ 0`,
the `tan²φ` form), composed from the delivered composite + the
delivered decomposition; QA's remaining witnesses (the `k = 1`
degenerate case recovering the plain Rayleigh gap, the `b = u`
tightness at `tan φ = 0`, the `λ₁ = λ₂` guard refutation on a
top-multiplicity fixture). One run, retiring the milestone.

**Approximate spectral projection, Step 1a — the Krylov/Chebyshev
interface layer (run 1, 2026-08-23, run `20260823T215632Z-run-1`;
`proposals/approximate-spectral-projection.md` Step 1a, the leading
Medium row of the Active priority table — which holds no High rows —
the previous run's recorded next handoff, and the proposal's recorded
open next step): DELIVERED — pure hard crust, zero new axioms (count
stays 9), QA 1571 → 1590 (`Krylov_QA` a new file at 19).**

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/Krylov.lean`
(namespace `SpectralGraphTheory`, at the shelf's `V : Type` interface
per the Step-0 finding; the umbrella importing it) — the scalar
Chebyshev layer (`abs_T_eval_le_one` unchanged from the spike; **both
Step-0-priced shallow gaps closed**: `natDegree_T` by
`Nat.twoStepInduction` + `natDegree_sub_eq_left_of_natDegree_lt`, and
`one_le_eval_T_of_one_le` through the private conjunction engine
`eval_T_pair_mono` — ordinary induction suffices, the recurrence's
step needing nothing beyond the two previous conjunction instances,
with index-monotonicity as the byproduct); the Krylov layer (`sum_mulVec`
the priced pin-gap push; the real **`krylovSpan`** definition — the
hardening over the spike's inlined span; `scalar_mul_eq_smul`;
`aeval_mulVec_eq_eval_smul` through `Heat.pow_mulVec_smul`;
`aeval_mulVec_mem_krylovSpan` restated at `krylovSpan`); and
`kanielPaigeSkeleton` at the spike's exact hypothesis form, its five
named discharge sites preserved verbatim as 1b's contract. The module
docstring carries the survey note (pin gaps closed, the `V : Type`
finding, the citation-boundary note: the Saad §6 citation stays with
the proposal that owns the statement).

**QA (+19, `Scaffold/QA/SpectralGraph/Krylov_QA.lean`):** raw
Chebyshev pins (`T₂(0) = −1` endpoint; `T₃(1/2) = −1` *interior*
band-bound equality through the two-step recurrence; `T₂(1/4) = −7/8`
strict, the band instance composed with the raw value to `7/8 ≤ 1`);
`natDegree` instances (5 and 0); the growth pair two-route (`1 ≤ T₂(2)`
from the theorem, `T₂(2) = 7` raw — genuine growth, not a degenerate
constant); `sum_mulVec` on concrete matrices; the polynomial action by
**two independent routes** (transfer theorem vs. hand-computed
`aeval diagM (X²+1) = diagM² + 1 = !![5,0;0,1]`) plus the annihilator
`(X − 2)(diagM) *ᵥ e₁ = 0`; Krylov membership by two routes (theorem at
`p = X` vs. generator-direct at `i = 1`); the **degree-guard
refutation** (`M e₁ = e₂ ∉ krylovSpan M e₁ 1` — the hypothesis-free
form false, `hdeg` load-bearing); the **composed-use witness**
(`(aeval M (T ℝ 5)) *ᵥ e₁ ∈ krylovSpan M e₁ 6` with `hdeg` from
`natDegree_T` alone — 1b's exact consumption pattern); and the **full
skeleton instantiation** on `diagM = diag(2,0)`, `b = ½(e₁+e₂)`,
`k = 1`, `p = 1` — all twelve hypotheses hand-discharged, the bound
constant pinned `= 2`, the hidden witness's Rayleigh value pinned raw
(`rayleigh diagM b = 1`), so the instantiated bound reads `2 − 1 = 1 ≤
2` end-to-end.

**Verification:** spike first (`wip/krylov1a_spike.lean` green, all
`#print axioms` the standard three — the transfer fixes becoming the
proposal's recorded trap list: `Nat.twoStepInduction`'s `more` case
hands `P n` before `P (n+1)`; `leadingCoeff_eq_zero` cannot rewrite a
`≠` directly — `rw [Ne, …]` first; `(T ℝ 5)` OfNat vs `(T ℝ ↑5)` cast
are rw-incompatible though defeq; **the numeric-default trap's
polynomial face** — an un-ascribed `C 1`/bare `X` in a *goal statement*
elaborates the whole `aeval` at `ℕ[X]`, surfacing as display-identical
`rw` failures until `pp.all` exposes it, and bare `2 • v` picks the
ℕ-smul; cons-junk tails close robustly by `funext i; fin_cases i` +
`norm_num [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two]`);
`lake env lean` on the module and the QA file — zero errors, zero
warnings each; explicit `lake build` targets both ✔; `#print axioms`
via `wip/krylov1a_axcheck.lean` on all 8 public theorems + the
definition + all 19 QA declarations — `propext, Classical.choice,
Quot.sound` only; **full `lake build` ✔ (2256 targets, +3, "Build
completed successfully"; zero warnings in the changed modules — the
log's only Scaffold diagnostic the documented pre-existing
unused-variable note in untouched `Derived/ProjectorDrift.lean`)**;
`lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1590/9/0**,
idempotent). Records updated: the proposal (status header, the full
Step-1a delivery record with the trap list, open-next-step → 1b),
`proposals/README.md` (the Medium row + the progress paragraph),
README (1590; module-table row + proved-list sentence), the radar (QA
axis count synced 1571/41 → 1590/42, held 4.0), the scoreboard (all
four verification rows, a new interpretation bullet), the SGT index
map (new Krylov section + 9 declaration rows), the umbrella, this
plan, and the activity log. Nothing committed; the prior runs'
uncommitted deliveries and the untracked `docs/scaffold.jpeg`
preserved untouched.

**Next milestone (open):** **Step 1b — the spectral discharge**: the
eigenbasis-expansion layer (b's decomposition along the top
eigenvector, `horth`/`horthM` through `IsSymm`, `hbottom` through the
Rayleigh-sandwich mirror, `hband` through `quadForm_eigvalOf` + Parseval
+ `|T ∘ w| ≤ 1` on the band, `hp₁` through the affine band map
`w(λ) = (2λ − λ₂ − λₙ)/(λ₂ − λₙ)` with `natDegree_T` +
`natDegree_comp` supplying `hdeg`). One run. Then 1c (statement + QA,
retiring the milestone).

**Discrete affine convergence — the `sgt-gaps.md` item-2 consumer
interface; the proposal COMPLETE (run 1, 2026-08-23, run
`20260823T194800Z-run-1`; `proposals/discrete-affine-convergence.md`,
the Active priority table's single remaining High row, the previous
run's recorded next handoff, and the proposal's own "authorized to
begin immediately"): DELIVERED — both steps in one run as pure hard
crust, zero new axioms (count stays 9), QA 1546 → 1571 (the new
`Dynamics` domain, `DiscreteAffine_QA` a new file at 25), opening
backlog item 5's discrete-affine slice.**

**Delivered:** the new `Scaffold/Mathlib/Dynamics/DiscreteAffine.lean`
(namespace `Scaffold.Dynamics`, a new `Dynamics` area — the statements
carry no graph structure per the proposal's own scope note, so not the
event-driven `GraphTheory/Dynamics`; minimal imports, the umbrella
importing it) — `tendsto_pow_smul_atTop_nhds_zero` (Step 1: `r ^ n • x
→ 0` for `|r| < 1`, the pin's `tendsto_pow_atTop_nhds_zero_of_abs_lt_one`
lifted through the pin's `Filter.Tendsto.smul_const`, both located by
the survey and re-verified on delivery), `affineIteration_eq` (the
closed form `x_n = (1−α)^n • (x_0 − e) + e`, pure module induction),
and `affineIteration_tendsto_atTop` (Step 2: convergence to the
equilibrium under `0 < α < 2` at the consumer's exact `Tendsto x atTop
(𝓝 equilibrium)` shape). **Statement-shape decision recorded before
stating:** all three at a general real normed space `E` — the proofs
never use finiteness or coordinates, the drafted `V → ℝ`/`Fintype V`
shape is the instance, QA instantiating exactly it (the Tikhonov
Section-5 generality precedent).

**QA (+25, four sections, `Scaffold/QA/Dynamics/DiscreteAffine_QA.lean`):**
the decay wrapper by **two routes** (theorem vs. entrywise
`tendsto_pi_nhds` + per-coordinate `Tendsto.mul` — the lifting through
disjoint API paths) with numeric decay instances (`(1/2)^5`/`(1/2)^10`
pins); the positive fixture at `α = 1/2` with the recurrence in the
theorem's exact hypothesis form, per-step values, the closed form from
the public theorem, per-coordinate geometric decay, and convergence by
two independent routes; and the proposal's two mandated boundary
witnesses as **proved refutations**, complementary by construction —
`α = 2` oscillation (`xosc n = (−1)^n • ![1,0]`, ε-δ non-convergence at
`ε = 1`, `0 < α` intact so exactly `hα2` isolated) and `α = 0`
constancy (constant `![1,0] ≠ 0` provably not converging, `α < 2`
intact so exactly `hα0` isolated).

**Verification:** spike first (`wip/dac_spike.lean`, five rounds to
green — the fixes becoming the recorded trap list:
`Filter.Tendsto.congr`'s direction (use `Filter.tendsto_congr`'s
`.mpr` for the reverse); `← add_smul` needs `add_assoc` first (the
`b + c` subterm is otherwise not a syntactic subterm of `(a+b)+c`);
bare `![2,4] i` in standalone ascriptions defaults to `ℕ` (the
recorded trap re-hit); `norm_num` does not close `|(1:ℝ)/2| < 1`
directly — `abs_lt` first; `Metric.tendsto_atTop` as the
non-convergence refutation engine); `lake env lean` on the module and
the QA file — zero errors, zero warnings each; explicit `lake build`
targets both ✔; `#print axioms` via `wip/dac_axcheck.lean` on all 28
declarations (3 public + 25 QA) — `propext, Classical.choice,
Quot.sound` only; **full `lake build` ✔ (2253 targets, +1 for the new
umbrella-reachable module; zero warnings in the changed modules — the
log's warning mass is the documented Mathlib-internal set)**;
`lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1571/9/0**,
idempotent). Records updated: the proposal (status header COMPLETE,
the delivery record with pin-technique notes), `proposals/README.md`
(the High row retired to the Delivered table; the progress paragraph
de-staled — its historical program facts all preserved in the
Delivered table, with the three previously paragraph-only slices
consolidated into one row; a new delivered row), README (1571; the
module table + proved-list sentence), the radar (QA axis count synced
1546/40 → 1571/41, held 4.0), the scoreboard (both Direct rows, build
row, lint row, a new interpretation bullet), the SGT index map (new
`Dynamics.DiscreteAffine` section + 3 declaration rows), backlog item
5 (the discrete-affine slice delivery note, remaining scope still
gated), the umbrella, this plan, and the activity log. Nothing
committed; the prior run's uncommitted Tikhonov Phase-2 delivery and
the untracked `docs/scaffold.jpeg` preserved untouched.

**Next milestone (open):** **approximate spectral projection Step 1a —
the interface layer** (the recorded open next step of its Step-0
survey), then 1b, then 1c.

**Tikhonov Phase 2 — the hard-filter limit + tail suppression; the
proposal COMPLETE (run 1, 2026-08-23, run `20260823T183842Z-run-1`;
`proposals/tikhonov-shrinkage-filter.md` Phase 2, the Active priority
table's first remaining High row and the recorded next handoff of the
reversibility-completion run): DELIVERED — Steps 1+2 in one run as pure
hard crust, zero new axioms (count stays 9), QA 1522 → 1546
(`Tikhonov_QA` +24, three new sections).**

**Delivered:** in `GraphTheory.Tikhonov` Section 5 —
`tikhonovShrinkage_tendsto_zero` (the `sgt-gaps.md` item-1 consumer's
exact statement `Tendsto (fun π => tikhonovShrinkage π lam) (𝓝 0)
(𝓝 0)` at fixed `0 < lam`, two-sided — strictly stronger than the
requested `π → 0⁺` — via `ContinuousAt.div` at the nonzero denominator
`lam`); the tail-suppression corollary in two forms — the general
symmetric-matrix `tikhonovShrinkage_tail_energy_tendsto_zero`
(statement-shape decision recorded: nothing in the proof uses PSD or
the Laplacian, so the carrier is any symmetric matrix — the module's
own `dotProduct_eigvecOf_filter` generality precedent; each tail term
by Step 1 at its own eigenvalue through an ascribed-constant
`Tendsto.mul` then `.pow 2`, the sum by `tendsto_finset_sum`) and the
consumer-facing Laplacian `tikhonovMinimizer_tail_energy_tendsto_zero`
(the filtered signal's coefficient energy on the selected
positive-eigenvalue tail vanishes; composed through the coefficient
identity at `Tendsto.congr`'s pointwise-∀ form) — **suppression-stated
per the requester's explicit non-overclaim instruction**: no
band-projector convergence claimed anywhere, in statement or
docstring.

**QA** (+24): the **two-mode tail** on the diagonal `diag13` fixture
*reused from `Band_QA`* (its eigenvector-direction lemmas supplying
the coefficient squares `1` and `0` without re-derivation — the
QA-to-QA import precedent): the tail energy pinned in **closed form**
`∑ i, (…)² = tikhonovShrinkage π 1 ^ 2` at every `π`, evaluated
exactly at `π = 1/10` (`1/121`) and `π = 1/100` (`1/10201`); the
corollary consumed at a concrete tolerance (`∃ δ > 0` forcing tail
energy `< 1/100` near `0`, through `Metric.tendsto_nhds_nhds`); the
**scalar `lam = 0` refutation** (the hypothesis-free form false — the
factor is `1` at every `π ≠ 0`, `0` at `π = 0`, so it has no limit at
all); the **tail-level boundary refutation on `K₂`** (the requester's
mandated "mode below lam" witness: kernel mode included ⇒ the energy
provably `≥ 1/2` at every nonzero `π`, from the kernel-eigenvector
line + unit norm + Parseval — the kernel mode passing through
untouched is exactly why the statement fails); and the
**minimizer-form instantiation** (the filtered nonzero-mode tail
identified as the eigenvalue-`2` singleton via a trace-based
uniqueness lemma, its `π = 1` energy pinned to `1/18` through the
coefficient identity).

**Verification:** spike first (`wip/tikP2_spike.lean` green — the
several rounds' fixes becoming the recorded trap list: `𝓝` needs
`open scoped Topology`; `λ` inside identifiers (`hλi`!) unlexable, the
re-hit ASP trap; `tendsto_finset_sum` a non-greppable `to_additive`
child of `tendsto_finset_prod`; `tendsto_const_nhds`'s value implicit
so the constant needs an ascribed `have`; square-term rewrites need
term-form lemmas (`(a·b)² ≠ b²`-shaped hypotheses cannot fire under
the outer square); `fin_cases`-on-witness beta-redexes fixed by
type-ascribed `have`s; `Metric.tendsto_nhds_nhds`'s `dist x 0`
needing `Real.dist_eq, sub_zero`); `lake env lean` on the module and
the QA file — zero errors, zero warnings each; explicit `lake build`
targets both ✔; `#print axioms` via `wip/tikP2_axcheck2.lean` on all
three public and all 24 QA declarations — `propext,
Classical.choice, Quot.sound` only; **full `lake build` ✔ (2252
targets, "Build completed successfully"; zero warnings in the changed
modules — the log's warning mass is Mathlib-internal plus documented
pre-existing notes in untouched modules)**; `lint_axioms` (**9**,
unchanged), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1546/9/0**, idempotent). Records updated: the proposal
(status header COMPLETE, the Phase-2 delivery record with
pin-technique notes), `proposals/README.md` (High row retired to the
Delivered table, progress paragraph and delivered-table row), README
(1546; the Tikhonov proved-list entry gaining the hard-filter limit
and tail suppression), the radar (QA axis count synced 1522/40 →
1546/40 held 4.0, assurance-log entry), the scoreboard (both Direct
rows, `lake build` row, lint row, a new interpretation bullet), the
SGT index map (+3 declaration rows, Phase-2 status note), this plan,
and the activity log. Nothing committed; prior runs' uncommitted
deliveries preserved untouched.

**Next milestone (open):** **discrete affine convergence** (the Active
table's single remaining High row — `sgt-gaps.md` item 2), then the
Medium rows by leverage (approximate spectral projection Step 1a).

**Reversibility Phase C, Step 2 — the first-order remainder bound (run
1, 2026-08-23, run `20260823T170118Z-run-1`;
`proposals/reversibility-and-heat-semigroup.md` Phase C Step 2, the
Active priority table's first High row and the recorded open next step
of the Steps 0+1 delivery; **the proposal COMPLETE**): DELIVERED —
pure hard crust, zero new axioms (count stays 9), QA 1507 → 1522
(`Heat_QA` 50 → 66).**

**Delivered:** in `GraphTheory.Heat` —
`heatKernel_firstOrder_remainder_apply_le`: on the smallness window
`∀ i, |t · λᵢ| ≤ 1`, every coordinate of the heat flow deviates from
its first-order Taylor polynomial at zero by at most
`t² · ∑ᵢ λᵢ² |vᵢ ⬝ᵥ x| |vᵢ a|` — the entrywise
(boundary-observable) form the `spectral-proof` rewrite's dissolution
theorem reads, at exactly the Step-0-surveyed committed shape: the
flow coordinate through `heatKernel_mulVec_eq_sum`, `x a` through
`eigvecOf_expansion_apply`, the generator coordinate through the same
expansion + `dotProduct_eigvecOf_mulVec`, the three sums combined
termwise (the pin's to_additive children used right-to-left), the
triangle by `Finset.abs_sum_le_sum_abs`, and each mode's scalar
remainder by `Real.abs_exp_sub_one_sub_id_le` at `x := -(t · λᵢ)` —
**no nonnegativity hypothesis** (per-mode, valid for any symmetric
network); plus `heatKernel_firstOrder_remainder_interval`, the
uniform `[0, T]` packaging (monotonicity hypothesis-transfer at
`0 ≤ t ≤ T`). The Euclidean-norm variant deliberately not stated
(√n-loss Cauchy–Schwarz plumbing, no new content; a consumer naming
one can adjoin it — recorded).

**QA** (`Heat_QA.lean` 50 → 66, the proposal's named pair): the K₂
eigenvalue inventory per vertex index (PSD/trace/determinant — no sort
machinery) with `edge_eigvalOf_cases`/`exists_two`; the eigenmode
structure `v = c • ![1,-1]`, `2c² = 1` making the spectral constant
**exactly `4`** (orientation-sign-independent — robust to the
spectral-theorem choice); the window fact `[0, 1/2]`; the
**concrete-bound witness** (theorem at the endpoint `t = 1/2`, RHS
evaluated to the concrete `1`; raw value `1 − 2t − e^{-2t}` pinned at
every nonzero time by the closed-form route — no eigenbasis, no
exponential lemma; composite `e⁻¹ ≤ 1`); the **boundary-degradation
witness** (both times' concrete constants `1/4` at `t = 1/4`
(interval route) and `1` at `t = 1/2`, pinning the `t²` scaling — a
wrong power of `t` contradicts at least one component); and the
**fence** (the window hypothesis refuted at `t = 1`: `|1 · 2| = 2 ≰ 1`
— local by construction, not accidentally global).

**Verification:** spiked first (`wip/heatC2_spike.lean`,
`wip/heatC2_qa_spike.lean` — both green pre-transfer, the fixes
becoming the recorded trap list: `set`-abstraction vs `rw`; the
sum-distrib direction; per-term `(t·λᵢ)²` splitting before
`← Finset.mul_sum`; ℕ-numeral smul (`2 • v` needs `(2 : ℝ) •`);
`rw`-under-`eigvecOf` motive failures solved by fresh-goal coordinate
lemmas; `mul_self_abs` absent at the pin); `lake env lean` on the
module and QA — zero errors, zero warnings each; explicit `lake build`
targets both ✔; `#print axioms` via `wip/heatC2_axcheck.lean` on all
seventeen new declarations — `propext, Classical.choice, Quot.sound`
only; **full `lake build` ✔ (2252 targets, "Build completed
successfully"; zero warnings in the changed modules)**; `lint_axioms`
(**9**, unchanged), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1522/9/0**, idempotent). Records updated: the
proposal (status header, the Step-2 delivery record with
pin-technique notes), `proposals/README.md` (High row → Delivered,
prose de-staled), README (1522; heat paragraph + module table), the
radar (axes 5 + QA **held** 4.0/4.0, counts synced 1507/40 →
1522/40), the scoreboard (both Direct rows, build row, lint row, a new
interpretation bullet), the SGT index map (+2 declaration rows, Phase
C status line), this plan, and the activity log. Nothing committed;
prior runs' uncommitted deliveries preserved untouched.

**Next milestone (open):** **Tikhonov Phase 2** — the hard-filter
limit (`tikhonovShrinkage π λ → 1` as `λ > 0`, `π → 0`-side), plus the
finite tail-suppression corollary, stated as suppression per the
requester's non-overclaim instruction; then discrete affine
convergence (the other High row).

**Reversibility Phase C, Steps 0 + 1 — the survey + the heat-flow
derivative at zero (run 1, 2026-08-23, run `20260823T153334Z-run-1`;
`proposals/reversibility-and-heat-semigroup.md` Phase C, the Active
priority table's first High row of the new 2026-08-23/24 `sgt-gaps.md`
wave — the priority-0 rule; the precedented survey+small-step
pairing): DELIVERED — pure hard crust, zero new axioms (count stays 9),
QA 1503 → 1507 (`Heat_QA` 46 → 50).**

**Delivered:** in `GraphTheory.Heat` — the Step-0 survey recorded in
the module's own docstring before any statement was frozen: the pin's
`Real.abs_exp_sub_one_sub_id_le` (`|x| ≤ 1 → |Real.exp x − 1 − x| ≤
x²`, `Complex/Exponential.lean:1211`) committed as Step 2's termwise
remainder engine (the Taylor file exists but adds plumbing the plain
bound doesn't need), and the run's sharpest elaboration finding: **a
direct vector-form proof times out at `whnf` on a variable vertex
type** (the `smul_const`/`HasDerivAt.sum` instance synthesis over the
`Pi` norms; the `Fin 2` QA statements elaborating fine is what
isolated it). Step 1: the entrywise engine
`heatKernel_mulVec_apply_hasDerivAt_zero` — Duhamel's
`heatApply_hasDerivAt` termwise-sum technique (`HasDerivAt.exp`,
`HasDerivAt.sum`) adapted to the Step-4 eigenbasis expansion
`heatKernel_mulVec_eq_sum`, the derivative-at-zero sum re-expanded to
`−(L *ᵥ x)` through `eigvecOf_expansion_apply` + the shelf's
self-adjoint pairing transfer `dotProduct_eigvecOf_mulVec` (the
pre-edit survey finding that this lemma already exists on the shelf
saved the run its one planned sub-proof) — and the headline
**`heatKernel_mulVec_hasDerivAt_zero`**: `HasDerivAt (fun t =>
heatKernel A t *ᵥ x) (-(laplacian A *ᵥ x)) 0`, the infinitesimal
generator statement `d/dt e^{-tL} x |₀ = −L x`, the `spectral-proof`
rewrite's dissolution-theorem input, assembled by the pin's
`hasDerivAt_pi`. `hA : A.IsSymm` carried exactly as the expansion
lemma already requires.

**QA** (`Heat_QA.lean` 46 → 50): the derivative value on K₂ at
`x = ![1,3]` pinned to `![2,-2]` by **two independent routes to one
statement** — the theorem route vs. the raw route (the Step-4 closed
form `1 + ((e^{−2t}−1)/2) • L` plus scalar calculus only — no
eigenbasis, no expansion, no `hasDerivAt_pi`); plus the
**infinitesimal-conservation cross-check in both directions**
(derivative `0` at `onesVec` through the Phase C theorem +
`laplacian_ones_in_kernel` vs. from Step 3's constant-flow
conservation alone — Phase C and Phase B Step 3 checking each other).

**Pin-technique notes (recorded in the proposal):** Duhamel's
`(hasDerivAt_id t).neg.mul_const` chain yields the unparenthesized
`−t * c` shape while the expansion's factors are `Real.exp (-(t * λ))`
— build the inner `HasDerivAt` parenthesized (`(.mul_const).neg`) and
reduce the derivative only at the final value identification;
`HasDerivAt.const_mul` elaborates the constant on the left at this
pin; `Finset.sum_neg_distrib` exists only as the `to_additive` child
of `prod_inv_distrib` (not greppable, but usable); the per-term
`Pi.smul_apply, smul_eq_mul` chain leaves a `mul_assoc` residue
(close with `ring`); the QA t=0 closed-form extension needs the
`by_cases` split.

**Verification:** spike first (`wip/heatC_spike.lean` green, all
`#print axioms` the standard three; eight rounds to green, the fixes
becoming the recorded trap list, the decisive one the
entrywise-plus-`hasDerivAt_pi` restructure) then transfer;
`lake env lean` on the module and the QA file — zero errors, zero
warnings each; explicit `lake build` targets for both ✔;
`#print axioms` via `wip/heatC_axcheck.lean` on all six new
declarations — `propext, Classical.choice, Quot.sound` only; **full
`lake build` ✔ (2252 targets, "Build completed successfully"; no
warnings in the changed modules)**; `lint_axioms` (**9**, unchanged),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**1507/9/0**, idempotent; `Heat_QA` 46 → 50). Records updated: the
proposal (Phase C delivery record, open-next-step → Step 2),
`proposals/README.md` (the High row), README (1507; heat-semigroup
sentence + module-table row), the radar (axis 5 + QA axis **held** at
4.0/4.0 with the delivery recorded and counts synced 1503/40 →
1507/40), the scoreboard (both Direct rows, the `lake build` row, lint
row, a new interpretation bullet), the SGT index map (Heat section +2
declaration rows, Phase C status line), this plan, and the activity
log. Nothing committed; the prior runs' uncommitted deliveries
preserved untouched.

**Next milestone (open):** **Phase C Step 2** — the first-order
remainder bound on `[0, T]`, termwise through the surveyed
`Real.abs_exp_sub_one_sub_id_le` per the committed shape, with the QA
pair the proposal names (concrete-bound witness cross-checked against
the direct exponential-series value; boundary-degradation witness).
Then the other two High rows by leverage.

**Approximate spectral projection, Step 0 — the scoping survey;
Lanczos/Kaniel–Paige cleared (run 1, 2026-08-23, run
`20260823T132040Z-run-1`; `proposals/approximate-spectral-projection.md`,
the top Medium row with the Active table holding no High rows, and both
the heat-semigroup completion's next handoff and this plan's own
recorded next milestone naming exactly this run): DELIVERED — zero shelf
Lean changes (count stays 9, QA stays 1503), the deliverable being the
survey record plus a green axiom-clean spike, exactly the Cheeger
Step-0 precedent.**

**Decision: the Lanczos/Kaniel–Paige shape is CLEARED** — the one
tractable shape; Nyström deferred with its obstruction named
(sampling-without-replacement matrix concentration absent from pin and
shelf; `Matrix.pinv` absent from the pin), the Chebyshev-filter shape
recorded as the natural second consumer of the same Chebyshev layer
(its original gate — the then-undelivered band projectors — dissolved
2026-08-20/21).

**The survey's decisive findings (all recorded in the proposal's
Step-0 record before any Step-1 authorization):**

1. **The exact finite-`k` statement, existence form:** for symmetric
   `M` with simple top eigenvalue `λ₁` (hypothesis form:
   `λ₂`-bounds-every-non-top-eigenvalue + `λ₂ < λ₁`, guard QA'd by
   refutation), unit `b = cos φ • u + sin φ • g` along the top
   eigenvector, and `k ≥ 1`, the Krylov space `span{b, Mb, …, Mᵏ⁻¹b}`
   contains nonzero `x` with `λ₁ − R_M(x) ≤ (λ₁ − λₙ) · tan²φ /
   T_{k−1}(1+2γ)²` at `γ = (λ₁−λ₂)/(λ₂−λₙ)`. Statement-shape
   decisions recorded: no sup (the Rayleigh–Ritz value is a corollary),
   no tridiagonal Lanczos iteration (exact-arithmetic variational
   content only), the Chebyshev value left explicit (the cosh growth
   bound a non-vacuity corollary), and `λ`-names will differ (`λ₁` is
   not a lexable Lean identifier — `λ` reserved).
2. **Every proof dependency verified present** — shelf: the orthonormal
   eigenbasis (`eigvecOf_inner`/`eigvecOf_complete`), the spectral
   quadratic form `quadForm_eigvalOf`, Parseval `dotProduct_eigvecOf`,
   the Rayleigh sandwich both ends
   (`quadForm_le_evals_last`/`evals_first_mul_dotProduct_le_quadForm`),
   `rayleigh`, `Heat.pow_mulVec_smul`; pin: `Polynomial.Chebyshev.T`
   with `T_real_cos` (the whole band bound follows from it), the
   `aeval`/monomial-sum layer. Shallow gaps priced: no
   `Matrix.sum_mulVec` (4 lines), no `natDegree T = n` (~15), no cosh
   growth lemma (~25, off the critical path).
3. **The skeleton spike green and axiom-clean**
   (`wip/asp_step0_spike.lean`, four declarations, every
   `#print axioms` exactly `propext, Classical.choice, Quot.sound`):
   the Chebyshev band bound `abs_T_eval_le_one` (real proof from
   `T_real_cos` + `Real.cos_arccos` + `Real.cos_mem_Icc`), the
   polynomial eigenvector action `aeval_mulVec_eq_eval_smul`
   (consuming `Heat.pow_mulVec_smul`), Krylov membership
   `aeval_mulVec_mem_krylovSpan`, and the full hypothesis-form
   `kanielPaigeSkeleton` — the spectral layer enters as five *named*
   discharge sites (`hp₁`, `horth`, `horthM`, `hbottom`, `hband`) and
   the skeleton proves the exact bound composes from exactly those
   plus the interface pieces. No mathematical obstruction surfaced at
   any point — the tractability evidence.
4. **The run's sharpest pin finding:** the shelf's SGT interface is
   `V : Type` (Type 0), not `Type*` — working at `Type*` made
   `rayleigh` and `Heat.pow_mulVec_smul` both fail with
   postponed-instance stuck elaboration, and matching Type 0 dissolved
   four apparent cross-module traps at once. Recorded in the proposal
   with the full technique list (pin's `pow_succ`/`mul_pow`
   orientations, `div_le_div_iff₀`, the `Finset.induction` binder
   count, the dependent `Finset.sum_comm` signature, `nlinarith`'s
   association-overload timeout and the `set`-abbreviation fix).

**Step-1 decomposition authorized (the cleared shape only):** 1a the
interface layer (~150–200 lines, low risk — everything already green
in the spike); 1b the spectral discharge (~200–300, medium risk — the
expansion plumbing on the shelf's own `quadForm_eigvalOf` pattern);
1c statement + QA (~150–250 — the diagonal 3×3 two-route witness, the
`k = 1` degenerate case, the `b = u` tightness witness, the `λ₁ = λ₂`
guard refutation).

**Verification:** `lake env lean wip/asp_step0_spike.lean` — zero
errors, zero warnings; all four `#print axioms` the standard three.
No shelf or QA module touched, so no module builds required beyond
the spike's own elaboration against the built oleans;
`lint_axioms` (9, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated unchanged
(**1503/9/0**, idempotent). Records updated: the proposal (the full
Step-0 record, status header, open-next-step → 1a),
`proposals/README.md` (the Medium row), this plan, and the activity
log. Nothing committed; the prior runs' uncommitted heat-semigroup
delivery preserved untouched.

**Next milestone (open):** **Step 1a — the interface layer**: the
spike's four real lemmas plus the two priced shallow gaps into a new
shelf module (`GraphTheory/Krylov.lean` or an appropriate section),
with the module-level survey note. One run. Then 1b, then 1c.

**Reversibility Phase B, Step 4 — eigenmode decay + the connected-graph
DC limit, the payoff statement (run 1, 2026-08-23, run
`20260823T112921Z-run-1`; `proposals/reversibility-and-heat-semigroup.md`
Phase B at its recorded open next step — the Active table's single High
row, so the priority-0 rule applied, and both the proposal's "Open next
step" and the Step-3 delivery's next handoff named exactly this run):
DELIVERED — pure hard crust, zero new axioms (count stays 9 at every
Phase B step), QA 1482 → 1503 (`Heat_QA` 25 → 46); **the proposal is
COMPLETE** and the external consumer's (`sgt-gaps.md`) four-item
interface — heat evolution on `laplacian A`, identity + semigroup law,
mass conservation, eigenmode decay with the DC-limit consequence — is
fully discharged as hard crust. Radar axis 5 re-scored 3.5 → 4.0 (the
named trigger).**

**Delivered:** in `GraphTheory.Heat` — the **eigenmode engine**
`exp_mulVec_eq_smul_of_mulVec_eq_smul` (`M *ᵥ v = μ • v → exp ℝ M *ᵥ v
= Real.exp μ • v`), the load-bearing bridge the plan's Step-3 note
required: its proof *is* Step 3's `expSeries_hasSum_exp` pushed through
the continuous action `N ↦ N *ᵥ v` at an eigenvector (`HasSum.map`),
each series term collapsed by the new power lemma `pow_mulVec_smul`,
the remaining scalar series summed by the pin's
`NormedSpace.exp_series_hasSum_exp'` at ℝ (identified with `Real.exp`
through `Real.exp_eq_exp_ℝ` — the pin's normed-section lemma applies at
the scalar level, no matrix-type transfer needed); Step 3's kernel
engine re-derived as the `μ = 0` case **at unchanged statement**; the
**rank-one-idempotent collapse** `exp_eq_one_add_of_mul_self_eq_smul`
(`M * M = c • M → exp ℝ M = 1 + ((exp c − 1)/c) • M`, the square-zero
collapse's sibling — its scalar tail shifted by the pin's
topological-group `hasSum_nat_add_iff'`, the pin having *no* plain
tail-shift `HasSum` lemma, then divided through `c` by a continuous
additive map and reassembled on `tsum_eq_zero_add` +
`tsum_smul_const`); `heatKernel_mulVec_eigvecOf` (eigenmode decay in
mode form, every `t`); `heatKernel_decayFactor_antitone` (the
proposal's named monotonicity) + `heatKernel_decayFactor_le_one` (PSD
dissipation); the **eigenbasis expansion** `heatKernel_mulVec_eq_sum`
(the spectral-calculus identity in action form over the proved
orthonormal basis — the survey's recorded statement-shape decision: the
expansion lives on `eigvecOf`/`eigvalOf`, where the machinery is, the
sorted-spectrum statement stays scalar); the scalar
`tendsto_exp_neg_mul_atTop`; and the payoff
**`heatKernel_mulVec_tendsto_atTop`** — on connected symmetric
nonnegative graphs, the heat flow of any vector converges to its mean
`((∑ j, x j)/|V|) • onesVec` — assembled from PSD
(`quadForm_eigvecOf_self` + `laplacian_psd`), kernel-mode existence
via `det L = 0` (`Matrix.exists_mulVec_eq_zero_iff` at `onesVec`) +
`det_eq_prod_eigenvalues` (the survey-selected route, shorter than the
expansion argument), the kernel characterization
`laplacian_kernel_eq_span_onesVec` with uniqueness-by-orthogonality
(the Fiedler line-template: a second kernel mode would put two
orthogonal unit vectors in one line), per-mode vanishing by
`tendsto_exp_neg_mul_atTop`, and `tendsto_finset_sum` limit passage.

**QA** (`Heat_QA.lean` 25 → 46): eigenmode decay on the symmetric K₂
fixture by **two independent routes to one statement** —
`heatKernel_edge_mode_engine_QA` (the engine at every time) vs
`heatKernel_edge_mode_raw_QA` (the new closed form `heatKernel K₂ t =
1 + ((e^{−2t} − 1)/2) • laplacian K₂` from the rank-one-idempotent
collapse plus hand arithmetic — independent of the engine); the
**engine⇄collapse cross-validation** at a nonzero eigenvalue (the
all-ones `m2`: `exp m2 *ᵥ ![1,1] = e² • ![1,1]` derived both ways); the
**K₂ Laplacian spectrum pinned `evals = [0, 2]`** from
trace/determinant/sortedness (the Cheeger-QA pinning pattern at the
combinatorial Laplacian) with the monotonicity theorem instantiated to
`e^{−2} ≤ 1` reading both constants from the pin; and **the DC limit by
two routes** (`heatKernel_edge_dc_theorem_QA` through the payoff
theorem with the mean computed by hand vs `heatKernel_edge_dc_raw_QA`
from the closed form's action `![2 − e^{−2t}, 2 + e^{−2t}]` tending to
`![2,2]` through the scalar decay-factor lemma — independent of the
theorem, the kernel characterization, PSD, and the eigenbasis).

**Pin-specific technique notes (recorded for future runs):** the pin
has no `HasSum.congr` (a private two-line funext wrapper `hasSum_of_eq`
is the family transport); `hasSum_nat_add_iff'` is the only tail-shift
and needs `Finset.sum_range_succ`/`sum_range_zero` to reduce its
`range 1` sum (no `Finset.sum_range_1`); `NormedSpace.exp_eq_tsum` at
matrix type rewrites into a beta-redex — follow with an explicit
`show`; `Filter.Tendsto.congr` at this pin takes a pointwise `∀`
equality, not an `EventuallyEq`; `rw` cannot rewrite under binders
(use `simp only [theorem]` inside a `fun t => …`); scalar-literal
statements default `2` to ℕ unless the vector is ascribed
`(… : Fin 2 → ℝ)` and the scalar `(2 : ℝ)`; `div_mul_cancel₀` takes
its value argument first; and `neg_pos` mis-elaborates (derive
`0 < -μ` by `linarith`).

**Verification:** spike first (`wip/heat_step4_spike.lean` green, all
`#print axioms` the standard three; six rounds to green) then transfer;
`lake env lean` on the module and the QA file — zero errors, zero
warnings each; explicit `lake build` targets for both ✔;
`#print axioms` via `wip/heat_step4_axcheck.lean` on all thirty-one
new/rewritten declarations — `propext, Classical.choice, Quot.sound`
only; **full `lake build` ✔ (2252 targets, "Build completed
successfully", detached; no warnings in the changed modules)**;
`lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1503/9/0**,
idempotent; `Heat_QA` 25 → 46). Records updated: the proposal (status
header COMPLETE, the Step-4 delivery record with technique notes,
open-next-step closed), `proposals/README.md` (the High row retired to
the Delivered table, progress paragraph rewritten — the Active table
holds no High rows), README (1503; the heat-semigroup sentence and
module-table row gaining eigenmode decay and the DC limit), the radar
(axis 5 **re-scored 3.5 → 4.0** — the named trigger fired, the
continuous-time side now a closed capability family, the axis's only
remaining absent category the ℓ² → TV conversion; QA axis count synced
1482/40 → 1503/40, held at 4.0; a new assurance-log entry), the
scoreboard (both Direct rows, the `lake build` row, lint row, a new
interpretation bullet), the SGT index map (Heat section +10 declaration
rows, status line → Steps 0–4 COMPLETE), this plan, and the activity
log. Nothing committed; the prior runs' uncommitted Phase-B deliveries
preserved untouched.

**Next milestone (open):** the Medium rows by leverage — **approximate
spectral projection** (`approximate-spectral-projection.md` — Step 0
first; a legitimate recorded outcome is "not tractable at reasonable
cost"). The PF consumers (irreducible stationary distributions,
PageRank) are unblocked as new-proposal candidates, each needing its
own document per the one-step discipline.

---

**Reversibility Phase B, Step 3 — mass conservation (run 1, 2026-08-23,
run `20260823T092311Z-run-1`; `proposals/reversibility-and-heat-semigroup.md`
Phase B at its recorded open next step — the Active table's single High
row, so the priority-0 rule applies, and both the proposal's "Open next
step" and the Step-2 delivery's next handoff name exactly this run):
DELIVERED — pure hard crust, zero new axioms (count stays 9), QA
1474 → 1482 (`Heat_QA` 17 → 25); the external consumer's three-item
interface (identity + semigroup law + mass conservation) is now
complete hard crust.**

**Pre-edit survey findings (recorded before any statement):**

- `NormedSpace.exp` at this pin is defined in the *topological-algebra*
  section (`Exponential.lean`, variable line ~97: `[Field 𝕂] [Ring 𝔸]
  [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸] [TopologicalRing 𝔸] [T2Space 𝔸]`) —
  no norm needed, which is exactly why `Heat.lean`'s statements elaborate
  with the Pi topology on matrices (`Topology/Instances/Matrix.lean`
  declares matrix instances by forwarding to the Pi ones). The normed
  `expSeries_summable'` therefore does **not** apply at matrix type
  without `letI`-ing `linftyOp` — and then its summability lives in the
  linftyOp-induced topology, not the file-level Pi topology, with no
  topology-equality lemma available. The summability-free square-zero
  route of Step 1 does not generalize (the exponential terms are not
  eventually zero).
- The pin has **no Pi-type HasSum/Summable lemmas** (`hasSum_pi` /
  `summable_pi` absent everywhere) and no finite↔countable interchange
  except `tsum_sum` (per-index summability). `Matrix.transpose_tsum`
  (`Topology/Instances/Matrix.lean`) shows the pin's own pattern for an
  operation commuting with tsums: `HasSum.map` with a continuous
  `AddMonoidHom`, plus a non-summable branch killed by
  `tsum_eq_zero_of_not_summable` on both sides.
- Route selected (entrywise, no `letI`, no norm instances on matrices):
  (1) the entrywise power bound `|Mⁿ i j| ≤ Bⁿ` at `B = ∑ |M p q|`
  (induction through `Matrix.mul_apply` +
  `Finset.abs_sum_le_sum_abs`); (2) entrywise summability by comparison
  with `Real.summable_pow_div_factorial` (`SpecificLimits/Normed.lean`
  line 808) through `Summable.of_norm`; (3) a pin-gap helper
  `hasSum_pi` (assembled from `tendsto_pi_nhds` + `Finset.sum_apply`)
  applied twice; (4) `exp ℝ M = ∑' n!⁻¹ • Mⁿ` by the topological
  `exp_eq_tsum`, closing `expSeries_hasSum_exp`; (5)
  `HasSum.map` with the additive `· *ᵥ v` (`Matrix.add_mulVec`,
  continuity entrywise through `continuous_finset_sum`/
  `continuous_apply`); (6) collapse via `tsum_eq_sum` over `{0}` at
  `mulVec_mulVec`-power annihilation. All names verified present in the
  pin: `Matrix.{add,zero,one}_mulVec`, `smul_mulVec_assoc`,
  `mulVec_mulVec` (simp), `Matrix.sum_apply`, `Matrix.mul_apply`,
  `Finset.abs_sum_le_sum_abs`, `Summable.of_norm`,
  `Real.summable_pow_div_factorial`, `tendsto_pi_nhds`,
  `HasSum.map`/`HasSum.tsum_eq`, `tsum_eq_sum`.

**Delivered:** in `GraphTheory.Heat`, a new Step-3 section — the
pin-gap Pi-HasSum assembler `hasSum_pi`; the entrywise power bound
`abs_pow_apply_le` (`|(M ^ n) i j| ≤ (∑ p q, |M p q|) ^ n`,
`Matrix.mul_apply`-induction, the entire matrix-analysis input,
norm-free); the entrywise summability `summable_exp_term` (comparison
against `Real.summable_pow_div_factorial` through
`Summable.of_norm_bounded`); the assembled convergence
`expSeries_hasSum_exp` (the exponential series converges to
`NormedSpace.exp ℝ M` in the entrywise/Pi topology — the content the
pin's normed section does not provide at matrix type); the engine
`exp_mulVec_eq_of_mulVec_eq_zero` (`M *ᵥ v = 0 → exp ℝ M *ᵥ v = v`:
the continuous additive action pushes the HasSum through `HasSum.map`,
and the pushed series collapses onto its `n = 0` term by `tsum_eq_sum`
over `{0}` at `pow_add`-factorized power annihilation); and the
headline **`heatKernel_mulVec_onesVec`** (`heatKernel A t *ᵥ onesVec =
onesVec` at every time, hypothesis-free, through the shelf's
`laplacian_ones_in_kernel` — `L *ᵥ 1 = 0` needs no symmetry since the
Laplacian's row sums vanish identically). The module also gained the
module-level Step-3 survey note and three imports
(`Analysis.SpecificLimits.Normed`, `Analysis.Normed.Group.InfiniteSum`,
`Order.Filter.Tendsto`).

**QA** (`Heat_QA.lean` 17 → 25): conservation by **two independent
routes to one statement** — `heatKernel_ones_conserved_asym_QA`
(theorem route on the asymmetric fixture) vs
`heatKernel_ones_conserved_raw_QA` (the closed form `!![1-t, t; -t, 1+t]`
hand-multiplied onto `onesVec`, independent of the theorem); the raw
kernel-instance check `asymLaplacian_mulVec_ones_raw_QA` (the exact
instance of `laplacian_ones_in_kernel` the theorem consumes, verified
independently); the symmetric-fixture instantiation (conservation not
locked to the square-zero accident); the proposal's named
**per-component no-leakage witness** on the new disconnected `Fin 3`
fixture `disAdj` (edge `{0,1}` + isolated vertex `2`, encoded as an
entrywise function because `Fin 3` cons-literals resist `simp`'s
index-2 reduction at this pin): the `{0,1}`-component indicator checked
`L`-harmonic raw from the definitions
(`disLaplacian_mulVec_component_raw_QA`) then fixed by the engine at
every time (`heatKernel_noLeakage_component_QA`), with the
isolated-vertex indicator fixed too (`heatKernel_isolated_fixed_QA`) —
heat provably does not cross components, so conservation is not
accidentally vacuous on disconnected input; and the
**kernel-hypothesis guard** `heatKernel_asym_not_fix_nonkernel_QA` (a
non-kernel vector is provably *not* fixed: the exact kernel
`!![0,1;-1,2]` sends `![1,0]` to `![0,-1]` — the hypothesis-free
strengthening refuted with every other structural fact intact).

**Pin-specific technique notes (recorded for future runs):** application
binds tighter than `^` (`(M ^ n) i j` needs explicit parens);
`pow_succ'` factors the wrong way at this pin (`a^(n+1) = a * a^n` —
use `pow_add` + `pow_one` for `M^n * M`); `Filter.tendsto_congr` is
namespaced under `Filter`; `Finset.sum_apply` takes the index first
(`Finset.sum_apply x s f`); `Finset.sum_le_sum` needs `f`/`g` named
arguments or the `OrderedAddCommMonoid` synthesis gets stuck behind a
metavariable; `Finset.sum_le_sum_of_subset` is canonically-ordered-only
(unusable over ℝ — singleton bounds go through `Finset.sum_insert`/
`Finset.insert_erase` splitting + `le_add_of_nonneg_right`); and on the
QA side, `Fin 3` cons-literals resist `simp`'s index-2 reduction,
`fin_cases`' `⟨n, ⋯⟩`-form indices resist `rfl`, and kernel `decide`
is blocked by `Real.decidableEq`'s classical path — the robust fixture
encoding is an entrywise function
(`Matrix.of fun i j => if … then 1 else 0`) with function-form
indicators, which `simp`/`norm_num` reduce at `fin_cases` literals.

**Verification:** spike first (`wip/heat_step3_spike.lean` green, all
`#print axioms` the standard three; five rounds to green — the fixes
were exactly the trap list above) then transfer; `lake env lean` on the
module and the QA file — zero errors, zero warnings each; explicit
`lake build` targets for both ✔; `#print axioms` via
`wip/heat_step3_axcheck.lean` on all six new public and all eight new
QA declarations — `propext, Classical.choice, Quot.sound` only; **full
`lake build` ✔ (2252 targets, "Build completed successfully",
detached)**; `lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1482/9/0**,
idempotent; `Heat_QA` 17 → 25). Records updated: the proposal (status
header, the Step-3 delivery record with the technique notes,
open-next-step → Step 4), `proposals/README.md` (High row + progress
paragraph + Delivered row), README (1482; the heat-semigroup sentence
and module-table row gaining mass conservation), the radar (axis 5
**held at 3.5** with the Step-3 delivery recorded and the absent clause
narrowed to Step 4 — the named re-score trigger; QA axis count synced
1474/40 → 1482/40, held at 4.0), the scoreboard (both Direct rows, the
`lake build` row, lint row, a new interpretation bullet), the SGT index
map (Heat section +6 declaration rows, status line → Steps 0–3), this
plan, and the activity log. Nothing committed; the prior runs'
uncommitted Steps-0+1/Step-2 deliveries preserved untouched.

**Next milestone (open):** **Reversibility Phase B Step 4** — eigenmode
decay + the connected-graph DC limit, the proposal's payoff statement
(the active-milestone section above records the selected scope). After
Phase B completes: the remaining Medium rows by leverage (approximate
spectral projection Step 0; the PF consumers as new-proposal
candidates).

**Reversibility Phase B, Step 2 — the semigroup property (run 1,
2026-08-23; `proposals/reversibility-and-heat-semigroup.md` Phase B at
its recorded open next step — the Active table's single High row, so the
priority-0 rule applies, and both the proposal's "Open next step" and the
Steps-0+1 delivery's next handoff name exactly this run): DELIVERED —
pure hard crust, zero new axioms (count stays 9), QA 1467 → 1474
(`Heat_QA` 10 → 17); the external consumer's two-item core interface
("identity at time zero + semigroup law") is now complete hard crust.**

**Delivered:** in `GraphTheory.Heat` — the semigroup law
`heatKernel_mul_heatKernel` (`heatKernel A s * heatKernel A t =
heatKernel A (s + t)`, **hypothesis-free**: no symmetry, no sign
restriction on the times) through the pin's `Matrix.exp_add_of_commute`
at the commuting pair `-(s • L)` / `-(t • L)` (scalar multiples of one
matrix commute: `(s • L) * (t • L) = (s * t) • (L * L)` both ways via
`Algebra.smul_mul_assoc`/`Algebra.mul_smul_comm`/`smul_smul`; the joined
exponent reduced by `neg_add` + `add_smul`), **with no ball/radius
hypothesis** — the Step-0 survey's norm-free finding holding exactly as
recorded, re-verified against the pinned source this run; plus the
every-time square-zero collapse
`exp_neg_smul_eq_one_add_of_mul_self_eq_zero` (`exp ℝ (-(t • M)) =
1 + -(t • M)` for `M * M = 0` — the Step-1 `t = 1` handle generalized to
all times; the exponent squares to `(t * t) • (M * M) = 0`), the
interface that makes QA exactly evaluable at symbolic times. **One
transfer correction recorded (the spike's two-round shape, same as
Step 1):** the sketch's `smul_add` reduction is `add_smul` at module
level (different scalars, one matrix), and `rw` against
`Matrix.exp_add_of_commute` needs a fully-ground `have` plus
`simp only [heatKernel] at h ⊢` — the naive `rw [← Matrix.exp_add_of_
commute _ _ hcomm]` leaves instance metavariables unassignable and
fails keyed matching.

**QA** (`Heat_QA.lean` 10 → 17): the semigroup law witnessed by **two
independent routes to one closed-form statement** — the raw route
(`heatKernel_asym_semigroup_raw_QA`: the fixture's closed forms
`!![1-s, s; -s, 1+s]` and `!![1-t, t; -t, 1+t]` multiplied by hand
through `Matrix.mul` on literals, every entry closed by `ring`,
independent of the theorem) and the theorem route
(`heatKernel_asym_semigroup_theorem_QA`: the law composed with one
closed form) — a wrong time-combination constant anywhere in the
delivered chain contradicts the hand computation; the **every-time
closed form** `heatKernel asymAdj t = !![1-t, t; -t, 1+t]` for symbolic
`t`; the **numeric instance** at `s = 2, t = 3` (`!![-4, 5; -5, 6]`);
the **group property** `heatKernel asymAdj 1 * heatKernel asymAdj (-1)
= 1` (forward-then-backward flow is the identity — the semigroup law
composed with the time-zero identity, the consumer's two core interface
items working together); and the **degenerate `t = 0` identities** on
the symmetric K₂ fixture where no closed form exists (both orders).

**Verification:** spike first (`wip/heat_step2_spike.lean` green, all
`#print axioms` the standard three) then transfer; `lake env lean` on
the module and the QA file — zero errors, zero warnings each; explicit
`lake build` targets for both ✔; `#print axioms` via
`wip/heat_step2_axcheck.lean` on both new public and all seven new QA
declarations — `propext, Classical.choice, Quot.sound` only; **full
`lake build` ✔ (2252 targets, "Build completed successfully",
detached)**; `lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1474/9/0**,
idempotent; `Heat_QA` 10 → 17). Records updated: the proposal (status
header, the Step-2 delivery record, open-next-step → Step 3),
`proposals/README.md` (High row + progress paragraph + Delivered row),
README (1474, the heat-semigroup sentence and module-table row gaining
the semigroup law), the radar (axis 5 **held at 3.5** with the Step-2
delivery recorded and the absent clause narrowed to Steps 3–4; QA axis
count synced 1467/40 → 1474/40, held at 4.0), the scoreboard (both
Direct rows, the `lake build` row, lint row, a new interpretation
bullet), the SGT index map (Heat section +2 declaration rows, Steps
0–2), this plan, and the activity log. Nothing committed; the
prior run's uncommitted Steps-0+1 delivery preserved untouched.

**Reversibility Phase B, Steps 0 + 1 — the graph heat semigroup:
survey, then the definition with symmetry and identity (run 1, 2026-08-23;
`proposals/reversibility-and-heat-semigroup.md` Phase B, the Active
table's single High row — its operator-decision gate resolved 2026-08-23
by `sgt-gaps.md`, the independent `spectral-proof` clean-sheet rewrite
project, which names this exact Phase B by file path as its one remaining
Scaffold dependency and lists the interface Steps 1–4 supply verbatim:
heat evolution specialized to `laplacian A`, identity at time zero +
semigroup law, `onesVec` preservation, eigenmode decay with the
connected-graph DC-limit consequence. This is a real external consumer —
the first High row since the table was instituted — so per the
priority-0 rule it outranks every Medium row. Selected scope for this
run: the Step-0 survey (record-before-proving, per the proposal) plus
Step 1 — `heatKernel A t := NormedSpace.exp ℝ (-(t • laplacian A))`
with symmetry (from the shelf's `laplacian_symmetric` through
`Matrix.IsSymm.exp`) and `heatKernel A 0 = 1` (from `NormedSpace.exp_zero`),
zero new axioms, per the proposal's own no-new-axioms mandate. The
precedent for pairing a survey-only Step 0 with a small Step 1 is the
directed-operators run of 2026-08-22.): DELIVERED — Steps 0+1 as pure
hard crust in the new `GraphTheory.Heat`, zero new axioms (count stays
9), QA 1457 → 1467 (`Heat_QA` a new file at 10).**

**Pre-edit survey findings (Step 0, recorded before any statement):** the
pinned Mathlib's
`Mathlib/Analysis/Normed/Algebra/MatrixExponential.lean` is the exact
surface the proposal sketched, and it is *purpose-built to be norm-free*:
`Matrix.exp_add_of_commute` (line 120), `Matrix.isUnit_exp` (142),
`Matrix.exp_neg` (166), `Matrix.exp_zsmul` (173), `Matrix.exp_conj`/
`exp_conj'` (179/184) each `letI` the `linftyOp` norm *inside* their
proofs, so no ball-membership or radius hypothesis reaches the caller —
the proposal's `expSeries_radius_eq_top` worry does not arise at this
pin. `Matrix.IsSymm.exp` (108) needs only `[Field 𝕂] [CommRing 𝔸]
[TopologicalRing 𝔸] [Algebra 𝕂 𝔸] [T2Space 𝔸]` — for `Matrix V V ℝ` all
instances are global (`Topology/Instances/Matrix.lean`: Pi topology,
`Matrix.topologicalRing` at `[Fintype V]`, T2). One naming correction to
the proposal sketch: there is no `Matrix.exp` declaration — the function
is `NormedSpace.exp ℝ` used at matrix type (the Matrix-namespaced lemmas
are wrappers), and the matrix-level `exp_add_of_commute` is reached as
`Matrix.exp_add_of_commute` with entry-ring `NormedRing ℝ`/`NormedAlgebra
ℝ ℝ`/`CompleteSpace ℝ` all global. For Step 1 only `Matrix.IsSymm.exp`
and `NormedSpace.exp_zero` are consumed. The repo's `Perturbation.Duhamel`
already carries a *vector-level* damped eigenbasis semigroup (`heatApply`,
explicitly "no `Matrix.exp`") — a different object; a bridge to it is
Step-4 business, not Step-1.

**DELIVERED (same run):** the new `Scaffold/Mathlib/GraphTheory/Heat.lean`
(namespace `SpectralGraphTheory`, zero new axioms — the proposal's own
mandate; count stays 9) — `heatKernel A t := NormedSpace.exp ℝ
(-(t • laplacian A))` (the external consumer's first interface item);
`heatKernel_isSymm` (shelf `laplacian_symmetric` through
`Matrix.IsSymm.smul`/`.neg` and the pin's `Matrix.IsSymm.exp`); the
hypothesis-free `heatKernel_zero`; and the general square-zero collapse
`exp_eq_one_add_of_mul_self_eq_zero` (`M * M = 0 → exp ℝ M = 1 + M`, by
`exp_eq_tsum` + `tsum_eq_sum` over `range 2`). QA at
`Scaffold/QA/SpectralGraph/Heat_QA.lean` (10 theorem declarations): the
time-zero identity computed on both fixtures (hypothesis-free); symmetry
through the theorem on K₂ with the hypothesis derived from the literal;
the **exact closed form** `heatKernel asymAdj 1 = !![0, 1; -1, 2]` on the
asymmetric fixture whose Laplacian `!![1,-1;1,-1]` is square-zero — the
spike itself caught the first draft's wrong `(1,1)` entry, the failure
mode numeric QA exists for; the **symmetry hypothesis
refuted-on-omission** (entries `1 ≠ -1`, the fixture's `IsSymm` provably
violated at the same pair); and the **sign witness** `e^{-L} ≠ e^{+L}`
entrywise (`0 ≠ 2`).

**Verification:** spike first (`wip/heat_spike.lean` green, all
`#print axioms` the standard three) then transfer; `lake env lean` on the
module and the QA file — zero errors, zero warnings each; explicit
`lake build` targets for both ✔; `#print axioms` via `wip/heat_axcheck.lean`
on all four public and all ten QA declarations — `propext,
Classical.choice, Quot.sound` only; **full `lake build` ✔ (2252 targets
(+2), "Build completed successfully", detached)**; `lint_axioms`
(**9**, unchanged), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1467/9/0**, idempotent; `Heat_QA` a new file
row at 10). Records updated: the proposal (status header, the Step-0
survey record, the full Steps-0+1 delivery record, open-next-step →
Step 2), `proposals/README.md` (High row + progress paragraph + Delivered
row), README (1467, heat-semigroup in the proved list, module-table row),
the radar (axis 5 **held at 3.5** with the delivery recorded and the
absent clause updated — the definition layer, not the Steps-2–4
statements; QA axis count synced 1457/39 → 1467/40, held at 4.0), the
scoreboard (both Direct rows, the `lake build` row, lint row, a new
interpretation bullet), the SGT index map (new Heat section), the
coverage map (the matrix-exponential row: present and purpose-built
norm-free), backlog item 5 (delivery-opened note), this plan, and the
activity log. Nothing committed.

**Next milestone (open):** **Reversibility Phase B Step 2** — the
semigroup property `heatKernel A s * heatKernel A t = heatKernel A
(s + t)` via `Matrix.exp_add_of_commute` at the commuting scalar
multiples (`-(s • L)` and `-(t • L)` commute trivially; `neg_add` +
`smul_add` reduce the exponent; the survey record above is why no ball
hypothesis is needed), with QA (the semigroup law instantiated where
both sides are exactly evaluable — the square-zero fixture and `t = 0`
identities). Then Steps 3 (mass conservation through
`laplacian_mulVec_ones`) and 4 (eigenmode decay + the DC limit), one per
run per the proposal's operating instructions. After Phase B completes:
the remaining Medium rows by leverage (approximate spectral projection
Step 0; the PF consumers as new-proposal candidates).

**Fiedler Phase B — the certified conductance cut (run 1, 2026-08-23;
`proposals/fiedler-partitioning.md` Phase B, whose recorded operator gate
was dissolved by the same day's `cheeger_lower_bound` retirement — pure
hard crust, zero new axioms; the proposal is COMPLETE, QA 1449 → 1457).**
In `GraphTheory.Cheeger`: `cheegerConstant_attained` (the conductance
`sInf` realized as a minimum, no regularity hypothesis — the finiteness
step converting Cheeger's inequality-about-an-infimum into a statement
about an actual cut). In `GraphTheory.Fiedler` (new Phase B section,
importing `Cheeger`): `fiedlerVector_rayleigh_regularNormalizedLaplacian`
(`R_{L_sym}(f) = lambda2 / d`) and the headline `cheeger_cut_existence`:
on every connected `d`-regular graph, `∃ S` nonempty proper with
`conductance A S ^ 2 ≤ 2 * lambda2 A / d` — the classical Cheeger
cut-existence corollary, assembled from `cheeger_sweep` at the Fiedler
vector composed with attainment. **Statement-shape deviation recorded
before stating:** the sketch's sign-partition bound is not certifiable
from the Cheeger inequalities; the certified object is the conductance
minimizer, the swept-level-set extraction the named follow-on. QA
(`Fiedler_QA` 57 → 65, on K₂): `cheegerConstant (K₂) = 1` pinned both
directions; the Rayleigh transfer cross-checked against the independently
pinned `lambda2 (K₂) = 2`; the certified cut identified and its bound
displayed (`1 ≤ 4`); and the regularity refutation (the `hd`-dropped form
at `d = 100` demands `1 ≤ 1/25`, false). Verification: spike first
(`wip/fiedlerB_spike.lean`); `lake env lean` on both modules and the QA
file clean (Cheeger carrying only the documented pre-existing
`unusedSectionVars` warning); explicit `lake build` targets ✔;
`#print axioms` the standard three; **full `lake build` ✔ (2250
targets)**; `lint_axioms` (**9**), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1457/9/0**).
Records updated across the proposal, `proposals/README.md`, README,
radar, scoreboard, backlog, both indexes, this plan, and the activity log;
nothing committed.

**Cheeger hard-direction Step 1c — median + assembly in `Cheeger.lean`,
retiring `cheeger_lower_bound` (run 1, 2026-08-23;
`proposals/discharge-perturbation-axioms.md` at its recorded open next
step — the top-ranked Medium item with the Active table holding no High
rows, and both the proposal's Step-1c plan and the 1b delivery's next
handoff naming this run; the *final* component): DELIVERED —
`cheeger_lower_bound` proved at the unchanged name, hypotheses, and
conclusion, **explicit axioms 10 → 9**, the discharge program
COMPLETE (Weyl, Davis–Kahan, and both Cheeger directions all proved
hard crust). QA 1423 → 1449 (`Cheeger_QA` 78 → 104).**

**Delivered:** in `GraphTheory.Cheeger`, a new "hard direction Step 1c"
section — **median existence** `exists_median` (some `m` with
`2·|{m < x i}| ≤ n` and `2·|{x i < m}| ≤ n`) by pure Finset arithmetic
with **no sorting** (a route simplification over the survey's
`Finset.sort` + `get` sketch: the at-most-half set
`T := {i : 2·|{j : x i < x j}| ≤ n}` is nonempty at a maximizing vertex
via `Finset.exists_max_image`, a `T`-minimal value works via
`Finset.exists_min_image`, and the failure case is self-refuting — a
majority strict lower level set's maximizer lies in `T` below the
`T`-minimum; the empty-type case discharged separately); the level-set
**inclusions** `posPart_superlevel_subset`/`negPart_superlevel_subset`
(at `t > 0`, `{t ≤ (x−m)⁺²} ⊆ {x > m}` and `{t ≤ (m−x)⁺²} ⊆ {x < m}`)
supplying `coarea_core`'s `hy` in exactly its delivered closed-set form
(`minority_posPart`/`minority_negPart`); the **per-part bound**
`hardDirection_perPart` (`φ²·d·∑y² ≤ E'(y)`: the 1b co-area core
squared and composed with the 1a Cauchy–Schwarz core through the
regularity bridge, `cheegerConstant_nonneg` supplying the squaring's
side condition, the zero-norm case by `E'`-nonnegativity); the **norm
split** `median_parts_norm` (`∑(x−m)⁺² + ∑(m−x)⁺² = ∑x² + n·m² ≥ ∑x²`,
pointwise `u² + v² = (x−m)²` since the parts are disjointly
supported); the **sweep lemma** `cheeger_sweep` (`φ²/2 ≤ R_{L_sym}(x)`
for every nonzero `x ⊥ 1` — both median parts through the 1a *fused*
contraction and the `E'/(2d‖x‖²)` normalization, the corrected 1a
constant budget consumed exactly); and the retirement itself — the
spike's `assembly_skeleton` with the hypothesis discharged:
`secondEval_variational` + `le_csInf` at the `Pi.single` witness.

**QA** (`Cheeger_QA.lean` 78 → 104): the **median forced into its
interval** on the tie-heavy `![1,1,−1,−1]` (the theorem's returned `m`
provably in `[−1, 1]`; a defective median puts all four values on one
strict side and one at-most-half count reads `2·4 ≤ 4` — refuted); the
**per-part bound pinned** at the 1b `K₂` equality fixture (`1 ≤ 2`,
both sides raw); the **norm split's exact `+ n·m²` remainder** at two
medians on `![1,−1,3,−3]` (`m = 0`: `20 = ∑x²` exact; `m = 1`:
`24 = 20 + 4·1²`, the theorem's inequality the strict `20 ≤ 24`); the
**sweep on `K₂`** (`1/2 ≤ 2`, the quotient the independently pinned
`λ₂` value) and **on `C₄` at `d = 2`** (non-unit degree: `R = 1`
through the 1a normalization with `E' = 8`, `‖x‖² = 2` raw; the
visible gap `φ²/2 ≤ 1/8 < 1 = R` via the exhaustively computed
`φ ≤ 1/2`); and the **retirement instance**
`cheeger_lower_bound_edge_QA` (`1/2 ≤ λ₂(L_sym) = 2` through the
proved theorem, both endpoints independently pinned — the
instantiation that previously consumed the admitted axiom). The two
pre-existing axiom-consuming QA theorems
(`cheeger_positive_implies_secondEval_pos_QA`,
`cheeger_bounds_coherent_QA`) compiled unchanged and **silently shed
their `cheeger_lower_bound` dependency**.

**Verification:** `lake env lean` on the module (only the documented
pre-existing `unusedSectionVars` warning) and on the QA file (zero
errors, zero warnings); explicit `lake build` targets for both ✔;
`#print axioms` via `wip/cheeger1c_axcheck.lean` on the retired
theorem, all ten new public theorems, all nine new QA headlines, and
the two former axiom-consumers — `propext, Classical.choice,
Quot.sound` only; **full `lake build` ✔ (2250 targets, "Build
completed successfully", detached)**; `lint_axioms` (**9**),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(**1449/9/0**). Spike discipline followed: the development landed
green in `wip/cheeger1c_spike.lean` first, then transferred. Records
updated: the proposal (status header COMPLETE, the Step-1c delivery
record replacing the open next step, with pin-specific technique notes
— `Finset.filter_eq_univ_iff` absent (`Finset.eq_univ_iff_forall` +
hand-assembled `Finset.mem_filter` instead), metavariable-stuck
partial applications needing ascribed `have`s, the
`Finset.mem_filter` beta-redex defeating `rw` until `simp only`
beta-reduces, and `le_of_mul_le_mul_left`'s left-multiplier signature
taking its positivity argument directly), `proposals/README.md`
(Medium row retired to the Delivered table; progress paragraph
rewritten), the Chung source index (the lower-bound row proved-not-
axiom, the retirement note), the SGT index map (Cheeger section +5
rows + program-complete note), README (9 axioms, 1449, both Cheeger
inequalities in the proved list, trust-surface paragraph rewritten),
the radar (axis 4 **re-scored 4.0 → 4.5** — both directions of the
axis's central isoperimetric–spectral family now proved; the
axiom-minimization trend extended to `... → 9 → 10 → 9` with the
row-head count drift from the PF admission repaired; QA count synced
1423/39 → 1449/39; the downstream-reuse gap clause updated), the
scoreboard (both Direct rows, the `lake build` row, lint row, a new
retirement interpretation bullet), backlog item 4's Phase-B trust
note, this plan, and the activity log. The worktree's prior-run
uncommitted Step-1b delivery preserved untouched; nothing committed.

**Next milestone (open):** the Medium rows by leverage — **approximate
spectral projection** (`approximate-spectral-projection.md` — Step 0
first; it may legitimately conclude nothing is tractable at reasonable
cost, a valid recorded outcome). The PF consumers (irreducible
stationary distributions, PageRank) are unblocked as new-proposal
candidates, each needing its own document per the one-step discipline.
Reversibility Phase B and Fiedler Phase B still need operator
decisions.

---

**Cheeger hard-direction Step 1b — the co-area core in `Cheeger.lean`
(run 1, 2026-08-23;
`proposals/discharge-perturbation-axioms.md` at its recorded open next
step — the top-ranked Medium item with the Active table holding no High
rows, the plan's own recorded next handoff naming this run, and the
survey's dedicated-run instruction for the crux): DELIVERED — zero new
axioms (count stays 10), QA 1404 → 1423 (`Cheeger_QA` 59 → 78).**

**Delivered:** in `GraphTheory.Cheeger`, a new "hard direction Step 1b"
section — the layer-cake primitive `indicatorLE` (`1_{t ≤ c}`, stated
through `Set.indicator` on `{x | x ≤ c}` to match
`intervalIntegral.integral_indicator`'s own truncation shape exactly)
with the **mass layer-cake** `integral_indicatorLE`
(`∫₀^R 1_{t ≤ c} dt = c`) and the **pair layer-cake**
`integral_abs_indicatorLE_sub` (`∫₀^R |1_{t ≤ c} − 1_{t ≤ d}| dt =
|c − d|`), their integrability (`intervalIntegrable_indicatorLE` +
a generic `intervalIntegrable_const_mul` for the pin's missing
`IntervalIntegrable.const_mul`), the **closed-superlevel cut identity**
`sum_pairAbs_eq_two_boundary` (`∑ i j, A i j |1_{t ≤ c_i} −
1_{t ≤ c_j}| = 2 · boundary S_t`; `hA` load-bearing through
`boundary_compl`), the **minority conductance**
`boundary_ge_of_minority` (`φ·d·|S| ≤ boundary S` for nonempty
`2|S| ≤ n`), the indicator↔cardinality dictionary
`sum_indicatorLE_eq_card_filter`, the per-level bound `sum_pairAbs_ge`,
and the headline **`coarea_core`**: for *any* `y : V → ℝ` whose
nonempty closed superlevel sets `{i : t ≤ y i²}` at positive levels are
minority-side, `2·(φ·d·∑ y i²) ≤ ∑ i j, A i j·|y i² − y j²|` — the
lower complement of Component A; composed with it, the per-part bound
`φ²·d·‖y‖² ≤ E'(y)` that Step 1c consumes.

**The run's two sharpest outputs are survey corrections:**
(1) the priced ~30-line hand Finset-induction Fubini is *unnecessary* —
the pin has `intervalIntegral.integral_finset_sum` (the survey searched
for the name `integral_sum`), plus `IntervalIntegrable.sum`, `.abs`,
and `integral_mono_ae_restrict`; (2) the `Iic`-indicator encoding
dissolves the survey's `Ι = Ioc` right-endpoint drop-point trap — every
congruence in the delivered chain is pointwise, with the single `t = 0`
integrand-failure point (φ-side `2φd·n` against a vanishing cut side)
absorbed by Lebesgue's atom-freeness (`mem_ae_iff` +
`Real.volume_singleton`). **Two hypothesis drops verified:** no
`hynonneg` (the chain runs on `y i² ≥ 0`, automatic) and no `hcard`
(minority already forces the complement nonempty); the minority
hypothesis itself is stated on *closed* superlevel sets at *positive*
levels — at `t = 0` the closed set is all of `V` for every `y`, so a
`t ≥ 0` reading would be unsatisfiable.

**QA** (`Cheeger_QA.lean` 59 → 78): the **K₂ equality pin** — at
`edgeY = ![1,0]` both sides independently evaluate to `2`, so the
bound is *attained with equality* and any defective constant anywhere
in the layer-cake chain breaks it (minority hypothesis derived,
load-bearing); the **strict multi-level C₄ witness** at
`cycY = ![2,1,0,0]` (squared values `(4,1,0,0)`, two level strata): raw
total variation `16` against `20φ ≤ 10` (φ bounded by the adjacent-pair
cut's exhaustively computed conductance `1/2` — no `φ(C₄)` enumeration
needed); the **dictionary pin** at level `t = 1` where vertex `1` has
`y² = 1 = t` and its indicator is `1` — the closed-set semantics
load-bearing; and the **minority refutation-on-omission** — at
`edgeOnes = ![1,1]` the hypothesis-free conclusion reads `4 ≤ 0` with
the minority hypothesis provably unsatisfiable at `t = 1` and every
other hypothesis holding on the fixture.

**Verification:** `lake env lean` on the module (only the documented
pre-existing `unusedSectionVars` warning) and on the QA file (zero
errors, zero warnings); explicit `lake build` targets for both ✔;
`#print axioms` on all twelve new public theorems and seven QA
headlines — `propext, Classical.choice, Quot.sound` only; **full
`lake build` ✔ (2250 targets, "Build completed successfully",
detached)**; `lint_axioms` (10, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1423/10/0**).
Records updated: the proposal (status header, second inline dated
survey correction at the Fubini note, the Step-1b delivery record with
pin-specific technique notes — the `(0:ℝ)..R` Float-lexing trap, the
`Set.indicator_of_mem` membership-direction trap, `Set.Iic`-vs-setOf
`rw` matching, the `IntervalIntegrable.sum` Pi-application whnf loop
routed through an explicit `Finset.sum_apply` function equation,
`integral_const` ambiguity, and `integrable_const`'s
`IsFiniteMeasure` requirement at this pin — open-next-step → 1c),
`proposals/README.md` (Medium row + the no-High-rows paragraph), the
SGT index map (Cheeger section +7 rows + program note), README (1423,
the trust-surface paragraph: the hard direction now reduced to its
final component), the radar (QA axis held 4.0, count synced
1404/39 → 1423/39, hold logged, and the row-head count drift left by
earlier syncs repaired), the scoreboard (both Direct rows, the
`lake build` row, lint row, a new interpretation bullet), this plan,
and the activity log. Nothing committed.

**Next milestone (open):** **Cheeger Step 1c** — median + assembly,
the *final* component: median existence over the value multiset, the
inclusion `{(x−m)⁺ ≥ t} ⊆ {x > m}` at `t > 0` supplying `coarea_core`'s
`hy` in its delivered closed-set-at-`0 < t` form, the degenerate cases,
the norm split, and the assembly `(2φd∑y²)² ≤ (∑|Δ|)² ≤ E'·4d∑y²` per
part, summed through the fused contraction into `φ²/2 ≤ R`, retiring
`cheeger_lower_bound` at the unchanged statement (explicit axioms
10 → 9) through the spike's `assembly_skeleton`. **Approximate
spectral projection** still needs its Step 0; the PF consumers
(irreducible stationary distributions, PageRank) are new-proposal
candidates. Reversibility Phase B and Fiedler Phase B still need
operator decisions.

---

**Cheeger hard-direction Step 1a — the pure-algebra component in
`Cheeger.lean` (run 1, 2026-08-23;
`proposals/discharge-perturbation-axioms.md` at its recorded open next
step — the top-ranked Medium item with the Active table holding no High
rows, and both the proposal's own gate and the plan's recorded next
handoff naming this transfer run): DELIVERED — zero new axioms (count
stays 10), QA 1378 → 1404 (`Cheeger_QA` 33 → 59).**

**Pre-edit finding (recorded before any statement was frozen, and the
delivery's sharpest output):** re-deriving the constant chain exposed an
internal inconsistency in the survey's recorded route — its step-5
summation (`E'(u) ≤ E'(x)` and `E'(v) ≤ E'(x)`, summed to `2E'(x)`) is
loose by exactly the factor `2` the statement's `/2` consumes, and its
step-6 normalization `R = E'/(d‖x‖²)` omits the `/2` of
`laplacian_quadForm` (`E'` is the *ordered* double sum = twice
`quadForm (laplacian A)`); as literally recorded the two errors cancel,
which is why the twice-hand-checked writeup looked exact. The spike's
hypothesis-form `assembly_skeleton` verified the *composition*, not the
constants — the exact failure mode the survey's own QA-discipline note
anticipated.

**Delivered:** in `GraphTheory.Cheeger`, a new "hard direction Step 1a"
section — **Component A** `core_sum_abs_sq_sub_sq` (transferred verbatim
from the survey spike, `IsSymm` statement guard), the scalar **fused
median-part contraction** `sq_posPart_sub_add_sq_negPart_sub_le`
(`(max (a−m) 0 − max (b−m) 0)² + (max (m−a) 0 − max (m−b) 0)² ≤ (a−b)²`)
with its summed form `sum_edgeWeight_sq_posPart_add_sq_negPart_le`
(`E'((x−m)⁺) + E'((x−m)⁻) ≤ E'(x)`, nonneg weights only — the *tight*
form: cross-edge slack `(u+v)² ≥ u²+v²` pays for carrying both parts,
translation invariance absorbed into the pointwise RHS; the separate
translation-invariance lemma the sketch named is inert and was not
added), the regularity bridge `sum_deg_mul_eq_of_regular`, and the
**normalization** `rayleigh_regularNormalizedLaplacian_eq`
(`R(x) = E'(x)/(2d‖x‖²)`). With these shapes the chain is exact:
per-part `φ²d‖y‖² ≤ E'(y)` (1b composed with Component A) sums to
`φ²d‖x‖² ≤ E'(x) = 2dR‖x‖²`, i.e. `φ²/2 ≤ R`.

**QA** (`Cheeger_QA.lean` 33 → 59): Component A on `K₂` at `![1,0]`
with all three quantities computed independently (the degree sum
through the new bridge — load-bearing) and the strict gap `4 < 8`
pinned; the contraction on `C₄` in an **equality case**
(`![1,0,-1,0]` at `m = 0`: `4 + 4 = 8`) and a **strict case**
(`![1,1,-1,-1]`: `4 + 4 < 16`); the normalization on `K₂` at
`![1,-1]` evaluated to `2` and cross-checked against the independently
pinned `λ₂(L_sym) = 2` (`rayleigh_edge_attains_secondEval_QA` — a
defective denominator constant would fail this check); **two guard
refutations**: `IsSymm` refuted-on-omission at the nonnegative
asymmetric `!![0,1/10;1,0]` (`121/100 ≤ 44/100` false; the column-vs-row
sum mismatch at vertex `0`), nonnegativity refuted-on-omission at the
symmetric negative `!![0,-1;-1,0]` (`-1 ≤ -2` false) — each with the
surviving structure proved to *hold* on the fixture.

**Verification:** `lake env lean` on the module (only the documented
pre-existing `unusedSectionVars` warning, verified identical in HEAD by
a `git stash` round-trip) and on the QA file (zero errors, zero
warnings); explicit `lake build` targets for both ✔; `#print axioms` on
all five new public theorems and eight QA headlines — `propext,
Classical.choice, Quot.sound` only; **full `lake build` ✔ (2232
targets, "Build completed successfully")**; `lint_axioms` (10,
unchanged), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1404/10/0**, idempotent under re-run). Records updated:
the proposal (Step-1a delivery record, the inline survey correction at
its step 6, the status header, open-next-step → 1b),
`proposals/README.md` (Medium row + the no-High-rows paragraph), the
SGT index map (Cheeger section +4 rows + program note), README (1404,
the trust-surface sentence noting the 1a layer), the radar (QA axis
held 4.0, count synced 1378/39 → 1404/39, hold logged), the scoreboard
(both Direct rows, the `lake build` row, lint date, a new
interpretation bullet), this plan, and the activity log. The worktree's
unrelated operator-side change (`proposals/palomar-submission.md`)
preserved untouched; nothing committed.

**Next milestone (open):** **Cheeger Step 1b** — the co-area core, the
crux: for `y ≥ 0` whose nonempty level sets are minority-side,
`½ ∑ A |y i² − y j²| ≥ φ d ∑ y i²`, by the interval-integral encoding
(per-pair FTC + the hand Finset-induction Fubini, ~30 lines of friction
the survey priced in) + per-level conductance; must consume the Step-1a
interfaces at their corrected constant budget. Then Step 1c (median +
assembly) retires `cheeger_lower_bound` at the unchanged statement.
**Approximate spectral projection** still needs its Step 0; the PF
consumers (irreducible stationary distributions, PageRank) are
new-proposal candidates. Reversibility Phase B and Fiedler Phase B
still need operator decisions.

---

**Cheeger hard-direction Step 0 survey (run 1, 2026-08-22;
`proposals/discharge-perturbation-axioms.md` at its recorded open next step —
the top-ranked Medium item with the Active table holding no High rows and the
execution plan's own recorded next handoff naming this survey first: the last
perturbation-axiom remainder, `cheeger_lower_bound` (`Cheeger.lean:88`),
`φ²/2 ≤ λ₂(L_sym)` on `d`-regular graphs): DELIVERED — decisive
positive-with-large-cost, the proposal's whole per-axiom gate now satisfied;
Step 1 is authorized as dedicated runs per the Davis–Kahan precedent. Zero
Lean source changes (count stays 10 axioms, QA stays 1378); the deliverable
is the survey record plus a green, axiom-clean spike.**

**Delivered — the survey's decisive findings (all recorded in the proposal
before any Step-1 edit):**

1. **The reduction that dissolves the spectral side:** the shelf's proved
   `secondEval_variational` (`Spectral.lean:1745`) turns the theorem into
   one sweep lemma (`∀ x ⊥ 1, x ≠ 0: φ²/2 ≤ R_{L_sym}(x)`) via `le_csInf`
   — no eigenvector, no spectral-side work; both of `L_sym`'s side
   conditions are already-proved `Cheeger.lean` theorems. The assembly
   skeleton is **spike-verified end-to-end in hypothesis form**
   (`CheegerSpike.assembly_skeleton`, `#print axioms` the standard three).
2. **The tight-constant route, reconstructed and hand-checked twice:** the
   median split of `x − m·1` into its two positive parts routes both parts
   to minority-side level sets (the half-volume obstruction is real —
   recorded with the (2,2,2,2,2,−1,−1,−1) counterexample shape so no
   future run re-derives it); per part, co-area + Cauchy–Schwarz +
   Lipschitz contraction give `φ²d‖y‖² ≤ E'(y)`; the norm split
   `‖u‖²+‖v‖² = ‖x‖² + nm² ≥ ‖x‖²` makes the two parts jointly carry the
   full norm, so the factor 2 from summing both parts is *exactly* the
   statement's `/2` — nothing lost anywhere in the chain.
3. **Spike-verified green components** (`wip/cheeger_spike.lean`,
   git-ignored, every `#print axioms` clean): Component A —
   `(∑_{ij} A i j |f i² − f j²|)² ≤ (∑_{ij} A i j (f i − f j)²)·(4∑ i deg i f i²)`
   via `Finset.sum_mul_sq_le_sq_mul_sq` over `V × V` (statement guard
   found: needs `IsSymm`, not just nonnegness — the cross double sum's
   column sums must match `deg`'s row sums); the 1-Lipschitz shifted-
   positive-part contraction `|max (a−m) 0 − max (b−m) 0| ≤ |a−b|`; the
   scalar FTC primitive `∫ t in a..b, 2t = b²−a²`.
4. **Pin facts recorded with traps:** `Fintype.sum_prod_type'` direction;
   `Real.mul_self_sqrt` vs the *different* `Real.sqrt_mul_self`;
   `intervalIntegral.integral_congr`'s `Set.EqOn (uIcc a b)` form; the
   `intervalIntegral.*` dotted-name race against the root-level integral
   *function* (use `open intervalIntegral` + bare names);
   `Matrix.IsSymm.apply`'s swapped argument convention; and **no
   finite-sum/interval-integral interchange exists at this pin** — the
   co-area Fubini needs a ~30-line Finset induction over `integral_add`
   (priced into Step 1b).
5. **Step-1 decomposition with cost estimates:** 1a pure algebra
   (~150–250 lines, low risk, entirely spike-verified — the next run's
   transfer), 1b the co-area core (~250–400 lines, the crux,
   moderate-high risk — the analogue of Davis–Kahan's equal-rank
   lemma), 1c median + assembly (~150–250 lines, moderate risk);
   550–900 total, with the constant-pinning QA discipline (K₂ equality +
   strict case) carried forward before Step 1's statements freeze — this
   repository has been burned by a false Cheeger shape before.

**Verification:** `lake env lean wip/cheeger_spike.lean` — zero errors (one
unused-section-variable warning), `#print axioms` on all three named theorems
reads `propext, Classical.choice, Quot.sound`; `lake build` of
`Scaffold.Mathlib.GraphTheory.Cheeger` ✔ (untouched module, explicit target —
no `Scaffold/**` file changed this run, so the umbrella build certifies
nothing new and the spike's direct elaboration is the decisive check);
`lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated, **zero diff** (idempotent — counts unchanged
at 1378/10/0). Records updated: the proposal (status header, the full survey
record replacing "unsurveyed", per-axiom item 3, open-next-step → Step 1a),
`proposals/README.md` (Medium row + the no-High-rows paragraph), this plan,
and the activity log. The worktree's unrelated operator-side change
(`proposals/palomar-submission.md`) preserved untouched. Nothing committed.

**Next milestone (open):** **Cheeger Step 1a** — the pure-algebra component
transferred to `Cheeger.lean` at its public shape (Component A with the
`IsSymm` guard, summed contraction, translation invariance, the
`R = E'/(d‖x‖²)` normalization) with QA; then 1b (the co-area core) and 1c
(median + assembly) as dedicated runs. **Approximate spectral projection**
still needs its Step 0. The PF consumers (irreducible stationary
distributions, PageRank) are unblocked as new-proposal candidates, each
needing its own document. Reversibility Phase B and Fiedler Phase B still
need operator decisions.

---

**Perron–Frobenius admission (run 1, 2026-08-22; `proposals/admit-perron-frobenius.md`,
the top-ranked Medium row with the Active table holding no High rows and
the recorded next milestone of the directed-operators completion — whose
sharpest output, the PSD refutation, explicitly names Perron–Frobenius as
what the directed spectral theory now needs): DELIVERED — the scoped
admission, one new explicit cited axiom (9 → 10), the first admission
since the 2026-08-19 scope decision.**

**Delivered:** the new `Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean`
(namespace `Scaffold.LinearAlgebra`) — the combinatorial irreducibility
predicate `Matrix.IsIrreducible` (global, Fintype-free, `ReflTransGen`
on positive entries — mirroring `Matrix.IsSymm`'s reading surface rather
than a bespoke predicate) and the admitted axiom `perron_frobenius` at
the proposal's scoped qualification level: `0 < r` with a strictly
positive eigenvector `A *ᵥ x = r • x`; simplicity as
`rootMultiplicity r A.charpoly = 1` over ℝ; the strong H&J uniqueness
(every nonzero nonnegative eigenvector, whatever its eigenvalue, is a
positive multiple of `x`) with the only-eigenvalue clause `μ = r` as an
explicit conjunct; and complex-spectrum domination
`∀ z ∈ (charpoly (A.map (algebraMap ℝ ℂ))).roots, |z| ≤ r` — together
with the first conjunct this is exactly "`r = ρ(A)` and `ρ(A)` is an
eigenvalue", encoded directly because the pin has no matrix spectral
radius. Two recorded statement guards: the `hex : ∃ i j, 0 < A i j`
degeneracy guard (H&J implicitly at `n ≥ 2`, where irreducibility
already forces a positive entry; over arbitrary `Fintype V` the
vacuously irreducible 1×1 zero matrix and the empty type would falsify
`0 < r` — `hex` is exactly the missing strength) and **no
strict-dominance clause** (primitivity's requirement, honored verbatim
from the proposal's Calibration section).

**QA** (`Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`, 36
declarations — the first LinearAlgebra-domain file; zero errors, zero
warnings; `#print axioms` split verified: the five axiom-consuming
theorems list exactly `perron_frobenius` + the three standard axioms,
the eleven hand theorems only the standard three): both fixtures
asymmetric and rational — the positive witness `P = !![1,2;1,0]`
(primitive) with the Perron root **derived to be exactly 2** from the
axiom's eigen-equation on its unknown existential witness, the Perron
vector pinned to a positive multiple of the hand `(2,1)`, the
simplicity clause cross-checked against the hand factorization
(`charpoly = (X+1)(X−2)`, `rootMultiplicity 2 = 1`), the complexified
charpoly's roots pinned to `{2, −1}`, and the domination clause
instantiated at both roots (the strict case); and the mandated
**imprimitive-cycle negative witness** `D = !![0,4;1,0]` (asymmetric
directed 2-cycle) — `strict_dominance_refuted_QA` refutes the
strengthening at `|−2| = 2 = r` (hand Perron pair + hand eigenpair, no
axiom consumed: the refutation targets the strengthening, not the
axiom) while `D_axiom_domination_QA` instantiates the axiom's own
clause at the same peripheral root with equality — the weaker
conclusion is exactly what survives on imprimitive input. Hand-only
only-eigenvalue theorems on both fixtures, cross-checked against the
axiom's clause through the hand Perron eigenvector.

**Verification:** `lake env lean` on the module and QA — zero errors,
zero warnings each; explicit target builds of both ✔; `#print axioms`
as above ✔; umbrella import added and **full `lake build` ✔ (2232
targets, "Build completed successfully", zero errors, detached)**;
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1378/10/0**, idempotent under re-run). Records
updated: the proposal (status header DELIVERED, full delivery record
with pin-specific QA techniques — `open Polynomial` plain vs scoped for
`X`/`C`, eta-expanded `fin_cases` indices bridged by `show`,
C-numeral-to-numeral helpers because `ring` treats `C c` as an atom and
this pin's `C_mul` points opposite to modern Mathlib, the `(2:ℝ) •`
annotation trap, and the `charpoly_map`-vs-`coe_algebraMap` mismatch
avoided by direct `det_fin_two` computation), `proposals/README.md`
(Active Medium row retired, progress paragraph rewritten, Delivered row
prepended), the Horn–Johnson source index (Theorem 8.4.4 row + scope
note), the new `index/map/linear_algebra.md` + map README row, the
coverage map's named-absent row updated, backlog item 8 (third update),
README (10 axioms, 1378 QA, trust-surface prose, module table row),
radar (QA axis count synced 1342/38 → 1378/39, held at 4.0, hold
logged), scoreboard (both Direct rows, `lake build` row, lint row,
interpretation bullet), this plan, and the activity log. Nothing
committed.

**Next milestone (open):** the Medium rows by leverage — **the Cheeger
hard-direction Step 0 survey** (known-hard working assumption; the
last perturbation-axiom remainder) and **approximate spectral
projection** (Step 0 first). The PF consumers — irreducible stationary
distributions and PageRank — are now unblocked as new-proposal
candidates, each needing its own document per the one-step discipline.
Reversibility Phase B and Fiedler Phase B still need operator
decisions.

---

**Perron–Frobenius admission (run 1, 2026-08-22; `proposals/admit-perron-frobenius.md`,
the top-ranked Medium row with the Active table holding no High rows and
the recorded next milestone of the directed-operators completion — whose
sharpest output, the PSD refutation, explicitly names Perron–Frobenius as
what the directed spectral theory now needs): the proposal's scoped
admission — irreducibility via directed reachability, the axiom at Horn &
Johnson Theorem 8.4.4's qualification level (no strict-dominance clause),
QA with the mandated positive witness and the imprimitive-cycle negative
witness, and the index/coverage/count records. Adds one explicit cited
axiom (9 → 10). No consumer work (stationary distributions, PageRank stay
named follow-ons).**

**Pre-edit survey findings (this run):** no `Matrix.spectralRadius` in the
pin (the only `spectralRadius` hits are operator-theory/C* files, the same
thread the resolvent program already found structurally inapplicable to
real matrices), so the spectral-radius content is encoded directly: `r` is
an eigenvalue with the complex-spectrum domination clause
`∀ z ∈ (charpoly (A.map (algebraMap ℝ ℂ))).roots, |z| ≤ r` — together these
say exactly "r = ρ(A) and ρ(A) is an eigenvalue". Pin facts verified:
`rootMultiplicity a p` argument order, `Polynomial.roots_mul`,
`roots_X_sub_C`, `Matrix.charpoly_map`, `Complex.abs` (not `Complex.norm`)
with `abs_ofReal`/`abs_natCast`.

**Statement-shape decisions (recorded before stating):** (1) statement
degeneracy guard `(hex : ∃ i j, 0 < A i j)` — H&J implicitly work at
n ≥ 2, where irreducibility already forces a positive entry; over
arbitrary `Fintype V` the 1×1 zero matrix (vacuously irreducible) and the
empty type would make `0 < r` false, so `hex` is exactly the missing
strength, not decoration. (2) The uniqueness clause is the strong H&J
form — every nonnegative eigenvector (any eigenvalue, nonzero) is a
positive multiple of the Perron vector — with the proposal's fourth bullet
(only `r` has a nonnegative eigenvector) as an explicit conjunct. (3)
Simplicity as `rootMultiplicity r (charpoly A) = 1` over ℝ (real-root
multiplicity is invariant under ℝ → ℂ extension). (4) Irreducibility
defined globally as `Matrix.IsIrreducible` via `ReflTransGen` on positive
entries (Mathlib-convention reading surface, mirroring `Matrix.IsSymm`),
Fintype-free. QA fixtures both rational by design: positive witness
`!![1,2;1,0]` (asymmetric, Perron root 2, eigenvector (2,1), other
eigenvalue −1 — the primitive case where dominance is strict), negative
witness `!![0,4;1,0]` (asymmetric directed 2-cycle, Perron root 2, second
eigenvalue −2 with eigenvector (−2,1), equal moduli — the imprimitive
peripheral spectrum the Calibration section warns about).

**Next action:** write `Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean`,
QA at `Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`, then
records (umbrella, Horn–Johnson index row, map row, coverage map, counts).

---

**Directed operators Step 2 (the directed normalized Laplacian) + the
Step-3 agreement brick — run 1, 2026-08-22; `proposals/directed-graph-operators.md`
at its recorded open next step, the top-ranked Medium row with the Active table
holding no High rows: DELIVERED — the proposal's Lean content is COMPLETE
(Step 3's remaining content was recorded by the Step-0 record as "one line from
decision (b)", so folding it into Step 2's run is the same one-Lean-step shape
Steps 0+1 used). Zero new axioms (count stays 9).**

**Delivered:** in `GraphTheory.Directed` — `directedNormalizedLaplacian`
(`I − ½(SAS + SAᵀS)`, `S = degreeInvSqrt` — the out-degree normalization of
decision (b); the shelf's square-root diagonals reused verbatim since `deg`
*is* the out-degree), the entry form, **hypothesis-free symmetry** (the two
defining halves are transposes of each other — the directed axis' one
symmetric operator), the acceptance-bar agreement
`= normalizedLaplacian` under `A.IsSymm`, and the square-root-free conjugate
`√D L_dir √D = degreeMatrix A − ½(A + Aᵀ)` (the symmetrized adjacency at
out-degree normalization, exact analogue of the shelf's
`degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`).

**The delivery's sharpest output is a refutation:** `L_dir` is symmetric but
provably **not PSD** on directed input — QA's `dirB = !![0,4;1,0]` fixture
(nonnegative, positive out-degrees, `L_dir` symmetric by the theorem) has
`quadForm L_dir 1 = −1/2 < 0` (the symmetrized weight `5/2` overweights the
out-degree normalization `√4·√1 = 2`, driving `L_dir 0 1` to `−5/4` past
`−1`), so the positivity layer of the undirected toolkit does not transfer —
the proposal's Calibration boundary, now witnessed numerically; the directed
spectral theory needs Perron–Frobenius.

**QA** (`Directed_QA.lean`, 41 → 88 declarations; `#print axioms` on nineteen
headline QA theorems clean): all nine `L_dir dirA` entries computed from the
entry form (degrees `(4,1,1)` all squares → the operator is exactly
`[[1,−1,−1/2],[−1,1,0],[−1/2,0,1]]`); symmetry through the theorem on
asymmetric input (the load-bearing certification) and raw at the `(0,1)/(1,0)`
pair; the conjugate instantiated with both sides' `(0,1)` entries computed raw
and matching at `−2`; the symmetric-edge agreement through the Step-3 theorem
with both operators pinned raw; and the two new negative witnesses — undirected
reuse (`L_dir dirA ≠ normalizedLaplacian dirA`, `−1 ≠ −3/2`) and the PSD
refutation above.

**Verification:** `lake env lean` on the module and QA — zero errors, zero
warnings each; explicit target builds of both ✔; `#print axioms` on the five
new public and nineteen headline QA theorems ✔ (three standard axioms only);
**full `lake build` ✔ (2230 targets, "Build completed successfully", zero
errors, detached)**; `lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1342/9/0**;
`Directed_QA` 41 → 88). Records updated: the proposal (status header
COMPLETE, Step-2 delivery record with the pin-specific QA techniques —
`Real.sqrt_eq_iff_eq_sq` for numerals, `if_pos rfl`/`if_neg (by decide : …)`
for the entry form's conditional (not `Matrix.one_apply_ne (by decide)`:
metavariables), full `simp` for ground `Fin`-index `if`s that `norm_num`
leaves standing, and the `rw`-rewrites-all-occurrences duplicate trap),
`proposals/README.md` (Medium row → program complete, progress paragraph,
Delivered row), backlog item 8 (second update), the SGT index map (Directed
section, +5 rows), README (1342, proved list, module table), radar (QA axis
count synced **1295/38 → 1342/38**, held at 4.0, hold logged), scoreboard
(both Direct rows, the `lake build` row, a new interpretation bullet), this
plan, and the activity log. Nothing committed.

**Next milestone (open):** the Medium rows by leverage — **the Perron–Frobenius
admission** (`admit-perron-frobenius.md` — decoupled by the Step-0 record;
its QA plan's imprimitive-cycle negative witness is the centerpiece; the
natural continuation of the directed axis this run completed), the **Cheeger
hard-direction Step 0 survey** (known-hard working assumption), and
**approximate spectral projection** (Step 0 first). Reversibility Phase B and
Fiedler Phase B still need operator decisions.

---

**Directed operators Step 0 (survey + convention decisions) + Step 1
(the degree layer) — run 1, 2026-08-22;
`proposals/directed-graph-operators.md` + the coordinated build-order
decision with `proposals/admit-perron-frobenius.md`, the top-ranked
Medium program with the Active table holding no High rows: DELIVERED —
the directed axis is open, zero new axioms (count stays 9).**

**Step 0 decisions (all recorded in the proposal before any Lean
statement):**

- **(c) Mathlib re-survey:** no directed Laplacian in the pin —
  `LapMatrix.lean` is the undirected SimpleGraph one; `Combinatorics/
  Digraph/` is relation-structures only. PF re-confirmed absent.
  Coverage map rows hold; no correction needed.
- **(a) Carrier:** reuse — no new type. `WAdj` is an abbrev of
  `Matrix V V ℝ` with symmetry only ever a call-site hypothesis, so the
  named reuse risk is structurally absent; the directed axis is stated
  on `Matrix V V ℝ` directly.
- **Discovery:** items 1 and 3 of the recommendation *already exist
  hypothesis-free* — `deg` is the row sum (out-degree) and
  `walkTransitionMatrix = D⁻¹A`, `walkLaplacian = I − D⁻¹A` carry no
  symmetry hypothesis, with row-stochasticity and conservation proved
  for any positive-row-sum matrix. Step 1's genuine content: `inDeg`,
  degree agreements, directed handshaking, and the asymmetric-input QA
  certification.
- **(b) Convention:** the out-degree-symmetrized normalized Laplacian
  `I − ½(D_out^{-1/2}AD_out^{-1/2} + D_out^{-1/2}AᵀD_out^{-1/2})` —
  symmetric by construction, reduces to `normalizedLaplacian` on the
  symmetric cone, axiom-free. Deliberately *not* Chung 2005's
  Perron-vector convention (which would make an admitted axiom a
  prerequisite of a definition). **Build-order consequence recorded:
  the two proposals are decoupled** — PF proceeds on its own leverage
  case (irreducible stationary distributions, PageRank); Chung's
  Laplacian remains a later separate definition once PF exists.

**Step 1 delivery:** the new `Scaffold/Mathlib/GraphTheory/Directed.lean`
— `outDeg`, `inDeg` (column sum), `outDeg_eq_deg` /
`inDeg_eq_deg_transpose` (both `rfl`), `inDeg_eq_outDeg_of_isSymm` +
`inDeg_eq_deg_of_isSymm` (the symmetric cone — the walk-operator part
of the Step-3 bar needs no separate theorem since the definitions are
shared), and `sum_outDeg_eq_sum_inDeg` (directed handshaking by
`Finset.sum_comm`). QA `Scaffold/QA/SpectralGraph/Directed_QA.lean`
(41 declarations): the genuinely-directed fixture
`!![0,3,1;1,0,0;1,0,0]` with `outDeg = (4,1,1) ≠ (2,3,1) = inDeg` (the
negative witness), row-stochasticity + conservation instantiated **on
asymmetric input** through the pre-existing shelf theorems (the
load-bearing certification — had `walkTransitionMatrix` been defined
through the symmetrized adjacency, or `deg` through a symmetric sum,
these instantiations would fail), the walk matrix's asymmetry refuted
(`3/4 ≠ 1`), agreement on a symmetric fixture through the theorems and
raw, handshaking `6 = 6` by both routes.

**Verification:** `lake env lean` on the module and QA — zero errors,
zero warnings each (the `DecidableEq`-free theorems carry `omit`
clauses); explicit target builds of both ✔; `#print axioms` on the
seven public and twelve headline QA theorems ✔ (three standard axioms
only); umbrella import added and **full `lake build` ✔ (2230 targets,
"Build completed successfully", zero errors, detached)**;
`lint_axioms` (**9**, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1295/9/0**;
`Directed_QA` a new file row at 41; both Direct rows and the
`lake build` row extended; a new interpretation bullet). Records
updated: the proposal (status header, Step-0 record, Step-1 delivery
record with the pin-specific QA technique — the `vecHead/vecTail`
simp residue on new-def unfolds and the `rfl`-table +
`Fin.sum_univ_three` deterministic route), `proposals/README.md`
(Medium row + progress paragraph), backlog item 8, the SGT index map
(new Directed section), README (1295, proved list, module table),
radar (QA axis count synced **1295/38**, held at 4.0, hold logged),
this plan, and the activity log. Nothing committed; the worktree's
prior-run uncommitted deliveries remain preserved.

**Next milestone (open):** the Medium rows by leverage — **directed
operators Step 2** (the normalized Laplacian at the recorded
convention; unblocked), **the Perron–Frobenius admission**
(`admit-perron-frobenius.md` — decoupled by the Step-0 record; its QA
plan's imprimitive-cycle negative witness is its centerpiece), the
**Cheeger hard-direction Step 0 survey** (known-hard working
assumption), and **approximate spectral projection** (Step 0 first).
Reversibility Phase B and Fiedler Phase B still need operator
decisions.

**Subgaussian tail bound — Step 0 spike + repair-and-retire in one run
(run 1, 2026-08-22; `proposals/prove-subgaussian-tail-bound.md`, the
2026-08-22 operator-directed addition — the top-ranked Medium row with
the Active table holding no High rows): DELIVERED — explicit axioms
10 → 9, the repository's first measure-theoretic axiom retirement.**

**Not the retirement the proposal's Step 2 envisioned — a correctness
repair instead (Woodbury precedent, decision recorded before stating).**
The mandated Step 0 spike (`wip/subgaussian_spike.lean`, git-ignored,
green end-to-end) confirmed the old statement — `(hK : 0 ≤ K)
(h_sub : subgaussianNorm X μ ≤ K)` — was **materially false in two
independent junk ways**: (1) `Real.sInf_empty` (Archimedean.lean:190)
makes the norm-hypothesis vacuous when the defining set is empty (any
measure of total mass > 2); (2) `MeasureTheory.integral_undef`
(Bochner.lean:743) — the Bochner integral of a non-integrable function
*is defined to be 0* — so heavy-tailed `X` satisfy the defining MGF
bound at every `K` (the set is **full**, not empty — this also
falsified the `subgaussianNorm` docstring's recorded junk behavior,
which was corrected with a dated note), norm `0`, and the old
conclusion would claim subgaussian tails even under probability
measures. Both refuted in QA with the old hypotheses proved satisfied
(`3 • δ₀`: every MGF integral `3 > 2`, norm `= 0 ≤ 1` vacuously,
conclusion at `t = 0` reads `3 ≤ 2`).

**Repaired statement (same name, same conclusion incl. the `2K²`
constant, same `t`/`ht`):** hypotheses `(hK : 0 < K)`,
`h_int : Integrable (fun ω => exp (X ω ^ 2 / K ^ 2)) μ`,
`h_mom : ∫ ω, exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2` — exactly the content
Markov's inequality consumes; strictly stronger than the old shape
whenever that was non-vacuous; the junk `K = 0` branch (bound `2·exp 0
= 2`) dropped. **The proposal's open `K = sInf` boundary question
dissolves** — the repaired hypotheses never mention the `sInf`
(recorded in the delivery record per the acceptance criteria).

**Route (every lemma verified at this pin's exact signature):** the
`Real.exp_half` square-root bridge gives ae-strong-measurability at the
half scale *as a function of the hypothesis-side MGF* (no measurability
hypothesis on `X` needed — `Continuous.comp_aestronglyMeasurable`);
`Integrable.mono'` + `integral_mono_of_nonneg` transfer the moment;
shelf Markov `mul_meas_ge_le_integral_of_nonneg` (no `0 ≤ ε` at this
signature) at `exp (t²/(2K²))`;
`Integrable.measure_norm_ge_lt_top` forces the Markov event finite (the
step the toReal-shaped Markov cannot give at `μ = ∞`); ENNReal
conversion via `ofReal_toReal`/`ofReal_le_ofReal`. `#print axioms` on
the theorem: `propext, Classical.choice, Quot.sound` only.

**QA** (`Scalar_QA.lean` 6 → 17; axiom-clean on all twelve touched/new
theorems; the zero-QA family no longer consumes `hoeffding_lemma`): the
zero fixture through the new hypotheses; the proposal-mandated
**nonzero instance** (constant-1, `K = 2`, `t = 1` on `dirac 0`;
moment `exp (1/4) ≤ 2` via the pinned `Real.log_two_gt_d9`; event side
`= 1` and bound side `1 ≤ 2·exp (−1/8)` both pinned raw); the
four-piece refutation family (fixture, empty-set junk mechanism
exhibited as a theorem, old hypotheses provably satisfiable, old
conclusion refuted).

**Verification:** `lake env lean` on the module (only the pre-existing
`unused variable K` warning, verified identical in HEAD) and on the QA
file (zero errors; nine remaining warnings = the pre-existing set in
untouched declarations, verified against HEAD); module + QA oleans
built explicitly; **full `lake build` ✔ (2229 targets, "Build completed
successfully", detached)**; `lint_axioms` (**9**), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated
(**1254/9/0**, idempotent under re-run). Records updated: both index
files (`vershynin_hdp.md` — the Chapter-2 row is its first
proved-not-axiom row; `probability_concentration.md` with the
junk-behavior notes), scoreboard (counts, both Direct rows, `lake
build` row, lint row, interpretation bullet), radar (axiom-minimization
axis synced to 9 with the trend extended and the hold logged; QA axis
count synced 1254/37, held), README (counts, trust-surface prose),
architecture §12 (retirement + residual note), the module's two
docstrings (`subgaussianNorm` junk-behavior correction;
`hoeffding_lemma`'s stale QA-note referencing the nonexistent
`hoeffding_lemma_zero_QA`), the proposal (full delivery record with
pin-specific API notes and the adjacent-hazard residual), this plan,
and the activity log. The worktree's unrelated operator-side change
(the `proposals/README.md` Low row for the clean-room lemma map) was
preserved untouched. Nothing committed.

**Named residual (for other axioms' Step 0s, not addressed here):** the
same junk-integral mechanism likely infects
`hoeffding_inequality`/`bernstein_inequality`'s mean hypotheses on
infinite measures and the matrix trio's `MatrixMDS` set-integrals —
recorded in the proposal and architecture §12.

**Next milestone (open):** the Medium rows by leverage —
**Perron–Frobenius + directed operators** (scoped together, Step 0
first per the convention-choice gate), the **Cheeger hard-direction
Step 0 survey** (known-hard working assumption), and **approximate
spectral projection** (Step 0 first). Reversibility Phase B and Fiedler
Phase B still need operator decisions.

---

**Relative Entropy and Shannon Entropy for finite distributions — both
steps, one program (run 1, 2026-08-22; `proposals/finite-relative-
entropy.md`, the top-ranked Medium row with the Active table holding no
High rows and its own backlog gate recorded open): DELIVERED — the
program is COMPLETE.**
Pure hard crust — **zero new axioms** (count stays 10; `#print axioms`
on all nine public theorems — the scalar pair, the four Gibbs/entropy
statements, the bridge, and the uniform normalization — reads only
`propext, Classical.choice, Quot.sound`). Closes the entropy half of
backlog item 6 (the reversibility half landed earlier the same day).

**Pre-edit survey (the proposal's mandated Jensen-API survey, done
before any statement):** the full shelf is present in the pin —
`ConcaveOn.le_map_sum` (Jensen.lean:71), `StrictConcaveOn.lt_map_sum`
(:145), `StrictConcaveOn.eq_of_map_sum_eq` (:169),
`StrictConcaveOn.map_sum_eq_iff'` (:233, the nonnegative-weights
equality case), `strictConcaveOn_log_Ioi`
(SpecificFunctions/Basic.lean:63) — so the proposal's stop-and-record
clause (a missing Jensen variant) is **not** triggered.

**Route decision (recorded before stating):** delivered by the *term-wise*
information inequality instead — `Real.one_sub_inv_le_log_of_pos`
(Log/Basic.lean:281, `1 − x⁻¹ ≤ log x`) for nonnegativity and
`Real.log_lt_sub_one_of_pos` (Log/Basic.lean:230, strict off `x = 1`)
for the equality case. This is the same textbook proof (Cover–Thomas
2.6.3's own route via `log t ≤ t − 1` term-wise), needs no Finset-`smul`
Jensen plumbing, no `Ioi`-membership side conditions, and no
support-finset filtering: the `p i = 0` junk case is discharged inside
the per-term bound (`0 ≥ −q i`), and strictness there is *stronger*
(`gap = q i > 0`) — the equality case `p = q` falls out with no
`∑_{support} q` argument at all.

**Statement-shape decisions (recorded before stating, honored as
stated):** `klDiv p q := ∑ i, if p i = 0 then 0 else p i * Real.log
(p i / q i)` (factored through the scalar `klTerm` — the visible junk
convention the proposal mandates); `shannonEntropy p := -∑ i, klTerm
(p i) 1` (the proposal's exact sign); the equality iff at full
function equality `p = q`; the entropy maximum at `Real.log
(Fintype.card V)` with equality iff `p` is uniform, with `Nonempty V`
*derived* from `∑ p = 1` rather than assumed.

**Delivered:** the new `Scaffold/Mathlib/InformationTheory/Entropy.lean`
(namespace `Scaffold.InformationTheory`): `klTerm`, `klDiv`,
`shannonEntropy`, `sub_le_klTerm` + `eq_of_klTerm_eq_sub` (the
term-wise core), `klDiv_nonneg` + `klDiv_eq_zero_iff` (Gibbs both
directions), `sum_inv_card_eq_one`,
`klDiv_apply_uniform` (the bridge), `shannonEntropy_le_log_card` +
`shannonEntropy_eq_log_card_iff`, and `shannonEntropy_nonneg`.

**QA** (`Scaffold/QA/InformationTheory/Entropy_QA.lean`, 31
declarations; `#print axioms` on thirteen headlines clean): the biased
coin's divergence and entropy each **hand-computed** to closed
log-forms (`¼·log(27/16)`, `¼·log(256/27)`) with the divergence pinned
strictly positive; the equality case exercised in both directions
against raw computations; **the uniform bridge numerically
cross-checked** at the fair coin (`¼·log(27/16) = log 2 −
¼·log(256/27)`, both sides independently pinned — load-bearing on the
bridge); the maximum attained at uniform on `Fin 4` two ways and
**strictly missed** by the non-uniform `(1/2, 1/6, 1/6, 1/6)` —
strictness only through the equality-case iff, the proposal's
prescribed load-bearing use — plus the divergence-side companion; and
the delta distribution's entropy exactly `0`, the junk convention
exhibited.

**Verification:** `lake env lean` on the module and QA — zero errors,
zero warnings each; explicit target builds of both modules ✔;
`#print axioms` on the nine public and thirteen headline QA theorems ✔
(three standard axioms only); umbrella import added and **full
`lake build` ✔ (2229 targets, "Build completed successfully", zero
errors)**; `lint_axioms` (10, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1243/10/0**;
`Entropy_QA` a new file row at 31). **Build-reachability fact recorded
this run (content-change probe):** the default `lake build` target is
the `Scaffold.lean` umbrella closure — it certifies every public
module including the new one, but does not itself compile the QA tree;
QA modules are certified by direct elaboration and explicit targets
(the scoreboard's `lake build` row now states this scope precisely).
Records updated: proposal (status header, full delivery record with
pin-specific API notes — `Real.log_pow`/`Real.log_inv` explicit
arguments, `Finset.sum_one` absent at that name, `ring_nf` for
coefficient-atom identities, `Finset.sum_sub_distrib`'s orientation —
open-next-step → none with the deferred items named),
`proposals/README.md` (Medium row → Delivered; progress paragraph),
the new `index/map/information_theory.md` + map README row, scoreboard
(counts, both Direct rows, `lake build` row, QA-declaration bullet, a
new interpretation bullet), radar (QA axis held at 4.0, count synced
**1243/37**, sync logged), README (1243, module table, proved list,
and the stale conditional-on-Davis–Kahan persistence note corrected),
backlog item 6 (entropy half delivered), this plan, and the activity
log. The worktree's unrelated operator-side and prior-run-uncommitted
changes remain preserved untouched.

**Next milestone (open):** the Medium rows by leverage — **the
subgaussian tail bound** (the 2026-08-22 operator-directed addition —
run its Step 0 first), **Perron–Frobenius + directed operators** (Step
0 first per the convention-choice gate), the **Cheeger hard-direction
Step 0 survey** (known-hard), and **approximate spectral projection**
(Step 0 first). Reversibility Phase B and Fiedler Phase B still need
operator decisions.

---

**Mixing-time Step 3, component 2 of 2 — the χ² assembly, the program's
closing statement (run 1, 2026-08-22; `proposals/mixing-time-bound.md`
at its recorded open next step — the top Medium row with the Active
table holding no High rows; component 2 is exactly the numbered gluing
list the component-1 delivery record left): DELIVERED — the mixing-time
program is COMPLETE.**
Pure hard crust — **zero new axioms** (count stays 10; `#print axioms`
on all seven new public theorems — three entry lemmas in `Normalized`,
four theorems in `Mixing` — reads only `propext, Classical.choice,
Quot.sound`). Radar axis 5 **re-scored 3.0 → 3.5** per the proposal's
own gate (the mixing *statement* is the trigger; its proof and QA have
both landed).

**Statement-shape decisions (recorded before stating, honored as
stated):** connectivity enters as the shelf kernel theorem's exact
hypotheses (`(supportGraph A hA).Connected` + `hnonneg`) — the QA
negative witness proves the conclusion *false* without it even when the
rate hypothesis genuinely holds; the rate stays hypothesis-shaped; no
`t = 0` special case.

**Delivered:** in `Normalized.lean` the constant fix
`walkTransitionMatrix_mulVec_one` (`P *ᵥ 1 = 1`) and the entry lemmas
`degreeSqrt_mulVec_apply`/`degreeInvSqrt_mulVec_apply`; in `Mixing.lean`
the centered evolution `walkDensity_sub_one`
(`h_t − 1 = Pᵗ *ᵥ (h₀ − 1)`), mass conservation
`sum_deg_mul_walkDensity_sub_one_eq_zero`, the connectivity mode
derivation `eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_
of_eigvalOf_eq_zero` (the one piece with real content: kernel transfer
through the congruence `√D L_sym √D = L` → the shelf's
`exists_const_of_laplacian_mulVec_eq_zero` → entrywise
`v k = √(deg k)·c` → collapse by mass conservation), and the headline
`chiSquareDistance_le_of_connected` —
`χ²(t, x) ≤ r^(2t) · ((π x)⁻¹ − 1)`. The route landed exactly as
paved, with the forecast risks (the `√2`-atom QA arithmetic, the
loop-row symmetry step) both consumed by the recorded techniques.

**QA** (`Mixing_QA.lean`, 67 → 117 declarations; `#print axioms` on
twelve headline QA theorems clean): K₃ with the final bound
**attained exactly** at `t = 1, 2` (both sides pinned raw); the
centered-evolution and connectivity-derived-mode cross-checks against
the component-1 hand computations; P₃'s rate derived basis-independently
from two SOS certificates (the Dirichlet identity
`v ⬝ L_sym v = (v₀ − v₁/√2)² + (v₂ − v₁/√2)²` and its `2‖v‖² − ·`
companion — every eigenvalue in `[0, 2]`, no exact spectrum), the
λ* = 1 bound honest and strict (`1 ≤ 3`); **negative witnesses**:
connectivity load-bearing on the triangle⊕self-loop `Fin 4` fixture
(spectrum `{0, 0, 3/2, 3/2}` derived basis-independently, rate
hypothesis *provably holding* at `r = 1/2` — the loop's `μ = 0` mode
excluded from the rate hypothesis by design, exactly the hole
connectivity plugs — while `χ²(3) = 3/8 > 3/64` refutes the
conclusion), and the rate load-bearing at `r = 1/4` (hypothesis
unsatisfiable by the trace, conclusion `1/2 > 1/8` refuted).

**Verification:** `lake env lean` on `Normalized.lean` (only its
documented pre-existing `congr 1` note), `Mixing.lean`, and
`Mixing_QA.lean` (zero errors, zero warnings on the latter two);
`#print axioms` on the seven new public and twelve headline QA theorems
✔ (three standard axioms only); oleans built; **full `lake build` ✔
(2228 targets, "Build completed successfully", detached, zero
errors)**; `lint_axioms` (10, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1212/10/0**;
`Mixing_QA` 67 → 117). Records updated: proposal (status header
COMPLETE, full component-2 delivery record with the two pin-specific
API discoveries — this snapshot's `Finset.mul_sum`/`sum_mul` argument
order `(s)(f)(a)` with `mul_sum : a * ∑ f = ∑ (a·f)`, and the
matrix-literal far-corner entry (`!![…;0,0,0,2]`-shaped) defeating
`rfl`-in-`fin_cases` and `norm_num`, the robust routes being an
entry-table lemma or a scalar-multiple route — and open-next-step →
none with the three optional items named), `proposals/README.md`
(the Medium row retired to the Delivered table; the progress paragraph
rewritten; the duplicate reversibility row — 2026-08-19 drift —
removed), scoreboard (both Direct rows prepended, the `lake build` row
extended, a new interpretation bullet), radar (axis 5 re-scored
**3.0 → 3.5** with the full re-score log entry; the weakest-axes
paragraph rewritten; QA count synced 1212/36), README (1212, the
proved list gains the closing mixing bound, module table, coverage
snapshot 3.0 → 3.5), SGT index map (Mixing section: program-complete
header + 4 rows + the entry-lemma note), backlog item 2 (program
complete), this plan, and the activity log. The worktree's unrelated
operator-side changes (`proposals/prove-subgaussian-tail-bound.md` +
its README row, untracked) remain preserved untouched, as do the
uncommitted-but-delivered Step-2/Phase A/Step-3-component-1 changes.

**Next milestone (open):** the Medium rows by leverage — **Relative
Entropy** (Gibbs' inequality and the entropy maximum from Mathlib's
proved strict-concavity machinery), **the subgaussian tail bound**
(Step 0 first), **Perron–Frobenius + directed operators** (Step 0
first per the convention-choice gate), the **Cheeger hard-direction
Step 0 survey** (known-hard), and **approximate spectral projection**
(Step 0 first). Reversibility Phase B and Fiedler Phase B still need
operator decisions.

---

**Mixing-time Step 3, component 1 of 2 — the geometric decay engine
(run 1, 2026-08-22; `proposals/mixing-time-bound.md` at its recorded open
next step, the top Medium row with the Active table holding no High rows,
executed as the sub-decomposition the proposal itself licenses for its
hardest step — the electrical program's own steps-4/5 precedent):
DELIVERED.**
Pure hard crust — **zero new axioms** (count stays 10; `#print axioms`
on all eight new public theorems reads only `propext,
Classical.choice, Quot.sound`).

**Scope decision recorded before any statement (the split the proposal
authorizes):** Step 3 = (1) the decay engine — conjugated matrix powers,
eigencomponent evolution, the Parseval-exact decay identity, and the
hypothesis-shaped ℓ²(π) contraction — plus (2) the χ² assembly — the
density-evolution bridge `h_t − 1 = Pᵗ(h₀ − 1)`, the kernel-orthogonality
derivation under connectivity, and the final
`χ²(t, x) ≤ (λ*)²ᵗ·((π x)⁻¹ − 1)`. This run delivered (1) only; (2) is a
later dedicated run.

**Statement-shape decisions, made before stating:**

1. **Value-based mode exclusion, not index-based.** The non-decaying mode
   is excluded by `eigvalOf (L_sym) i = 0` (the zero-eigenvalue modes of
   the *symmetrized* operator), not by excluding spectral index 0 — the
   index form is only correct when the kernel is one-dimensional, and the
   value form keeps the contraction true unconditionally (on a
   disconnected graph the mode hypothesis honestly fails for a
   one-component start, exactly as it should: there is no decay to
   stationarity).
2. **Hypothesis-shaped rate `r`**, not a `sup'`-packaged definition:
   `hrate : ∀ i, eigvalOf i ≠ 0 → |1 − eigvalOf i| ≤ r`. QA instantiates
   with hand-computed rates; packaging the sup is component 2's business
   when the walkEvals-side instantiation is needed.
3. **No sign hypothesis on `r`** — the rate hypothesis already forces
   `r ≥ 0` whenever it is non-vacuous (`|1 − μ| ≥ 0`), and the vacuous
   case collapses term-wise; carrying `0 ≤ r` would be decorative.
4. **The public headline is the π-form contraction**
   `∑ π ((Pᵗ g) i)² ≤ r^{2t} ∑ π (g i)²`, with the Euclidean
   √D-conjugated engine beneath it — the mixing-relevant shape, per the
   Step-2 scoping record's weighted-form-is-primary decision.

**Route (recorded before stating, from this run's pre-edit reading of the
delivered Step-1/Step-2 interfaces):** the engine never forms the
non-symmetric power `Pᵗ` in eigen-coordinates; it conjugates it —
`√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)` (one induction from the
similarity identity `√D P = (1 − L_sym) √D`), then reads coefficients
through the *generic* eigenaction at `1 − M`
(`v i ⬝ᵥ ((1−M) *ᵥ x) = (1 − μ i)(v i ⬝ᵥ x)`, composed from the shelf's
`dotProduct_eigvecOf_mulVec`), so each eigencoefficient evolves by
multiplication by `1 − μ i` per step. Parseval (`dotProduct_eigvecOf`)
then resolves `‖√D (Pᵗ g)‖² = ∑ ((1−μ i)ᵗ c i)²` exactly, and the
contraction is term-wise: kernel modes die by the mode hypothesis,
decaying modes by the rate hypothesis (`|1−μ| ≤ r` ⟹ even powers
dominate), with no case split on `r < 1` needed at all. Load-bearing on
`degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`,
`dotProduct_eigvecOf_mulVec`, `dotProduct_eigvecOf`, and
`eigvecOf_inner` — an error in any would surface here. The route landed
exactly as paved.

**Delivered:** one generic lemma in `GraphTheory.Spectral`
(`eigvecOf_dotProduct_one_sub_mulVec`, the `1 − M` eigenaction), the
conjugated-power layer in `GraphTheory.Normalized`
(`degreeSqrt_mul_walkTransitionMatrix_eq` + the headline
`degreeSqrt_mulVec_pow_walkTransitionMatrix`), and the engine in
`GraphTheory.Mixing` (eigencoordinate evolution, the Parseval-exact
identity, the norm-form contraction, the π-norm bridge
`sum_stationaryVec_smul_sq_eq`, and the π-form headline
`sum_stationaryVec_smul_sq_pow_walkTransitionMatrix_le`).

**QA** (`Mixing_QA.lean`, 33 → 67 declarations): the triangle K₃
(connected, non-bipartite — λ* = 1/2, *genuine* decay): every
eigen-fact derived **without naming Mathlib's classically chosen basis
vectors** (`tri_eigvalOf_cases`: every eigenvalue `0` or `3/2`, from the
summed eigen equation plus the unit-norm quadratic form;
`tri_kernel_const`: kernel = constants; `tri_exists_kernel_index`: by
trace `3` vs `9/2`); the mode and rate hypotheses derived from these;
the contraction instantiated at `t = 1, 2` on `h₀ − 1 = (2,−1,−1)` with
**exact** decay (`2 → 1/2 → 1/8` against bounds `(1/4)·2`, `(1/16)·2` —
equalities, pinned raw both sides). P₃ retained for the degenerate
λ* = 1 oscillation cross-check: the exact Parseval identity at `t = 2`
pins the basis-independent eigencomponent sum to `4`, tied by the π-norm
bridge to the already-pinned `χ²(2) = 1`. Negative witness: the mode
hypothesis dropped at `g = 1` — conclusion refuted (`1 ≤ 1/4`) *and* the
hypothesis provably unsatisfiable at the kernel index (coefficient
`3·c·√2 ≠ 0`, `c ≠ 0` by unit norm).

**Verification:** `lake env lean` on `Spectral.lean` (only its documented
pre-existing section-variable warnings), `Normalized.lean` (only the
documented pre-existing `congr 1` note), `Mixing.lean` and
`Mixing_QA.lean` — zero errors, zero warnings; `#print axioms` on the
eight public and thirteen headline QA theorems ✔ (three standard axioms
only); oleans built; **full `lake build` ✔ (2227 targets, "Build
completed successfully", detached, zero errors)**; `lint_axioms` (10,
unchanged), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1162/10/0**; `Mixing_QA` 33 → 67). The pre-edit Mathlib
survey recorded in the plan: `Matrix.dotProduct_sub`, `pow_le_pow_left₀`,
`sq_le_sq'`, `Matrix.mulVec_mulVec` all present; the generic `1 − M`
eigenaction absent (hence added to the center); one pin-specific
discovery logged here — this snapshot's `Finset.sum_sub` is named
`Finset.sum_sub_distrib`, and `linear_combination` takes the exact
coefficient expression (the `-hunit` sign mattered in QA). Radar axis 5
**held at 3.0** per the proposal's own gate (the mixing *statement* is
component 2's to deliver; hold + trigger logged); QA axis count synced
1162/36, held. Records updated: proposal (status header, full
component-1 delivery record, open-next-step rewritten to the numbered
component-2 gluing list), `proposals/README.md` (Medium row + progress
paragraph + Delivered row), scoreboard (counts, both Direct rows, `lake
build` row, interpretation bullet, definitions count), radar (new hold
entry), README (1162, proved list, module table), SGT index map (Mixing
section +5 rows, supporting-additions note), backlog item 2, this plan,
and the activity log. The worktree's unrelated operator-side changes
(`proposals/prove-subgaussian-tail-bound.md` + its README row, untracked)
remain preserved untouched, as do the uncommitted-but-delivered Step-2
and Phase A changes.

**Next milestone (open):** the Medium rows by leverage — **mixing-time
Step 3 component 2** (the χ² assembly: centered evolution,
connectivity kernel-orthogonality, the final
`χ²(t, x) ≤ (λ*)²ᵗ · ((π x)⁻¹ − 1)` — pure gluing on this delivery per
the proposal's numbered list; the program's closing statement),
**Relative Entropy**, **the subgaussian tail bound** (Step 0 first),
**Perron–Frobenius + directed operators** (Step 0 first per the
convention-choice gate), the **Cheeger hard-direction Step 0 survey**
(known-hard), and **approximate spectral projection** (Step 0 first).
Reversibility Phase B and Fiedler Phase B still need operator
decisions.

---

**Mixing-time Step 2 — the ℓ²-mixing proxy: definitions and evolution
interface (run 1, 2026-08-22; `proposals/mixing-time-bound.md` at its
recorded open next step, the top Medium row with the Active table
holding no High rows): DELIVERED.**
Pure hard crust — **zero new axioms** (count stays 10; `#print axioms`
on all fourteen new public theorems reads only `propext,
Classical.choice, Quot.sound`).

**The decide-and-record scoping gate, made first, before any statement
(exactly the record the proposal authorizes a run to make):**
(1) *The ℓ² statement alone satisfies this proposal's goal* — the
ℓ² → TV conversion stays scoped as a further, separate step, per the
proposal's own Step 4 framing ("own proposal-scale decision, not a
default continuation of this one"). (2) Within ℓ², the *weighted* form
is primary: the proxy is the χ² distance
`χ²(t, x) = ∑ i, (ν_t i − π i)² / π i` with `π = deg/vol`, because the
geometric decay bound of Step 3 is Parseval-exact in the π-weighted
inner product — the only inner product in which the transferred
eigenbasis of Step 1 is orthogonal (D-orthogonality; the plain
Euclidean inner product does not diagonalize the walk's adjoint
evolution). The unweighted Euclidean distance of the proposal's
original sketch is delivered as the corollary bridge
(`sum_sub_sq_walkDistribution_le`), not as the primary object.

**Delivered in the new `GraphTheory.Mixing`:** `stationaryVec`
(`deg/vol`) with positivity and sums-to-one, `walk_isStationary`
(the π-form composed from the proved degree form),
`walkDistribution` (`(Pᵀ)ᵗ *ᵥ δₓ`) with the zero/succ evolution
equations and mass conservation, `walkDensity` (`ν_t/π`) with the
**density evolution `walkDensity_succ`** (`h_{t+1} = P *ᵥ h_t` — the
first consumer of the Phase A detailed-balance interface
`walk_detailed_balance_measure`, load-bearing on it and on the `D⁻¹A`
orientation; the exact interface Step 3 consumes), and
`chiSquareDistance` with nonnegativity, the `= 0 ↔ ν_t = π`
characterization, the `t = 0` value `(π x)⁻¹ − 1` (Step 3's
normalization), the density-form equivalence, and the plain-ℓ²
corollary bridge. Junk-value discipline documented in the definition
docstrings; every theorem carries the positivity hypothesis that rules
the junk case out.

**QA** (`Mixing_QA.lean`, 33 declarations): the P₃ fixture —
`π = (1/4, 1/2, 1/4)` pinned from degrees and volume; stationarity
through the theorem *and* raw (`Pᵀ *ᵥ π = π`); the laws at `t = 0, 1, 2`
pinned (`δ₀`, `(0,1,0)`, `(1/2,0,1/2)`) with mass conservation
instantiated and recomputed from the pinned literal; the density
evolution instantiated and cross-checked raw (`P *ᵥ (4,0,0) = (0,2,0)`
— `P` itself, not its adjoint); `χ²(0) = 3` by *both* routes (theorem
and the raw termwise sum `9/4 + 1/2 + 1/4`); `χ²(2) = 1` raw — the
bipartite *oscillation* the Step-3 bound must reproduce on this
fixture (λ* = 1, no decay); the density-form equivalence instantiated
with its sum recomputed raw (`1`); the plain-ℓ² bridge instantiated at
`c = 1/2` with the unweighted sum pinned to `3/8 < 1/2` strict. Two
negative witnesses: the asymmetric `!![0,2;1,0]` (positive degrees, so
only `IsSymm` missing) where hypothesis-free stationarity is refuted
at the entry where symmetry provably fails (`1/3 ≠ 2/3`); and the zero
adjacency where `χ²(0, 0) = 0` (junk division) while the law is the
point mass `≠ π` — refuting the hypothesis-free vanishing
characterization.

**Verification:** `lake env lean` on `Mixing.lean` and
`Mixing_QA.lean` — zero errors, zero warnings each;
`#print axioms` on the fourteen public and twelve headline QA
theorems ✔ (three standard axioms only); oleans built; **full
`lake build` ✔ (2227 targets, "Build completed successfully",
detached)**; `lint_axioms` (10, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1128/10/0**;
`Mixing_QA` a new file row at 33). The pre-edit Mathlib survey
recorded in the proposal: no chi-square/total-variation/mixing-time
objects in the pin — the coverage map's recorded absence holds (no
correction needed). Records updated: proposal (status header, scoping
record + full Step-2 delivery record, open-next-step → Step 3 with the
consumed interfaces named), `proposals/README.md` (Medium row +
progress paragraph + Delivered row), scoreboard (both Direct rows
prepended, `lake build` row, lint dates, interpretation bullet), radar
(axis-5 evidence row + weakest-axes paragraph extended; **held at
3.0** per the proposal's own no-re-score-before-Step-3 gate, hold
logged; QA count synced 1128/36), README (1128, proved list, module
table, span list), SGT index map (new Mixing section, 17 rows), the
umbrella import, backlog item 2 (Step 2 delivered, Step 3 named as the
remaining piece), this plan, and the activity log. The worktree's
unrelated operator-side change (`proposals/prove-subgaussian-tail-bound.md`
+ its README row, uncommitted) remains preserved untouched.

**Next milestone (open):** the Medium rows by leverage — **mixing-time
Step 3** (the geometric decay bound `χ² ≤ (λ*)²ᵗ · normalization`, the
program's hardest single step, consuming exactly this delivery plus
the Step-1 transfer; may need sub-decomposition across runs),
**Relative Entropy**, **the subgaussian tail bound** (Step 0 first),
**Perron–Frobenius + directed operators** (Step 0 first per the
convention-choice gate), the **Cheeger hard-direction Step 0 survey**
(known-hard), and **approximate spectral projection** (Step 0 first).
Reversibility Phase B and Fiedler Phase B still need operator
decisions.

---

**Reversibility Phase A — detailed balance for the simple random walk on
weighted graphs (run 1, 2026-08-22; `proposals/reversibility-and-heat-
semigroup.md` Phase A, both of its steps in one run per its own operating
instruction — the top unblocked Medium row by the inner-dependency test:
the higher-ranked mixing-time Step 2's ℓ²(π) proxy geometry consumes
exactly this detailed-balance interface, so this is the strictly inner,
cheaper dependency delivered first): DELIVERED.**
Pure hard crust — **zero new axioms** (count stays 10; `#print axioms`
on all four new public theorems plus the new
`Normalized.walkTransitionMatrix_apply` reads only `propext,
Classical.choice, Quot.sound`) and **no new definitions** (the
proposal's own mandate).

**Delivered in `GraphTheory.Stationary`:** `walk_detailed_balance`
(degree-measure form `deg i * P i j = deg j * P j i`, both sides exactly
`A i j` — the degree weight cancels `walkTransitionMatrix`'s `D⁻¹` row
factor and `A.IsSymm` identifies the entries), `walk_detailed_balance_
measure` (the stationary-measure π-form at `π = deg/vol`, by
side-condition-free division — **no volume-positivity hypothesis
carried**, strictly more general than drafted; stated with the explicit
house form `(Finset.univ : Finset V)` after discovering that bare
`univ` auto-binds as a *local* arbitrary finset),
`diagonal_deg_mul_walkTransitionMatrix_isSymm` (reversibility *is*
symmetrizability: `D * P` symmetric — the self-adjointness interface the
mixing program's ℓ²(π) proxy consumes), and
`transitionMatrix_detailed_balance_uniform` (the Phase A Step-2 regular
case, *composed* from the already-proved `transitionMatrix_symmetric`
— the pre-edit survey's finding — rather than re-proved). Alongside in
`Normalized.lean`: the entry lemma `walkTransitionMatrix_apply`
(`P i j = (deg A i)⁻¹ * A i j`) and the correction of the stale "Named
gap (deferred)" similarity docstring (the 2026-08-22 transfer closed it).

**QA** (`Stationary_QA.lean`, 12 → 26 declarations): the proposal's two
prescribed witnesses. Positive — P₃ balance instantiated through the
theorems at every index pair and cross-checked by raw literal
arithmetic (degree form `1 = 1`; π-form `1/4 = 1/4` with `vol = 4`
pinned independently from the degrees; symmetrized off-diagonal entries
both `1` — equal degree-weighted mass in both directions; uniform form
instantiated at the edge). Negative — the asymmetric `!![0,2;1,0]` with
positive degrees `(2, 1)`: hypothesis-free balance *refuted*
(`2 ≠ 1`) with the symmetry hypothesis provably violated at the same
entry pair, so `hA` is load-bearing.

**Verification:** `lake env lean` on `Normalized.lean`,
`Stationary.lean`, `Stationary_QA.lean` — zero errors (Stationary's two
warnings are the documented pre-existing ones, verified identical in
HEAD via stash); `#print axioms` on all public and eight headline QA
theorems ✔ (three standard axioms only); oleans built; **full
`lake build` ✔ (2227 targets, "Build completed successfully",
detached)** — which compiles every QA module as a library target;
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1095/10/0**; `Stationary_QA` 12 → 26).
**Records repaired alongside:** the radar axis-5 *table row* and
"Weakest axes" paragraph, which the same day's earlier mixing-time
re-score had left stale at 2.5 with the closed gap still named — synced
to the recorded 3.0 state. Radar axis 5 **held at 3.0** for this
delivery (composed identity within the counted walk-operator family;
hold + triggers logged). Records updated: proposal (status header,
Phase A delivery record with the statement-shape notes, open-next-step
→ Phase B's operator gate only), `proposals/README.md` (Phase B-only
row + Delivered row + progress paragraph), scoreboard (both Direct rows
prepended, new interpretation bullet), radar (table row, weakest-axes,
narrative entry), README (1095, proved list), SGT index map (Stationary
section, 4 new rows + entry-lemma note), backlog item 6 (reversibility
half delivered), this plan, and the activity log. An unrelated
operator-side change in the worktree (the new
`proposals/prove-subgaussian-tail-bound.md` + its README row) was
preserved untouched and left uncommitted.

**Next milestone (open):** the Medium rows by leverage — **mixing-time
Step 2** (the ℓ²-mixing proxy; its decide-and-record scoping gate
first, now with this run's detailed-balance interface available to it),
**Relative Entropy**, **the subgaussian tail bound** (the 2026-08-22
operator-directed addition; Step 0 first), **Perron–Frobenius + directed
operators** (Step 0 first), the **Cheeger hard-direction Step 0 survey**
(known-hard), and **approximate spectral projection** (Step 0 first).
Reversibility Phase B and Fiedler Phase B still need operator
decisions.

---

**Mixing-time Step 1 — eigenpair transfer to the general walk matrix through
the proved similarity identity (run 1, 2026-08-22;
`proposals/mixing-time-bound.md` at its recorded open next step, the top
Medium row now that the Active table has no High rows): DELIVERED.**
Pure hard crust — **zero new axioms** (count stays 10; `#print axioms` on
all nine new public theorems reads only `propext, Classical.choice,
Quot.sound`). This closes `Normalized.lean`'s own named residual gap (the
walk form is not symmetric, so `evals` does not apply to it) and builds the
interface the proposal's Step 3 decay bound consumes.

**Delivered in `GraphTheory.Normalized`** (the mandatory Mathlib survey
found no general similar-matrices-share-eigenvalues interface in the pin —
no `IsSimilar`, no charpoly-conjugation invariance — so the direct
diagonal-case transfer was the route, exactly the proposal's anticipated
cheaper branch): `walkLaplacian_mulVec_degreeInvSqrt` /
`normalizedLaplacian_mulVec_degreeSqrt` (eigenpair transfer in **both
directions** at the same eigenvalue, by conjugating the eigenvector with
`1/√D`/`√D` — pure `mulVec` algebra, no characteristic polynomial, which
dissolves the module docstring's recorded charpoly obstruction),
`walkTransitionMatrix_mulVec_degreeInvSqrt` (the `(1 − μ)` transition
reflection), the eigenbasis instantiations
`walkLaplacian_mulVec_eigvecOf`/`walkTransitionMatrix_mulVec_eigvecOf`,
`degreeInvSqrt_mulVec_ne_zero` + `eigvecOf_ne_zero` (witness nonvanishing),
`walk_eigvec_expansion` (completeness of the transferred family — the
diagonalizability interface, from `eigvecOf_expansion_apply` + the
invertibility shuffle), and `walkEvals` +
`exists_eigenvector_walkTransitionMatrix_eq_walkEvals` (every transferred
spectrum entry certified a genuine eigenvalue of `P` with an explicit
nonzero conjugated-eigenvector witness).

**QA** (`Normalized_QA.lean`, 14 → 34 declarations): the P₃ fixture
(degrees 1, 2, 1) with hand eigenpairs `(1, √2, 1)`, `(1, 0, −1)`,
`(1, −√2, 1)` at eigenvalues 0, 1, 2 — each verified by raw computation,
transferred **through the theorems**, and cross-checked by raw arithmetic
on the conjugated vectors `(1,1,1)`, `(1,0,−1)`, `(1,−1,1)`; the backward
transfer fed from the raw walk eigenpair and pinned back to the hand
eigenvector; the `walkEvals` existential at every spectral index; the
spanning hand-solve reconstructing `(1,2,3)`; and the two shortcut guards
refuted in proved form (skipping the conjugation; forgetting `1 − μ`).
QA-infrastructure note recorded in the proposal: the `√(1+1)` vs `√2`
atom mismatch is bridged by a pinned `1 + 1 = 2` simp rewrite
(`path_one_add_one_QA`), reusable by future `√`-arithmetic QA on this
fixture.

**Verification:** `lake env lean` on the module and QA — zero errors, zero
new warnings (the module's only diagnostic is the pre-existing `congr 1`
note, identical in HEAD); `#print axioms` on the nine public and seven
headline QA theorems ✔ (three standard axioms only); oleans built; **full
`lake build` ✔ (2227 targets, "Build completed successfully", detached)**;
`lint_axioms`, `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1081/10/0**). Records updated: the scoreboard (both Direct
rows + the `lake build` row prepended, a new interpretation bullet), radar
(**axis 5 re-scored 2.5 → 3.0** — the axis's named walk-spectrum gap
closed, the proposal's proof-landed-and-QA-passed gate satisfied; QA axis
count synced 1081/35, held, logged), README (status table, the proved
list, the coverage snapshot's axis-5 row), the SGT index map (Normalized
transfer section, 9 rows), the backlog (item 2's residual marked closed
with the survey re-confirmation), the proposal (status header, full
delivery record, open-next-step → Step 2), `proposals/README.md` (Medium
row + progress paragraph), this plan, and the activity log.

**Next milestone (open):** the Medium rows by leverage — **mixing-time
Step 2** (the ℓ²-mixing proxy; its own decide-and-record scoping gate
first: ℓ² alone, or scope the TV conversion as a further step — a
scoping record a run may make), **Reversibility Phase A** (cheap, zero
new axioms), **Relative Entropy**, **Perron–Frobenius + directed
operators** (Step 0 first), the **Cheeger hard-direction Step 0 survey**
(known-hard), and **approximate spectral projection** (Step 0 first).
Fiedler Phase B still needs an operator decision.

---

**Davis–Kahan Step 1, component 2 of 2 — the Duhamel/FTC assembly, retiring
`davis_kahan_sin_theta` from axiom to proved theorem (run 1, 2026-08-21;
`proposals/discharge-perturbation-axioms.md` at its recorded open next step,
consuming the delivered component 1): DELIVERED — the Davis–Kahan target is
CLOSED (explicit axioms 11 → 10).**

The new public module
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/Duhamel.lean`
(~900 lines, zero new axioms — `#print axioms` on every public theorem
reads only `propext, Classical.choice, Quot.sound`): the heat-semigroup
layer transferred from the Step-0 spike (`heatApply` with
expansion/adjoint, Parseval damping, eigenaction, differentiability,
and the new `t = 0` eigenbasis-expansion identity), the sorted-spectrum
step `evals_succ_le_of_lt`, the projector coefficient filter
`dotProduct_eigvecOf_spectralProjector_mulVec`, the two
cluster-filtered decay bounds, the pairing (duality) norm reduction
`l2OpNorm_le_of_abs_dotProduct_le` (self-application route), the
headline Duhamel bound
`l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le`
(`‖(1 − Q) * P‖ ≤ ‖E‖ / (b − a)` — the scalar pairing
`⟨e^{-t(A+E)}z_y, e^{tA}z_x⟩` whose derivative is exactly
`−⟨e^{-t(A+E)}z_y, E e^{tA}z_x⟩` by the symmetry shuffle; FTC on
`[0,T]` with the explicit exponential majorant; the boundary term sent
to `T → ∞`), the rank layer (`rank_spectralProjector_eq_card_filter`,
the no-tie pin), and the `‖P − Q‖ ≤ 1` gap-metric endpoint.
`Perturbation/DavisKahan.lean`'s `axiom davis_kahan_sin_theta` became
`theorem` at the **unchanged statement**, by the recorded pre-edit
three-way tie case split (no-tie: equal ranks → component 1's identity
→ the Duhamel bound; either tie: separation + the proved
`weyl_additive_upper` force `δ ≤ ‖E‖` → the `≤ 1` endpoint finishes).

**Downstream (verified by `#print axioms`):** `davisKahanTwoPoint`
fully hard crust; `eventStreamProjectorDrift` conditional on
`matrix_azuma_hoeffding` alone.

**QA** (`DavisKahan_QA.lean`, 3 → 20 declarations): the retained
zero-perturbation instance plus the proposal-required **strict
non-vacuity witness** — `dkA = diag(0,2)` perturbed by
`dkE = [[0,3/4],[3/4,0]]`, both spectra and `‖dkE‖ = 3/4` pinned
independently (trace/determinant/sortedness + the proved bridge), the
eigenvector directions pinned from the eigen equations
(one-dimensional eigenspaces, no control over Mathlib's classical
eigenbasis needed), both projectors pinned to literals
(`Q = (1/10)!![9,−3;−3,1]`, `P = diag(1,0)`), the bound instance
`‖Q − P‖ ≤ 1/3`, and the difference's own pinned spectrum giving the
exact distance `1/√10 < 1/3` — strict, exercising the no-tie (Duhamel)
branch.

**Verification:** both new modules and the QA elaborate directly
(`lake env lean`, zero errors, zero warnings); oleans built;
`#print axioms` on the retired theorem, the derived consumers, and all
new QA headlines reads only the three standard axioms; **all 35 QA
modules batch-elaborated, zero errors (BATCH-DONE fail=0)**; **full
`lake build` ✔ (2227 targets, "Build completed successfully",
detached)**; `lint_axioms`, `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (**1061/10/0**). Records updated: the two
index files (`sources/davis_kahan_1970.md` retirement annotation; a new
Duhamel section + retirement note in `map/perturbation.md`), README
(10 axioms, 1061 QA, proved list, module table), architecture §12, the
scoreboard (counts, lint/build/QA/public rows, interpretation bullet),
radar (axis 7 re-scored **3.5 → 4.0** — the axis's first calculus-based
proof technique as a new capability family; axiom-minimization trend →
10; proved-depth and QA-count syncs; the re-score logged), the proposal
(status header, full Step-1 delivery record with the tie-case
discovery, open-next-step → the Cheeger hard-direction survey),
`proposals/README.md` (Medium row + progress paragraph), the umbrella
import, this plan, and the activity log.

**Next milestone (open):** the Medium rows by leverage — **mixing-time
Step 1** (eigenvalue transfer via the proved similarity identity),
**Reversibility Phase A** (cheap, zero new axioms), **Relative
Entropy**, **Perron–Frobenius + directed operators** (Step 0 first),
the **Cheeger hard-direction Step 0 survey** (known-hard working
assumption, now this proposal's only remaining target), and
**approximate spectral projection** (Step 0 first). Fiedler Phase B
still needs an operator decision.

---

**Leverage:** the largest single axiom retirement this proposal
contemplates — explicit axioms 11 → 10 — and the one whose downstream
effect is widest: `Derived.ProjectorDrift.davisKahanTwoPoint` would become
fully proved hard crust (its last axiom dependency shed) and
`eventStreamProjectorDrift` conditional on `matrix_azuma_hoeffding` alone.
Load-bearing on the delivered component 1 (`l2OpNorm_sub_eq_of_rank_eq`),
the spike-verified semigroup primitives (`wip/dk_spike.lean`), the proved
`weyl_additive_upper` + `l2OpNorm_eq_max_abs_evals` bridge, and the
center's eigenbasis layer — errors in any would surface here.

**Route (recorded before stating, from the Step-0 survey plus this run's
pre-edit reading of the exact axiom shape):** the scalar Duhamel pairing —
for `P = spectralProjector A a`, `Q = spectralProjector (A+E) c'`,
`u(t) = e^{-t(A+E)}((I−Q)y)` (damped eigenbasis expansion, spike's
`heatApply`), `w(t) = e^{tA}(Px)` (negative-parameter `heatApply`):
`d/dt ⟨u(t), w(t)⟩ = −⟨u(t), E w(t)⟩` (spike differentiability + eigenaction
+ the reducing commutation), FTC on `[0,T]` with the explicit exponential
majorant gives
`|⟨y, ((I−Q)P)x⟩| ≤ |g(T)| + ‖E‖(1−e^{−δ'T})/δ'` at `δ' = b − a`, and
`g(T) ≤ e^{−Tδ'}‖x‖‖y‖ → 0`, so the pairing norm bound is `‖E‖/δ' ≤ ‖E‖/δ`
by the separation hypothesis. The A-side decay needs only `λ ≤ a` on P's
range (definitional coefficient filter); the (A+E)-side decay needs the
sortedness step `evals ⟨k⟩ < μᵢ → evals ⟨k+1⟩ ≤ μᵢ` (b := `evals ⟨k+1⟩`).
**Tie handling found during this pre-edit pass (new decision, recorded
before stating):** `initialProjector` includes whole tied eigenspaces, so
under eigenvalue ties at a threshold the two projector ranks differ and
component 1's identity does not apply directly. Both tie cases collapse:
if either `evals hA ⟨k⟩ = evals hA ⟨k+1⟩` or `evals hAE ⟨k⟩ =
evals hAE ⟨k+1⟩`, the proved Weyl additive bound + separation force
`δ ≤ ‖E‖`, and the unconditional `‖P − Q‖ ≤ 1` (max decomposition +
`l2OpNorm_le_one_of_isSymm_idempotent` + submultiplicativity) finishes via
`‖P−Q‖ ≤ 1 ≤ ‖E‖/δ`. In the no-tie case both ranks are `k+1` (count
lemma) and the delivered identity applies. So the retirement is a
three-way case split, two of which need no Duhamel at all.

**Next action:** survey the exact Mathlib intervalIntegral/dotProduct
signatures on the pinned snapshot, then build the new
`Analysis/OperatorTheory/Perturbation/Duhamel.lean` (semigroup layer
transfer + sortedness step + decay bounds + FTC assembly), rewrite
`DavisKahan.lean`'s `axiom` to `theorem`, verify consumers, and extend
`DavisKahan_QA.lean` with the proposal-required strict non-vacuity
witness (rational 2×2 rotation fixture, projector pinned through the
eigen equations per the Band-QA technique).

---

**Davis–Kahan Step 1, component 1 of 2 — the equal-rank projector
identity as its own hard-crust delivery (run 1, 2026-08-21;
`proposals/discharge-perturbation-axioms.md` at its recorded open next
step, the authorized two-component split's first half): DELIVERED.**
`‖P − Q‖ = ‖(I−Q)P‖` for real symmetric idempotent matrices (orthogonal
projectors) of equal rank, in a new public module
`Analysis/OperatorTheory/Perturbation/ProjectionGap.lean` (~1570 lines),
zero new axioms — `#print axioms` on every public theorem reads only
`propext, Classical.choice, Quot.sound`. This was the component the
Step-0 survey rated "moderate-large, the least-predictable piece" —
REQUIRED for the constant-1 operator-norm Davis–Kahan statement.
**Component 2, the Duhamel/FTC assembly, is a separate, later, dedicated
run** — not started, per the proposal's one-step-per-run discipline.

**Leverage:** it is the enabling lemma of the largest remaining
axiom-retirement this proposal contemplates (11 explicit axioms → 10 at
Step-1 completion); it is load-bearing on the proved Courant–Fischer
engine's counting lemmas (`card_filter_eigvalOf_lt_evals_le`,
`succ_le_card_filter_eigvalOf_le`,
`finrank_span_eigvecOf_finset`,
`dotProduct_eigvecOf_eq_zero_of_mem_span`) and on Mathlib's
`Matrix.L2OpNorm` C*-layer (`l2_opNorm_conjTranspose_mul_self`,
`l2_opNorm_mul`) — an error in any of those would surface here.

**Route (recorded before stating, after a pre-edit shelf survey):**
no characteristic-polynomial/XY-YX machinery is needed — this pin's
Mathlib has no AB/BA charpoly lemma (surveyed), and the shelf's own
counting lemmas route everything: (A) the always-true layer
`‖P−Q‖ = max ‖(I−Q)P‖ ‖(I−P)Q‖` by the orthogonal decomposition
`(P−Q)x = (I−Q)Px ⊥ Q(I−P)x` plus the factorizations
`(I−Q)P = (I−Q)(P−Q)`, `Q(I−P) = Q(Q−P)`; (B) the equal-rank core
`‖(I−Q)P‖ = ‖(I−P)Q‖` via `‖(I−Q)P‖² = ‖P(I−Q)P‖` (C*-identity) `=
evals hSP last = 1 − τ` with `τ := evals h(PQP) ⟨n − rank P⟩`, where
the two inequality directions reduce to: PQP ⪰ τ·P on ran P (eigenbasis
expansion: eigvalOf ≥ τ on the nonzero spectrum by the strict-count
lemma, `span{vᵢ : μᵢ ≠ 0} = ran P` when rank PQP = rank P; else
τ = 0 by the same counting), and a witness at τ (the minimizing
eigenvector, or a `ran P ∩ ker Q` vector when τ = 0 — nonempty because
ker(QP) = ker(PQP) via the identity `x ⬝ᵥ (PQP*ᵥx) = ‖Q*(ᵥPx)‖²`);
τ symmetry `τ_P = τ_Q` from `evals hPQP = evals hQPQ` via the
eigenspace transfer `v ↦ QP*ᵥv` (injective at μ ≠ 0 since
`PQ*(ᵥQP*ᵥv) = μ•v`) plus per-μ basis-count = eigenspace-dimension
(`finrank_span_eigvecOf_finset`) plus equal zero-counts
(Mathlib `rank_eq_card_non_zero_eigs`, `rank_transpose`).

**Delivered QA** (`Scaffold/QA/Perturbation/ProjectionGap_QA.lean`,
37 declarations, 0 `sorry`): the 30°-rotation projector fixture realized
as the Pythagorean rotation (`P = diag(1,0)`, `Q` onto the line of
`(4/5, 3/5)`, `sin θ = 3/5`, kept rational throughout) — both projector
ranks pinned, the sandwich `PQP` and its spectrum pinned, `‖(I−Q)P‖ =
3/5` verified by two independent routes (the module's squared-residual
theorem and raw literal arithmetic through the proved operator-norm
bridge), `‖P − Q‖ = 3/5` from the difference's own pinned spectrum, and
the unequal-rank guard `P` vs `1` refuting the hypothesis-free form
(`‖P−1‖ = 1 ≠ 0 = ‖(1−1)P‖`).

**Verification:** `Scaffold.lean` now imports `ProjectionGap`; both the
core module and its QA file elaborate with zero errors and zero
warnings; `lint_axioms` (11, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (QA declarations
998 → 1035).

**Next milestone (open):** Davis–Kahan Step 1, component 2 — the
Duhamel/FTC assembly consuming this identity plus the spike-verified
semigroup primitives (`wip/dk_spike.lean`) — as a dedicated run, per the
proposal's one-step-per-run discipline. After that, `davis_kahan_sin_theta`
retires from axiom to proved theorem.

---

**Davis–Kahan Step 0 tractability survey (run 1, 2026-08-21;
`proposals/discharge-perturbation-axioms.md` — with no High rows left in
the Active priority table, the top Medium item by the recorded ranking):
DELIVERED — decisive positive-with-large-cost, the route named and
spike-verified, plus the citation mislocation the survey surfaced
repaired in all four files.** Step 1 (the retirement itself) was NOT
started — the survey's own cost estimate (600–1000 lines, two genuinely
new components) puts it beyond one run; it is now authorized as a
dedicated run per the proposal's contingency gate.

**Survey findings (paper read in full, arXiv:1405.0680):**

- **Citation mislocation, repaired.** The axiom's provenance note paired
  "Theorem 2" with "constant 1" — a pairing that does not exist in the
  paper. YWS's actual Theorem 2 is population-gap/Frobenius/constant-2
  (Weyl + Wielandt–Hoffman + a Kronecker Sylvester bound); the repo's
  mixed-gap operator-norm constant-1 statement is the paper's
  **Theorem 1** (classical Davis–Kahan restated, operator-norm variant
  noted there) at the bottom cluster, single-pair δ by sortedness —
  equivalence re-verified during the survey. The axiom statement itself
  is unchanged and its constant-1 tightness re-verified numerically at
  the 2×2 rotation family (sinθ ≈ 0.0985 vs bound ≈ 0.0990, attained
  asymptotically). Corrected: `DavisKahan.lean`'s docstring (with a
  dated correction note), `index/sources/davis_kahan_1970.md`,
  `index/map/perturbation.md`, `docs/2_ARCHITECTURE.md` §12.
- **Route map.** The entrywise eigenbasis-coordinate identity
  `(λ̂ᵢ − λⱼ)⟨vⱼ,ûᵢ⟩ = −⟨ûᵢ,Evⱼ⟩` over the cleanly side-separated
  pairing caps at Frobenius shape, constant √(k+1) — exactly YWS Thm 2's
  `d^{1/2}` numerator; it cannot discharge the exact statement.
  Constant-1 operator-norm needs the **Duhamel/exponential integral**
  `(I−Q)P = ∫₀^∞ e^{-tÃ}(I−Q)E e^{tA}P dt` (the mixed gap *is* side
  separation, giving `e^{-tδ}` decay; no `Matrix.exp` — the semigroups
  live at vector level as damped eigenbasis expansions), plus the
  **equal-rank projector identity** `‖P−Q‖ = ‖(I−Q)P‖` (principal
  angles; required for constant 1 since the reverse direction degrades
  through Weyl to `δ − 2‖E‖`; naive `(P−Q)²` decompositions were
  hand-checked and fail — a 2×2 counterexample to the tempting identity
  was worked out).
- **Spike (`wip/dk_spike.lean`, git-ignored): all five primitives
  PROVED, each `#print axioms`-clean (`propext, Classical.choice,
  Quot.sound` only)** — the vector-level heat semigroup `heatApply`,
  its expansion/adjoint workhorse, **Parseval damping**
  (`‖S_t x‖² = ∑ e^{-2tλᵢ}cᵢ²`), **eigenaction** (through the shelf's
  `mulVec_eigvecOf_sum_apply`), **differentiability in `t`** (this
  pin's `HasDerivAt.sum`/`HasDerivAt.exp` — imports
  `Analysis.Calculus.Deriv.Add` + `Analysis.SpecialFunctions.ExpDeriv`
  are not transitive through `GraphTheory.Spectral`), and the
  **reducing commutation** `spectralProjector M hM c * M =
  M * spectralProjector M hM c` (+ `mulVec` form). ~250 spike lines,
  essentially transferable.
- **Step-1 estimate: 600–1000 lines over 2–3 runs** — spike transfer,
  the equal-rank identity (moderate-large, least predictable), the FTC
  assembly (moderate — scalar `intervalIntegral` FTC + the `e^{-δt}`
  decay bound from cluster-filtered Parseval damping), cluster-filtered
  norm corollaries, QA.

**Verification:** `lake env lean` on the changed module
(`Perturbation/DavisKahan.lean` — docstring only, zero errors/zero
warnings), its closest QA consumer (`DavisKahan_QA.lean` — clean), and
the derived consumer (`Derived/ProjectorDrift.lean` — only the
documented pre-existing `hγ` warning); the spike elaborates end-to-end
with all three `#print axioms` reads clean; `lint_axioms` (**11**),
`check_citations`, `check_markdown_links` pass; scoreboard regeneration
idempotent (**998/11/0** — this run changed no Lean declarations, so
counts are the previous run's Step-4 state). Environment healthy at run
start (5387 Mathlib oleans; no fetch needed).

**Records updated:** proposal (Status header, the full Step-0 survey
record with all findings and estimates, per-axiom item 2 closed,
Open-next-step rewritten to the authorized Step 1), the axiom docstring
+ both index files + architecture §12 (the citation repair),
`proposals/README.md` (the Medium row and the progress paragraph — the
top next candidate is now Davis–Kahan Step 1 itself), scoreboard
(regenerated, idempotent), this plan, and the activity log.

**Next milestone (open):** **Davis–Kahan Step 1** — now authorized, as a
dedicated run (or the two-component split: the equal-rank projector
identity first as its own hard-crust delivery, then the Duhamel
assembly); or the other Medium rows by leverage (mixing-time Step 1;
Reversibility Phase A; Relative Entropy; Perron–Frobenius + directed
operators, Step 0 first; the Cheeger hard-direction survey, known-hard;
approximate spectral projection, Step 0 first; Fiedler Phase B still
needs an operator decision).

---

**Spectral Band Projectors, Step 4 — the Hilbert-projection
specialization (run 1, 2026-08-21; `proposals/spectral-band-projectors.md`,
the Active table's only High row, at its recorded open next step — the
program's last step): DELIVERED; the program is COMPLETE.** Pure hard
crust — **zero new axioms** (count stays 11; `#print axioms` on all
three new public theorems reads only `propext, Classical.choice,
Quot.sound`). The proposal's one-step-per-run rule held throughout the
program (Steps 1–3 on 2026-08-20, Step 4 on 2026-08-21).

**Pre-edit survey outcome (the proposal's mandatory pre-step):** the
pinned snapshot has the whole shelf — the identification lemma
`eq_orthogonalProjection_of_mem_of_inner_eq_zero`, the minimality
lemma `orthogonalProjection_minimal`,
`HasOrthogonalProjection.ofCompleteSpace` (resolving on
finite-dimensional EuclideanSpace), and the transport spine
(`EuclideanSpace.inner_piLp_equiv_symm` and
`Matrix.toEuclideanLin_piLp_equiv_symm`, both `rfl` — the resolvent
Step-0 precedent one notation-level cleaner, `toEuclideanLin` needing
no coercion). No obstruction; the proposal's stop-and-record clause
was not triggered.

**Delivered in `GraphTheory.Band`** (with the two Mathlib imports
`Analysis.InnerProductSpace.{Projection,PiL2}` added):

- `bandProjector_residual_dotProduct_eq_zero` — the engine:
  `(x − B *ᵥ x) ⬝ᵥ (B *ᵥ z) = 0`, consuming exactly the two Step-1
  facts (symmetry moves the band across the dot product; idempotence
  collapses `B *ᵥ (x − B *ᵥ x)` to `0`) — the section reduces to
  Step 1 plus Mathlib.
- `bandProjector_toEuclidean_apply_eq_orthogonalProjection` — the
  identification: `orthogonalProjection (range (toEuclideanLin B))
  (e x) = e (B *ᵥ x)` — the SGT center's first consumption of
  `Analysis/InnerProductSpace/Projection.lean`.
- `norm_sub_bandProjector_apply_le` — the closest-point property over
  the band's fixed space (equivalent to range membership by
  idempotence): from `orthogonalProjection_minimal` + the
  conditionally-complete `ciInf_le` (`iInf_le` does not apply over ℝ;
  `BddBelow` witnessed by `0`).

**Statement-shape decisions recorded before stating:** statements at
`EuclideanSpace ℝ V` — the bare `V → ℝ` default norm instance is the
sup norm, and a closest-point claim there would be silently
wrong-normed; the fixed-point hypothesis form over the
range-membership existential (equivalent by idempotence, no witness
juggling for consumers); the range form `LinearMap.range
(toEuclideanLin B)` over an eigenspace-span form (they coincide for an
idempotent self-adjoint band projector; the range form needs no
agreement theorem — a named residual in the proposal).

**QA** `SpectralGraph/Band_QA.lean` (+25 by the generator metric, 109
in file, 998 total): the band `(0,2] = diag(1,0)` pinned from the
pinned threshold projectors; the identification instantiated and
pinned to the packaged band image; the residual engine witnessed
through the theorem *and* by raw literal arithmetic; minimality
instantiated at three competitors — **attained** (signal-to-projection
distance exactly `4`), **strict over the zero signal** (`4 ≤ 5`, the
3-4-5 triangle), **generic over the whole range line**
(`4 ≤ √((3−t)²+16)`, both norms pinned through `‖e v‖² = v ⬝ᵥ v`) —
with `band_diag13_hilb_min_line_raw` reproducing the identical line
inequality from bare square-positivity (an independent hand-check the
transported theorem's claim must match); the **high band** also
instantiated (`3 ≤ 5`, not fixture-locked); and the **fixed-space
guard** — the hypothesis-free form refuted at the unfiltered signal
(distance `0 < 4`, the signal provably not fixed by the band), so the
fixed-point hypothesis is load-bearing.

**Verification:** `lake env lean` on `Band` and `Band_QA` — zero
errors, zero warnings (public module after two argument-shape fixes:
`LinearMap.mem_range` has no explicit arguments on this snapshot, and
`orthogonalProjection_minimal` takes its submodule implicitly with the
point explicit; plus the `ciInf_le`-for-ℝ substitution; QA after three
proof-shape fixes — the simp-closes-goal/norm_num-trap, the
dot-product `ring` residue, and a `rw`-scope fix replaced by `calc`);
`#print axioms` on the three public and nine headline QA theorems ✔
(three standard axioms only); oleans produced during iteration; **all
thirty-four QA modules batch-elaborated, zero errors (BATCH-DONE
fail=0 — one mid-batch restart at the 10-minute tool timeout, no state
damage)**; **full `lake build` ✔ (2186 targets, "Build completed
successfully", detached log + poll)**; `lint_axioms` (**11**),
`check_citations`, `check_markdown_links` pass; scoreboard
regeneration idempotent (**998/11/0**). Environment healthy at run
start (correct-path olean check: 5387 present; no fetch needed).

**Records updated:** module/QA/umbrella docstrings, scoreboard
(998/11/0, both Direct rows prepended with the Step-4 slice, the
`lake build` row extended, the Step-4 interpretation bullet, the
provenance note's run events), radar (**axis 2 re-scored 4.0 → 4.5** —
the capability dimension the two prior records explicitly reserved as
the trigger: a characterized closest-point/projection interface into
Mathlib's inner-product-space machinery, not another band-family
member; QA count synced 998/34 with the QA axis **held at 4.0** and
both decisions logged in the re-scoring log; the QA axis's evidence
row gains the Step-4 kinds), README (998/11; the proved list gains the
Hilbert-projection specialization; the coverage snapshot's spectral
linear algebra row synced 3.5 → 4.5 — it had been stale at 3.5 since
the Tikhonov re-score, now matching the radar), SGT index map (Band
section: program-complete header + 3 rows), proposal (status header
program complete, Step-4 delivery record with the survey outcome and
statement-shape decisions, open-next-step rewritten to none with the
named span-form residual), and `proposals/README.md` (the High row
removed from the Active table; Delivered row added; progress paragraph
rewritten — **the Active table now has no High rows; the next run
falls through to the Medium rows by leverage**).

**Next milestone (open):** with no High rows, the next run selects
among the Medium rows by leverage — the top candidates as ranked in
`proposals/README.md`'s progress paragraph: the **Davis–Kahan Step 0
survey** (`discharge-perturbation-axioms.md` — shrinking the mushy
center; tractability genuinely unknown), **mixing-time Step 1**
(eigenvalue transfer via the proved similarity identity),
**Reversibility Phase A** (cheap, zero new axioms, composes existing
lemmas), **Relative Entropy** (Gibbs' inequality from Mathlib's proved
strict-concavity machinery), **Perron–Frobenius + directed operators**
(scoped together, Step 0 first), and **approximate spectral
projection** (Step 0 first). Fiedler Phase B still needs an operator
decision.

---

**Spectral Band Projectors, Step 3 — completeness under a partition
(run 1, 2026-08-20; `proposals/spectral-band-projectors.md`, the
Active table's only remaining High row, at its recorded open next
step): DELIVERED.** Pure hard crust — **zero new axioms** (count stays
11; `#print axioms` on all four new public theorems reads only
`propext, Classical.choice, Quot.sound`). The proposal's
one-step-per-run rule was honored — Step 4 (the Hilbert projection
specialization) untouched.

**Route (as recorded before stating):** the algebraic engine is the
*unconditional* telescoping law, and it landed exactly as paved —
`Finset.sum_range_succ` induction with the residue closed by `abel`
(one snapshot surprise recorded: this Mathlib's `sum_range_succ`
appends the new term on the *right*, giving the natural order
`f 0 + f 1 + …`, and neither `Finset.sum_range_two` nor `Nat.cast_mono`
exists here). Completeness consumes exactly the two endpoint covering
hypotheses; monotonicity is deliberately *not* folded into the sum
identity (telescoping does not consume it — it would be decorative),
and is delivered as its own theorem where it is load-bearing.

**Delivered in `GraphTheory.Band`:**

- `sum_range_bandProjector_eq_sub` — the unconditional telescoping law
  `∑_{k<n} B(t_k, t_{k+1}) = P_{t_n} − P_{t_0}` for *any* threshold
  sequence, ordered or not (load-bearing on the band definition's
  exact difference shape: a sign-flipped or transposed definition
  would leave an uncancellable residue);
- `sum_range_bandProjector_eq_one` — **completeness under a
  partition**: a family whose start is strictly below every eigenvalue
  and whose end covers them all resolves the identity (both covering
  hypotheses load-bearing — refutable-on-omission in both directions);
- `bandProjector_mul_bandProjector_eq_zero_of_monotone` — distinct
  members of a **monotone** family compose to zero (`Monotone t`
  supplies exactly the disjointness `t (k+1) ≤ t m` Step 2 consumes);
  together with completeness, the identity resolves into mutually
  orthogonal band projectors — the partition character stated rather
  than assumed;
- `sum_range_bandProjector_mulVec_eq_self` — the consumer's form
  `∑ B_k *ᵥ x = x`, through the inlined `mulVec` analog of
  `Matrix.sum_mul` (a sum-interchange needing `Matrix.sum_apply`
  because `Finset.sum_apply` cannot see through the `Matrix.of`
  wrapper).

**QA** `SpectralGraph/Band_QA.lean` (+41 by the generator metric, 84 in
file, 973 total): the proposal's partition witness — the covering
two-band family `t k = 2k` summed to the identity **through the
theorem and from independently pinned band values**; a three-band
partition `t k = k` with an **empty middle band** and its top
threshold exactly touching the eigenvalue `3` (the closed right
endpoint); the **two endpoint guards** — a family starting at `2` and
a family truncated at `n = 1` each provably fails to sum to the
identity, with each violated covering hypothesis separately refuted
(the design note's "silently ignores modes" failure mode, witnessed in
both directions); the **non-monotone telescoping witness** (family
`4, 0, 4`: junk band `−1` cancelling covering band `1`, both sides
independently `0`); monotone-family orthogonality instantiated; and
the vector decomposition on `![7,−5]` by theorem and raw routes.

**Verification:** `lake env lean` on `Band` and `Band_QA` — zero
errors, zero warnings (public module first pass; QA after two
proof-shape fixes, one being the `rw`-closes-`3 ≤ 3`-by-itself linter
trap already documented at Step 2); `#print axioms` on the four public
and thirteen headline QA theorems ✔ (three standard axioms only);
oleans produced directly during iteration (the recorded fast `lean -o`
path); **all thirty-four QA modules batch-elaborated, zero errors
(BATCH-DONE fail=0)**; **full `lake build` ✔ (2186 targets,
"Build completed successfully", detached log + poll)**;
`lint_axioms` (**11**), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (**973/11/0**). Environment: an
olean-presence false alarm at run start (the check used the wrong
path — no `lean/` level in the layout; corrected check recorded in
the scoreboard's provenance note, with one redundant idempotent
re-fetch), and one `lake build` invocation killed at its tool timeout
during Mathlib trace replay left the olean set intact (verified by
count); the final build ran detached per the recorded procedure.

**Records updated:** module/QA/umbrella docstrings, scoreboard
(973/11/0, both Direct rows prepended with the Step-3 slice, the
`lake build` row extended, the Step-3 interpretation bullet, the
provenance note amended with the wrong-path check correction), radar
(axis 2 evidence extended with the completeness layer, **score held at
4.0** per protocol — same-family completion; Step 4, consuming
Mathlib's Hilbert projection machinery, stays the natural re-score
trigger; QA count synced 973/34 with the QA axis **held at 4.0**; both
holds logged), README (status table synced to 973/11; the proved list
gains partition completeness), SGT index map (Band section extended,
Steps 1–3; +4 rows), proposal (status header Step 3 DELIVERED,
delivery record with the route and the statement-shape decision,
open-next-step rewritten to Step 4), `proposals/README.md` (High row
note + Delivered row + progress paragraph — **Step 4 is now the top
of the Active table**).

**Next milestone (open):** the same proposal's **Step 4 — the
Hilbert-projection specialization** (the band projector's output is
the closest point in its range to the input, by instantiating
Mathlib's Hilbert projection theorem at the band's eigenspace; the
proposal's own mandatory pre-step is the signature survey of
`Analysis/InnerProductSpace/Projection.lean`, with the resolvent
Step-0 record's `toEuclideanCLM` transport spine as precedent — the
program's last step). Or the Medium rows (Fiedler Phase B — needs an
operator decision; mixing-time Step 1; Reversibility A and B; Relative
Entropy; Perron–Frobenius + directed operators; discharge-perturbation
— the Davis–Kahan Step 0 survey; approximate spectral projection).

---

**`spectral_persistence` removal (2026-08-20, operator-directed, interactive
session — not an `opencode-pursue` run): DELIVERED.** Editorial axiom
removal, not a proof-based retirement: the operator's stated criterion was
that the axiom is not well-established published math, distinct from
every prior retirement (all of which discharged a citation-backed axiom
by proof). Deleted `axiom spectral_persistence` from
`Scaffold/Mathlib/GraphTheory/Dynamics.lean` and its sole QA consumer
`persistence_zero_perturbation_QA` from `Scaffold/QA/SpectralGraph/Dynamics_QA.lean`;
fixed a dangling docstring reference in `Scaffold/Derived/ProjectorDrift.lean`.
`TimeVaryingGraph`/`laplacianSequence`/`IsEventDriven`/
`laplacianSequence_symmetric` are untouched (still consumed by
`Derived.EventStream`/`Derived.ProjectorDrift`, which already cover the
motivating persistence use without this axiom via the proved two-endpoint
chain). Explicit axiom count 12 → 11; QA declarations 917 → 916. Synced:
`index/map/spectral_graph.md`, `index/map/perturbation.md`,
`index/sources/davis_kahan_1970.md`, `docs/2_ARCHITECTURE.md`,
`docs/7_SGT_RADAR.md`, `README.md`, `docs/5_QA_SCOREBOARD.md` (regenerated
+ a new dated narrative bullet), `docs/6_SGT_BACKLOG.md` (appended, not
rewritten). `research/archive/` left untouched per `AGENTS.md`'s
archive-immutability rule — the earlier request in this session to also
scrub archive mentions was declined for that reason; this narrower
Lean-only removal was carried out instead.

**Verification:** `lake env lean` on the three touched modules — zero
errors (one pre-existing, unrelated unused-variable warning in
`ProjectorDrift.lean`, confirmed present before this change);
`scripts/generate_qa_scoreboard.py` regeneration reflects the new counts;
a full `lake build` was not run for this change (not requested, and the
three touched modules elaborate cleanly in isolation with no signature
changes to anything else imports).

---

**Spectral Band Projectors, Step 1 — the two-sided band projector (run 1,
2026-08-20; `proposals/spectral-band-projectors.md`, the Active table's
only remaining High row, at its recorded open next step "begin with
Step 1"): DELIVERED.** Pure hard crust — **zero new axioms** (count stays
12; `#print axioms` on all seven new public theorems reads only
`propext, Classical.choice, Quot.sound`).

**Pre-edit survey of `spectralProjector`'s lemma set (the proposal's
mandatory Step-1 check):** `spectralProjector_symmetric`,
`spectralProjector_idempotent`, `spectralProjector_eq_zero`,
`spectralProjector_eq_one` all exist and are proved — nothing to
reprove. **Route decision recorded before stating:** idempotence of the
*difference* `P_b − P_a` does not transfer from idempotence of each
factor (differences of idempotents are not idempotent in general); the
load-bearing missing piece is the **nestedness cross-law**
`P_{c₁} * P_{c₂} = P_{min c₁ c₂}`, proved entrywise by the same
orthonormal expansion as the existing idempotence proof with the two
threshold filters intersecting (the flipped order by transposing
symmetry). Delivered as the new master lemma
`spectralProjector_mul_spectralProjector` plus the two ordered
consumption shapes `_of_le` / `_of_le'`; the existing
`spectralProjector_idempotent` is **re-derived from the master at
unchanged statement** (its 50-line entrywise proof replaced by one
rewrite). Alongside it, the eigenvector-*action* layer: the complete
`spectralProjector_mulVec_eigvecOf`
(`P_c *ᵥ vᵢ = if λᵢ ≤ c then vᵢ else 0`) with its `_self` / `_of_lt`
specializations — the bandpass consumer interface.

**Delivered in the new `GraphTheory.Band`** (parameterized by interval
`(a, b]` per the design note, not by index; the definition is total
with the `a > b` negated-band junk documented rather than type-guarded;
every property carries `a ≤ b` exactly where needed): `bandProjector`,
`bandProjector_symmetric`, `bandProjector_idempotent` (through the
cross-law), the action interface
`bandProjector_mulVec_eigvecOf_self` / `_eq_zero_left` /
`_eq_zero_right`, the design note's named special case
`bandProjector_eq_spectralProjector_of_lt` (`spectralProjector` kept,
not re-derived), and the covering band `bandProjector_eq_one` (the
two-band instance of Step 3's completeness statement).

**QA** `SpectralGraph/Band_QA.lean` (27 declarations by the generator
metric, 917 total): the diagonal fixture `!![1,0;0,3]` — chosen over
the dense `!![2,1;1,2]` because one-dimensional eigenspaces make the
eigenvector *directions* computable from the eigen equations
(`λ = 1 ⇒ v = ![±1,0]`, sign-independent outer products, so no control
over Mathlib's classical choice is needed) — with the spectrum `{1,3}`
pinned from trace + determinant independent of the machinery under
test; the projector at any threshold in `[1,3)` pinned to the
hand-computed outer product `e₀e₀ᵀ = !![1,0;0,0]` (the proposal's
positive witness); band values computed independently (`B(−1,2] =
diag(1,0)`, `B(2,4] = diag(0,1)`, `B(−1,4] = 1`, and the
between-eigenvalues band `B(3/2,5/2] = 0` — the gapped-definition
guard); idempotence both through the theorem and by raw literal
multiplication; the cross-law instantiated numerically in both orders;
and mode selection witnessed in both directions — the excluded mode
**annihilated and provably not fixed** (`B(2,4] *ᵥ v₁ = 0 ≠ v₁` with
`v₁ ≠ 0` from unit norm), the strictly-interior mode (`λ = 3 ∈ (2,4]`)
fixed, the low-band mode fixed (theorem) and recomputed by raw
arithmetic.

**Verification:** `lake env lean` on `GraphTheory.Spectral`,
`GraphTheory.Band`, and `SpectralGraph/Band_QA` — zero errors, zero
warnings on the two new modules, `Spectral`'s only diagnostics the
documented pre-existing section-variable warnings; oleans produced
directly during iteration; `#print axioms` on the seven public and nine
headline QA theorems ✔ (three standard axioms only); **all thirty-four
QA modules batch-elaborated, zero errors**; the full `lake build`
detached from the tool timeout (log + poll) — see the terminal activity
entry for the final count; `lint_axioms` (**12**), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**917/12/0**; `Band_QA` a new file row at 27).

**Records updated:** module docstrings (Band + the Spectral additions),
umbrella (`Scaffold.lean` import + docstring), scoreboard (917/12/0,
the QA-module and public-module verification rows prepended with the
Band slice, the Step-1 interpretation bullet, the stale QA-declaration
count note fixed), radar (subject axis 2 evidence extended with the
band family and the QA axis count synced 917/34, **both held** per
protocol — the band projector is a second member of the
constructed-operator-family capability counted at the Tikhonov
re-score; Steps 2–4 are the natural re-score triggers; holds logged),
README (917; the proved list gains the band projectors), SGT index map
(new Band section, 8 rows; the Spectral section's projector-algebra
paragraph extended with the product-and-action layer; module list
updated), proposal (status header, Step-1 delivery record with the
route finding and the survey outcome, open-next-step rewritten to
Step 2), and `proposals/README.md` (High row note + Delivered row +
progress paragraph).

**Next milestone (open):** the same proposal's **Step 2 — orthogonality
of disjoint bands** (`a ≤ b ≤ c ≤ d`: the two band projectors compose
to zero; the route is paved — the cross-law's ordered forms expand the
product to `P_{min b d} − P_{min b c} − P_{min a d} + P_{min a c}`,
which collapses under the ordering), then Step 3 (partition
completeness) and Step 4 (the Hilbert projection specialization —
survey `Analysis/InnerProductSpace/Projection.lean` signatures first).
Or the Medium rows (Fiedler Phase B — needs an operator decision;
mixing-time Step 1; Reversibility A and B; Relative Entropy;
Perron–Frobenius + directed operators; discharge-perturbation — the
Davis–Kahan Step 0 survey; approximate spectral projection).

**Tikhonov Regularization in the Laplacian Eigenbasis (run 1,
2026-08-20; `proposals/tikhonov-shrinkage-filter.md`, the Active
table's top High row): DELIVERED — all three build steps in one run**
(the proposal's own "may cover more than one if the first lands
cleanly" clause). Pure hard crust — **zero new axioms** (count stays
12; `#print axioms` on all 18 public theorems reads only `propext,
Classical.choice, Quot.sound`).

**Definition-route decision (recorded before stating, per the standing
rule):** the minimizer is **defined directly by the eigenbasis
formula** `x* = ∑_k (π/(λ_k+π)) (v_k ⬝ᵥ y) • v_k`, not extracted by
`Classical.choice` from strict convexity — every interface theorem
(coefficient identity, normal equation, minimality) becomes a
computation and uniqueness a corollary of the strict-convexity
decomposition. A Mathlib convexity-API survey proved unnecessary on
this route (nothing outside the eigenbasis machinery is consumed —
the proposal's own cost case).

**Delivered in the new `GraphTheory.Tikhonov`:**

- **Step 2 first (the identity layer):** the closed-form
  eigencoefficient identity `tikhonovMinimizer_dotProduct_eigvecOf`
  (hypothesis-free — pure orthonormality), proved through a *generic*
  spectral-filter workhorse `dotProduct_eigvecOf_filter` (any filter
  function `g`; any graph-signal-processing consumer can reuse it),
  plus the expansion-injectivity `ext_of_dotProduct_eigvecOf_eq` and
  `eigvalOf_laplacian_nonneg`.
- **The normal equation both ways:** `tikhonovMinimizer_add_smul_one_mulVec`
  (`(L + π•1) *ᵥ x* = π • y`) and the **converse characterization**
  `eq_tikhonovMinimizer_of_add_smul_one_mulVec` — any solution of the
  normal equation *is* the minimizer. This is the interface that lets
  QA pin the spectral construction against a hand-solved linear
  system.
- **Step 1:** the objective `tikhonovObjective`, the
  **strict-convexity decomposition** `tikhonovObjective_sub_minimizer`
  (`obj(x) − obj(x*) = ∑_k (1 + λ_k/π)(d_k − d*_k)²`, positive
  weights by PSD + `π > 0`), and its two corollaries
  `tikhonovObjective_minimizer_le` (minimality) and
  `eq_of_tikhonovObjective_eq_minimizer` (vector-equality uniqueness).
- **Step 3:** the shrinkage-factor arithmetic layer
  (`tikhonovShrinkage` with `pos`, `ne_zero`, `le_one`, `lt_one`,
  `eq_one_iff`, strict antitonicity), mean preservation
  `sum_tikhonovMinimizer_eq_sum` (symmetry + `π ≠ 0` only — each
  component's mean is preserved on disconnected graphs),
  `tikhonovMinimizer_eigvecOf`, and the not-a-projection theorem
  `tikhonovMinimizer_ne_apply_self_of_eigvalOf_pos` (idempotence
  failure `T(T v) ≠ T v` at any positive-eigenvalue eigenvector; the
  sketch's nonnegativity hypothesis found unnecessary and deleted).
- **Two recorded statement-shape deviations from the proposal's
  Step 3:** (1) the claim "never exactly 1" is *false at λ = 0* — the
  factor is exactly `1` there, the kernel mode passes through
  untouched, and that **is** mean preservation; the delivered
  statements are `0 < factor`, `factor ≤ 1`, `factor < 1 ↔ 0 < λ`,
  `factor = 1 ↔ λ = 0`, strict antitonicity. (2) "not a projection"
  is delivered as a theorem (idempotence failure), not a docstring
  note.

**QA** `SpectralGraph/Tikhonov_QA.lean` (+30 by the generator metric;
`K₂`, signal `![1,0]`, `π = 1`): the minimizer **pinned through the
normal equation** — candidate `![2/3,1/3]` verified by hand (entrywise
Gaussian elimination, independent of the module) and promoted by the
converse characterization, so the spectral-theorem construction and a
hand-solved 2×2 system independently meet at the same vector; the
objective pinned exactly (`obj(x*) = 1/3` against `obj(y) = obj(0) =
1`, minimality instantiated, strict improvement certified); the
spectrum pinned (trace `2`, det `0`, PSD ⇒ eigenvalues ∈ {0,2}) making
the shrinkage story exact (factors `1` and `1/3`, ordering,
`1/3 ∈ Ioo 0 1`); **not-a-projection numerically** (`T(T y) =
![5/9,4/9] ≠ ![6/9,3/9] = T y` via a second hand-solved system);
mean preservation instantiated twice; and the **`hπ` guard
refuted-on-omission** (at `π = 0` the minimizer is the zero vector and
the hypothesis-free minimality would read `1 ≤ 0`). Named residual:
`tikhonovMinimizer_eigvecOf` not numerically instantiated (`eigvecOf`
entries are not kernel-computable; covered transitively by the two
normal-equation pins).

**Verification:** `lake env lean` on the public module and its QA —
zero errors, zero warnings; `#print axioms` on all 18 public and 14
headline QA theorems ✔ (three standard axioms only); oleans produced
directly during iteration; **all thirty-three QA modules
batch-elaborated, zero errors** (only the documented pre-existing
section-variable warnings in untouched modules); **full `lake build` ✔
(2185 targets, "Build completed successfully" — run detached from the
tool timeout after one invocation was killed at its tool timeout
mid-replay, the recorded hazard; the Mathlib oleans survived that
kill)**; `lint_axioms` (**12**), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**890/12/0**; `Tikhonov_QA` a new file row at 30).

**Records updated:** module/QA/umbrella docstrings, scoreboard
(890/12/0, the `lake build` row extended with the Tikhonov module and
the detached-build operational note, both Direct-rows prepended with
the Tikhonov slice, new milestone interpretation bullet, provenance
note), radar (subject axis 2 re-scored **3.5 → 4.0** — the axis's
first *constructed application-facing operator family*, the EML
re-score's precedent class; QA count synced 890/33 with the QA axis
**held at 4.0**; both logged in the re-scoring log), README (890;
proved list gains the Tikhonov family), SGT index map (new Tikhonov
section, 18 rows; module list updated), proposal (status header
DELIVERED + delivery record with both deviations + named residuals +
open-next-step none), and `proposals/README.md` (the High row moved to
Delivered; **Spectral Band Projectors is now the top High row**).

**Next milestone (open):** the Active table's remaining High row —
**Spectral Band Projectors** (`spectral-band-projectors.md`, no gate:
the two-sided band as the difference of two `spectralProjector`
calls); or the Medium rows (Fiedler Phase B — needs an operator
decision; mixing-time Step 1; Reversibility A and B; Relative
Entropy; Perron–Frobenius + directed operators; discharge-perturbation
— Davis–Kahan Step 0 survey; approximate spectral projection).

**Discharge the Weyl perturbation axiom (run 1, 2026-08-20; operator
direction: `proposals/discharge-perturbation-axioms.md`, `weyl_inequality`
only): DELIVERED.** Step 0's additive-bound spike returned a decisive
**positive** (recorded in the proposal before any module edit): the
additive window is *not* a free corollary of the norm bridge — it needs
both Courant–Fischer witness directions plus **both** Rayleigh
domination bounds, the bottom half (`evals_first_mul_dotProduct_le_quadForm`)
newly added to `GraphTheory.Spectral` as the mirror of the EML step's
`quadForm_le_evals_last` — but alongside them it is cheap (~120 lines).
Step 1 then executed per the direction: **`weyl_inequality` retired from
admitted axiom to proved theorem at the unchanged name, hypotheses, and
conclusion** (explicit axioms **13 → 12**; `#print axioms` reads only
`propext, Classical.choice, Quot.sound`). `davis_kahan_sin_theta` and
`cheeger_lower_bound` untouched, per the direction and the proposal's
own tractability ranking.

**Delivered in `Analysis.OperatorTheory.Perturbation.Weyl`:**

- `weyl_additive_upper` — `λᵢ(A+E) ≤ λᵢ(A) + λₙ(E)` (the witness
  subspace for `A` exhibited as a member of the competitor set defining
  `λᵢ(A+E)` through `evals_min_max`; `R_{A+E} = R_A + R_E` split by the
  local `quadForm_add'` copy, `R_E ≤ λₙ(E)` by `quadForm_le_evals_last`).
- `weyl_additive_lower` — `λᵢ(A) + λ₁(E) ≤ λᵢ(A+E)` (the competitor
  direction for `A` inside the `(i+1)`-dimensional witness subspace for
  `A+E`; the competitor vector's `R_A = R_{A+E} − R_E ≤ λᵢ(A+E) −
  λ₁(E)` by the new bottom domination).
- `theorem weyl_inequality` — the composed retirement (window →
  `l2OpNorm_eq_max_abs_evals` bridge; bridge's `1 ≤ card V` covered by
  vacuity at `card V = 0`).
- `spectral_gap_stability` — unchanged code, now fully hard crust.

**Downstream effect (verified by `#print axioms`):**
`davisKahanTwoPoint` conditional on `davis_kahan_sin_theta` alone;
`eventStreamProjectorDrift` on `davis_kahan_sin_theta` +
`matrix_azuma_hoeffding` — both shed the `weyl_inequality` dependency
without code changes.

**QA** `Perturbation/Weyl_QA.lean` (+14 by the generator metric, 18 in
file): the nonzero fixture `A = E = !![2,1;1,2]` with both spectra
pinned independently (trace/determinant/sortedness: `[1,3]`, `[2,6]`)
and `‖E‖ = 3` through the proved bridge — the bound instantiated at
both indices, **attained exactly** at the top (`|6−3| = 3 = ‖E‖`),
**strict** at the bottom (`1 < 3` — the proposal's required
non-vacuity witness), both additive bounds instantiated at both indices
with endpoint attainment, and the **window-endpoint guard**: the upper
additive bound with `λ₁(E)` in place of `λₙ(E)` refuted (`6 ≤ 4` is
false), so the window's endpoints are load-bearing and not
interchangeable. All nine QA theorems: three standard axioms only.

**Verification:** `lake env lean` on both changed public modules
(`GraphTheory.Spectral` + `Perturbation.Weyl`) and the QA module —
zero errors, zero warnings; oleans produced directly during iteration;
`#print axioms` on the four public theorems, nine QA theorems, and both
derived consumers ✔; **all thirty-two QA modules batch-elaborated, zero
errors**; **full `lake build` ✔ (2184 targets, "Build completed
successfully")**; `lint_axioms` (**12**), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**860/12/0**; `Weyl_QA` 4 → 18 by the generator metric). Environment
healthy at run start (5387 Mathlib oleans present; no cache fetch
needed).

**Records updated:** module/QA/derived docstrings (`ProjectorDrift`'s
dependency-status notes), scoreboard (860/12/0, verification rows
extended, Weyl-retirement interpretation bullet, derived-layer
provenance), radar (axes 2/7, proved-depth, downstream-reuse evidence
extended with scores **held** per protocol — assurance tracked through
the shrinking axiom count instead; QA count 860/32 with the holds
logged), README (860/12; Weyl moved to the proved list),
Mathlib coverage map (perturbation row: Weyl proved locally),
perturbation index map (Weyl section all-proved, 3 new rows),
probability index map (derived-chain dependency note), Weyl source
index (retirement annotation), proposal (Step-0 record + Step-1
delivery + status header + open-next-step), and
`proposals/README.md` (the Medium row's note rewritten).

**Next milestone (open):** back to the Active table's two ungated High
rows — **Tikhonov Regularization** (`tikhonov-shrinkage-filter.md`, a
corollary of the proved eigenbasis expansion) and **Spectral Band
Projectors** (`spectral-band-projectors.md`, the difference of two
`spectralProjector` calls) — or, on this proposal's track, the
**Davis–Kahan Step 0 survey** (its tractability is still genuinely
unknown even with the now-richer shelf). The other Medium rows (Fiedler
Phase B — needs an operator decision; mixing-time Step 1; Reversibility
A and B; Relative Entropy; Perron–Frobenius + directed operators;
approximate spectral projection) stay queued.

**Resolvent Calculus for PSD Matrices, Step 3 — injectivity (run 1,
2026-08-20): DELIVERED; the program is COMPLETE.** The Active
priority table's top High item (`proposals/resolvent-calculus-psd.md`)
at its recorded open next step — the final step, the proposal's item 5.
Pure hard crust — **zero new axioms** (count stays 13; `#print axioms`
on all three new public theorems reads only `propext,
Classical.choice, Quot.sound`).

**Delivered** in `Analysis.OperatorTheory.Resolvent`, exactly the
proposal's recorded route (contrapose the Step-1 resolvent identity:
equal resolvents collapse the identity's left side to `0`, so
`(A+1)⁻¹ * (B − A) * (B+1)⁻¹ = 0`; multiplying through by `A + 1` on
the left and `B + 1` on the right cancels both invertible outer
factors, leaving `B − A = 0`):

- `eq_of_inv_add_one_eq_inv_add_one` — the core algebraic form: equal
  resolvents of `+1`-invertible matrices force equal matrices. The two
  determinant hypotheses are exactly what the cancellation consumes
  (load-bearing — the QA guard refutes the hypothesis-free form).
- `resolvent_map_injective_of_quadForm_nonneg` — the proposal's item-5
  shape: `A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹` on quadForm-nonneg matrices (the
  determinant hypotheses supplied by Step 1's
  `isUnit_det_add_one_of_quadForm_nonneg`).
- `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg` — the packaged
  iff: resolvent equality as a *certificate* of matrix equality, for
  contrapositive consumers.

Load-bearing on Step 1 throughout — the factoring *is*
`resolvent_identity_sub`.

**QA** `OperatorTheory/Resolvent_QA.lean` (+19 declarations by the
scoreboard metric, 94 in file): the injectivity instantiated at **two
distinct PSD pairs** — `lap2` vs `0`, and the less degenerate `lap2`
vs `mat2` (neither zero; `mat2`'s PSD proved from the sum-of-squares
identity `xᵀ(mat2)x = (x₀+x₁)² + x₀² + x₁²`) — with both resolvents
independently pinned by left-inverse witnesses (`(mat2+1)⁻¹ =
(1/8)!![3,−1;−1,3]`, a new fixture), distinctness verified by entries
(`1/3 ≠ 0`, `2/3 ≠ 3/8`), bridge lemmas rewriting the theorem's
output to exactly those numeric facts, and the packaged iff consumed
contrapositively; plus the **invertibility guard** — the
hypothesis-free implication "equal resolvents → equal matrices"
**refuted** at `A = −1` vs `B = −1 + E` (`E` nilpotent, `B + 1 =
!![0,1;0,0]`, determinant `0` by a zero row): distinct matrices whose
`+1` shifts are both singular, so both resolvents are the junk inverse
`0` — equal while the matrices differ; the core theorem's determinant
hypotheses are load-bearing, not decorative.

**Verification:** `lake env lean` on the changed public module and its
QA module — zero errors, zero warnings; `#print axioms` on the three
new public theorems and eleven new QA theorems ✔ (three standard
axioms only); oleans produced directly during iteration; **all
thirty-two QA modules batch-elaborated, zero errors** (the only
diagnostics are the eight documented pre-existing section-variable
warnings in untouched modules); **full `lake build` ✔ (2184 targets,
"Build completed successfully")**; `lint_axioms` (13),
`check_citations`, `check_markdown_links` pass; scoreboard
regeneration idempotent (**846/13/0**; `Resolvent_QA` 75 → 94 by the
generator metric). Environment: the pruned-oleans state recurred at
run start; the recorded interpreted cache fetch restored the oleans.
Two mid-run operational events recorded in the scoreboard's
provenance note: `lake build` invocations interrupted at their tool
timeouts left the Mathlib olean dir wiped mid-replay (a re-fetch
restored it, and the final *uninterrupted* full build replayed the
trace residue and passed), and a macOS case-insensitivity trap was
diagnosed (creating `.lake/build/lib/lean/` in this workspace shadows
the toolchain's core `Lean/` tree and breaks all elaboration; this
repo's layout is `.lake/build/lib/Scaffold/...` directly).

**Records updated:** module/QA docstrings, scoreboard (846/13/0, the
QA-module and public-module verification rows extended, Step-3
interpretation bullet, provenance note), radar (axis 2, proved-depth,
and QA axis evidence extended with scores **held** — program
completion within counted interfaces, not a new capability family;
QA count 846/32; the holds logged in the re-scoring log), README
(846; the proved list gains the resolvent-map injectivity),
perturbation index map (3 new Resolvent rows; Deferred Work loses the
injectivity item), proposal Step-3 delivery record + status header
(program complete) + open-next-step (none; named residuals), and
`proposals/README.md` (the High row moved to Delivered; progress note
rewritten — **Tikhonov Regularization is now the top High row**).

**Next milestone (open):** the Active table's remaining High rows —
**Tikhonov Regularization** (`tikhonov-shrinkage-filter.md`, no gate:
a corollary of the proved eigenbasis expansion) and **Spectral Band
Projectors** (`spectral-band-projectors.md`, no gate: the two-sided
band as the difference of two `spectralProjector` calls). The Medium
rows (Fiedler Phase B — needs an operator decision; mixing-time Step
1; Reversibility A and B; Relative Entropy; Perron–Frobenius +
directed operators; discharge-perturbation; approximate spectral
projection) stay queued.

**Resolvent Calculus for PSD Matrices, Step 2 — the norm and Lipschitz
bounds (run 1, 2026-08-19): DELIVERED.** The Active priority table's
top High item (`proposals/resolvent-calculus-psd.md`), at the step its
Step-1 delivery record and the proposal's Open-next-step section both
named — pure hard crust, **zero new axioms** (count stays 13;
`#print axioms` on all three new public theorems reads only `propext,
Classical.choice, Quot.sound`). Step 3 (injectivity) was NOT started
(the proposal's one-step-per-run rule).

**Delivered** in `Analysis.OperatorTheory.Resolvent`, the proposal's
items 2 and 4, by the **recorded route deviation** (the proposal
sketched "the delivered bridge plus the shifted/inverted eigenvalue
transfer"; the *energy route* is strictly stronger and cheaper): for
`y = (M + t•1)⁻¹ *ᵥ x`, the quadratic-form hypothesis gives
`t‖y‖² ≤ quadForm M y + t‖y‖² = y ⬝ᵥ x ≤ ‖y‖‖x‖` (dot-product
Cauchy–Schwarz, transported to `EuclideanSpace` inner products through
the bridge's own `opNorm_le_bound`/`cstar_norm_def` spine), packaged
exactly as Step 0's upper direction was:

- `l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg` — the
  **general-`t`** bound `‖(M + t•1)⁻¹‖ ≤ t⁻¹` with **no symmetry
  hypothesis** (the same strengthening style as Step 1's invertibility
  theorem; only the quadratic form at the resolvent's own argument is
  evaluated). Bonus strengthening recorded: the underlying energy
  inequality `t • (y ⬝ᵥ y) ≤ y ⬝ᵥ x` holds for *any* `t`
  (positivity enters only at the division step).
- `l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg` — the `t = 1`
  instance, the proposal's item 2 (`‖(A+1)⁻¹‖ ≤ 1`).
- `l2OpNorm_resolvent_sub_le_of_quadForm_nonneg` — the proposal's item
  4, the **Lipschitz bound** `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖`: the
  Step-1 resolvent identity, the scoped `NormedRing`
  submultiplicativity (`norm_mul_le` — resolving under
  `Matrix.L2OpNorm`, the instance Step 0 verified), and the norm bound
  on both factors — **load-bearing on Step 1 throughout** (both
  determinant hypotheses supplied by the Step-1 invertibility theorem;
  the factoring *is* `resolvent_identity_sub`).

The sorted-eigenvalue transfer for shifted/inverted matrices is
thereby not needed by this step and remains a named residual for a
consumer that genuinely needs eigenvalue pins of transformed matrices
(the mixing-time program's similarity transfer is the named such
consumer).

**QA** `OperatorTheory/Resolvent_QA.lean` (+45 declarations by the
scoreboard metric, 75 in file) — the proposal's three QA items plus
tightness: the norm bound **attained with route agreement**
(`‖(L(K₂)+1)⁻¹‖ = 1` exactly — the theorem's energy route and the
eigenvalue-bridge route, on the pinned spectrum `{1/3, 1}` of
`(1/3)!![2,1;1,2]`, independently meet at the value); the general-`t`
instance `‖(L+2•1)⁻¹‖ = 1/2` exactly (spectrum `{1/4, 1/2}`, the
`t = 2` resolvent `(1/8)!![3,1;1,3]` pinned by an independent
left-inverse witness) — also attained; the Lipschitz instance at
`A = L`, `B = 0` with **both sides independently pinned** (difference
spectrum `{-2/3, 0}` → norm `2/3`; `‖L‖ = 2` from spectrum `{0, 2}`;
the instantiated theorem reads `2/3 ≤ 2` — a reversed or badly-factored
statement would produce a falsehood); the **shift-load-bearing
witness** (the proposal's QA item 3): the invertible PSD `(1/4)I`
*without* the shift has `‖A⁻¹‖ = 4 > 1` (inverse `4I` by an
independent left-inverse witness, norm from the pinned spectrum
`{4,4}`); and the **hypothesis-load-bearing witness**: the symmetric
non-PSD `-(3/4)I` has `+1` shift equal to `(1/4)I` — invertible,
inverse norm `4 > 1` — with the violated hypothesis exhibited at
`![1,0]` (`quadForm = -3/4 < 0`).

**Verification:** `lake env lean` on the changed public module and its
QA module — zero errors, zero warnings; `#print axioms` on the three
new public theorems and eight headline QA theorems ✔ (three standard
axioms only); module oleans produced directly during iteration (the
recorded fast-`lean -o` path); **all thirty-two QA modules
batch-elaborated, zero errors** (the only diagnostics are the eight
documented pre-existing section-variable warnings in untouched
modules); full `lake build` ✔; `lint_axioms` (13), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**827/13/0**; `Resolvent_QA` 30 → 75 by the generator metric).
Environment: the pruned-oleans state recurred again at run start; the
recorded interpreted cache fetch restored the oleans (5685, ~4 min)
before any elaboration. Implementation notes recorded for future QA
work: the `Finset.prod_eq_multiset_prod` bridge (not `..._sum`) for
product pins; `det_eq_prod_eigenvalues` carries a `ℝ→𝕜` coercion that
only `simpa` normalizes away (the two-step `simpa` + `norm_num`
converts to the `lo * hi` pin shape); `norm_num` does not close
`|1/3| ≤ 1` — rewrite with `abs_of_nonneg (show (0:ℝ) ≤ 1/3 by
norm_num)` explicitly, and a trailing `try norm_num` absorbs `rw`'s
inconsistent auto-closing; `-2/3` parses as `(-2)/3`, so `abs_neg`
does not match — convert with `show (-2/3:ℝ) = -(2/3) from by
norm_num` first; `1/4 * 1/2` parses left-associatively as
`(1/4 * 1)/2` — parenthesize; the two-point spectrum pin is
generalized (`two_point_pin_of_sum_prod`, target roots `lo ≤ hi` with
sum/prod matching) and reused five times.

**Records updated:** module/QA docstrings, scoreboard (827/13/0, the
QA-module and public-module verification rows extended, Step-2
milestone bullet), radar (axis 2 evidence completed with the bounds,
score **held at 3.5** — family completion, not a new capability; QA
count 827/32 with the attainment/route-agreement and guard kinds; the
QA axis **held at 4.0**; both holds logged in the re-scoring log;
proved-depth hard-crust list extended), README (827; the proved list
gains the resolvent norm/Lipschitz bounds), perturbation index map
(3 new Resolvent rows; Deferred Work narrowed to Step-3 injectivity),
proposal Step-2 delivery record + status header + open-next-step
(Step 3), and `proposals/README.md` (the High row now points at Step
3).

**Next milestone (open):** Resolvent **Step 3** — injectivity
(`A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹`, a one-line consequence of the Step-1
identity), which completes the program; or the two ungated High rows —
**Tikhonov Regularization** (a corollary of the proved eigenbasis
expansion) and **Spectral Band Projectors** (the difference of two
`spectralProjector` calls). The Medium rows (Fiedler Phase B — needs
an operator decision; mixing-time Step 1; Reversibility A and B;
Relative Entropy; Perron–Frobenius + directed operators;
discharge-perturbation — whose Weyl target now shares the bridge AND
the delivered norm/Lipschitz pattern; approximate spectral projection)
stay queued.

**Resolvent Calculus for PSD Matrices, Steps 0 and 1 (run 1,
2026-08-19): DELIVERED.** The Active priority table's top High item
(`proposals/resolvent-calculus-psd.md`), opened at its mandatory Step
0 gate and through Step 1 (the steps-0+1 precedent). Pure hard crust —
**zero new axioms** (count stays 13; `#print axioms` on every public
theorem reads only `propext, Classical.choice, Quot.sound`). Steps 2–3
(norm bound, Lipschitz bound, injectivity) were NOT started.

**Step 0 (the spike, decisive negative, then the fallback bridge):**
the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is
**structurally inapplicable** to `Matrix V V ℝ` — it is stated
`[CStarAlgebra A]`, which extends `NormedAlgebra ℂ A` and
`StarModule ℂ A`, and `NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℝ)`
fails to synthesize (elaboration-verified; the scoped
`Matrix.L2OpNorm` instances `NormedRing`/`CStarRing` resolve, but the
complex-algebra bundle cannot — a structural obstruction, not an
instance-search gap). The proposal's own contingency was adopted and
delivered in the new `Analysis.OperatorTheory.Resolvent`: the
from-scratch operator-norm bridge from the proved eigenbasis
machinery — `abs_eigvalOf_le_l2OpNorm` (unit eigenvector through
`toEuclideanCLM` + `ContinuousLinearMap.le_opNorm` +
`cstar_norm_def`), `l2OpNorm_le_of_abs_eigvalOf_le` (Parseval
`dotProduct_eigvecOf` + eigenaction `dotProduct_eigvecOf_mulVec`
resolving `‖M *ᵥ y‖²` termwise, then `opNorm_le_bound`), their
sorted-spectrum forms, and the packaged extremal identity
`l2OpNorm_eq_max_abs_evals` (`‖M‖ = max |evals hM 0| |evals hM last|`)
— the Step-0 target statement. One generic addition to the center:
`evals_first_le_eigvalOf` in `GraphTheory.Spectral` (the
first-sorted-entry mirror of `eigvalOf_le_evals_last`). The bridge is
the one-time cost the proposal identified — the shared route for
Step 2's norm/Lipschitz bounds and the
`discharge-perturbation-axioms.md` Weyl target.

**Step 1:** `isUnit_det_add_smul_one_of_quadForm_nonneg` — `M + t • 1`
invertible for *any* matrix with nonnegative quadratic form and
`t > 0` (kernel-vector route: a kernel vector would force
`quadForm M v + t (v ⬝ᵥ v) = 0`, both terms nonnegative, the second
positive — **no symmetry hypothesis needed**, a recorded strengthening
over the proposal's PSD-symmetric sketch), with the `t = 1` instance;
and `resolvent_identity_sub`
(`(A+1)⁻¹ − (B+1)⁻¹ = (A+1)⁻¹ * (B − A) * (B+1)⁻¹`) by pure
`nonsing_inv` algebra.

**QA** `OperatorTheory/Resolvent_QA.lean` (30 declarations, the first
OperatorTheory-domain QA file): the `!![2,1;1,2]` fixture with
spectrum `[1,3]` pinned from trace/determinant/sortedness independent
of the bridge; both directions composed to pin `‖mat2‖ = 3` exactly
(the literature spectral-norm value); the extremal form at
`max 1 3 = 3`; the **negative witness** `¬(‖mat2‖ ≤ 1)` — bounding by
one eigenvalue's absolute value is refuted, so the `∀ k` hypothesis is
load-bearing; the shifted-PSD invertibility cross-checked against
computed determinants (`3` at `t = 1`, `8` at `t = 2`) with the
**shift-load-bearing witness** (the unshifted `K₂` Laplacian's
determinant is exactly `0` — PSD alone gives no invertibility; the
`+1` is not decorative); and the resolvent identity at `A = L(K₂)`,
`B = 0` with `(L+1)⁻¹` computed to `(1/3)!![2,1;1,2]` by an
independent left-inverse witness, both sides of the identity
independently computed from the raw definitions to the same literal
matrix — a wrong factoring (order or sign) would fail the check.

**Verification:** `lake env lean` on both changed public modules
(`Spectral` + the new `Resolvent`) and the QA module — zero errors,
zero warnings; `#print axioms` on all eight public theorems and six
headline QA theorems ✔ (three standard axioms only); module oleans
produced directly during iteration; **all thirty-two QA modules
batch-elaborated, zero errors**; **full `lake build` ✔ (2184 targets,
"Build completed successfully")**; `lint_axioms` (13),
`check_citations`, `check_markdown_links` pass; scoreboard
regeneration idempotent (**782/13/0**, `OperatorTheory` a new QA
domain row). Environment: the pruned-oleans state recurred at run
start (Mathlib build dir empty); the recorded interpreted cache fetch
restored 5387 before any elaboration, and the full build replayed the
Mathlib trace residue (~35 min). Implementation notes recorded for
future L2OpNorm work: `CStarAlgebra` is the *complex* bundle — for
real matrices use the scoped `Matrix.L2OpNorm` instances plus
`cstar_norm_def`/`toEuclideanCLM_piLp_equiv_symm`/`toLin'_apply` as
the transport spine; `omit ... in` must precede doc comments; `rw`
with an equation whose LHS is a bare `1` rewrites every `1` in sight
(including inside `A + 1`); matrix entrywise computation is cheapest
via `Matrix.det_fin_two`/`det` on the *entries*
(`simp only [Matrix.add_apply, Matrix.one_apply, ...]` + `norm_num`),
not via literal-matrix rewriting; a numeral `2` in `2 • (1 : Matrix)`
elaborates as ℕ-smul unless written `(2 : ℝ)`.

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean` +
docstring), scoreboard (782/13/0, verification rows for the QA and
public module targets, milestone bullet), radar (subject axis 2
evidence extended with the bridge + steps-1 facts and the score **held
at 3.5** per protocol; QA count 782/32 with the pinned-norm/shift-guard/
identity-check kinds, the QA axis **held at 4.0** — both holds logged
in the re-scoring log; proved-depth hard-crust list extended), README
(782; the proved list gains the operator-norm/resolvent bridge),
Mathlib coverage map (the operator-norm row: the scoped L2OpNorm
instances exist but no real-matrix norm↔eigenvalue bridge — the
C*-thread's `NormedAlgebra ℂ` obstruction, elaboration-verified),
perturbation index map (new Resolvent section, 7 rows; Deferred Work
narrowed to steps 2–3), proposal Step-0 decision record + Step-1
delivery record + status header + open-next-step (Step 2), and
`proposals/README.md` (the High row now points at Step 2). The
operator's concurrent edits (`governance/ADVERSARIAL_REVIEW.md`,
`proposals/discharge-perturbation-axioms.md`) are preserved untouched.

**Next milestone (open):** the Active table's top High rows —
**Resolvent Step 2** (`‖(A+1)⁻¹‖ ≤ 1` and the Lipschitz bound
`‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A − B‖` through the delivered bridge plus the
shifted/inverted eigenvalue transfer, then Step 3's one-line
injectivity; or the ungated High items **Tikhonov Regularization**
(no gate — a corollary of the proved eigenbasis expansion) and
**Spectral Band Projectors** (no gate — the difference of two
`spectralProjector` calls). The Medium rows (Fiedler Phase B — needs
an operator decision; mixing-time Step 1; Reversibility A and B;
Relative Entropy; Perron–Frobenius + directed operators;
discharge-perturbation — whose Weyl target now shares the delivered
bridge; approximate spectral projection) stay queued.

**Decidable spectral certificates, Step 4 — QA and extraction
demonstration (run 1, 2026-08-19): DELIVERED; the program is
COMPLETE.** The Active priority table's top High item
(`proposals/decidable-spectral-certificates.md`) at its final step —
pure QA, **zero new axioms** (count stays 13; no public-module
changes), 688 → 752 QA declarations; `#print axioms` on all 22 new
headline theorems reads only `propext, Classical.choice, Quot.sound`.

**Delivered in the two QA modules:**

- `SpectralCertificates_QA.lean` (+17, 39 in file): the **`C₆`
  chain at the second required size** — kernel `decide` accept at the
  attained `1`, reject at `0`, fractional `3/2`/`1/2`, arithmetic
  pinned (`rawNumer = 8`, `denom = 4`, quotient `8/(2·4) = 1`), the ℚ
  specification through the proved bridge, end-to-end
  `lambda2 (C₆) ≤ 1` and `≤ 3/2`; and the **exact pin** — a C₄
  Poincaré inequality (`2‖x‖² ≤ xᵀLx` on `1⊥`; the `n = 4` Wirtinger
  identity `E = 2Σx² + 2(x₀+x₂)²` by `linear_combination`) through the
  **lower** half of `lambda2_variational` (`le_csInf` — its first
  `≥`-direction QA consumer) pins `lambda2 (C₄) = 2`, so the
  certificate chain is **exactly tight** (`cert4_certificate_exact_QA`:
  the kernel checker accepts precisely at the true `lambda2` and
  rejects the integer bound `1` below it).
- `Expander_QA.lean` (+47, 88 in file): the exact C₄ pins
  (`λ₂ = 2`, `λ_max = 4` — the latter via the alternating vector
  through `quadForm_le_evals_last`), so **`μ(C₄) = 2` exactly** and the
  Ramanujan bound `2√(d−1)` is *attained with equality*; the **`K₃`
  fixture** — the energy identity `xᵀLx = 3‖x‖² − (Σx)²` pinning
  `λ₂ = λ_max = 3`, `μ(K₃) = 1` (classical `μ(Kₙ) = 1`, strictly
  Ramanujan), with the EML **attained exactly on both cuts tested**
  (both sides compute to `2/3`); the **`C₆` EML** with derived `μ ≤ 2`
  (test vector + the identity `xᵀLx = 4‖x‖² − Σ_edges(xᵢ+xᵢ₊₁)²` +
  PSD), attained exactly on the alternating cut `({0,2,4},{0,2,4})`.

**Acceptance Criterion 4 (documentation):** scoreboard (752/13/0,
verification rows + step-4 milestone bullet), radar (QA count/kinds
synced; subject axes 4 and 7 evidence extended with scores **held** per
protocol and the holds logged in the re-scoring log), the
traction-plan extraction-gap note (the revisit precondition named there
is met — added as planning provenance respecting that document's
clean-room boundary), README count (752), proposal Step-4 delivery
record + status header (program complete, AC 1–4 all met), and
`proposals/README.md` (row moved to Delivered; progress note rewritten
— the three `sgt-gaps`-promoted High rows are now the top of the Active
table).

**Verification:** `lake env lean` on both changed QA modules — zero
errors, zero warnings; `#print axioms` on the 22 new headline theorems
✔ (three standard axioms only); all thirty-one QA modules
batch-elaborated, zero errors; **full `lake build` ✔ (2183 targets)**;
`lint_axioms` (13), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (752/13/0). Environment healthy at
run start (full Mathlib oleans present — the pruned-oleans state did
not recur; no cache fetch needed). Recorded implementation notes: the
`cons_val` simp family stops at index four (the `rfl`-provable
`vecCons_val_five` helper bridges index five when both indices are
`OfNat`-literals from sum expansion; `fin_cases` row indices defeat the
chain, so C₆ row sums are proved per row by `show` up to defeq); ℤ
structural facts evaluate by `decide` where ℝ ones cannot.

**Next milestone (open):** the Active table's top High rows are now the
three `sgt-gaps`-promoted items, each with its recorded entry point —
**Resolvent Calculus for PSD Matrices** (Step 0 first: the unverified
`IsSelfAdjoint.spectralRadius_eq_nnnorm` C*-algebra thread for the
operator-norm bridge, shared with `discharge-perturbation-axioms.md`'s
Weyl target), **Tikhonov Regularization in the Laplacian Eigenbasis**
(no gate — a corollary of the proved eigenbasis expansion), and
**Spectral Band Projectors** (no gate — the two-sided band is the
difference of two existing `spectralProjector` calls). The Medium rows
(Fiedler Phase B — needs an operator decision; mixing-time Step 1;
Reversibility Phases A and B; Relative Entropy; Perron–Frobenius +
directed operators; discharge-perturbation; approximate spectral
projection) stay queued.

**Decidable spectral certificates, Step 3 — the computable certificate
module (run 1, 2026-08-19): DELIVERED.** The Active priority table's
top High item (`proposals/decidable-spectral-certificates.md`), at the
step its Step-2 delivery record named as next. Pure hard crust —
**zero new axioms** (count stays 13; `#print axioms` on every public
theorem of the new module reads only `propext, Classical.choice,
Quot.sound`). Step 4 was NOT started this run.

**Delivered** in the new `GraphTheory.SpectralCertificates`, exactly
as the Step 0 re-scoping pinned — both halves, bridged: (a) the
ordered-field transport layer, whose hinge `algebraMap_apply`
(`algebraMap ℚ ℝ q = (q : ℝ)`) is `rfl`, carrying symmetry,
nonnegativity, dot products, and the Dirichlet energy
(`quadForm_laplacian_map_algebraMap` — the certificate's `rawNumer` is
exactly `quadForm (laplacian A ℝ) (toReal v)` halved, load-bearing on
the center's `laplacian_quadForm` convention); (b) the one-sided
Rayleigh consumer form `lambda2_le_rayleigh` — the division-form twin
of the Step-2 multiplication bound, proved straight from the proved
`lambda2_variational` (constraint-set membership + PSD
boundedness); (c) the ℚ specification checker
`isSpectralUpperBoundCertificate` with its soundness theorem
`lambda2_le_of_certificate` at exactly the proposal's sketched
statement shape — the flagship load-bearing consumer of
`lambda2_variational`: `rawNumer/2` is the Laplacian energy,
`dotOne = 0` is the constraint, `sInf ≤ rayleigh ≤ bound` follows
(two recorded implementation deviations: the cross-multiplied raw
inequality form so both checkers share one shape, and `decide`
conjuncts with public `rfl` unfolding lemmas because the `let`-shaped
bodies yield no usable simp equations); (d) the kernel-verifiable
**ℤ cross-multiplied twin** `isSpectralUpperBoundCertificateInt`
(exactly the Step 0 recorded shape, `== 0` included) and its
fractional-bound variant, with the proved bridges —
`...Int_iff` (sound *and complete* against the specification at an
integer bound) and `...IntFrac_iff` (the cross-multiplication bridge;
`0 < den` external, genuinely needed for the reverse direction — the
ℚ-side bound alone cannot see the sign of `den`); (e) the
kernel-facing corollaries `lambda2_le_of_certificateInt` /
`...IntFrac` (the executable chain: `decide`d integer data → proved
bridge → real bound; the matrix-equality transfer
`lambda2_le_of_matrix_eq` handles `lambda2`'s proof-valued symmetry
argument by `subst` + proof irrelevance).

**QA** `SpectralGraph/SpectralCertificates_QA.lean` (22 declarations,
fresh `C₄` fixture): kernel-`decide`d demonstrations on the twin —
accepted at the attained bound `2`, rejected at `1`, non-orthogonal
and zero test vectors rejected, fractional `5/2` accepted / `3/2`
rejected; the ℚ specification proved `= true` **only through the
proved bridge** (the Step 0 wall made explicit — the bridge is
load-bearing in QA); the end-to-end soundness instances
`lambda2 (C₄) ≤ 2` and `≤ 5/2` consuming `decide`d hypotheses; the
checker's arithmetic pinned (`dotOne = 0`, `denom = 2`, `rawNumer =
8`, Rayleigh quotient `4/2 = 2` — the certified bound is exactly the
test vector's quotient); and the **guard refutation** —
`lambda2 ≤ rayleigh onesVec` refuted on the connected cycle
(`0 < lambda2` via `lambda2_pos_of_connected`, `rayleigh onesVec = 0`
computed), so the orthogonality conjunct (and the zero-vector guard,
same junk value `0`) is load-bearing, exactly as the proposal's
Calibration 2 demands. Acceptance Criterion 2 thereby read against
the ℤ twin as re-scoped.

**Verification:** `lake env lean` on the new public module and its QA
module — zero errors, zero warnings; `#print axioms` on all eight
headline public theorems and the five key QA theorems ✔ (three
standard axioms only); module olean produced directly during
iteration; **all thirty-one QA modules batch-elaborated, zero
errors**; **full `lake build` ✔ (2183 targets, one more than before —
the new module; 6:27 wall)**; `lint_axioms` (13), `check_citations`,
`check_markdown_links` pass; scoreboard regeneration idempotent
(**688/13/0**). Environment: the pruned-oleans state recurred at run
start; the recorded interpreted cache fetch re-applied (5685 files
unpacked) before any elaboration.

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean`
+ its docstring), scoreboard (688/13/0, verification rows for the new
public and QA modules, step-3 milestone bullet), radar (subject axis
7 re-scored **3.0 → 3.5** — the axis's first verified
numerical/spectral algorithm driver, with the re-score logged; QA
count 688/31 with the kernel-`decide`d algorithmic QA kind described;
the QA axis **held at 4.0** per protocol — parametric/randomized QA
untouched), README (688, the proved list gains the
certificate-soundness layer, new module row, axis-7 cell 3.5), SGT
index map (new `SpectralCertificates` section, 11 rows + header;
module list updated), proposal Step-3 delivery record (with both
implementation deviations and the `0 < den` external-hypothesis
note) + status header, and `proposals/README.md` (High row now points
at Step 4).

**Next milestone (open):** proposal Step 4 — QA and extraction
demonstration: the `C₆` kernel-`decide` demonstrations, the
`Kₙ`/`Cₙ` Ramanujan fixture family per the Step 0 scope decision
(drop the label rather than expand scope if awkward), exact spectrum
pins for the derived-`μ`/certified-bound sharpness (the C₄ QA pins
the *quotient*, not `lambda2 = 2` itself — an exact lower-bound pin
is Step 4's natural completion), and the Acceptance-Criterion-4
documentation notes (scoreboard/radar/traction-plan). The Medium rows
(Fiedler Phase B — needs an operator decision; mixing-time Step 1;
Reversibility Phase A and Phase B; Relative Entropy; the new
resolvent/Tikhonov/band-projector High rows) stay queued.

**Decidable spectral certificates, Step 2 — the Expander Mixing Lemma
itself (run 1, 2026-08-19): DELIVERED.** The Active priority table's
top High item (`proposals/decidable-spectral-certificates.md`), at the
step its Step-1 delivery record named as next. Pure hard crust —
**zero new axioms** (count stays 13; `#print axioms` on all nine new
public theorems reads only `propext, Classical.choice, Quot.sound`).
Steps 3–4 were NOT started this run.

**Delivered route** (cheaper and stronger than the proposal's
eigenspace-expansion sketch — no eigenspace split of `A`, no
Cauchy–Schwarz, no kernel case analysis, no affine spectrum transfer):
(a) two generic additions to `Spectral.lean` — `eigvalOf_le_evals_last`
(sort membership + monotonicity) and the top Rayleigh domination in
multiplication form `quadForm_le_evals_last` (`xᵀ M x ≤ λ_max •
(x ⬝ᵥ x)` for every symmetric matrix, unconditionally in `x`), plus
`dotProduct_self_pos` made public; (b) the `d`-regular identity
`quadForm_add_quadForm_laplacian` (`xᵀAx + xᵀLx = d • ‖x‖²` — the
quadratic form of `A + L = D`), with generic support `quadForm_add`,
`quadForm_add_sub_eq` (polarization), `quadForm_degreeMatrix`;
(c) the Rayleigh sandwich on `1⊥` — `lambda2_mul_dotProduct_le_quadForm`
(the proved `secondEval_le_rayleigh` multiplied out) below,
`quadForm_le_evals_last` above — giving the operator bound
`abs_quadForm_le_of_ortho_onesVec`; (d) the sharp bilinear bound
`quadForm_bilinear_sq_le_of_ortho_onesVec` by the scaling trick
(`√Y•x ± √X•y` through polarization; `a² = Y, b² = X` attains AM–GM
equality — no slack); (e) the variance identity
`dotProduct_centeredIndicator_self` (`‖cS‖² = |S|(|V|−|S|)/|V|`);
(f) the headline `expander_mixing_lemma` at the Step 0 restated `√`
signature, squaring only inside the proof. **Statement-shape
strengthening recorded in the proposal:** the Step 0 sketch's `hloop`
hypothesis is dropped — the `A + L = D` identity needs regularity
only (self-loops sit on `D`'s diagonal either way).

**QA** `SpectralGraph/Expander_QA.lean` (+19 declarations, 41 in
file): the spectral hypothesis is **derived, not assumed** — `μ = 2`
proved on `C₄` from three independent bounds (test vector
`![1,0,−1,0]` with Rayleigh quotient `2` for `λ₂ ≤ 2` via
`secondEval_le_rayleigh`; a direct sum-of-squares estimate
`xᵀLx ≤ 4‖x‖²` routed to `λ_max ≤ 4` through `quadForm_eigvecOf_self`
+ `evals_mem_eigvalOf`; PSD lower bounds for both). The lemma is
instantiated on two cuts, and the bound is **attained exactly** on the
opposite cut (both sides independently compute to `2`: `|0−2| =
2√16/4`) and on the alternating vector in the operator bound
(`|xᵀAx| = 8 = 2‖x‖²`) — the derived `μ` is tight, the theorem not
vacuous; the half cut's deviation computes to `0`, and the variance
identity cross-checks against the pinned `±1/2` entries.

**Verification:** `lake env lean` on both changed public modules and
the QA module — zero errors, zero warnings; `#print axioms` on the
nine new public theorems ✔ (three standard axioms only); explicit
`lake build` of the two targets ✔; **full `lake build` ✔ (2182
targets)**; all thirty QA modules batch-elaborated, zero errors;
`lint_axioms` (13), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (**666/13/0**). Environment: the
pruned oleans state recurred at run start; the recorded interpreted
cache fetch restored Mathlib's oleans, then `lake build Batteries`
preceded iteration (direct `lake env lean -o` used for fast olean
updates during iteration; the final full `lake build` replayed the
trace chain and rebuilt cleanly).

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean`),
scoreboard (666/13/0, verification rows, step-2 milestone bullet),
radar (subject axis 4 re-scored **3.5 → 4.0** — a new theorem family,
spectral–combinatorial discrepancy, with the re-score logged; QA count
666/30 with the derived-hypothesis and sharpness QA kinds described;
the QA axis **held at 4.0** per protocol — parametric/randomized QA
untouched; proved-depth text; weakest-axes paragraph), README (666,
axis-4 cell 4.0, the proved list gains the EML, cuts-and-expansion
module row), SGT index map (8 new Expander rows + section header; 3
new Spectral rows), proposal Step-2 delivery record (+ the `hloop`
deviation) + status header, and `proposals/README.md` (High row now
points at Step 3). The operator's concurrent changes (README's
why-SGT section; untracked `governance/ADVERSARIAL_REVIEW.md` and six
new untracked proposals incl. `directed-graph-operators.md`; edits to
`1_STRATEGY.md`, `6_SGT_BACKLOG.md`, `CONTRIBUTING.md`,
`admit-perron-frobenius.md`, `electrical-flow-routing.md`) are
preserved untouched.

**Next milestone (open):** proposal Step 3 — the computable
certificate module, now scoped by the Step 0 record: deliver both the
ℚ-facing soundness statement (`isSpectralUpperBoundCertificate` /
`lambda2_le_of_certificate`, consuming `lambda2_variational` — the
proposal's flagship load-bearing consumer) and the kernel-verifiable
integer cross-multiplied twin, bridged by a proved cross-multiplication
lemma; then Step 4 (QA incl. the kernel `decide` demonstrations on
`C₄`/`C₆` and the Ramanujan fixture family). The Medium rows (Fiedler
Phase B — needs an operator decision; mixing-time Step 1; Reversibility
Phase A; Relative Entropy) stay queued.

**Decidable spectral certificates, steps 0 and 1 (run 1, 2026-08-19):
DELIVERED.** The Active priority table's top High item
(`proposals/decidable-spectral-certificates.md`) opened at its
recorded gate and through its first build step — the steps 0–1
precedent of the electrical-flow program. Zero new axioms (count stays
13); steps 2–4 were NOT started this run.

**Step 0 (the gate, recorded in the proposal before any Lean):** (1)
the adjacency-vs-Laplacian convention resolved **Laplacian-first
through the `d`-regular bridge** — survey evidence: no
adjacency-eigenvalue interface exists anywhere (adjacency is weights
and fixtures only; every spectral declaration is Laplacian-wrapped or
generic-symmetric), the certificate half (Step 3) is already
Laplacian, the generic symmetric engine applies to an adjacency matrix
for free (so the bridge `A = d•1 − L` needs no new interface), and no
named consumer wants adjacency eigenvalues; the restated
`expander_mixing_lemma` signature is pinned in the proposal with the
`√`-form as the mathematical statement and squaring as a recorded
Step-2 implementation option. (2) The ℚ-`decide` spike returned a
decisive **negative**: plain kernel `decide` cannot verify the
proposal's ℚ-arithmetic certificate — a reducibility wall, not
performance (`((2:ℚ) + 2) = 4` is already stuck at `(Rat.add 2 2).num`:
ℚ literals are opaque kernel literals, so `Rat.add`/`Rat.div`/
`Rat.blt` never unfold in elaborator reduction; `#eval` works via
native externs but is not kernel-checked; controls `Nat.gcd`,
ℕ-sums-over-`Fin`, and ℤ arithmetic all decide fine). Adopted fallback
(recorded): the **integer cross-multiplied twin** — all data in ℤ,
inequality `rawNumer ≤ 2 * bound * denom` — kernel-decided clean at
`C₄` (`Fin 4`, attained `λ₂ = 2`: accepted at `2`, rejected at `1`;
non-orthogonal and zero test vectors rejected) and `C₆` (`Fin 6`,
attained `λ₂ = 1`), plus the fractional-bound clearing form (`λ₂ ≤ 5/2`
accepted, `≤ 3/2` rejected); whole acceptance file ~15 s wall, almost
all `Mathlib.Tactic` import. Step 3 is thereby re-scoped: deliver both
the ℚ-facing soundness statement and the ℤ twin, bridged by a proved
cross-multiplication lemma; Acceptance Criterion 2 reads against the
twin. (3) Ramanujan QA scope resolved to the existing `Kₙ`/`Cₙ`
fixture family (both are small Ramanujan instances), with the
drop-if-awkward fallback per the proposal's own rule.

**Step 1 (hard crust):** the new `Scaffold/Mathlib/GraphTheory/Expander`
— `edgeWeight` (degenerate-cut guards, the degree-sum form
`edgeWeight A S univ = ∑ i ∈ S, deg A i`, the hypothesis-free matrix
form `edgeWeight_eq_dotProduct`, `edgeWeight_symm` by sum swap);
`indicatorVec`/`centeredIndicator` with the decomposition and the
orthogonality `sum_centeredIndicator_eq_zero` /
`centeredIndicator_dotProduct_onesVec` — both **unconditional** (the
empty-type case handled; no `Nonempty` hypothesis carried — a small
strengthening over the proposal's sketch); `mulVec_onesVec_eq_const`
(consuming `deg`'s row-sum shape); and the headline
`edgeWeight_eq_regular_add_centered` (`e(S,T) = d·|S|·|T|/n +
centered cross term`), symmetry load-bearing through
`Matrix.dotProduct_mulVec`'s transpose and regularity through the
`A *ᵥ onesVec = d` evaluation. `#print axioms` on all seven public
theorems: only the three standard axioms.

**QA** `SpectralGraph/Expander_QA.lean` (22 declarations, fresh `C₄`
fixture per the QA-independence convention): values computed from the
raw definitions (adjacent `1`, opposite `0`, half-and-half `2`, total
`8`, matrix form cross-checked, centered indicators pinned entrywise
with orthogonality computed from the pinned entries); the
decomposition instantiated on an adjacent cut (`1 = 1/2 + 1/2`) and an
opposite cut (`0 = 1/2 − 1/2`), cross terms computed independently;
three negative witnesses — main-term-only refuted (`0 ≠ 1/2`), wrong
degree refuted (`1 ≠ 3/4`), asymmetric weight breaks cut symmetry
(`2 ≠ 1`).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings (targeted `omit` clauses on unused section
variables; two `set_option linter.unnecessarySeqFocus false in` on the
cross-term lemmas where `simp` closes some `fin_cases` branches —
repo precedent); `#print axioms` on the seven public theorems ✔;
explicit `lake build` of both targets ✔; full `lake build` ✔ (2182
targets, one more than before — the new module); all **thirty** QA
modules batch-elaborated, zero errors (only the documented
pre-existing section-variable warnings in untouched modules);
`lint_axioms` (13), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (647/13/0). Environment: the pruned
oleans state recurred at run start (Mathlib empty, Batteries partial,
Scaffold empty) — the recorded interpreted cache fetch restored
Mathlib's 5685, then an explicit `lake build Batteries` (the fetch
does not cover Batteries' non-default facet modules that
`Mathlib.Tactic` needs) preceded the full `lake build` (~33 min cold
residue; recorded for the next run).

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean` +
docstring), scoreboard (647/13/0, verification rows, milestone
bullet), radar (QA 647/30 with the discrepancy-core QA kind described;
the QA axis **held at 4.0** per protocol with the hold recorded in the
re-scoring log — steps 0–1 are decisions and interface plumbing, the
parametric-QA gap untouched), README (647, cuts-and-expansion module
row), SGT index map (new `Expander` section, 6 rows + status line),
proposal Step-0 decision record + restated signature + Step-1 delivery
record, and `proposals/README.md` (High row now points at Step 2).

**Next milestone (open):** proposal Step 2 — **the Expander Mixing
Lemma** itself: the bridge layer (the eigenvalue hypothesis
`max |d − λ| ≤ μ` → the Rayleigh-form operator bound `|xᵀAx| ≤ μ xᵀx`
on `x ⊥ 1`, through the eigenbasis/Courant–Fischer machinery), then
the centered-cross-term bound by Cauchy–Schwarz, packaged as the
restated signature (with the recorded option to square both sides to
stay in ordered-field arithmetic); then Step 3 (the certificate
module, now scoped with the ℤ twin) and Step 4 (QA incl. the kernel
`decide` demonstrations on `C₄`/`C₆`). The Medium rows (Fiedler Phase
B — needs an operator decision; mixing-time Step 1; Reversibility
Phase A; Relative Entropy) stay queued. The operator's untracked
`adversarial.md`, `sgt-gaps.md`, and `why-sgt.md` are preserved
untouched.

**Foster's Theorem Phase A (run 1, 2026-08-19): DELIVERED.** The Active
priority table's top High item, `proposals/spectral-graph-sparsification.md`
**Phase A only**, delivered as pure hard crust in the new
`Scaffold/Mathlib/GraphTheory/Foster` — **zero new axioms** (count stays 13;
`#print axioms foster_theorem` reads only `propext, Classical.choice,
Quot.sound`). Phase B was NOT started (blocked in the proposal on the
unresolved matrix-Chernoff scope decision).

**Delivered** (all proved): `card_filter_eigvalOf_laplacian_eq_zero` (the
kernel of a connected Laplacian occupies exactly one eigenbasis index —
at most one by orthonormality against the one-dimensional kernel, at
least one because `onesVec` is a nonzero kernel vector — the counting
fact behind `n − 1`); `effectiveResistance_eq_sum_eigbasis` (the
per-pair spectral sum `R u v = ∑_k (v_k u − v_k v)²/λ_k` over nonzero
eigenvalues — the pseudoinverse-free Foster kernel); the headline
`foster_theorem` (`(∑ i, ∑ j, A i j * R i j)/2 = card V − 1` on every
connected symmetric-nonnegative network, stated at full strength with
no cardinality hypothesis); and the leverage-score objects
(`leverageScore` — the importance-sampling object of the blocked
Phase B, junk below `2 ≤ card V` documented — and
`sum_leverageScore_eq_two`, the probability-distribution corollary with
`hcard` as the division guard). Route exactly as the proposal's
"Correction" scoped: spectral resolution + double-sum swap +
per-eigenvector Dirichlet evaluation (`∑_{i,j} A i j (v_k i − v_k j)² =
2 λ_k` via `laplacian_quadForm`/`quadForm_eigvecOf_self`) + the
kernel-index count — reconciling (not reversing) the
`electrical-structure-crust.md` removal, which was of the `L⁺` route
only; no pseudoinverse or matrix square root anywhere.

**QA** `SpectralGraph/Foster_QA.lean` (53 declarations): the cliques
`K₃`/`K₄`, the path `P₃`, and the 3-leaf star — every resistance pinned
by an explicit potential witness (`K₄` through the general-pair
potential `(e i − e j)/4`, proved to solve the unit demand for *every*
pair via the entrywise `L = 4I − J` structure, so all twelve ordered
terms are pinned by one lemma); each ordered Foster sum computed
independently of the theorem (`4`, `6`, `4`, `6`) and cross-checked
against the theorem's `card V − 1` (`2`, `3`, `2`, `3`); the
**double-counting factor refuted-on-omission on both cliques** exactly
as the proposal's calibration demands (`4 ≠ 2` on `K₃`, `6 ≠ 3` on
`K₄` — a statement shape dropping the `/ 2` would be refuted);
non-edge pairs provably absent (zero conductance); leverage pinned
(`K₃` edge `1/3`, total `2`; `K₄` edge `1/6`).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings (the five `K₄`-adjacent QA lemmas where `simp`
closes some `fin_cases` branches carry targeted
`set_option linter.unreachableTactic/unusedTactic false in`
modifiers); `#print axioms` on all four public theorems confirms only
the three standard axioms; `lake build` of the Foster target ✔; full
`lake build` ✔ (2181 targets, one more than before — the new module);
all twenty-nine QA modules batch-elaborated, zero errors (only the
eight documented pre-existing section-variable warnings in untouched
modules); `lint_axioms` (13), `check_citations`, `check_markdown_links`
pass; scoreboard regeneration idempotent (625/13/0). Environment: the
pruned Mathlib-oleans state recurred at run start; the recorded
interpreted cache fetch restored 5387 oleans before any elaboration
(see the scoreboard's provenance note).

**Records updated:** module/QA docstrings, umbrella (`Scaffold.lean` +
its docstring), scoreboard (625/13/0, verification rows, Foster
milestone bullet), radar (subject axis 6 re-scored **4.0 → 4.5** — a
new theorem family, global network identities, not packaging — with
the re-score logged; QA 625/29 with the Foster QA kind; weakest-axes
paragraph; re-scoring log), README (625, axis-6 cell 4.5, Foster added
to the proved list and the electrical-structure module row), SGT index
map (new Foster section, 5 rows), backlog item 7 (Foster delivered;
family residuals unchanged), proposal Phase A delivery record + status
header, and `proposals/README.md` (Phase A row moved from Active to
Delivered; progress note rewritten — **decidable spectral certificates
is now the top High item**, Step 0 gate first).

**Next milestone (open):** the Active table's top High item is now
**decidable spectral certificates Step 0** (the convention decision +
ℚ-`decide` spike, both scoped in its own proposal — do not begin Step
1 before they are recorded); the Medium rows (Fiedler Phase B — needs
an operator decision; mixing-time Step 1; Reversibility Phase A;
Relative Entropy) are queued behind it. The operator's Medium/Low rows
and the untracked `why-sgt.md` are preserved untouched.

**Electrical-flow routing, step 5 — the ICP capacity-reinforcement
example (run 1, 2026-08-19): DELIVERED; the program is COMPLETE.** The
Active priority table's top High item `proposals/electrical-flow-routing.md`,
at its recorded final step, delivered as pure packaging of step 4 (zero
new axioms; the explicit count stayed 13 throughout the program).

**Delivered** in `GraphTheory.ElectricalFlow` (9 declarations, all
proved): `increaseConductance` (raise one undirected pair's conductance
by `δ`, both ordered entries together so symmetry/nonnegativity are
preserved) with the entry interfaces and structural lemmas
(`increaseConductance_apply_of_reinforced`/`_of_not_reinforced`,
`le_increaseConductance`, `increaseConductance_isSymm`,
`increaseConductance_nonneg`); the connectivity adapter pair the step-4
record named as step 5's natural companion — `supportGraph_le_of_le`
(support graphs grow along entrywise domination, **no nonnegativity
hypothesis** since `0 < A i j ≤ B i j`) and `supportGraph_connected_of_le`
(capacity growth preserves connectivity, via Mathlib's
`SimpleGraph.Connected.mono` — found in the pin, no local walk
induction needed); and the one-hypothesis headline
`effectiveResistance_le_increaseConductance`:
`effectiveResistance (increaseConductance A i j δ) u v ≤
effectiveResistance A u v` for `δ ≥ 0`, with only the *original*
network's connectivity hypothesized — the reinforced network's is
derived. This is the proposal's ICP-facing fact as a one-line consumable
theorem: adding capacity cannot worsen the certified energy cost of
electrical routing.

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (+9 declarations, 88 in
file) — the release-facing proof example, on the Mathlib `Fin 3` path
graph through `SimpleGraph.toWAdj` (the proposal's suggested route):
the adapter weights bridged entrywise to the weighted-fixture world
(`path3_toWAdj_eq_connPathAdj`); the reinforcement computed to exactly
the concrete doubled-path matrix (`path3_reinforced_eq_pathDoubled_QA`);
the reinforced resistance `3/2` pinned by the independent potential
witness `![1/2, 0, −1]`, with the reinforced network's connectivity
proved by explicit walks — computed independently of the adapter the
headline consumes; the headline instantiated in the one-hypothesis form
(`path3_reinforcement_QA`); and the decrease certified strict
`3/2 < 2` against the adapter-bridged pinned original value
(`path3_reinforcement_strict_QA`).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings (targeted `omit [Fintype V]`/`[DecidableEq V]`
clauses where the section variables are unused); explicit `lake build`
of both targets ✔; all twenty-eight QA modules batch-elaborated, zero
errors; full `lake build` ✔ (2180 targets); `lint_axioms` (13),
`check_citations`, `check_markdown_links` pass; scoreboard regeneration
idempotent (572/13/0). One mid-run repair: a placeholder stub inserted
by a bad edit was replaced with the real section before any
verification ran (the policy forbids `True` placeholders; the delivered
module contains none).

**Records updated:** module/QA docstrings, scoreboard (572/13/0,
verification rows, step-5 milestone bullet), radar (QA 572/28 with the
step-5 kind; axis-6 evidence extended to program-complete with the
score **held at 4.0** — packaging, not new mathematics; the step-4
3.5 → 4.0 re-score added to the re-scoring log for continuity;
proved-depth completion clause; weakest-axes paragraph; header review
date), README (572), SGT index map (4 new rows; section header to
steps 0–5 complete), backlog item 7 (program-complete note), proposal
step-5 delivery record + status/open-next-step sections, and
`proposals/README.md` (row moved from the Active table to Delivered;
progress note rewritten — **Foster Phase A is now the top High item**).

**Next milestone (open):** the Active table's top High item is now
Foster's Theorem Phase A (`spectral-graph-sparsification.md`) — its
recorded scoping spike (the pseudoinverse-free statement shape:
eigenbasis expansion + the proved one-dimensional kernel
characterization) is the natural first run; or decidable-certificates
Step 0 (convention decision + ℚ-`decide` spike, both scoped in its
proposal). The operator's Medium/Low rows are preserved untouched.

**Electrical-flow routing, step 4 — Rayleigh monotonicity in conductance
form (run 1, 2026-08-19): DELIVERED.** The Active priority table's top
High item `proposals/electrical-flow-routing.md`, at its recorded next
step: entrywise `A ≤ B` ⇒ `effectiveResistance B u v ≤
effectiveResistance A u v` for connected symmetric nonnegative networks,
zero new axioms (count stays 13). The first *network-comparison* theorem
in the center (it relates two graphs, not two objects of one graph) and
the proposal's named ICP-facing fact — adding capacity cannot worsen the
certified energy cost of electrical routing.

**Delivered** in `GraphTheory.ElectricalFlow` (3 new declarations, all
proved): `isFlowOn_of_le` (flow-space growth — a flow supported on `A`
is a flow on every entrywise larger `B ≥ A ≥ 0`; support load-bearing: a
`B`-zero entry above a nonnegative `A` entry squeezes the latter to
zero), `flowEnergy_le_of_le` (raising conductances lowers dissipated
energy, termwise `θ²/B ≤ θ²/A`; support load-bearing a second time on
the `A i j = 0 < B i j` branch — the zero-conductance trap now guarding
the comparison), and the headline `effectiveResistance_le_of_le` —
exactly the proposed route: the `A`-unit-demand potential's current is a
unit flow *on `B`* (growth + Kirchhoff bridge), Thomson (step 3) on `B`
bounds `R_B` by its `B`-energy, the comparison bounds that by its
`A`-energy, and the step-2 identity evaluates it as `R_A`. Load-bearing
on solvability, the Kirchhoff bridge, support, Thomson, and the energy
identity — an error in any breaks the proof. Connectivity of both graphs
hypothesized per the proposal's initial-shape instruction; the optional
`supportGraph B`-from-`A` adapter deliberately not attempted (kept
non-blocking; noted for step 5 if its reinforcement shape wants a
one-hypothesis form).

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (+20 declarations, 79 in
file): the proposal's QA item 2 — conductance `1 → 2` on the unit edge,
resistance certified to decrease `1 → 1/2` from an independent potential
witness, monotonicity instantiated, decrease certified strict, and the
**orientation guard** (reverse inequality `1 ≤ 1/2` refuted numerically —
weights are conductances; a resistance-direction statement would be false
here, exactly the statement bug the proposal's calibration names); the
competitor transfer instantiated on computed objects (the `edgeAdj`-current
is a unit flow on `edge2Adj`; cross-network energy `1/2 ≤ 1` computed from
the raw definitions on both sides); and a partial increase on the triangle
(one edge's conductance doubled: `2/3 → 2/5` strict, new value pinned by
the independent potential `![2/5, 0, 1/5]`).

**Verification:** `lake env lean` on both changed modules — zero errors,
zero warnings; `lake build` of both targets ✔; all twenty-eight QA
modules batch-elaborated, zero errors (only the documented pre-existing
linter notes in untouched modules); full `lake build` ✔ (2180 targets);
`lint_axioms` (13), `check_citations`, `check_markdown_links` pass;
scoreboard regeneration idempotent (563/13/0). Environment: the pruned
Mathlib-oleans state recurred at run start; the recorded interpreted
cache fetch restored all 5685 before the checks.

**Records updated:** module/QA docstrings, scoreboard (563/13/0,
verification rows, step-4 milestone bullet), radar (subject axis 6
re-scored **3.5 → 4.0** per the step-3 recorded reservation — Thomson
and Rayleigh have both now landed; QA count 563/28 with the step-4 kind;
proved-depth text; weakest-axes paragraph), README (counts + axis-6 cell
4.0 + last-assessed date), SGT index map (3 new rows; section header to
steps 0–4), backlog item 7 (the stale "deferred Rayleigh" note corrected:
the conductance-form theorem is delivered via the flow route; only the
Dirichlet-principle *route* remains deferred), proposal step-4 delivery
record (+ the adapter note), and `proposals/README.md` progress note.

**Next milestone (open):** proposal step 5 — the ICP capacity-reinforcement
example (`effectiveResistance (increaseConductance A i j δ) u v ≤
effectiveResistance A u v` on a small `SimpleGraph.toWAdj` or weighted
fixture, short enough for release documentation; a packaging of step 4,
not new mathematics — the proposal's final step, after which the
electrical-flow program is complete). Or the other High items: Foster
Phase A (needs its pseudoinverse-free statement-shape spike) or
decidable-certificates Step 0 (convention decision + ℚ-`decide` spike,
both scoped in its proposal). The operator's concurrently added Medium
rows (Reversibility Phase A, Relative Entropy) and the icebox additions
are indexed by the operator in the priority table and preserved
untouched.

## Superseded milestones (historical)

**Citation hygiene and broad-SGT reorientation.** The projector algebra is
proved in the center. The persistence package is retained as an existing
compatibility/example result, not a roadmap goal. The citation-hygiene
audit items below were completed on 2026-08-17 (see Last verified state):

1. **False provenance note (found by audit):** the Chung index claimed
   earlier revisions recorded page-level locators "Theorem 2.1 p. 42,
   Theorem 2.2 p. 44". Git history contradicted this: the initial commit
   cited only "Theorem 2.2" without a page, and no pre-rebuild index file
   exists. The note now records the accurate history; theorem and page
   numbering stay explicitly unconfirmed against the printed text (no
   local copy; page numbers were not invented).
2. **Weyl citation fidelity:** `weyl_inequality`'s doc now records that
   its Lean form is the spectral-norm corollary of the cited general Weyl
   inequality (obtained by combining the additive bound with
   `λ₁(E) ≤ ‖E‖` and `λₙ(E) ≥ -‖E‖`).
3. **Davis–Kahan hypothesis tightening:** the separation hypothesis is
   now the binding single-pair two-cluster form
   `λ_{k+1}(A+E) - λ_k(A) ≥ δ` (the form used by the cited
   Yu–Wang–Samworth Theorem 2); the derived wrapper simplified to one
   Weyl fact at the gap index, and the QA reduces the pairwise form via
   `evals_sorted`.

**Hard-crust conversion (same module):** `spectral_gap_stability` is now
a theorem proved from `weyl_inequality` (Weyl at both gap endpoints plus
arithmetic), reducing the explicit axiom count 19 → 18 with identical
statement shape (no consumer changes).

**Leverage delivered:** a false provenance claim removed from the
human-review surface; two axiom statements aligned with their sources;
the mushy center shrunk at zero trust cost.

**Next action:** with citation hygiene closed, the next milestone is the
broad-SGT backlog (ready queue item 1) — **delivered on 2026-08-17**:
(a) `docs/6_SGT_BACKLOG.md`, the bounded center-first backlog ranked by
concrete reuse (random-walk/Markov interfaces; irregular normalized
adapters; expansion/cut interfaces; spectral algorithms; conditional
dynamics and statistical-mechanics items), each naming consumers and
dependency paths, linked from the README canonical-docs list; and (b) its
top-ranked item implemented: `Scaffold.Mathlib.GraphTheory.RandomWalk`
— `transitionMatrix`, proved row-stochasticity for `d`-regular graphs,
`randomWalkLaplacian`, and proved bridges to both existing worlds
(`= regularNormalizedLaplacian`; `= d⁻¹ • laplacian`). Pure hard crust,
no new axioms; QA `SpectralGraph/RandomWalk_QA.lean` with a concrete
two-vertex instantiation. Umbrella, scoreboard, and SGT index map
updated.

**Next milestone:** backlog item 2, remainder — the irregular walk form —
**delivered on 2026-08-17 (run 8)**. Evidence check first: the walk
Laplacian `I − D⁻¹A` is *not symmetric* for irregular graphs, so
Scaffold's `evals` does not apply to it, and the deferred eigenvalue
transfer would need a charpoly-roots interface absent from the pinned
Mathlib. Delivered in `GraphTheory.Normalized` (all proved): general
`walkTransitionMatrix` (`D⁻¹A`) with `walkTransitionMatrix_row_sum`
(row-stochasticity under positive degrees — the named Markov consumer),
`walkLaplacian`, and the similarity identity
`degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`
(`√D · L_walk · (1/√D) = L_sym`), with the eigenvalue-list transfer
recorded as the precisely named residual gap in the backlog. QA extended
at the 3-vertex path (row distributions, walk entries `1/2`/`1`, and the
similarity identity instantiated entrywise).

**Next milestone (open):** backlog item 3 — expansion and cut interfaces
(edge-boundary and uniform-weight conductance variants), each admitted
only with a named algorithm consumer.

**Active slice (run 10, 2026-08-17): cut duality — delivered.** The
existing cut surface (`vol`, `boundary`, `conductance`,
`cheegerConstant`) had nonnegativity but not the duality facts that
every cut-consuming algorithm assumes. Delivered in
`GraphTheory.Spectral` (all proved, no axioms): `vol_compl`
(`vol S + vol Sᶜ = vol univ`), `boundary_compl` (`boundary S =
boundary Sᶜ` for symmetric `A`, via `Finset.sum_comm` + symmetry),
`conductance_compl` (`conductance S = conductance Sᶜ` — Cheeger
minimizer canonicalization; the sweep-cut consumer interface),
`boundary_empty`/`boundary_univ` (degenerate-cut guards). QA at the
3-vertex path (`SpectralGraph/Cuts_QA.lean`, 11 declarations):
singleton boundary computes to `1`, duality and conductance invariance
instantiate, volume complementarity totals `4`, guards evaluate.
Backlog item 3's "Have" list updated.

**Next slice (open):** remaining backlog item 3 variants — edge-boundary
and uniform-weight conductance — each to be admitted only with a named
algorithm consumer; or backlog item 4 gating review.

**Active milestone (run 1, 2026-08-17): SGT coverage radar (operator
direction) — delivered.** `docs/7_SGT_RADAR.md` published with both
radars scored strictly from repository evidence (every score cites
declarations with proved/admitted/absent status): subject — models 2.5,
spectral algebra 3.5, variational 2.5, cuts/expansion 2.5, walks 2.5,
electrical **0.5** (entirely absent), perturbation/randomness 3.0,
adjacent systems 1.0; assurance — proved depth 3.5, axiom minimization
3.5, Mathlib interop 3.5, QA 3.0, citation fidelity 3.5, downstream
reuse **2.5** (RandomWalk/Normalized unconsumed). Includes a
re-scoring protocol (scores move only with usable, verified coverage,
recorded with the causing milestone). Backlog gains the radar-driven
gated candidate (item 7, electrical structure) and a downstream-reuse
standing decision; README canonical-docs list links the radar. No Lean
changes; hygiene suite passes.

**Next milestone (radar-driven): first downstream consumer for the
walk/normalized interfaces — delivered (run 2, 2026-08-17).** New
`Scaffold.Mathlib.GraphTheory.Stationary` (imports `Normalized`; all
proved, no axioms): `mulVec_one_eq_deg` (`A *ᵥ 1 = deg`),
`normalizedLaplacian_mulVec_sqrtDeg_eq_zero` (kernel of `L_sym` is
`√deg` — the normalized counterpart of `laplacian_ones_in_kernel`),
and `walkTransitionMatrix_transpose_mulVec_deg` (`Pᵀ *ᵥ deg = deg`:
the degree measure is stationary for the walk, `π ∝ deg` — the named
Markov-mixing consumer interface). QA
`SpectralGraph/Stationary_QA.lean` (6 declarations) at the 3-vertex
path. Radar: downstream reuse re-scored 2.5 → 3.0 with this milestone
recorded (protocol followed); remaining reuse gap: `RandomWalk`'s
regular-case bridges.

**Next milestone (open):** a consumer for `RandomWalk`'s regular
bridges — **delivered (run 3, 2026-08-17).** Evidence-based scoping:
the λ-transfer consumer needs `evals (c • M) = c • evals M`, but
Mathlib's `eigenvalues` is `irreducible_def` behind the eigenspace
decomposition — recorded as a named backlog candidate rather than
attempted. Delivered instead: `GraphTheory.Stationary` extended with
the walk-Laplacian kernel facts —
`randomWalkLaplacian_mulVec_one_eq_zero` (regular; consumes
`RandomWalk.transitionMatrix_row_sum`) and
`walkLaplacian_mulVec_one_eq_zero` (irregular; consumes
`Normalized.walkTransitionMatrix_row_sum`) — conservation of mass,
`(I − P) *ᵥ 1 = 0`, the base statement of diffusion/mixing arguments.
`Stationary` is now the demonstrated consumer of *both* interface
modules. QA at the regular edge and the irregular path. Radar: reuse
re-scored 3.0 → 3.5 (recorded); the constraint is now breadth of
reuse, and QA (3.0, degenerate-case skew) is the weakest assurance
axis.

**Next milestone (superseded — QA lever delivered below):** breadth
consumers for the walk/normalized interfaces (second consuming module —
e.g. variational Rayleigh bounds through the congruence bridge), or the
QA-assurance lever (property-based/falsification QA — delivered as the
run 1 slice below), or remaining backlog item 3 variants with named
consumers.

**Active slice (run 1, 2026-08-17): exhaustive/falsification QA for the
SGT center — delivered.** The QA axis was the weakest assurance axis
(3.0): existing QA instantiated theorems at one or two cuts and mostly
*applied* the general theorem (e.g. `path_boundary_compl_QA` rewrites
with `boundary_compl`), so a mis-defined `boundary`/`vol`/`conductance`
self-consistent with its own theorem family would not be caught.
Delivered `Scaffold/QA/SpectralGraph/Exhaustive_QA.lean` (87
declarations, hard crust, no axiom changes): (a) kernel-checked
exhaustive enumeration of **all** cuts of the 3-vertex path and the
4-cycle (`Finset.univ.powerset` equality by `decide` — `cuts3_eq`,
`cuts4_eq`), with `boundary`/`vol` values computed from the definitions
against hand-expected numbers; (b) duality recomposed from the
independently computed tables (`exh_boundary_duality_QA`,
`cyc_boundary_duality_QA`, `exh_vol_complementarity_QA`); (c) negative
witnesses — conductance separates adjacent-pair (`1/2`) from
opposite-pair (`1`) cuts on the cycle, Rayleigh separates `8/3` from
`0` on the path, and an asymmetric two-vertex weight shows
`boundary_compl`'s symmetry hypothesis is load-bearing (`2 ≠ 1`);
(d) walk row-stochasticity computed per row, independently of
`walkTransitionMatrix_row_sum`. Implementation note: `degreeMatrix`'s
diagonal conditional elaborates with a classical `Decidable` instance
(defined at generic `V`), so the Rayleigh checks compose the proved
Dirichlet identity and kernel theorem — the *values* are still fully
computed. Radar: QA re-scored 3.0 → 3.5 (recorded per protocol).

**Next milestone (delivered as the run 2 slice below):** breadth
consumers for the walk/normalized interfaces (second consuming module
— variational Rayleigh bounds through the congruence bridge). The
`evals (c • M) = c • evals M` Mathlib-excavation candidate and
backlog item 3 variants remain open.

**Active slice (run 2, 2026-08-17): variational transfer through the
congruence bridge — delivered.** The named breadth consumer from the
open milestone. Delivered
`Scaffold.Mathlib.GraphTheory.VariationalTransfer` (7 declarations,
all proved, no new axioms) plus QA
`SpectralGraph/VariationalTransfer_QA.lean` (15 declarations at the
3-vertex path): the generic congruence lemma
`quadForm (P M P) y = quadForm M (P *ᵥ y)` for symmetric `P`; the
Dirichlet-form transfer `yᵀ L y = (√D y)ᵀ L_sym (√D y)` consuming the
proved congruence; entrywise `√D *ᵥ y`; the degree-weighted
denominator `⬝(√D y, √D y) = ∑ deg i · y i²`; the headline
`rayleigh L_sym (√D y) = (yᵀ L y) / ∑ deg i · y i²` — the
irregular-graph normalized Rayleigh quotient the regular-only Cheeger
axioms cannot express; and `normalizedLaplacian_psd` transferred from
`laplacian_psd`. QA computes the classical value: at the path's
alternating vector, `8 / 4 = 2` — the largest eigenvalue of the
normalized path Laplacian, obtained without any spectral theorem.
`VariationalTransfer` is now the second consuming module of the
`Normalized`/`Spectral` interfaces (after `Stationary`). Radar:
downstream reuse 3.5 → 4.0, subject axis 3 (variational) 2.5 → 3.0,
both recorded per protocol. Umbrella and SGT index map updated.

**Next milestone (open):** the named `evals (c • M) = c • evals M`
Mathlib-excavation candidate (would connect `RandomWalk`'s regular
bridges to spectral statements); an irregular Cheeger statement shape
expressed through `rayleigh_normalizedLaplacian_degreeSqrt` (its
consumer interface is now available); or backlog item 3 variants with
named consumers.

**Decision milestone (run 9, 2026-08-17): `spectral_persistence`
deprecated — decision closed.** Consumer inventory (grep evidence): the
axiom had zero non-QA consumers — the derived layer mentioned it only in
a comment; its only use was the QA deliberately exercising the
compatibility surface; the derived two-endpoint chain
(`eventStreamProjectorDrift`/`davisKahanTwoPoint`) covers the motivating
persistence use. Per the architecture §9 lifecycle: `@[deprecated]` with
a migration note (probe-verified to apply to `axiom` declarations),
retained through the compatibility window — removal is a later release
decision, so the explicit axiom count remains 18 until then. The QA
exercises the deprecated surface with the linter silenced for that use
only. Indexes/docs updated (davis_kahan source, SGT/perturbation maps,
backlog standing decision, architecture debt, scoreboard). Bonus hygiene
in the same run: the derived module's use of Mathlib's deprecated
`div_lt_div_iff` upgraded to `div_lt_div_iff₀`; the full build now
carries zero deprecation warnings.

**Active milestone (run 1, 2026-08-18): Cheeger axiom statement-shape
repair — delivered.** Evidence found while scoping the
`evals (c • M)` candidate: both admitted Cheeger axioms state their
spectral side as `lambda2 (regularNormalizedLaplacian A d) …`, but
`lambda2` is defined as `evals (laplacian …) 1` — it wraps its argument
in the *combinatorial* Laplacian. The stated RHS was therefore the
second-smallest eigenvalue of `L(L_sym)`, not of `L_sym` itself; since
every `L_sym` row sums to zero, `L(L_sym) = -L_sym`, and on the
two-vertex edge the old lower-bound instance asserted `1²/2 ≤ 0` —
materially false. The docstring, index map, and source citation all
described the intended statement `φ²/2 ≤ λ₂(L_sym) ≤ 2φ`; only the
Lean RHS was defective. Delivered: new proved center interface
`secondEval` (second sorted eigenvalue of a symmetric matrix) plus the
bridge `lambda2_eq_secondEval`; both axioms restated with the corrected
RHS at unchanged names and hypotheses (emergency repair per
architecture §9); QA gains a **refutation of the old shape on the edge
graph** (`old_cheeger_lower_bound_refuted_QA`, via the new
`eigvalOf_le_of_quadForm_nonpos` Rayleigh bound and `cheegerConstant =
1`), an independent **value pinning of the corrected RHS**
(`edge_normLap_secondEval_eq_two_QA`: `λ₂(L_sym) = 2` on `K₂` from the
new `eigvalOf_sum_eq_trace` + `det_eq_prod_eigenvalues` +
sortedness), and `cheeger_bounds_edge_QA` instantiates the corrected
sandwich on the fixture. New center hard crust: `secondEval`,
`lambda2_eq_secondEval`, `evals_mem_eigvalOf`,
`eigvalOf_le_of_quadForm_nonpos`, `eigvalOf_sum_eq_trace`. This is the
first computational eigenvalue QA in the tree — the radar QA axis's
named residual gap (re-scored 3.5 → 4.0 per protocol). Axiom count
unchanged (18). Verification: `lake env lean` on both changed modules
(zero errors/warnings); all nineteen QA modules and the changed public
modules built directly; full `lake build` (2161 targets); all hygiene
scripts pass; scoreboard, radar, and both Cheeger indexes updated with
the correction record.

**Next milestone (open):** the `evals (c • M) = c • evals M`
Mathlib-excavation candidate (would connect `RandomWalk`'s regular
bridges to spectral statements — note the new trace/Rayleigh/membership
tools reduce its cost); an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs a precise source and
consumer); or backlog item 3 variants with named consumers.

**Active slice (run 1, 2026-08-18): electrical-crust step 1 —
connectivity and the kernel characterization — DELIVERED.** Operator
direction pinned `proposals/electrical-structure-crust.md` **step 1
only**: for a connected weighted graph, `ker (laplacian A)` is exactly
the constants — the converse of `laplacian_ones_in_kernel`
(`Spectral.lean`). Pure hard crust; **no new axioms** (count unchanged
at 18). Proposal steps 2–5 (effective resistance, Rayleigh
monotonicity, Foster) were NOT started — stopping here with a clean
proof is the successful outcome.

**Connectivity predicate decision (recorded before stating anything):**
adopted Mathlib's `SimpleGraph.Connected` through a `WAdj → SimpleGraph`
adapter `supportGraph A hA` with `Adj i j ↔ i ≠ j ∧ 0 < A i j`. The
`i ≠ j` conjunct is forced by `SimpleGraph` looplessness — positive
diagonal weights (self-loops) cancel in `D − A` and so must not create
adjacency. Tradeoff vs a native reachability inductive over `WAdj`: a
native predicate would duplicate Mathlib's `Walk`/`Reachable` machinery
with no consumer of the duplicate, and later proposal steps (component
structure, spanning trees) would need a bridge to Mathlib anyway. The
adapter reuses Mathlib's walk induction for the propagation argument,
takes the anchor vertex from `Connected`'s bundled `Nonempty` field
(discharging the empty-vertex-type case for free), and is the first
`WAdj → SimpleGraph` bridge — movement on the radar's standing
matrix-first interop deviation and the prerequisite shape for the
proposal's second recommendation (`SimpleGraph.toWAdj`). Cost: two new
Mathlib imports in `Spectral.lean` (`Combinatorics.SimpleGraph.Path`
for `Walk`/`Reachable`/`Connected`, `LinearAlgebra.Matrix.ToLin` for
`mulVecLin`), mitigated by the `supportGraph_adj` interface lemma
(`Iff.rfl`).

**Delivered statements** (all proved, in `GraphTheory.Spectral`):
`supportGraph` + `supportGraph_adj`; edge constancy
`eq_of_laplacian_mulVec_eq_zero_of_pos_weight` (zero Dirichlet energy
kills `(f i − f j)²` termwise on positive weights, via
`laplacian_quadForm` + nonneg weights); walk propagation
`eq_of_supportGraph_walk` (induction on `SimpleGraph.Walk`);
connected ⇒ kernel ⊆ constants
`exists_const_of_laplacian_mulVec_eq_zero`; `laplacian_mulVec_const`;
the iff `laplacian_mulVec_eq_zero_iff_exists_const`; the algebraic
headline `laplacian_kernel_eq_span_onesVec`
(`LinearMap.ker (Matrix.mulVecLin (laplacian A)) = span ℝ {onesVec}`).
QA `SpectralGraph/Connectivity_QA.lean` (15 declarations): connected
positive witness (3-vertex path — support graph connected by explicit
walks through the center, both iff directions, constant recovered and
pinned to its value, non-constant `![1,0,0]` computed out of the
kernel) plus a disconnected negative witness (two disjoint `Fin 4`
edges — component indicator `![1,1,0,0]` computed into the kernel yet
not constant, support graph proved not connected via a block invariant
over walks), showing the connectivity hypothesis is load-bearing.
Radar re-scored per protocol with this milestone (proof + QA landed):
subject axis 6 (electrical) 0.5 → 1.0, subject axis 1 (models)
2.5 → 3.0, assurance Mathlib interop 3.5 → 4.0; QA axis text updated
to 255 declarations / 20 modules. Backlog item 7 records step 1
delivered with named consumers for step 2.

**Next milestone (open):** proposal step 2 — effective resistance by
the potential equation (`IsEffectiveResistance A u v r ↔ ∃ f,
laplacian A *ᵥ f = e u − e v ∧ f u − f v = r`), whose
well-definedness consumes `laplacian_kernel_eq_span_onesVec`; or the
still-open earlier candidates: the `evals (c • M) = c • evals M`
Mathlib-excavation, an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs a precise source and
consumer), or backlog item 3 variants with named consumers.

**Active slice (run 1, 2026-08-18): the `SimpleGraph → WAdj`
interoperability adapter — DELIVERED.** The proposal's re-sequenced
step 1 (its "highest compounding multiplier"), completing the
two-directional adapter surface begun with `supportGraph`. Delivered
`GraphTheory/SimpleGraphAdapter` (all proved, **no new axioms**, count
unchanged at 18): `SimpleGraph.toWAdj` (defined as Mathlib
`adjMatrix ℝ` — no parallel matrix to drift), `toWAdj_apply`,
`toWAdj_symm`, `toWAdj_nonneg`; agreement family `deg_toWAdj`,
`vol_toWAdj_eq_sum_degrees`, handshake
`vol_toWAdj_univ_eq_two_mul_card_edges` (from Mathlib's degree-sum
formula), headline `laplacian G.toWAdj = G.lapMatrix ℝ`,
`boundary_toWAdj_eq_sum_neighbors` /
`boundary_toWAdj_eq_sum_card_neighbors` (crossing-edge count, each
crossing edge counted once); neutral re-exports
`laplacian_toWAdj_mulVec_eq_zero_iff_reachable` and
`finrank_ker_laplacian_toWAdj`; roundtrip
`supportGraph_toWAdj_eq_self` and connected-`G` corollary
`laplacian_toWAdj_kernel_eq_span_ones` (the delivered span theorem
applied to Mathlib graphs). QA
`SpectralGraph/SimpleGraphAdapter_QA.lean` (38 declarations): at the
3-vertex path, weights/degrees/Laplacian entries/both Laplacian
sides/boundary/handshake/kernel membership computed against
hand-expected numbers; disconnected `Fin 4` negative witness with the
component indicator computed *into* the kernel yet the kernel proved ≠
`span {onesVec}` (`twoEdge_kernel_ne_span_QA`) — connectivity is
load-bearing through the adapter. Umbrella, scoreboard (293 QA
declarations, 21 modules), SGT index map, backlog item 7, and radar
updated; radar re-scored per protocol after proof + QA landed: Mathlib
interop 4.0 → 4.5 (both directions, proved roundtrip, Mathlib
kernel/component results transferred), subject axis 1 (models)
3.0 → 3.5; README snapshot cell synced.

**Environment note (recorded):** the local `.lake/build` state was
found pruned at run start (Mathlib oleans down to 1795/5685, including
the modules this slice needs). The recorded interpreter-based cache
fetch (`lake env lean --run Cache/Main.lean get` from the mathlib
package) restored all 5685; `lake build` then recompiled the 2008
-target residue (~35 min) before the normal checks. Scoreboard
provenance note updated.

**Next milestone (open):** proposal step 3 — the kernel-equality
bridge `ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)`,
inheriting Mathlib's `lapMatrix_ker_basis` and
`card_ConnectedComponent_eq_rank_ker_lapMatrix` for the *weighted*
Laplacian (the delivered `finrank_ker_laplacian_toWAdj` covers only
0/1 weights); then step 4 (potential solvability, the hinge — the
proposal forbids defining effective resistance before it). Or the
still-open earlier candidates: the `evals (c • M) = c • evals M`
Mathlib-excavation, an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs a precise source and
consumer), or backlog item 3 variants with named consumers.

**Active slice (run 1, 2026-08-18): electrical-crust step 3 — the
kernel-equality bridge — DELIVERED.** Operator direction: proposal
step 3 only; one step per run; step 4 not started. All proved, **no
new axioms** (count unchanged at 18).

**Delivered center facts** (`GraphTheory.Spectral`): the diffusion-form
identity `laplacian_mulVec_apply` (`(L *ᵥ f) i = ∑ j, A i j (f i − f
j)`; self-loop weights cancel — honest w.r.t. `supportGraph`'s
looplessness), `laplacian_mulVec_eq_zero_of_forall_reachable`
(component-constant ⇒ kernel, entrywise; **no connectivity
hypothesis**), and the component-form characterization
`laplacian_mulVec_eq_zero_iff_forall_reachable` — the weighted
counterpart of Mathlib's unweighted iff, generalizing step 2's
connected statement to disconnected graphs.

**Delivered bridge + inheritances**
(`GraphTheory.SimpleGraphAdapter`): the headline
`ker_laplacian_eq_ker_supportGraph_lapMatrix` (`ker (laplacian A) =
ker ((supportGraph A).lapMatrix ℝ)` — weights do not change the
kernel; both sides are the component-constant vectors, so the proof is
the two iff's composed),
`finrank_ker_laplacian_eq_card_supportGraph_components` (kernel
dimension = component count for *weighted* graphs — Mathlib's rank
theorem inherited; the delivered `finrank_ker_laplacian_toWAdj`
covered only 0/1 weights), and the transported component-indicator
basis `laplacian_ker_basis` + value interface
`laplacian_ker_basis_apply` (Mathlib's `lapMatrix_ker_basis` via
`Basis.map`/`LinearEquiv.ofEq`). One unforeseen prerequisite,
recorded in the proposal: Mathlib's `lapMatrix` API needs
`DecidableRel G.Adj`, invisible through the `supportGraph` projection
— discharged once as `supportGraphAdjDecidable` (`Real.decidableLT`).

**QA** `SpectralGraph/KernelBridge_QA.lean` (14 declarations, reusing
the `Connectivity_QA` fixtures): connected 3-path — bridge
instantiates, component count `1`, dimension `1`, basis vector
constantly `1`, all simultaneous with the connected span theorem (a
mis-stated bridge would contradict it); disconnected two-edge fixture
— component count computed to `2` **independently of the transferred
theorem** (block classification + `Nat.card_eq_two_iff`), dimension
`2`, basis vectors computed to `![1,1,0,0]`/`![0,0,1,1]`, kernel
strictly larger than the constants (connectivity load-bearing).
Radar re-scored per protocol (proof + QA landed): subject axis 6
(electrical) 1.0 → 1.5 — weighted component structure complete; the
score stays below 2.0 because no electrical quantity (resistance,
Matrix–Tree, Kirchhoff) is defined yet. Umbrella, scoreboard (307 QA
declarations, 22 modules), SGT index map, backlog item 7, and
proposal checklist updated.

**Active slice (run 1, 2026-08-18): electrical-crust step 4 — potential
solvability, the hinge — DELIVERED.** Operator direction pinned
`proposals/electrical-structure-crust.md` **step 4 only**; steps 5–6
were NOT started — landing the hinge cleanly is the successful
outcome. All proved, **no new axioms** (count unchanged at 18).

**Route decision (recorded before stating, per the proposal):** the
**constructive eigenbasis** route was taken. Survey (this run): the pin
still has no ready-made `range L = (ker L)ᗮ` lemma over these function
types; the center's proved eigenbasis tools are exactly sufficient.

**Delivered center declarations** (`GraphTheory.Spectral`):
`laplacian_dotProduct_mulVec` (reciprocity `w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ
f`, from `Matrix.dotProduct_mulVec` + symmetry), the kernel certificate
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (unsolvability
witnesses), `mulVec_eigvecOf_sum_apply` (entrywise action on
eigenbasis combinations) and `exists_mulVec_eq_of_zero_comp`
(constructive spectral inversion `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b/λᵢ) • vᵢ` —
the load-bearing consumer of the eigenbasis algebra), the headline
`exists_laplacian_mulVec_eq_of_sum_eq_zero` (zero-sum ⇒ solvable on
connected graphs; the zero-eigenvalue components of `b` die through
`laplacian_kernel_eq_span_onesVec`, step 2's theorem), and the
specialization `exists_laplacian_mulVec_eq_single_sub_single` (unit
demand `e u − e v` solvable — step 5's defining equation).

**QA** `SpectralGraph/PotentialSolvability_QA.lean` (12 declarations,
reusing `Connectivity_QA` fixtures + a new two-vertex edge fixture):
computed potentials on the edge (`L *ᵥ ![1,0] = e₀ − e₁`) and the
3-path (`L *ᵥ ![1,0,−1] = e₀ − e₂`, the vector is fixed by its own
Laplacian); theorem instantiations (unit-demand and a general
alternating zero-sum demand); and **proved unsolvability** witnesses —
demand `e₀` (sum `1`) has no solution on the connected edge (via the
all-ones kernel certificate), and the zero-sum cross-component demand
`e₀ − e₂` has no solution on the disconnected fixture (via the
component-indicator kernel certificate) — both hypotheses shown
load-bearing, exactly per the proposal's step-4 witness spec. Radar
re-scored per protocol (proof + QA landed): subject axis 6 (electrical)
1.5 → 2.0 — the potential equation is now *completely characterized*
on connected graphs; the axis stays modest because no electrical
quantity is defined yet. Umbrella, scoreboard (319 QA declarations, 23
modules), SGT index map, backlog item 7, README snapshot, and proposal
checklist updated.

**Active slice (run 1, 2026-08-18): electrical-crust step 5 —
effective resistance, uniqueness, and energy — DELIVERED.** Operator
direction pinned `proposals/electrical-structure-crust.md` **step 5
only**; step 6 (the one-sided Dirichlet bound) was NOT started; one
step per run. All proved, **no new axioms** (count unchanged at 18).
Both authorized halves (definitional plumbing and the energy identity)
landed in one run.

**Mathlib survey (recorded before stating, per the proposal):** no
effective-resistance or "resistance" declaration anywhere in the pin;
no Moore–Penrose pseudoinverse — the potential-equation definition is
the only available route (and the intended one).

**Delivered** in the new `Scaffold/Mathlib/GraphTheory.Electrical`
(17 declarations, all proved; keeps `Spectral.lean` bounded): the
relation `IsEffectiveResistance A u v r` (`∃ f, L *ᵥ f = e u − e v ∧
f u − f v = r`); `exists_isEffectiveResistance` (existence, consuming
step 4's `exists_laplacian_mulVec_eq_single_sub_single`);
`isEffectiveResistance_unique_of_reachable` (uniqueness of `r` stated
at **reachability-pair strength** via step 3's component-form
characterization — valid within a component of a disconnected graph,
strictly stronger than the proposal's connected sketch) with the
connected corollary; the total function `effectiveResistance A u v : ℝ`
by classical choice, junk fallback `0` **stated, not hidden**
(`effectiveResistance_eq_zero_of_not_exists`) and QA-witnessed;
agreement `effectiveResistance_eq_of_reachable` /
`effectiveResistance_eq`; the energy identity at solution level —
`quadForm (laplacian A) f = f u − f v` for *any* solution, **no
hypotheses** (definitional unfolding of `quadForm` plus
`Matrix.dotProduct_single`) — and at function level
(`effectiveResistance_eq_quadForm`: `R u v = energy of an actual
potential`); `effectiveResistance_nonneg` (from `laplacian_psd` through
the energy identity); `effectiveResistance_symm` (relation-level
symmetry is hypothesis-free: negate the potential;
`isEffectiveResistance_symm`); `isEffectiveResistance_self_iff`
(diagonal characterized exactly, no hypotheses) and unconditional
`effectiveResistance_self`.

**QA** `SpectralGraph/EffectiveResistance_QA.lean` (17 declarations,
reusing the `Connectivity_QA`/`PotentialSolvability_QA` fixtures):
values computed from the definitions — unit edge `R 0 1 = 1` (witness
`![1,0]`), 3-path `R 0 2 = 2` (witness `![1,0,−1]`; series edges add);
the energy identity cross-checked against an energy computed
independently from the raw definitions; the junk fallback pinned on
the disconnected fixture (cross-component pair: no value exists —
proved from the step-4 unsolvability witness — while the function
reads `0`: fallback, not measurement); and same-component witnesses —
two *distinct* potentials `![1,0,0,0]`/`![2,1,0,0]` both witnessing
`r = 1` between `0` and `1`, with the reachability-form agreement
pinning `effectiveResistance 0 1 = 1` where the connected-graph
theorem's hypothesis fails (uniqueness is about `r`, not `f`; a
two-dimensional kernel does not break the value).

**Named residual (cheap, deferred by the scope fence):**
definiteness — `R u v = 0 ↔ u = v` on a reachable pair.

Radar re-scored per protocol (proof + QA landed): subject axis 6
(electrical) 2.0 → 2.5 — the first electrical quantity, with its full
well-definedness package; below 3.0 because the variational Dirichlet
bound, Rayleigh monotonicity, the resistance metric, and
Matrix–Tree/Kirchhoff remain absent. Umbrella, scoreboard (336 QA
declarations, 24 modules), SGT index map, backlog item 7, README
snapshot, and proposal checklist updated.

**Active slice (run 1, 2026-08-18): electrical-crust step 6 — the
one-sided Dirichlet bound — DELIVERED.** Operator direction pinned
`proposals/electrical-structure-crust.md` **step 6 only**; the named
cheap residual (`R u v = 0 ↔ u = v`) was NOT started — one step per
run; with this step the proposal's program is **complete** (steps 1–6,
axiom count 18 throughout).

**Mathlib survey (recorded before proving, per the proposal):** the
pin's only Cauchy–Schwarz is the *definite* inner-product-space one
(`Analysis/InnerProductSpace/Basic.lean`); the Laplacian energy form is
merely semidefinite (constants have zero energy), so it is unusable
without first quotienting out the kernel; no `QuadraticForm` C–S exists
at these function types. **Route taken (recorded before stating):**
polarization of the PSD energy, in three proved layers.

**Delivered** in `GraphTheory.Electrical` (4 new declarations, all
proved, no axioms): `sq_le_mul_of_forall_zero_le_sub` (algebra core: a
real quadratic nonnegative everywhere has nonpositive discriminant
`c² ≤ Q·E`; minimum at `t = c/E`, degenerate `E = 0` forces `c = 0`);
`quadForm_laplacian_sub_smul` (polarization `quadForm L (f − t • g) =
quadForm L f − 2t·(f ⬝ᵥ L g) + t²·quadForm L g`; the mixed terms agree
through the proved reciprocity `laplacian_dotProduct_mulVec`);
`laplacian_cauchy_schwarz` (`(f ⬝ᵥ L g)² ≤ quadForm L f · quadForm L
g`, **no connectivity hypothesis** — reusable beyond resistance); and
the headline `effectiveResistance_ge_sq_div_quadForm`
(`(f u − f v)² / quadForm L f ≤ effectiveResistance A u v` for any test
potential of positive energy, division guarded per architecture §4).
The headline is load-bearing on the whole chain: its cross term is
`f u − f v` *through the step-4 demand potential*, its energy is `R u
v` *through the step-5 energy identity*, and its C–S is `laplacian_psd`
— an error in any of those breaks this proof rather than passing beside
it. No attained supremum is used (the reverse direction is the deferred
Dirichlet principle).

**QA** `SpectralGraph/EffectiveResistance_QA.lean` (+9 declarations,
345 total): equality *attained* at the harmonic potentials on both
connected fixtures (edge `1²/1 = 1`, path `4/2 = 2`; energies computed
independently from the raw definitions — `edge_energy_e0_QA`,
`path_energy_e00_QA` reuse `path_energy_value_QA`); *strictness* at the
non-harmonic `![1,0,0]` (`1 < 2`); a **negative witness** refuting the
reverse inequality numerically (`2 ≤ 1` false — the one-sided form is
forced; the upper direction genuinely needs the attained-supremum
principle the proposal keeps deferred); and the **`0 <` energy guard
witnessed load-bearing** on the disconnected fixture (component
indicator: zero energy — kernel membership — with voltage difference
`1`, so an unguarded bound would read junk `1/0 = 0 ≤ 0` on both
sides).

Radar re-scored per protocol (proof + QA landed): subject axis 6
(electrical) 2.5 → 3.0 — the first variational/electrical inequality
on the axis; below 3.5 because full Rayleigh monotonicity, the
resistance metric, and Matrix–Tree/Kirchhoff remain absent (recorded
with the milestone). Radar QA-axis count synced to 345/24. Umbrella
unchanged (module already in it), scoreboard, SGT index map (4 new
`Electrical` rows), backlog item 7 (program complete; residual named),
README snapshot, and proposal checklist (all six steps ✅) updated.

**Active slice (run 1, 2026-08-18): retire `lambda2_variational` —
prove it in the matrix world, repairing a false statement shape —
DELIVERED.** Operator direction "advance
`proposals/prove-lambda2-variational.md`". **Finding (recorded before
stating anything):** the axiom as admitted was *materially false* — it
assumed only symmetry, but on `Fin 2` with `A = [[0,−1],[−1,0]]` the
Laplacian `[[−1,1],[1,−1]]` has sorted spectrum `[−2, 0]`, so
`lambda2 = 0` while every `x ⊥ onesVec` is a multiple of `(1,−1)` with
Rayleigh quotient `−2`; the axiom would assert `0 = −2`. Same defect
class as the 2026-08-18 Cheeger repair. **Delivered:** the axiom is now
a proved theorem at the same name with the load-bearing hypothesis
`hnonneg : ∀ i j, 0 ≤ A i j` added (matching `laplacian_psd`;
emergency repair per architecture §9); explicit axiom count 18 → 17.

**Route decision (recorded before proving):** the proposal's open next
step was to spike the `Matrix.IsHermitian ↔ LinearMap.IsSymmetric`
bridge (operator route through `Rayleigh.lean`, calibrated as several
sessions). Survey found a cheaper matrix-world route through the
repo's own proved eigenbasis tools; the LinearMap bridge was never
built. New proved hard crust in `GraphTheory.Spectral` (13
declarations): `eigvecOf_expansion_apply` (entrywise completeness,
factored out of and now reused by `exists_mulVec_eq_of_zero_comp`),
`dotProduct_eigvecOf` (Parseval), `dotProduct_eigvecOf_mulVec`
(self-adjointness in coordinates), `quadForm_eigvalOf` (spectral
resolution of the quadratic form), `quadForm_eigvecOf_self`,
`eigvecOf_ortho_onesVec` (nonzero-eigenvalue eigenvectors ⊥ `onesVec`,
symmetry only), the two **multiplicity pins** that make Courant–Fischer
provable without operator restriction — `evals_one_le_max_of_ne` (no
two distinct eigenbasis indices sit strictly below `evals 1`) and
`exists_ne_eigvalOf_of_evals_head_eq` (a repeated bottom entry comes
from two distinct indices) — and the headline `lambda2_variational`.
Lower bound: spectral resolution + the upper pin (the unique
below-λ₂ eigenvector is parallel to `onesVec`, invisible to the
constraint); upper bound: the eigenvector at `evals 1` when `λ₂ > 0`,
and a kernel vector ⊥ `onesVec` from the lower pin when `λ₂ = 0`
(the disconnected case). Load-bearing chain: resolution consumes
`eigvecOf_complete`; the unique-i₀ argument consumes
`laplacian_ones_in_kernel`; PSD consumes `laplacian_psd`.

**QA** `SpectralGraph/Variational_QA.lean` (+26 declarations, 371
total): the pre-repair shape **refuted in proved form**
(`old_lambda2_variational_refuted_QA`: `λ₂ = 0` from
trace/determinant/sortedness while the constraint set is exactly
`{−2}` by a parametric Rayleigh computation — `hnonneg` witnessed
load-bearing); `K₂` exact instantiation with `λ₂ = 2` computed **twice
independently** (sorted-spectrum pin; and *through* the theorem from
the parametric Rayleigh side — two routes that must agree); the
disconnected instantiation `λ₂ = 0` on two disjoint edges (kernel
witness `![1,1,−1,−1]` ⊥ `onesVec` + PSD floor); the path bound
`λ₂(P₃) ≤ 1` at the harmonic alternating vector.

**Scope caveat (recorded in the proposal):** the Cheeger proposal's
named intermediate is the *normalized* instance `secondEval L_sym`;
this delivery proves the combinatorial instance, from which the
normalized one follows via the proved congruence transfer — that
transfer step remains to be written.

Radar re-scored per protocol (proof + QA landed): subject axis 3
(variational) 3.0 → 3.5 — the row's named admitted gap closed by a
proved theorem; assurance axiom-minimization 3.5 → 4.0 — the first
axiom removed by proof rather than deprecation (net trend 26 → 19 →
18 → 17); proved-depth and QA text updated (QA count 371/24).
Umbrella unchanged, scoreboard, both source indexes (Chung §1.3,
Horn–Johnson §4.2 rows marked theorem), SGT index map, README
snapshot, and both proposals' status notes updated.

**Active slice (run 1, 2026-08-18): retire `cheeger_upper_bound` —
prove the Cheeger easy direction from a generalized Courant–Fischer —
DELIVERED.** Selected from `proposals/README.md`'s Active priority
table (top High item; Fiedler Phase A, the other High item, stays
queued and is the natural next run). Explicit axiom count **17 → 16**;
all new code proved, no new axioms, no consumer changes (the theorem
keeps the axiom's exact name, hypotheses, and statement).

**Route decision (recorded before proving, per the proposal):** the
named missing intermediate was built as a *generalization*, not a
transfer — the `lambda2_variational` Courant–Fischer argument was
lifted from `laplacian A` to any symmetric PSD matrix with
`M *ᵥ onesVec = 0` (`secondEval_variational`), so the normalized
instance needs **no eigenvalue-scaling lemma** (the
`evals (c • M)` excavation stays unnecessary): under `d`-regularity,
PSD of `L_sym` scales from `laplacian_psd` through the entrywise
identity `d • L_sym = laplacian A`, and the kernel fact is the row-sum
identity under `deg = d`.

**Delivered in `GraphTheory.Spectral`:** the generic
`eigvecOf_ortho_onesVec_of_mulVec_eq_zero` (the Laplacian instance
re-derives the existing `eigvecOf_ortho_onesVec` at unchanged shape);
`secondEval_variational` (full generalized body of the former
monolithic proof); `lambda2_variational` re-proved as a two-line
corollary at unchanged name/statement; the consumer form
`secondEval_le_rayleigh` (`secondEval ≤ R(x)` for every admissible
test vector — the interface test-vector arguments actually call).

**Delivered in `GraphTheory.Cheeger` (all proved):** the scaling
bridges (`quadForm_smul`, `smul_regularNormalizedLaplacian`,
`quadForm_regularNormalizedLaplacian`, `regularNormalizedLaplacian_psd`,
`regularNormalizedLaplacian_mulVec_onesVec`,
`vol_eq_of_regular`/`vol_pos_of_regular`); the volume-centered cut
indicator `cutTestVector` with its interface —
`cutTestVector_dotProduct_onesVec` (orthogonality under regularity),
`cutTestVector_ne_zero`,
`quadForm_laplacian_cutTestVector` (the general weighted-graph cut
energy identity `xᵀLx = boundary S · (vol V)²`, **no regularity
needed** — consumes `vol_compl`/`boundary_compl` cut duality),
`dotProduct_cutTestVector_self`, and
`rayleigh_regularNormalizedLaplacian_cutTestVector`
(`R(x) = boundary · vol V / (vol S · vol Sᶜ)`); the headline
`cheeger_upper_bound` as a theorem: per-cut bound
`λ₂ ≤ 2 · conductance S` (min ≤ both volumes), then `le_csInf` over
nonempty proper cuts. Load-bearing chain: the bound consumes the
variational engine, PSD scaling, the kernel fact, and cut duality — an
error in any breaks the proof.

**QA** `SpectralGraph/Cheeger_QA.lean` (+7 declarations, 378 total,
now importing `Exhaustive_QA` for the `C₄` tables): the test vector
pinned to `![1,-1]` on `K₂`; its Rayleigh value computed to `2` —
exactly the independently pinned `λ₂(L_sym)`
(`edge_normLap_secondEval_eq_two_QA`), so the test-vector bound is
*attained*; `cheeger_upper_bound_edge_eq_QA` proves the theorem's
bound attained on `K₂` as `λ₂ = 2φ` from independently computed
values; on `C₄`, `cutTestVector_cycle_rayleigh_QA` computes the
adjacent-pair test-vector Rayleigh value to exactly `1` and
`cheeger_upper_bound_cycle_le_QA` instantiates the theorem to
`λ₂ ≤ 1` through the exhaustively computed conductance `1/2`.

Docs updated: scoreboard (16/378/0, verification rows, milestone note),
radar (subject axis 4 re-scored 2.5 → 3.0 per protocol — the axis's
first inequality engine proved; axiom-minimization trend
26 → 19 → 18 → 17 → 16; QA count synced; proved-depth and reuse text),
both Cheeger indexes, backlog item 3, README snapshot, and
`proposals/README.md` (the proposal moved to Delivered with residuals
named: the irregular generalization — which *does* need the
congruence-transfer route since the engine's constraint is `onesVec`,
not `√deg` — and the proposal's two supporting moves).

**Next milestone (open):** the Fiedler proposal's Phase A (A1/A2) —
the remaining High item, scoped as close to free, and now composable
with the proved easy direction; or the residuals above; or the
`evals (c • M)` excavation.

**Active slice (run 1, 2026-08-18): audit and finish the uncommitted
normalized-Cheeger milestone — DELIVERED.** Operator direction (via
`scripts/finish-cheeger-milestone`): audit only the current uncommitted
Cheeger work — the `cheeger_upper_bound` retirement on the normalized
Laplacian (`secondEval (L_sym)`), whose hard-direction twin
(`cheeger_lower_bound`) correctly remains the sole admitted Cheeger
axiom — and finish it: no new mathematics, no new proposal, no commit.
Audit findings: (a) the Lean changes and record updates are present and
mutually consistent (16 axioms, 378 QA declarations, Cheeger QA 33,
README/scoreboard/radar/index/proposal rows all synced); (b) the
activity log's uncommitted diff had introduced exactly 6
trailing-whitespace lines — the Run/Session/Status metadata of its own
two newest entries (17:01/17:32Z) — now stripped; older committed
entries and the template's illustrative hard breaks are unrelated
records and were left untouched. Re-verification, all green: direct
elaboration (`lake env lean`) of `GraphTheory.Spectral`,
`GraphTheory.Cheeger`, and `QA.SpectralGraph.Cheeger_QA` — zero errors
(Cheeger QA zero warnings; the handful of linter notes elsewhere sit
in declarations verified present unchanged in HEAD, outside the diff
hunks); explicit `lake build` of the three targets ✔; `lint_axioms`,
`check_citations`, `check_markdown_links` pass; scoreboard
regeneration is byte-identical (no drift — 16/378/0 re-derived from
source); full `lake build` ✔ (2178 targets). Unrelated working-tree
changes preserved; nothing committed.

**Active slice (run 1, 2026-08-18): Fiedler Phase A — the vector and the
sign partition (proposal `fiedler-partitioning.md`, the remaining High
item at run start) — DELIVERED.** Hard crust, **no new axioms** (count
stays 16); Phase B is a separate later run and is explicitly
axiom-backed, not hard crust. Selected from `proposals/README.md`'s
Active priority table (top High item).

**A1 statement-shape decision (recorded before stating):** the
proposal's sketch `eigvecOf (laplacian A) hL ⟨1, by omega⟩` is
ill-typed — `eigvecOf` is indexed by `V` (the eigenbasis listing), not
by sorted-spectrum positions. Delivered instead: `fiedlerIndex` (the
eigenbasis index carrying `lambda2`, fixed by classical choice through
`evals_mem_eigvalOf`) with the interface lemma `fiedlerIndex_eigvalOf`,
and `fiedlerVector` = the eigenvector there. Delivered A1 theorems:
`fiedlerVector_eigen` (the eigenvector equation — the statement every
consumer starts from), `fiedlerVector_norm`/`fiedlerVector_ne_zero`
(unit norm from the orthonormal basis), `fiedlerVector_quadForm`
(Fiedler energy = `lambda2`), `fiedlerVector_ortho_onesVec` and the
sum form `fiedlerVector_sum_eq_zero` (under `0 < lambda2`).

**A2 plus the named load-bearing dependency:** the connectivity
hypothesis's content is exactly `lambda2 > 0`, and that implication is
now itself a theorem — `lambda2_pos_of_connected` (connected + symmetric
nonnegative weights ⇒ `0 < lambda2`; the algebraic-connectivity
certificate). Route: PSD bounds every eigenbasis eigenvalue, a
nonpositive `lambda2` pins the first two sorted entries to `0`, the
lower multiplicity pin yields two *distinct* orthonormal kernel basis
vectors, and `laplacian_kernel_eq_span_onesVec` (electrical step 2)
says the kernel is one line — contradiction. Load-bearing on the kernel
characterization and both multiplicity pins: an error in any breaks
this proof. `fiedlerPartition` (the sign half-space) then comes with
sanity facts at two strengths — interface form under `0 < lambda2`
(`fiedlerPartition_nonempty_of_pos`/`_ne_univ_of_pos`, both through
the zero-sum identity, exactly where `0 < lambda2` is load-bearing) and
the connectivity corollaries (`fiedlerPartition_nonempty`/
`_ne_univ`).

**QA** `SpectralGraph/Fiedler_QA.lean` (57 declarations, +57 total,
25 modules) — the Fiedler vector is noncomputable (spectral theorem +
classical choice), so the witnesses pin it through its proved defining
properties rather than by deciding entries. Positive witness 1 (`K₂`,
reusing `Variational_QA` fixtures): entries antisymmetric by the zero
sum, leading entry nonzero by unit norm, partition pinned to
`{0} ∨ {1}`, card `1`, boundary `1`. Positive witness 2 (the `P₄`
barbell — two `K₂` near-cliques joined by one bridge, the proposal's
named example shape): support-graph connectivity by explicit walks,
`0 < λ₂` via the certificate theorem, `λ₂ ≤ 1` via the proved Rayleigh
engine `secondEval_le_rayleigh` at the cut indicator
`![1,1,-1,-1]` (energy `4`, norm `4`), `λ₂ ≠ 1` because the eigen
equations at `λ = 1` force the vector to vanish against unit norm,
and then the eigen equations force the sign relations
`f 1 = (1-λ)f 0`, `f 2 = (1-λ)f 3`, `f 3 = -f 0` — so the partition is
*derived* to be exactly the known good cut `{0,1}` or its complement:
boundary `1`, volume `3`, conductance `1/3`, card `2`. Negative
witness (two disjoint edges): support graph proved not connected
(block invariant over walks), `λ₂ = 0` (hypothesis fails), and
`onesVec` is a nonzero eigenvector at `λ₂` (satisfying exactly the
equation `fiedlerVector_eigen` states) whose sign filter is all of
`univ` — the degenerate pattern the hypothesis rules out.

Docs: umbrella + module docstring, scoreboard (435/16/0, verification
rows, milestone bullet), radar (subject axis 4 re-scored 3.0 → 3.5 per
the proposal's own protocol — Phase A scored alone, Phase B to be
scored separately at its axiom-backed level; QA-axis count synced
435/25 with the new QA kind recorded; proved-depth and reuse text
extended), SGT index map (new `Fiedler` section), backlog item 4
(Phase A delivered; Phase B named as the open remainder), README
snapshot (axis-4 cell 3.5), proposal delivery record, and
`proposals/README.md` (Fiedler moved to Medium with the Phase B
decision framing).

**Environment note:** a new High item
(`proposals/repair-and-retire-woodbury.md`) appeared in the priority
table *during* this run (concurrent operator addition; the file is
untracked and preserved untouched). This run had already committed to
Fiedler Phase A when it started; the Woodbury repair is the natural
next run.

**Active slice (run 1, 2026-08-18): audit and finish the uncommitted
Fiedler Phase A milestone — DELIVERED.** Operator direction pinned
this run to finishing only: audit the existing Fiedler module and QA
changes, preserve unrelated work (the untracked Woodbury proposal,
`scripts/next-steps`), directly build the changed Lean modules and the
closest QA consumer, run the standard hygiene checks and the full
`lake build`, update only the corresponding records; no new proposal,
no commit.

**Audit outcome:** the Lean/QA/umbrella/index/proposal records are
mutually consistent — 57 Fiedler QA declarations, 16 explicit axioms,
25 QA modules, all re-derived from source (scoreboard regeneration
byte-identical). Exactly one defect was found and repaired: the
radar's subject-axis-4 **score cell** still read `3.0` while its own
trailing prose, the README snapshot, this plan, the proposal delivery
record, and the activity log all recorded the protocol re-score to
`3.5` — the cell is now synced to the recorded decision (README and
radar agree again). No Lean changes were needed: direct elaboration of
`GraphTheory.Fiedler` and `Fiedler_QA` is clean (zero errors, zero
warnings), targeted `lake build` of both targets ✔, `lint_axioms`
(16), `check_citations`, `check_markdown_links` pass, and the full
`lake build` succeeds ("Build completed successfully"; the 22
Scaffold-side notes are the documented pre-existing linter notes in
untouched committed modules — none in the two new Fiedler files —
plus Mathlib-package `docPrime` notes from recompiled Mathlib residue,
the known pruned-cache environment debt). Unrelated working-tree
changes preserved; nothing committed. The Fiedler Phase A milestone is
closed as delivered.

**Active slice (run 1, 2026-08-18): repair and retire the Woodbury
identity axiom — the High item — DELIVERED.** Selected from
`proposals/README.md`'s Active priority table (its High entry at run
start). The admitted `woodbury_identity` was verified false
(`A=1, U=V=1, C=0` in the scalar case: every stated determinant
hypothesis holds while the two sides evaluate to `1` and `0`), so this
was a correctness repair of the trust base, not a leverage bet:
`GraphTheory/Dynamics.lean` names this exact identity as its intended
future consumer, and a false axiom inherited there would fail exactly
the way `cheeger_lower_bound`'s old shape did — after something was
built on it. Explicit axiom count **16 → 15**.

**Delivered** (all per the proposal's scope; `sherman_morrison` stays
admitted, out of scope): (1) the axiom replaced by a theorem at the
same name with the standard middle factor `C⁻¹ + V A⁻¹ U` and exactly
the three `IsUnit …det` hypotheses — the old `IsUnit (A + U C V).det`
was *dropped as derivable* (a deliberate strengthening beyond the
proposal's sketch: Mathlib's `invertibleAddMulMul` constructs the
sum's `Invertible` instance from the middle one); (2) the proof is
pure upstream reuse — `Matrix.invOf_add_mul_mul` plus the
`NonsingularInverse` bridges `invertibleOfIsUnitDet` /
`invOf_eq_nonsing_inv`, all reachable through the module's existing
imports (zero new axioms, zero `sorry`, no wrapper, no deprecated
compatibility declaration — it would restate a falsehood; zero
consumers existed); (3) QA `Scaffold/QA/Core/MatrixUpdates_QA.lean`
(the first Core-domain QA file, 8 declarations): the retired shape
negated at its own `Fin 1`/`ℚ` statement and refuted *without consuming
any axiom* (`old_woodbury_identity_refuted_QA`), the old middle and sum
hypotheses separately proved *satisfied* at the counterexample (the
refutation is of a genuinely applicable statement), the corrected
`IsUnit C.det` hypothesis proved to exclude that counterexample, and
positive instances at scalars (`(2+3)⁻¹ = 1/5`) and at a non-scalar
rank-one update (`diag 2 2` + all-ones rank one = `!![3,1;1,3]`, both
sides computed to `!![3/8,-1/8;-1/8,3/8]` through the computed middle
`(1+1)⁻¹ = 1/2`), the theorem-consumed right sides pinned against
independently computed left sides. Computational route recorded in the
proposal: `Matrix.inv` is not `decide`-evaluable (kernel reduction
sticks on `Ring.inverse`); 1×1 inverses go through
`Matrix.inv_eq_left_inv` cancellation, 2×2 through the adjugate
formula. (4) Records: both indexes, scoreboard (15/443/0, milestone
bullet, verification rows), radar (axiom-minimization re-scored
4.0 → 4.5 per protocol — the first retirement motivated by verified
falsity rather than unprovedness; QA count 443/26; proved-depth text
extended), README (15 axioms, 443 QA), proposal delivery record, and
`proposals/README.md` (moved to Delivered; the operator's mid-run
additions — Courant–Fischer High, Sherman–Morrison/Perron–Frobenius
rows — preserved).

**Next milestone (open):** the operator's new High item —
`proposals/prove-courant-fischer.md` (general Courant–Fischer min–max;
four named downstream consumers); or the Sherman–Morrison retirement
(Medium, now unblocked and the cheapest retirement in the backlog);
Fiedler Phase B stays Medium and decision-gated.

**Active slice (run 1, 2026-08-18): prove the general Courant–Fischer
min–max — DELIVERED.** Selected from `proposals/README.md`'s Active
priority table (top High item). The proposal's open next step — survey
the pin for the dimension-intersection lemma — resolved affirmatively
before committing: `Submodule.finrank_sup_add_finrank_inf_eq`,
`Finset.exists_subset_card_eq`, `finrank_span_eq_card` (Fintype-family
form), `Fintype.linearIndependent_iff`, `Module.finrank_pi`,
`Submodule.ne_bot_iff` all present in v4.14.0. Pure hard crust — **no
axiom changes (count stays 15**; general min–max was never admitted).

**Delivered in `GraphTheory.Spectral`** (new `CourantFischer` section):
the general-`k` multiplicity pins as public center API
(`card_filter_eigvalOf_lt_evals_le`: at most `k` eigenbasis indices
strictly below `evals k`; `succ_le_card_filter_eigvalOf_le`: at least
`k+1` at or below — the count-form generalizations of the `k = 1` pins
behind `lambda2_variational`, via new private sorted-list workhorses
plus a multiset-transfer bridge); the orthonormal-family tools
(`eigvecOf_dotProduct`, `linearIndependent_eigvecOf_finset`,
`finrank_span_eigvecOf_finset`); the component-form Rayleigh bounds
(`rayleigh_le_evals_of_forall_dotProduct_eq_zero`,
`evals_le_rayleigh_of_forall_dotProduct_eq_zero` — the Rayleigh
quotient as an eigenvalue-weighted average through the proved spectral
resolution `quadForm_eigvalOf` + Parseval); span-orthogonality
(`dotProduct_eigvecOf_eq_zero_of_mem_span`, via the dot-product linear
functional's kernel); and the three headline forms —
`exists_submodule_forall_rayleigh_le` (existence direction:
`Finset.exists_subset_card_eq` extraction of `k+1` below-threshold
eigenbasis vectors, dimension by orthonormality, Rayleigh bound by
components), `exists_ne_mem_rayleigh_ge_of_finrank_eq` (competitor
direction: every `(k+1)`-dimensional `W` meets the tail eigenspace
nontrivially by `finrank_sup_add_finrank_inf_eq` + `Module.finrank_pi`
dimension counting, and the intersection vector's below-threshold
components vanish), and `evals_min_max` (the packaged infimum equation,
both inequalities from the two witness forms — no compactness needed).
Only symmetry is assumed throughout — no positivity, kernel, or graph
structure (contrast `secondEval_variational`, the index-1
PSD-plus-kernel instance). The four named consumers remain separate
follow-ons, per the proposal.

**QA** `SpectralGraph/CourantFischer_QA.lean` (33 declarations, 476
total): the `!![2,1;1,2]` fixture's spectrum `[1,3]` pinned from
trace/determinant/sortedness independent of the theorem; the competitor
direction instantiated on a hand-checked line; the existence direction
at `k = 1` yielding — through `Submodule.eq_top_of_finrank_eq` — the
derived universal "every Rayleigh quotient ≤ top eigenvalue", with the
competitor witness then pinned to attain `evals 1 = 3` exactly through
both directions; negative witnesses: the existence-direction property
refuted on the wrong line (`3 ≤ 1`), the dimension hypothesis proved
load-bearing (conclusion false on a one-dimensional subspace at index
`1`), and at the interior index `k = 1 < n−1` on the three-vertex path
Laplacian a wrong two-dimensional subspace refuted (`4/3 ≤ evals 1`
vs. the theorem-derived `evals 1 ≤ 1`) with the older
`secondEval_le_rayleigh` engine cross-checking the same bound.

Docs updated: scoreboard (15/476/0, milestone bullet, count sync),
radar (subject axis 3 re-scored 3.5 → 4.0 per protocol with the
milestone recorded; QA-axis count synced 476/27 with the new QA kind
described; proved-depth text extended), README (axis-3 cell, 476 QA,
maturity prose), SGT index map (new `Spectral` rows), proposal
delivery record, and `proposals/README.md` (moved to Delivered; no
High items remain — note added for the next run's selection).

**Next milestone (open):** no High item remains in the priority table.
Candidates: the Sherman–Morrison retirement (Medium, cheapest remaining
axiom retirement); the min–max theorem's named consumers as separately
scoped runs (interlacing retirement via min–max over shared test
subspaces; full Rayleigh/Dirichlet monotonicity through the now-proved
attained characterization); Fiedler Phase B (Medium, decision-gated);
the electrical definiteness residual; the `evals (c • M)` excavation.

**Active slice (run 1, 2026-08-18): retire the Sherman–Morrison axiom —
DELIVERED.** The Medium item `proposals/retire-sherman-morrison.md`
(the named cheapest remaining axiom retirement, unblocked by the
Woodbury repair), scope items 1–6 only. Explicit axiom count **15 →
14**; no new axioms, no `sorry`.

**Finding recorded before any edit, per the proposal's acceptance
criteria:** this was a **proof task, not a correctness repair** — the
statement was verified correct against the corrected Woodbury shape
first (at `C = [1]` the rank-one middle factor is exactly the scalar
denominator `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)`; the Woodbury `C`/`C⁻¹` defect is
invisible at rank one). The theorem keeps the axiom's exact name,
hypotheses, and statement; zero consumers existed, so no migration
surface.

**Route (as proposed, through Scaffold's own proved Woodbury theorem):**
`woodbury_identity` at `k = Fin 1` with `C = 1`; the packing lemma
`U * V = Matrix.of fun i j => u i * v j` (`Fin.sum_univ_one`, not
`rfl`, exactly as the proposal calibrated); the middle factor
identified with the 1×1 matrix of the scalar denominator (through
`Matrix.dotProduct_mulVec`); `hM` from `hv` via `Matrix.det_fin_one`;
the middle inverse via `Matrix.inv_eq_left_inv` + `inv_mul_cancel₀`;
the final entrywise↔matrix shape matched by the pin's
`Matrix.mul_smul`/`Matrix.smul_mul` algebra. Mathlib survey recorded:
`Matrix.inv_one` does *not* exist in the pin — `(1)⁻¹ = 1` derived via
`inv_eq_left_inv`. **Load-bearing:** the specialization consumes the
repaired Woodbury theorem, so a residual defect in that repair would
surface here rather than pass beside it.

**QA** `QA/Core/MatrixUpdates_QA.lean` (+4 declarations, 12 in file,
480 total): positive instance at the existing `A2 = diag 2 2` fixture
with `u = v = ![1,1]` — the update `!![3,1;1,3]`'s true inverse
`!![3/8,-1/8;-1/8,3/8]` computed independently by the adjugate formula
(`sherman_morrison_sum_inv_QA`), and the theorem-consumed right side
pinned to the same value with the denominator computed to `1` from the
definitions (`sherman_morrison_rhs_QA`); negative witness at the
excluded denominator — `A = !![1]`, `u = ![2]`, `v = ![-1/2]` attains
`v ⬝ᵥ (A⁻¹ *ᵥ u) = -1` exactly
(`sherman_morrison_excluded_denominator_QA`) and the update is the
singular zero matrix there (`sherman_morrison_singular_witness_QA`).

**Docs:** module docstring and theorem documentation, both indexes
(`higham_matrix_updates` retirement note + status; `perturbation` map
row marked proved), scoreboard (14/480/0, milestone bullet,
verification rows, QA-file count 8 → 12), radar (axiom-minimization
trend extended to 26 → … → 14 with the Core update-identity bridge now
axiom-free; QA-axis count synced 480/27 with the new QA kind
described), README (14 axioms, 480 QA), `proposals/README.md` (moved
to Delivered), and the proposal's delivery record. The operator's
concurrent working-tree changes (`.gitignore`, the two clean-room
proposal files, untracked `cdx-clean-assess.md` and
`proposals/clean-room-sgt-lemma-science-map.md`, the mushy-center
priority row) preserved untouched.

**Next milestone (open):** no High item remains. Candidates: the
remaining Medium items (Fiedler Phase B — needs its named operator
decision; the mixing-time program); the min–max theorem's named
consumers as separately scoped runs (interlacing retirement via
min–max over shared test subspaces; full Rayleigh/Dirichlet
monotonicity); the electrical definiteness residual; the `evals (c • M)`
excavation.

**Active slice (run 1, 2026-08-18): retire the Cauchy interlacing axiom
— the min–max theorem's first named consumer — DELIVERED.** Selected
from the center-out queue: `eigen_interlacing_principal_submatrix` was
one of the 14 remaining admitted axioms and the Courant–Fischer
proposal's first named consumer; retiring it both shrank the trust
surface (**14 → 13**) and made the brand-new min–max engine carry real
weight — its proof would fail if `evals_min_max`'s two witness
directions or the multiplicity pins were wrong (load-bearing growth,
per strategy §Load-bearing). Pre-check recorded: the statement is the
textbook two-sided window `λᵢ(M) ≤ μᵢ(B) ≤ λ_{i+d}(M)` and is true as
stated (the derivable `hn` aside) — a **pure proof task**, like
Sherman–Morrison, not a correctness repair. At unchanged
name/hypotheses/statement; zero consumers existed, so no migration
surface.

**Route (delivered as scoped, per the proposal's warning that the
subspace-intersection step is extra work):** the extend-by-zero padding
bridge `padVec`/`padVecLinear` (`↥S → ℝ` into `V → ℝ`) with proved
preservation of dot products (`dotProduct_padVec_self`), quadratic
forms (`quadForm_padVec`, no symmetry needed), and hence Rayleigh
quotients (`rayleigh_padVec`); lower bound via the CF existence
direction on the submatrix + `Submodule.map` image + the CF competitor
direction on the ambient; upper bound via the CF existence direction on
the ambient at index `i + d` + the dimension count
`finrank (U ⊓ range pad) ≥ i + 1` (the same
`Submodule.finrank_sup_add_finrank_inf_eq` + `Module.finrank_pi`
pattern the CF proof itself used — the proposal's warned extra step) +
exact-dimension extraction `exists_submodule_finrank_eq_of_le` (span
of `k` basis vectors, meeting the competitor direction's
equality-shaped hypothesis) + the comap dimension transfer
`finrank_comap_eq_of_le_range`. Pin survey recorded before proving:
`LinearEquiv.finrank_eq`, `LinearMap.finrank_range_of_inj`,
`finrank_span_eq_card`, `Module.finBasis`,
`Submodule.equivMapOfInjective` all present in the pin; one new import
(`Mathlib.Algebra.Module.Submodule.Range`, for `LinearMap.mem_range`).

**QA** `SpectralGraph/Interlacing_QA.lean` (+4 public declarations,
484 total): the `K₂` Laplacian spectrum `[0, 2]` and its
singleton-(`{0}`)-submatrix spectrum `[1]` both pinned from
trace/determinant/sortedness independent of the theorem; the theorem
instantiated to the **strict window `0 ≤ 1 ≤ 2`** (all three values
computed); and the negative witness — both collapsed one-sided bounds
(`μ₀ ≤ λ₀`, `λ₁ ≤ μ₀`) refuted in proved form, so the two-sided window
shape itself is witnessed. This supersedes the axiom-era note that no
thin QA of the inequality existed: computational eigenvalue QA
machinery (delivered with the Cheeger repair) did not exist when that
note was written.

Docs updated: module docstring and section header (Spectral.lean now
carries **zero** `axiom` declarations), scoreboard (13/484/0 +
milestone bullet + verification rows), radar (subject axis 2 evidence:
interlacing proved; assurance axiom-minimization trend
26 → … → 13; QA count 484/27; proved-depth and downstream-reuse text —
the retirement is the min–max engine's first *proof-level* consumer),
README (13 axioms, 484 QA, maturity bullet), Horn–Johnson source index
(interlacing row → theorem, §4.2 general min–max row added), SGT index
map (padding-bridge definitions + proved-status annotations), Mathlib
coverage map (interlacing now locally proved though still absent
upstream), Courant–Fischer proposal delivery note, and
`proposals/README.md` (additive record; the operator's concurrent
electrical-flow High item preserved untouched and acknowledged as the
next run's milestone).

**Next milestone (open):** the operator's new High item —
`proposals/electrical-flow-routing.md` (electrical flows, Thomson's
principle, Rayleigh monotonicity; step 0 is its representation/Mathlib
survey, per the operator's own indexing note). Or the remaining
Mediums (Fiedler Phase B, decision-gated; mixing-time step 1) and the
min–max engine's other named consumers (full Rayleigh/Dirichlet
monotonicity — now cheaper through the delivered padding bridge).

**Active slice (run 1, 2026-08-19): electrical-flow routing steps 0
and 1 — representation pinned and Kirchhoff conservation delivered —
DELIVERED.** Selected from `proposals/README.md`'s Active priority
table (its High entry at run start). Per the proposal's own operating
instructions: step 0 ran first (the pinned Mathlib re-surveyed; the
representation choice, zero-edge semantics, and target module recorded
in the proposal *before any Lean*), then the one Lean build step —
step 1. Zero new axioms (count stays 13); steps 2–5 (energy
agreement, Thomson, Rayleigh monotonicity, the ICP example) were
**not** started this run.

**Step 0 (survey and representation decision, recorded in the
proposal):** the pin has no network-flow/circulation/max-flow API
anywhere, no graph-native divergence (its only `Divergence` files are
the box/measure-integral divergence *theorems* on continua), no
electrical-network API (the `Rayleigh` hits are number theory and the
Rayleigh *quotient*), and the one oriented-edge type
`SimpleGraph.Dart` carries no flow/energy API and would force
`supportGraph` conversions with no upstream consumer — the matrix
representation `EdgeFlow V = Matrix V V ℝ` was pinned exactly as the
proposal sketched (conductance orientation; support as `IsFlowOn`'s
second conjunct; the ordered-pair `1/2` factor reserved for
`flowEnergy` in step 2), in a new focused module
`GraphTheory.ElectricalFlow` importing `Electrical` (keeps the
resistance module bounded; the flow interface has its own growth
path). Coverage map's electrical row re-surveyed with the
flow/divergence specifics (same absence verdict).

**Step 1 delivered** (all proved, `GraphTheory.ElectricalFlow`):
`electricalCurrent` (Ohm's law `A i j * (f i − f j)`), `flowDivergence`
(net outflow `∑ j, θ i j`), the predicates `IsFlowOn` (antisymmetry +
zero-conductance support — the guard against the proposal's named
zero-conductance trap) and `IsUnitFlow` (divergence exactly the unit
demand `e u − e v`),
`electricalCurrent_antisymm` (symmetry load-bearing),
`electricalCurrent_eq_zero_of_weight_eq_zero` (support,
unconditional), the **Kirchhoff bridge**
`flowDivergence_electricalCurrent`
(`flowDivergence (electricalCurrent A f) = laplacian A *ᵥ f` — a
one-line load-bearing consumer of the center's exact sign convention
`laplacian_mulVec_apply`), `isFlowOn_electricalCurrent`, and the
headline `isUnitFlow_electricalCurrent`: every unit-demand potential
induces a valid unit flow — the potential-based resistance API becomes
a routing object.

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (16 declarations, 500
total, 28 modules): `K₂` — current matrix `!![0,1;-1,0]`, divergence
`![1,-1]`, both computed from the raw definitions independently of the
bridge, plus the unit-flow instantiation through the headline theorem;
3-path — unit flow `0 → 1 → 2` with the internal vertex's divergence
computed to `0` (Kirchhoff conservation away from source/sink) and
nothing on the non-adjacent pair; **negative witnesses for both
proposal-named traps** — the asymmetric network `!![0,2;1,0]` where
the current provably fails antisymmetry (`2 ≠ 1`: `A.IsSymm`
load-bearing), and the edgeless-network phantom `!![0,1;-1,0]` which
satisfies antisymmetry *and* the unit divergence yet is excluded by
`IsFlowOn`'s support conjunct alone (dropping it would admit a unit
flow on a network with no edges; the energy-level refutation is
deferred to step 2 with `flowEnergy`).

**Docs updated:** umbrella (new import), scoreboard (500/13/0,
verification rows, milestone bullet), radar (QA-axis count 500/28 with
the new QA kind; subject axis 6 evidence extended and the score
**held at 3.0** per protocol — the axis rises with Thomson/Rayleigh,
which this interface exists to carry; proved-depth text), README
snapshot (umbrella list, 500 QA, date), SGT index map (new
`ElectricalFlow` section), coverage map (electrical row re-survey),
proposal step-0 decision + step-1 delivery record, and
`proposals/README.md` progress note (the operator's uncommitted
interlacing-table edit preserved untouched).

**Next milestone (open):** proposal step 2 — flow energy
(`flowEnergy` with the explicit zero branch and the mandatory `1/2`
ordered-pair factor), the energy agreement
`flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`
(load-bearing on the `1/2` conventions in both the current energy and
`laplacian_quadForm`), and its QA double-counting fixture; then steps
3–4 (Thomson, Rayleigh monotonicity) as separate runs. Or the
remaining Mediums (Fiedler Phase B, decision-gated; mixing-time step
1).

**Active slice (run 1, 2026-08-19): electrical-flow step 2 — flow
energy and the energy agreement — DELIVERED.** The Active priority
table's top High item (electrical-flow routing), continuing its
recorded next milestone. Scope held to the proposal's one-step rule:
steps 3–5 (Thomson, Rayleigh, the ICP example) were **not** started.
All proved, **no new axioms** (count stays 13).

**Delivered in `GraphTheory.ElectricalFlow`:** `flowEnergy` exactly as
the proposal pinned it — explicit zero branch (`if A i j = 0 then 0
else θ i j ^ 2 / A i j`), summed over ordered pairs, halved for double
counting; the **energy agreement**
`flowEnergy_electricalCurrent` (`flowEnergy A (electricalCurrent A f)
= quadForm (laplacian A) f` — termwise Ohm's-law algebra on the
nonzero branch, zero-on-zero on the branch, then `laplacian_quadForm`;
load-bearing on the `1/2` convention in *both* sums);
`flowEnergy_nonneg` (squares over positive conductances — the base
order fact steps 3–4 compare flows by); and the step-2 headline
`flowEnergy_electricalCurrent_eq_effectiveResistance` (on a connected
graph, a unit-demand current dissipates exactly the resistance it
routes — agreement composed with the crust's solution-level energy
identity and the total-function agreement theorem).

**Statement-shape deviation (recorded in the proposal):** the
agreement landed at **symmetry-only** strength — the proposal's
"must use nonnegative weights" is satisfied by the explicit zero-branch
handling; the nonzero-branch algebra `(c x)²/c = c x²` is pure field
algebra. QA witnesses both sides of the claim: the agreement
instantiates on a symmetric negative-weight network (both sides `-1`)
where `flowEnergy_nonneg` — which does hypothesize nonnegativity —
provably fails (energy `-1 < 0`).

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (+25 declarations, 41 in
file, 525 total): energies `1`/`2` computed from the raw `flowEnergy`
definition on `K₂`/`P₃`, each cross-checked against the independently
computed Dirichlet energies and pinned resistance values (three routes
meeting at each number); the **mandatory double-counting fixture** —
raw ordered-pair sum computes to `2 ≠ 1` = Dirichlet energy, so
omitting the `1/2` factor would numerically break the agreement; the
step-1 phantom's deferred energy pinning (`0` on the edgeless
network); the **zero-energy competitor** — on a real edge plus an
isolated vertex, an antisymmetric unit-divergence flow routing through
zero-conductance pairs dissipates `0 < 1` = the real resistance and is
excluded by `IsFlowOn`'s support conjunct alone (over
flows-satisfying-everything-except-support, Thomson's step-3 statement
would assert `1 ≤ 0` on this fixture); and the hypothesis-set witness
above. Fixture note recorded: all-zero-row matrices use the repo's
entrywise-`if` definition pattern (the matrix notation's zero-function
normalization leaves `vecTail` leftovers otherwise).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings (one new `omit` clause for `flowEnergy_nonneg`);
`lake build` of both targets ✔; full `lake build` ✔; all 28 QA
modules batch-elaborated with zero errors (only the documented
pre-existing linter notes in untouched modules); `lint_axioms` (13
covered), `check_citations`, `check_markdown_links` pass; scoreboard
regenerated (525/13/0) and idempotent.

**Docs updated:** scoreboard (525/13/0, milestone bullet, verification
rows, reviewed date), radar (QA-axis count 525/28 with the step-2 QA
kind described; subject axis 6 evidence extended with the score **held
at 3.0** per protocol — an identity, not a new inequality; proved-depth
text), README snapshot (umbrella cell, 525 QA), SGT index map (4 new
`ElectricalFlow` rows, section re-titled), proposal step-2 delivery
record + statement-shape deviation, and `proposals/README.md` progress
note (the operator's uncommitted sparsification-split table rows
preserved untouched).

**Next milestone (open):** proposal step 3 — **Thomson's principle**
(`effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit
flow `θ`, via the electrical current as the minimizer and
`flowEnergy_nonneg` on the divergence-free difference; the proposal
suggests splitting out the discrete integration-by-parts lemma if it
deserves a reusable interface); then steps 4–5 (Rayleigh monotonicity
in conductance form — orientation recorded as binding — and the ICP
capacity-reinforcement example). Or the remaining High items: Foster
Phase A (pseudoinverse-free eigenbasis route, needs its own
statement-shape spike) or the decidable-certificates Step 0
(convention decision + ℚ-kernel `decide` spike, both scoped in the
proposal).

**Active slice (run 1, 2026-08-19, IN PROGRESS): electrical-flow step
3 — Thomson's principle.** Selected from `proposals/README.md`'s
Active priority table (the electrical-flow High item, mid-program at
its recorded next step). Scope per the proposal's one-step rule: the
minimum-energy inequality over valid unit flows, stated as the
universal `effectiveResistance A u v ≤ flowEnergy A θ` (no `sInf`
packaging), plus QA (attainment at the electrical current; a strict
competitor witness). Steps 4–5 are NOT started this run.

**Active slice (run 1, 2026-08-19): electrical-flow step 3 —
Thomson's principle — DELIVERED.** The Active priority table's top
High item at its recorded next step; one-step rule held (steps 4–5 —
Rayleigh monotonicity and the ICP example — NOT started). All proved,
**no new axioms** (count stays 13).

**Delivered in `GraphTheory.ElectricalFlow`:** the flow-space
plumbing (`flowDivergence_sub` — divergence is linear;
`isFlowOn_sub` — the flow space is linear); the **divergence-free
superposition lemma**
`flowEnergy_add_of_flowDivergence_eq_zero` (a zero-divergence flow
perturbation of a current adds exactly its own energy — the discrete
integration-by-parts step, split out as its own reusable interface per
the proposal's suggestion); and the headline
`effectiveResistance_le_flowEnergy` (**Thomson's principle**: every
valid unit flow dissipates at least the resistance it routes — the
electrical current is the energy minimizer). Route exactly as
proposed: the competitor minus the unit-demand current is a flow with
zero divergence (Kirchhoff bridge + the demand equation — load-bearing
on the center's sign convention), the superposition lemma kills the
cross term (Ohm's law reduces it to `∑ i j, (f i − f j) * d i j`;
row sums vanish by zero divergence, column sums are the negated row
sums by antisymmetry), `flowEnergy_nonneg` discards the remainder, and
the step-2 identity evaluates the current's energy as the resistance.
**Statement-shape deviation (recorded in the proposal):** the
superposition lemma is stated with **no hypotheses on `A`** — not even
the symmetry the proposal's sketch assumed; only the perturbation's
flow properties enter. No `sInf` packaging, per the proposal's
explicit instruction.

**QA** `SpectralGraph/ElectricalFlow_QA.lean` (+18 declarations, 59 in
file, 543 total): the new triangle `K₃` fixture (the smallest network
with two parallel routes — unit flows non-unique) with the
unit-demand potential `![1, 1/3, 2/3]`, resistance `2/3`, and the
**split current** (`2/3` direct, `1/3` per path edge) whose energy
attains `2/3` from the raw definitions; the **detour competitor** (a
valid `IsUnitFlow` routing around the two-edge path, every conjunct
computed, energy `2`) with Thomson instantiated as the *strict* bound
`2/3 < 2` — the inequality is not vacuous on a network with competing
routes; the superposition decomposition composed as `2 = 2/3 + 4/3`
(all three energies computed independently of the lemma); and edge
attainment (`1 ≤ 1` with both values independently pinned). Fixture
note: the triangle and detour matrices use the entrywise-`if` pattern
(the matrix notation's zero-function normalization trap, already
recorded in step 2).

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings; `lake build` of both targets ✔; full `lake
build` ✔ (2180 targets); all twenty-eight QA modules batch-elaborated
with zero errors; `lint_axioms` (13 covered), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (543/13/0) and
idempotent. Radar re-scored per protocol (the recorded reservation —
"the axis is reserved to rise with Thomson/Rayleigh" — fired):
subject axis 6 **3.0 → 3.5** with the milestone recorded in the
re-score log; QA-axis count synced 543/28 with the step-3 QA kind
(triangular variational witnesses) described; proved-depth text
extended. Umbrella unchanged (module already in it); SGT index map
(4 new `ElectricalFlow` rows, section re-titled), README snapshot
(axis-6 cell 3.5, 543 QA), scoreboard verification rows + milestone
bullet, proposal step-3 delivery record + statement-shape deviation,
and `proposals/README.md` progress note updated.

**Next milestone (open):** proposal step 4 — **Rayleigh monotonicity
in conductance form** (`A ≤ B` entrywise ⇒ `effectiveResistance B u v
≤ effectiveResistance A u v`, both graphs connected symmetric
nonnegative; route per the proposal: the `A`-electrical unit flow as
competitor on `B`, its `B`-energy at most its `A`-energy since every
denominator increased, Thomson on `B` closes; the orientation is
binding — conductances, not resistances — and QA plan item 2, the
capacity increase `1 → 1/2` fixture, belongs there); then step 5 (the
ICP capacity-reinforcement example). Or the remaining High items:
Foster Phase A (pseudoinverse-free eigenbasis route, needs its own
statement-shape spike) or the decidable-certificates Step 0 (convention
decision + ℚ-kernel `decide` spike, both scoped in the proposal).

## Ready queue

1. ~~Proposal step 6 — the one-sided Dirichlet bound~~ — delivered
   above (program complete). Still open, cheap: the definiteness
   residual `R u v = 0 ↔ u = v` (reachable pair; the natural completion
   of nonnegativity, reusing the step-2 zero-energy ⇒ constant
   argument).

1. Citation hygiene — completed 2026-08-17 (see Active milestone and Last
   verified state); Chung provenance corrected, Weyl/Davis–Kahan fidelity
   notes added, DK hypothesis tightened, `spectral_gap_stability` proved
   from Weyl (axioms 19 → 18).
2. Establish the first broad-SGT backlog — delivered 2026-08-17 as
   `docs/6_SGT_BACKLOG.md` with its top item implemented
   (`GraphTheory.RandomWalk`); next backlog item: irregular normalized
   adapters.
3. Do not let retained applications or compatibility packages determine the
   next SGT milestone.
4. `spectral_persistence` retain-or-deprecate — decided 2026-08-17:
   deprecated with a migration note (zero non-QA consumers; derived
   chain covers the motivating use), retained through the compatibility
   window; removal is a later release decision. Do not extend its
   theorem family.
5. Re-admit removed subgaussian statements (moment growth, linear
   combinations, centering, sums) only when a consumer names them.

## Last verified state

- 2026-08-19 (decidable-certificates steps 0–1: convention decision +
  ℚ-decide spike + the `GraphTheory.Expander` discrepancy core, no
  axiom change): `lake env lean` on `GraphTheory.Expander` and on
  `QA.SpectralGraph.Expander_QA` — both zero errors, zero warnings
  (targeted `omit` clauses; two targeted
  `set_option linter.unnecessarySeqFocus false in` lines on the
  cross-term lemmas per repo precedent); `#print axioms` on all seven
  public theorems — only `propext, Classical.choice, Quot.sound`;
  `lake build Scaffold.Mathlib.GraphTheory.Expander` and
  `Scaffold.QA.SpectralGraph.Expander_QA` ✔; full `lake build` ✔
  (2182 targets); all thirty QA modules elaborated directly in one
  batch (zero errors — only the documented pre-existing linter notes
  in untouched modules); 647 QA declarations (+22 in `Expander_QA`),
  no `sorry`/`admit` anywhere under `Scaffold/`; 13 explicit cited
  axioms (unchanged — pure hard crust); all hygiene scripts pass
  (`lint_axioms` 13 covered, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (647/13/0) and
  idempotent after the prose edits; radar QA-axis count synced 647/30
  with the axis **held at 4.0** per protocol (hold recorded); README,
  SGT index map, proposal Step-0/Step-1 records, and
  `proposals/README.md` updated. The Step-0 spike artifacts were
  scratch files (removed after the outcomes were recorded in the
  proposal); environment recovery: mathlib interpreted cache fetch +
  explicit `lake build Batteries` (the fetch does not restore
  Batteries' modules needed by `Mathlib.Tactic`) + full build. The
  operator's concurrent untracked files (`adversarial.md`,
  `sgt-gaps.md`, `why-sgt.md`) preserved untouched. Nothing committed.

- 2026-08-19 (electrical-flow step 3: Thomson's principle, no axiom
  change): `lake env lean` on `GraphTheory.ElectricalFlow` and on
  `QA.SpectralGraph.ElectricalFlow_QA` — both zero errors, zero
  warnings (five no-`Fintype`/`DecidableEq`-needed lemmas silenced with
  `omit` clauses); `lake build
  Scaffold.Mathlib.GraphTheory.ElectricalFlow` and `lake build
  Scaffold.QA.SpectralGraph.ElectricalFlow_QA` ✔; full `lake build` ✔
  (2180 targets); all twenty-eight QA modules elaborated directly in
  one batch (zero errors — the only outputs are the documented
  pre-existing linter notes in untouched modules); 543 QA declarations
  (+18 in `ElectricalFlow_QA`, 59 in file), no `sorry`/`admit` anywhere
  under `Scaffold/` (textual matches are prose in comments/docstrings);
  13 explicit cited axioms (unchanged — pure hard crust; Thomson is
  proved from the step-1 Kirchhoff bridge, flow-space linearity, the
  superposition lemma, `flowEnergy_nonneg`, and the step-2 energy
  identity — an error in any would break the proof rather than pass
  beside it); all hygiene scripts pass (`lint_axioms` 13 covered,
  `check_citations`, `check_markdown_links`); scoreboard regenerated
  (543/13/0) and idempotent after the prose edits; radar re-scored per
  protocol (subject axis 6: 3.0 → 3.5 — the recorded reservation for
  Thomson fired — with the milestone in the re-score log; QA-axis count
  synced 543/28 with the step-3 QA kind; proved-depth text extended;
  weakest-axes paragraph updated), README snapshot (axis-6 cell 3.5,
  543 QA — a surgical count/score sync inside the operator's
  uncommitted rewrite, which is otherwise preserved untouched), SGT
  index map (4 new `ElectricalFlow` rows), proposal step-3 delivery
  record + statement-shape deviation (superposition lemma stated with
  no hypotheses on `A`), and `proposals/README.md` progress note
  updated. Nothing committed.

- 2026-08-19 (electrical-flow step 2: flow energy and the energy
  agreement, no axiom change): `lake env lean` on
  `GraphTheory.ElectricalFlow` and on
  `QA.SpectralGraph.ElectricalFlow_QA` — both zero errors, zero
  warnings (one new `omit` clause on `flowEnergy_nonneg`; the
  module's three step-1 clauses unchanged); `lake build
  Scaffold.Mathlib.GraphTheory.ElectricalFlow` and `lake build
  Scaffold.QA.SpectralGraph.ElectricalFlow_QA` ✔; full `lake build` ✔
  (2180 targets); all twenty-eight QA modules elaborated directly in
  one batch (zero errors — the only outputs are the documented
  pre-existing `unusedSectionVars` notes in untouched modules); 525 QA
  declarations (+25 in `ElectricalFlow_QA`, 41 in file), no
  `sorry`/`admit` anywhere under `Scaffold/` (textual matches are
  prose in comments/docstrings); 13 explicit cited axioms (unchanged —
  pure hard crust; the energy agreement and its corollaries are proved
  from `laplacian_quadForm`, the crust's solution-level energy
  identity, and the total-function agreement theorem); all hygiene
  scripts pass (`lint_axioms` 13 covered, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (525/13/0) and
  idempotent after the prose edits; radar (QA-axis count synced
  525/28 with the step-2 QA kind; subject axis 6 evidence extended,
  score held at 3.0 per protocol with the hold recorded in the
  re-score log; proved-depth text extended), README snapshot, SGT
  index map, proposal step-2 delivery record + statement-shape
  deviation, and `proposals/README.md` progress note updated. The
  operator's uncommitted changes (`proposals/README.md` sparsification
  split rows, untracked `icebox/` and
  `proposals/spectral-graph-sparsification.md`) preserved untouched;
  nothing committed.

- 2026-08-19 (electrical-flow steps 0–1: representation decision +
  Kirchhoff conservation, no axiom change): `lake env lean` on
  `GraphTheory.ElectricalFlow` and on
  `QA.SpectralGraph.ElectricalFlow_QA` — both zero errors, zero
  warnings (the three no-`Fintype`-needed lemmas silenced with `omit`
  clauses); `lake build Scaffold.Mathlib.GraphTheory.ElectricalFlow`
  and `lake build Scaffold.QA.SpectralGraph.ElectricalFlow_QA` ✔;
  full `lake build` ✔; all twenty-eight QA modules elaborated
  directly in one batch (zero failures); 500 QA declarations (+16, the
  new `ElectricalFlow_QA`), no `sorry`/`admit` anywhere under
  `Scaffold/`; 13 explicit cited axioms (unchanged — pure hard crust;
  the flow interface is the routing plumbing the proposal's steps 2–4
  consume); all hygiene scripts pass (`lint_axioms` 13 covered,
  `check_citations`, `check_markdown_links`); scoreboard regenerated
  (500/13/0) with verification rows and the milestone bullet; radar
  (QA-axis count synced 500/28 with the new QA kind; subject axis 6
  evidence extended with the score **held at 3.0** per protocol and
  the hold recorded in the re-score log; proved-depth text), README
  snapshot, SGT index map (new `ElectricalFlow` section), coverage
  map (electrical row re-surveyed for flows/divergence, same absence
  verdict), proposal step-0 decision + step-1 delivery record, and
  `proposals/README.md` progress note updated. The operator's
  uncommitted `proposals/README.md` change (the interlacing delivery
  row moved into the Delivered table) preserved untouched; nothing
  committed.

- 2026-08-18 (interlacing retirement, axiom 14 → 13): `lake env lean`
  on `GraphTheory.Spectral` — zero errors; the new-code
  section-variable notes silenced with `omit` clauses (the remaining
  notes at lines 163/527/2291/2313 are the documented pre-existing
  ones in untouched code) — and on
  `QA.SpectralGraph.Interlacing_QA` — zero errors (its two warnings
  are pre-existing, in untouched declarations); `lake build
  Scaffold.Mathlib.GraphTheory.Spectral` and `lake build
  Scaffold.QA.SpectralGraph.Interlacing_QA` ✔; full `lake build` ✔
  (2179 targets); 484 QA declarations (+4 public: `edgeLap_evals`,
  `edgeLap_sub_evals_eq_one`, `interlacing_edge_window_QA`,
  `interlacing_edge_window_strict_QA`; private helpers not counted), no
  `sorry`/`admit` anywhere under `Scaffold/`; 13 explicit cited axioms
  (−1: `eigen_interlacing_principal_submatrix` retired to a proved
  theorem at unchanged name/hypotheses/statement, proved from the
  locally proved Courant–Fischer engine through the padding bridge and
  the subspace-intersection dimension count — a pure proof task per the
  recorded pre-check, not a correctness repair); all hygiene scripts
  pass (`lint_axioms` 13 covered, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (13/484/0) and
  idempotent after the manual prose edits; radar (axis-2 evidence
  updated to proved; axiom-minimization trend → 13; QA 484/27;
  proved-depth and reuse text), README (13 axioms, 484 QA), both
  index files, coverage map, proposal delivery note, and
  `proposals/README.md` updated. The operator's concurrent
  working-tree additions (`proposals/electrical-flow-routing.md` — now
  the active High item and the next run's milestone — and its priority
  row) preserved untouched.

- 2026-08-18 (Sherman–Morrison retirement, axiom 15 → 14): `lake env
  lean` on `Core.MatrixUpdates` and on `QA.Core.MatrixUpdates_QA` —
  both zero errors, zero warnings; `lake build
  Scaffold.Mathlib.Core.MatrixUpdates` and `lake build
  Scaffold.QA.Core.MatrixUpdates_QA` ✔ (the QA file is the module's
  only direct consumer, verified by import search); full `lake build` ✔
  (2179 targets; the Scaffold-side linter notes are the documented
  pre-existing ones in untouched modules); 480 QA declarations (+4, the
  four new public Sherman–Morrison QA lemmas; the file's private
  helpers and defs are not counted), no `sorry`/`admit` anywhere under
  `Scaffold/` (textual matches are prose in comments/docstrings); 14
  explicit cited axioms (−1: `sherman_morrison` retired to a proved
  theorem at unchanged name/hypotheses/statement — the `k = Fin 1`
  specialization of the proved `woodbury_identity`, a pure proof task,
  not a correctness repair, per the proposal's pre-check); all hygiene
  scripts pass (`lint_axioms` 14 covered, `check_citations`;
  `check_markdown_links` reports only 4 broken links in the operator's
  untracked `cdx-clean-assess.md`, present before this run and outside
  this milestone's scope); scoreboard regenerated (14/480/0, QA file
  count 8 → 12) and idempotent after the manual prose edits; radar
  (axiom-minimization trend 26 → 19 → 18 → 17 → 16 → 15 → 14; QA-axis
  count 480/27), README (14 axioms, 480 QA), both indexes, proposal
  delivery record, and `proposals/README.md` updated (item moved to
  Delivered). Unrelated working-tree changes (the operator's
  `.gitignore`, `proposals/clean-room-sgt-export.md`,
  untracked `cdx-clean-assess.md` and
  `proposals/clean-room-sgt-lemma-science-map.md`, and the
  mushy-center priority row in `proposals/README.md`) preserved
  untouched; nothing committed.

- 2026-08-18 (general Courant–Fischer min–max proved, no axiom
  change): `lake env lean` on `GraphTheory.Spectral` — zero errors,
  zero new warnings (the one new-code linter note was silenced with an
  `omit` clause; the remaining notes are the documented pre-existing
  ones in untouched code) — and on
  `QA.SpectralGraph.CourantFischer_QA` — zero errors, zero warnings;
  `lake build Scaffold.Mathlib.GraphTheory.Spectral` and `lake build
  Scaffold.QA.SpectralGraph.CourantFischer_QA` ✔; full `lake build` ✔
  (2179 targets); all twenty-seven QA modules elaborated directly in
  one batch (zero failures); 476 QA declarations (+33, the new
  `CourantFischer_QA`), no `sorry`/`admit` anywhere under `Scaffold/`
  (textual matches are prose in comments/docstrings); 15 explicit
  cited axioms (unchanged — pure hard crust; general min–max was never
  admitted); all hygiene scripts pass (`lint_axioms` 15 covered,
  `check_citations`, `check_markdown_links`); scoreboard regenerated
  (15/476/0) with the milestone bullet and count sync; radar re-scored
  per protocol (subject axis 3: 3.5 → 4.0 recorded; QA-axis count
  synced 476/27; proved-depth text extended); README snapshot (axis-3
  cell 4.0, 476 QA); SGT index map (new `Spectral` rows); proposal
  delivery record; `proposals/README.md` (moved to Delivered with the
  four named consumers explicitly open; note added that no High item
  remains). Unrelated working-tree changes (the operator's
  `scripts/opencode-pursue` and `scripts/test_opencode_pursue.sh`
  modifications) preserved untouched.

- 2026-08-18 (Woodbury repair and retirement, axiom 16 → 15): `lake
  env lean` on `Core.MatrixUpdates` and on
  `QA.Core.MatrixUpdates_QA` — both zero errors, zero warnings; `lake
  build Scaffold.Mathlib.Core.MatrixUpdates` ✔; full `lake build` ✔
  (2179 targets); all twenty-six QA modules elaborated directly (zero
  errors — the only outputs are the documented pre-existing linter
  notes in untouched modules); 443 QA declarations (+8, the new
  Core-domain QA file), no `sorry`/`admit` anywhere under `Scaffold/`
  (textual matches are prose in comments/docstrings); 15 explicit
  cited axioms (−1: the verified-false `woodbury_identity` retired to a
  proved theorem at the standard middle factor `C⁻¹ + V A⁻¹ U` with the
  three `IsUnit` determinant hypotheses, the sum hypothesis dropped as
  derivable, proved from Mathlib's `Matrix.invOf_add_mul_mul` plus the
  `NonsingularInverse` bridges; the old scalar shape refuted in QA with
  its hypotheses proved satisfied at the counterexample); all hygiene
  scripts pass (`lint_axioms` 15 covered, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (15/443/0) with the
  milestone bullet and verification rows; radar re-scored per protocol
  (axiom-minimization 4.0 → 4.5; QA count synced 443/26; proved-depth
  text extended); README snapshot (15 axioms, 443 QA); both indexes
  (`higham_matrix_updates` repair note; `perturbation` map row marked
  proved); proposal delivery record; `proposals/README.md` moved the
  item to Delivered while preserving the operator's concurrent
  additions (Courant–Fischer High row, Sherman–Morrison and
  Perron–Frobenius rows; the operator's `scripts/next-steps` deletion
  preserved untouched).

- 2026-08-18 (audit-and-finish of the uncommitted Fiedler Phase A
  milestone): the delivered Phase A records audited and closed. One
  record defect found and repaired: the radar's subject-axis-4 score
  cell was stale at `3.0` (every other record — the radar's own
  re-score prose, the README snapshot, this plan, the proposal
  delivery record, the activity log — recorded the protocol re-score
  to `3.5`); the cell is synced, no other content changed. No Lean
  changes: `lake env lean` on `GraphTheory.Fiedler` and
  `QA.SpectralGraph.Fiedler_QA` — zero errors, zero warnings;
  targeted `lake build` of both targets ✔; full `lake build` ✔
  ("Build completed successfully" — the 22 Scaffold-side linter notes
  are the documented pre-existing ones in untouched committed modules,
  none in the new Fiedler files; the ~2980 further notes are
  Mathlib-package `docPrime` warnings over recompiled Mathlib residue,
  the recorded pruned-cache environment debt, not Scaffold code);
  scoreboard regeneration byte-identical (435/16/0 re-derived from
  source); `lint_axioms` (16 covered), `check_citations`,
  `check_markdown_links` pass. Unrelated working-tree changes
  (untracked `proposals/repair-and-retire-woodbury.md`,
  `scripts/next-steps`) preserved untouched; nothing committed.

- 2026-08-18 (Fiedler Phase A: vector, algebraic connectivity, sign
  partition): `lake env lean` on `GraphTheory.Fiedler` and on
  `QA.SpectralGraph.Fiedler_QA` — both zero errors, zero warnings;
  `lake build Scaffold.Mathlib.GraphTheory.Fiedler` and
  `lake build Scaffold.QA.SpectralGraph.Fiedler_QA` ✔; full `lake
  build` ✔ (2179 targets — the new module in the umbrella); all
  twenty-five QA modules elaborated directly in one batch (zero
  failures; the only diagnostics are the documented pre-existing
  linter notes in untouched modules); 435 QA declarations (+57), no
  `sorry`/`admit` anywhere under `Scaffold/` (the only textual matches
  are prose in comments); 16 explicit cited axioms (unchanged — pure
  hard crust); all hygiene scripts pass (`lint_axioms`,
  `check_citations`, `check_markdown_links`); scoreboard regenerated
  (435/16/0) with verification rows and the milestone bullet; radar
  re-scored per protocol (subject axis 4: 3.0 → 3.5, recorded; QA-axis
  count synced 435/25; proved-depth and reuse text extended); README
  snapshot (axis-4 cell); SGT index map (new `Fiedler` section);
  backlog item 4; proposal delivery record; `proposals/README.md`
  (Fiedler → Medium). Concurrent additions preserved untouched
  (untracked `proposals/repair-and-retire-woodbury.md` and its
  priority-table row, which appeared mid-run).

- 2026-08-18 (audit-and-finish of the uncommitted normalized-Cheeger
  milestone): no source changes — re-verification of the delivered
  `cheeger_upper_bound` retirement and closure of the milestone's
  records. Direct elaboration (`lake env lean`) of
  `GraphTheory.Spectral`, `GraphTheory.Cheeger`, and
  `QA.SpectralGraph.Cheeger_QA` — zero errors (Cheeger QA zero
  warnings; remaining linter notes verified pre-existing in HEAD,
  outside the diff hunks); explicit `lake build` of the three targets
  ✔; full `lake build` ✔ (2178 targets); `lint_axioms` (16 covered),
  `check_citations`, `check_markdown_links` pass; scoreboard
  regeneration byte-identical (16/378/0 re-derived from source;
  Cheeger QA 33); activity log's 6 self-introduced
  trailing-whitespace metadata lines stripped (older entries'
  illustrative hard breaks untouched); unrelated working-tree changes
  preserved; no commit.

- 2026-08-18 (`cheeger_upper_bound` retirement: Cheeger easy direction
  proved, axiom 17 → 16): `lake env lean` on `GraphTheory.Spectral`
  and `GraphTheory.Cheeger` (zero errors; only pre-existing linter
  notes in untouched code) and on `QA.SpectralGraph.Cheeger_QA`
  (zero errors, zero warnings); `lake build
  Scaffold.Mathlib.GraphTheory.Spectral` and
  `lake build Scaffold.Mathlib.GraphTheory.Cheeger` ✔; full `lake
  build` ✔ (2178 targets); all
  twenty-four QA modules elaborated directly in one batch (exit 0,
  zero failures); 378 QA declarations (+7), no `sorry`/`admit`
  anywhere under `Scaffold/` (textual matches are prose in comments);
  16 explicit cited axioms (−1: `cheeger_upper_bound` retired to a
  proved theorem at identical name/hypotheses/statement, proved from
  the new general-operator `secondEval_variational` with
  `lambda2_variational` re-proved as a corollary at unchanged shape);
  all hygiene scripts pass (`lint_axioms`, `check_citations`,
  `check_markdown_links`); scoreboard regenerated (16/378/0) with
  verification rows and a milestone note; radar re-scored per protocol
  (subject axis 4: 2.5 → 3.0; axiom-minimization trend recorded; QA
  count synced 378/24; proved-depth and reuse text updated); README
  snapshot (16 axioms, 378 QA, axis-4 cell); both Cheeger indexes;
  backlog item 3; `proposals/README.md` (proposal → Delivered with
  residuals) and the proposal's delivery record updated. Unrelated
  concurrent working-tree changes (`.opencode/`, `AGENTS.md`,
  `scripts/opencode-pursue`, `scripts/README.md`,
  `proposals/sell-the-methodology.md`,
  `proposals/retire-the-mushy-center.md`,
  `scripts/test_opencode_pursue.sh`, untracked `proposals/README.md`)
  were preserved untouched.

- 2026-08-18 (`lambda2_variational` retirement: proved Courant–Fischer,
  axiom 18 → 17): `lake env lean` on `GraphTheory.Spectral` (zero
  errors; zero new warnings — the seven pre-existing linter notes are
  untouched code) and on `QA.SpectralGraph.Variational_QA` (zero
  errors); `lake build Scaffold.QA.SpectralGraph.Variational_QA` ✔;
  full `lake build` ✔ (2178 targets); all twenty-four QA modules
  elaborated directly in one batch (zero failures); 371 QA
  declarations (+26), no `sorry`/`admit` anywhere under `Scaffold/`
  (textual matches are prose in comments); 17 explicit cited axioms
  (−1: `lambda2_variational` retired to a proved theorem restated with
  the load-bearing `hnonneg` hypothesis); all hygiene scripts pass
  (`lint_axioms`, `check_citations`, `check_markdown_links`);
  scoreboard regenerated (17/371/0) with prose synced; radar re-scored
  per protocol (subject axis 3: 3.0 → 3.5; axiom minimization 3.5 →
  4.0; QA count synced 371/24); README snapshot (17 axioms, 371 QA);
  both source indexes and the SGT index map updated; both proposals'
  status notes updated with the delivery and the normalized-instance
  scope caveat.

- 2026-08-18 (electrical-crust step 6: one-sided Dirichlet bound,
  program complete): `lake env lean` on `GraphTheory.Electrical` and on
  `QA.SpectralGraph.EffectiveResistance_QA` — both zero errors, zero
  warnings; `lake build Scaffold.QA.SpectralGraph.EffectiveResistance_QA`
  ✔ (2012 targets); full `lake build` ✔ (2178 targets); all twenty-four
  QA modules elaborated directly in one batch (zero errors — the only
  outputs are pre-existing `unusedSectionVars` warnings in untouched
  modules); 345 QA declarations (+9), no `sorry`/`admit` anywhere under
  `Scaffold/` (the only textual matches are prose in comments); 18
  explicit cited axioms (unchanged — pure hard crust); all hygiene
  scripts pass (`lint_axioms`, `check_citations`,
  `check_markdown_links`); scoreboard regenerated and its prose synced;
  SGT index map (4 new `Electrical` rows), backlog item 7, radar
  (subject axis 6: 2.5 → 3.0 recorded per protocol; QA-axis count
  synced to 345/24), README snapshot, and proposal checklist (all six
  steps ✅) updated.

- 2026-08-18 (electrical-crust step 5: effective resistance): `lake
  env lean` on `GraphTheory.Electrical` and on
  `QA.SpectralGraph.EffectiveResistance_QA` — both zero errors, zero
  warnings; `lake build Scaffold.QA.SpectralGraph.EffectiveResistance_QA`
  and `lake build Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter`
  (downstream consumer of the changed dependency chain) ✔; full `lake
  build` ✔ (2178 targets — the new module in the umbrella); all
  twenty-four QA modules elaborated directly in one batch (exit 0,
  zero failures); 336 QA declarations (+17), no `sorry`/`admit`
  anywhere under `Scaffold/` (the only textual matches are prose in
  comments and the `Scaffold/Trusted/README.md` quarantine
  explanation); 18 explicit cited axioms (unchanged — pure hard
  crust); all hygiene scripts pass (`lint_axioms`, `check_citations`,
  `check_markdown_links`); scoreboard regenerated; SGT index map
  (new `Electrical` section), backlog item 7, radar (subject axis 6:
  2.0 → 2.5, recorded per protocol), README snapshot, and proposal
  checklist updated (steps 1–5 of 6 delivered).

- 2026-08-18 (electrical-crust step 4: potential solvability): `lake
  env lean` on `GraphTheory.Spectral` (zero errors, zero new warnings —
  the eight pre-existing linter notes are untouched code) and on
  `QA.SpectralGraph.PotentialSolvability_QA` (zero errors, zero
  warnings); `lake build Scaffold.QA.SpectralGraph.PotentialSolvability_QA`
  and `lake build Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter` (a
  downstream consumer of the changed module) ✔; full `lake build` ✔
  (2177 targets); all twenty-three QA modules elaborated directly in
  one batch (exit 0, zero failures); 319 QA declarations (+12), no
  `sorry`/`admit` anywhere under `Scaffold/`; 18 explicit cited axioms
  (unchanged — pure hard crust); all hygiene scripts pass
  (`lint_axioms`, `check_citations`, `check_markdown_links`);
  scoreboard regenerated; SGT index map, backlog item 7, radar (subject
  axis 6: 1.5 → 2.0, recorded), README snapshot, and proposal
  checklist updated. Environment note: ~300 Mathlib oleans were found
  pruned at run start (recorded environment debt); the modules needed
  by the changed files, their consumers, and the full default build
  were all present and used — no cache fetch was required this run.

- 2026-08-18 (electrical-crust step 3: kernel-equality bridge):
  `lake env lean` on `GraphTheory.Spectral` (zero errors; zero *new*
  warnings — the pre-existing linter notes are untouched code) and on
  `GraphTheory.SimpleGraphAdapter` and
  `QA.SpectralGraph.KernelBridge_QA` (both zero errors, zero
  warnings); `lake build Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter`
  ✔; full `lake build` ✔ (2177 targets); all twenty-two QA modules
  elaborated directly in one batch (exit 0, zero failures); 307 QA
  declarations (+14), no `sorry`/`admit` anywhere under `Scaffold/`;
  18 explicit cited axioms (unchanged — pure hard crust); all hygiene
  scripts pass (`lint_axioms`, `check_citations`,
  `check_markdown_links`); scoreboard regenerated; SGT index map,
  backlog item 7, radar (subject axis 6: 1.0 → 1.5, recorded), and
  proposal checklist updated.

- 2026-08-18 (SimpleGraph→WAdj adapter): `lake env lean` on
  `GraphTheory.SimpleGraphAdapter` and on
  `QA.SpectralGraph.SimpleGraphAdapter_QA` — both zero errors, zero
  warnings; `lake build` of both targets ✔; full `lake build` ✔
  (2177 targets); all twenty-one QA modules built directly in one
  batch (exit 0); 293 QA declarations (+38), no `sorry`/`admit`
  anywhere under `Scaffold/`; 18 explicit cited axioms (unchanged —
  pure hard crust); `lint_axioms`, `check_citations`,
  `check_markdown_links` pass; scoreboard regenerated; SGT index map,
  backlog item 7, radar (interop 4.0 → 4.5, models 3.0 → 3.5,
  recorded), and README snapshot/maturity synced. Environment: pruned
  `.lake/build` restored via the recorded interpreter cache fetch +
  2008-target residue recompile before checks.
- 2026-08-18 (electrical-crust step 1: connectivity/kernel): `lake env
  lean` on `GraphTheory.Spectral` (zero errors; zero *new* warnings —
  the six pre-existing linter notes are untouched code) and on
  `QA.SpectralGraph.Connectivity_QA` (zero errors, zero warnings);
  `lake build Scaffold.Mathlib.GraphTheory.Spectral` and
  `lake build Scaffold.QA.SpectralGraph.Connectivity_QA` ✔; full
  `lake build` ✔ (2171 targets); 255 QA declarations (15 new), no
  `sorry`/`admit` anywhere under `Scaffold/`; 18 explicit cited axioms
  (unchanged — pure hard crust); all hygiene scripts pass
  (`lint_axioms`, `check_citations`, `check_markdown_links`);
  scoreboard regenerated; SGT index map, backlog item 7, and radar
  updated with recorded re-scores (subject axis 6: 0.5 → 1.0, subject
  axis 1: 2.5 → 3.0, assurance Mathlib interop: 3.5 → 4.0).
- 2026-08-18 (Cheeger statement-shape repair): `lake env lean` on
  `GraphTheory.Spectral`, `GraphTheory.Cheeger`, and
  `QA.SpectralGraph.Cheeger_QA` pass with zero errors and zero
  warnings; all nineteen QA modules and the changed public modules
  built directly; full `lake build` passes (2161 targets); 240 QA
  declarations (19 new), no `sorry`/`admit`; 18 explicit cited axioms
  (unchanged); both Cheeger axioms restated at the corrected
  `secondEval (L_sym)` spectral side with the old shape refuted in
  proved form; radar QA axis re-scored 3.5 → 4.0 (recorded); all
  hygiene scripts pass; scoreboard, radar, `index/map/spectral_graph`,
  and `index/sources/chung_spectral_graph` updated.
- 2026-08-17 (variational transfer / second interface consumer):
  direct elaboration and `lake build` of
  `Scaffold.Mathlib.GraphTheory.VariationalTransfer` and
  `Scaffold.QA.SpectralGraph.VariationalTransfer_QA` pass clean; full
  `lake build` passes with the module in the umbrella (1997 targets);
  221 QA declarations (15 new), no `sorry`/`admit`; 18 explicit cited
  axioms (unchanged — pure hard crust); radar reuse 3.5 → 4.0 and
  subject axis 3 (variational) 2.5 → 3.0 recorded; all hygiene scripts
  pass; SGT index map updated.
- 2026-08-17 (exhaustive/falsification QA): `lake build` passes; direct
  elaboration and `lake build` of
  `Scaffold.QA.SpectralGraph.Exhaustive_QA` pass with zero errors and
  zero warnings; 206 QA declarations (87 new), no `sorry`/`admit`; 18
  explicit cited axioms (unchanged — pure hard crust); exhaustive
  decide-certified cut sweeps on both fixtures, duality recomposed from
  computed tables, negative witnesses (conductance `1/2` vs `1`,
  Rayleigh `8/3` vs `0`, asymmetric duality failure `2 ≠ 1`), walk row
  sums computed; radar QA re-scored 3.0 → 3.5 (recorded); all hygiene
  scripts pass.
- 2026-08-17 (walk-Laplacian kernel / RandomWalk consumer): `lake
  build` passes; 119 QA declarations, no `sorry`/`admit`; 18 explicit
  cited axioms (unchanged); `Stationary` consumes both interface
  modules; radar reuse 3.0 → 3.5 recorded; all hygiene scripts pass.
- 2026-08-17 (stationary structure): `lake build` passes with
  `GraphTheory.Stationary` in the umbrella; twenty public modules and
  seventeen QA modules (116 declarations) compile directly with no
  `sorry`/`admit`; 18 explicit cited axioms (unchanged); downstream
  reuse radar score 2.5 → 3.0 recorded; all hygiene scripts pass.
- 2026-08-17 (cut duality): `lake build` passes; 107 QA declarations
  (new `SpectralGraph/Cuts_QA.lean`), no `sorry`/`admit`; 18 explicit
  cited axioms (unchanged); cut duality proved in the center
  (`vol_compl`, `boundary_compl`, `conductance_compl`,
  `boundary_empty`, `boundary_univ`); all hygiene scripts pass.
- 2026-08-17 (irregular walk form): `lake build` passes; 96 QA
  declarations, no `sorry`/`admit`; 18 explicit cited axioms (unchanged);
  general `walkTransitionMatrix` with row-stochasticity, `walkLaplacian`,
  and the similarity identity `√D · L_walk · (1/√D) = L_sym` proved;
  all hygiene scripts pass.
- 2026-08-17 (irregular normalized Laplacian): `lake build` passes with
  `GraphTheory.Normalized` in the umbrella; nineteen public modules and
  fifteen QA modules (93 declarations) compile directly with no
  `sorry`/`admit`; 18 explicit cited axioms (unchanged — pure hard
  crust); `lint_axioms`, `check_citations`, `check_markdown_links` all
  pass.
- 2026-08-17 (broad-SGT backlog + random-walk interfaces): `lake build`
  passes with `GraphTheory.RandomWalk` in the umbrella; eighteen public
  modules and fourteen QA modules (82 declarations) compile directly
  with no `sorry`/`admit`; 18 explicit cited axioms (unchanged — the
  increment is pure hard crust); `lint_axioms`, `check_citations`,
  `check_markdown_links` all pass; `docs/6_SGT_BACKLOG.md` published and
  linked.
- 2026-08-17 (citation hygiene + tightening): `lake build` passes;
  explicit axioms reduced 19 → 18 (`spectral_gap_stability` now proved
  from `weyl_inequality`); `davis_kahan_sin_theta` separation tightened
  to the single-pair two-cluster form (derived wrapper simplified to one
  Weyl fact; QA reduces the pairwise form via `evals_sorted`); Chung
  index provenance note corrected against git history; Weyl doc records
  the norm-corollary relation; `lint_axioms`, `check_citations`,
  `check_markdown_links` all pass; 75 QA declarations, no `sorry`/`admit`.
- 2026-08-17 (projector algebra): `lake build` passes; all seventeen
  public modules and all thirteen QA modules (75 declarations) compile
  directly with no `sorry`/`admit`; eigenbasis orthonormality
  (`eigvecOf_inner`) and completeness (`eigvecOf_complete`) proved from
  the Mathlib spectral-theorem API; `spectralProjector_idempotent`,
  `initialProjector_idempotent`, `spectralProjector_eq_zero`,
  `spectralProjector_eq_one` proved; new QA
  file `SpectralGraph/Projector_QA.lean` (5 declarations).

## Blockers

- The native Mathlib cache executable fails on this macOS environment with a
  dyld segment error. Cached artifacts were obtained through the recorded Lean
  interpreter workaround; this is environment debt, not an SGT source failure.
