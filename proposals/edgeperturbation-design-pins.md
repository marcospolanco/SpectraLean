# The Edge-Perturbation Design's Independence + PSD Positive Pins

**Status:** COMPLETE — delivered in the opening run (2026-09-07,
`20260907T073103Z-run-1`); see the delivery record below.

**Origin:** the consumption census's next cluster by size
(`wip/census_20260907_post7.txt`, inert set 35): the EdgePerturbation
module carries 4 never-touched theorems — the largest remaining cluster,
and the layer sitting directly under `matrix_hoeffding`'s one real theorem
consumer (23 QA consumers) and the scalar `hoeffding_inequality` degree
chain.

## The gap

The edge-perturbation design (`Scaffold/Mathlib/GraphTheory/EdgePerturbation.lean`)
is the sampling engine behind the delivered concentration capstones. Its
QA file evaluates the design's arithmetic extensively — variance
statistics, packaging identities, tail instances — but four of its public
theorems have never been consumed by any QA proof (census 2026-09-07,
value-closure exact):

- `indepFun_perturbSummand` — the PAIRWISE independence clause of
  `matrix_hoeffding` at the design (its docstring calls it "the two-point
  consequence, kept for the refutation records"; the mutual `iIndepFun`
  twin is consumed, this one never);
- `indepFun_degPerturbSummand` — the pairwise independence clause of
  `hoeffding_inequality` at the degree design (same story: the mutual
  twin consumed, this one never);
- `perturbEdgeLap_posSemidef` — nonnegative-weight edge blocks are PSD;
- `rankOne_posSemidef` — every rank-one symmetric matrix is PSD.

The existing QA re-derives energies and measures *beside* these
theorems (`epK2_degree_event_measure` factors the JOINT measure through
the raw coordinate independence `indepFun_coord`, never through the
design's own theorem; the PSD clause QA `epNeg_clause_QA` consumes
`perturbSummand_sq_le`, which routes through the square-of-symmetric
route and never through the rank-one PSD layer). One adjacent single
completes the cluster: `Scaffold.Derived.EdgePerturbationTail.
matrix_hoeffding_quadForm` — the generic quadratic-form passthrough added
by the 2026-08-30 centering repair — has zero consumers (the design's own
`edgePerturbation_quadForm_tail` re-derives the norm→form domination
itself rather than routing through the passthrough).

## Leverage

- The two `IndepFun` theorems are the exact `h_indep` clause shapes of the
  concentration axioms at the design; the pins factor a concrete JOINT
  measure through them (`1/2 · 1/2 = 1/4` at the `K₂` fair coin) — a wrong
  clause (e.g. independence stated at the wrong coordinates, or the
  measure name wrong) breaks the factorization loudly.
- The PSD pair is the design's semidefinite-order floor; pinning an
  ENERGY value through the theorem (not beside it) makes a sign error in
  `perturbEdgeLap`/`rankOne` fail the pin immediately.
- The passthrough pin converts the repair's generic interface from inert
  to consumed, at a numeric instance IDENTICAL to the existing
  `epK2_quadForm_tail_QA` — two interfaces, one value.

## Plan

1. Spike (`wip/eppins_spike.lean`) at the existing `epK2` fixture:
   the PSD energy pins (value-carrying inputs, non-eigenvector for the
   rank-one pin), the two joint-mass factorizations through the design's
   `IndepFun` theorems with raw `sum_coord2_mul` companions (two routes,
   one value), and the passthrough instance.
2. Land as a new `StructuralPins` section in
   `Scaffold/QA/Derived/EdgePerturbation_QA.lean`; the passthrough
   instance labeled CONDITIONAL ON the `matrix_hoeffding` axiom exactly as
   its siblings are.
3. Axiom audit (`#print axioms` on every new declaration), full ladder,
   census re-run (target: exactly 5 theorems leaving the inert set, no
   collateral).

## Delivery record (2026-09-07)

DELIVERED at the full designed scope — 16 QA declarations (14 theorems +
the `epNegEdge` and `eppEntryFiber` fixtures) in `EdgePerturbation_QA.lean`'s
new `StructuralPins` section, QA 6645 → 6661 by the generator's metric,
with the first genuine consumption of all five targets:

- **`rankOne_posSemidef`** pinned at the NON-eigenvector input
  `![1, 2]`: the raw inner product `![1,2] ⬝ᵥ epVec = 2 − ... = −1` (the
  sign flip pinned), the energy `1` computed raw at entry level, and
  `0 ≤ energy` THROUGH the theorem — a negative-definite `rankOne`
  breaks the pin exactly at the sign flip.
- **`perturbEdgeLap_posSemidef`** pinned at the `K₂` edge `(0,1)`
  (weight `1`): energy `4` raw (through the pinned edge block and the
  rank-one action), `0 ≤ energy` through the theorem — load-bearing on
  the block's sign convention and shape.
- **The `h : 0 ≤ A e.1 e.2` scope witness** (`epNegEdge` fixture): at a
  negative weight the dropped-hypothesis statement is refuted (energy
  `−4 < 0` at `epVec`) — the PSD clause's weight hypothesis is
  load-bearing exactly where the design's squared domination clause is
  sign-free.
- **`indepFun_degPerturbSummand`** pinned by factorizing the joint
  summand event `{X_{01} = 1/2} ∩ {X_{10} = 1/2}` THROUGH the theorem
  (`1/2 · 1/2`), each preimage its coordinate cylinder (the incident
  weight `1` pinned by `epK2_degWeight_facts`), masses by
  `epK2_cyl_mass`; **the raw companion** computes the SAME event by
  direct `sum_coord2_mul` arithmetic (two routes, one value `1/4`).
- **`indepFun_perturbSummand`** pinned the same way at the MATRIX
  codomain: the summands take values `±½ • rankOne epVec`, the level
  sets are the `(0,1)`-entry fibers `eppEntryFiber (∓½)` (measurable
  through `measurable_pi_apply` composed over the shelf's hand-rolled
  product σ-algebra — `MeasurableSingletonClass` does not fire through
  the `Matrix` synonym, so the entry route is the honest one, and the
  fiber membership is itself an entry-level read of the random matrix:
  the block's `(0,1)` entry is `−1`, so `X = +½ • R` lands in
  `fiber(−½)`), joint factorized through the theorem, raw companion by
  `sum_coord2_mul` at the (true, false) cylinder (again `1/4`).
- **`matrix_hoeffding_quadForm`** (the 2026-08-30 repair's
  never-consumed generic passthrough) instantiated at the full `K₂`
  design family (the `Fintype.equivFin` transport mirroring
  `edgePerturbation_norm_tail`'s assembly, every clause discharged by
  the design's own theorems: `stronglyMeasurable_perturbSummand`,
  `iIndepFun_perturbSummand`, `perturbSummand_isSymm`,
  `integral_perturbSummand_eq_zero`, `perturbSummand_sq_le`), at
  `t = 1`, `x = e₀`, with the bound collapsed through the pinned
  variance norm `8` to `4 exp(−1/16)` — the generic-route twin of the
  existing `epK2_quadForm_tail_QA` value. CONDITIONAL ON the
  `matrix_hoeffding` axiom, instantiated not re-proved (the one
  axiom-carrying declaration of the delivery, labeled as such).

**Consumption closure verified by the tool**: the census re-run
(`wip/census_20260907_post8.txt`) shows exactly the 5 targeted theorems
leaving the inert set (1332 → 1337 value-consumed, 35 → 30
never-touched, the `EdgePerturbation (4)` and
`Derived.EdgePerturbationTail (1)` lines gone, no bonus, no collateral;
`matrix_hoeffding`'s QA consumer count 23 → 24, that being the
passthrough instance itself). The pins method's seventh application.

**Spike traps recorded** (`wip/eppins_spike.lean`, green across four fix
rounds): `PosSemidef.2`'s energy clause comes at `star x` (`dotProduct
(star x) (M *ᵥ x)`) — rewrites on the unstarred form fail syntactically
while remaining defeq-true, the cure being the type-ascribed `have hv' :
0 ≤ … := hv` bridge (the same idiom `epK2_interval_fence_QA` already
used); `rw` rewrites only the FIRST of two structurally-identical `Finset
Bool` sums — the per-sum helper `hbernsum` factored out and applied
twice; the scoped `ℝ≥0∞` notation needs its `open scoped ENNReal`
(section-local in the landed module); `open scoped Classical in` must
PRECEDE the docstring of the theorem it governs; `Finset.sum_univ_bool`
does not exist in the pinned Mathlib — the shelf's `univ = {false,
true}` + `Finset.sum_insert` + `Finset.sum_singleton` chain is the
working idiom, with the `bern p e true = ofReal (p e)` side closing by
`rfl` and the `false` side needing `norm_num` (`1 − 1/2` is not
definitional); the initial count draft of "8 QA theorems / 6653" was
corrected by the regenerated scoreboard's metric to 16 / 6661.

**Verification:** spike-first; the landed module elaborates with zero
errors/warnings (the three `ring_nf` infos pre-existing at HEAD lines);
explicit build ✔; **full `lake build` +
`check_build_completeness.py` — 135/135 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` exit 0 (4 axioms unchanged);
`check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new `epp*`
names collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (**1369 / 6661 / 4 / 0**) with the verification row; map
freshness exit 0 after the 6661 sync in both map data tables + SVG
regeneration (49 stations, no status change — none owed); README
(counts + date + the highlights bullet) and the radar's QA row synced
(held 4.5). **Axiom audit** (`wip/eppins_axcheck.lean`, 16
declarations): the 15 hard-crust ones exactly `propext,
Classical.choice, Quot.sound`; the passthrough instance honestly
carrying `matrix_hoeffding`.

**Remaining risk:** none owed — QA-only, no axiom disposition changed,
no public statement changed. Honest scope: the pins are at the `K₂`
fixture and the fair coin `p ≡ ½` only; the PSD pins at one input each
(the non-eigenvector `![1,2]` chosen so the sign-flip content is
pinned); the joint-mass factorizations at one pair of level sets; the
mutual-independence twins (`iIndepFun_*`) were already consumed and are
not re-pinned.
