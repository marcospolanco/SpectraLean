# Proposal: The Graph-Layer Singles' Positive Pins

**Status:** COMPLETE (delivered 2026-09-07, run `20260907T134207Z-run-1`,
session `ses_f840b32f9ffeQquR0Tn6QqpJwb`; delivery record below).

The consumption census's named next batch (the prior terminal handoff's
own words: "the named-weight singles … and the cheap structural
entry-level pins are the natural next batch"), executed as one sweep:
seven of the ten never-touched singles (inert set 21, per
`wip/census_20260907_post12.txt`), all in the deterministic graph
layer, each receiving its first genuine QA consumption at delivered
fixtures — the pins method's eleventh application.

## Why these seven

- **`isEffectiveResistance_unique`** (Electrical) — the strategy
  document's own example of load-bearing content
  (`docs/1_STRATEGY.md` § Load-bearing growth cites the kernel
  characterization as the exactness pillar of resistance
  well-definedness). Never consumed: the file pinned existence, the
  value function, and the metric, but never the uniqueness theorem's
  forcing step.
- **`IsMultiwayPartition.covers`** (Multiway) — the partition
  structure's covering field, never applied to an instance.
- **`randomWalkLaplacian_symmetric`** (RandomWalk) — the walk
  Laplacian's symmetry, never instantiated.
- **`degreeMatrix_diagonal_nonneg`** (Spectral) — this file already
  carries the SIGNED-INPUT KILL (`sfNegEdge`); the positive
  instantiation completes the fence/pin pair.
- **The `edgeWeight` degenerate-set trio** (`edgeWeight_empty_left`,
  `edgeWeight_empty_right`, `edgeWeight_univ_right`, Expander) — the
  Expander-mixing layer's bookkeeping edges, never consumed.

Out of scope, recorded deliberately: the probability trio
(`indepFun_indicator_coord`, `hoeffding_iid`, `bernstein_iid`) — one
shared-fixture batch that deserves its own run on the Bernoulli/iid
machinery; `l_infty_norm_nonneg` (Core.Norms) — no existing QA module
imports `Core.Norms`, so the pin needs its own QA file, overhead
disproportionate to one entry-level lemma until a second Core pin
exists; the Band/Normalized pairs (scope decisions already recorded in
`heat-irreducible-pairs-pins.md`); the AlonBoppana/Expander-cluster/
Azuma helper-shaped remainders.

## The pins (14 QA declarations across five files, QA 6713 → 6727)

**EffectiveResistance_QA.lean (`SinglesPins`, 3):** the shifted
potential `![2, 1] = ![1, 0] + onesVec` proved to solve the same unit
demand through `laplacian_ones_in_kernel` (the exact mechanism the
uniqueness proof identifies as the only freedom); **the two-route
headline** — both potentials certify resistances (at genuinely
different-looking voltage differences), and
`eru_edge_uniqueness_twoRoute` derives their equality THROUGH
`isEffectiveResistance_unique`, with the raw arithmetic beside it
(both `1`).

**MultiwayCheeger_QA.lean (`SinglesPins`, 2):** `covers` consumed at
the K₂ singleton partition (witnesses from the structure field); the
raw self-membership companion.

**RandomWalk_QA.lean (`SinglesPins`, 2):** symmetry through the
theorem at `d = 2` — deliberately OFF the fixture's degree, so the
entries carry the genuine `1/2` scaling — with the `(1, 0)` entry
derived from `(0, 1)` through the theorem against the raw value
`−1/2`.

**Spectral_QA.lean (`SinglesPins`, 4):** the weight-`2` edge fixture
`sdpAdj` (symmetric nonnegative); the raw diagonal `2`; the positive
pin through the theorem — the value-carrying companion to the file's
existing signed kill at `sfNegEdge`.

**Expander_QA.lean (`SinglesPins`, 4):** the degenerate-cut trio at
`C₄` — empty source, empty target, and the value-carrying
`edgeWeight_univ_right` (the singleton's cut weight = its degree
`2`), with the raw double-sum companion.

## Delivery record (2026-09-07)

**Delivered at the full designed scope** — all seven singles consumed,
14 QA declarations, zero axiom contact (`#print axioms` via
`wip/gspins_axcheck.lean` on all 14 — every one exactly `propext,
Classical.choice, Quot.sound`).

**Verification.** Spike-first (`wip/gspins_spike.lean` — green after
four fix rounds; traps recorded: `isEffectiveResistance_unique`'s
implicit `{r s}` unify against the GOAL before the hypotheses are
checked, so the hypothesis ORDER swaps — pass the goal-LHS instance
first; `MultiwayCheeger_QA`'s namespace is `.MultiwayQA`, not `.QA`;
`fin_cases` splits where `simp` closes one branch need explicit
bullets — the `<;> norm_num` continuation both errors (`no goals`) on
the closed branch and draws the `unnecessarySeqFocus` warning
otherwise; singleton-Finset sums under `simp [expCycleAdj4_deg]`
reduce to `1 + 1 = 2` and need the trailing `norm_num`). All five
landed modules elaborate with literally zero output
(errors/warnings/infos). Explicit builds ✔. Full `lake build` +
`check_build_completeness.py` — 135/135 fresh, 0 stale, 0 missing,
exit 0. `lint_axioms` exit 0 (4 axioms unchanged).
`check_refutation_independence` (24-tag clean).
`check_public_reachability` (63 modules). `check_citations`.
`check_markdown_links`. `check_qa_name_uniqueness` (the new
`eru_*`/`mwp_*`/`rwp_*`/`sdp*`/`exw_*` names collision-free).
`check_backlog_freshness` clean. Scoreboard regenerated (1376 / 6727 /
4 / 0) with the verification row. Map freshness exit 0 after the 6727
sync in both map data tables + SVG regeneration (49 stations, no
status change — none owed). **Consumption closure verified by the
tool**: the census re-run (`wip/census_20260907_post13.txt`, diffed
against `post12`) shows exactly the 7 targeted theorems leaving the
inert set — 1353 → 1360 value-consumed, 21 → 14 never-touched, no
bonus, no collateral.

**Remaining risk:** none owed — QA-only, no axiom disposition changed,
no public statement changed. Honest scope: the uniqueness two-route at
one edge fixture; the covers pins at the K₂ singleton partition; the
symmetry entry read at one off-degree choice; the diagonal pin at one
fixture; the degenerate-cut trio at `C₄` only. The deferred items stay
recorded above.
