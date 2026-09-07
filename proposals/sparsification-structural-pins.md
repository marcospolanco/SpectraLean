# Proposal: The Sparsification Structural Lemmas' Positive Pins

**Status:** COMPLETE (delivered in the opening run, run
`20260907T040424Z-run-1`, session `ses_f8684723effefqlJShDqrQZ0l1`;
delivery record below)

## Why this, why now

The compiler-derived consumption census's largest remaining inert
cluster (per `wip/census_20260907_post.txt`, 59 never-touched): **the
sparsification design's nine structural lemmas** — the
sampled-Laplacian machinery under `matrix_bernstein`'s one real
theorem consumer (`Derived.SparsificationTail`), never themselves
consumed by QA. This is the third application of the pins method (the
census → targeted first-consumption loop, after Tikhonov's 11 and the
mixing-time interfaces' 10) and its first matrix-level target: the
lemmas assert structural properties (symmetry, idempotence, PSD, norm
bound, independence) of the objects the sparsification pipeline is
built from, and the prior QA pinned the pipeline's scalar statistics
(leverage, integrals, variance) around them without touching them.

**SGT leverage:** the sampled Laplacian is the object behind the
library's one admitted-axiom consumer chain on the sparsification
axis; its structural spine was unexercised. The pins put weight on
every layer: the eigen-coordinate projector, the sampling design
(probability, weight, summand, measure), and the graph-coordinate
sampled operator — including a computed VALUE that exercises the
weights, the `1/2` ordered-pair factor, and `rankOne` together.

## Step 0: the census (exact)

The nine never-consumed theorems:
`imageProjector_isSymm`, `imageProjector_mul_self`,
`quadForm_imageProjector_nonneg`, `l2OpNorm_imageProjector_le`,
`ssSampled_isSymm`, `indepFun_ssSummand`, `ssWeight_nonneg`,
`ssLaplacian_isSymm`, `quadForm_ssLaplacian_nonneg`.

## Step 1: the pins (15 QA theorems, one section)

All at the delivered `spK2` fixture, at the natural unsaturated
budget `q = 1` (pair probability `p = min 1 (1·1/2) = 1/2`;
inverse-probability weights exactly `2` at the kept outcome, `0` at
the missed one):

1. **The projector four**: symmetry with the off-diagonal entry
   equality derived THROUGH the theorem (`spp_proj_symm_QA`);
   idempotence with the diagonal entries' squaring read through the
   theorem — each diagonal entry is `0` or `1`, eigen-index dependent,
   and both square to themselves (`spp_proj_idem_QA`); the PSD at the
   unit vector (`spp_proj_quad_nonneg_QA`); the operator-norm bound
   (`spp_proj_norm_QA`).
2. **The sampling design four**: the sampled operator's symmetry at
   every outcome (`spp_sampled_symm_QA`); the two distinct ordered
   pairs' summand independence at the design's own measure — the
   matrix-concentration `h_indep` clause's design fact
   (`spp_summand_indep_QA`); the weight's nonnegativity at both
   outcomes THROUGH the theorem, made nontrivial by the pinned values
   (`spp_weight_nonneg_QA` with `spp_weight_true_QA = 2`,
   `spp_weight_false_QA = 0`, and the probability/weight companions
   `spp_prob_half_QA`, `spp_prob_half_swapped_QA`,
   `spp_weight_true_swapped_QA`).
3. **The sampled Laplacian three**: symmetry at every outcome
   (`spp_lap_symm_QA`); PSD at the kept outcome and alternating
   vector (`spp_lap_quad_nonneg_QA`); and the computed VALUE
   (`spp_lap_quad_value_QA`): at the all-true outcome each
   off-diagonal pair contributes weight `2` halved by the ordered
   factor, so the sampled Laplacian is exactly TWICE the true one and
   the alternating vector's form is `2 · 4 = 8` — the diagonal pairs
   contribute zero through the vanishing voltage difference alone
   (no weight computation needed). The value is load-bearing on the
   sampled-Laplacian definition's exact shape: a wrong weight formula,
   a missing or doubled `1/2`, or a wrong `rankOne` normalization
   breaks it.

## QA obligation

The pins are the QA. No shelf change; zero axiom contact.

## Delivery record (2026-09-07)

DELIVERED at the full designed scope in the opening run: 15 QA
theorems in `Sparsification_QA.lean`'s new `StructuralPins` section
(78 → 93 by the generator metric; QA 6579 → 6594), QA-only, zero axiom
contact (`#print axioms` via `wip/sppins_axcheck.lean` on all 15 —
every one exactly `propext, Classical.choice, Quot.sound`; the 24-tag
independence check unchanged and clean).

**Consumption closure, verified by the tool**: the census re-run
(`wip/census_20260907_post2.txt`) shows exactly the 9 targeted
theorems leaving the inert set — value-consumed 1298 → 1307,
never-touched 59 → 50, no bonus, no collateral.

Verification: spike-first (`wip/sppins_spike.lean` — the nine
consumptions green in one round, the computed-value pin after two;
the recorded traps: `quadForm_finset_sum` being PRIVATE to the shelf
(the QA route is `Fintype.sum_prod_type` + a quadForm-additivity
helper on the public `Matrix.add_mulVec`/`Matrix.add_dotProduct`),
and the `Matrix.mulVec_add`/`add_mulVec` name pair — the sum-side
distributivity is `add_`, the argument-side `mulVec_add`); the landed
module elaborates with zero errors/warnings; explicit build ✔; **full
`lake build` + `check_build_completeness.py` — 135 source files, 135
fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0
(4 axioms unchanged); `check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new `spp_*`
names collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (6594) with the verification row; map freshness exit 0
after the stats sync.

Remaining risk: none owed — QA-only, no axiom disposition changed, no
public statement changed. QA proves consequences relative to the
substrate; it does not prove the substrate (no axiom touched). Honest
scope: one fixture (`K₂`), one budget (`q = 1`), the projector pins
at entry level (the diagonal VALUES are eigen-index dependent, pinned
only through the trace elsewhere).
