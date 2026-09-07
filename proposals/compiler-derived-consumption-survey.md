# The Compiler-Derived QA→Shelf Consumption Survey

**Status:** Delivered (same-run proposal + delivery record, 2026-09-06)  
**Tool:** `scripts/consumption_survey.py` (report-only; not a blocking ladder check)

## Motivation

Three consecutive terminal handoffs named the theorem-level QA-mention
survey's honest residue: every string-heuristic survey key produced
false inert-declarations somewhere (the sharp-layer audit's closure
half was caught by hand-check and recorded in
`adversarial-fences-sharp-layer-family.md`). Audit and bridge targeting
needs the answer only the elaborator can give: for a given QA
declaration, which shelf constants does its elaborated proof *actually*
depend on?

## Design

A Lean metaprogram probe (generated per run into `wip/`, elaborated by
`lake env lean`) imports the public umbrella `Scaffold` plus a
co-importable group of QA modules, then computes by memoized worklist
fixpoint over the constant graph, for every QA declaration, the SHELF
constants (`Scaffold.Mathlib.*` / `Scaffold.Derived.*` defining
modules) reachable from its elaborated VALUE and, separately, from its
TYPE. The two reports are kept separate because they are different
evidence:

- **value-edge** — the QA proof consumes the shelf constant's proof;
- **type-edge** — the QA statement exercises the shelf constant's
  interface.

The string keys conflated these; the false inerts came from exactly
that conflation.

**Why the closure is exact.** By import direction nothing in Mathlib
imports Scaffold, so the fixpoint universe is the Scaffold constants
alone; Mathlib intermediates are filtered at the edge level, not
approximated.

**Why groups.** The QA tree carries the 24 allowlisted cross-module
duplicate names (`check_qa_name_uniqueness.py`'s residual class), and a
single file importing every QA module is precisely the "future module
that imports both" whose failure mode that guard documents — the first
run of this tool hit it on `k2Adj._cstage1`. Modules are partitioned
into groups with pairwise-disjoint statically-extracted exported names;
a bisection fallback handles any extraction miss (in the delivered run
the initial 57-module group collided four times before resolving —
the fallback is load-bearing, not decorative).

## Step 0 — validation

The tool must reproduce known-true dependencies from recent
deliveries; the check is built into the script and fails loudly:

- `prC4G_top_QA` → `googleMatrix_evals_top_eq_one`
- `prCycG_second_QA` → `googleMatrix_evals_second_le`
- `prCycG_bot_QA` → `evals_sum_eq_trace`

All three reproduced (`[survey] validation: 3 known-true dependencies
reproduced`).

Hand spot-checks of the *inert* side (the exact failure mode the string
keys had):

- Every inert-theorem name was grep'd against the QA tree. All
  hits resolve into three classes: (a) **docstring mentions** — fence
  documentation naming the fenced theorem without instantiating it
  (see Finding 1); (b) **substring artifacts** (`measurable`,
  `norm_bound`, `covers`, numeric components); (c) **one near-miss** —
  `pageRankMixingTime_le_of_rate` appears in QA only through the
  PRIMED variant `pageRankMixingTime_le_of_rate'`, which the census
  correctly records as consumed while the unprimed form is inert.
- `hsm.measurable` in `PairwiseIndependence_QA.lean` is Mathlib's
  `StronglyMeasurable.measurable`, not the `MatrixMDS` projection —
  verified by reading the local context.
- Structure-literal field labels (`measurable := …` in `Matrix_QA`)
  are arguments to `MatrixMDS.mk`, not projection references — the
  projections are genuinely uninstantiated.

## The first census (2026-09-06, `main` @ 8eae073 + same-day deliveries)

8,988 QA declarations with any shelf contact; 76,218 value-edges and
25,571 type-edges.

| Shelf kind | total | value-consumed | type-only | never touched |
| --- | --- | --- | --- | --- |
| theorem/lemma (public) | 1,357 | 1,276 | 0 | **81** |
| def (public) | 182 | 179 | 0 | **3** |
| axiom | 4 | — | — | — |

Axiom QA value-consumer counts (an exactness baseline for future
retirement-impact analysis): `matrix_hoeffding` 23, `matrix_bernstein`
8, `perron_frobenius` 6, `matrix_azuma_hoeffding` 3.

Top value-consumed shelf theorems (distinct QA consumers) — the
load-bearing spine: `isHermitian_of_isSymm` 1218,
`degreeMatrix_off_diagonal` 961, `eigvecOf_inner` 899,
`degreeMatrix_diagonal` 827, `eigvecOf_complete` 708,
`eigvecOf_expansion_apply` 644, `walkTransitionMatrix_apply` 620,
`laplacian_quadForm` 577, `dotProduct_eigvecOf_mulVec` 563,
`dotProduct_eigvecOf` 552, `eigvalOf_sum_eq_trace` 511,
`laplacian_symmetric` 505, `degreeMatrix_symmetric` 505,
`supportGraph_adj` 483, `quadForm_eigvecOf_self` 447.

### The 81 never-touched shelf theorems

- `Scaffold.Derived.EdgePerturbationTail` (1): `matrix_hoeffding_quadForm`
- `Core.Norms` (1): `l_infty_norm_nonneg`
- `AlonBoppana` (3): `cycleAdj_nonneg`, `levClass_pairwise_disjoint`, `radialVec_apply`
- `Band` (2): `bandProjector_mulVec_eigvecOf_eq_zero_right`, `eq_zero_of_bandProjector_mulVec_eq_self`
- `DirectedMixing` (4): `pageRankMixingTimeFrom_anti`, `pageRankMixingTimeFrom_le_of_rate`, `pageRankMixingTime_le_of_escalation`, `pageRankMixingTime_le_of_rate`
- `EdgePerturbation` (4): `indepFun_degPerturbSummand`, `indepFun_perturbSummand`, `perturbEdgeLap_posSemidef`, `rankOne_posSemidef`
- `Electrical` (1): `isEffectiveResistance_unique`
- `Expander` (3): `edgeWeight_empty_left`, `edgeWeight_empty_right`, `edgeWeight_univ_right`
- `FunctionalCalculus` (5): `dotProduct_eigvecOf_spectralCalc_mulVec`, `magneticHeat_apply`, `magneticHeat_mulVec_eigenvectorBasis`, `spectralCalc_id`, `spectralCalc_tikhonovShrinkage_eq_smul_inv'`
- `Heat` (2): `heatKernel_decayFactor_le_one`, `normalizedHeatKernel_zero`
- `IrreducibleStationary` (2): `isIrreducible_transpose`, `pow_entry_le_one`
- `Magnetic` (6): `conj_exp_I_mul_exp_I`, `hermQuadForm_eq_zero_of_mulVec_eq_zero`, `magneticLaplacian_mulVec_eq_zero_iff`, `magneticLaplacian_mulVec_eq_zero_of_forall_exp_mul_eq`, `magneticQuadForm_im_eq_zero`, `magneticQuadForm_re_nonneg`
- `Mixing` (4): `chiSquareDistance_eq_zero_iff`, `klDiv_lazyWalkDistribution_le`, `lazyWalkDistribution_tvDistance_le_of_connected`, `walkDistribution_tvDistance_le_max_rate`
- `Multiway` (1): `IsMultiwayPartition.covers` (Prop-field projection)
- `Normalized` (2): `walkLaplacian_mulVec_eigvecOf`, `walk_eigvec_expansion`
- `Oversmoothing` (6): `lazyWalkDistribution_tvDistance_le_of_depth`, `lazyWalkMixingTimeFrom_anti`, `lazyWalkMixingTimeFrom_le_of_connected`, `walkDistribution_sub_stationaryVec_abs_le_max_rate`, `walkMixingTime_le_of_escalation`, `walkMixingTime_spec`
- `Poincare` (2): `poincare_inequality_normalized_of_connected`, `poincare_inequality_of_connected`
- `RandomWalk` (1): `randomWalkLaplacian_symmetric`
- `Signed` (4): `laplacian_mulVec_switchVec`, `signedAdj_symmetric`, `signedLaplacian_symmetric`, `switchVec_ne_zero`
- `Sparsification` (9): `imageProjector_isSymm`, `imageProjector_mul_self`, `indepFun_ssSummand`, `l2OpNorm_imageProjector_le`, `quadForm_imageProjector_nonneg`, `quadForm_ssLaplacian_nonneg`, `ssLaplacian_isSymm`, `ssSampled_isSymm`, `ssWeight_nonneg`
- `Spectral` (1): `degreeMatrix_diagonal_nonneg`
- `Tikhonov` (11): `eq_of_tikhonovObjective_eq_minimizer`, `tikhonovMinimizer_add_smul_one_mulVec`, `tikhonovMinimizer_eigvecOf`, `tikhonovMinimizer_ne_apply_self_of_eigvalOf_pos`, `tikhonovObjective_minimizer_le`, `tikhonovObjective_sub_minimizer`, `tikhonovShrinkage_le_one`, `tikhonovShrinkage_lt_one`, `tikhonovShrinkage_lt_tikhonovShrinkage`, `tikhonovShrinkage_ne_zero`, `tikhonovShrinkage_pos`
- `Azuma` (3): `MatrixMDS.cond_mean_zero`, `MatrixMDS.measurable`, `MatrixMDS.norm_bound` (Prop-field projections)
- `Bernstein` (1): `bernstein_iid`
- `Hoeffding` (1): `hoeffding_iid`
- `IIDProduct` (1): `indepFun_indicator_coord`

The 3 never-touched defs: `Core.l_infty_norm`, `Core.MRV`, `Core.RV` —
the definition-only `Core` modules the primitive-convergence survey
classified by hand; the compiler agrees.

## Findings

1. **The fenced-but-never-consumed class (≈17 of the 81).** A
   hypothesis-form fence states the would-be conclusion of the shelved
   theorem manually and derives `False` from it — the shelf constant
   never enters the proof term. This is *by design* (the fence's
   fixture breaks the theorem's hypothesis set; instantiating is
   impossible), and it is exactly where every string key lied: the
   name mention in the fence docstring read as coverage. The exact
   census separates the two evidences for the first time: fences are
   statement-level refutation records, not consumption. Notable
   members: `hoeffding_iid`, `bernstein_iid`,
   `indepFun_indicator_coord`, `heatKernel_decayFactor_le_one`,
   `randomWalkLaplacian_symmetric`, `walkLaplacian_mulVec_eigvecOf`,
   `walk_eigvec_expansion`, `isIrreducible_transpose`,
   `pow_entry_le_one`, `spectralCalc_id`, the Sparsification trio
   fenced 2026-09-05, `degreeMatrix_diagonal_nonneg`.
2. **The iid convenience wrappers are never positively pinned.**
   `hoeffding_iid` and `bernstein_iid` are fenced but never
   instantiated anywhere — the same families' base theorems
   (`hoeffding_inequality`, `bernstein_inequality`) carry real pins.
   Positive pins (a genuine i.i.d. instantiation at the delivered
   biased-product fixtures) are cheap, named candidates.
3. **Tikhonov is the least-consumed theorem family**: 11 of its ~24
   theorems never touched — the shrinkage trio alone
   (`tikhonovShrinkage_pos/_lt_one/_le_one`) is a coherent unpinned
   cluster with an existing `Tikhonov_QA.lean` fixture layer to build
   on. A natural audit/bridge target under the standing pattern.
4. **The mixing-time interfaces are designed-but-unconsumed.** The
   `*_spec` / `*_anti` / `*_le_of_*` families in `DirectedMixing` and
   `Oversmoothing` (10 theorems) have zero QA consumers — the QA pins
   the display values, not the interfaces. This is the exact-shape
   answer to the QA-axis frontier's "randomized half" question: the
   deterministic half's own interface layer is the nearer gap.
5. **`matrix_hoeffding_quadForm` — the 2026-08-30 repair's generic
   passthrough — has zero QA consumers.** Its hypothesis-matched
   forms live only in the Derived chain. A one-line instantiation
   obligation is now named.
6. **Axiom consumer counts are now exact**: any future retirement
   proposal can price its QA-blast-radius from this census instead of
   grep (the `perron_frobenius` deprecation's "who consumes it"
   question is answerable: 6 QA value-consumers).

## Counting-metric reconciliation (honesty note)

The census's 1,357 public elaborated theorem/lemma constants vs the
scoreboard's 1,359 source-regex count differ by the two metrics' known
blind spots, verified at name level on the `Spectral` module: (a) the
elaborator kind-checks Prop-structure-field projections
(`MatrixMDS.norm_bound`, `IsMultiwayPartition.covers`) as theorems —
no source `theorem` line; (b) the source regex occasionally matches
prose lines beginning with the word "theorem"/"lemma" in docstrings;
(c) private helpers (~180 by source count) are excluded from both.
No anomaly; the two numbers measure different things and agree to
within ~1.5%.

The 8,988 "QA declarations" figure counts every QA-module constant
with any shelf contact — theorems, fixtures (`def`s), private kill
engines, and generated equation helpers — a wider universe than the
scoreboard's 6,513 source-QA-theorem count by design.

## Verification

- `[survey] validation: 3 known-true dependencies reproduced` (in-script
  Step-0 block, fails nonzero on disagreement).
- Full run log: 5 initial groups, 4 bisects, 11 probe elaborations, all
  OK; census written. The edge totals (76,218 value / 25,571 type) and
  the 81-theorem inert census were identical across every run after
  the first; the gen-filter changes recorded above reclassify
  declaration KINDS only (never edges), and the final run's headline
  numbers are the reproducible reference.
- No Lean source changed; `lake build` + `check_build_completeness.py`
  re-verified after the delivery (135/135, exit 0) — see the activity
  log entry for the same run.
- Ladder re-run post-delivery: `lint_axioms`, `check_citations`,
  `check_markdown_links`, `check_qa_name_uniqueness`,
  `check_public_reachability`, `check_backlog_freshness`,
  `check_refutation_independence` — all clean (no axiom/QA/import
  surface touched; the ladder row certifies the records, not the tool:
  the tool is report-only by design).

## Technique findings (Lean 4.14 metaprogramming)

- `let mut` is illegal inside a `match` arm (term position): wrap the
  arm in `Id.run do`.
- `NameSet` is an `RBTree` in this toolchain: `.fold`, not `.foldl`;
  no `.size` — cardinality by folding a counter.
- The Handle method is `putStr` (`put` does not exist) and emits no
  terminator — record separators must be written explicitly.
- `` `?. `` is not a valid name literal; `Name.anonymous` for defaults.
- `env.getModuleIdxFor?` + `header.moduleNames` give defining modules
  including `_private.` prefixes — private-constant module attribution
  needs the `_private.<mod>.<idx>.` wrapper stripped by hand.

## Residual / next steps

- The census is a snapshot; re-run
  `python3 scripts/consumption_survey.py` after any QA or shelf
  delivery. Wiring it into the blocking ladder was deliberately
  rejected (it elaborates 11 probes, ~8 minutes — a targeting tool,
  not a check).
- The 81-name listing above is the standing target pool for audit and
  bridge selection; the highest-leverage named items are the Tikhonov
  cluster (Finding 3) and the mixing-time interface layer (Finding 4).
- The type-edge half of the census is currently carried as data (edges
  in the TSV, not summarized beyond the headline); a future interface-
  exercise report (which QA statements mention which shelf constants)
  is one aggregation away if a consumer names itself.
