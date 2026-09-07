# Proposal: The Tikhonov Family's Adversarial Fence Audit and First Positive Pins

**Status:** COMPLETE (delivered across two runs: the 2026-09-06T16:06Z
run spiked and landed the QA; run `20260907T013052Z-run-1`, session
`ses_f8684723effefqlJShDqrQZ0l1`, verified the elaboration, ran the
axiom audit and full ladder, and wrote the records; delivery record
below)

## Why this, why now

The compiler-derived consumption census
(`compiler-derived-consumption-survey.md`, delivered 2026-09-06) named
this family its top audit target — the exact tool's first application
as a targeting instrument. The census found `GraphTheory.Tikhonov` the
library's least-consumed theorem family: **11 of its ~24 theorems with
zero QA value-consumers**. The pre-audit QA was not thin — it pins the
minimizer by a hand-solved linear system, the objective numerically,
the shrinkage values, mean preservation, non-idempotence — but it
*re-derives* those instantiations beside the theorems rather than
consuming them: `minimality_K2` proves `obj(x*) = 1/3 ≤ 1 = obj(y)`
by direct computation without `tikhonovObjective_minimizer_le`, and
`y_ne_min_K2` proves the vectors differ by `congrArg` on the pinned
objective values, never touching
`eq_of_tikhonovObjective_eq_minimizer` — the file header's
"consumed contrapositively" claim was aspirational, not consumption
(verified this run: the census's inert verdict on that theorem is
correct).

**SGT leverage:** two independent halves, both load-bearing on the
substrate rather than beside it:

1. **Positive pins** — the first genuine consumption of all 11 inert
   theorems. A pin that *derives a known numeric truth from the
   theorem* (rather than re-deriving it independently) fails if the
   theorem's statement or the definitions it routes through
   (`tikhonovMinimizer`, `tikhonovObjective`, the eigenbasis
   machinery) are wrong. This is the "create new load-bearing
   consumers" directive (`docs/1_STRATEGY.md` § Load-bearing growth)
   applied mechanically: the census names the unconsumed surface, the
   pins put real weight on it.
2. **Hypothesis-form fences** — the standing audit pattern's
   clause-necessity pass over the family's hypothesis surface, which
   had only the 2026-08-20 free-form `π = 0` witnesses
   (`not_minimality_pi0_K2`), never reconciled into the per-clause
   discipline.

## Step 0: the census (from the compiler-derived survey)

The 11 never-consumed theorems, by layer:

- **Shrinkage arithmetic (6):** `tikhonovShrinkage_pos`,
  `tikhonovShrinkage_ne_zero`, `tikhonovShrinkage_le_one`,
  `tikhonovShrinkage_lt_one`,
  `tikhonovShrinkage_lt_tikhonovShrinkage`,
  `tikhonovShrinkage_eq_one_iff`.
- **Matrix level (5):** `tikhonovMinimizer_add_smul_one_mulVec` (the
  *forward* normal equation — the converse
  `eq_tikhonovMinimizer_of_add_smul_one_mulVec` was consumed by
  `tik_K2_eq` at delivery), `tikhonovObjective_minimizer_le`,
  `eq_of_tikhonovObjective_eq_minimizer`,
  `tikhonovMinimizer_eigvecOf`,
  `tikhonovMinimizer_ne_apply_self_of_eigvalOf_pos`.

Unfenced load-bearing clauses (the fence targets): every `hπ`/`hlam`
clause of the shrinkage-arithmetic five; the `hπ : π ≠ 0` clauses of
the matrix family (`sum_tikhonovMinimizer_eq_sum`,
`eq_tikhonovMinimizer_of_add_smul_one_mulVec`,
`tikhonovObjective_minimizer_le`,
`eq_of_tikhonovObjective_eq_minimizer`,
`tikhonovObjective_sub_minimizer`); the `hμ : 0 < …` clause of the
non-idempotence theorem; the `hnonneg` clause of
`eigvalOf_laplacian_nonneg` (the PSD hypothesis — the whole family's
spectral ordering lives on it).

## Step 1: the positive pins (first consumption)

Eleven `tkp_` pins, most through the existing `K₂` fixture layer
(`adjK2`, `lapK2_symmetric`, `tik_K2_eq`, the objective pins):

- the shrinkage-arithmetic six at both pinned eigenvalues `{0, 2}` —
  the value pins (`1` at the kernel mode, `1/3` at the positive
  mode), the interval memberships, the strict antitonicity read
  numerically (`1/3 < 1` THROUGH the theorem, `tkp_lt_lt_value`), and
  `tikhonovShrinkage_eq_one_iff` consumed in the contrapositive
  direction (`λ = 2 ≠ 0` forces the factor off `1`);
- **the forward normal equation** (`tkp_normal`): the hand-solved
  system `normal_K2` re-derived FROM
  `tikhonovMinimizer_add_smul_one_mulVec` — the direction that had
  never been consumed (the delivery QA used only the converse
  characterization to promote the hand solution);
- **minimality through the theorem** (`tkp_minimality`) with its
  numeric reading `1/3 ≤ 1` (`tkp_minimality_value`);
- **uniqueness consumed forward** (`tkp_uniqueness`): the hand value
  `![2/3, 1/3]` recognized as *the* minimizer through the
  strict-convexity engine — a genuinely different route than the
  normal equation;
- the eigenvector-input theorem at the positive mode
  (`tkp_eigvec_shrunk`: `T v = (1/3) • v`);
- non-idempotence through the theorem (`tkp_ne_self`, consuming
  `lapK2_exists_nonzero` for the eigenvalue-`2` index).

## Step 2: the fences

Fourteen `tkf_` hypothesis-form fences plus companions and one fresh
fixture:

- **The shrinkage-arithmetic five's `hπ`/`hlam` clauses** at
  junk-free scalar fixtures wherever the kill is genuine: `pos`'s
  `hπ` at `(−2, 3)` (factor genuinely `-2`) and `hlam` at
  `(1, −2)` (factor `-1`); `ne_zero`'s `hπ` at `(0, 2)` (factor
  GENUINELY zero — `π = 0` annihilates every mode, the degenerate
  smoothing limit) and its `hlam` at the JUNK corner `(1, −1)`
  (denominator vanishes, `1/0 = 0` — recorded as junk, not dressed
  up); `le_one`'s `hπ` at `(−1/2, 1/4)` (factor `2`) and `hlam` at
  `(2, −1)` (factor `2`); `lt_one`'s `hπ` at `(−2, 1)` (factor `2`)
  and its `hlam` at the BOUNDARY `(1, 0)` (factor exactly `1`,
  genuinely, no junk — the `0 < λ` hypothesis excludes exactly the
  kernel mode, the statement-shape deviation the delivery already
  recorded); the antitonicity's `hπ` at `π = −1` (factor genuinely
  *increasing*) and `h₁` at the STRADDLE pair `(1, −3)`/`(1, 0)`
  (opposite sides of the pole `λ = −π`: factors `-1/2` and `1`, the
  claimed inequality `1 < −1/2`); `eq_one_iff`'s `hπ` at the JUNK
  corner `(0, 0)` (`0/0 = 0 ≠ 1` while `λ = 0` — the dropped `←`
  direction false).
- **The `π = 0` matrix guards**, on the general lemma
  `tik_K2_zero_gen` (the `π = 0` minimizer is the zero vector for
  EVERY signal — every junk factor is `0/λ = 0`; the general form of
  the file's existing `tik_K2_zero`): `sum_tikhonovMinimizer_eq_sum`'s
  `hπ` (filtered sum `0` vs signal sum `1`);
  `eq_tikhonovMinimizer_of_add_smul_one_mulVec`'s `hπ` with its
  kept-genuine companion `tkf_eq_min_hpi_hz` (the premise `hz` HOLDS
  at the constant vector — the Laplacian kills it — yet the constant
  is not the zero minimizer);
  `tikhonovObjective_minimizer_le`'s `hπ` — the reconciliation of the
  2026-08-20 free-form witness `not_minimality_pi0_K2` into the
  per-clause discipline; `eq_of_tikhonovObjective_eq_minimizer`'s
  `hπ` with its kept-genuine tie companion `tkf_uniq_hpi_kept` (at
  `π = 0` the objective degenerates to the fidelity term, the tie
  hypothesis is GENUINE at `x = 2y`, and uniqueness fails — the
  clearest witness that the `π ≠ 0` guard is what carries strict
  convexity); and `tikhonovObjective_sub_minimizer`'s `hπ` — the
  heaviest fence: at `π = 0` the left side is `−1` while the right
  side is Parseval's `∑ (v ⱼ ⬝ᵥ y)² = 1` (every weight `1 + λ/0`
  junk, every factor `0/λ` junk), the identity genuinely false at
  the degeneration.
- **The kernel-mode kill of the non-idempotence theorem's `hμ`**
  (`tkf_ne_self_hmu`): at an eigenvalue-`0` index the filter fixes
  its input exactly — THROUGH the eigen theorem itself
  (`tikhonovMinimizer_eigvecOf` gives `T v = shrink(1, 0) • v = v`),
  so the dropped statement's inequality is `v ≠ v`. The `0 < μ`
  hypothesis excludes exactly the kernel mode. Its `hπ` twin at
  `π = 0` (the filter is the zero map, trivially idempotent) with the
  kept-genuine companion `tkf_ne_self_hpi_hmu`.
- **The PSD clause** (`tkf_lap_nonneg_hnonneg`): at the fresh signed
  network `tkfSigned = !![0, −1; −1, 0]` (symmetry KEPT genuine —
  the clause the `hnonneg` hypothesis does not carry), the Laplacian
  `!![−1, 1; 1, −1]` has spectrum `{0, −2}` (pinned through
  trace/determinant: product `0`, sum `−2`), so the dropped
  nonnegativity conclusion fails at a genuinely negative eigenvalue.

## Priced deferrals (not delivered)

The pole-class fences for `tikhonovMinimizer_add_smul_one_mulVec`'s
`hπ`/`hnonneg` pair: the normal equation provably HOLDS at every
non-pole `π` — per mode the identity
`shrink(π, λ) · (λ + π) = π` needs only `λ + π ≠ 0` — so a kill
needs a fixture with an eigenvalue at EXACTLY `−π`, where the junk
division `π/0 = 0` makes the minimizer the kernel projector while the
normal-equation left side retains the full `λ • v` term. Two routes:
(a) the diagonal fixture `diag(−1, …)` at `π = 1` (eigenvalue `-1` at
the pole) — needs the off-pole modes kept genuine; (b) a dedicated
`K₂`-variant with a signed weight making the Laplacian's positive
mode equal `−π`. Both need care distinguishing the junk kill from a
genuine one; priced, not attempted.

## QA obligation

The pins and fences are the QA. No shelf change; zero axiom contact
(the family is all-proved hard crust; the fences are theorem
instantiations, so no `-- @refutes` tags apply).

## Delivery record (2026-09-07)

DELIVERED at the full designed scope across two runs: 48 QA
declarations in `Tikhonov_QA.lean`'s new `AdversarialFences` section
(QA 6513 → 6561; the file 54 → 102 theorems), QA-only, zero axiom
contact (`#print axioms` via `wip/tikfences_axcheck.lean` on all 48
nameable declarations — every one exactly
`propext, Classical.choice, Quot.sound`; the 24-tag independence
check unchanged and clean). The 2026-09-06T16:06Z run spiked
(`wip/tikfences_spike.lean`), landed the QA insertion, and
regenerated the scoreboard before interruption; run
`20260907T013052Z-run-1` verified the landed module's elaboration
(zero errors, zero warnings), ran the axiom audit, the full build,
and the complete ladder, and wrote this record.

Consumption closure: with the `tkp_` pins landed, the census's 11
never-consumed Tikhonov theorems all have genuine QA value-consumers
— the family leaves the least-consumed rank. (The census itself is a
snapshot; re-run it to refresh the ranking.)

Verification: spike-first; `lake env lean` on the landed module with
zero errors/warnings; explicit `lake build` of the module and the
umbrella; **full `lake build` + `check_build_completeness.py` — 135
source files, 135 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 axioms unchanged);
`check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new
`tkp_*`/`tkf_*`/`tik_K2_zero_gen`/`obj_two_pi0_K2`/`tkfSigned*`
names collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (6561) with the verification row; map freshness exit 0
after the stats sync in both map data tables + SVG regeneration
(49 stations, no status change — this proposal is not a map
station's cited source).

Remaining risk: none owed — QA-only, no axiom disposition changed, no
public statement changed. QA proves consequences relative to the
substrate; it does not prove the substrate (no axiom touched).
Honest scope: the pins are at the `K₂` fixture (two eigenvalues) and
the scalar shrinkage level; the pole-class deferrals above are priced
with both routes.
