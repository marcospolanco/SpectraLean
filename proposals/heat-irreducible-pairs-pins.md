# Proposal: The Heat + IrreducibleStationary Pairs' Positive Pins

**Status:** COMPLETE. Delivered 2026-09-07 (run `20260907T114557Z-run-1`,
session `ses_f84763143ffeAVPDc1KGOxyMgM`); QA-only, zero axiom contact.

## The census finding this closes

`scripts/consumption_survey.py`'s census
(`wip/census_20260907_post10.txt`) leaves the inert set at 25 with four
2-clusters (Band, Heat, IrreducibleStationary, Normalized). This
delivery takes the **Heat pair** and the **IrreducibleStationary pair**
— four theorems whose pins are cheap and genuinely valued at the
delivered fixtures, the prior handoff's "cheap batch of pairs" option.

Scope decisions (why not all four pairs):

- The Band pair's `eq_zero_of_bandProjector_mulVec_eq_self` is a
  vanishing statement whose positive instance is degenerate — with
  disjoint bands (`b ≤ c`) only `w = 0` satisfies both fixed-point
  hypotheses, so a positive pin proves `0 = 0`. Its natural QA shape
  is a hypothesis-necessity fence (an `h₁`-breaker), which belongs to
  a Band-audit delivery, not a pins batch.
- The Normalized pair (`walkLaplacian_mulVec_eigvecOf`,
  `walk_eigvec_expansion`) is stated at the *opaque* spectral-theorem
  basis `eigvecOf`, whose sign is not resolvable without unfolding;
  the existing QA consumes the generic-vector transfer forms
  (`walkLaplacian_mulVec_degreeInvSqrt` at the P₃ hand eigenpairs)
  instead. Priced as residue: a pin would need sign-robust quadratic
  sums or an `eigvecOf`-identification lemma.

## What was delivered

Thirteen QA declarations across the two QA files' new `StructuralPins`
sections (QA 6685 → 6698), the first genuine consumption of all four:

- **The decay-factor pair on `heatEdgeAdj`** (spectrum `{0, 2}` pinned
  by the delivered `edgeLaplacian_evals_QA`): at the constant mode the
  bound is **attained with equality** (`e^{-1·0} = 1 ≤ 1` — the kernel
  mode undamped, the `≤ 1` sharp; the value pinned in
  `hkp_decay_kernel_value_QA`); at the Fiedler mode `t = 1` the factor
  is `e^{-2} ≤ 1` with the **strictness pinned** through the file's
  established `Real.exp_lt_exp` idiom — the two modes together show
  the bound is exactly the damping-no-amplification statement.
- **The `t = 0` identity** (`normalizedHeatKernel_zero`) — the
  operator identity consumed by acting on the antisymmetric vector:
  `normalizedHeatKernel heatEdgeAdj 0 *ᵥ ![1, -1] = ![1, -1]` through
  the theorem (`one_mulVec`), no matrix exponential computed.
- **The transpose-irreducibility two-route join on GENUINELY DIRECTED
  input**: the walk matrix of the `A3` star (asymmetric even though
  `A3` is symmetric — rows scaled by different reciprocals). Route A:
  `isIrreducible_transpose` ∘ `walkTransitionMatrix_isIrreducible`.
  Route B: raw `ReflTransGen` paths in the arc-reversal digraph (the
  hub-`0` pattern, every arc weight read through
  `Matrix.transpose_apply` at the pinned `A3P_*` entries). Two routes,
  one fact.
- **The chain consumed onward**: the transpose's irreducibility feeds
  `exists_pow_pos_of_isIrreducible` — `∃ m, 0 < (Pᵀ^m) 0 1` derived
  through both theorems — with the raw witness `(Pᵀ) 0 1 = P 1 0 = 1`
  pinning the existential non-vacuous at `m = 1`.
- **The `[0, 1]` power-entry bound attained with equality**:
  `(P²) 0 0 = 1 ≤ 1` through `pow_entry_le_one` (hypotheses from the
  new `A3P_nonneg` helper and the shelf's `walkTransitionMatrix_row_sum`),
  with the raw computation `(P²) 0 0 = 1/2·1 + 1/2·1 = 1` — the star's
  two-step return genuinely reaches the bound.

## Technique findings (Lean 4.14 / this Mathlib pin)

- Inline `by rw [Matrix.transpose_apply, A3P_ij]; norm_num` inside an
  `exact Relation.ReflTransGen.head (…) refl` leaves the entry's
  arguments as metavariables and the rewrite fails — the working shape
  is concrete `have hTij : 0 < Pᵀ i j` facts first, then fully
  concrete `head` terms (the goal's post-`fin_cases` beta-redexes
  unify by defeq).
- An `any_goals exact <term>` cascade reports application-type-mismatch
  errors rather than catching per goal; explicit `fin_cases` bullets
  are the robust form.
- Multi-line `exact` terms where the continuation is a bare identifier
  do not parse (the identifier lands at command position) — single
  lines or parenthesized continuations.

## Verification

Spike-first (`wip/hipins_spike.lean` — green after three fix rounds,
the traps above recorded); both landed modules elaborate with zero
errors/warnings (the 2 `ring_nf` infos in `Heat_QA` verified
pre-existing at HEAD); explicit builds ✔; the 13-declaration axiom
audit (`wip/hipins_axcheck.lean`) — every one exactly `propext,
Classical.choice, Quot.sound`; full `lake build` +
`check_build_completeness.py` (135/135 fresh — two mtime stalenesses
caused by the pre-existing-info check's stash round-trip, cured by the
documented artifact-removal remediation); `lint_axioms` exit 0 (4
axioms unchanged); `check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new `hkp_*` /
`nhk_*` / `isp_*` / `A3P*` names collision-free);
`check_backlog_freshness` clean; scoreboard regenerated
(1369 / 6698 / 4 / 0); map freshness exit 0 after the stats sync;
**the census re-run (`wip/census_20260907_post11.txt`, diffed against
`post10`) shows exactly the 4 targeted theorems leaving the inert set
(1342 → 1346 value-consumed, 25 → 21 never-touched, the Heat (2) and
IrreducibleStationary (2) lines gone, no bonus, no collateral)**.

## Honest scope

The decay pins are at `t = 1` and the two sorted indices of one
fixture; the `t = 0` identity at one nontrivial vector; the transpose
join at the one asymmetric walk fixture (3 vertices); the power-entry
pin at one entry of one power. The Band and Normalized pairs remain
inert with their scope decisions recorded above — the delivery's
priced residue.
