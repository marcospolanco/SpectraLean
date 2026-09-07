# Proposal: The AlonBoppana Inert Trio's Positive Pins

**Status:** COMPLETE. Delivered 2026-09-07 (run `20260907T161228Z-run-1`,
session `ses_f83866b92ffeZMaPKRE7jkT5Jb`); QA-only, zero axiom contact.

## The census finding this closes

`scripts/consumption_survey.py`'s census
(`wip/census_20260907_post15.txt`) leaves the inert set at 7, headed by
the AlonBoppana cluster (3): `cycleAdj_nonneg` (the cycle-adapter
nonnegativity interface, generic over the scale — never instantiated),
`levClass_pairwise_disjoint` (the level-class partition law — the
"levels are a partition" half the tree-ball machinery assumes), and
`radialVec_apply` (the radial test vector's entry form — the
falsifiability anchor, which the earlier energy pins bypass by
def-unfolding). The prior handoff names this cluster first among the
inert tail.

## What was delivered

Sixteen QA declarations in `AlonBoppana_QA.lean`'s new inert-trio pins
section (QA 6766 → 6782), all at the delivered `abC4` fixture whose
level geometry was already pinned:

- **The cycle-adapter bridge** `ab_cycle4_eq : cycleAdj 4 = abC4` —
  entrywise, the `cycleGraph 4` adjacency decided at all sixteen index
  pairs (the `DecidableRel` instance makes each `if_pos`/`if_neg`
  decidable). Load-bearing: a wrong adjacency convention (a path
  instead of a cycle) breaks the equality. Through the bridge,
  `ab_cycle4_nonneg_via_cycleAdj` — `cycleAdj_nonneg`'s first genuine
  consumption, the generic theorem delivering the fixture's
  nonnegativity — joined to the raw wrap-edge value
  `abC4 3 0 = 1` (the entry that distinguishes a cycle from a path).
- **The level geometry completed**: the iff form
  `abC4_levE_zero_iff` (through the connected junk-zero-honest
  characterization), the endpoint/vertex-`2`/vertex-`3` level values
  (`0`, `1`, `1` — each by one adjacency fact plus one non-identity),
  and the two explicit classes `abC4_levClass_zero_eq` /
  `abC4_levClass_one_eq` — level `0` is exactly the edge `{0, 1}`,
  level `1` exactly the far side `{2, 3}`.
- **The disjointness law consumed, two routes**:
  `abC4_levClass_disjoint` through `levClass_pairwise_disjoint` (its
  first genuine consumption, via an explicit-∀ re-packaging because
  `Pairwise`'s ⦃a b⦄ are not positionally applicable), and
  `abC4_levClass_disjoint_raw` by literal Finset arithmetic on the two
  pinned classes — two routes, one fact. Plus the nonempty-vs-empty
  instance `abC4_levClass_disjoint_empty` (levels `1` and `2`, joined
  to the delivered level-`2` emptiness pin).
- **The entry form consumed, all three branches**:
  `abC4_radialVec_endpoint` (`ρ⁰ = 1` at `levE = 0 ≤ 1`),
  `abC4_radialVec_level1` (`ρ¹ = ρ` at `levE = 1 ≤ 1`), and
  `abC4_radialVec_truncated` (`0` at truncation `k = 0` — the `if`'s
  load-bearing dropped branch), each through `radialVec_apply`, with
  `abC4_radialVec_raw` the def-unfolding companion triple — two
  routes per value.

## Consumption closure (the tool's verdict)

The census re-run (`wip/census_20260907_post16.txt`, diffed against
`post15`) shows exactly the 3 targeted theorems leaving the inert set —
1367 → 1370 value-consumed, 7 → 4 never-touched, the AlonBoppana line
gone, no bonus, no collateral. The pins method's fourteenth
application.

## Traps recorded (the spike's fix rounds)

- `levClass_pairwise_disjoint`'s `A`/`hA` are implicit and
  `Pairwise`'s `⦃a b⦄` are strict-implicit: a positional call
  `... 0 1 0 1 (by decide)` lands the numerals in the `a ≠ b` slot —
  the robust shape is the explicit-∀ re-packaging
  `have hpair : ∀ a b, a ≠ b → ... := levClass_pairwise_disjoint
  (A := abC4) 0 1`.
- `rw` inside a `show`-typed `if_pos` argument auto-closes rfl-shaped
  side conditions (`1 ≤ 1`) inconsistently across the three branches —
  per-branch inspection, `omega` only where the residue is not
  rfl-shaped (`0 ≤ 1`, `¬1 ≤ 0`).
- The `{1}`-Finset membership residue after an iff-rewrite defeats
  `tauto` — a trailing `simp` normalizes `z ∈ {1}` to `z = 1`.
- `lake env lean` elaboration does not write the module's olean — the
  documented mtime-staleness remediation (explicit `lake build
  <module>`) was needed once, and the axcheck run must follow it
  (the audit's imports resolve against the built artifact).

## Residue

- The inert tail is now 4: the Azuma `MatrixMDS` structure fields (3)
  and `l_infty_norm_nonneg` (whose own Core-targeting QA module would
  also first-consume the never-touched def `l_infty_norm`).
- The disjointness pins are at the one `C₄` edge; a parametric
  cycle-family instance (the Step-8 style) is a natural future
  extension, not owed.
