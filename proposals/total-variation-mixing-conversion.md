# Proposal: The ℓ² → Total-Variation Mixing Conversion

**Status:** COMPLETE from birth — proposed and delivered in the same
run (2026-08-31, run `20260831T141839Z-run-1`), per the same-run
pattern of `spectral-encoding-drift-pipeline.md` and
`hoeffding-inequality-degree-concentration.md`. Zero new axioms
(count stays 5); every delivered declaration pure hard crust at
exactly `propext, Classical.choice, Quot.sound` (`wip/tv_axcheck.lean`,
35 audited).

Companion to [Strategy](../docs/1_STRATEGY.md), the mixing program
(`mixing-time-bound.md`, whose optional Step 4 this delivers as its
own proposal-scale decision, exactly as that step's own text demands),
the oversmoothing family
([`message-passing-depth-mixing-bound.md`](message-passing-depth-mixing-bound.md),
whose TV twin this delivers), and [SGT Radar](../docs/7_SGT_RADAR.md)
axis 5 (random walks and diffusion), whose score line names this
conversion as *the axis's only remaining absent category*.

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources on Markov
chain mixing (the conversion `TV ≤ (1/2)·√χ²` is classical; see
Sources below). Do not copy this proposal verbatim.

## The obligation this discharges

The mixing program delivered its closing bound
`chiSquareDistance_le_of_connected` on 2026-08-22 in the χ² distance —
an ℓ²(π)-weighted proxy — and explicitly deferred the conversion to
total variation as its optional Step 4, gated on two conditions
(`mixing-time-bound.md`):

1. *"only if a named consumer needs TV specifically rather than ℓ²"*,
   and
2. *"Requires a probability-measure wrapper Scaffold has never used
   before — treat as its own proposal-scale decision, not a default
   continuation of this one."*

The radar has recorded the consequence ever since: axis 5's score
line carries "Absent: the ℓ² → total-variation conversion … the axis's
only remaining absent category." This proposal discharges both gates
and closes the category.

### Step 0: the two gates, discharged on the record

**The consumer gate.** The named consumer is the *field-standard
mixing statement itself*: every textbook mixing bound — Levin–Peres–
Wilmer's `t_mix(ε)` definition and the entire mixing-time literature —
is stated in total variation, not in any ℓ² proxy. Concretely, the
repo-side consumer is the **TV twin of the delivered oversmoothing
ceiling** (the repo's most recent delivered family,
`Oversmoothing.lean`): past the ceiling's own threshold form at `2ε`,
the propagated *distribution* is within `ε` of stationarity in total
variation — with the two-start `2ε` indistinguishability twin, the
statement the message-passing literature actually cites when it cites
mixing. This names the identity the consumer needs (the conversion
constant and the walk-level composition), exactly what the gate
demanded.

**The cost gate.** The 2026-08-22 cost estimate ("a probability-measure
wrapper Scaffold has never used before") is dissolved by scoping, not
paid: the entire `Mixing` module is already vector-valued
(`walkDistribution : V → ℝ`, `stationaryVec : V → ℝ`), and finite-state
total variation *is* `(1/2) ∑ i, |μ i − ν i|` on the vertex type — a
real-valued definition with no `MeasureTheory` anywhere. This is the
mixing program's own Step-2 scoping idiom (χ² chosen over TV in 2026-08-22
precisely to avoid measure-theoretic definitions) applied to the
conversion step; nothing about the mathematical content required the
wrapper the original estimate feared.

### The mathematics

One Cauchy–Schwarz step. For a positive weight `w` of total mass one
and any vector `ν`:

```
TV(ν, w) = (1/2) ∑ i, |ν i − w i|
         = (1/2) ∑ i, w i · |ν i / w i − 1|          (w i > 0)
        ≤ (1/2) √(∑ i, w i) · √(∑ i, w i (ν i/w i − 1)²)   (Cauchy–Schwarz)
        = (1/2) · √(∑ i, (ν i − w i)² / w i)          (∑ w = 1)
        = (1/2) · √χ²(ν, w)
```

Composed with the proved `chiSquareDistance_le_of_connected`:
`TV(ν_t x, π) ≤ (1/2) · √(r^{2t} · ((π x)⁻¹ − 1))`. The constant
`1/2` is sharp — attained exactly on `K₂` at `t = 1` (below), where
Cauchy–Schwarz attains equality because the centered density
`h₁ = (0, 2)` has `|h − 1|` constant.

Statement design note (found while proving, kept in the Lean): the
pointwise identity `|ν i − w i| = w i · |ν i / w i − 1|` is sign-free,
so the generic conversion needs **no sign or mass hypothesis on `ν`**
— it holds for arbitrary signed vectors, strictly more general than
the probability-vector form the textbooks state. The two load-bearing
hypotheses are `w i > 0` (for the identity and the Cauchy–Schwarz
weights) and `∑ w = 1` (for the final collapse) — the second fenced
in QA (below).

## The Lean

**`Mixing.lean`, new `TotalVariation` section** (7 declarations):
`tvDistance` (noncomputable, the vector form), `tvDistance_nonneg`,
`tvDistance_symm`, `tvDistance_triangle` (the only structural fact the
two-start twin needs), **`tvDistance_le_half_sqrt`** (the generic
conversion: `hw : ∀ i, 0 < w i`, `hw1 : ∑ i, w i = 1`, conclusion
`tvDistance ν w ≤ (1/2) * Real.sqrt (∑ i, (ν i - w i)^2 / w i)`),
`walkDistribution_tvDistance_le` (the unconditional walk-level shadow,
hypotheses only `hd` and `[Nonempty V]`), and
**`walkDistribution_tvDistance_le_of_connected`** (the rate form, at
exactly the χ² theorem's hypothesis set).

**`Oversmoothing.lean`, new TV-twin section** (3 declarations):
`walkDistribution_tvDistance_le_of_rate` (the split-constant form
`(1/2) · r^t · √C` with `C = (π x)⁻¹ − 1 ≥ 0` from
`stationaryVec_le_one`; un-split → split through
`Real.sqrt_mul`/`Real.sqrt_sq` at `0 ≤ r`),
**`walkDistribution_tvDistance_le_of_depth`** (the TV ceiling: past
`log (√C / (2ε)) / log (1/r)` the walk law is within `ε` of π in TV —
the entrywise ceiling's own threshold with `ε` at `2ε`, discharged
through the family's own `pow_mul_le_of_log_threshold`), and
**`walkDistribution_tvDistance_sub_le_of_depth`** (the two-start `2ε`
twin via the triangle inequality and symmetry).

## Degenerate-corner analysis (the §5 floor)

- **`∑ w = 1` dropped**: materially false — at the mass-`2` weight
  `w = (1, 1)` (positive, the only other hypothesis, genuinely
  satisfied) and the genuine probability vector `ν = (1/2, 1/2)`, the
  un-guarded conclusion reads `1/2 ≤ (1/2)·√(1/2)`, refuted in QA
  (`tv_conversion_mass_guard_refuted_QA`, with
  `tv_conversion_fixture_clauses_QA` proving the surviving hypothesis
  genuinely holds at the fixture — the refutation isolates exactly the
  mass clause).
- **`V = ∅`**: the walk-level theorems carry `[Nonempty V]` inherited
  from the χ² family's own corner discipline; the generic conversion
  is vacuous-fine on an empty type (empty sums).
- **`r < 0`**: the un-split rate form inherits the χ² bound's
  `r ^ (2t)` (even power, sign-blind); the split form adds `0 ≤ r`
  explicitly since `√((r^t)²) = |r^t|`; the depth form's `0 < r`
  matches the ceiling family's own.
- **`C = 0`** (single-vertex): the depth threshold degenerates
  exactly as the entrywise ceiling's does (`pow_mul_le_of_log_threshold`
  handles `C = 0` trivially — `hthr'`'s constant `√C/2 = 0`).

## QA (`Mixing_QA.lean`'s TV section, +25)

On a new `K₂` edge fixture (`k2Adj`: symmetric, unit weights, degrees
`(1, 1)`, `π = (1/2, 1/2)`, connected by an explicit edge-walk,
one-step law `(0, 1)` by raw evaluation):

- **The exact-attainment pin** `k2_conversion_attained_QA`:
  `TV(ν₁, π) = 1/2 = (1/2)·√χ²(1)` with both sides pinned
  independently (`k2_tv_one_QA` = `1/2` by raw summation;
  `k2_chi2_one_QA` = `1` by raw summation) — the conversion's constant
  *attained*, so no sharper constant in front of the square root can
  hold. The strongest QA shape a bound theorem can have.
- The unconditional instance `k2_conversion_le_QA` (the bipartite edge
  admits no `r < 1` rate — the rate form is honestly vacuous there,
  the conversion is not).
- The mass-one fence and its clauses record (above).

On the counted triangle fixture (`triAdj`):

- The exact TV values at `t = 1, 2, 3`: `1/3`, `1/6`, `1/12`, each by
  raw summation over the pinned walk laws — `t = 1` sits beside the
  instance bound `(1/2)·√(1/2)` with the domination *proved*
  (`tri_tv_rate_one_holds_QA`: honest Cauchy–Schwarz slack — equality
  in the conversion needs `|h − 1|` constant, which fails on the
  triangle).
- Both rate-form instances (un-split and split) at `r = 1/2`, `t = 1`.
- **The depth-form certificate** `tri_tv_depth_two_QA`: at `ε = 1/4`,
  depth `2` certifies `TV ≤ 1/4` (threshold `log(2√2)/log 2 = 3/2 ≤
  2`), with **depth `1` proved to fail the threshold**
  (`tri_tv_depth_one_fails_QA`: `2 < 2√2`) — the threshold hypothesis
  load-bearing, mirroring the entrywise family's
  `tri_ceiling_threshold_three_sharp_QA` pattern; the true value
  `TV(2) = 1/6` sits inside the certified `1/4`.
- **The two-start twin** `tri_tv_two_start_three_QA` at depth `3`
  (both starts' thresholds hold by symmetry): `TV(ν₃ 0, ν₃ 1) ≤ 1/2`,
  with the raw value pinned at `1/8` — a quarter of the bound, honest
  slack beside the certified statement.

## Technique findings (recorded so they are not re-attempted)

1. **`Real.sqrt_le_sqrt` is an implication in this pin**
   (`sqrt x ≤ sqrt y ↔ x ≤ y` is the *ℝ≥0* namespace's shape at the
   file's top; the ℝ one at `Sqrt.lean:310` is `x ≤ y → √x ≤ √y`) —
   `.mpr` on it fails with "invalid field notation". Meanwhile
   `Real.sqrt_lt_sqrt (hx : 0 ≤ x) (h : x < y)` *is* a two-explicit-
   argument implication, and `Real.sqrt_lt_sqrt_iff (hx : 0 ≤ x)` is
   the iff. Mixed conventions inside one file — check each by name.
2. **`Real.sqrt_mul` takes the nonneg proof first, the second factor
   as an explicit ℝ**: `Real.sqrt_mul (sq_nonneg a) b : √(a*b) =
   √a*√b` — not `(h₁) (h₂)`.
3. **`pow_mul_le_of_log_threshold` consumes `log (C / ε)`, which
   parses as `log ((√C/2)/ε)` when instantiated at `C := √C/2`** — a
   public statement phrased as `log (√C / (2 * ε))` (the honest
   "ceiling at 2ε" display) needs an in-proof `by ring` conversion
   `√C/2/ε = √C/(2*ε)` before the bridge applies.
4. **`norm_num` does not evaluate `|·|` of numeral differences by
   itself**, but `norm_num [neg_sub, abs_of_neg, abs_of_nonneg]` does,
   with the sign side-goals discharged by norm_num itself — the
   triangle/edge TV value pins are one-liners once the matrix-literal
   evaluation lemmas (`Matrix.cons_val_*`, `Matrix.head_cons`) are in
   the list. (The repo's earlier `tri_ceiling_one_value_QA` used the
   same pattern for the positive-sign case only.)
5. **The stale-olen import boundary recurs on the
   Mixing→Oversmoothing edge** (documented before for Derived→QA):
   `lake env lean Oversmoothing.lean` against the pre-edit Mixing
   olean cannot see the new declarations — build the imported module
   explicitly first.
6. **A hypothesis the proof turns out not to need should be deleted,
   not retained**: the generic conversion originally carried
   `hν : ∀ i, 0 ≤ ν i` from the textbook form; the sign-free identity
   route makes it dead weight, and the unused-binder linter is the
   alarm. The delivered statement is strictly stronger.

## Verification (the ladder, 2026-08-31)

Spike first: `wip/tv_spike.lean` (all shelf declarations + the full QA
section + the audit) iterated to zero errors/zero warnings before any
shelf edit. `lake env lean` zero errors/zero warnings on all three
touched modules (`Mixing.lean`, `Oversmoothing.lean`,
`Mixing_QA.lean`); explicit `lake build` targets ✔ on all three;
`#print axioms` via `wip/tv_axcheck.lean` on all 35 audited
declarations (10 shelf + 25 QA) — every one exactly
`propext, Classical.choice, Quot.sound`; **full `lake build` ✔
(2407/2408) immediately followed by `check_build_completeness.py` —
131 source files, 131 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` (5, both PF findings allowlisted-confirmed — no axiom
surface touched); `check_refutation_independence` (10-tag clean — no
tags added, nothing here touches an axiom);
`check_public_reachability` clean (62 modules); `check_citations`,
`check_markdown_links` pass; scoreboard regenerated at **3338/5/0**
(+25); `check_scaffold_map_freshness` exit 0 after the 3313 → 3338
stats sync in both map files and SVG regeneration. Records ladder
completed in the same delivery: this proposal, `proposals/README.md`,
README, the radar (axis 5 re-scored 4.0 → 4.5 — its single named
absent category closed; QA axis synced at 4.0 per protocol),
`index/map/spectral_graph.md`, the scoreboard verification row, both
map data tables + regenerated SVG, the QA module's purpose header, the
execution plan, and the activity log.

## Sources

The conversion step is classical — the standing locator rule applies
(no page-level locators invented; a physical-copy confirmation can
upgrade this note):

- Levin, Peres & Wilmer, *Markov Chains and Mixing Times* — the
  χ²-to-TV Cauchy–Schwarz relation, stated there among the basic
  distance comparisons (the `1/2` constant is sharp, as the `K₂` pin
  attests). No `index/sources/` entry added: the delivery is a proved
  theorem, not an admitted axiom — citations bind the axiom boundary,
  and the proof here is self-contained (one Cauchy–Schwarz through
  `Finset.sum_mul_sq_le_sq_mul_sq`).

## Deferred / out of scope

- The **mixing time** `t_mix(ε) := sInf {t | ∀ s ≥ t, ...}` as a
  defined object, and statements about it (monotonicity, submultiplicivity)
  — the depth-form TV ceiling already carries the operative content
  (an explicit certified depth); a defined `t_mix` has no consumer
  yet. Not attempted.
- The reverse (TV → χ²) direction and the `4TV² ≤ χ²`-class two-sided
  calculus — no consumer has named it.
- The ℓ∞ (entrywise) distance form — already delivered as the
  oversmoothing family's `walkDistribution_sub_stationaryVec_abs_le`;
  nothing to add.
