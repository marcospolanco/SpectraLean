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

- ~~The **mixing time** `t_mix(ε) := sInf {t | ∀ s ≥ t, ...}` as a
  defined object, and statements about it (monotonicity,
  submultiplicivity) — the depth-form TV ceiling already carries the
  operative content (an explicit certified depth); a defined `t_mix`
  has no consumer yet. Not attempted.~~ **Delivered 2026-09-01** as
  this file's own follow-on delivery (see the next section): the
  consumer gate was discharged by the Poisson-bridge delivery, whose
  transfer corollary's `hmix` clause is exactly the object's witness
  condition.
- The reverse (TV → χ²) direction and the `4TV² ≤ χ²`-class two-sided
  calculus — no consumer has named it.
- The ℓ∞ (entrywise) distance form — already delivered as the
  oversmoothing family's `walkDistribution_sub_stationaryVec_abs_le`;
  nothing to add.

## Follow-on delivery record: the discrete `t_mix` object (2026-09-01)

Run `20260901T070242Z-run-1`. The Deferred item above delivered as this
proposal's follow-on — zero new axioms (count stays 5; `#print axioms`
via `wip/dtmix_axcheck.lean` on all 16 audited declarations — 7 shelf +
9 QA — every one exactly `propext, Classical.choice, Quot.sound`, pure
hard crust). QA 3478 → 3487 (+9, `Mixing_QA.lean`'s `DiscMixingTime`
section).

**The consumer gate, discharged.** This proposal deferred the object
with "a defined `t_mix` has no consumer yet". The Poisson-bridge
delivery (`proposals/continuous-time-chi-square-mixing.md`, 2026-09-01)
then put the consumer on the shelf: the transfer corollary
`contWalkDistribution_tvDistance_le_of_discreteMixing` hypothesizes
`hmix : ∀ k ≥ m, TV_disc(k) ≤ ε₁` — exactly the object's witness
condition. With that half in place, defining the object became the
standing handoff's first-named plain follow-on choice, and this
delivery closes the loop in the other direction: the object's own
attainment fact now *discharges* the corollary's `hmix`.

**The shelf** (`Oversmoothing.lean`'s new discrete-mixing-time section —
placed there because the ceiling's certificate engine
`walkDistribution_tvDistance_le_of_depth` lives in that module and its
imports already point toward `Mixing.lean`'s transfer corollary; zero
duplication, zero import changes; 7 declarations):

- `walkMixingTimeFrom A x ε := sInf {t : ℕ | ∀ s ≥ t, TV_disc(s) ≤ ε}`
  — Levin–Peres–Wilmer ch. 20's per-start `t_mix` reading, the discrete
  twin of `Mixing.lean`'s `contMixingTimeFrom`, with the junk corner
  documented (at an unreachable `ε`, `sInf ∅ = 0` on `ℕ` — pinned and
  fenced in QA, see below).
- `walkMixingTimeFrom_bddBelow` / `_le_of_cert` — the certificate
  interface (any witness time certifies the mixing time), the
  `pow_mul_le_of_log_threshold`/`contMixingTimeFrom_le_of_cert` family
  idiom.
- `walkMixingTimeFrom_spec` — **the attainment specification, the
  discrete object's own advantage over its continuous twin**: `ℕ` is
  well-ordered, so the infimum of a nonempty witness set is a *member*
  (`csInf_mem` — no monotonicity needed, the "∀ s ≥ t" is in the
  membership predicate), and membership *is* the uniform bound. Given
  any witness, `t_mix` itself satisfies the certificate condition —
  this one-liner is what composes with the transfer corollary.
- `walkMixingTimeFrom_le_of_connected` — **the spectral ceiling**
  `t_mix(ε) ≤ ⌈log(√C/(2ε))/log(1/r)⌉` at exactly the depth-form TV
  certificate's hypothesis set (connected, `0 < r < 1`, rate
  certificate): a two-line composition — `Nat.le_ceil` supplies the
  threshold, `walkDistribution_tvDistance_le_of_depth` the bound. The
  big-`ε` case is absorbed (a negative threshold ceilings to `0`). The
  `0 < r < 1` restriction is honest and load-bearing: periodic chains
  admit no such certificate (the `K₂` fence below), which is exactly why
  the junk corner cannot be reached through this theorem.
- `walkMixingTimeFrom_anti` — ε-antitonicity, the continuous twin's
  `csInf_le_csInf` mirror with the witness hypothesis.
- `contWalkDistribution_tvDistance_le_of_walkMixingTime` — **the bridge
  composition, the named consumer**: on a connected graph with a rate
  certificate, a Poisson lower-tail bound below `t_mix(ε₁)` gives
  `TV_cont(t) ≤ ε₁ + ε₂` — the caller supplies only the Poisson tail;
  `hmix` is discharged by the object (the ceiling supplies the witness
  existence, `_spec` the certificate).

**The QA** (`Mixing_QA.lean`'s `DiscMixingTime` section, +9):

- **The exact closed forms on the triangle**, each pinned in *both*
  directions: `t_mix(1/3) = 1` (`tri_mix_eq_third_QA`), `t_mix(1/6) = 2`
  (`tri_mix_eq_sixth_QA`), `t_mix(1/12) = 3` (`tri_mix_eq_twelfth_QA`)
  — the certificate interface gives `≤` from the exact TV values
  `TV(m) = (2/3)·2^{−m}`, the attainment specification refutes the
  smaller values (e.g. `t_mix(1/6) ≠ 1` because `TV(1) = 1/3 > 1/6`).
  Both interfaces load-bearing on the object's exact shape.
- **The antitone instance** `t_mix(1/6) ≤ t_mix(1/12)` with exact values
  `2 ≤ 3` on both sides (`tri_mix_anti_QA`).
- **The ceiling attained exactly** (`tri_mix_ceiling_attained_QA`): at
  rate `1/2` and `ε = √2/4` — where the threshold ratio
  `√C/(2ε) = √2/(√2/2) = 2` sits exactly at the power the certificate
  names — the object is `1` and the ceiling's own right side evaluates
  to `1`: no slack anywhere in the package. Plus **the ceiling computed
  with honest slack** (`tri_mix_ceiling_slack_QA`): at the working
  threshold `ε = 1/6` the right side evaluates to exactly `3` against
  the true `2` — one wasted step, the Cauchy–Schwarz conversion's price
  on the triangle, pinned by the two strict log inequalities
  `4 < 3√2 ≤ 8`.
- **The `K₂` junk corner pinned and fenced** (`k2_mix_junk_corner_QA`):
  no witness time exists at `ε = 1/4` (the periodic chain's
  `TV_disc ≡ 1/2`), so the object's defining set is empty and
  `sInf ∅ = 0` — a value that *looks* anti-conservative. The QA pins it
  beside the existing no-certificate fence, and the docstring records
  why no theorem instantiates there: the ceiling's `0 < r < 1` is
  undischargeable on `K₂` (the edge's normalized gap `2` forces
  `r ≥ 1`).
- **The bridge instance** (`tri_bridge_mix_QA`): the same bound the
  hand-certified `tri_mixing_transfer_QA` derives (`TV_cont(8) ≤ 5/24`)
  re-derived through the new theorem — the caller supplies only the
  Poisson tail bound, the discrete certificate is the object's own.

**Verification** (the run's own ladder, before any record was written):
spike first (`wip/dtmix_spike.lean` — the shelf declarations, the full
QA section, and the axiom audit iterated to zero errors before any
shelf edit; the QA module carries its recorded benign `Try this:
ring_nf` note class, now 3 notes, from the copied numeric block in
`tri_bridge_mix_QA`); `lake env lean` zero errors on both touched
modules; explicit `lake build` targets ✔ on both; **full `lake build` ✔
immediately followed by `check_build_completeness.py` — 133 source
files, 133 fresh artifacts, 0 stale, 0 missing, exit 0** (after the
documented single-module mtime remediation — the stale-olen
QA-imports-shelf boundary recurrence); `lint_axioms` exit 0 (5, both PF
findings allowlisted-confirmed); `check_refutation_independence`
(10-tag clean — no tags added, nothing here touches an axiom);
`check_public_reachability` clean (63 modules); `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**3487/5/0**) with
the verification row added; `check_scaffold_map_freshness` exit 0 after
the 3478 → 3487 stats sync in both map files and SVG regeneration (no
proposal status header changed — a follow-on record, no tier change).

**Technique findings** (recorded so they are not re-attempted):

- `csInf_mem` exists for `ℕ` through `[WellFoundedLT ℕ]` — the
  attainment specification needs no monotonicity argument at all,
  because the "∀ s ≥ t" lives in the membership predicate itself;
  designing the statement shape before checking this would have
  produced a needless `walkDistribution_tvDistance_anti` detour.
- `Nat.sInf_empty : sInf ∅ = 0` is the ℕ-valued junk-corner idiom (vs.
  the ℝ-valued twin's `sInf ∅ = 0` documentation).
- `Nat.le_ceil : a ≤ ↑⌈a⌉₊` supplies the real→natural threshold bridge
  in one term, with `exact_mod_cast` carrying the natural side.
- `pow_le_pow_right₀` does not normalize `2 ^ 1` to `2` on delivery —
  `norm_num at hp` first, then `exact hp` (the direct term-mode
  application type-mismatches).
- `div_lt_iff₀` vs. `lt_div_iff₀` for `c < a / b` goals: the mpr
  argument shape is `c * b < a`, and the two lemmas' iff directions
  read opposite to intuition under bare `rw`.
- A `by norm_num` bridge between `↑n` (the `Nat.lt_ceil`/`Nat.ceil_le`
  iff sides) and a numeral is counterproductive — norm_num normalizes
  the *goal's* denominators (`2 * (1/6)` → `1/3`) and breaks the match;
  the bare defeq unification `Nat.lt_ceil.mpr hltx` works directly.
- `field_simp` on a goal with an atom denominator prints an
  unconditional `Try this: ring_nf` note; `refine (div_eq_iff _).mpr
  (by ring)` avoids it (the module's recorded note baseline stays at
  the copied-block minimum).
- `nlinarith` is tactic-block-only — `have h : P := nlinarith [...]`
  fails with "function expected"; `:= by nlinarith [...]` is required.

**Remaining risk:** none owed by the delivery — pure hard crust, no
axiom disposition changed, no existing public statement changed. The
submultiplicivity-class statements the original deferral named remain
undelivered with no consumer named; the sup-over-starts uniform `t_mix`
remains a trivial composition left consumer-gated.

## Follow-on delivery record: the uniform `t_mix` and the
submultiplicativity class (2026-09-01)

**Status: DELIVERED** — the deferral's own named remainder (the
submultiplicivity-class `t_mix` statements and the sup-over-starts
uniform object, both recorded in the previous record's remaining-risk
line as "no consumer named" / "consumer-gated") delivered as one
package whose two halves discharge *each other's* gates: the uniform
object's named consumer is the submultiplicativity class — LPW's
`d(s+t) ≤ d(s)d(t)` and the ε-escalation corollary it powers are
theorems about the worst-case-start object, unstatable per-start — and
the escalation corollary's own consumer is the field's canonical
bridge (LPW's `t_mix := t_mix(1/4)` convention: one certified
evaluation time yields every ε-level mixing time; Montenegro–Tetali
state their bounds at the worst-case start). Zero new axioms (count
stays 5), pure hard crust: `#print axioms` via `wip/uniformmix_axcheck.lean`
on all 46 nameable declarations (19 public shelf + 27 QA; the 3
file-private cores audited transitively through their public
consumers) reads exactly `propext, Classical.choice, Quot.sound`.
Spike by run `20260901T124410Z-run-1` (`wip/uniformmix_spike.lean`,
iterated to zero errors/warnings); the landing run
`20260901T163200Z-run-1` found the spike complete on disk, confirmed
it elaborating clean, and landed it unchanged.

### The shelf (`Oversmoothing.lean`'s new `UniformMixing` section)

- **LPW's two distances** — `walkTVPair` (`d(t) = max_{x,y}
  TV(ν_t^x, ν_t^y)`, the two-start distance the submultiplicativity
  class lives on) and `walkTVUniform` (`d̄(t) = max_x TV(ν_t^x, π)`,
  Montenegro–Tetali's distance, the one whose threshold curve *is* the
  mixing time), both `Finset.sup'` maxima (genuine maxima on a finite
  type) with nonnegativity.
- **The sharp Dobrushin contraction**
  `tvDistance_pow_walkTransitionMatrixTranspose_mulVec_le`:
  `TV(μ(Pᵀ)ᵗ, ν(Pᵀ)ᵗ) ≤ TV(μ,ν) · d(t)` at equal masses —
  hypothesis-minimal (no stochasticity, no signs; only the
  recentering mass-zero condition). The engine is the private
  pairing core `abs_sum_mul_le_of_pairwise` (recentering `g` at its
  finite minimum is exactly what makes the positive-part split
  valid — the naive triangle route loses the factor `2` here) plus
  the sign-statistic core `tvDistance_mulVec_le_pair`, closed against
  the delivered distinguishing-function bound
  `tvDistance_ge_half_abs_sum` (the spectral-floor delivery's own TV
  toolkit lemma — its second consumer).
- **The submultiplicativity class** — `walkTVPair_submul`
  (`d(s+t) ≤ d(s)d(t)`; the Dobrushin contraction at the pair of
  `s`-step laws, equal masses by walk conservation — pure Markovity,
  no connectivity, no rates), the stationary mixture identity
  `stationaryVec_eq_sum_smul_walkDistribution` (π as the π-weighted
  mixture of the `t`-step laws, its fixed-point property expanded
  through linearity), the finite TV-convexity core,
  `walkTVUniform_le_walkTVPair` (`d̄ ≤ d`, no reversibility needed),
  `walkTVUniform_mul_walkTVPair_le` (`d̄(s+t) ≤ d̄(s)d(t)`), and the
  escalation engine `walkTVUniform_succ_mul_le`
  (`d̄((k+1)t₀) ≤ d̄(t₀)d(t₀)^k`).
- **The uniform object** — `walkMixingTime A ε := sInf {t | ∀ s ≥ t,
  ∀ x, TV(ν_s^x, π) ≤ ε}` (LPW ch. 20's field-standard reading), with
  `walkMixingTime_bddBelow`/`_le_of_cert`/`_spec` (the
  certificate-and-attainment interface mirroring the per-start
  object's), the witness-hypothesized per-start domination
  `walkMixingTimeFrom_le_walkMixingTime` (the witness is load-bearing
  and not decorative: at the junk corner — no uniform witness,
  `sInf ∅ = 0` — the un-witnessed statement is false, fenced in QA),
  and the finite-sup interchange `walkMixingTime_eq_sup_walkMixingTimeFrom`
  (on a finite type the uniform object *is* the worst start's
  per-start object — hypothesis-light, no graph structure).
- **The ε-escalation corollary** — `walkMixingTime_le_mul_of_escalation`
  (`t_mix(ε) ≤ (k+1)t₀` whenever `d̄(t₀) ≤ ε₀`, `d(t₀) ≤ ρ < 1`,
  `ε₀ρᵏ ≤ ε`) and its ⌈log⌉ display twin
  `walkMixingTime_le_of_escalation` (the threshold discharged through
  the shelf's own `pow_mul_le_of_log_threshold`); plus the uniform
  spectral ceiling `walkMixingTime_le_of_connected` (the per-start
  ceiling's uniform form at uniformly bounded start constants `C`).

### The QA (`Mixing_QA.lean`'s new `UniformMixing` section, +27,
3517 → 3544)

The triangle is the fixture where every statement in the package is
*tight* (`d(m) = (1/2)^m`, `d̄(m) = (2/3)·2^{−m}`):

- **The distance pins from raw law literals** — the one- and two-step
  laws from all three starts (the sup terms' raw material),
  `d(1) = 1/2`, `d(2) = 1/4` (the two-start sup over nine pairs),
  `d̄(1) = 1/3`, `d̄(2) = 1/6` (the worst-start sup over three
  starts), each `le` side proved per-pair/per-start and each `ge`
  side by the exhibited maximizing pair/start.
- **Submultiplicativity attained with equality** —
  `d(2) = d(1)·d(1)` (`1/4 = (1/2)(1/2)`), `d̄(2) = d̄(1)·d(1)`
  (`1/6 = (1/3)(1/2)`), and the escalation engine at `k = 1`: no
  slack anywhere in the package, and the sharp Dobrushin constant
  load-bearing (a factor-`2` statement would read `1/4 ≤ 1/2`, true
  with slack — the equality pins the constant).
- **`d̄ ≤ d` with honest slack witnessed** (`1/3 ≤ 1/2`, both sides
  independently pinned).
- **The uniform object's exact closed forms** — `t_mix(1/3) = 1` and
  `t_mix(1/6) = 2`, each pinned in both directions (the escalation
  certificate above — at `ε = 1/3` closing *exactly* at `k = 0` —
  and the per-start pins `t_mix⁰(1/3) = 1`, `t_mix⁰(1/6) = 2` below,
  through the domination with the uniform witness supplied); the
  sup-interchange instantiated structurally; the uniform ceiling
  instance at `C = 2`.
- **The `K₂` periodicity corner at the uniform level** — `d(1) = 1`
  maximal (the two one-step laws sit on opposite vertices), so no
  escalation certificate `ρ < 1` exists and submultiplicativity
  degenerates to `1 ≤ 1·1`; no uniform mixing witness at `1/4`; and
  the object's empty-set infimum `walkMixingTime k2Adj (1/4) = 0`
  pinned and fenced — the anti-conservative-looking junk corner that
  every theorem in the package guards against by carrying a witness
  or a `ρ < 1` certificate.

### Technique findings (recorded so they are not re-attempted)

The spike was completed by the prior run, so this landing run's
findings are about *landing*, not proving:

- Splitting a spike into shelf/QA landings is safest with a script
  over line ranges (namespace boilerplate stripped once, section
  wrappers added once); hand-editing 600-line insertions invites
  dropped `omit` lines.
- The partial-line edit idiom for newest-first Markdown tables
  (oldString ending mid-row) preserves the following row exactly,
  but the row must be re-verified afterward — the truncation point is
  invisible in a diff review.
- A spike whose three namespace blocks were grown iteratively can be
  merged into one landed section without re-elaboration risk only
  because each block was independently closed; keep that property
  when authoring.
- `#print axioms` cannot name `private` declarations from an import —
  the three private cores are audited transitively through their
  public consumers, and the axcheck header says so explicitly.

### Verification (the ladder, run by the landing run
`20260901T163200Z-run-1`)

Spike found complete and confirmed elaborating clean (`lake env lean`
exit 0, zero errors/warnings) before landing; `lake env lean` zero
errors/zero warnings on both touched modules (only the QA module's 3
recorded pre-existing benign `ring_nf` notes); explicit `lake build`
targets ✔ on both; `#print axioms` via `wip/uniformmix_axcheck.lean`
on all 46 nameable declarations — every one exactly `propext,
Classical.choice, Quot.sound`; full `lake build` ✔ immediately
followed by `check_build_completeness.py` — 133 source files, 133
fresh artifacts, 0 stale, 0 missing, exit 0; `lint_axioms` exit 0
(5, both PF findings allowlisted-confirmed); `check_refutation_independence`
(10-tag clean — no tags added, nothing here touches an axiom);
`check_public_reachability` clean (63 repo modules); `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (3544/5/0) with
the verification row added; `check_scaffold_map_freshness` exit 0
after the 3517 → 3544 stats sync in both map files and SVG
regeneration (no proposal status header changed — a follow-on record,
no tier change).

**Remaining risk:** none owed by the delivery — pure hard crust, no
axiom disposition changed, no existing public statement changed (one
incidental cleanup: the uncommitted `Mixing.lean` diff's doubled
`omit [DecidableEq V] in` line, an accidental duplicate from the
spectral-floor run, removed). The deferral list's remainder is now
only the reverse TV → χ² calculus (still no consumer named). LPW's
`t_mix := t_mix(1/4)` convention itself (the packaging of the
escalation corollary at the canonical threshold) is now a one-line
consumer away rather than missing machinery.
