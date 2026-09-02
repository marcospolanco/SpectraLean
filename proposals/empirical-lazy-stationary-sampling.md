# Proposal: The Empirical Lazy Sampling Guarantee

**Status:** COMPLETE — proposed and delivered in the same run
(`20260902T003639Z-run-1`), per the same-run pattern of
`lazy-mixing-time-objects.md`. Zero new axioms (count stays 5):
`#print axioms` via `wip/lazystat_axcheck.lean` on all 15 audited
declarations (3 shelf + 12 QA) reads exactly
`[propext, Classical.choice, Quot.sound]` — pure hard crust. QA
3600 → 3612.

Companion to [Strategy](../docs/1_STRATEGY.md), to
[lazy-mixing-time-objects.md](lazy-mixing-time-objects.md) (the parent
delivery; its "named follow-on" section is this proposal's gate
discharge), to
[lazy-walk-mixing.md](lazy-walk-mixing.md) (the lazy rate family), and
to [empirical-stationary-distribution-concentration.md](empirical-stationary-distribution-concentration.md)
(the plain program this clones at the lazy law).

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources (empirical
estimation of stationary distributions, lazy Markov chains, and
Hoeffding-type concentration are classical; see Sources below). Do not
copy this proposal verbatim.

## The obligation this discharges

`lazy-mixing-time-objects.md`'s delivery record closes with a named
follow-on: **the empirical-stationary sampling guarantee at the lazy
law** — `empiricalLazyWalkDistribution_stationary_tail_of_depth`, the
lazy analogue of `Derived/EmpiricalStationary.lean`'s capstone — with
the delivered entrywise lazy ceiling
`lazyWalkDistribution_sub_stationaryVec_abs_le` named as its hypothesis
supplier. This delivery is that composition.

### The consumer, already named twice

The plain capstone
(`empiricalWalkDistribution_stationary_tail_of_depth`) is framed by its
own docstring as a guarantee for *an agent that can only simulate the
walk*: past the depth certificate's threshold, `n` simulated
trajectories of length `t₀` estimate `π i` to `ε` at a Hoeffding tail.
That agent's plain hypothesis supplier is the plain **entrywise**
ceiling, whose `0 < r < 1` rate certificate is **provably
unsatisfiable on every connected bipartite graph** — paths, trees,
grids, the exact fixtures the setting names (`lazy-walk-mixing.md`'s
leverage case, fenced as never-decay pins in χ²/TV/entropy; the plain
`t_mix` object is *junk* there, `sInf ∅ = 0`). Instantiate the agent on
the bipartite class and the plain program certifies nothing. The lazy
supplier replaces the certificate hypothesis with the **computed
intrinsic rate** `(1 − λ₂/2)^t` under connectivity alone
(`lazy-mixing-time-objects.md`'s headline interface) — so the lazy
capstone instantiates on exactly the class where the plain one is dead.
This is not breadth beside the program; it is the program's own
recorded extension to its named fixture class.

### Why this outranks the other queue items

The execution plan's remaining candidates are: the reverse TV → χ²
calculus (no consumer named — undeliverable under the repo's
name-the-consumer discipline), log-Sobolev (adoption is explicitly an
operator decision, not missing machinery), and two operator-gated items.
This is the only named, ungated, hypothesis-supplied follow-on on the
queue.

## The delivery

Three theorems in `Scaffold/Derived/EmpiricalStationary.lean`'s new
`LazyStationaryLimit` section, each the lazy clone of the plain
`StationaryLimit` section at `q = lazyWalkDistribution A t₀ x`:

1. `empiricalLazyWalkDistribution_tail` — the fixed-time form: `n`
   i.i.d. samples of the `t₀`-step *lazy* walk law concentrate around
   the law itself at `2 exp (−2 n t²)`. The law's probability-vector
   certification is proved (`lazyWalkDistribution_nonneg`,
   `sum_lazyWalkDistribution`) — no connectivity, no symmetry.

2. `empiricalLazyWalkDistribution_stationary_tail` — the bias-term
   form: at any threshold strictly above the **computed** bias
   `(1 − λ₂/2)^{t₀} √(π i ((π x)⁻¹ − 1))`, the exponent pays only for
   the residual `t − bias`. Hypothesis set = the entrywise lazy
   ceiling's own (connectivity the only graph hypothesis, plus
   `2 ≤ |V|` for `secondEval`): **no rate certificate at all** — the
   plain twin's caller-supplied `r` replaced by the intrinsic rate,
   which is the entire point of the lazy program.

3. `empiricalLazyWalkDistribution_stationary_tail_of_depth` — the
   capstone: past the lazy ceiling's own threshold at `ε / 2` (the
   `log (√(π i ((π x)⁻¹ − 1)) / (ε/2)) / log (1/(1 − λ₂/2)) ≤ t₀`
   form), `n` simulated lazy trajectories estimate `π i` to `ε` at
   `2 exp (− n ε² / 2)`. The `λ₂ < 2` strictness is honest and visible,
   mirroring the depth-form lazy TV ceiling (K₂'s rate-0 corner is
   excluded; there the bias-term form still instantiates since the bias
   is exactly `0` for `t₀ ≥ 1`).

All three are pure hard crust: the tail engine is the 2026-08-30-retired
(locally proved) `hoeffding_empirical`, the bias is the proved entrywise
lazy ceiling, the threshold calculus is the proved
`pow_mul_le_of_log_threshold`.

### QA (the new lazy section of `EmpiricalStationary_QA.lean`)

On the three-vertex path `P₃` — the bipartite fixture class the plain
program cannot reach — with `λ₂ = 1` pinned (`path_secondEval_QA`, rate
`1/2`):

- **The fence (the leverage case made negative):** no `r ∈ (0, 1)`
  certificate for the *plain* walk exists on `P₃` — the plain capstone's
  hypothesis set is provably unsatisfiable there (from
  `chiSquareDistance_le_of_connected` at a would-be certificate against
  the pinned `path_plain_never_QA`: `χ²_plain(center, t) ≡ 1` forces
  `r² ≥ 1`). The lazy capstone instantiates on the same fixture — the
  periodicity fix read at the sampling level.
- The **bias-term instance** from the corner start (bias `(1/2)^{t₀+1}`
  at the pinned rate, the raw true deviation computed beside it).
- The **depth-form capstone instance** at `t₀ = 3`, `ε = 1/4`, `n = 2`
  closing at `2 exp (−1/8)` — the same `log(4√3)/log 2 ≤ 3` threshold
  the delivered lazy-ceiling QA pinned (`path_lazy_corner_ceiling_slack_QA`
  reuse).
- The **exact-stationary contrast** from the center start: the true
  deviation is `0` at every `t ≥ 1` (`path_lazy_center_mix_all_QA`)
  while the theorem still quotes the honest positive bias — the
  slack-witness shape.
- **Non-vacuity**: the measured event genuinely carries mass.

Acceptance: `#print axioms` on every new declaration exactly
`propext, Classical.choice, Quot.sound`; the full ladder green.

## Cost and risk

One new section in an existing module plus a QA section — no new
modules, no import changes (`EmpiricalStationary.lean` already imports
`Mixing` and `Oversmoothing`). Statement shapes are fixed by the plain
twins; the only design freedom is the intrinsic-rate bias replacing the
`r`-certificate, which is the delivery's point. Risk: low — every
ingredient is proved hard crust; the composition mirrors a delivered
proof line-for-line.

## Delivery record (2026-09-02, run `20260902T003639Z-run-1`)

Delivered as proposed, with one arithmetic correction the spike's
elaborator caught (below). The three theorems landed in
`Derived/EmpiricalStationary.lean`'s `LazyStationaryLimit` section at
the proposed shapes; the QA landed as the lazy section of
`EmpiricalStationary_QA.lean`.

### What was delivered

- `empiricalLazyWalkDistribution_tail` — the fixed-time form at the
  lazy law (the plain twin's `hoeffding_empirical_iid` composition at
  `q = lazyWalkDistribution A t₀ x`, certified by the proved
  `lazyWalkDistribution_nonneg`/`sum_lazyWalkDistribution`).
- `empiricalLazyWalkDistribution_stationary_tail` — the bias-term form
  at the **computed intrinsic-rate bias**: hypothesis set is exactly
  `lazyWalkDistribution_sub_stationaryVec_abs_le`'s (connectivity the
  only graph hypothesis, `2 ≤ |V|` for `secondEval`), the triangle
  route over the entrywise lazy ceiling — no rate certificate anywhere.
- `empiricalLazyWalkDistribution_stationary_tail_of_depth` — the
  capstone: `r := 1 − λ₂/2` with `0 < r` derived from the honest
  visible `λ₂ < 2` and `r < 1` from connectivity
  (`secondEval_normalizedLaplacian_pos_of_connected`), `b ≤ ε/2` through
  the proved `pow_mul_le_of_log_threshold`, then the plain twin's
  exponent-domination block verbatim.

### The QA (12 lemmas, all on the bipartite path P₃ at the pinned gap
`λ₂ = 1` — rate `1/2`)

- `path_plain_cert_fenced_QA` — **the leverage case made negative**: no
  `r ∈ (0,1)` certificate for the plain walk exists on P₃ (a would-be
  certificate fed to the proved `chiSquareDistance_le_of_connected`
  bounds the center-start plain χ² by `r²`, against the pinned
  `χ²_plain ≡ 1` — forcing `r² ≥ 1`).
- `path_lazy_tail_instance_QA` — the fixed-time instance (bound
  `2 exp(−4)`).
- `path_lazy_corner_biasConstant_QA` (`√(π₀·((π₀)⁻¹−1)) = √3/2`),
  `path_lazy_stationary_tail_bias_QA` (**the bias-term instance** — the
  fixture class the plain twin cannot reach), with
  `path_lazy_corner_law_two_QA` (`ν_lazy(2, corner) = (3/8, 1/2, 1/8)`),
  `path_lazy_corner_deviation_two_QA` (the raw true deviation `1/8`),
  and `path_lazy_corner_bias_two_le_QA` (`1/8 ≤ √3/8`, the fold-in is
  honest slack) beside it.
- `path_lazy_capstone_threshold_QA` (`log(4√3)/log 2 ≤ 3` — the same
  threshold the delivered lazy-ceiling QA pinned) and
  `path_lazy_capstone_depth_QA` (**the capstone instance**: `t₀ = 3`,
  `ε = 1/4`, `n = 2`, closing at `2 exp(−1/16)`), with
  `path_lazy_corner_entry_three_QA` (`ν_lazy(3, corner) 0 = 5/16`) and
  `path_lazy_capstone_event_ge_QA` (non-vacuity: the both-at-0 cylinder
  at mass `25/256` sits inside the measured event).
- `path_lazy_center_contrast_QA` — **the exact-stationary contrast**:
  from the center start the true deviation is `0` at every `t₀ ≥ 1`
  while the quoted bias is honestly positive — the theorem never claims
  the bias vanishes where the truth does.

### The arithmetic correction (the spike discipline working)

The first draft stated the capstone instance's bound as
`2 exp(−1/8)`. `norm_num` reduced the proof's numeric bridge to
`False`: the exponent is `−n·ε²/2 = −2·(1/16)/2 = −1/16`, not `−1/8`
— a plain normalization slip of exactly the kind QA exists to catch,
caught before any shelf edit (the plain twin's identical-shape triangle
instance also closes at `−1/16`, which the cross-check confirmed).

### Technique findings (the pinned Mathlib/toolchain, for future runs)

1. **`chiSquareDistance_le_of_connected`'s binder order**: the start
   vertex `x` comes *before* `hrate`; passing the certificate one slot
   early elaborates it as the start vertex and reports a confusing
   `Prop`-vs-type mismatch at a distance.
2. **`Real.sqrt_lt_sqrt` here is two-argument** (`(ha : 0 ≤ a)
   (h : a < b) : √a < √b`) and yields `√3 < √16`, not `√3 < 4`; the
   robust route to a numeric strict bound is the one-argument
   `Real.sqrt_le_sqrt` + `Real.sqrt_sq` (`√4 = 2`) and `linarith`, not
   rewriting `√16`.
3. **`Real.log_mul` with explicit `≠ 0` proofs pins the pattern's
   `a`**: the delivered QA's double-`log_mul` idiom does not match
   `log (2 * 2 * 2)` (left-associated, so the pattern reads
   `log (2 * ?b)`); `Real.log_pow 2 3` — explicit, hypothesis-free — is
   the robust route to `log 8 = 3 · log 2`.
4. **`rw [hk]` with `hk : (2 : ℕ) = 1 + 1` fails** on goals carrying
   ℝ numerals (motive not type correct); the robust succ-shift on a
   literal time is `show lazyWalkDistribution A (1 + 1) x = _` (defeq
   `1 + 1 ≡ 2`), then `rw [lazyWalkDistribution_succ]`.
5. **`norm_num` folds `r ^ (2 * 1) * 1` to `|r|`** (a `sq_abs`-style
   normalization), so the fence discharges through
   `rw [abs_of_pos hr0]` + `linarith`, not a `sq_lt` lemma.
6. **A numeral in a proof slot** (`(1/4)` where `hε : 0 < ε` is
   expected) reports "numerals are data in Lean, but the expected type
   is a proposition" at the *application* site; name the implicit
   (`(ε := 1/4)`) rather than relying on positional inference.
7. **`Real.mul_one` does not exist** in this pin (the root `mul_one`
   does), and inside a final `exact`, dropping goal-normalization
   rewrites in favor of proving the target's exact shape is often
   cleaner than pre-normalizing.
8. **`Real.sqrt_div` here is `{x} (hx : 0 ≤ x) (y : ℝ)`** — the
   numerator's nonnegativity proof first, the denominator as a *value*;
   `ENNReal.ofReal_mul` takes exactly one side goal (`0 ≤ p`), unlike
   the two-proof shapes earlier pins used.

### Verification

Spike first (`wip/lazystat_spike.lean` — shelf + full QA + the axiom
audit iterated to zero errors/zero warnings before any shelf edit,
including the arithmetic correction above); `lake env lean` zero errors
on both touched modules (the QA-imports-shelf stale-olen boundary met
once and remediated per the completeness script's docstring); explicit
`lake build` targets ✔ on both; **`#print axioms` via
`wip/lazystat_axcheck.lean` on all 15 declarations: exactly
`propext, Classical.choice, Quot.sound`**; **full `lake build` ✔
immediately followed by `check_build_completeness.py` — 133 source
files, 133 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (5, both PF findings allowlisted-confirmed);
`check_refutation_independence` (10-tag clean — no tags added, nothing
touches an axiom); `check_public_reachability` clean (63 repo modules);
`check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (**3612/5/0**) with the verification row;
**map-freshness exit 0** after the 3600 → 3612 stats sync in both map
files and SVG regeneration (no station — no tier change). Records
updated: this proposal, `proposals/README.md` (Delivered row), README
(3612 + the walks-and-mixing row's lazy-sampling extension), the radar
(QA axis synced 3600 → 3612 held at 4.0), `index/map/spectral_graph.md`
(the Derived empirical-stationary section's lazy rows), the scoreboard
verification row, both map data tables + regenerated SVG, the QA
module's purpose header, the backlog item-2 update, the execution plan,
and the activity log. Nothing committed; the previous runs' uncommitted
deliveries preserved.

## Sources

- Levin, Peres & Wilmer, *Markov Chains and Mixing Times*, ch. 5.2
  (lazy chains), ch. 6 (the empirical estimation setting), ch. 12
  (spectral certificates) — the plain program's own citation.
- Tropp-style Hoeffding for bounded i.i.d. summands, as retired to a
  proved theorem 2026-08-30 (`hoeffding_empirical`).
