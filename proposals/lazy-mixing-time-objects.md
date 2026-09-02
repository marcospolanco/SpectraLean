# Proposal: The Lazy `t_mix` Object and the Depth-Form Lazy Ceiling

**Status:** COMPLETE — proposed and delivered in the same run
(`20260901T224217Z-run-1`), per the same-run pattern of
`lazy-walk-mixing.md` and `poincare-inequality.md`. Zero new axioms
(count stays 5): `#print axioms` via `wip/lazymix_axcheck.lean` on all
20 audited declarations (9 shelf + 11 QA) reads exactly
`[propext, Classical.choice, Quot.sound]` — pure hard crust. QA
3589 → 3600.

Companion to [Strategy](../docs/1_STRATEGY.md), to
[lazy-walk-mixing.md](lazy-walk-mixing.md) (the parent delivery whose
recorded follow-ons these are), and to
[message-passing-depth-mixing-bound.md](message-passing-depth-mixing-bound.md)
+ [total-variation-mixing-conversion.md](total-variation-mixing-conversion.md)
(the plain ceiling and `t_mix` packages these compositions mirror).

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources (lazy
Markov chains, mixing times, and their spectral bounds are classical;
see Sources below). Do not copy this proposal verbatim.

## The obligation this discharges

`lazy-walk-mixing.md` delivered the lazy chain's *rate* family — the
intrinsic-rate χ²/TV/entropy corollaries in `Mixing.lean` — and
recorded two follow-ons as "one composition each, gated on a consumer
naming a bipartite-input instance":

1. the **depth-form lazy ceiling** (the plain family's
   `walkDistribution_tvDistance_le_of_depth` at the lazy law), and
2. the **`t_mix` objects at `lazyWalkDistribution`** (the plain
   `walkMixingTimeFrom` package at the lazy law).

### The consumer gate, discharged by naming the bipartite-input instance

The empirical-stationary-distribution program's capstone
(`Derived/EmpiricalStationary.lean`,
`empiricalWalkDistribution_stationary_tail_of_depth`) is framed by its
own docstring as a guarantee for *an agent that can only simulate the
walk*: past the depth certificate's threshold, `n` simulated
trajectories estimate `π i` to `ε` at a Hoeffding tail. That agent's
hypothesis supplier is the plain **entrywise** ceiling
`walkDistribution_sub_stationaryVec_le_of_depth` (the entrywise
extraction folded in by the triangle route) — whose `0 < r < 1` rate
certificate is **provably unsatisfiable on every connected bipartite
graph** (the parent delivery's own leverage case; fenced as never-decay
pins in three metrics). Instantiate the agent's setting on the
canonical bipartite inputs — a path, a tree, a grid — and the plain
program certifies *nothing*: the walk law provably never approaches π.
The field-standard fix (LPW ch. 5.2) is the lazy chain. The named
consumer is therefore **the lazy entrywise ceiling as that extension's
hypothesis supplier** (the capstone's lazy analogue,
`empiricalLazyWalk…` — recorded here as the named follow-on this
delivery unlocks, not delivered in this run), instantiated on the
bipartite class; the QA below names the instances concretely (`K₂`,
`P₃`). Secondary consumer, unchanged from the plain family's own
delivery record: LPW's canonical `t_mix` packaging, whose per-start
discrete object is the field-standard way every textbook states a
discrete mixing bound.

### Why the objects (not just the rates) matter

The plain `t_mix` objects are *junk* precisely on the bipartite class:
the witness set `{t | ∀ s ≥ t, TV_s ≤ ε}` is empty at every reachable
`ε` (TV ≡ 1/2 at every time on `K₂` — fenced on file), so
`walkMixingTimeFrom = sInf ∅ = 0` with no mixing at all (the recorded
junk corner). The lazy twins carry genuine, finite, exactly-pinnable
mixing times on the same fixtures — the periodicity fix completed at
the object level, which is where every downstream consumer (LPW's
`t_mix := t_mix(1/4)` convention, the empirical agent above, the
escalation class) reads it.

## The delivery

### Engine (`Mixing.lean`, one lemma beside the signless engine)

- `secondEval_normalizedLaplacian_le_two` : `λ₂(L_sym) ≤ 2` — the
  missing spectrum cap. Route: sortedness (`evals_sorted`) gives
  `evals ⟨1⟩ ≤ evals ⟨last⟩`, `evals_mem_eigvalOf` exhibits the last
  entry as some `eigvalOf i`, and the delivered pointwise signless
  bound `eigvalOf_normalizedLaplacian_le_two` closes. Today only the
  pointwise `μ ≤ 2` and the nonzero-mode `λ₂ ≤ μ` exist; the cap makes
  the lazy rate `1 − λ₂/2` nonnegative without a strictness hypothesis
  (it is exactly `0` on `K₂`).

### Shelf (`Oversmoothing.lean`, new `LazyMixingTime` section)

1. `lazyWalkDistribution_sub_stationaryVec_abs_le` — the **entrywise
   lazy ceiling at the intrinsic rate** (the named consumer's
   interface): `|ν_lazy(t) x y − π y| ≤ (1−λ₂/2)^t · √(π y · ((π x)⁻¹
   − 1))` with connectivity the only graph hypothesis — the plain
   twin's `r`-certificate hypothesis *replaced by the computed
   intrinsic rate*, which is the entire point of the lazy program.
   Route: the plain twin's own proof at the lazy objects (one χ²
   summand against the whole sum, then the delivered
   `lazyChiSquareDistance_le_of_connected`).
2. `lazyWalkDistribution_tvDistance_le_of_depth` — the **depth-form
   TV ceiling**: `TV_lazy(t) ≤ ε` past the threshold
   `log(√((π x)⁻¹−1)/(2ε))/log(1/(1−λ₂/2))`, at `0 < λ₂ < 2` (both
   strictness halves derived: `0 < λ₂` from connectivity via the
   Fiedler mirror, `λ₂ < 2` honest and visible — the `K₂` rate-0
   corner is excluded and documented; on `K₂` the object is exact in
   one step anyway, pinned in QA). Composes the delivered
   `lazyWalkDistribution_tvDistance_le_of_connected` with the generic
   `pow_mul_le_of_log_threshold`.
3. `lazyWalkMixingTimeFrom A x ε := sInf {t | ∀ s ≥ t, TV_lazy(s,x)
   ≤ ε}` — the **object**, plus its package: `_bddBelow`,
   `_le_of_cert` (the certificate interface), **`_spec`** (attainment:
   `csInf_mem` at the well-ordering — the plain twin's own advantage,
   inherited verbatim), `_anti` (ε-antitonicity), and
   **`_le_of_connected`** — the intrinsic-rate spectral ceiling
   `t_mix(ε) ≤ ⌈log(√((π x)⁻¹−1)/(2ε))/log(1/(1−λ₂/2))⌉`.

### QA (`Mixing_QA.lean`, the lazy section's extension)

On the bipartite fixtures, exact closed forms pinned in *both*
directions (the `_le_of_cert`/`_spec` interface, both load-bearing on
the object's exact shape):

- **K₂**: `t_mix_lazy(0, 1/4) = 1` (TV(0) = 1/2 fails, TV(s ≥ 1) = 0
  witnesses), the entrywise bound **attained exactly** at rate `0`
  (both sides zero), and the **object-level periodicity contrast**:
  plain `t_mix(1/8) = 0` *junk* (empty witness set, the recorded
  corner) against lazy `t_mix(1/8) = 1` genuine.
- **P₃ center**: `t_mix_lazy(center, 1/4) = 1` and the **spectral
  ceiling attained exactly** (both evaluate to `1` at the pinned gap
  `λ₂ = 1` — no slack anywhere in the package).
- **P₃ corner**: the exact TV closed form `TV_lazy(1+t) = 2^{−(t+1)}`
  at every time (induction through the law's evolution:
  `P_Lᵀ(1,0,−1) = (1/2)(1,0,−1)` — the pure `μ = 2` mode dead after
  one step, the `μ = 1` mode halving), giving `t_mix_lazy(corner,
  1/8) = 2` in both directions and the ceiling **computed with honest
  slack** (ceiling `3` vs truth `2` — the threshold `log(4√3)/log 2`
  strictly between `2` and `3`).

### Statement-shape decisions (pre-spike)

- The entrywise ceiling states the *intrinsic* rate (no `r`
  hypothesis) — nonnegativity of `r^t` from the new λ₂ ≤ 2 cap. The
  depth/ceiling statements carry the visible `λ₂ < 2` strictness
  because the log threshold genuinely needs `0 < r`; on `K₂` the rate
  is exactly `0` and those statements are honestly outside their
  hypothesis set (the object QA covers `K₂` directly instead). No
  statement hides this.
- The per-start object only; the uniform lazy twin stays ungated (the
  plain uniform object's consumer class has no lazy instantiation
  named).

## Sources

- Levin, Peres & Wilmer, *Markov Chains and Mixing Times*, ch. 5
  (lazy chains; the convention `P_L = (P+I)/2`), ch. 12
  (`t_mix`-ceiling routes), ch. 20 (mixing-time objects) — the same
  locators the parent delivery and the plain `t_mix` package record.

## Verification plan

Spike first (`wip/lazymix_spike.lean`): all shelf declarations, the
full QA section, and the `#print axioms` audit iterated to zero
errors/zero warnings before any shelf edit. Then `lake env lean` on
both touched modules, explicit `lake build` targets, full `lake build`
+ `check_build_completeness.py`, and the records ladder
(`lint_axioms`, `check_refutation_independence`,
`check_public_reachability`, `check_citations`,
`check_markdown_links`, scoreboard regeneration,
`check_scaffold_map_freshness` after the stats sync).

---

## Delivery record (2026-09-01, run `20260901T224217Z-run-1`)

Delivered exactly as scoped, with one scope reduction recorded below.

**Landed.** `Mixing.lean`: `secondEval_normalizedLaplacian_le_two`
beside the signless engine (sortedness + `evals_mem_eigvalOf` + the
pointwise bound — with the pointwise twin, the whole normalized
spectrum now lives in `[0, 2]` at the cap level, and the lazy rate is
nonnegative by theorem rather than by hypothesis). `Oversmoothing.lean`:
the `LazyMixingTime` section — all seven declarations of the plan,
at the plan's statement shapes (the entrywise ceiling at the intrinsic
rate with connectivity the only graph hypothesis; the depth/ceiling
statements carrying the honest visible `λ₂ < 2`; the object package
with the inherited `csInf_mem` attainment).

**QA landed** (11 declarations, both-direction pins throughout): the
exact corner-start TV closed form `TV_lazy(1+t, corner) = (1/2)^{t+2}`
at every time (induction through the transpose's action on the
antisymmetric mode, `P_Lᵀ(1,0,−1) = (1/2)(1,0,−1)`, and the shelf's
`π`-stationarity), which yields `t_mix_lazy(corner, 1/8) = 2` pinned in
both directions; `t_mix_lazy(center, 1/4) = 1` with the ceiling
**attained exactly** (both evaluate to `1`); the corner ceiling with
honest slack (`3` vs `2`); `t_mix_lazy(K₂, 0, 1/4) = 1`; the
**object-level periodicity contrast** (plain `t_mix(K₂, 1/8) = 0` junk
against lazy `= 1` genuine — the fence proving the plain witness set
empty through the never-decay pin `k2_disc_tv_eq_QA`); the entrywise
bound attained exactly on `K₂` (rate `0`, both sides zero) and with
witnessed slack on the path (`1/4 < √3/4`).

**Scope reduction.** The plan's `path_lazy_matrix_QA` (the full
nine-entry transpose-matrix pin) was dropped in favor of stating the
transpose's *action* on the antisymmetric mode (`mulVec` at one vector)
— the 2D-matrix-literal entry reduction proved unreliable (finding 5
below) and the action statement is what the induction consumes anyway.

**Verification.** Spike first (`wip/lazymix_spike.lean`, iterated to
zero errors/zero warnings/zero sorries before any shelf edit); `lake
env lean` clean on all three touched modules (only the QA module's 3
recorded pre-existing benign `ring_nf` notes); explicit `lake build`
targets ✔ on all three; `#print axioms` on all 20 new declarations:
exactly the standard three; full `lake build` ✔ +
`check_build_completeness.py` — 133 source files, 133 fresh artifacts,
0 stale, 0 missing, exit 0; the full ladder clean (`lint_axioms`,
`check_refutation_independence` 10-tag, `check_public_reachability` 63
modules, `check_citations`, `check_markdown_links`,
`check_backlog_freshness`, scoreboard 3600/5/0, map-freshness exit 0
after the stats sync + SVG regeneration).

**Corner analysis (the hypothesis honesty pass).** The depth/ceiling
statements' `λ₂ < 2` strictness is genuine, not decorative: on `K₂`
the pinned gap is exactly `2` (the rate is `0`, the log threshold
degenerate) and those statements are honestly outside their hypothesis
set there — covered instead by the direct object pins (`t_mix = 1` in
both directions). The entrywise ceiling needs no strictness (the λ₂ ≤ 2
cap gives rate nonnegativity; `0^0 = 1` keeps `t = 0` sound). The
object's junk corner (unreachable `ε` → `sInf ∅ = 0`) is unchanged
from the plain twin and documented in the docstring.

**Technique findings** (all from the spike loop; recorded for the next
run's amortization):

1. **`pow_succ`'s product order.** In the pinned Mathlib `pow_succ :
   a ^ (n + 1) = a ^ n * a` — the reversed order against the classical
   spelling. `rw [pow_succ]` on a goal whose other side spells
   `a * a ^ n` leaves a `mul_comm` residue that rw's closing `rfl`
   cannot discharge; add the explicit `mul_comm` rewrite to the chain.
2. **`ring` vs division-form pow bases.** `ring` cannot close
   commutativity goals carrying a division-form pow atom
   (`(1/2 : ℝ)^(t+2) * (1/2) = (1/2) * (1/2)^(t+2)`), while it
   succeeds on the inverse-normalized form
   (`((2 : ℝ)^(t+2))⁻¹ * 2⁻¹ = 2⁻¹ * ((2 : ℝ)^(t+2))⁻¹`) — on which,
   in turn, `ring_nf` fails. Robust idioms: make the scalar an opaque
   local (`set c := (1/2 : ℝ)^(t+2)`) before entry arithmetic, or
   normalize to the `1/(2^n)` form the shipped QA already prefers.
3. **Inline `by` under `congrArg`.** `exact congrArg (· • v) (by
   ring)` fails even when `ring` closes the instantiated goal — the
   `by`-block elaborates against `congrArg`'s still-unassigned
   metavariables. Pre-bind the equality as a `have`, or use a term
   (`mul_comm _ _`) whose own metavars unify against the goal.
4. **`Matrix.mulVec_smul`** (`M *ᵥ b • v = b • M *ᵥ v`) exists and
   replaces a fragile `simp [mul_comm, mul_left_comm, …]`
   scalar-extraction proof outright.
5. **2D matrix literals do not entry-reduce reliably.** `!![a, b; c,
   d]`-shaped statement RHSes get stuck at the far corner in an
   eta-collapsed `vecHead (vecTail fun i => …)` state under both `simp`
   and `simp only` with the `cons_val` family; 1D vector literals
   reduce fine once `Matrix.cons_val_succ` joins the set. Pin vector
   equalities or `mulVec` actions, not 2D literals.
6. **Applying `Monotone (evals hM)`** wanted the two `Fin` index
   arguments pre-bound as `have`s with anonymous-constructor-free
   proofs (`Fin.mk_le_mk.mpr (by omega)`); the direct
   anonymous-constructor application elaborated the coercion shape
   instead of the `≤`.
7. **Name drift.** `div_div` (not `div_div_eq_div_mul`) is this pin's
   `(a / b) / c = a / (b * c)`; `Real.sqrt_mul` takes the value `y`
   explicit (`Real.sqrt_mul (h : 0 ≤ x) (y : ℝ)`); and λ remains a
   reserved token (`hλ₂` → `hslt` — the parent's finding, re-hit).
8. **One-shot abs-sum evaluation.** The file's own idiom — `rw
   [tvDistance]` *first*, then `norm_num […, neg_sub, abs_of_neg,
   abs_of_nonneg]` — evaluates the ℓ¹ abs-sums that neither bare
   `simp` (leaves `|1 − 2⁻¹|`-shaped residues) nor `norm_num` without
   the leading `rw` (leaves `|4⁻¹|`-shaped residues) closes reliably.
9. **The stale-olen boundary, shelf-flavored.** After landing the
   `Mixing.lean` lemma, `lake env lean Oversmoothing.lean` failed with
   `unknown identifier 'secondEval_normalizedLaplacian_le_two'` until
   the explicit `Mixing` target rebuilt — the documented
   QA-imports-shelf recurrence, now also met at the
   shelf-imports-shelf boundary.
