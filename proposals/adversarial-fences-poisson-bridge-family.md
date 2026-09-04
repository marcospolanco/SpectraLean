# Adversarial Fence Audit of the Poisson-Bridge Family

**Status:** COMPLETE (delivered 2026-09-03, same-run)  
**Proposer:** autonomous run `20260903T033044Z-run-1`  
**Consumes:** `governance/ADVERSARIAL_REVIEW.md`, the three prior
family-audit delivery records
(`adversarial-fences-tv-dobrushin-engines.md`,
`adversarial-fences-lazy-family.md`,
`adversarial-fences-entropy-family.md`)

## Motivation

The standing handoff (execution plan, entropy-family delivery) names
"the Poisson-bridge and primitivity-supplier QA families" as the open
audit frontiers of the audit-shaped adversarial pass over
mixing-cascade QA. The Poisson-bridge family is the older of the two:
its QA was delivered 2026-09-01
(`proposals/continuous-time-chi-square-mixing.md`, second follow-on)
and **never independently re-read** — two days before the
adversarial-review discipline produced its first fence. The family is
the mixing program's continuous↔discrete hinge: the Poissonization
identity (`contWalkDistribution_eq_tsum`), the TV convexity toolkit
(`tvDistance_tsum_le`, `tsum_eq_range_add`), and the
comparability/transfer pair
(`contWalkDistribution_tvDistance_add_le`,
`contWalkDistribution_tvDistance_le_of_discreteMixing`) that every
continuous-time capstone and the discrete `t_mix` object's bridge
composition route through.

The existing `PoissonBridge` QA section holds positive instances
(triangle closed forms, both theorem instances at `t = 8`, `m = 2`,
the anti-monotonicity instance) and two periodicity witnesses
(`k2_no_discrete_mixing_QA`, `k2_reverse_comparability_QA` — both
statement-level, neither hypothesis-form). No clause of the family has
a negative witness in the repository.

## Audit target

The family as delivered — 23 shelf declarations:

- `Mixing.lean`'s Poisson-bridge section (21): `poissonWeight`,
  `poissonWeight_nonneg`, `poissonWeight_hasSum_one`,
  `poissonWeight_summable`, `poissonWeight_tsum_eq_one`,
  `walkDensity_eq_pow_walkTransitionMatrix_mulVec`,
  `hasSum_poisson_walkDensity`, `contWalkDensity_eq_tsum`,
  `contWalkDistribution_eq_tsum`,
  `tvDistance_le_one_of_nonneg_of_sum_eq_one`,
  `walkDistribution_tvDistance_le_one`,
  `tvDistance_walkTransitionMatrixTranspose_mulVec_le`,
  `tvDistance_walkTransitionMatrixTranspose_pow_mulVec_le`,
  `walkTransitionMatrixTranspose_pow_mulVec_stationaryVec`,
  `walkDistribution_add`, `walkDistribution_tvDistance_anti`,
  `tsum_eq_range_add`, `tvDistance_tsum_le`,
  `contWalkDistribution_tvDistance_le_tsum`,
  `contWalkDistribution_tvDistance_add_le`,
  `contWalkDistribution_tvDistance_le_of_discreteMixing`;
- `Heat.lean`'s two generic helpers (`pow_smul_matrix`,
  `matrix_exp_smul_one`).

The clause census at audit time: **45 load-bearing clauses** (the
`[Nonempty V]` instance-arguments and the hypothesis-free identities —
`poissonWeight`'s mass triple, `walkDistribution_add`, both `Heat`
helpers — carry none and are recorded as such).

## Step 0: the clause census (audit-shaped, before any Lean)

Per `governance/ADVERSARIAL_REVIEW.md`: for every clause, either a
fence (the negation of the conclusion at a specific instantiation,
both sides pinned to closed forms) plus an isolation companion (every
other clause verified genuine at the fixture, the dropped one verified
failing), or a recorded non-fenceable with a precise mechanism.
Fixtures reused: `negOffAdj` (kills `hnn`), `asymSwapAdj` (kills
`hA`, idempotent walk Laplacian, closed-form heat kernel), `zdAdj`
(kills `hd`), `k2Adj`/`triAdj` (genuine chains). One new fixture
forecast: an asymmetric 2-vertex chain killing `hA` for
*monotonicity* (`walkDistribution_tvDistance_anti`), where the
existing asymmetric fixtures provably cannot serve (at `asymSwapAdj`
the law is absorbed after one step, so the TV sequence is constant).

Headline fence designs (full list in the delivery record once
verified):

- **The identity's `hA` clauses** — the Poissonization identity is
  *reversibility*: `P = D⁻¹A` is π-reversible exactly when `A` is
  symmetric. At `asymSwapAdj` (nonnegative, positive degrees, `A 0 1 =
  0 ≠ 4 = A 1 0`) the discrete law from `0` is `δ₀` at every time
  (row `0` of `P` is `(1,0)`), so the Poisson mixture is the constant
  `(3, 0)` density / `(1, 0)` law — while the heat kernel's drift
  term `3(1 − e^{−t})` is genuinely nonzero. Every identity-shaped
  clause (`walkDensity_eq_pow_…`, the `HasSum`/`eq_tsum` triple,
  `walkTransitionMatrixTranspose_pow_…_stationaryVec`) dies on this
  one arithmetic, at `t = 1`.
- **The rate theorems' `hA`** — at the same fixture at `t = 2`, the
  continuous law `(1, 2(1 − e^{−2}))` has TV `1 − e^{−2} > 2/3`
  against the Poisson-averaged discrete TV (constant `2/3`): the
  dropped `tvDistance_le_tsum` and comparability statements read
  `1 − e^{−2} ≤ 2/3`, refuted from `2 < e` alone (`e² > 4 > 3`).
- **The `ht` clauses at negative time** — the Poissonization identity
  itself has *no* time clause (it holds at `t = −1`), so the
  continuous law at `t = −1` is the honest closed form
  `((1+e²)/2, (1−e²)/2)` on `K₂` (existing `k2_cont_density_neg_one`
  machinery): TV `= e²/2 > 1/2` = the Poisson-averaged discrete TV —
  the signed weights `e·(−1)ᵏ/k!` break the convexity bound exactly
  where `poissonWeight_nonneg`'s own `ht` clause fails.
- **The `hnn` clauses** — at `negOffAdj` (`P = A`, eigenvalues
  `1, 3`): the discrete TVs grow as `3ᵏ/2`, and the backward heat
  kernel grows as `e^{2t}` — at `t = 1` the continuous TV is exactly
  `e²/2` against the initial `1/2` (existing
  `negOff_cont_density_one`), killing the comparability's `hnn` at
  `m = 0`; the one-step law `(2, −1)` (existing `negOff_dist_one`)
  kills `walkDistribution_tvDistance_le_one` and the adjoint-walk
  contraction (`TV 1 → 3`).
- **`tvDistance_tsum_le`'s mass clauses** — the direct route for
  `hc`/`hc1` (a mass-`2` mixture `![4/5, 6/5]` with TV `1/2` against
  the average `1/5`), and a **new hazard class for the fence corpus:
  the divergent-tsum junk route** for `hν`/`hν1` — Poisson-summable
  weights `c k = 2^{−(k−1)}` against *geometrically growing* laws
  make both tsums in the statement non-summable, so both sides junk to
  `0` while the left TV is the honest `1/2`: `1/2 ≤ 0`, refuted
  through `tsum_eq_zero_of_not_summable`.
- **The transfer corollary's `htail`** — on the triangle at
  `t = 1/2`, `m = 2`: the genuine certificate `ε₁ = 1/6`
  (`TV_disc(k) = (2/3)·2^{−k}`), the failing tail budget `ε₂ = 1/20`
  against the honest head `(3/2)e^{−1/2}`, and the conclusion
  `(2/3)e^{−3/4} ≤ 13/60` refuted from a new shelf-free helper
  `e < 3` (series bound: `e ≤ ∑_{k<5} 1/k! + 1/60 = 109/40 < 3`
  through `Nat.factorial_mul_pow_le_factorial` and the geometric
  tail). `hmix` is already fenced (`k2_no_discrete_mixing_QA` —
  recorded, not duplicated).

Recorded non-fenceables (mechanisms to be verified precisely in the
delivery record): the `hd` clauses (ten) — with `hnn` retained,
`D⁻¹A` is honestly substochastic (a zero degree makes the row junk
`0⁻¹·0 = 0`, which is the true row value for a nonnegative isolated
vertex), `π` stays stationary for the junk-collapsed chain, so mass
conservation, the contractions, monotonicity, and the comparability
split all survive on truth; `tvDistance_tsum_le`'s `hπ`/`hπ1` — the
convexity bound is the triangle inequality against the mixture
weights and needs no structure on the target; the `_le_tsum` rate's
`hnn`/`hd` — the factorial always beats the matrix-power growth of
`ν_k`, so the Poisson-weighted series stays honest and convexity
applies; the transfer corollary's `hnn` — every symmetric stochastic
2×2 with a negative entry has spectral escape `> 1`, so no
`hnn`-failing fixture can carry a genuine `hmix` certificate (the
corollary's own hypothesis screens the broken fixtures out).

## Deliverable

A `PoissonFences` section appended to `Scaffold/QA/SpectralGraph/
Mixing_QA.lean` (after `EntropyFences`, reusing its fixtures and
closed forms), developed spike-first in `wip/poissonfences_spike.lean`
to zero errors/zero warnings before any shelf edit. QA-only, zero
axiom contact (count stays 4; `#print axioms` audit via
`wip/poissonfences_axcheck.lean` on every new declaration — expected
exactly `propext, Classical.choice, Quot.sound`; no `-- @refutes`
tags: these refute *theorem* instantiations and consume nothing
admitted). Records: this proposal (COMPLETE + delivery record with
technique findings), `proposals/README.md` (new Delivered row — plus
moving the entropy audit's misfiled row out of the Active table, an
entry finding), README, the radar (QA axis sync, score held per
protocol), `index/map/spectral_graph.md`, the backlog item-8 update +
reviewed-date bump, the scoreboard, both map data tables, the
execution plan, and the activity log.

## Consumer

None beyond the audit discipline itself: the fences are negative
witnesses that make the family's hypothesis clauses falsifiable — the
load-bearing-growth principle (`docs/1_STRATEGY.md`) applied
retroactively to the hinge every continuous-time consumer stands on.
The non-fenceable findings name removable hypotheses (the `hd` clauses
under `hnn`) without changing any public statement this run.

## Delivery record (2026-09-03)

**Delivered as `Mixing_QA.lean`'s new `PoissonFences` section — QA-only,
zero axiom contact (count stays 4; `#print axioms` via
`wip/poissonfences_axcheck.lean` on all 83 new declarations — 1 fixture
`def` (`asymFlowAdj`), 17 helper pins, 28 fences, 37 support lemmas and
companions — every one exactly `propext, Classical.choice, Quot.sound`;
no `-- @refutes` tags, since these refute *theorem* instantiations and
consume nothing admitted). QA 4012 → 4094 (+82 by the generator metric,
which counts theorems/lemmas only).**

**The 28 fences, by declaration:**

- `poissonWeight_nonneg` — `ht` at `t = −1`, `k = 1`: the weight is
  `−e < 0`.
- `walkDensity_eq_pow_walkTransitionMatrix_mulVec` — `hA` at the
  asymmetric swap, `k = 1`: the walk power sends the start density
  `(3, 0)` to `(3, 3)`; the density evolution stays `(3, 0)`. The
  identity *is* reversibility (`P = D⁻¹A` is π-reversible exactly at
  symmetry).
- `hasSum_poisson_walkDensity` — `hA`: the Poisson mixture of the
  constant `(3, 0)` densities honestly sums to `(3, 0)`, against the
  heat kernel's genuine drift `(3, 3(1 − e⁻¹))`.
- `contWalkDensity_eq_tsum` / `contWalkDistribution_eq_tsum` — `hA`:
  the same arithmetic at both packaging levels.
- `tvDistance_le_one_of_nonneg_of_sum_eq_one` — all four mass clauses
  (`hμ`, `hμ1`, `hν`, `hν1`) at two-point vectors: TV `3/2 > 1`.
- `walkDistribution_tvDistance_le_one` — `hnn` at `negOffAdj`, `t = 1`:
  the law `(2, −1)` has TV `3/2 > 1`.
- `tvDistance_walkTransitionMatrixTranspose_mulVec_le` and its power
  twin — `hnn` at `negOffAdj`: the basis pair's TV triples (`1 → 3`).
- `walkTransitionMatrixTranspose_pow_mulVec_stationaryVec` — `hA`:
  `Pᵀ π = (1, 0) ≠ (1/3, 2/3) = π`.
- `walkDistribution_tvDistance_anti` — `hnn` at `negOffAdj`
  (`TV: 3/2 → 9/2`, the two-step law `(5, −4)` pinned); `hA` at the
  **new fixture `asymFlowAdj = !![1,1;3,0]]`** (`P = [[1/2,1/2],[1,0]]`,
  `π = (2/5, 3/5)`): TV rises `1/10 → 7/20` — the existing asymmetric
  fixtures cannot serve (at the swap the law is absorbed in one step,
  so the TV sequence is constant).
- `tsum_eq_range_add` — `hsm` at the constant-one sequence, `m = 1`:
  both tsums junk to `0` against the head `1`.
- `tvDistance_tsum_le` — `hc` at the alternating geometric weights
  `(3/2)(−1/2)ᵏ` against the geometric family
  `ν k = (1/2 ± (1/8)(−1/2)ᵏ)`: the mixture `(3/4, 1/4)` has TV `1/4`
  against the weighted average `3/20` — the signed weighting loses
  the triangle slack; `hc1` at the mass-`2` single-point weight
  (`TV 1/2 > 1/5`); **`hν` and `hν1` by the divergent-tsum junk route**
  — the summable weights `1/2·2⁻ᵏ` against the growing families
  `(2ᵏ⁺¹, 1 − 2ᵏ⁺¹)` and `(2ᵏ⁺¹, 2ᵏ⁺¹ − 1)` make every series in the
  statement non-summable (`tsum_eq_zero_of_not_summable`), so both
  sides junk to `0` against the honest left TV `1/2`. **First
  divergent-tsum junk fence in the corpus** — the tsum twin of the
  junk-integral hazard class (`docs/2_ARCHITECTURE.md` §5).
- `contWalkDistribution_tvDistance_le_tsum` — `hA` at the swap,
  `t = 2`: the continuous TV `1 − e⁻²` (the mass-drift law
  `(1, 2(1 − e⁻²))` pinned through the idempotent-Laplacian heat
  kernel) against the Poisson average of the constant discrete `2/3`,
  refuted from `e² > 4 > 3`; `ht` at the edge `t = −1`: the signed
  weights leave the continuous TV at `e²/2` against the average `1/2`.
- `contWalkDistribution_tvDistance_add_le` — `hA` at the swap
  (`m = 0`, same numbers); `hnn` at `negOffAdj` (`t = 1`, `m = 0`: the
  backward-semigroup law `((1+e²)/2, (1−e²)/2)` has TV `e²/2 > 1/2` =
  the initial TV); `ht` at the edge (`t = −1`, `m = 0`).
- `contWalkDistribution_tvDistance_le_of_discreteMixing` — `hA`
  (both certificate clauses genuine: `ε₁ = 2/3` attained, empty head
  `≤ 0`); `ht` (same at the edge, `ε₁ = 1/2`); **`htail`** on the
  triangle at `t = 1/2`, `m = 2`: the certificate `ε₁ = 1/6` genuine
  (`TV_disc(k) = (2/3)·2⁻ᵏ`), the tail budget `ε₂ = 1/20` against the
  honest head `(3/2)e^{−1/2}`, conclusion `(2/3)e^{−3/4} ≤ 13/60`
  refuted from **the new series bound `e < 3`** (`exp_one_lt_three`:
  the range-5 partial sum `65/24` plus the factorial-vs-geometric tail
  `1/60`, through `Nat.factorial_mul_pow_le_factorial`). `hmix` was
  already fenced (`k2_no_discrete_mixing_QA`) — recorded, not
  duplicated.

**The recorded non-fenceables** (each with its mechanism, per the
audit discipline): the ten `hd` clauses — with `hnn` retained, a zero
degree makes the `D⁻¹A` row the *true* zero row (`0⁻¹·0 = 0` for
nonnegative isolated vertices), `π` stays stationary for the
junk-collapsed substochastic chain, so mass conservation, the
contractions, monotonicity, the identities (which are symmetry-only
algebra), and the comparability split all survive on truth —
proof-shaped hypotheses, the same class as the lazy audit's `hd`
findings; `tvDistance_tsum_le`'s `hπ`/`hπ1` — the convexity bound is
the triangle inequality against the mixture weights and needs no
structure on the target (mass only feeds the summability bookkeeping);
the `_le_tsum` rate's `hnn`/`hd` — the factorial always beats the
matrix-power growth of `ν_k` (finite matrix, exponential at worst), so
the Poisson-weighted series stays honest and convexity applies
sign-free; the transfer corollary's `hnn` — every symmetric stochastic
2×2 with a negative entry has spectral escape `> 1` (`P = [[b,c],[c,b]]`
with `c < 0` has second eigenvalue `(b−c)/(b+c) > 1`), so the discrete
TVs grow without bound and no `hnn`-failing fixture can carry a
genuine `hmix` — the corollary's own certificate hypothesis screens
the broken fixtures out.

**Two removable-hypothesis findings** (recorded, no statement changed
this run): the `hd` clauses above are removable *given `hnn`* (the
substochastic algebra is complete), and the Poissonization identity
triple's `hd` is removable outright — the identity is symmetry-only
algebra and the zero-degree corners junk-collapse consistently on both
sides (verified at `zdAdj` in the spike).

**Six technique findings:**

1. **The matrix-literal index-type trap**: `![a, b]` elaborates at
   `Fin (Nat.succ 1)`, and `omega` cannot case-split a variable of
   that type — `funext` over a bare matrix literal kills the
   file's load-bearing `omega`-rcases idiom silently. Fix: state
   pointwise pins with an explicit `∀ i : Fin 2` binder (or anchor
   the equation at a genuinely `Fin 2`-typed term). This generalizes
   the recorded `Fin`-literal shape-mismatch findings from entries
   to whole vectors.
2. `rw [h, h]` with `h : P = v` rewrites *all* occurrences in the
   first step and fails on the second — the two-occurrence idiom is
   one `rw [h]` or `simp only [h]`.
3. `rw [show ((2:ℕ) = 1 + 1 from rfl), walkDistribution_succ, ...]`
   fails with *motive not type correct* — the numeral rewrite hits
   `Fin 2` occurrences in types. Fix: `have h := walkDistribution_succ
   A 1 0` and `exact h` (the `2` vs `1 + 1` mismatch is defeq).
4. `abs` of a subtraction-of-numerals is closed by `norm_num` only
   after an explicit `abs_of_nonneg`/`abs_of_neg` sign step in
   `rw`-position; the sign side-conditions themselves default to ℕ
   unless annotated (`show (1:ℝ)/2 - 3/5 < 0`).
5. `pow_le_pow_left₀` takes `(0 ≤ a)` then `(a ≤ b)` then the
   exponent — the argument order differs from `pow_lt_pow_left₀`
   usage patterns recorded earlier.
6. `Pi.hasSum` on a matrix-literal-valued sequence inherits the
   literal's index type — entrywise HasSum construction needs the
   explicit `∀ i : Fin 2` statement before `Pi.hasSum.mpr`.

**Verification:** spike first (`wip/poissonfences_spike.lean` — the
full 83-declaration section, iterated to zero errors/zero warnings/
zero infos before any shelf edit); `lake env lean` on the touched QA
module (zero errors, zero warnings — the three positioned info-level
`ring_nf` hints confirmed pre-existing by elaborating the HEAD
baseline, which emits the same three); explicit
`lake build Scaffold.QA.SpectralGraph.Mixing_QA` ✔; **the
83-declaration axiom audit above**; **full `lake build` ✔ immediately
followed by `check_build_completeness.py` — 133 source files, 133
fresh artifacts, 0 stale, 0 missing, exit 0**; `lint_axioms` exit 0
(4 current axioms, unchanged; only the allowlisted-confirmed PF
finding); `check_refutation_independence` (9-tag clean — no tags
touched); `check_public_reachability` clean (63 repo modules);
`check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (**4094/4/0**); map freshness after the stats
sync below. One incident, recovered with no loss: a landing-script
typo truncated `Mixing_QA.lean` after `open(...,'w')` but before the
write; restored verbatim from `git show HEAD:` (the session's start
state was clean and the file had no other pending changes) and the
landing redone — the final module's diff contains only the intended
insertion.
