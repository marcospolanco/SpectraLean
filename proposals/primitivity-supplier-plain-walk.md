# The Primitivity Supplier — Connected + Odd Closed Walk ⟹ a Strictly Positive Walk Power

**Status:** COMPLETE — delivered 2026-09-02, run `20260902T181038Z-run-1`
**Kind:** hard-crust delivery (zero axiom contact; axiom count stays 4)

## The frontier

The standing execution-plan handoff (after the parametric-cycle-QA run)
names, in rough leverage order, "the first sampling-capstone *twin* with
a produced target on the undirected plain-walk side (blocked on an
irreducibility+primitivity supplier that does not exist yet —
connected+non-bipartite ⟹ a strictly positive walk power, a real
combinatorial program)". This proposal is that supplier plus its named
consumer chain.

What is on the shelf today, and what each piece waits for:

- `tvDistance_vecMul_pow_le_of_pos_power` (Mixing, delivered
  2026-09-02 with the uniform-`t_mix` run): the Doeblin rate engine —
  from `δ ≤ (P^m) i j` entrywise it derives
  `TV(ν ᵥ* P^t, π) ≤ (1 − |V|δ)^{t/m} · TV(ν, π)`. It has **no
  undirected consumer**: on the plain walk no positive power is known
  to exist except by caller fiat.
- `primitive_power_tendsto` (PrimitiveConvergence, retired from axiom
  2026-09-02): power convergence from `P.IsPrimitive`. Its `IsPrimitive`
  hypothesis is discharged on the Google walk by `isPrimitive_of_pos`
  (the teleportation floor makes the matrix itself positive) — but on
  the *plain* walk `IsPrimitive` has no supplier, so the retired
  theorem's convergence never reaches undirected input.
- The plain-walk sampling capstones
  (`empiricalWalkDistribution_stationary_tail[_of_depth]`) carry a
  caller-supplied spectral rate certificate `hrate : |1 − μ| ≤ r, r < 1`
  — provably unsatisfiable on bipartite graphs and, on non-bipartite
  ones, satisfiable only by supplying the spectrum. The PageRank family
  got its self-contained twin (`empiricalPageRank_tail_selfcontained_of_depth`)
  because the Google walk's rate is hypothesis-computable (`α`); the
  plain family has no intrinsic-rate twin because nothing connects
  graph structure to a positive power.

## The mathematical content

**Theorem (supplier, matrix level).** Let `M` be entrywise nonnegative
on a finite index type. Assume:

- `hreach`: every pair is joined by some positive power entry
  (`∀ u v, ∃ a, 0 < (M^a) u v` — irreducibility's consequence shape,
  `exists_pow_pos_of_isIrreducible` delivers it from
  `Matrix.IsIrreducible`);
- `htwo`: every index has a positive 2-cycle in the support
  (`∀ v, ∃ z, 0 < M v z ∧ 0 < M z v`);
- `hodd`: every index has an odd closed walk
  (`∀ v, ∃ t, Odd t ∧ 0 < (M^t) v v`).

Then `M.IsPrimitive`: some strictly positive power is strictly positive
entrywise.

*Proof.* For each pair `(u, v)` let `d = d(u,v)` be a witness from
`hreach`, `L₀ = L₀(v) ≥ 1` an odd closed-walk length at `v` from
`hodd`, and `z = z(v)` a 2-cycle partner from `htwo`. Concatenation of
power entries is the single-term bound (`(M^{a+b}) i j ≥ (M^a) i k ·
(M^b) k j`, one term of the defining sum), so:

- *family 1*: `(M^{d + 2j}) u v > 0` for every `j` — reach `v`, then
  bounce `j` times along `v → z → v`;
- *family 2*: `(M^{d + L₀ + 2j}) u v > 0` for every `j` — reach `v`,
  run the odd closed walk at `v`, then bounce.

The two families have opposite parities (L₀ odd), so **every**
`t ≥ g(u,v) := d(u,v) + L₀(v)` is a good length. Take `m := 1 + ∑ u v,
g(u,v)`; then `g(u,v) ≤ m` for every pair (single-term vs. sum of
naturals), and the parity split on `m − d(u,v)` lands every pair in one
of the two families. ∎

Design notes recorded before stating:

- **No symmetry hypothesis.** The first draft assumed `M.IsSymm` (the
  reversed walk gives the odd closed walk at every vertex). That is
  unavailable at the point of use: `walkTransitionMatrix A = D⁻¹A` is
  *not* symmetric on irregular graphs. The fix is to make the two
  combinatorial ingredients (`htwo`, `hodd`) support-level hypotheses
  and derive them at the graph level, where `Walk.reverse` makes
  reversal trivial. This is the hypothesis-honest shape: they say
  exactly "every vertex lies on a 2-cycle and an odd cycle of the
  support digraph".
- **Hypothesis minimality.** `htwo` is not implied by `hodd` + `hreach`
  at matrix level (the bounce needs an entry-level 2-cycle; powers of
  odd length do not give +2 steps without it — the Frobenius-coin route
  through only `⟨2p, 2p + t₀⟩` would work but drags in the coin
  problem for no downstream gain, since `hd : 0 < deg` discharges
  `htwo` in one line).
- **Degenerate corners (§5 discipline).** Conclusion is pure
  positivity (no `card`-prefactor to collapse); empty index type: all
  hypotheses vacuous except that `IsPrimitive` needs `0 < k` — the
  `1 +` in the witness `m := 1 + ∑ …` keeps the theorem true there
  with no case split. No `Measure`, no integrals.

**Theorem (walk-level wrapper).** For `A : WAdj` symmetric nonnegative
with positive degrees, if the support graph is connected and contains
*one* odd closed walk (`∃ w (p : Walk w w), Odd p.length`), then
`walkTransitionMatrix A` is primitive. The wrapper discharges `hreach`
by the walk→power bridge (walk induction; each step contributes a
positive entry via `supportGraph_adj` and `walkTransitionMatrix_apply`),
`htwo` from degree positivity (a positive row of a nonnegative-sum-one
row has a positive entry, both directions along the symmetric `A`), and
`hodd` per vertex `v` by concatenating a walk `v → w`, the odd walk at
`w`, and the *reversed* walk `w → v` — total length `2·len + t₀`, odd.

*Interface note:* the odd-walk hypothesis is stated as an explicit
`Walk w w` with `Odd p.length` rather than "non-bipartite" — the pinned
Mathlib has no `SimpleGraph.Bipartite` and no odd-cycle extraction
theorem (checked 2026-09-02), and the supplier needs only the walk, not
the cycle. "Connected + non-bipartite ⟹ primitive" is this theorem plus
the classical bipartite dichotomy, which stays ungated and unclaimed
here.

**Corollary (the rate).** Composing with
`tvDistance_vecMul_pow_le_of_pos_power` and the transpose↔`vecMul`
bridge: on the same hypothesis set,
`TV(walkDistribution A t x, stationaryVec A) ≤ (1 − |V|δ)^{t/m}` at the
produced `(m, δ)` — the plain walk's first mixing rate with **no
spectral certificate and no caller-supplied `r`**, the intrinsic-rate
family's non-bipartite member (the entrywise lazy ceiling being its
bipartite member).

**Corollary (the convergence).** `primitive_power_tendsto` reaches the
undirected plain walk: the retired theorem's first undirected consumer
(`walkDistribution A t x → stationaryVec A` at `atTop`, via
`primitive_vecMul_tendsto` and the law/power bridge).

**Theorem (the named consumer — the sampling capstone twin).**
`empiricalWalkDistribution_tail_selfcontained_of_depth`: on connected
+ odd-closed-walk `A`, `∃ t₀ : ℕ, ∀ s ≥ t₀, ∀ x`, `n` i.i.d. simulated
walk trajectories of length `s` estimate `stationaryVec A i` to `ε` at
`2 exp(−nε²/2)` — the plain family's self-contained twin: no caller
rate certificate (the PageRank twin's `α`-display threshold becomes an
existential threshold here, honestly — `(m, δ)` are produced, not
computable from the statement's visible parameters). Plus the
bias-term form at the produced rate
(`empiricalWalkDistribution_stationary_tail_of_pos_power`), whose bias
`ρ^{t₀/m} · TV(δ_x, π)` keeps the start-dependent `TV` explicit.

## QA plan (the falsification surface)

On the triangle `K₃` (`triAdj`, degrees 2, `π = (1/3,1/3,1/3)`,
`walkTransitionMatrix = !![0,½,½; ½,0,½; ½,½,0]`):

1. **The power pins**: `(P²) 0 0 = 1/2`, `(P²) 0 1 = 1/4` — the
   primitive witness at `m = 2` with `δ = 1/4` (and `P` itself has zero
   diagonal — the witness power genuinely has to be `≥ 2`).
2. **The supplier instance**: `walkTransitionMatrix_isPrimitive…`
   instantiated through the triangle walk `0 → 1 → 2 → 0`.
3. **The rate attained exactly at even times**: truth
   `TV(ν_t, π) = (2/3)(1/2)^t` (pinned at `t = 1, 2, 3` from the law
   pins; `TV(δ₀, π) = 2/3` pinned) against the bound
   `(1/4)^{⌊t/2⌋}·(2/3)` — equality at `t = 2`, factor-2 slack at
   `t = 1, 3`. The engine's `t/m` floor arithmetic exercised on both
   parities.
4. **The periodicity fence (hypothesis load-bearing)**: on `K₂` the
   plain walk's odd powers have zero diagonal at every odd time
   (`P^t = P` odd / `I` even, by induction) — `hodd` is unsatisfiable
   there, so the supplier's hypothesis set is exactly what separates
   the triangle from the fence.
5. **The capstone instance**: the self-contained theorem instantiated
   at `ε = 1/4` with the produced threshold's explicit member `s = 4`
   (bias `(1/4)^2·(2/3) = 1/24 ≤ ε/2`), the guarantee pinned at
   `2 exp(−1/16)`-shape for every start; and the truth-side witness
   that `s = 2` cannot serve (`TV(ν₂, π) = 1/6 > 1/8`) — the produced
   threshold's honest slack.

## Verification plan

Spike first (`wip/primsup_spike.lean`): all new declarations + the full
QA + the `#print axioms` audit, iterated to zero errors / zero warnings
before any shelf edit. Then: `lake env lean` on every touched module,
explicit `lake build` targets, the full `lake build` +
`check_build_completeness.py` pair, `lint_axioms.py`,
`check_refutation_independence.py`, `check_public_reachability.py`,
`check_citations.py`, `check_markdown_links.py`,
`check_backlog_freshness.py`, scoreboard regeneration, and
`check_scaffold_map_freshness.py` after the stats sync.

## Leverage case

- Closes the execution plan's named first-magnitude frontier (the
  undirected plain-walk sampling twin) *and* its blocker in one package.
- The supplier is genuinely new mathematics for the repository (the
  two-parity covering argument), and load-bearing: a wrong `IsPrimitive`
  shape, a wrong `t/m` floor, or a wrong parity split fails the exact
  attainment QA above.
- Gives the retired `primitive_power_tendsto` its first undirected
  consumer, and the Doeblin TV engine its first undirected consumer —
  both engines currently sit with zero reach into the plain-walk world.
- Zero axiom contact; the plain walk's certificate-free rate closes the
  asymmetry the lazy family was built to patch, on the complementary
  (non-bipartite) class.


## Delivery record

DELIVERED at the statement shapes recorded above, zero new axioms
(count stays 4; `#print axioms` via `wip/primsup_axcheck.lean` on all
39 audited declarations — 9 new shelf + 20 QA + 10 consumed-layer
spot-checks including `primitive_power_tendsto` itself — every one
exactly `propext, Classical.choice, Quot.sound`). QA 3748 → 3768
(+20, `EmpiricalStationary_QA.lean`'s Primitivity section).

**What landed.** (1) The matrix-level engine in
`PrimitiveConvergence.lean`: `pow_entry_pos_of_pos` (single-term
concatenation), `pow_entry_pos_bounce` (the `+2` bounce chain), and
`isPrimitive_of_pow_pos_of_odd_loop` — the two-parity covering, with
the `1 +` in the witness `m := 1 + ∑ (d + L₀)` keeping the empty
index-type corner split-free and the support-level `htwo`/`hodd`
shape surviving the irregular-degree walk matrix. (2) The walk-level
section in `Mixing.lean`: the `Walk`-induction bridge, the wrapper
(the odd walk transported to every vertex by reversal — the statement
design's key move, since matrix-level symmetry is unavailable), the
Doeblin rate with the simplex diameter folding `TV(δ_x, π) ≤ 1`, and
the convergence corollary through `primitive_vecMul_tendsto`. (3) The
capstone pair in `EmpiricalStationary.lean` (the bias-term form with
the start-dependent TV kept explicit, and the self-contained twin
with its honest existential threshold — the `ρ = 0` vs `0 < ρ < 1`
case split on the threshold production, `pow_mul_le_of_log_threshold`
consumed in the second case only). (4) The QA: the primitive square
pinned on the triangle (`P² = (1/4)(J−I)`, the `m = 1` zero-diagonal
fence), the supplier instantiated through the explicit odd walk
`0→1→2→0`, **the engine attained exactly at the even time `t = 2`**
(truth `TV = 1/6` = engine `(1/4)^{2/2}·(2/3)`), the odd-time
factor-`2` slack pinned, the `K₂` periodicity fence (`(P^t) 0 0 = 0`
at every odd `t` — `hodd` exactly isolating the bipartite class), the
self-contained instance at `ε = 1/4` with the produced threshold's
arithmetic (`⌈log 8/log 4⌉ = 2`) and its honest slack witnessed on
the truth side (`TV(ν₂) = 1/6 > 1/8`), and the convergence instance.

**Verification.** Spike first (`wip/primsup_spike.lean` — all
declarations + full QA + audit, iterated to zero errors/zero warnings
before any shelf edit); `lake env lean` zero errors/zero warnings on
all four touched modules; explicit `lake build` targets ✔; the
39-declaration axiom audit above; full `lake build` ✔ immediately
followed by `check_build_completeness.py` (the QA module flagged
stale once, remediated per the script's documented
`lake build <module>` route, then 133/133 fresh, exit 0);
`lint_axioms` exit 0; `check_refutation_independence` (9-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_backlog_freshness`; scoreboard
regenerated (**3768/4/0**); map-freshness exit 0 after the stats sync
and SVG regeneration.

**Technique findings** (for the next run's spike work):
1. `rw`-into-goal of a `Pi.single`-applied equation elaborates with a
   stuck higher-order metavariable (`(Pi.single (0 : Fin 3) (1 : ℝ)) 0`
   in a standalone `have` carries an unresolved `?β`) — the elaborated
   theorem statement is fine, but pins against it must reduce through
   `simp only [Pi.single_apply, if_pos/if_neg …]` in the goal, never
   through a separately-stated entry `have`.
2. `norm_num` does not evaluate `|·|` of differences either — the
   robust three-entry TV pin computes each difference as an explicit
   `show … = numeral from by norm_num`, rewrites, then
   `abs_of_nonneg`/`abs_neg` explicitly (the Doeblin delivery's
   two-entry note generalizes: one `abs` lemma application per sign
   class, negative ones through `abs_neg` first).
3. `pow_le_pow_right_of_le_one'` needs a `MulLeftMono` instance the
   elaborator does not find for `ℝ` in this context — the exponent
   monotonicity at base ≤ 1 is cheaper to inline: split `k = j + r` by
   `omega`, `pow_add`, and `mul_le_mul_of_nonneg_left (pow_le_one₀ …)`.
4. `Walk.cons` chains against `supportGraph`'s definitionally-`And`
   adjacency fail as anonymous constructors (the expected `Adj` type
   does not unfold under the metavariable-laden elaboration);
   `supportGraph_adj.mpr ⟨…⟩` in a `have` with the explicit
   `(supportGraph … ).Adj i j` type ascription is the reliable shape.
5. Matrix-literal entries at `Fin 3` index `2` do not evaluate under
   `norm_num [triAdj]` (the `vecTail` chain) — `rw [triAdj_apply]`
   plus an explicit `if_neg`/`if_pos` decides the index comparison.
6. `Matrix.mulVec_transpose` + `Matrix.transpose_pow` are the whole
   law↔engine bridge (`walkDistribution A t x = δ_x ᵥ* P^t`) — worth
   knowing before drafting any consumer of the `vecMul`-shaped TV
   engines.

**Remaining risk:** none owed by the delivery — pure hard crust, no
axiom disposition changed, no existing public statement changed.
Honest scope: the odd-closed-walk interface is *weaker* than
"non-bipartite" (the classical dichotomy — no odd closed walk ⟹
bipartite — is true but deliberately not bundled; the pinned Mathlib
has no `SimpleGraph.Bipartite` to state it through, and no consumer
has asked); the rate is the Doeblin bound (typically loose, exact on
the triangle at even times as pinned); the spectral route to the
plain family's certificate (non-bipartite ⟹ `λ_max(L_sym) < 2` ⟹
`r < 1`) remains ungated and undelivered.
