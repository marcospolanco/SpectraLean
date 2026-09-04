# Adversarial Fence Audit of the Primitivity-Supplier Family

**Status:** COMPLETE (delivered 2026-09-03, same-run)

Run `20260903T154410Z-run-1`, session `ses_f980f316fffen4UgB3DPK5FJ0b`.

## Motivation

The mixing-cascade QA audit (the standing handoff's audit-shaped pass) has
now fenced four families — the TV/Dobrushin engines
(`adversarial-fences-tv-dobrushin-engines.md`), the lazy family
(`adversarial-fences-lazy-family.md`), the entropy family
(`adversarial-fences-entropy-family.md`), and the Poisson bridge
(`adversarial-fences-poisson-bridge-family.md`) — and the execution plan's
handoff names exactly one cascade member left unaudited: **the
primitivity-supplier family** (delivered 2026-09-02 by
`proposals/primitivity-supplier-plain-walk.md`), whose QA was written by
its own delivery run and never independently re-read. This proposal is
that re-read: hypothesis necessity per
`governance/ADVERSARIAL_REVIEW.md` Phase 2/3, closing every
load-bearing clause with no negative witness anywhere in the repository
with a hypothesis-form fence plus isolation companion.

Completing this family finishes the audit-shaped pass over the entire
mixing cascade — every 2026-09-01/02 mixing QA family will then have an
independent adversarial re-read on record.

## Audit target

- `Scaffold/Mathlib/LinearAlgebra/PrimitiveConvergence.lean`'s supplier
  section: `pow_entry_pos_of_pos` (hnn, h1, h2), `pow_entry_pos_bounce`
  (hnn, h1, hz1, hz2), `isPrimitive_of_pow_pos_of_odd_loop` (hnn,
  hreach, htwo, hodd);
- `Scaffold/Mathlib/GraphTheory/Mixing.lean`'s walk level:
  `pow_walkTransitionMatrix_pos_of_walk` (hA, hnn, hd),
  `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk` (hA, hnn,
  hd, hconn, hp), `walkDistribution_tvDistance_le_of_pos_power` (hA,
  hnn, hd, hle), `walkDistribution_tendsto_stationaryVec` (same set as
  the supplier);
- `Scaffold/Derived/EmpiricalStationary.lean`'s
  `empiricalWalkDistribution_tail_selfcontained_of_depth` (the
  supplier's graph clauses plus hε/hn) — the consumer capstone.

`deg` is the plain row sum (`∑ j, A i j`, not the abs-sum) — this fact
shapes several fixtures (a symmetric matrix with negative entries can
still have positive degrees, and `P = D⁻¹A` is row-stochastic whenever
`deg ≠ 0` regardless of signs).

## Step 0: the clause census (worked before any Lean)

Fenceable (fixture designed, mechanism worked — Step 1 lands these):

Engine level:

1. `pow_entry_pos_of_pos.hnn` — at `M = !![−2,1;0,1]` with `i=0, k=1,
   j=1, a=b=1`: `h1 : 0 < M 0 1 = 1` and `h2 : 0 < M 1 1 = 1` genuine,
   the off-path negative diagonal poisons `(M²) 0 0 = (−2)(1) + (1)(1)
   ... ` — precisely, `(M²) 0 1 = M 0 0·M 0 1 + M 0 1·M 1 1 = −1 < 0`.
2. `pow_entry_pos_of_pos.h1` / `.h2` — at the swap `!![0,1;1,0]` with
   `a=b=1`: the dropped seed leaves `(M²) 0 1 = 0`.
3. `pow_entry_pos_bounce.hnn` — at `M = !![1,−2;1,1]`, `u=v=0, e=0,
   z=0, n=1`: both bounce entries are `M 0 0 = 1` (genuine), the
   off-path entry `M 0 1 = −2` makes `(M²) 0 0 = 1·1 + (−2)(1) = −1`.
4. `pow_entry_pos_bounce.h1` — at the swap, `u=0, v=1, z=0, e=0,
   n=1`: `(M⁰) 0 1 = 0` fails, `(M²) 0 1 = 0`.
5. `pow_entry_pos_bounce.hz1` — at `M = !![0,0;1,1]`, `v=0, z=1,
   n=1`: `hz1 : 0 < M 0 1 = 0` fails while `hz2 : 0 < M 1 0 = 1` and
   the `e=0` seed are genuine; `(M²) 0 0 = 0`.
6. `pow_entry_pos_bounce.hz2` — at `M = !![0,1;0,1]`, `v=0, z=1`:
   mirror.
7. `isPrimitive_of_pow_pos_of_odd_loop.hreach` — at `M = 1` (2×2):
   self-loops make `htwo`/`hodd` genuine, `(M^k) 0 1 = 0` at every `k`
   kills both the hypothesis and the conclusion.
8. `isPrimitive_of_pow_pos_of_odd_loop.htwo` — at the 3-cycle
   permutation `p3 = !![0,1,0;0,0,1;1,0,0]`: `p3³ = 1` supplies
   `hreach` (witnesses 1, 2, 3) and `hodd` (t = 3), but no vertex has
   a reciprocal positive pair; every power `p3^k = p3^(k mod 3)` is a
   permutation matrix with a zero entry — no 2-cycle anywhere, exactly
   the periodicity `htwo` excludes.
9. `isPrimitive_of_pow_pos_of_odd_loop.hodd` — at the swap matrix
   (= the walk matrix of `K₂`, reusing `k2P_two_eq_one` and
   `k2_odd_diag_zero_QA`): `htwo` and `hreach` genuine, every odd
   power has zero diagonal, every even power is the identity —
   the bipartite class the lazy program patches.
10. `isPrimitive_of_pow_pos_of_odd_loop.hnn` — at `M = !![1,−3;1,1]`:
    self-loops genuine for `htwo`/`hodd`; `hreach` genuine through the
    exact cube structure `M³ = −8·1` (witnesses: a=6 for diagonals —
    `M⁶ = 64·1` — a=4 for `(0,1)` — `M⁴ = −8·M`, entry `24` — and
    a=1 for `(1,0)`); no power is entrywise positive because
    `M^k = (−8)^q • M^r` at `k = 3q + r` and each of `1, M, M²` has a
    nonpositive entry with the sign flip unable to fix all entries at
    once.

Walk level:

11. `pow_walkTransitionMatrix_pos_of_walk.hnn` — at `negOffAdj`
    (symmetric, degrees `(1,1)` positive, off-diagonal `−1`): the
    support graph contains the edge (adjacency needs `A 0 1 ≠ 0`,
    which `−1` satisfies), but `(P^1) 0 1 = (deg 0)⁻¹·(−1) = −1`.
12. `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk.hnn` —
    at the new fixture `negTri = !![2,1,1;1,2,−1;1,−1,2]` (symmetric,
    degrees `(4,2,2)` positive, support graph the full triangle, odd
    walk 0→1→2→0): `P` has the exact row formula
    `(P^k) 2 1 = 1/4 − (3/2)^k / 2 < 0` for every `k ≥ 1` (row 2 of
    every power has a negative entry, by a three-entry induction —
    the certificate-screening that makes the rate theorem's own `hnn`
    non-fenceable does not reach the supplier's conclusion).
13. `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk.hconn`
    — at the new fixture `triIso4 = !![0,1,1,0;1,0,1,0;1,1,0,0;0,0,0,1]`
    (triangle ⊕ an isolated self-weighted vertex: symmetric,
    nonnegative, degrees `(2,2,2,1)` positive, the triangle's odd walk
    genuine): vertex 3 is unreachable from 0 (walks cannot leave the
    triangle block), and `(P^k) 0 3 = 0` at every `k` (block
    induction) — no power is strictly positive.
14. `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk.hp` —
    at `K₂` with `p := 0→1→0` (length 2, even): every other
    hypothesis genuine (connected!), conclusion ¬IsPrimitive by the
    same even/odd power collapse as item 9.
15. `walkDistribution_tvDistance_le_of_pos_power.hle` — at `K₂`,
    `δ = 1, m = t = 1, x = 0`: `δ = 1` exceeds the diagonal
    certificate `(P^1) 0 0 = 0`, the bound's base goes negative,
    `1 − 2·1 = −1` against the truth `TV(ν₁ 0, π) = 1/2`.
16. `walkDistribution_tvDistance_le_of_pos_power.hA` — at
    `asymLoopAdj` with `δ = 1/2, m = t = 1, x = 0`: `P = (1/2)·J` so
    the certificate `hle` is genuine at equality, but `π =
    (3/4, 1/4)` is *not* stationary at the asymmetric chain — the law
    is `(1/2, 1/2)` after one step, `TV = 1/4 > 0 = (1 − 2·(1/2))^1`:
    symmetry is load-bearing through stationarity, not through the
    certificate.
17. `walkDistribution_tendsto_stationaryVec.hnn` — at `negTri`,
    `x = 1`: row 1 of every power `P^k = (1/2, 1/4 + (3/2)^k/2,
    1/4 − (3/2)^k/2)` (the mirror of item 12's induction) diverges in
    coordinate 2 — the walk law is not a law at all under the dropped
    hypothesis and converges to nothing.
18. `walkDistribution_tendsto_stationaryVec.hconn` — at `triIso4`,
    `x = 3`: the law is `δ₃` at every time (the self-weighted vertex
    is absorbing), so the sequence is constantly `δ₃ ≠ π`
    (`π 3 = 1/7`) — convergent, to the wrong vector.
19. `walkDistribution_tendsto_stationaryVec.hp` — at `K₂`: the law
    alternates `δ₀/δ₁` by parity of `t`, at distance `1` — no limit
    exists (the ε-route at `ε = 1/4` through consecutive times of
    opposite parity).

Consumer (the capstone `empiricalWalkDistribution_tail_selfcontained_of_depth`):

20. `.hp` — at `K₂`, `ε = 1/4`, `i = 0`, `n = 32`: at every even
    `s` and start `x = 0` the law is `δ₀`, the sampling measure
    concentrates on the all-zero trajectory, the deviation event has
    measure `1 > 2·exp(−1)`.
21. `.hconn` — at `triIso4`, `x`-quantified via `x = 3`: the law is
    `δ₃` at every time, `|1 − π 3| = 6/7 ≥ 1/4`, measure `1 >
    2·exp(−1)` at `n = 32`.

Non-fenceable, with mechanisms (to be recorded in the delivery):

- `pow_walkTransitionMatrix_pos_of_walk.hA` and the supplier's /
  tendsto's / capstone's `hA` — structural: `supportGraph A hA`
  consumes the symmetry proof in its own statement, so the remaining
  hypotheses cannot be formed at an asymmetric fixture.
- `pow_walkTransitionMatrix_pos_of_walk.hd` — removable-given-`hnn`
  (P4): the junk `(0:ℝ)⁻¹ = 0` keeps `P = D⁻¹A` entrywise nonnegative
  at zero degrees — the plain twin of the lazy/entropy audits'
  recorded finding for `walkTransitionMatrix_nonneg`/`walkDensity_nonneg`;
  and on any walk, every visited vertex has positive degree by
  adjacency, so the conclusion is truth-shaped on the walk.
- supplier `.hd` — non-fenceable: any fixture failing `hd` is screened
  by `hconn` (a connected graph with ≥ 2 vertices forces positive row
  sums at nonnegative entries) or by the odd-walk requirement; the
  1-vertex diagonal-zero corner is screened by `hp` (no odd closed
  walk exists on a loop-free single vertex).
- rate `.hd` — at zero degrees the junk `P` row is zero, mass ≤ 1,
  and the `m = 0`/`δ = 0` junk corner of `hle` collapses the right
  side to `(1−0)^{t/0} = 1` — the simplex diameter — so the
  conclusion survives on truth.
- rate `.hnn` — certificate-screened: the falsification route (base
  `1 − |V|δ < 0` at odd exponent, right side negative) needs
  `δ > 1/|V|` through `hle`, and `P^m`'s row sums are always `1`
  (`P = D⁻¹A` is stochastic at every nonzero degree, signs included),
  so strictly-many-entries-above-`1/|V|` is unsatisfiable;
  at `negOffAdj` the negative eigen-direction additionally makes some
  entry of every `P^m` negative, pushing `hle`'s `δ` below zero and
  the base above 1 — the same class as the Poisson audit's
  transfer-corollary finding (the certificate hypothesis screens the
  broken fixtures).
- rate/tendsto/capstone `[Nonempty V]` — instance-argument,
  structural (recorded non-fenceable in every prior audit).
- tendsto `.hA` — structural via `hconn`'s statement.
- capstone `.hnn`/`.hd` — structural: the conclusion's own sampling
  object `iidPMF (walkDistribution …) (walkDistribution_nonneg A hnn
  hd …) …` consumes the certifications, so the negated conclusion is
  not well-formed without them.
- capstone `.hε` — benign junk: at `ε ≤ 0` the deviation event is all
  of the sampling space (measure 1) but the right side is
  `2·exp(−nε²/2) = 2 ≥ 1` — the bound holds anyway.
- capstone `.hn` — benign junk: at `n = 0` the right side is
  `2·exp(0) = 2 ≥ 1 ≥ ` any measure.
- rate's `m = 0` junk corner — benign: `t/0 = 0` in `ℕ`, right side
  `1 ≥ ` simplex diameter.

## Deliverable

One QA-only change set, zero axiom contact, in a new
`PrimitivityFences` section of
`Scaffold/QA/Derived/EmpiricalStationary_QA.lean` (the family's QA
home; its imports already cover every reused fixture in
`Mixing_QA.lean`): the fences of items 1–21 with isolation
companions, the two new fixtures (`negTri`, `triIso4`) with their
pins, via a `wip/` spike first. No `-- @refutes` tags (these refute
*theorem* instantiations; nothing admitted is consumed).

## Consumer

The audit itself is the consumer of the 2026-09-02 delivery's QA; its
own consumers are every future user of the supplier, the plain-walk
rate, and the self-contained plain-walk capstone — the negative
witnesses are the falsifiability surface for exactly the statements
the sampling program stands on.


## Delivery record (2026-09-03)

DELIVERED as designed with two fixtures reshaped by a Step-0 finding
(below): QA-only, +197 by the generator metric (4094 → 4291; the
landed section carries 212 declarations, 15 of them fixture `def`s),
`EmpiricalStationary_QA.lean`'s new `PrimitivityFences` section.
**Zero axiom contact**: `#print axioms` via
`wip/primsupfences_axcheck.lean` on all 212 new declarations — 209
exactly `propext, Classical.choice, Quot.sound`, the three Fin-case
helpers (`fin2_eq`, `fin3_eq`, `fin4_eq`) the strictly smaller
`propext, Quot.sound`; no `-- @refutes` tags (these refute *theorem*
instantiations; nothing admitted is consumed).

**The Step-0 finding that reshaped two fixtures:** the support graph's
adjacency is `i ≠ j ∧ 0 < A i j` — **positive** weights, not nonzero.
A negative edge is not a graph edge, so the original `negTri`
(negative off-diagonal) and `negOffAdj` walk designs were invalid: the
odd closed walk could not exist, the walk could not exist. The
delivered fixtures hide the negative weight where the graph cannot
see it — `negWalkAdj = !![−3/2,1,1;1,0,1;1,1,0]` puts it on the
diagonal (row sums stay positive, so `deg`/`hd` stays genuine) and
the bridge's conclusion still fails on the genuine walk `0 → 1 → 2`
(`(P²) 0 2 = (−3)(2) + (2)(1/2) + (2)(0) = −5`);
`negDiagTri = !![−4,3,3;3,0,1;3,1,0]` does the same at supplier level,
where the walk matrix's symmetric-subspace eigenvalue `−11/4` gives
the exact closed forms `P^k (0,1,1) = ((11/5)γ^{k−1} + 4/5,
−(11/20)γ^{k−1} + 4/5, …)` and `(P^k) 1 0 = 1/5 + (11/20)γ^{k−1}`
(`γ = −11/4`; `negDiagTri_pow_mulVec_w`, `negDiagTri_row1_col0`) —
no power entrywise positive, the law from `1` divergent (consecutive
even-spaced entries differ by ≥ `231/64`).

The remaining fences as censused: the engine trio's clauses at
`concatNeg`/`bounceNeg`/`bounceNoUp`/`bounceNoDown`/`swap2`; the
supplier's four at `ident2` (unreachable pair), `cycle3` (the directed
3-cycle permutation, `cycle3 ^ 3 = 1`, no reciprocal pair anywhere),
`swap2` (the bipartite class), and `rot2 = !![1,−3;1,1]`
(`rot2_pow_three_mul`: every power a signed multiple of `1`, `M`,
`M²`, each with a nonpositive entry no sign flip repairs); the
supplier/corollary `hp` at `K₂` (`k2WalkEven`, `k2P_not_isPrimitive`,
the alternating-law `k2_tendsto_hp_fence_QA`); their `hconn` at
`triIso4` (`triIso4_pow_off`: the cross-block entry zero at every
power; `triIso4_walk_stays`: walks cannot leave the triangle block;
`triIso4_pow_row3` + `triIso4_pi_three`: the absorbed law `δ₃` with
`π 3 = 1/7 ≠ 1` — convergent to the wrong vector, a distinct failure
mode from alternation); the rate's `hle` (base `1 − 2·1 = −1 < 0`
against `TV = 1/2` on `K₂`) and `hA` (`asymLoopAdj` with
`P = (1/2)·J`: `hle` genuine at equality, `π = (3/4,1/4)` not
stationary at the asymmetric chain, `TV = 1/4 > 0` — symmetry is
load-bearing through stationarity, not the certificate).

Non-fenceables recorded with mechanisms (as censused): the structural
`hA`s (`supportGraph` consumes the symmetry proof in the statements of
`hconn`/walks; the capstone's `hnn`/`hd` are consumed by the
conclusion's own `iidPMF` certifications); the rate's `hnn` (certificate-screened:
falsification needs base `1 − |V|δ < 0`, i.e. `δ > 1/|V|` through
`hle`, impossible with row sums `1` — `P = D⁻¹A` is stochastic at
every nonzero degree, signs included); the rate's `hd` and the
`m = 0`/`δ = 0` corner (junk rows are zero rows: mass ≤ 1, the right
side collapses to `1 = ` the simplex diameter); the capstone's
`hε`/`hn` (benign junk: the event is everything but the right side is
`2 ≥ 1 ≥ ` any measure); `pow_walk`'s `hd` (removable given `hnn` —
the plain twin of the lazy/entropy audits' recorded finding; on any
walk every visited vertex has positive degree by adjacency);
`pow_walk`'s/tendsto's `hA` (structural); the supplier's `hd`
(removable given `hnn` + `hconn` on ≥ 2 vertices — the odd walk
itself forces edges; the 1-vertex diagonal-zero corner is screened by
`hp`); `[Nonempty V]` (instance-argument, structural).

**Consumer-fence follow-ons priced (not delivered):** the capstone's
two graph clauses (`.hp` at `K₂` even-time laws — the δ₀-concentrated
sampling measure makes the deviation event's measure `1 >
2exp(−nε²/2)` at `n` with `2exp(−n/32) < 1`, e.g. `n = 32` via
`Real.add_one_lt_exp`; `.hconn` at `triIso4` from `x = 3` with
`|1 − 1/7| = 6/7 ≥ 1/4`) — both mechanisms fully worked, both needing
the `iidPMF` measure-of-singleton machinery (`toMeasure_cyl` +
finite-union null or direct enumeration), deferred as a bounded
follow-on rather than bundled into an already-large delivery.

**Follow-on delivery record (2026-09-03, run `20260903T182707Z-run-1`,
session `ses_f977fcdc0ffe3Up9DMcZ31uwqc`):** the two priced consumer
fences DELIVERED as designed with one parameter adjustment — QA-only,
+6 by the generator metric (4291 → 4297), the capstone subsection of
the same `PrimitivityFences` section. Zero axiom contact: `#print
axioms` via `wip/capstonefences_axcheck.lean` on all six new
declarations exactly `propext, Classical.choice, Quot.sound`; no
`-- @refutes` tags (theorem instantiations, nothing admitted
consumed). The mechanism as priced, via `toMeasure_cyl_inter` at the
all-coordinates cylinder (cleaner than the priced singleton-route
sketch: one application collapses to a single factor and `1 ^ n`) —
generalized as `toMeasure_cyl_singleton_one` (any point-mass factor
`q v = 1`, any `Fin n`): `hp` as `k2_capstone_hp_fence_QA` at `K₂`
(every other hypothesis genuine *including connectivity* —
`k2_capstone_hp_isolation_QA`; at the even time `s = 2(t₀+1)` past any
threshold the law from `0` is `δ₀` by `k2_law_even_entry`, the
all-zero trajectory carries the full mass, deviation `|1 − 1/2| =
1/2` at mass `1`) and `hconn` as `triIso4_capstone_hconn_fence_QA`
(the genuine odd walk `triIso4Walk3` and every walk-level clause
genuine — `triIso4_capstone_hconn_isolation_QA`; the law from the
absorbing vertex `x = 3` is `δ₃` at *every* time by
`triIso4_pow_row3`, deviation `|1 − 1/7| = 6/7` at mass `1`, at every
threshold time — a failure mode distinct from the `hp` fence's
parity-gated one). The adjustment: the priced `(ε, n) = (1/4, 32)`
needs the numeric side `2 exp(−1) < 1`, i.e. a strict `2 < exp 1`,
which the corpus's non-strict engine (`Real.add_one_le_exp`) cannot
deliver; the delivered `(ε, n) = (1/2, 32)` reads `2 exp(−4) ≤ 2/5 <
1` by exactly the `tri_naive_stationary_refuted_QA` route
(`exp 4 ≥ 5` + `inv_anti₀`) at the same honest deviations (both ≥ the
threshold at equality-plus). One technique finding: `rw` cannot
rewrite with a `≤`-hypothesis — the `−16/9` original's
`rw [hval, inv_div] at hinv` idiom rewrites the *hypothesis* with an
equation; converting `5⁻¹ ≤ 1/5` needs `LE.le.trans_eq (one_div
_).symm`, not a rewrite.

Technique findings (nine):

1. **The positive-weight support graph** (the delivery's headline
   Step-0 finding): `supportGraph A hA`'s adjacency is `i ≠ j ∧
   0 < A i j` — negative weights are not edges. Any fence fixture for
   walk-level theorems must hide negative weights off the positive
   structure (a diagonal works; row sums must stay positive for `deg`).
2. **`rw [show k = (k-1)+1 …]` captures every `k`** — including the
   `k` inside `k − 1` terms elsewhere in the goal, silently corrupting
   exponents; state exponent identities at the `+1`-form and bridge
   with `congr 1; omega`.
3. **The negative-numeral parse trap**: `-11/4` parses as `(-11)/4`,
   so `(-a)`-patterned lemma LHSes (`neg_pow_two_mul_succ`) do not
   fire on it; bridge with a `norm_num`-proved conversion
   `(-(11/4:ℝ)) = (-11/4:ℝ)`. The recorded Fin-literal shape-mismatch
   class, generalized to real-numeral parse shapes.
4. **`pow_succ _ _` will not unify `γ^k = γ^(k-1)·γ` as a term**
   (the unifier refuses `k =?= ?n + 1` for a variable `k`); prove it
   by rewriting inside a goal or state at `(k-1)+1`.
5. **`decide` cannot evaluate `0 < if …` over ℝ** (`Real.decidableLT`
   is classical); evaluate the `ite` by defeq `show` or an if-table
   lemma + `simp` (the house idiom), never `decide` the whole
   proposition.
6. **`open scoped Classical` poisons kernel `decide`** through
   `Classical.propDecidable` instance selection — dropped from the
   spike; the landed section does not open it.
7. **`Finset.sum_eq_single_of_mem`'s argument order** is
   `(a) (h : a ∈ s) (h₀)` — the membership proof *before* the
   vanishing clause (an argument-order trap in the recorded
   `pow_le_pow_left₀` class).
8. `Fin.sum_univ_four` (the `Fin` namespace), not
   `Finset.sum_univ_four`.
9. **The ¬Tendsto idiom for divergent/alternating laws**:
   `Metric.tendsto_atTop` at a small `ε`, `dist_triangle` on
   times `N` and `N + 2`, and a per-entry lower bound
   (`dist_ge_entry` from `norm_le_pi_norm`) — two uses here
   (a diverging coordinate, an alternating pair), both avoiding any
   subsequential-limit machinery.

## Verification

Spike first (`wip/primsupfences_spike.lean` — the full delivery,
iterated to zero errors/zero warnings before any shelf edit);
`lake env lean` on the landed QA module — zero errors, zero warnings;
explicit `lake build Scaffold.QA.Derived.EmpiricalStationary_QA` ✔
(the three positioned info-level `ring_nf` hints and the ProjectorDrift
unused-variable warning confirmed pre-existing on the HEAD baseline by
prior runs); the 212-declaration axiom audit above; **full `lake
build` ✔ immediately followed by `check_build_completeness.py` — 133
source files, 133 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 current axioms, unchanged; only the
allowlisted-confirmed PF finding); `check_refutation_independence`
(9-tag clean — no tags touched); `check_public_reachability` clean
(63 repo modules); `check_citations` ("All axioms have proper
citations!"); `check_markdown_links` clean; `check_backlog_freshness`
clean; scoreboard regenerated (**4291/4/0**) with the verification
row; map-freshness exit 0 after the 4094 → 4291 stats sync in both
map files and SVG regeneration (no station — no tier change).

## Remaining risk

None owed by the delivery — QA-only, no axiom disposition changed, no
public statement changed. Honest scope: the capstone's two graph
clauses are priced follow-ons with worked mechanisms (above); the
audit's completion means every 2026-09-01/02 mixing-cascade QA family
now has an independent adversarial re-read on record.
