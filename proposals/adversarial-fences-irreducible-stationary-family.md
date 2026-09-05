# Adversarial Fence Audit of the Irreducible-Stationary Family

**Status:** COMPLETE — delivered 2026-09-05, run `20260905T063329Z-run-1`,
session `ses_f8fccbc1bffe5ZBfco2P6X0n6C`, at the full priced scope
(the Step-0 pricing below is the delivered scope; the delivery record
closes the document).

## Motivation

The prior terminal handoff (the stationary family's audit,
2026-09-05) named `IrreducibleStationary` (3 transitive non-QA
consumers) and `Directed` (3) as the audit method's next targets. This
run's own fresh reverse-import walk confirms both numbers. The pick
between them is not the consumer metric (tied) but the unfenced clause
surface:

- `IrreducibleStationary.lean` (661 lines, hard crust since the
  2026-09-02 Cesàro re-proof) carries **twelve public theorems with
  ~28 load-bearing clause instances**: the support-lemma row-sum
  clauses, the power-entry lemmas' nonnegativity/row-sum clauses, the
  power-positivity engine's two clauses, the Krylov–Bogoliubov cluster
  lemma's four, the row-stochastic existence theorem's two, and the
  walk-level stationary family's `hnn`/`hirr`/`hex`/`hdeg`/σ/τ clause
  sets.
- Its QA (706 lines, `IrreducibleStationary_QA.lean`) carries exactly
  two negative witnesses — `A4_existsUnique_refuted_QA` and
  `A4_smul_unique_refuted_QA` — both **hypothesis-free** (they drop the
  entire hypothesis stack at the reducible two-block fixture), so no
  per-clause necessity information exists anywhere in the repository:
  they prove only that *some* hypothesis somewhere in the stack is
  load-bearing, not which.
- `Directed.lean`, by contrast, has four fenceable clauses (`hA` ×3,
  `hd` ×1) over five hypothesis-free statements — a proportionately
  small audit; it remains the next target after this one.

The shelf is the hard-crust root of the directed mixing axis:
`PageRank`, `DirectedMixing`, and the `EmpiricalStationary` derived
capstone all import it transitively, and the QA-level
`DirectedMixing_QA`/`Oversmoothing_QA` chains sit downstream. A
statement-shape defect here propagates to every directed consumer.

## Step 0: priced clause surface

Pricing conventions as in the prior audits (each row: the clause, the
priced fixture, the kill mechanism, the disposition).

### A. Support lemmas

| # | Theorem | Clause | Disposition |
| --- | --- | --- | --- |
| A1 | `isIrreducible_transpose` | `h : M.IsIrreducible` | **Fence** at the identity: the transpose of the identity is the identity, whose only arcs are self-loops — `¬RTG 0 1` through a generic self-only-arcs lemma (refl handles the diagonal). |
| A2 | `walkTransitionMatrix_isIrreducible` | `hirr` | **Fence** at the identity (degrees `1`, so the walk is the identity): arc structure preserved, reducible. |
| A3 | `walkTransitionMatrix_isIrreducible` | `hdeg` | **Fence** at `!![-1, 1; 1, 1]]` (degrees `(0, 2)`; the positive arc `0→1` coexists with the canceling `-1` diagonal): the junk `0⁻¹ = 0` zeroes the walk's row `0`, killing all arcs out of vertex `0`. The `d = 0`-corner mechanism transferring the random-walk audit's finding to the irreducibility interface. |
| A4 | `vecMul_mul`, `vecMul_entry`, `vecMul_sum` | — | **Non-fenceable**: no mathematical hypotheses. |
| A5 | `sum_vecMul_eq_of_row_sum` | `hrow` | **Fence** at the zero matrix: mass is annihilated, `0 ≠ ∑ v`. |
| A6 | `pow_row_sum` | `hrow` | **Fence** at the zero matrix, `t = 1`. |
| A7 | `pow_entry_nonneg` | `hnn` | **Fence** at `-1 • 1` (Fin 1), `t = 1`. |
| A8 | `pow_entry_le_one` | `hnn` | **Fence** at `!![2, -1; 0, 1]]` (row sums `1` genuine, the negative entry off the arc): `t = 1` entry `2 > 1`. |
| A9 | `pow_entry_le_one` | `hrow` | **Fence** at `!![0, 2; 0, 0]]` (nonnegative genuine): `t = 1` entry `2 > 1`. |

### B. The power-positivity engine

| # | Theorem | Clause | Disposition |
| --- | --- | --- | --- |
| B1 | `exists_pow_pos_of_isIrreducible` | `hirr` | **Fence** at the nilpotent `!![0, 1; 0, 0]]` (nonnegative genuine, vertex `1` stranded): `(M^m) 1 0 = 0` for every `m` (the row is zero and `M² = 0`). |
| B2 | `exists_pow_pos_of_isIrreducible` | `hnn` | **Fence** at the rank-one fixture `ppNegM = !![-1, 1, 10; 1, -1, -10; -10, 10, 100]]` (`u ⊗ v` with `u = (1,-1,1)`, `v = (-1,1,10)`, `v ⬝ᵥ u = 98`): irreducible through the five positive arcs `0→1, 0→2, 1→0, 2→1, 2→2`, but `M² = 98 • M`, so every power `M^(k+1) = 98^k • M` and the pair `(1, 2)` entry is `98^k · (-10) < 0` for all `k` (and `δ = 0` at `k = -1`/`m = 0`): **the power entries have m-constant sign — cancellation cannot flip them**. On `Fin 2` this fence is impossible (strong connectivity forces both off-diagonal arcs positive, so `m = 1` already wins), which is why the fixture is `Fin 3`. |

### C. The Krylov–Bogoliubov cluster lemma

| # | Theorem | Clause | Disposition |
| --- | --- | --- | --- |
| C1 | `exists_cluster_stationary_of_orbit` | `hm : 0 ≤ m` | **Screened, unsatisfiable**: with `hgnn` and `hgsum` kept, a negative `m` forces `∑` of nonnegatives `< 0`. Truth-removable, not fenceable. |
| C2 | `exists_cluster_stationary_of_orbit` | `hgnn` | **Fence** at the Jordan-block fixture `!![0, 1; -1, 2]]` (a single eigenvalue `1` with a nontrivial Jordan block) with the orbit `g s = ![2 - s, s - 1]`: mass `1` constant (`hm`, `hgsum` genuine), dynamics genuine (`g s ᵥ* M = g (s+1)` by direct entry arithmetic), but `g 0 = ![2, -1]` — **the orbit escapes the simplex exactly where the entrywise bound `|g 0 j| ≤ m` needs nonnegativity**, and the conclusion dies because the fixed space is `ℝ • ![1, -1]` (mass `0`, no nonneg member of mass `1`). The audit's headline mechanism: the telescoping defect `t⁻¹ • (g 0 - g t)` is bounded only because nonnegativity confined the orbit. |
| C3 | `exists_cluster_stationary_of_orbit` | `hgsum` | **Fence** at `M = 2 • 1` (Fin 1) with the growing orbit `g s = ![2^(s+1)]`: `hm`, `hgnn`, `hgstep` genuine, masses `2^(s+1) ≠ 1`, no stationary vector of mass `1` (the only fixed point is `0`). |
| C4 | `exists_cluster_stationary_of_orbit` | `hgstep` | **Fence** at the same `M = 2 • 1` with the constant `g s = ![1]`: masses constant `1`, nonneg genuine, but `g s ᵥ* M = 2 ≠ 1`, conclusion dead identically. |

### D. Row-stochastic existence

| # | Theorem | Clause | Disposition |
| --- | --- | --- | --- |
| D1 | `exists_nonneg_stationary_of_row_stochastic` | `hnn` | **Fence** at the Jordan fixture `!![0, 1; -1, 2]]` (row sums `1` genuine): the fixed space `ℝ • ![1, -1]` has no nonneg member of mass `2`. |
| D2 | `exists_nonneg_stationary_of_row_stochastic` | `hrow` | **Fence** at `M = 2 • 1` (Fin 1, nonneg genuine): only fixed point `0`, mass `0 ≠ 1`. |
| D3 | `[Nonempty V]` instance | — | **Screened**: at `Fin 0` the conclusion is provable directly (the conditions are vacuous and the empty function is stationary), so the instance is truth-removable — recorded, not fenced. |

### E. The walk-level stationary family

For all five walk-level theorems the clause set is
`hnn`/`hirr`/`hex`/`hdeg` (+ the σ/τ clauses where present).

| # | Theorem | Clause | Disposition |
| --- | --- | --- | --- |
| E1 | `exists_walkPerronVector` | `hnn` | **Fence** at `wpNegAdj = !![-1/2, 1, 1/2; -3/2, 2, 1/2; 1/4, 1/4, 1/2]]` (degrees `(1,1,1)`, irreducible through positive arcs, `hex` genuine): the walk is the matrix itself and its left-fixed space is exactly `ℝ • ![1, -1, 0]` — no strictly positive fixed vector exists. |
| E2 | `exists_walkPerronVector` | `hirr` | **Fence** at the delivered `A4` two-block fixture: two nonneg nonzero fixed vectors (`pi4a`, `pi4b`) that are not positive multiples kill the uniqueness clause. |
| E3 | `exists_walkPerronVector`, `exists_stationaryVec_of_irreducible` | `hdeg` | **P4 truth-removable + strengthening companion**: `hnn + hirr + hex ⟹ ∀ i, 0 < deg A i` (a first arc out of `i` exists unless `i` is alone, where `hex` supplies the loop). Delivered as a proved derivation lemma plus a restated theorem. |
| E4 | same | `hex` | **P4 truth-removable + strengthening companion**: `hnn + (∃ i, 0 < deg A i) ⟹ hex` (a positive row sum has a positive summand — `hirr` not even needed). Same delivery shape. |
| E5 | `exists_stationaryVec_of_irreducible` | `hnn` | **Fence** at `wpNegAdj`: strictly positive stationary would be a fixed vector — none exists. |
| E6 | `exists_stationaryVec_of_irreducible` | `hirr` | **Fence** at `!![0, 1; 0, 2]]` (nonneg, degrees `(1,2)`, `hex` genuine; vertex `0` transient): the walk `!![0,1;0,1]]` forces every stationary `π` to have `π 0 = 0`. |
| E7 | `stationaryVec_smul_of_irreducible` | `hσ`, `hτ` | **Fences** at the delivered `A2` edge: signed stationary vectors (`![-1,-1]`) break the positive-multiple conclusion both ways. |
| E8 | `stationaryVec_smul_of_irreducible` | `hσ0`, `hτ0` | **Fences** at `A2`: the zero vector on either side collapses `τ = c • σ` against `c > 0`. |
| E9 | `stationaryVec_smul_of_irreducible` | `hσs`, `hτs` | **Fences** at `A2`: non-stationary σ (or τ) at `![1,0]`/`![1,1]` breaks the multiple. |
| E10 | `stationaryVec_smul_of_irreducible` | `hnn` | **Fence** at `smNegAdj = !![2, 1, -2; -1, 0, 2; 1, 1, -1]]` (degrees `(1,1,1)`, irreducible, `hex` genuine; `= 1 + u ⊗ v` with `u = (1,-1,1)`, `v = (1,1,-1)`): the fixed space is the 2-plane `σ ⬝ᵥ u = 0`, which meets the nonneg cone in the wedge `σ 0 + σ 2 = σ 1` — the two stationary witnesses `![1,1,0]` and `![0,1,1]` are nonneg, nonzero, and not positive multiples. **On the 1-dimensional signed fixtures (wpNeg/spNeg below) this clause is not fenceable** — the nonneg cone meets the fixed line in one ray, where the conclusion holds. |
| E11 | `stationaryVec_smul_of_irreducible` | `hirr` | Already fenced in hypothesis-free form by `A4_smul_unique_refuted_QA`; **reconciled** into the hypothesis-form discipline at the same fixture. |
| E12 | `existsUnique_stationaryVec_of_irreducible` | `hirr` | Same reconciliation at `A4` (the delivered `∃!` refutation restated in hypothesis form). |
| E13 | `existsUnique_stationaryVec_of_irreducible` | `hnn` | **Fence** at `smNegAdj`: the wedge's mass-1 slice is a whole segment (`σ 0 + σ 2 = 1/2`), so the stationary distribution is far from unique. |
| E14 | `stationaryVec_pos_of_irreducible` | `hirr` | **Fence** at `!![0, 1; 0, 2]]` with `σ = ![0, 1]`: stationary, nonneg, nonzero — and vanishing at the transient vertex. |
| E15 | `stationaryVec_pos_of_irreducible` | `hnn` | **Fence** at `spNegAdj = !![-1, 1, 1; 2, 0, -1; 1/2, 1/4, 1/4]]` (degrees `(1,1,1)`, irreducible, `hex` genuine) with `σ = ![1, 1, 0]`: stationary through the cancellation `1·1 + 1·(-1) = 0` in coordinate `2` — **nonneg stationary mass can vanish on strong support precisely because signed entries cancel**, the mechanism the nonnegative proof rules out. |
| E16 | `stationaryVec_pos_of_irreducible` | `hσ`, `hσ0`, `hσs` | **Fences** at `A2`: the signed stationary `![-1,-1]`, the zero vector, and the non-stationary `![1,0]` each break strict positivity. |
| E17 | `stationaryVec_pos_of_irreducible` | `hdeg`, `hex` | P4 by E3/E4 (the same derivations; noted, not re-delivered). |

Fixture count: five Fin 3 signed/weighted fixtures (`ppNegM`,
`wpNegAdj`, `smNegAdj`, `spNegAdj` new; plus the delivered `A3`/`A4`
and four Fin 1/Fin 2 one-liners).

## Non-goals

- No shelf (`.lean` under `Scaffold/Mathlib/`) changes: the audit is
  QA-only. The strengthening companions live in the QA file as proved
  lemmas; promoting them onto the shelf is a separate decision.
- No `-- @refutes` tags: every fenced statement is a theorem
  instantiation of an all-proved shelf — nothing admitted is consumed
  (verified by `#print axioms` in the delivery record).
- `Directed.lean`'s own four-clause surface is the next audit, not part
  of this one.

## Acceptance bar

1. Every fence compiles with zero `sorry`/`admit`, states the theorem's
   conclusion with exactly one clause dropped, and keeps every kept
   clause genuine at the fixture (isolation companions where the
   genuineness is nontrivial).
2. `#print axioms` on every new declaration: exactly `propext,
   Classical.choice, Quot.sound`.
3. Full ladder: module build, full `lake build` +
   `check_build_completeness.py`, `lint_axioms`,
   `check_refutation_independence` (no tag changes),
   `check_public_reachability`, `check_citations`,
   `check_markdown_links`, `check_backlog_freshness`, scoreboard
   regeneration, map-freshness after the stats sync.

## Delivery record (2026-09-05)

DELIVERED at the full priced scope — see the terminal activity entry.
Summary of what landed:

- **Thirty-two hypothesis-form fences** (A1–A3, A5–A9, B1–B2, C2–C4,
  D1–D2, E1–E2, E5–E10, E13–E16 — the last two rows covering the full
  σ/τ clause set: `hσ`, `hσ0`, `hσs`, `hτ`, `hτ0`, `hτs` across
  `stationaryVec_smul_of_irreducible` and `stationaryVec_pos_of_irreducible`),
  each with pinned entry/degree companions and isolation evidence where
  nontrivial, plus the two reconciliations (E11–E12) restating the
  delivered hypothesis-free refutations at `A4` in hypothesis form.
- **Two proved strengthening companions** (E3–E4): the derivation
  lemmas `deg_pos_of_nonneg_irreducible` (`hnn + hirr + hex ⟹ hdeg`,
  first-arc route with the subsingleton loop case) and
  `exists_pos_entry_of_deg_pos` (`hnn + one positive degree ⟹ hex`,
  positive-summand route), with the restated existence theorem
  `exists_walkPerronVector_of_hex` consuming them.
- **Three screened/unsatisfiable records** (C1, D3, E17) with
  mechanisms.
- **256 declarations** (234 theorems/lemmas + 22 fixture/pin `def`s);
  QA 5494 → 5728 (+234 by the generator metric).
- Headline technique findings are in the terminal activity entry; the
  generic pieces landed for reuse: the self-only-arcs `ReflTransGen`
  lemma (`rtg_eq_of_self`) and the first-arc extractor
  (`exists_arc_of_rtg` via `cases_head` — the constructor-case
  discovery behind the `hdeg` strengthening), the rank-one
  `M² = c • M` power-sign pin, and the mass-constant escaping-orbit
  construction for cluster-lemma clauses.
- **Technique findings** (the spike's six fix rounds, all in recorded
  trap classes): `ReflTransGen`'s inductive principle exposes only
  `refl`/`tail` in this pin — `head` is a theorem, so first-arc
  extraction goes through `cases_head`, not induction; the
  `vecMul_smul`/`smul_vecMul` pair covers only scalar-on-vector —
  scalar-on-matrix needs a local `Finset.mul_sum` transfer
  (`vecMul_smul_matrix`); `(by norm_num)` in an application position
  against a not-yet-unified `m` postpones and shifts the whole
  application — ascribe (`by norm_num : (0 : ℝ) ≤ 1`) or pass `g`
  explicitly first; and the per-entry-pin route
  (`simp only [pins]` at literal indices + `funext`/`fin_cases` +
  `exact`, defeq-closed) remains the only robust way through `Fin 3`
  `ext`-goals — the eta-wrapped literals defeat `rw` of the same pins
  (third confirmation of the recorded trap).
- **Screened/unsatisfiable records**: C1 (`hm` — nonneg vectors of mass
  `m < 0` cannot exist), D3 (`[Nonempty V]` — the `Fin 0` conclusion
  is provable directly), E17 (the E3/E4 derivations transfer).
