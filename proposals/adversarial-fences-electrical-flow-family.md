# The Electrical-Flow Family's Adversarial Fence Audit

**Status:** COMPLETE — delivered 2026-09-04 (run `20260904T112107Z-run-1`,
session `ses_f93e20d9cffeCGvcs2oM7CGC5f`); see the delivery record at
the end.

## Scope

The eighth application of the adversarial fence audit method
(`governance/ADVERSARIAL_REVIEW.md`; seven precedents over the mixing
cascade, the irregular Cheeger family, the regular Cheeger family, and
the effective-resistance core family), and the second over the
electrical cluster — applied to **the electrical-flow family**:
`Scaffold/Mathlib/GraphTheory/ElectricalFlow.lean`'s routing layer (the
flow predicates and Kirchhoff bridge, the flow-energy layer, Thomson's
principle with its superposition lemma, Rayleigh monotonicity, and the
capacity-reinforcement packaging) plus its QA
(`Scaffold/QA/SpectralGraph/ElectricalFlow_QA.lean`, 1072 lines — the
electrical cluster's largest). This is the prior terminal handoff's
top-named next target ("`ElectricalFlow_QA` … the cluster's largest —
both consuming this delivery's substrate").

Selection rationale: the Active priority table is all-Low (nothing to
pursue per priority item 0); every named frontier stays decision- or
consumer-gated. Under center-out judgment the highest-leverage safe
increment is the established audit method applied to the electrical
cluster in its own consumption order. This family's QA (delivered
2026-08-19/20 with the module) already carries an unusually strong
delivery-scoped negative-witness set (the symmetry guard, the support
guards at both levels, the double-counting guard, the
negative-conductance statement-shape witness, the zero-energy
competitor, the orientation guard) — but it predates the
adversarial-review discipline as a *systematic hypothesis-necessity
pass*: no run has yet asked, clause by clause, whether every
load-bearing hypothesis of every public theorem has a negative witness
anywhere in the repository.

QA-only: no axiom contact (count stays 4), no shelf change, pure
insertion into `ElectricalFlow_QA.lean` as a new `AdversarialFences`
section; spiked first in `wip/efflowfences_spike.lean`.

## Step-0 survey: clause pricing

Every public theorem of `ElectricalFlow.lean`, every hypothesis, priced
as **fence** (a concrete instantiation where the dropped-hypothesis
statement is false, all other hypotheses genuine), **screened** (a
delivered witness already refutes this clause — cited, not duplicated),
**non-fenceable** (with mechanism), or **structural** (the hypothesis is
the object of the statement, or consumed by another hypothesis's own
type). Fixtures are reused from the delivered substrate wherever
possible (`edgeAdj`, `connPathAdj`, `negWAdj`, `zeroWAdj`, `asymWAdj`,
`phantomFlow`, `cheatWAdj`, `cheatFlow`, `edge2Adj`, `triAdj`,
`connDiscAdj`, and the 2026-09-04 delivery's `sgnK4Adj` with its junk
pin `sgnK4_fallback_zero_QA`).

### Step 1 — flows and the Kirchhoff bridge

| Theorem | Clause | Verdict |
| --- | --- | --- |
| `electricalCurrent_antisymm` | `hA` | **Screened** — `asymWAdj_current_not_antisymm_QA` (2026-08-20). |
| `electricalCurrent_eq_zero_of_weight_eq_zero` | `h` | Structural — `h` *is* the statement's condition; no dropped form exists. |
| `flowDivergence_electricalCurrent` | — | Structural — no hypotheses. |
| `isFlowOn_electricalCurrent` | `hA` | **Fence** (1-line derivation of the screened witness: `IsFlowOn`'s first conjunct is antisymmetry, so `¬ IsFlowOn asymWAdj (electricalCurrent asymWAdj ![1,0])` follows immediately). |
| `isUnitFlow_electricalCurrent` | `hA`, `hf` | Structural — `hf` is the object; `hA` sits under `hf`'s own world (the demand is solvable exactly where the bridge applies). |

### Step 2 — flow energy

| Theorem | Clause | Verdict |
| --- | --- | --- |
| `flowEnergy_electricalCurrent` | `hA` | **Fence** — new fixture `asymPath4Adj` (below): the ordered-pair sum `(1/2)∑ A i j (f i − f j)²` equals `fᵀ(D−A)f` only when row sums equal column sums; on the asymmetric 4-path with the genuine demand potential `f = ![3/2, 1, 1/2, 0]` (solving `L *ᵥ f = e 0 − e 3` exactly), `flowEnergy = 1 ≠ 3/2 = quadForm (laplacian A) f`. The correction term `(1/2)∑ⱼ f j² (rowsum_j − colsum_j)` is exactly `1/2` here. |
| `flowEnergy_nonneg` | `hnonneg` | **Screened** — `negWAdj_flowEnergy_not_nonneg_QA`. |
| `flowEnergy_electricalCurrent_eq_effectiveResistance` | `hA` | **Fence** — same fixture `asymPath4Adj`: `effectiveResistance` is the (unique-at-fixture) voltage difference `3/2` while the energy is `1`. Uniqueness is *fixture-local* (no `hA`-free uniqueness lemma exists): every solution `g` of the demand satisfies `g 0 − g 3 = 3/2` by linarith over the four row equations, so the `Classical.choose` witness is pinned without reachability. |
| 〃 | `hnonneg` | **Non-fenceable** — on symmetric connected *signed* networks the identity stays true: `flowEnergy = quadForm` needs only symmetry, `quadForm L f = f u − f v` is the hA-free solution-level identity, and every witness's voltage difference equals it. Mechanism: kernel invariance (`L 1 = 0` unconditionally). Recorded as a P4 (truth-removable given `hA` + `hf`). |
| 〃 | `hconn` | **Non-fenceable** — `hf` solvable + `hA` forces `u, v` into one component (pair the demand with the component indicator in `ker Lᵀ = ker L`), and component-reachability is exactly what the agreement/uniqueness theorems consume. Dropped-`hconn` statements stay true wherever `hf` is genuine. P4. |

### Step 3 — Thomson's principle

| Theorem | Clause | Verdict |
| --- | --- | --- |
| `flowDivergence_sub` | — | Structural — no hypotheses. |
| `isFlowOn_sub` | `hθ`, `hψ` | Structural — definitional conjuncts of the flow space; no dropped form is a mathematical claim. |
| `flowEnergy_add_of_flowDivergence_eq_zero` | `hd` | **Fence** — `cheatWAdj` + the new cyclic phantom `cycleFlow` (the 3-cycle `0→1→2→0`, antisymmetric, divergence-free at every vertex, riding the two zero-conductance pairs `(0,2)`, `(1,2)`): `flowEnergy (current ![1,0,0] + d) = 4 ≠ 2 = 1 + 1` = current energy + phantom energy. The support conjunct of `IsFlowOn` is what kills the free phantom at the superposition level — the integration-by-parts cross term dies only because `d` vanishes on zero branches. |
| 〃 | `hdiv` | **Fence** — `edgeAdj` with `d = 2·(electricalCurrent edgeAdj ![1,0])` (a genuine flow, divergence `[2, −2] ≠ 0`): `flowEnergy (3·current) = 9 ≠ 5 = 1 + 4`. |
| `effectiveResistance_le_flowEnergy` | `hnonneg` | **Fence** — the delivered signed fixture `sgnK4Adj` with a new unit flow `0→3→1→2` riding *both* negative edges: antisymmetric, supported (negative entries are nonzero), divergence exactly `e 0 − e 2`, energy `−1 < 0` = the delivered junk resistance `sgnK4_fallback_zero_QA`. The dropped-`hnonneg` statement reads `0 ≤ −1`. The 2026-08-20-era `negWAdj` witness cannot serve here: its support graph is edgeless, so `hconn` fails there — connectivity is genuine exactly on `sgnK4Adj`. |
| 〃 | `hA` | Structural — `hconn`'s support graph consumes the symmetry proof. |
| 〃 | `hconn` | **Non-fenceable** — `hθ` genuine forces `u, v` same-component (a supported flow's divergences sum to zero per component while `e u − e v` contributes `1` to `u`'s), and same-component demand solvability is the crust theorem. Dropped-`hconn` stays true wherever `hθ` holds. P4. |
| 〃 | `hθ` | Structural — the object. |

### Step 4 — Rayleigh monotonicity

| Theorem | Clause | Verdict |
| --- | --- | --- |
| `isFlowOn_of_le` | `hnonneg` | **Fence** — `negWAdj ≤ zeroWAdj` entrywise (negative below zero), `θ = phantomFlow` a genuine flow on `negWAdj` (its only zero entries are diagonal): the conclusion is exactly the delivered `phantomFlow_not_isFlowOn_QA`. A signed network's flow space does *not* transfer upward into a dominating network whose zeros sit above negative entries. |
| 〃 | `hle` | **Fence** — `edgeAdj`, `θ = electricalCurrent edgeAdj ![1,0]` (a genuine flow), `B = zeroWAdj`: the current carries `1` across the zero-conductance pair of `B`. |
| `flowEnergy_le_of_le` | `hθ` | **Fence** — `A = zeroWAdj`, `B = edgeAdj` (dominating), `θ = phantomFlow`: `flowEnergy B θ = 1 > 0 = flowEnergy A θ` (the delivered `phantom_flowEnergy_zero_QA`). An unsupported flow's energy comparison inverts. |
| 〃 | `hnonneg` | **Fence** — `A = negWAdj ≤ edgeAdj = B`, `θ = phantomFlow` genuine on `A`: `flowEnergy B θ = 1 ≤ −1 = flowEnergy A θ` is false. Negative conductances make the *lower* network's energy smaller — the comparison direction needs nonnegativity. |
| 〃 | `hle` | **Fence** — `A = edge2Adj`, `B = edgeAdj` (the *reverse* domination fails: `1 < 2`), `θ` the unit current: `1 ≤ 1/2` false (the orientation guard's numbers at the energy level, via the delivered `edge2_crossEnergy_value_QA`). |
| `effectiveResistance_le_of_le` | `hnonnegA` | **Fence** — `A = negWAdj ≤ edgeAdj = B`: `R_B 0 1 = 1` (delivered) against `R_A 0 1 = −1` — *not* junk: the signed edge's demand is genuinely solvable (`f = ![0,1]`, voltage difference `−1`; fixture-local uniqueness by the single row equation), a real negative resistance. Dropped statement reads `1 ≤ −1`. |
| 〃 | `hconnA` | **Fence** — `A = cheatWAdj` (edge `{0,1}` + isolated `2`, support graph disconnected), `B = connPathAdj` (dominating, connected): `R_B 0 2 = 2` (delivered) against `R_A 0 2 = 0` — the isolated vertex makes the demand `e 0 − e 2` unsolvable at row `2` (degree `0`), so the total function takes its junk fallback and the dropped statement reads `2 ≤ 0`. Reinforcing a *disconnected* network can only add positive resistance above a junk zero. |
| 〃 | `hnonnegB` | **Non-fenceable / P4** — implied by `hnonnegA` + `hle` entrywise (`B ≥ A ≥ 0`). |
| 〃 | `hconnB` | **Non-fenceable / P4** — the ADVERSARIAL_REVIEW worked pilot's own finding: `supportGraph_connected_of_le` derives it from `hA, hB, hle, hconnA`. |
| 〃 | `hA`, `hB` | Structural — consumed by the support graphs in `hconnA`/`hconnB`. |
| 〃 | `hle` | **Screened** — the orientation guard `rayleigh_orientation_guard_QA` refutes the reversed conclusion on the same numbers. |
| 〃 | `u v` | Structural — the object. |

### Step 5 — capacity reinforcement

| Theorem | Clause | Verdict |
| --- | --- | --- |
| `le_increaseConductance` | `hδ` | **Fence** — `edgeAdj`, `δ = −1`: the reinforced entry is `0 < 1`, so `A k l ≤ reinforced k l` fails at the reinforced pair. |
| `increaseConductance_apply_of_reinforced` / `_of_not_reinforced` | `h` | Structural — `h` is the branch condition. |
| `increaseConductance_isSymm` | `hA` | **Fence** — reinforcing the asymmetric `asymWAdj` pair `(0,1)` raises `A 0 1` to `3` and `A 1 0` to `2`: still asymmetric. |
| `increaseConductance_nonneg` | `hnonneg` | **Fence** — `negWAdj` reinforced by `δ = 1/2`: the reinforced entry `−1/2 < 0`. |
| 〃 | `hδ` | **Fence** — `edgeAdj` reinforced by `δ = −2`: the reinforced entry `−1 < 0`. |
| `supportGraph_le_of_le` | `hle` | **Fence** — `A = connPathAdj`, `B = cheatWAdj`: the support edge `{1, 2}` is lost (its `B`-entry is `0`), so the containment fails at that pair. |
| 〃 | `hA`, `hB` | Structural — the support graphs consume them. |
| `supportGraph_connected_of_le` | `hconn` | **Fence** — `A = B = connDiscAdj` (`hle` = `le_refl` genuine): the conclusion is exactly the delivered `connDisc_not_connected_QA`. |
| 〃 | `hle` | **Fence** — `A = connPathAdj` (connected, genuine), `B = cheatWAdj` (not dominating: `connPathAdj 1 2 = 1 > 0`): the conclusion needs the new `cheatWAdj`-disconnectedness pin (walks from `2` have no first edge — every `cheatWAdj 2 · = 0`). |
| 〃 | `hA`, `hB` | Structural. |
| `effectiveResistance_le_increaseConductance` | `hδ` | **Fence** — `edgeAdj`, `δ = −1/2`: the reinforced network is the conductance-`1/2` edge (`halfEdgeAdj`), whose resistance is genuinely `2` (potential `![2, 0]`), above `R edgeAdj 0 1 = 1` (delivered): the dropped statement reads `2 ≤ 1`. A *negative* reinforcement raises resistance. |
| 〃 | `hconn` | **Fence** — `A = cheatWAdj` (disconnected — hypothesis dropped), reinforce the pair `(1, 2)` by `δ = 1`: the reinforced network computes to exactly `connPathAdj` (entrywise), so `R 0 2` goes `0 → 2` and the dropped statement reads `2 ≤ 0`. The ICP-facing one-hypothesis form genuinely needs the original network's connectivity. |
| 〃 | `hA`, `hnonneg` | Structural / screened-adjacent — `hA` feeds the support graph; the `hnonneg` clause reduces to `increaseConductance_nonneg`'s dropped forms (fenced above at the constructor level). |

**Priced fence count: 22** (one screened-by-derivation), plus the
non-fenceable/P4 records above and the structural classifications.

## New fixtures and helper obligations

1. `asymPath4Adj : Matrix (Fin 4) (Fin 4) ℝ` — the asymmetric 4-path
   `0 ⇄(2/1) 1 ⇄(1/1) 2 ⇄(1/2) 3` (only the end links asymmetric).
   Pins: asymmetry; the demand `e 0 − e 3` solvable at
   `f = ![3/2, 1, 1/2, 0]` (entrywise); the fixture-local uniqueness
   `∀ g` solving, `g 0 − g 3 = 3/2` (linarith over the four row
   equations — this is the route that pins `effectiveResistance` with
   no `hA`-free uniqueness lemma); `flowEnergy (current f) = 1`;
   `quadForm (laplacian A) f = 3/2`.
2. `cycleFlow : Matrix (Fin 3) (Fin 3) ℝ` — the antisymmetric 3-cycle
   `0→1→2→0`. Pins: antisymmetry; divergence zero at every vertex;
   failure of support on `cheatWAdj`; the three energy values (`4`, the
   sum, `1`) at `f = ![1,0,0]`.
3. The double current `2 • current` on `edgeAdj`: divergence `[2, −2]`;
   genuine flow; energies `9`, `1`, `4`.
4. `negRouteFlow : Matrix (Fin 4) (Fin 4) ℝ` — the unit flow
   `0→3→1→2` on `sgnK4Adj` riding both negative edges. Pins:
   antisymmetry; support (all ridden entries nonzero — negative is not
   zero); divergence `e 0 − e 2`; energy `−1`.
5. `IsFlowOn negWAdj phantomFlow` — the negative-conductance support
   pin (only diagonal entries vanish there).
6. `halfEdgeAdj : Matrix (Fin 2) (Fin 2) ℝ` — the conductance-`1/2`
   edge; `increaseConductance edgeAdj 0 1 (−1/2) = halfEdgeAdj`
   entrywise; connected; `R = 2` via the potential `![2, 0]`.
7. `cheatWAdj` support-graph disconnectedness — the walk-blocks idiom
   from `Connectivity_QA` (`connDisc_walk_blocks`), one block: every
   walk from `2` dies at its first edge since `cheatWAdj 2 · = 0`.
8. `cheatWAdj` demand-`e 0 − e 2` unsolvability (row-`2` zero) and the
   junk pin `effectiveResistance cheatWAdj 0 2 = 0`.
9. `increaseConductance cheatWAdj 1 2 1 = connPathAdj` entrywise.
10. `negWAdj`'s genuine resistance `−1` (witness + fixture-local
    uniqueness from the single row equation).

## Non-goals

- No shelf (`ElectricalFlow.lean`) change: every fence is a theorem
  instantiation; the P4 findings are recorded here, not acted on.
- No `-- @refutes` tags: nothing admitted is consumed (the family is
  hard crust; `#print axioms` audited on every new declaration).
- The Foster and KernelBridge QA families are the cluster's remaining
  unaudited members, next in consumption order.

## Delivery record (2026-09-04, run `20260904T112107Z-run-1`)

DELIVERED at the full planned scope — QA-only, zero axiom contact
(count stays 4; `#print axioms` via `wip/efflowfences_axcheck.lean` on
all 89 new declarations — every one exactly `propext, Classical.choice,
Quot.sound`; no `-- @refutes` tags — theorem instantiations, nothing
admitted consumed). QA 4695 → 4780 (+85 by the generator metric; the
89 declarations include the five fixture `def`s `asymPath4Adj`,
`cycleFlow`, `doubleCurrent`, `negRouteFlow`, `halfEdgeAdj`). Radar QA
axis synced to 4780, score held 4.5 per protocol (negative witnesses of
an already-counted family, not a named-gap closure). Landed as a pure
insertion in `ElectricalFlow_QA.lean`'s new `AdversarialFences` section
(814/0 in numstat), spiked first in `wip/efflowfences_spike.lean` to
zero errors/zero warnings (two fix rounds, all in recorded trap
classes).

All 22 priced fences closed with isolation companions, exactly as the
survey priced them — no clause was re-scoped, screened, or dropped in
landing: the agreement/identity `hA` pair at `asymPath4Adj`
(`1 ≠ 3/2`); the superposition `hd` at `cycleFlow` (`4 ≠ 2`) and
`hdiv` at `doubleCurrent` (`9 ≠ 5`); Thomson's `hnneg` at
`negRouteFlow` on the delivered signed 4-cycle (`0 ≤ −1`); the
flow-space `hnneg`/`hle` pair; the energy-comparison `hθ`/`hnneg`/`hle`
trio (`1 ≤ 0`, `1 ≤ −1`, `1 ≤ 1/2`); Rayleigh's `hnnegA` (the signed
edge's genuine negative resistance: `1 ≤ −1`) and `hconnA` (`2 ≤ 0`);
the support-monotonicity `hle`; the connectivity-adapter `hconn`/`hle`
pair; the reinforcement entry `hδ`/`hA`/`hnneg`/`hδ` quartet; and the
headline reinforcement `hδ` (`2 ≤ 1`) and `hconn` (`2 ≤ 0`, the
reinforced cheat network computing entrywise to exactly the path);
plus `isFlowOn_electricalCurrent`'s `hA` by one-step derivation from
the delivered antisymmetry witness. The three P4 records stand as
surveyed.

### Technique findings

1. **The `degreeMatrix` dependent-`if` stall, third confirmation —
   now on `Fin 4` with an entrywise `if`-fixture.** Unfolding
   `laplacian`/`degreeMatrix`/`deg` for `(laplacian A).mulVec f` left
   `↑(Finset.filter …).card` terms the simp set cannot evaluate;
   the recorded `laplacian_mulVec_apply` diffusion-form route
   (`rw [laplacian_mulVec_apply]` before `fin_cases`) evaluates
   cleanly. This is now the third independent confirmation of the
   2026-09-04 finding; the diffusion form should be the default route
   for any `Fin ≥ 3` Laplacian-action pin.
2. **Matrix-literal `!![…]` fixtures on `Fin 4` do not evaluate under
   `simp [fixture]`** — entries at literal indices stall as
   `Matrix.vecHead (Matrix.vecTail …)`; the entrywise `if`-definition
   pattern (as `sgnK4Adj`, `connDiscAdj`) evaluates trivially. `Fin 2`
   and `Fin 3` literals evaluate fine (`doubleCurrent`, `cycleFlow`),
   so the trap is scale-specific — worth citing before any `Fin 4+`
   literal fixture is attempted.
3. **`induction` on a `Walk` whose start index is a literal fails**
   ("index in target's type is not a variable") — the
   `Connectivity_QA` idiom (property as an iff on *both* endpoints,
   `u = 2 ↔ v = 2`, closed in the `cons` case by `iff_of_false` with
   the block argument) is load-bearing style; a start-fixed statement
   (`Walk 2 v`) does not admit the induction at all.
4. **Term-mode `by norm_num` inside an anonymous constructor can be
   skipped by the elaborator** (linter: "tactic does nothing"/"never
   executed") even though the same goal closes under tactic-mode
   `norm_num` — the robust idiom is `refine ⟨…, ?_⟩` then the tactic,
   which worked everywhere.
5. **`rw [row_zero _] at h` cannot synthesize the placeholder** when
   the row index is an inaccessible induction variable — the working
   route is a standalone helper lemma quantified over the index
   (`cheat_pos_touching2_false`), consumed by `exact`.

### Verification

Spike first (`wip/efflowfences_spike.lean` — the full 89-declaration
delivery, iterated to zero errors/zero warnings before any shelf edit,
two fix rounds); `lake env lean` on the landed module (zero errors,
zero warnings); explicit `lake build
Scaffold.QA.SpectralGraph.ElectricalFlow_QA` ✔; the 89-declaration
axiom audit above; full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh artifacts,
0 stale, 0 missing, exit 0; `lint_axioms` exit 0 (4 current axioms,
unchanged; only the allowlisted-confirmed PF finding);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (**4780/4/0**)
with the verification row; `check_scaffold_map_freshness` exit 0 after
the 4695 → 4780 stats sync in both map data files and SVG regeneration
(49 stations, no status change — none owed). The landing verified a
pure insertion (814/0 in numstat). Nothing committed; the prior runs'
uncommitted deliveries preserved.
