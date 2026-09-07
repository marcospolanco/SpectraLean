# Proposal: The Poincaré Pair's Connectivity-Route Pins

**Status:** COMPLETE. Delivered 2026-09-07 (run `20260907T110729Z-run-1`,
session `ses_f84763143ffeAVPDc1KGOxyMgM`); QA-only, zero axiom contact.

## The census finding this closes

`scripts/consumption_survey.py`'s census (`wip/census_20260907_post8.txt`)
leaves the inert set at 30, with no cluster larger than three. The
selection keys the last seven pins deliveries established are cluster
size and name weight; at the size floor (3-clusters are all modules'
leftover singles and small families), the Poincaré pair wins on name
weight — it is the family's *headline* pair, the two theorems named in
the module's own title, and the shape a consumer holding a connected
graph reaches for. Both

- `poincare_inequality_of_connected` and
- `poincare_inequality_normalized_of_connected`

are never consumed: every existing QA pin in `Poincare_QA.lean` routes
through the `hpos` (positivity) forms `poincare_inequality` /
`poincare_inequality_normalized`, with the gap's positivity discharged
by separately pinned spectrum values (`pcEdge_secondEval_pos_QA` etc.).
The connectivity-transfer route — the twins' whole content, deriving
`0 < λ₂` from `hconn` through `lambda2_pos_of_connected` /
`secondEval_normalizedLaplacian_pos_of_connected` — has never been
exercised by a QA proof.

## What was delivered

Nine QA theorems in `Poincare_QA.lean`'s new `StructuralPins` section
(QA 6661 → 6670), the first genuine consumption of both twins:

- **The connectivity facts** (`pcEdge_supportGraph_connected`,
  `pcP3_supportGraph_connected`, `pcK3_supportGraph_connected`) — the
  support graphs of all three connected fixtures proved connected by
  the repo's established walk idiom
  (`SimpleGraph.connected_iff_exists_forall_reachable` with explicit
  hub walks), each adjacency witness discharged through the fixture's
  own entry interface (`pcEdge_apply` / `pcK3_apply`; `simp [pcP3]`).
  These are the `hconn` hypotheses the twins consume — the first time
  the matrix→graph adapter surface carries a connectivity proof for
  these fixtures.
- **The connectivity-route instance pins**
  (`pcEdge_poincare_of_connected_instance_QA`,
  `pcP3_poincare_of_connected_instance_QA`,
  `pcK3_normalized_poincare_of_connected_instance_QA`) — the
  combinatorial twin instantiated at the `K₂` and `P₃` Fiedler vectors
  and the normalized twin at `K₃`'s `(1,−1,0)`, each conclusion
  derived THROUGH the twin with no spectral certificate in hand: the
  gap's positivity is delivered inside the theorem from `hconn`. The
  statements are identical to the delivered `hpos`-route instances, so
  the raw attainment companions (`pcEdge_poincare_attained_QA`,
  `pcP3_poincare_attained_QA`, `pcK3_normalized_poincare_attained_QA`
  — both sides pinned `2` / `2` / `4`) join them: the connectivity
  route delivers exactly the sharp constants the wrong-constant
  refutation (`pcEdge_wrong_constant_refuted_QA`) proves
  unimprovable. Two routes to the same inequality, one pinned value.
- **The scope witness** (`pcDisc_supportGraph_not_connected`, with the
  helpers `pcDisc_cross_zero` and `pcDisc_walk_stays`) — the
  disconnected fixture's support graph proved NOT connected (walk
  induction: no positive cross-block entry exists, so walks from the
  first block never leave it; a `0→2` walk would contradict
  `2 ≤ 2`). This pins the `hconn` hypothesis as exactly the boundary
  the delivered no-constant fence (`pcDisc_no_poincare_constant_QA`:
  variance `1`, energy `0`, no finite `c` works) prices: connectivity
  rules out precisely the fixtures where no Poincaré constant of any
  size exists.

## Why this is load-bearing

The twins are proved, so a pin cannot falsify their proofs — but the
*interface* the strategy's falsifiability section asks QA to stress is
exactly what the pins exercise: the `hconn : (supportGraph A hA).Connected`
hypothesis shape (through the matrix→`SimpleGraph` adapter, discharged
for the first time at these fixtures), and the conclusion statement
(identical to the `hpos` route's, so any drift in the twin's
statement — e.g. a mis-transfered gap — breaks the join to the pinned
attainment values). The connectivity facts themselves are new
adapter-surface evidence: `supportGraph`'s `Adj i j ↔ i ≠ j ∧ 0 < A i j`
is consumed at three fixtures through `supportGraph_adj`, and the
not-connected witness consumes it through the walk API.

## Technique findings (Lean 4.14 / this Mathlib pin)

- `norm_num` decides the `Fin 2` equality in `pcEdge_apply`'s `if`
  (`if 0 = 1 then 0 else 1`) but NOT the `Fin 3` one (`if 0 = 2 …`
  stays stuck): the `K₃` adjacency witness needs
  `rw [pcK3_apply, if_neg (by decide)]; norm_num`. One fix round in
  the spike; everything else green first try.
- `SimpleGraph.Connected`'s field order in this pin puts
  `Preconnected` first (`hconn.1 0 2` yields `Reachable 0 2`
  directly) — matching the `triIso4_not_connected` idiom in
  `EmpiricalStationary_QA.lean` rather than Mathlib main's
  `Nonempty ∧ Preconnected` order.

## Verification

Spike-first (`wip/pcpins_spike.lean` — green after one fix round, the
`Fin 3` `if` above); the landed module elaborates with zero
errors/warnings; explicit build ✔; the 9-declaration axiom audit
(`wip/pcpins_axcheck.lean`) — every one exactly `propext,
Classical.choice, Quot.sound`; full `lake build` +
`check_build_completeness.py` (135/135 fresh — one self-inflicted
mtime staleness from a diagnostic `touch` cured by the documented
artifact-removal remediation); `lint_axioms` exit 0 (4 axioms
unchanged); `check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new names
collision-free); `check_backlog_freshness` clean; scoreboard
regenerated (1369 / 6670 / 4 / 0); map freshness exit 0 after the
stats sync; **the census re-run (`wip/census_20260907_post9.txt`)
verifying exactly the two targeted theorems leaving the inert set
(1337 → 1339 value-consumed, 30 → 28 never-touched, the `Poincare
(2)` line gone, no bonus, no collateral — diffed against `post8`)**.

## Honest scope

Positive pins plus one negative scope witness; no hypothesis-necessity
fences owed (the twins' hypothesis surface is connectivity, whose
necessity is exactly the delivered no-constant fence — already priced
at admission). The pins are at the module's own three connected
fixtures and one disconnected fixture; the instances are at Fiedler
vectors (attainment joins); no irregular-graph normalized pin (the
normalized twin's `hd` degree-positivity clause is discharged at the
regular triangle only — an irregular connected fixture would be a
natural future pin but the twin's consumption does not need one).
