# The QA Name-Collision Guard and the Exhaustive_QA Witness-Layer Reconciliation

**Status:** COMPLETE (delivered 2026-09-05, run `20260905T142414Z-run-1`,
session `ses_f8e134871ffeiWXCb84ykj7oaD`)

Two halves of one delivery: the mechanical closure of the QA-lattice
name-collision class (the residue the 2026-09-05 `edgeAdj` repair priced
as "unsurveyed"), and the standing audit remainder named by that repair
run's terminal handoff — `Exhaustive_QA.lean`'s free-form witness layer,
reconciled into the per-clause fence discipline.

## Part A: the collision-class survey and guard

### The survey

Scoping the reconciliation (which lives in `Exhaustive_QA.lean` beside
its `asymAdj2` fixture) immediately surfaced a member of the collision
class the `edgeAdj` repair had left unsurveyed: `asymAdj2` is defined
in **both** `Exhaustive_QA.lean` and `Stationary_QA.lean` — identical
bodies, plus two identical degree pins. A full parse of every
`Scaffold/QA/**/*.lean` module (doc comments stripped so prose lines
beginning "theorem and …" are not matched; namespaces tracked through
`namespace`/`section`/`end` stacks) found **24 residual cross-module
duplicate names**, in three mechanism classes:

1. **Identical-body fixture redeclarations** — the direct cost of the
   pre-2026-09-4 convention that QA modules never import each other
   (each file redeclared the fixtures it needed): `asymAdj2`
   (Exhaustive↔Stationary), `edgeAdj2`/`edgeAdj2_deg`
   (Normalized↔Stationary), the `pathAdj` family (six names across
   Cuts/Mixing/Normalized/Stationary, up to four files each),
   `path_vol_QA` (Mixing↔Stationary).
2. **Different-body duplicates** — same graph, different spellings,
   the most dangerous subclass (co-import would still fail hard, but
   a reader diffing the two definitions by name would expect
   equality): `k2Adj`/`k2Adj_nonneg` (Mixing's `!![0,1;1,0]]` vs
   Variational's `fun i j => if i = j then 0 else 1`), the `path3Adj`
   trio (CourantFischer vs Variational), the `triAdj` trio
   (ElectricalFlow's `if`-spelling vs Mixing's `!![…]` literal).
3. **Shared private-helper spellings** — pin/identity lemmas each file
   rederived: `list_two_eq` (five SpectralGraph files; a separate
   three-file set in the Perturbation namespace),
   `two_point_pin` (Cheeger↔Heat),
   `two_point_pin_of_sum_prod` (three Perturbation files),
   `constantStream`/`constantStream_increment_zero_QA`
   (EventStream↔ProjectorDrift).

No rename landed in this delivery: the `edgeAdj` repair's per-pair
recipe (map reference domains from the import graph first; check for
shelf-level same-named API before renaming QA fixtures; expect
out-of-target QA modules to need explicit rebuilds, with
`check_build_completeness.py` as the safety net) stays the repair
route, taken **on demand** when a co-import consumer actually appears
— the prior run's pricing, unchanged. What changed is that the class
can no longer grow silently.

### The guard

`scripts/check_qa_name_uniqueness.py` applies the
`lint_axioms.py` degenerate-corner-guard pattern to the QA lattice:

- fails on any **new** cross-module duplicate (a name declared in more
  than one `Scaffold/QA/**` module within the same namespace);
- fails on any **drift** in the residual allowlist (a rename landing, or
  a new file joining an existing collision) — every allowlisted name
  records its exact sorted file set, so the disposition is settled
  deliberately at each such boundary;
- passes clean on the calibrated tree (24 allowlisted residuals,
  mechanisms recorded in the script);
- scope is `Scaffold/QA/**` only: `Scaffold/Mathlib` is co-imported by
  the umbrella build, so a shelf-level collision fails the build
  immediately rather than staying latent — the guard checks exactly
  the layer where the defect class is latent.

**Self-test (the guard must be able to fail):** two probe modules —
one declaring `asymAdj2` (a third file joining an allowlisted pair)
and both declaring a shared fresh name — produced both failure modes
(`ALLOWLIST DRIFT` with recorded-vs-actual file sets; `NEW collision`
with the rename instruction), then clean again after removal. A guard
that cannot fail would be inert; this one was made to fail before
being trusted.

## Part B: the Exhaustive_QA witness-layer reconciliation

The standing audit remainder (recorded 2026-09-04 by the
normalized-family audit: "`Exhaustive_QA.lean`'s own partial
negative-witness layer over the same interfaces was not re-read (a
separate audit target)"; named the natural next target by the
`edgeAdj` repair run's terminal handoff). The file's 2026-08-17
negative-witness layer predates the per-clause fence discipline:

- **Reconciled:** `asym_boundary_not_dual_QA` (the free-form witness
  that `boundary_compl`'s symmetry hypothesis is load-bearing, `2 ≠ 1`)
  is now the *proof engine* of the per-clause fence
  `exh_boundary_compl_hA_fence_QA` — the witness is inside the
  discipline, consumed rather than merely cited.
- **Completed:** the sibling clause `conductance_compl`'s `hA` is
  fenced at the same `asymAdj2` fixture through pinned conductance
  values (`conductance {0} = 2/min(2,1) = 2` vs
  `conductance {0}ᶜ = 1/min(1,2) = 1`) — the cut-duality pair's
  coverage now exists at this file's own layer, with the Step-1
  `Spectral_QA` fences at `dirB` as an independent second fixture and
  independent proof route.
- **Classified, not converted:** the three `*_separates_QA` theorems
  are interface-separation checks (positive computations that distinct
  inputs evaluate distinctly — they falsify a *collapsed* definition,
  not a dropped hypothesis); they have no per-clause fence form and
  stay as delivered.
- **Isolation companions:** `exhAsym_not_isSymm` (the fixture is
  genuinely outside the dropped symmetric cone) and
  `exhPathAdj_deg_pos` (the walk row-sum computations' positive-side
  companion — the path sits inside `walkTransitionMatrix_row_sum`'s
  `hd` cone, while `Normalized_QA`'s C1 fence kills the dropped
  statement outside it).
- **Clause-surface context recorded in the section docstring:** every
  other hypothesis-bearing statement the file computes from is fenced
  at its home QA file (`laplacian_quadForm` at `dirA`/`sfNegEdge`,
  the walk layer's `hd` clauses in `Normalized_QA` section C); the
  hypothesis-free statements (`vol_compl`, `boundary_empty`/`_univ`,
  `walkTransitionMatrix_apply`, `laplacian_ones_in_kernel`) have
  nothing to fence.
- **Header repair:** the file header's "QA modules are built
  independently and must not import each other" has been false since
  the 2026-09-04 QA-import deliveries and the 2026-09-05 lattice
  repair; it now states the actual policy (fixtures stay fresh-named
  so the module stays independently elaborable; QA-to-QA imports are
  permitted; residual same-named fixtures are tracked by the guard).
- **No new collision instances:** every new name uses `exh`/`exhAsym`
  stems, verified collision-free by the guard (the `asymAdj2` residual
  is still exactly the Exhaustive/Stationary pair).

## Technique findings

1. **The complement-side boundary pin transfer:** the free-form
   witness pins `boundary {0}ᶜ = 1`, but the conductance computation
   at the `{1}` cut needs `boundary {1} = 1`; the transfer is
   `rw [← compl2_0]` then `exact` of the witness side. Rewriting the
   witness's own LHS form directly into the singleton-form goal fails
   (pattern mismatch: `{0}ᶜ` vs `{1}`), the spike's one fix round.
2. **Comment stripping before declaration matching:** prose lines
   beginning "theorem and …" inside doc comments produced a false
   `and` collision in the first survey pass; any future
   declaration-enumeration tooling must strip `/- … -/` and `-- …`
   first.
3. **The guard's failure modes need probing, not assuming:** the first
   self-test probe was itself wrong (it declared `asymAdj2_probe`, a
   *different* name, and the guard correctly ignored it) — a reminder
   that a negative test must exercise the exact failure mechanism
   (joining an allowlisted set; duplicating a fresh name).
4. **Different-body duplicates are the subclass to watch:** the
   identical-body pairs are routine, but `k2Adj`/`path3Adj`/`triAdj`
   carry *different spellings at the same name* — any future rename
   pass must re-pin values per file, not assume name equality implies
   body equality.

## Verification

- Spike first (`wip/exhwitness_spike.lean` — the full 14-declaration
  section, green after one fix round, the trap class recorded above);
  `lake env lean` on the landed module: zero errors, zero warnings.
- Axiom audit (`wip/exhwitness_axcheck.lean`): `#print axioms` on all
  14 new declarations — every one exactly
  `propext, Classical.choice, Quot.sound`; no `-- @refutes` tags
  (theorem instantiations of an all-proved shelf, nothing admitted
  consumed); 12-tag independence check unchanged and clean.
- `lake build Scaffold.QA.SpectralGraph.Exhaustive_QA` ✔ (2190/2190);
  full `lake build` ✔ immediately followed by
  `check_build_completeness.py`: 134 source files, 134 fresh
  artifacts, 0 stale, 0 missing, exit 0.
- The guard: clean on the calibrated tree; both failure modes
  self-tested (see above); probes removed afterward.
- `lint_axioms` exit 0 (4 axioms unchanged); `check_citations`
  ("All axioms have proper citations!"); `check_markdown_links`
  clean; `check_backlog_freshness` clean;
  `check_public_reachability` clean (63 modules — the QA-only section
  unreachable from the umbrella).
- Scoreboard regenerated: QA 6027 → **6041** (+14; 14 theorems, 0 new
  fixtures); map-freshness exit 0 after the stats sync in both map
  data tables and SVG regeneration (49 stations, no status change —
  none owed: this proposal is not a map station's cited source).

## Remaining risk

None owed — QA-layer and tooling only; no axiom disposition changed,
no public statement changed, no shelf API touched. Honest scope: the
collision class is closed *mechanically* (new instances fail the
guard), not *repaired* — the 24 residual names remain, each blocking
exactly its own module-pair co-import until renamed on demand; the
reconciliation completes the named pre-discipline witness layer, so
every free-form negative witness in the QA tree is now inside the
per-clause discipline.

## Next handoff

The Active priority table stays all-Low (decision-gated). The standing
frontiers remain available (the QA axis's randomized half; the priced
undirected `walkTVPair` join; the sharp `|λ₂| = α` layer; the reverse
TV → χ² calculus; the heat audit's priced deferral D1). The audit
method has no remaining named pre-discipline target; the natural next
survey axis is either a residual-pair rename (when a co-import
consumer appears — the recipe is recorded here and in the `edgeAdj`
addendum) or a fresh consumption survey for a new audit target.
