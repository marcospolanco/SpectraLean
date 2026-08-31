# Proposal: Certified Sparsification Schedules for Scalable GNN Training

**Status:** **Track A DELIVERED 2026-08-31** (run `20260831T042937Z-run-1`;
see the delivery record at the bottom). Track B remains gated elsewhere
(`matrix-master-bound-first-slice.md` Step 2, operator decision) and is
not authorized by this document. Authorizes documentation/packaging
work now (Track A); Track B is not authorized by this document
and is already gated elsewhere.

**Provenance:** New-capability menu item #3, chosen by the operator
2026-08-30 alongside item #2
(`message-passing-depth-mixing-bound.md`). Framed originally as: *"ties
the matrix-concentration axis to leverage-score sparsification... highest
practical value, but gated on the harder Lieb-concavity step in the matrix
retirement route that's currently parked."*

## Correction: the theorem already exists

That framing implies the certified guarantee doesn't exist yet and is
blocked. **It already exists, delivered 2026-08-28.**
[`spectral-sparsification-via-leverage-scores.md`](spectral-sparsification-via-leverage-scores.md)
landed exactly this statement in `Scaffold/Derived/SparsificationTail.lean`:

```
theorem sparsification_graph_budget [Nonempty V] (hnn : ∀ i j, 0 ≤ A i j)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (q : ℝ) (hq : 0 < q)
    (hqbudget : (8 / 3) * Real.log (2 * (Fintype.card V : ℝ) / δ)
      / ε ^ 2 ≤ q) :
    ssMeasure A hA q hq.le
        {ω | ∃ x : V → ℝ, (1 - ε) * quadForm (laplacian A) x
            > quadForm (ssLaplacian A hA q ω) x ∨
          quadForm (ssLaplacian A hA q ω) x
            > (1 + ε) * quadForm (laplacian A) x}
      ≤ ENNReal.ofReal δ
```

Read informally: **sample `q ≥ (8/3)·log(2n/δ)/ε²` edges (per-edge
leverage-score sampling), and with probability at least `1 − δ`, *every*
vector `x` (in particular every graph signal a spectral GNN filter would
apply) has its Laplacian quadratic form preserved within a factor
`(1 ± ε)`.** This is precisely "sample this many edges, your GNN's
spectral filter output changes by at most `ε` with probability `1 − δ`" —
the capability as originally described, already proved, already QA'd,
already in the tree.

## What is actually still missing: the trust caveat, not the theorem

`sparsification_graph_budget` and its precursor
`sparsification_multiplicative_budget` are **conditional on
`matrix_bernstein`** — Tropp's matrix Bernstein inequality, still an
admitted axiom (source-cited, hazard-audited, now carrying a
`Replacement path:` note per
`scripts/check_refutation_independence.py`'s companion lint pointing at
`matrix-master-bound-first-slice.md`'s gated Step 2). The guarantee is
real and Lean-checked *relative to* that axiom, not unconditionally proved.
This is the genuine, correctly-identified gate from the original framing —
it was just attached to the wrong thing (the theorem's existence, rather
than the theorem's unconditional status).

## Two honestly separate tracks

### Track A — package and expose what's already proved (unblocked, do now)

No new Lean proof work. The existing guarantee needs to be legible to the
audience it's actually for:

1. A short, ML-facing usage note (in `docs/` or alongside
   `SparsificationTail.lean`'s module doc) stating the budget formula
   `q ≥ (8/3)·log(2n/δ)/ε²` in plain terms a GNN practitioner can apply
   without reading the Lean, **with the `matrix_bernstein` trust caveat
   stated up front, not buried** — this project's whole discipline is
   built on never letting a conditional result read as unconditionally
   proved.
2. Optionally, a closed-form convenience corollary computing a concrete
   `q` from `(n, ε, δ)` directly (the current statement takes `q` as a
   hypothesis to be discharged; a corollary that instead *outputs* the
   minimal integer `q` may be more directly usable by a caller who doesn't
   want to solve the inequality themselves) — small, mechanical, zero new
   axioms.
3. Cross-reference from `docs/arch/python-certificate-bridge.md` as a
   second candidate certified quantity (alongside the spectral upper-bound
   certificate already named there) — not building the bridge itself, just
   noting the connection so a future bridge implementation has this on its
   list.

### Track B — retire `matrix_bernstein`, making the guarantee unconditional (highest value, already gated, not decided here)

This is the "harder Lieb-concavity step" from the original framing, and it
is **already identified and gated** in
[`matrix-master-bound-first-slice.md`](matrix-master-bound-first-slice.md)'s
own "Step 2 — the sum-MGF gate": Tropp's Theorem 6.1 via Lieb's concavity
of the trace exponential, gated on an **operator decision** between
admitting the analytic core (Golden–Thompson/Lieb as newly cited axioms)
and proving it outright (genuinely deep, multi-run). **This proposal does
not reopen or duplicate that gate.** It simply names the dependency: if
and when Step 2 lands, `sparsification_graph_budget` (and every other
consumer of `matrix_bernstein`) becomes unconditionally proved with no
further work needed on the sparsification side — the theorem statement
does not change, only its trust status does.

## Acceptance criteria (Track A only — Track B is out of scope here)

- No new axiom, `sorry`, or `admit`.
- The usage note states the `matrix_bernstein` conditionality explicitly,
  matching this project's citation/trust-reporting discipline
  (`docs/2_ARCHITECTURE.md` §5).
- If the closed-form `q`-producing corollary is built: `#print axioms`
  reads exactly `propext, Classical.choice, Quot.sound` (it can only ever
  be *at most* as trusted as `sparsification_graph_budget`, i.e. still
  conditional on `matrix_bernstein` — do not let the corollary's framing
  imply otherwise).
- Full ladder passes; records ladder completed in the same delivery.

## Deferred / out of scope

- Track B itself — completing the matrix master-bound retirement route's
  Step 2. Tracked at `matrix-master-bound-first-slice.md`, gated on the
  operator decision already recorded there. Not this proposal's to decide
  or execute.
- Building the Python certificate bridge — tracked at
  `docs/arch/python-certificate-bridge.md`, itself gated on an operator
  decision. This proposal only adds a cross-reference, not the bridge.

## Delivery record (Track A, 2026-08-31, run `20260831T042937Z-run-1`)

All three Track A items delivered in one run; zero new axioms (count
stays 5), zero `sorry`/`admit`, QA 3246 → 3252 (+6).

**(1) The closed-form corollary** (item 2), in
`Scaffold/Derived/SparsificationTail.lean`'s new Track A section:

- `sparsificationBudget n ε δ := max 1 ⌈(8/3)·log(2n/δ)/ε²⌉` — the
  minimal natural `q` certified for *both* clauses of the budget
  hypothesis;
- `sparsificationBudget_pos` / `_le` / `_min` — positivity, the budget
  inequality, and **minimality among naturals** (any positive natural
  meeting the inequality dominates the closed form — it is the exact
  minimum, not merely a valid choice). All four are pure real
  arithmetic: **`#print axioms` reads exactly
  `propext, Classical.choice, Quot.sound`**, per the acceptance
  criterion;
- `sparsification_graph_budget_closedForm` — the plug-in guarantee:
  pass only the graph hypotheses and `(ε, δ)`; the sampling count comes
  from the formula. Honestly **conditional on `matrix_bernstein`**
  (standard three + that axiom), exactly as trusted as the budget
  corollary it applies; its docstring says so and the usage note
  repeats it.

QA (`SparsificationTail_QA.lean`'s closed-form budget section, +6): the
budget pinned at two exact-`e` designs where `Real.log_exp` collapses
the log (`budget_e_design_QA` = **8** exactly; `budget_exp3_design_QA`
= **24** — the formula tracks the log argument, not a constant); the
**`max 1` floor load-bearing** (`budget_floor_QA`: at `n = 1`, `δ = 10`
the ceiling alone is `0`, killing the `0 < q` clause every budget
theorem needs); minimality pinned through `sparsificationBudget_min`
itself (`budget_minimal_e_design_QA`: the inequality provably fails at
`q = 7`); the closed form **joined to the file's own hand budget**
(`budget_closedForm_le_hand_QA`: `sparsificationBudget 2 (1/2) (1/2)
≤ 100`, the same `log 8 ≤ 300/32` route the hand-worked
`budget_tail_K2` instance used); and the plug-in interface pin
`budget_closedForm_K2`. The six arithmetic pins at exactly the standard
three; the interface pin honestly carrying `matrix_bernstein`
(`wip/gnnbudget_axcheck.lean`).

**(2) The ML-facing usage note** (item 1):
`docs/gnn-sparsification-budget.md` — the budget formula in plain
terms, the worked `n = 10⁶` interpretation, the certificate-vs-
recommendation distinction, and the `matrix_bernstein` trust caveat as
the first section. Linked from the module docstring, the README docs
list, and the README sparsification highlight.

**(3) The python-bridge cross-reference** (item 3): the "Not limited to
`lambda2`" non-goal of `docs/arch/python-certificate-bridge.md` now
names the budget check as the second candidate certified quantity
(pure ordered-real arithmetic, kernel-checkable, feeding the
conditional guarantee), linking the usage note.

**Verification** (spike `wip/gnnbudget_spike.lean` iterated to zero
errors before any shelf edit): `lake env lean` zero errors on both
touched modules; explicit `lake build` targets ✔; **full `lake build` ✔
(2407/2408) immediately followed by `check_build_completeness.py` —
131/131 fresh artifacts, exit 0**; `lint_axioms` (5), 
`check_refutation_independence` (10 tagged, clean),
`check_public_reachability` (62 modules), `check_citations`,
`check_markdown_links`, **`check_scaffold_map_freshness` exit 0**
(after the 3246 → 3252 stats sync in both map files + SVG regen);
scoreboard regenerated at 3252/5/0 with this verification row; README,
radar QA axis (score held at 4.0 per protocol — packaging plus pins for
the already-counted sparsification family), `index/map/spectral_graph.md`
(the module's Track A paragraph and two table rows), and both map data
tables updated. The delivery changes no axiom disposition and no
existing public statement.

**Remaining:** Track B (the Lieb-concavity step) stays gated on the
operator decision in `matrix-master-bound-first-slice.md` — when it
lands, `sparsification_graph_budget` and
`sparsification_graph_budget_closedForm` become unconditionally proved
with no change to their statements.
