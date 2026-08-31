# Proposal: Certified Sparsification Schedules for Scalable GNN Training

**Status:** Proposed, but see the correction below before treating this as
new work — most of it is already delivered. Authorizes documentation/
packaging work now (Track A); Track B is not authorized by this document
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
