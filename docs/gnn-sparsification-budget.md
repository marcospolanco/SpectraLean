# A Certified Edge-Sampling Budget for GNN Training

**Status:** Practitioner-facing usage note for the delivered guarantee
(`proposals/spectral-graph-sparsification-gnn-training.md`, Track A;
Lean source: `Scaffold/Derived/SparsificationTail.lean`).
**Read the trust caveat first — it is the point of this note.**

## The trust caveat, up front

The guarantee below is **Lean-machine-checked *relative to* one
explicit, cited, still-unproved axiom**: `matrix_bernstein` (Tropp,
"User-friendly tail bounds for sums of random matrices", FoCM
12(4):389–434, 2012, Theorem 1.1). Every *hypothesis* of the theorem —
the sampling design, the centering, the variance bound, the constants —
is proved unconditionally in Lean; the tail inequality itself is
admitted as that axiom. If and when the matrix master-bound retirement
route (`proposals/matrix-master-bound-first-slice.md`, gated Step 2)
lands, this guarantee becomes unconditionally proved with **no change
to its statement**. Until then, do not describe it as unconditionally
proved. The budget *formula* (`sparsificationBudget` below) is pure
arithmetic and carries **no axiom** at all.

## What you get

On a weighted undirected graph with symmetric nonnegative weights
`A ∈ ℝ^{n×n}` (any `n ≥ 1`, connectivity not required), sample edges by
leverage score: include each ordered vertex pair independently with the
delivered per-pair probability at budget `q`, forming the sampled
Laplacian `L̃(ω)`. Then for every accuracy `ε ∈ (0, 1]` and failure
probability `δ > 0`:

> **Sample `q ≥ (8/3) · log(2n/δ) / ε²` (per edge) and, with
> probability at least `1 − δ`, *every* graph signal `x` satisfies
> `(1−ε) · xᵀLx ≤ xᵀL̃x ≤ (1+ε) · xᵀLx`.**

"Every graph signal" is the GNN-relevant quantifier: any spectral filter
your GNN applies is a function of the Laplacian's action on vectors, and
the theorem preserves *all* quadratic forms simultaneously — so every
Laplacian-based filter output moves by at most the `ε` factor, not just
one fixed test vector. This is the Spielman–Srivastava sparsifier
guarantee in its textbook multiplicative form
(`sparsification_graph_budget` in `SparsificationTail.lean`).

## The closed form

The theorem takes `q` as a hypothesis you must discharge. The companion
definition outputs it directly:

```
sparsificationBudget n ε δ := max 1 ⌈(8/3) · log(2n/δ) / ε²⌉
```

Three proved properties (`sparsificationBudget_pos`, `_le`, `_min`, all
axiom-free):

- it is positive;
- it meets the theorem's budget inequality, so it can be plugged in
  directly (`sparsification_graph_budget_closedForm`: pass only the
  graph, `ε`, and `δ`);
- it is the **minimal** natural `q` with both properties — you are not
  paying an integer of slack over the certificate.

Example: `n = 2` (a single edge, the QA fixture), `ε = δ = 1/2` gives
`sparsificationBudget 2 0.5 0.5 ≤ 100` — proved in QA against the same
`log 8 ≤ 300/32` estimate the hand-worked instance used.

## Worked interpretation

- `ε = 0.1` (10% relative distortion of every quadratic form),
  `δ = 0.05`, `n = 10⁶`: `q ≈ (8/3)·log(4·10⁷)/0.01 ≈ 5300` per
  ordered pair — independent of graph density, exactly the sense in
  which sparsification buys scalability.
- Smaller `ε` costs quadratically; more confidence (smaller `δ`) costs
  only logarithmically.
- The formula is a *certificate*, not a recommendation: it is the
  budget at which this particular proof goes through, pinned minimal
  within that certificate. Empirical samplers often do better; nothing
  here certifies them.

## What this note does not claim

- It does not claim the guarantee is unconditional — see the caveat.
- It does not certify any specific implementation (Python or
  otherwise): the theorem is about the mathematical sampling operator,
  not code. A future Python certificate bridge
  (`docs/arch/python-certificate-bridge.md`) names this budget check as
  its second candidate certified quantity.
- It does not address directed graphs, or sampling schemes other than
  the delivered per-pair leverage-score design.

## Pointers

- Lean: `Scaffold/Derived/SparsificationTail.lean` (module docstring
  lists every declaration); QA pins in
  `Scaffold/QA/Derived/SparsificationTail_QA.lean`.
- Program record: `proposals/spectral-sparsification-via-leverage-scores.md`
  (the theorem, delivered 2026-08-28) and
  `proposals/spectral-graph-sparsification-gnn-training.md` (this
  packaging, Track A).
