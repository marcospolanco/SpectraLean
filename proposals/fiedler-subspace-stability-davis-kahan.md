# Proposal: Fiedler Subspace Stability via Davis–Kahan

**Status:** Proposed; **priority:** Medium-High. This document authorizes
no Lean changes, axiom admissions, commits, or external publication on
its own — Step 0 (the survey below) must land before Step 1 begins.

## The obligation this discharges

`davis_kahan_sin_theta`
(`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/DavisKahan.lean`)
was retired from axiom to fully proved theorem on 2026-08-21 — real hard
crust, not conditional on anything. Per `scripts/measure_load_bearing.py`,
it has **zero real theorem consumers anywhere in the shelf**: every
other file that imports the module does so for something else (Weyl,
Duhamel, Resolvent live nearby and are separately consumed), and nothing
actually invokes `davis_kahan_sin_theta` by name in a proof term. For the
standard eigenvector/subspace-perturbation bound behind spectral
clustering stability and PCA robustness theory generally to sit proved
and never once called is the sharpest version of this session's
robustness concern: a load-bearing-looking result whose exact hypothesis
shape (the two-cluster separation `δ`, the rank/tie case split) has never
been exercised by anything that would break if it were misstated.

## Assessed from

`DavisKahan.lean`'s exact statement (`initialProjector`, the sorted-index
separation hypothesis `evals hAE ⟨k+1⟩ - evals hA ⟨k⟩ ≥ δ`, the ℓ² operator
norm bound `‖E‖ / δ`), `Scaffold/Mathlib/GraphTheory/Fiedler.lean`
(`fiedlerIndex`, `fiedlerVector`, `fiedlerVector_eigen`, both built over
the **combinatorial** Laplacian `laplacian A`, requiring only
`hA : A.IsSymm` and `hcard : 2 ≤ Fintype.card V` — no regularity), and
`Scaffold/Mathlib/GraphTheory/Heat.lean`'s connected-graph kernel fact
(`laplacian_kernel_eq_span_onesVec` — used already in Foster's proof —
the Laplacian's zero-eigenspace is *exactly* `span {onesVec}` on every
connected graph, perturbed or not, so long as both `A` and `A + E` remain
valid connected-graph Laplacians).

## The statement (draft shape — subject to Step 0 correction)

**Step 1 (direct instantiation, tightly scoped):** for a connected
weighted graph `A` and a symmetric perturbation `E` such that `A + E` is
also a valid symmetric adjacency matrix, with the Fiedler eigenvalue
`λ₂` (index 1, i.e. `k = 1` in `DavisKahan`'s convention: the bottom-2
cluster) separated from the perturbed graph's third eigenvalue by `δ`,

```
davis_kahan_sin_theta (laplacian A) E hA hAE 1 hk δ hδ hsep
  : ‖initialProjector (laplacian (A + E)) hAE' 1
      - initialProjector (laplacian A) hA' 1‖ ≤ ‖E‖ / δ
```

instantiated directly — the rank-2 subspace spanned by `{onesVec,
fiedlerVector A}` moves by at most `‖E‖ / δ` under the perturbation.
This is a mechanical instantiation (no new proof machinery), but it is
the first real exercise of `davis_kahan_sin_theta`'s exact hypothesis
shape by a genuine graph-theoretic object rather than an abstract
symmetric matrix pair, and it composes cleanly with either
[spectral-sparsification-via-leverage-scores.md](spectral-sparsification-via-leverage-scores.md)
or
[matrix-hoeffding-spectral-gap-estimation.md](matrix-hoeffding-spectral-gap-estimation.md)
as the "then bound the subspace rotation" half of a concentration → subspace-stability
pipeline, if either of those lands first (not required — this proposal
stands alone with `‖E‖` as a hypothesis, not a derived quantity).

**Step 2 (the sharper, deferred statement — the actual payoff, not
authorized in Step 1):** isolate the **Fiedler vector's own** rotation,
not the rank-2 subspace containing it. Since `laplacian_kernel_eq_span_onesVec`
pins the index-0 component to the exact same fixed line `span {onesVec}`
in both `A` and `A + E` (connected graphs never move their kernel
direction — only the Laplacian null space, not the perturbation, decides
it), the rank-2 rotation bounded in Step 1 is entirely attributable to
the Fiedler component. Making that precise needs a new lemma: for
`P, Q` rank-2 symmetric idempotents both containing a common fixed
rank-1 subprojector `Π₀` (`P * Π₀ = Π₀`, `Q * Π₀ = Π₀`), bound the
distance between the residual rank-1 projectors `P - Π₀` and `Q - Π₀` in
terms of `‖P - Q‖` — plausible linear algebra, not yet verified against
the pin. **Step 0 must check this residual-projector lemma's exact
proof route (or find it already in `Spectral.lean`/`Resolvent.lean`)
before Step 2 is authorized**; if it does not close cheaply, Step 1's
rank-2 statement stands alone as the delivered consumer and Step 2 is
iceboxed with the specific obstruction recorded.

## QA obligations (draft — refine after Step 0)

1. A small connected fixture (K₂, a 3-path, or a 4-cycle) with a
   concrete symmetric perturbation `E` (e.g. a single edge-weight
   change), the projector distance computed both by the theorem and by
   direct eigenvector computation on the fixture, cross-checked.
2. A boundary witness: `δ` too small or the perturbation large enough to
   force the trivial bound `‖P − Q‖ ≤ 1` (the tie-case branches in
   `davis_kahan_sin_theta`'s own proof) — instantiated on the fixture to
   confirm the graph-theoretic wrapper inherits the tie-awareness
   correctly, not just the generic-case branch.
3. If Step 2 lands: the residual-projector lemma exercised on the same
   fixture, with the Fiedler vector's own angular movement computed by
   hand and compared to the derived bound.

## Acceptance bar

- Step 0 delivers a written verdict on Step 2's residual-projector
  lemma before it is attempted; Step 1 alone is a complete, valid
  delivery if Step 2 does not close cheaply.
- Zero new axioms; `davis_kahan_sin_theta` becomes a real consumed
  dependency, not merely an imported module.
- `docs/7_SGT_RADAR.md` axis 4 (Cuts/Expansion) is the natural re-score
  target — this is the first stability statement about the Fiedler
  partition itself, distinct from Fiedler's existing static
  conductance-certificate content.

## Companion

[Fiedler Partitioning (delivered)](fiedler-partitioning.md),
[Discharge Perturbation Axioms (Davis–Kahan delivery record)](discharge-perturbation-axioms.md),
`docs/7_SGT_RADAR.md` axis 4.
