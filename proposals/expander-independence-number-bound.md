# Proposal: The Hoffman-Type Independence Number Bound — a Real Consumer for the Expander Mixing Lemma

**Status:** Proposed; **priority:** Medium-High. This document authorizes
no Lean changes, axiom admissions, commits, or external publication on
its own — Step 0 (the survey below) must land before Step 1 begins.

## The obligation this discharges

`Scaffold/Mathlib/GraphTheory/Expander.lean`'s `expander_mixing_lemma`
(delivered `f45cf8e`, decidable-spectral-certificates Step 2) is a real,
substantial, classical result — 24 declarations of genuine spectral
discrepancy machinery — with **zero real theorem consumers anywhere in
the shelf**, confirmed by `scripts/measure_load_bearing.py`. It was
proved as the certificate program's payoff and then never built upon.
This is a sharper case than the concentration-axiom valleys addressed
earlier in this session: `expander_mixing_lemma` is fully proved hard
crust, not an axiom, so its exact hypothesis shape (`d`-regularity, the
`μ`-bound on both non-trivial ends of the spectrum, the specific
`edgeWeight`/discrepancy statement) has genuine mathematical content
sitting unexercised by anything that would break if a constant or
direction were misstated.

**A companion false lead, recorded so it is not re-investigated:**
`Scaffold/Mathlib/Analysis/OperatorTheory/Perturbation/ProjectionGap.lean`
was also found "never built" by the same completeness-check incident
that motivated this proposal's sibling
([verify-build-completeness.md](verify-build-completeness.md)). It is
**not** a valley — `measure_load_bearing.py` shows 5 real Mathlib
consumers (it is load-bearing inside the Davis–Kahan proof chain,
`discharge-perturbation-axioms.md`'s delivered route). Its QA file being
absent from any build artifact was purely the orphaning bug the
completeness check now catches; the module itself was never idle. Do
not propose a consumer for it on the strength of that incident alone.

## Assessed from

`Expander.lean`'s exact statement of `expander_mixing_lemma` (`d`-regular,
symmetric, nonnegative weights; `μ` bounding both `|d − λ₂|` and
`|d − λ_n|`; the discrepancy bound on `edgeWeight A S T`), and a direct
search of the pinned Mathlib
(`.lake/packages/mathlib/Mathlib/Combinatorics/SimpleGraph/`) for
independence-number machinery: **none exists** — no
`SimpleGraph.independenceNumber`, no `IsIndepSet` predicate, nothing.
This means the target statement must be defined natively over Scaffold's
own `WAdj`/`Finset V` conventions, matching how every other
combinatorial predicate in this shelf (`cutTestVector`, `conductance`,
`fiedlerPartition`) is already built — not adapted from an upstream
Mathlib definition that does not exist.

## The statement (draft shape — subject to Step 0 correction)

The classical Hoffman ratio bound, specialized to the mixing lemma
already delivered: for `S` an independent set (no edge weight within
it: `∀ i j ∈ S, i ≠ j → A i j = 0` — the natural nonnegative-weight
reading of "independent" over a weighted graph) of a `d`-regular graph
with second-eigenvalue bound `μ` exactly as `expander_mixing_lemma`
already hypothesizes,

```
(S.card : ℝ) ≤ μ * (Fintype.card V : ℝ) / (d + μ)
```

**Route (mechanical, one application):** instantiate
`expander_mixing_lemma` at `T = S`. Independence collapses
`edgeWeight A S S` to `0` (the sum of a zero function — a short lemma,
likely already close to `edgeWeight`'s existing algebra in
`Expander.lean`'s early sections). The inequality becomes
`d·|S|²/n ≤ μ·|S|·(n−|S|)/n` (the `√` collapses because `S.card = T.card`
makes the product under the root a perfect square — `Real.sqrt_sq` at a
nonnegative quantity). Cancel `|S|/n` (handling `S = ∅` as a trivial
`0 ≤ …` degenerate case first) and rearrange
`d|S| ≤ μ(n−|S|)` to the stated bound. This is genuinely a short,
mechanical derivation from the delivered lemma — the interesting content
is entirely already proved; this proposal's job is packaging it as the
named classical corollary, not new spectral mathematics.

**Step 0 must check, before stating:**
1. Whether `edgeWeight A S S = 0` under the independence hypothesis is
   a one-line consequence of `edgeWeight`'s definition
   (`Expander.lean:91`, a `Finset.sum`) or needs a short supporting
   lemma.
2. The exact degenerate-case handling at `S = ∅` (bound reads `0 ≤ …`,
   trivial) and at `S.card = Fintype.card V` (independent set on the
   whole graph forces `d = 0` — a companion fence worth stating, not
   just avoiding division by zero).
3. Whether `μ + d > 0` needs its own hypothesis or is already implied
   (on a nontrivial graph with `d > 0` and `μ ≥ 0` from `hμ`'s `abs`
   structure, likely free).

## QA obligations (draft — refine after Step 0)

1. A concrete `d`-regular fixture with a known independent set (e.g. a
   bipartite-flavored small graph, or the empty-edge complement of a
   clique) where the bound is evaluated numerically and the independent
   set's actual size checked against it — the fixture should make the
   bound non-vacuous (an independent set that is provably *close to* the
   bound, not trivially far under it, per this session's QA-tightness
   discipline).
2. The degenerate `S = ∅` case and the "independent set = whole graph"
   fence (forcing `d = 0`, refuted on a positive-degree fixture) as
   proved boundary witnesses, not just hypothesis guards.
3. A non-independent-set instantiation showing the hypothesis is load-
   bearing (`edgeWeight A S S ≠ 0` on a fixture with an internal edge,
   the conclusion's derivation genuinely blocked, not just unproved).

## Priced follow-on, not authorized here

**The spectral diameter bound** (`diam(G) = O(log n / log(d/μ))`,
the other classical Expander Mixing Lemma consequence) is explicitly
**not** in this proposal's scope — it needs an iterated ball-growth
argument over `SimpleGraph.dist`/walk-length machinery, a genuinely
harder combinatorial induction than this proposal's one-shot algebraic
corollary, and belongs in its own document if a named consumer prices
it, per the one-step discipline this shelf already follows for Cheeger
and Krylov.

## Acceptance bar

- Step 0 delivers a written verdict on the three checks above before
  any shelf Lean is written.
- Zero new axioms — this is a corollary of already-proved hard crust.
- `Expander.lean` gains its first real theorem consumer.
- `docs/7_SGT_RADAR.md` axis 4 (Cuts/Expansion) is the natural re-score
  target.

## Companion

[Verify Build Completeness](verify-build-completeness.md) (the
incident this proposal responds to), `proposals/decidable-spectral-certificates.md`
(the Expander Mixing Lemma's original delivery), `docs/7_SGT_RADAR.md`
axis 4.
