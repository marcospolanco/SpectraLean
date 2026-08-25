# Proposal: Recovering Tikhonov / Heat as Functional-Calculus Instances

**Status:** Gated stub — not authorized. This is Step 4 of
[hermitian-functional-calculus-bridge.md](hermitian-functional-calculus-bridge.md),
named there as a separate consumer per the one-shape-per-proposal
discipline. Do not begin until that proposal's Steps 1–3 are delivered.

## The ask, once unblocked

Pick **one** of `Tikhonov.lean`'s `tikhonovShrinkage`/`tikhonovMinimizer`
family or `Heat.lean`'s `heatKernel`, and prove it equals the general
calculus wrapper applied to the corresponding scalar function
(`π ↦ π/(λ+π)` for Tikhonov, `t ↦ e^{-tλ}` for heat) — an equality
theorem, not a restatement. This is the bridge's actual falsifiability
test at a real consumer: a wrong calculus specialization contradicts an
already-proved, independently-delivered definition.

Pick the one with the smaller reconciliation gap between its own proof
route and the calculus's unitary-diagonalization route — Step 0 of the
parent proposal should note which, if either, is obviously cheaper;
otherwise decide at the start of this proposal's own (future) Step 0.

## Explicit non-goals

Do not attempt both Tikhonov and Heat in one delivery — pick one,
finish it, and this document (or a sibling) covers the other as its own
separately-authorized follow-on. Do not restate this as "the calculus
generalizes Tikhonov/Heat" — the existing modules stay as delivered;
this is an equality theorem bridging them to the new interface, additive
only.

## Companion

[Hermitian Functional-Calculus Bridge](hermitian-functional-calculus-bridge.md)
(the gate), [Tikhonov Shrinkage Filter](tikhonov-shrinkage-filter.md),
[Reversibility and Heat Semigroup](reversibility-and-heat-semigroup.md).
