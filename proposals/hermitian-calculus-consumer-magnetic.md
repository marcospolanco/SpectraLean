# Proposal: A Genuinely Complex Magnetic-Laplacian Calculus Consumer

**Status:** Gated stub — not authorized. This is Step 5 of
[hermitian-functional-calculus-bridge.md](hermitian-functional-calculus-bridge.md),
named there as a separate consumer per the one-shape-per-proposal
discipline. Do not begin until that proposal's Steps 1–3 are delivered
**and** the complex-Hermitian half of the calculus (not just
real-symmetric) is confirmed working by Step 0's API-split check.

## The ask, once unblocked

`Magnetic.lean`'s `magneticLaplacian_isHermitian` is already proved,
hypothesis-free, for arbitrary directed input — the shelf's first
genuinely complex Hermitian object. Pick **one** concrete function of
it as the first consumer: a magnetic heat propagator
(`f(t) = e^{-tM}`, the natural complex analogue of `Heat.lean`'s real
construction) is the most natural first choice, since it reuses the
real case's proof shape most directly. A magnetic resolvent or a
square-root/positive-part construction are named alternatives if heat
turns out costlier than expected.

Deliver: the operator via the calculus wrapper, its eigenvector action
at `magneticLaplacian`'s (complex) eigenbasis, and one QA fixture on a
small directed graph with nonzero phase, checked against a hand
computation — the same two-independent-routes discipline used
throughout this shelf.

## Explicit non-goals

Do not attempt a magnetic Cheeger inequality, a synchronization/
frustration functional, or any eigenvalue-gap statement for `M` here —
`Magnetic.lean`'s own proposal already priced these as separate,
consumer-gated follow-ons. This proposal is scoped to exhibiting one
calculus-built operator and proving it well-defined and correct, not to
new spectral-graph-theory content about directed community detection.

## Companion

[Hermitian Functional-Calculus Bridge](hermitian-functional-calculus-bridge.md)
(the gate), [The Magnetic Laplacian](magnetic-laplacian.md) (the
consumed object).
