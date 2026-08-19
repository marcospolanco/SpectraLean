# Traction Plan

## Purpose

Promote the future public SGT library as a useful Lean dependency with one
clear promise, not as a broad research vision.

This plan applies only to the new clean-room repository. Do not reference this
repository, its history, persistence work, or prior application rationale in
the new project's public materials.

## Release readiness

Before announcing the first release, provide:

- a one-sentence purpose;
- a Lake installation snippet pinned to a release tag;
- three narrow imports;
- one short, useful proof example — the current best candidate is the
  electrical-structure module (effective resistance, existence,
  uniqueness, the energy identity, and the one-sided Dirichlet bound),
  proved with zero admitted axioms;
- generated API documentation; and
- an explicit table separating proved declarations from assumptions,
  generated per module (axiom count via `scripts/lint_axioms.py`), not
  asserted narratively — a module is "proved" only if that count is zero.

## Initial audience

Start with Lean and Mathlib contributors who need reusable interfaces for
graph Laplacians, random walks, normalized Laplacians, cuts, or stationary
distributions. Lead with a concrete integration problem rather than a general
claim about formalizing spectral graph theory — effective-resistance-based
routing or load-balancing analysis is the current strongest candidate,
since it is backed by a zero-axiom module end to end.

This audience is a deliberate narrowing, not an oversight: it is people who
already work inside a proof assistant and already accept an axiom-backed,
citable component as valuable — the same currency Mathlib itself trades in.
A broader "helps engineers generally" pitch (ML engineers wanting GNN
robustness bounds, distributed-systems engineers wanting mixing-time
guarantees, agent-tooling engineers wanting a training benchmark) was
assessed and set aside as premature, not merely unconsidered: every proved
result here is `noncomputable` Lean with no extraction path to a runnable
artifact, so an engineer outside a proof assistant has nothing to consume
yet. Revisit only if that extraction gap closes.

> **Note (2026-08-19, per `proposals/decidable-spectral-certificates.md`
> Acceptance Criterion 4):** the revisit precondition named above is now
> met in the source repository. The decidable-certificates program
> (steps 0–4, delivered 2026-08-19, zero new axioms) closes the
> extraction gap *inside Lean*: an external numerical solver emits an
> integer/rational test vector and bound, and Scaffold kernel-checks
> the certificate (`decide` on the integer twin, verified at `Fin 4`
> and `Fin 6` sizes) while a proved soundness theorem
> (`lambda2_le_of_certificate`) lifts the check to a verified
> `lambda2 ≤ bound` in the real spectral center — QA pins the chain
> *exactly tight* on `C₄` (the checker accepts precisely at the true
> `lambda2 = 2` and rejects every integer bound below it). This note is
> planning provenance for the revisit decision, not release material;
> the clean-room boundary above still governs what the new repository's
> public materials may say.

## Launch sequence

1. Publish a tagged release with the readiness material above.
2. Post a concise launch note in the relevant Lean Zulip discussion and open
   GitHub Discussions or issues for integration requests. The Lean community
   primarily gathers on Zulip and GitHub; see the
   [Lean community site](https://leanprover-community.github.io/).
3. Ask focused questions: which graph-native adapter is most needed, which
   theorem shape is missing, and which interfaces are suitable for upstream
   Mathlib work.
4. Propose one or two independently useful APIs upstream. A small accepted
   upstream contribution is stronger promotion than a broad announcement.
5. After an outside user adopts the library, publish a short technical note:
   the problem, API design, trust boundary, examples, and roadmap.

## Communication rules

- Describe only assurance the new repository can demonstrate.
- Never market an axiom-backed result as foundationally formalized.
- Keep all claims application-neutral and counsel-approved.
- Prefer narrow examples and stable release notes over aspirational scope.

## Measures of traction

Prioritize:

- outside imports;
- external issues and pull requests;
- downstream packages; and
- upstream adoption.

Do not treat stars as the primary measure of usefulness.
