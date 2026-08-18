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
- one short, useful proof example;
- generated API documentation; and
- an explicit table separating proved declarations from assumptions.

## Initial audience

Start with Lean and Mathlib contributors who need reusable interfaces for
graph Laplacians, random walks, normalized Laplacians, cuts, or stationary
distributions. Lead with a concrete integration problem rather than a general
claim about formalizing spectral graph theory.

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
