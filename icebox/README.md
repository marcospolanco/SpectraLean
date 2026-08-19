# Icebox

This directory holds technical findings and mini-proposals that are real,
scoped, and potentially valuable, but that this project has explicitly
decided **not** to pursue right now — distinct from both other archival
locations in this repository:

- `proposals/` — active work, indexed with a priority in
  `proposals/README.md`. Something here is not that: it has no priority,
  and an autonomous run should never pick it up on its own.
- `research/archive/` — historical provenance record, not to be edited
  except archive metadata, preserving what was true at some past point.
  Something here is not that either: it is a current, standing technical
  assessment, kept up to date if the landscape changes (e.g. if the pinned
  Mathlib later adds the missing machinery).

An icebox entry exists because someone did real investigative work —
surveyed the pinned Mathlib, worked out why something is hard, named the
actual paths forward — and that work is worth keeping findable rather than
losing it to conversation history, even though nobody is committing to act
on it now. If a future proposal wants to pursue one of these, promote it to
`proposals/` and cite the icebox entry as its survey groundwork rather than
re-deriving it.

## Contents

- [Matrix Chernoff / Golden–Thompson Formalization Gap](matrix-chernoff-formalization-gap.md)
  — why `proposals/spectral-graph-sparsification.md`'s Phase B is blocked,
  in full technical detail; the proposal itself carries only the summary.
- [Lyapunov Stability Formalization Gap](lyapunov-stability-formalization-gap.md)
  — why Lyapunov stability has no proposal despite being well-established
  math: neither Scaffold nor the pinned Mathlib has any ODE-trajectory or
  derivative-along-a-curve infrastructure to state it in terms of. The
  discrete/spectral content anyone citing "Lyapunov" likely wants is
  already a free corollary of `proposals/reversibility-and-heat-semigroup.md`.
- [Stochastic Calculus and Log-Sobolev Formalization Gap](stochastic-calculus-and-log-sobolev-gap.md)
  — why the two hard pieces of backlog item 6 (continuous-time
  noisy/stochastic dynamics, and log-Sobolev inequalities beyond the
  already-available Poincaré/spectral-gap bound) stay off the active list:
  both are entirely absent from the pinned Mathlib, and log-Sobolev
  additionally has no comparison theorem to build from even once
  `proposals/finite-relative-entropy.md`'s entropy functional exists.
- [Non-Mathlib Lean Dependencies](external-lean-dependencies.md) — what
  exists elsewhere on GitHub for the machinery named absent in the three
  entries above (real repos for Matrix-Tree and Lieb's concavity turn up),
  and why consuming one is a governance decision this project has never
  made and has no process for, not a `lakefile.lean` one-liner.
