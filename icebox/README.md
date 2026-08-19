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
