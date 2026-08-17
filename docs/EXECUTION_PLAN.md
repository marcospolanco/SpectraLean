# Execution plan

This is the compact, current-state ledger for sustained autonomous work. It is
updated at milestone boundaries; [`AGENT_ACTIVITY.md`](AGENT_ACTIVITY.md)
holds the append-only narrative.

## Active milestone

**Recover the probability/concentration bridge for SGT.** The current SGT
center, perturbation bridge, and dynamic-persistence frontier compile through
the `Scaffold` umbrella. The excluded concentration modules now form the
nearest load-bearing gap between that frontier and event-stream guarantees.

**Next action:** inventory direct elaboration failures in
`Scaffold/Mathlib/Probability/Concentration/`, repair the smallest coherent
syntax/type/API slice, and build its closest QA consumer before expanding the
umbrella.

## Ready queue

1. Repair malformed concentration-module syntax and define or correctly
   import the `RV` and `Independent` interfaces required by the first slice.
2. Add a source citation and index entry for `matrix_azuma_hoeffding`, then
   certify its QA after the module compiles.
3. Review page-level locators for Horn--Johnson and Chung; tighten explicit
   projector/eigenbasis assumptions where possible.
4. Restore the concentration bridge to the umbrella only after direct module
   and QA checks pass.

## Last verified state

- `lake build` completed successfully on 2026-08-17 for the current
  `Scaffold` umbrella.
- The SGT and perturbation QA slice contains 47 declarations and no live
  `sorry` or `admit`.
- Probability/concentration modules remain excluded and uncertified; see the
  QA scoreboard and the latest activity entry for exact evidence.

## Blockers

- The native Mathlib cache executable fails on this macOS environment with a
  dyld segment error. Cached artifacts were obtained through the recorded Lean
  interpreter workaround; this is environment debt, not an SGT source failure.
