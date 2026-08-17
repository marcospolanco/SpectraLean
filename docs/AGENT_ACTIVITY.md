# Agent activity

This is an append-only, operator-facing journal of autonomous work. Entries
record intentions, material decisions, verification, and the next handoff;
they are summaries, not model transcripts.

## 2026-08-17 — SGT center reaches a clean default build

**Status:** completed  
**Milestone:** Restore honest build reachability for the spectral graph theory
(SGT) center, its perturbation bridge, and its dynamic-persistence frontier.

The library target no longer points at the nonexistent `Main.lean`; `lake
build` now compiles the `Scaffold` umbrella successfully. To make that result
meaningful, the SGT surface was rebuilt around real sorted-spectrum,
Laplacian, projector, and update definitions, with proved basic identities
and QA. Classical results not yet formalized remain visible as cited axioms,
rather than hidden placeholders.

The repaired bridge covers Cheeger, Weyl, Davis--Kahan, dynamics, matrix
updates, and norms. QA now has 47 declarations and no live `sorry` or
`admit`; it exposed and corrected a missing no-self-loop hypothesis in the
Laplacian-trace statement. Citation and Markdown checks were repaired so they
respect ordinary source-comment placement and ignore vendored dependencies.

**Verification:** `lake build` completed successfully. Mathlib artifacts were
bootstrapped through the Lean interpreter after the native cache executable
hit a local macOS dyld failure; the workaround and its provenance are recorded
in the QA scoreboard.

**Trust boundary:** the SGT/bridge public API retains explicit cited axioms
for Cauchy interlacing, the variational characterization of `lambda2`,
Cheeger bounds, Weyl, Davis--Kahan, persistence, and matrix-update identities.
Their consequences are checked; the axioms themselves are not claimed as
foundationally proved.

**Next handoff:** repair the excluded probability/concentration modules,
starting with malformed syntax and undefined `RV`/`Independent`, then add the
missing citation for `matrix_azuma_hoeffding`. Separately, review page-level
locators for Horn--Johnson and Chung and reduce the remaining admitted
projector/eigenbasis interfaces.
