# Proposals Index

This directory holds two kinds of document: **active proposals**, each
authorizing nothing on its own until a run is directed at it, and
**delivered records**, kept in place (not archived — see each file's own
note) because live documents still cite them as evidence. This file is the
index of both, and the priority list `scripts/opencode-pursue` checks
before falling back to its own center-out judgment.

## How this is used

Before selecting a milestone, an autonomous run should check the **Active
priority** table below. If anything is marked **High**, pursue the
highest-leverage High item first. If nothing is above **Medium**, fall
back to the center-out SGT policy (`docs/1_STRATEGY.md`,
`docs/6_SGT_BACKLOG.md`) as usual. **Low** items are not a queue to work
down — they are proposals whose next step needs a human decision (counsel
sign-off, an operator choice between routes) that an autonomous Lean-work
run cannot make, so leverage-ranking them against Medium/High items would
misrepresent them as simply less urgent when they are actually blocked on
something else entirely.

Keep this table current by hand at proposal boundaries: when a proposal's
blocker resolves, when a new proposal is added, or when one is delivered
— move it to the table below rather than letting two sources of truth
drift apart.

## Active priority

| Priority | Proposal | Why |
| --- | --- | --- |
| High | [The Fiedler Vector and a Certified Spectral Partition](fiedler-partitioning.md) | Phase A (A1/A2) has no dependency on any other open proposal and was scoped as "close to free" — existence and definition compose almost entirely from already-proved eigenbasis machinery. Run this regardless of what happens elsewhere. Phase B now has a *proved* easy-direction foundation to compose with (`prove-cheeger-easy-direction.md` delivered), though it still needs the hard direction for a two-sided guarantee. |
| Medium | [A Spectral Mixing-Time Bound](mixing-time-bound.md) | Step 1 (eigenvalue transfer via the already-proved similarity identity) is reachable now, but the program's own calibration section rates the full bound as "at least as hard as the electrical program's solvability step" — real, unblocked work, but bigger and riskier than the High item. |
| Low — human decision required | [Clean-Room SGT Export](clean-room-sgt-export.md) | Needs patent counsel sign-off before any phase starts. Potentially the highest-leverage item in this directory overall, but not one an autonomous Lean-work run can act on. |
| Low — human decision required | [Get Outside Signal](get-outside-signal.md) | Phase 0 is explicitly "outside this document's authority" — gated on the same counsel sign-off as the export. |
| Low — human decision required | [Sell the Methodology](sell-the-methodology.md) | Gated on the export existing and, per its own text, likely a *stricter* clean-room pass than the code export. |
| Low — human decision required | [A Discovery-Layer MCP Server](discovery-mcp-server.md) | Phase 0 is explicitly outside this document's authority; Phase 1 has nothing to point at until the export is tagged. |

## Delivered

| Proposal | Delivered | Result |
| --- | --- | --- |
| [Prove One Named Inequality](prove-cheeger-easy-direction.md) | 2026-08-18 | The easy direction of Cheeger (`cheeger_upper_bound`, `λ₂(L_sym) ≤ 2φ`) retired from axiom to proved theorem (17 → 16). Route: the `lambda2_variational` argument generalized to any symmetric PSD matrix with `onesVec` in its kernel (`secondEval_variational`), consumed through the new `secondEval_le_rayleigh` at the volume-centered cut indicator. The remaining Cheeger axiom is the hard direction only. Residuals named in the proposal file: the irregular-graph generalization (the proposal's "forces" item) and the supporting moves (meta-work freeze, one Mathlib PR) are not delivered by this retirement. |
| [Grow the Crust Through Electrical Structure](electrical-structure-crust.md) | 2026-08-18 | All six steps landed. `GraphTheory.Electrical` — effective resistance, existence, uniqueness, the energy identity, and the one-sided Dirichlet bound — all proved, zero new axioms. Axiom count held at 18 throughout the program. |
| [Prove λ₂'s Variational Characterization](prove-lambda2-variational.md) | 2026-08-18 | `lambda2_variational` retired as an axiom (18 → 17). Delivered for the combinatorial Laplacian instance; the normalized-Laplacian instance `prove-cheeger-easy-direction.md` needs is a named remaining step, not yet written — see that proposal's updated priority above. |
| [Sustained Autonomous Scaffold Pursuit](sustained-autonomous-pursuit.md) | 2026-08-17 | The adopted design behind `scripts/opencode-pursue`, `AGENTS.md`, and `scripts/README.md` — foundational to how every other proposal in this directory gets executed, not itself an SGT math proposal. |

## Retired

| Proposal | Disposition |
| --- | --- |
| `gem-eng-use-cases.md` (root, never tracked) → `eng-use-cases.md` | Corrected once (proved/admitted tagging added, fabricated quantum persona removed), then judged unnecessary as a standalone document — useful content integrated into `docs/traction-plan.md` (release-readiness proof example, audience narrowing, and the recorded reason broader engineering personas were set aside). File removed. |
