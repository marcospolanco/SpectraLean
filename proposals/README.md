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
| High | [Prove General Courant–Fischer Min-Max](prove-courant-fischer.md) | The largest-surface-area *proof* candidate currently identified — reuses only already-proved eigenbasis algebra from `Spectral.lean` (no new Mathlib bridge, unlike the original `lambda2_variational` sketch) plus one standard dimension-counting lemma to survey for. Names four separate downstream consumers as potential follow-ons: `eigen_interlacing_principal_submatrix`, full Rayleigh monotonicity, the Cheeger hard direction, and transitively `fiedler-partitioning.md` Phase B. |
| Medium | [The Fiedler Vector and a Certified Spectral Partition](fiedler-partitioning.md) | Phase A (A1/A2) delivered 2026-08-18 as hard crust (`GraphTheory.Fiedler`: the vector, the algebraic-connectivity certificate `lambda2_pos_of_connected`, and the sign partition proved nonempty/proper; no new axioms). What remains is Phase B — a certified conductance bound on the Fiedler partition — which is *not* hard crust: it composes the proved easy direction with the still-admitted Cheeger hard direction, so it is an axiom-backed derived theorem. Real, unblocked work, but it needs the operator decision the proposal itself names (run against the admitted hard direction, or defer until it is proved) and adds trust surface rather than reducing it — hence Medium, not High. |
| Medium | [A Spectral Mixing-Time Bound](mixing-time-bound.md) | Step 1 (eigenvalue transfer via the already-proved similarity identity) is reachable now, but the program's own calibration section rates the full bound as "at least as hard as the electrical program's solvability step" — real, unblocked work, but bigger and riskier than the High items. |
| Medium | [Derive and Retire the Sherman–Morrison Axiom](retire-sherman-morrison.md) | Woodbury's rank-one special case — already stated *correctly* (verified against the corrected Woodbury shape), so no correctness urgency, just a cheap proof now that the Woodbury repair has landed (2026-08-18): same Mathlib machinery, no API migration needed, and the retired-Woodbury QA file (`MatrixUpdates_QA`) already provides the 1×1/2×2 inverse-computation scaffolding its QA would reuse. The cheapest axiom retirement in the backlog, but sequenced after Woodbury rather than standing on its own leverage — hence Medium. |
| Low — human decision required | [Clean-Room SGT Export](clean-room-sgt-export.md) | Needs patent counsel sign-off before any phase starts. Potentially the highest-leverage item in this directory overall, but not one an autonomous Lean-work run can act on. |
| Low — human decision required | [Get Outside Signal](get-outside-signal.md) | Phase 0 is explicitly "outside this document's authority" — gated on the same counsel sign-off as the export. |
| Low — human decision required | [Sell the Methodology](sell-the-methodology.md) | Gated on the export existing and, per its own text, likely a *stricter* clean-room pass than the code export. |
| Low — human decision required | [A Discovery-Layer MCP Server](discovery-mcp-server.md) | Phase 0 is explicitly outside this document's authority; Phase 1 has nothing to point at until the export is tagged. |
| Low — scope decision required | [Admit Perron–Frobenius for Irreducible Nonnegative Matrices](admit-perron-frobenius.md) | Different gate than the counsel items above: this is a *strategic* scope-expansion decision, not an external sign-off. Every existing backlog item and radar axis is scoped to undirected graphs; this proposal explicitly names itself as opening a new axis (directed graphs / general Markov chains) that `docs/1_STRATEGY.md`'s center-out policy does not currently cover. The proposal's own acceptance criteria require that decision resolved, adopted or declined, before any Lean work starts — an autonomous run should not treat this as routine backlog and should not start it without that decision on record. |

## Delivered

| Proposal | Delivered | Result |
| --- | --- | --- |
| [Repair and Retire the Woodbury Identity Axiom](repair-and-retire-woodbury.md) | 2026-08-18 | The verified-false admitted axiom retired to a proved theorem at the same name (16 → 15 axioms), an emergency correctness repair per architecture §9. Statement migrated to the standard middle factor `C⁻¹ + V A⁻¹ U` with exactly the three `IsUnit` determinant hypotheses (the sum's invertibility now derived); proved from Mathlib's `Matrix.invOf_add_mul_mul` plus the `NonsingularInverse` bridges — zero local proof cost, zero new axioms. The old scalar shape is refuted in QA *with its hypotheses proved satisfied* at the counterexample, and the corrected `IsUnit C.det` hypothesis is proved to exclude it. Zero consumers existed, so no migration surface; no deprecated compatibility declaration (it must not restate the false identity). |
| [Prove One Named Inequality](prove-cheeger-easy-direction.md) | 2026-08-18 | The easy direction of Cheeger (`cheeger_upper_bound`, `λ₂(L_sym) ≤ 2φ`) retired from axiom to proved theorem (17 → 16). Route: the `lambda2_variational` argument generalized to any symmetric PSD matrix with `onesVec` in its kernel (`secondEval_variational`), consumed through the new `secondEval_le_rayleigh` at the volume-centered cut indicator. The remaining Cheeger axiom is the hard direction only. Residuals named in the proposal file: the irregular-graph generalization (the proposal's "forces" item) and the supporting moves (meta-work freeze, one Mathlib PR) are not delivered by this retirement. |
| [Grow the Crust Through Electrical Structure](electrical-structure-crust.md) | 2026-08-18 | All six steps landed. `GraphTheory.Electrical` — effective resistance, existence, uniqueness, the energy identity, and the one-sided Dirichlet bound — all proved, zero new axioms. Axiom count held at 18 throughout the program. |
| [Prove λ₂'s Variational Characterization](prove-lambda2-variational.md) | 2026-08-18 | `lambda2_variational` retired as an axiom (18 → 17). Delivered for the combinatorial Laplacian instance; the normalized-Laplacian instance `prove-cheeger-easy-direction.md` needs is a named remaining step, not yet written — see that proposal's updated priority above. |
| [Sustained Autonomous Scaffold Pursuit](sustained-autonomous-pursuit.md) | 2026-08-17 | The adopted design behind `scripts/opencode-pursue`, `AGENTS.md`, and `scripts/README.md` — foundational to how every other proposal in this directory gets executed, not itself an SGT math proposal. |

## Retired

| Proposal | Disposition |
| --- | --- |
| `gem-eng-use-cases.md` (root, never tracked) → `eng-use-cases.md` | Corrected once (proved/admitted tagging added, fabricated quantum persona removed), then judged unnecessary as a standalone document — useful content integrated into `docs/traction-plan.md` (release-readiness proof example, audience narrowing, and the recorded reason broader engineering personas were set aside). File removed. |
