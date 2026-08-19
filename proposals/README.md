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
| High | [Electrical Flows, Thomson's Principle, and Rayleigh Monotonicity](electrical-flow-routing.md) | The strongest zero-axiom center-to-ICP bridge: turns the delivered potential-based resistance API into a conserved unit-flow routing interface, proves the minimum-energy characterization, and derives the capacity-monotonicity theorem the traction plan can demonstrate to Lean/Mathlib adopters. Load-bearing on the Laplacian sign convention, support, solvability, kernel uniqueness, energy identity, and effective-resistance agreement; no new axioms. |
| Medium | [The Fiedler Vector and a Certified Spectral Partition](fiedler-partitioning.md) | Phase A (A1/A2) delivered 2026-08-18 as hard crust (`GraphTheory.Fiedler`: the vector, the algebraic-connectivity certificate `lambda2_pos_of_connected`, and the sign partition proved nonempty/proper; no new axioms). What remains is Phase B — a certified conductance bound on the Fiedler partition — which is *not* hard crust: it composes the proved easy direction with the still-admitted Cheeger hard direction, so it is an axiom-backed derived theorem. Real, unblocked work, but it needs the operator decision the proposal itself names (run against the admitted hard direction, or defer until it is proved) and adds trust surface rather than reducing it — hence Medium, not High. |
| Medium | [A Spectral Mixing-Time Bound](mixing-time-bound.md) | Step 1 (eigenvalue transfer via the already-proved similarity identity) is reachable now, but the program's own calibration section rates the full bound as "at least as hard as the electrical program's solvability step" — real, unblocked work, but bigger and riskier than the High items. |
| Low — human decision required | [Clean-Room SGT Export](clean-room-sgt-export.md) | Needs patent counsel sign-off before any phase starts. Potentially the highest-leverage item in this directory overall, but not one an autonomous Lean-work run can act on. |
| Low — human decision required | [Get Outside Signal](get-outside-signal.md) | Phase 0 is explicitly "outside this document's authority" — gated on the same counsel sign-off as the export. |
| Low — human decision required | [Sell the Methodology](sell-the-methodology.md) | Gated on the export existing and, per its own text, likely a *stricter* clean-room pass than the code export. |
| Low — human decision required | [A Discovery-Layer MCP Server](discovery-mcp-server.md) | Phase 0 is explicitly outside this document's authority; Phase 1 has nothing to point at until the export is tagged. |
| Low — scope decision required | [Admit Perron–Frobenius for Irreducible Nonnegative Matrices](admit-perron-frobenius.md) | Different gate than the counsel items above: this is a *strategic* scope-expansion decision, not an external sign-off. Every existing backlog item and radar axis is scoped to undirected graphs; this proposal explicitly names itself as opening a new axis (directed graphs / general Markov chains) that `docs/1_STRATEGY.md`'s center-out policy does not currently cover. The proposal's own acceptance criteria require that decision resolved, adopted or declined, before any Lean work starts — an autonomous run should not treat this as routine backlog and should not start it without that decision on record. |
| Low — process decision required | [Retire the Mushy Center Systematically](retire-the-mushy-center.md) | Found unindexed while auditing this table (2026-08-18) — added by the same run that delivered the Cheeger easy direction, never previously recorded here. Proposes a heavier apparatus for axiom retirement: a formal elimination board, parallel per-candidate worktrees, a four-stage survey/formalize/falsify/integrate workflow. Worth an honest tension check before adoption: its own pilot section names the normalized-Cheeger transfer as its first candidate, and that has *already been delivered* using the lightweight mechanism already in place (this table plus one-step-per-run) — four axiom-related deliveries landed that way in short order. Whether the heavier process is worth adopting over what's already working is an operator call, not a default; an autonomous run should not stand up the board unprompted. |

With the electrical-flow proposal indexed, it is the active High item and
therefore the next autonomous milestone under the priority policy above. Its
step 0 is a representation/Mathlib survey; no Lean implementation begins until
that decision is recorded. Fiedler Phase B retains its named operator decision,
and the mixing-time program remains the unblocked Medium fallback.

(Recorded 2026-08-18, later the same day: the interlacing retirement — the
min–max proposal's first named consumer — was delivered between table edits:
`eigen_interlacing_principal_submatrix` proved from the Courant–Fischer
engine, axioms 14 → 13, with the window pinned numerically in QA. See the
delivery note in `prove-courant-fischer.md`.)

## Delivered

| Proposal | Delivered | Result |
| --- | --- | --- |
| [Derive and Retire the Sherman–Morrison Axiom](retire-sherman-morrison.md) | 2026-08-18 | The `sherman_morrison` axiom retired to a proved theorem at unchanged name, hypotheses, and statement (15 → 14 axioms) — a **pure proof task, not a correctness repair** (the proposal's own pre-check verified the statement correct against the corrected Woodbury shape; the `C`/`C⁻¹` defect is invisible at rank one). Route as proposed: the `k = Fin 1` specialization of the proved `woodbury_identity` — `Fin 1` column/row packing, the 1×1 middle factor with entry `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)` (`Fin.sum_univ_one` computation), unit determinant from `hv` through `Matrix.det_fin_one`, the 1×1 scalar inverse through `Matrix.inv_eq_left_inv`, and the pin's `mul_smul`/`smul_mul` reshaping. Load-bearing on the Woodbury repair. QA (+4 in `MatrixUpdates_QA`): adjugate-independent positive instance at `diag 2 2` + all-ones (`!![3/8,-1/8;-1/8,3/8]`, denominator computed to `1`), and the excluded-denominator negative witness (`v ⬝ᵥ (A⁻¹ *ᵥ u) = -1` attained at a `Fin 1` fixture where the update is the singular zero matrix). |
| [Prove General Courant–Fischer Min-Max](prove-courant-fischer.md) | 2026-08-18 | The `k`-th sorted eigenvalue of any real symmetric matrix characterized at every index, pure hard crust (axiom count stays 15 — general min–max was never admitted): the two witness directions (`exists_submodule_forall_rayleigh_le`, `exists_ne_mem_rayleigh_ge_of_finrank_eq`) and the packaged infimum equation `evals_min_max`, all symmetry-only, proved through the existing eigenbasis algebra plus the pin's dimension-intersection lemma (the proposal's open survey step resolved affirmatively first). New public center API: general-`k` multiplicity pins and component-form Rayleigh bounds. QA (33 declarations): pinned spectra, both directions instantiated (incl. the derived top-eigenvalue-domination universal and exact attainment), and negative witnesses (wrong subspace refuted; dimension hypothesis load-bearing; interior-index wrong subspace refuted on the path Laplacian with cross-engine agreement). The four named consumers (interlacing, Rayleigh monotonicity, Cheeger hard direction, Fiedler Phase B) remain open follow-ons, as the proposal itself requires. |
| [Repair and Retire the Woodbury Identity Axiom](repair-and-retire-woodbury.md) | 2026-08-18 | The verified-false admitted axiom retired to a proved theorem at the same name (16 → 15 axioms), an emergency correctness repair per architecture §9. Statement migrated to the standard middle factor `C⁻¹ + V A⁻¹ U` with exactly the three `IsUnit` determinant hypotheses (the sum's invertibility now derived); proved from Mathlib's `Matrix.invOf_add_mul_mul` plus the `NonsingularInverse` bridges — zero local proof cost, zero new axioms. The old scalar shape is refuted in QA *with its hypotheses proved satisfied* at the counterexample, and the corrected `IsUnit C.det` hypothesis is proved to exclude it. Zero consumers existed, so no migration surface; no deprecated compatibility declaration (it must not restate the false identity). |
| [Prove One Named Inequality](prove-cheeger-easy-direction.md) | 2026-08-18 | The easy direction of Cheeger (`cheeger_upper_bound`, `λ₂(L_sym) ≤ 2φ`) retired from axiom to proved theorem (17 → 16). Route: the `lambda2_variational` argument generalized to any symmetric PSD matrix with `onesVec` in its kernel (`secondEval_variational`), consumed through the new `secondEval_le_rayleigh` at the volume-centered cut indicator. The remaining Cheeger axiom is the hard direction only. Residuals named in the proposal file: the irregular-graph generalization (the proposal's "forces" item) and the supporting moves (meta-work freeze, one Mathlib PR) are not delivered by this retirement. |
| [Grow the Crust Through Electrical Structure](electrical-structure-crust.md) | 2026-08-18 | All six steps landed. `GraphTheory.Electrical` — effective resistance, existence, uniqueness, the energy identity, and the one-sided Dirichlet bound — all proved, zero new axioms. Axiom count held at 18 throughout the program. |
| [Prove λ₂'s Variational Characterization](prove-lambda2-variational.md) | 2026-08-18 | `lambda2_variational` retired as an axiom (18 → 17). Delivered for the combinatorial Laplacian instance; the normalized-Laplacian instance `prove-cheeger-easy-direction.md` needs is a named remaining step, not yet written — see that proposal's updated priority above. |
| [Sustained Autonomous Scaffold Pursuit](sustained-autonomous-pursuit.md) | 2026-08-17 | The adopted design behind `scripts/opencode-pursue`, `AGENTS.md`, and `scripts/README.md` — foundational to how every other proposal in this directory gets executed, not itself an SGT math proposal. |

## Retired

| Proposal | Disposition |
| --- | --- |
| `gem-eng-use-cases.md` (root, never tracked) → `eng-use-cases.md` | Corrected once (proved/admitted tagging added, fabricated quantum persona removed), then judged unnecessary as a standalone document — useful content integrated into `docs/traction-plan.md` (release-readiness proof example, audience narrowing, and the recorded reason broader engineering personas were set aside). File removed. |
