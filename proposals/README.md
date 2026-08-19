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
| High | [Foster's Theorem](spectral-graph-sparsification.md) (Phase A only) | Reviewed and split 2026-08-18 from a bundled proposal that also claimed a full Spielman–Srivastava sparsification result — see that document's "Correction" for why only this half is ready. Foster's theorem was explicitly removed from `electrical-structure-crust.md`'s program for needing a pseudoinverse trace identity; the removal stands, but a genuine pseudoinverse-free route now exists (eigenbasis expansion + the now-proved one-dimensional kernel characterization, reusing exactly today's Courant–Fischer-era machinery), which is why this reopens the decision rather than quietly reversing it. Zero new axioms if the eigenbasis route holds up. |
| High | [Decidable Spectral Certificates and the Expander Mixing Lemma](decidable-spectral-certificates.md) | Upgraded from Medium 2026-08-18. Its certificate-soundness proof is a checked-by-hand load-bearing consumer of `lambda2_variational` (proved the same day) — closes the exact noncomputable-extraction gap `docs/traction-plan.md` names as the reason broader-audience outreach stays premature, so strategically bigger than a typical proof target. **Run Step 0 first**: the proposal shipped without resolving the adjacency-vs-Laplacian eigenvalue convention the classical Expander Mixing Lemma needs, or spiking whether kernel `decide` on ℚ arithmetic is actually fast enough at even modest `Fin n` sizes to satisfy its own acceptance criterion. Both are now scoped in the proposal's own Step 0 — do not begin Step 1 before that decision and spike are recorded. |
| Medium | [The Fiedler Vector and a Certified Spectral Partition](fiedler-partitioning.md) | Phase A (A1/A2) delivered 2026-08-18 as hard crust (`GraphTheory.Fiedler`: the vector, the algebraic-connectivity certificate `lambda2_pos_of_connected`, and the sign partition proved nonempty/proper; no new axioms). What remains is Phase B — a certified conductance bound on the Fiedler partition — which is *not* hard crust: it composes the proved easy direction with the still-admitted Cheeger hard direction, so it is an axiom-backed derived theorem. Real, unblocked work, but it needs the operator decision the proposal itself names (run against the admitted hard direction, or defer until it is proved) and adds trust surface rather than reducing it — hence Medium, not High. |
| Medium | [A Spectral Mixing-Time Bound](mixing-time-bound.md) | Step 1 (eigenvalue transfer via the already-proved similarity identity) is reachable now, but the program's own calibration section rates the full bound as "at least as hard as the electrical program's solvability step" — real, unblocked work, but bigger and riskier than the High items. |
| Medium | [Reversibility and the Heat Semigroup](reversibility-and-heat-semigroup.md) (Phase A only — reversibility/detailed balance) | Added 2026-08-18, closing the two items `docs/7_SGT_RADAR.md` axis 5 names as absent that `mixing-time-bound.md` does not already claim (heat kernels, reversibility). Phase A's own backlog gate (item 6, "gated on item 1-2 stability") is already open — items 1-2 are recorded delivered — so this is unblocked, cheap (composes existing `Stationary`/`Normalized` lemmas), zero new axioms. |
| Low — process decision required | [Reversibility and the Heat Semigroup](reversibility-and-heat-semigroup.md) (Phase B only — the heat semigroup `e^{-tL}`) | Backlog item 5 ("graph-dynamical systems") gates admission on a named SGT consumer; the proposal names itself as one but, per this table's own convention, an autonomous run should not treat that as self-authorizing. Otherwise cheap and axiom-free — Mathlib's matrix-exponential API (`IsSymm.exp`, `exp_add_of_commute`) plus Scaffold's already-proved eigenbasis machinery cover every step, and unlike the mixing-time program it does not depend on the still-open walk-eigenvalue-transfer gap. |
| Medium | [Relative Entropy and Shannon Entropy for Finite Distributions](finite-relative-entropy.md) | Added 2026-08-18, closing the entropy half of backlog item 6 (the reversibility half is `reversibility-and-heat-semigroup.md` Phase A, above); that item's own gate ("gated on item 1-2 stability") is already open. Cheap and axiom-free — Gibbs' inequality and the entropy maximum bound are direct corollaries of Mathlib's already-proved `strictConcaveOn_log_Ioi` plus its general finite Jensen-inequality lemmas, no measure theory needed. Has a real named consumer on record: `docs/3_SPECTRAL_THEORY.md`'s retained (not active) x90 pipeline names an undefined "spectral entropy H(t)" this would give a real definition to, though reviving that pipeline is explicitly out of this proposal's scope. |
| Low — technical decision required | [Spielman–Srivastava Sparsification](spectral-graph-sparsification.md) (Phase B only — Foster's theorem, Phase A, is the separate High item above) | Not the "Medium" this row previously said — reviewed 2026-08-18 and found to cite a theorem, `Scaffold.Probability.Concentration.MatrixChernoff.matrix_chernoff_upper_lower`, that does not exist anywhere in this repository; `sampledLaplacian` is likewise undefined. This is not a citation fix — the entire sparsification guarantee currently rests on nothing. Three real paths forward are named in the proposal's own "Correction": survey whether the existing `matrix_bernstein` axiom's hypotheses can actually supply what's needed, admit a new carefully-scoped matrix-Chernoff axiom with its own leverage case, or attempt a from-scratch proof (likely needing Lieb's concavity theorem or Golden–Thompson, neither remotely available). None of the three is a routine Lean-implementation decision; an autonomous run should not begin any Phase B work under this proposal until one is chosen. |
| Low — human decision required | [Clean-Room SGT Export](clean-room-sgt-export.md) | Needs patent counsel sign-off before any phase starts. Potentially the highest-leverage item in this directory overall, but not one an autonomous Lean-work run can act on. |
| Low — human decision required | [Get Outside Signal](get-outside-signal.md) | Phase 0 is explicitly "outside this document's authority" — gated on the same counsel sign-off as the export. |
| Low — human decision required | [Sell the Methodology](sell-the-methodology.md) | Gated on the export existing and, per its own text, likely a *stricter* clean-room pass than the code export. |
| Low — human decision required | [A Discovery-Layer MCP Server](discovery-mcp-server.md) | Phase 0 is explicitly outside this document's authority; Phase 1 has nothing to point at until the export is tagged. |
| Low — scope decision required | [Admit Perron–Frobenius for Irreducible Nonnegative Matrices](admit-perron-frobenius.md) | Different gate than the counsel items above: this is a *strategic* scope-expansion decision, not an external sign-off. Every existing backlog item and radar axis is scoped to undirected graphs; this proposal explicitly names itself as opening a new axis (directed graphs / general Markov chains) that `docs/1_STRATEGY.md`'s center-out policy does not currently cover. The proposal's own acceptance criteria require that decision resolved, adopted or declined, before any Lean work starts — an autonomous run should not treat this as routine backlog and should not start it without that decision on record. |
| Low — technical decision required | [The Weighted Matrix-Tree (Kirchhoff) Theorem](weighted-matrix-tree-theorem.md) | Added 2026-08-19 as the answer to "if we build one more piece of genuinely new machinery, what should it be" — compared explicitly against `icebox/`'s three candidates (Golden-Thompson, ODE-trajectory calculus, stochastic calculus) and judged the best fit for this project's idiom (finite determinants and graph induction, not a foreign kind of math) and its most active axis (6). Not self-authorizing: `docs/6_SGT_BACKLOG.md` item 7 already names this exact candidate and gates it explicitly — "admit or define nothing here until a named consumer states which identity it needs" — and this proposal does not supply one. Does **not** accelerate or feed Foster's theorem (`spectral-graph-sparsification.md` Phase A already has its own pseudoinverse-free route); the document is explicit about not overstating that connection. |
| Low — process decision required | [Retire the Mushy Center Systematically](retire-the-mushy-center.md) | Found unindexed while auditing this table (2026-08-18) — added by the same run that delivered the Cheeger easy direction, never previously recorded here. Proposes a heavier apparatus for axiom retirement: a formal elimination board, parallel per-candidate worktrees, a four-stage survey/formalize/falsify/integrate workflow. Worth an honest tension check before adoption: its own pilot section names the normalized-Cheeger transfer as its first candidate, and that has *already been delivered* using the lightweight mechanism already in place (this table plus one-step-per-run) — four axiom-related deliveries landed that way in short order. Whether the heavier process is worth adopting over what's already working is an operator call, not a default; an autonomous run should not stand up the board unprompted. |

With the electrical-flow proposal indexed, it is the active High item and
therefore the next autonomous milestone under the priority policy above.
**Progress (2026-08-19):** its step 0 is delivered — the representation
survey re-run against the pin (no flow/circulation/graph-divergence API
anywhere; `SimpleGraph.Dart` carries none) with the matrix representation,
zero-edge semantics, and the focused `GraphTheory.ElectricalFlow` module
recorded in the proposal before any Lean — and step 1 (the flow interface
and Kirchhoff conservation, `isUnitFlow_electricalCurrent`) landed the same
run at no axiom cost. **Step 2 (flow energy and the energy agreement) was
delivered 2026-08-19 in a follow-up run:** `flowEnergy` with the explicit
zero branch and the `1/2` ordered-pair factor, the symmetry-only agreement
`flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`,
`flowEnergy_nonneg`, and the unit-demand identity equating the current's
dissipated energy with the effective resistance it routes — zero axioms
added, with the mandatory double-counting fixture (raw ordered-pair sum
`2 ≠ 1` = Dirichlet energy on `K₂`) and the Thomson-breaking zero-energy
competitor (energy `0 < 1` = resistance, excluded by the support conjunct
alone) both landed in QA. **Step 3 (Thomson's principle) was delivered
2026-08-19 in a third run:** `effectiveResistance_le_flowEnergy` — every
valid unit flow dissipates at least the resistance it routes — proved via
the divergence-free superposition lemma
`flowEnergy_add_of_flowDivergence_eq_zero` (discrete integration by
parts; stated with no hypotheses on `A`), flow-space linearity, and
`flowEnergy_nonneg`; QA witnesses attainment at the split current on the
triangle (`2/3`), a strict competitor (the detour flow: `2/3 < 2`), and
the decomposition `2 = 2/3 + 4/3`. **Step 4 (Rayleigh monotonicity in
conductance form) was delivered 2026-08-19 in a fourth run:**
`effectiveResistance_le_of_le` — entrywise `A ≤ B` on connected symmetric
nonnegative networks gives `R_B ≤ R_A` — via the flow-space-growth and
energy-comparison interfaces (`isFlowOn_of_le`, `flowEnergy_le_of_le`,
support load-bearing in both), Thomson on `B` at the transferred
`A`-current, and the step-2 energy identity; QA delivers the proposal's
capacity-increase item (`1 → 1/2`, strict, with the orientation guard
refuting the reverse direction) plus a partial increase on the triangle
(`2/3 → 2/5`); zero axioms. The next run's milestone is step 5 (the ICP
capacity-reinforcement example — packaging the monotonicity theorem as
`effectiveResistance (increaseConductance A i j δ) u v ≤
effectiveResistance A u v`; the optional connectivity adapter noted in the
step-4 record belongs there if that shape wants it). Fiedler Phase B
retains its named operator decision, and the mixing-time program remains
the unblocked Medium fallback.

## Delivered

| Proposal | Delivered | Result |
| --- | --- | --- |
| Cauchy interlacing retirement (`eigen_interlacing_principal_submatrix`, no dedicated proposal file — the min–max proposal's first named consumer) | 2026-08-18 | `eigen_interlacing_principal_submatrix` proved from the locally built Courant–Fischer engine (14 → 13 axioms) — the first SGT-center retirement, and the engine's first named consumer as `prove-courant-fischer.md` itself anticipated. The interlacing window is pinned numerically in QA. See the delivery note in `prove-courant-fischer.md` for the route. |
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
