# Agent activity

This is an append-only, operator-facing journal of autonomous work. Entries
record intentions, material decisions, verification, and the next handoff;
they are summaries, not model transcripts.

## Required format for new entries

Use a heading and metadata block in this form. `run` is the wrapper invocation
identifier; `session` is the OpenCode session ID. Obtain the timestamp with
`date -u +%Y-%m-%dT%H:%M:%SZ` and inspect the session list before the terminal
entry. If a session ID cannot be established from repository evidence, write
`unavailable` rather than inventing one.

```markdown
## 2026-08-17T12:34:56Z — Short milestone title

**Run:** `20260817T123456Z-run-1`  
**Session:** `ses_…`  
**Status:** in-progress | completed | blocked | interrupted | superseded  
**Milestone:** One-sentence objective and SGT-leverage rationale.
```

Follow the metadata with concise `Changes`, `Verification`, `Remaining risk`,
and `Next handoff` paragraphs as applicable.

## 2026-08-23T05:28:00Z — Fiedler Phase B delivered: the certified conductance cut, first consumer of the Cheeger retirement; the proposal complete

**Run:** `20260823T044903Z-run-1`  
**Session:** `ses_fd30cfa3effedhPliQNP3CHfHI`  
**Status:** completed  
**Milestone:** `proposals/fiedler-partitioning.md` Phase B — **the certified conductance cut, delivered as pure hard crust, zero new axioms (count stays 9)** — the first load-bearing consumer of the previous run's `cheeger_lower_bound`/`cheeger_sweep` retirement. The proposal's recorded operator gate ("run Phase B against the admitted Cheeger hard direction, or defer until it is proved") was **dissolved by the retirement itself**: the deferral option completed, so the run composed proved theorems only, adding no trust surface. The proposal is now COMPLETE (Phase A 2026-08-18, Phase B 2026-08-23).

**Changes:** `GraphTheory.Cheeger` — `cheegerConstant_attained` (the conductance `sInf` realized as a minimum by `Finset.exists_min_image` over the filtered powerset of nonempty proper subsets, no regularity hypothesis: the finiteness step converting Cheeger's inequality-about-an-infimum into a statement about an actual cut). `GraphTheory.Fiedler` (new Phase B section, importing `Cheeger`) — `fiedlerVector_rayleigh_regularNormalizedLaplacian` (`R_{L_sym}(f) = lambda2 / d`) and the headline `cheeger_cut_existence`: on every connected `d`-regular graph, `∃ S` nonempty proper with `conductance S ^ 2 ≤ 2 · lambda2 / d` — the classical Cheeger cut-existence corollary. **Statement-shape deviation recorded before stating** (proposal + module docstring): the sketch's sign-partition bound is not certifiable from the Cheeger inequalities (they bound the conductance *minimum*; no λ₂-only bound on the sign half-space holds in general); the certified object is the minimizer, and the swept-level-set extraction is the named strengthening follow-on. QA `Fiedler_QA` 57 → 65 (1457 total), on the K₂ fixture: `cheegerConstant (K₂) = 1` pinned both directions (every nonempty proper cut on `Fin 2` identified as a singleton by the card count); attainment instantiated; the Rayleigh transfer cross-checked against the independently pinned `lambda2 (K₂) = 2`; the certified cut identified with its bound theorem-sourced and displayed as `1 ≤ 4`; connectivity proved to hold; and the regularity refutation — the `hd`-dropped form at `d = 100` demands `1 ≤ 1/25`, false. Records: the proposal (status header COMPLETE, gate-dissolution record, Phase B delivery record), `proposals/README.md` (Medium row → Delivered; progress paragraph), README (1457, proved list, module table), radar (axis 4 **held at 4.5** per protocol — composition within the counted Cheeger family plus a finiteness attainment lemma, with the absent list updated: the swept-level-set certificate is the new named gap; QA axis synced 1457/39, held), scoreboard (both Direct rows, `lake build`, lint, new interpretation bullet), backlog item 4, SGT index map (+3 rows), Chung source index (corollary row), the execution plan, this log.

**Decisive commands and outcomes:** spike first (`wip/fiedlerB_spike.lean` green, all `#print axioms` the standard three) then transfer; `lake env lean` on `Cheeger.lean` (only the documented pre-existing `unusedSectionVars` warning) and `Fiedler.lean` (zero errors, zero warnings) and `Fiedler_QA.lean` (zero errors, zero warnings); explicit `lake build` targets ✔; `#print axioms` via `wip/fiedlerB_axcheck{,2}.lean` on the three public and eight QA headline declarations — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2250 targets, "Build completed successfully")**; `lint_axioms` (9, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1457/9/0**, idempotent. Pin-specific notes for the record: `le_div_iff₀` (not `div_le_iff₀`) matches the conclusion-side `/ d`; `inv_mul_eq_div` closes the `d⁻¹ * λ₂ = λ₂ / d` step; `(by omega)` inside `obtain ... := Finset.card_eq_one.1 (by omega)` sees no usable constraints — the card fact must be a tactic-mode `have`; `csInf_le` at this pin takes `BddBelow` (bounded by 0 via `conductance_nonneg`) while `le_csInf` takes nonemptiness; `Fin.sum_univ_two` (not `Finset.`); and `rw [← h]` on a hypothesis containing the value `1` rewrites the numeral too — a calc through `h3.symm` avoids it.

**Verification:** every changed module elaborates directly and is linked into the full default build (QA via explicit targets per the recorded scope). The delivery is fully proved hard crust — nothing axiom-backed was added. It is load-bearing on the retirement end-to-end: a wrong constant anywhere in the retired `cheeger_sweep` chain falsifies `cheeger_cut_existence` outright, the QA Rayleigh-transfer cross-check fails on any defective normalization, and the regularity refutation ties the hypothesis set to a refuted hypothesis-free form at a fixture satisfying every other hypothesis.

**Remaining risk:** the certified cut's *witness* is the conductance minimizer (classical choice over a finite search — existence, not extraction); the stronger algorithmic statement (certifying an explicit Fiedler level set by a sweep argument) is the named follow-on and needs new mathematics (a sweep-extraction lemma with averaging-over-levels strictness care) beyond the Cheeger inequalities. The QA certificate is displayed on `K₂` where the bound is loose (`1 ≤ 4`); tightness fixtures would need larger expanders not in the QA zoo.

**Next handoff:** the remaining Medium rows by leverage — **approximate spectral projection** (Step 0 first; a recorded "not tractable at reasonable cost" is a valid outcome) and the **PF consumers** (irreducible stationary distributions, PageRank) as new-proposal candidates per the one-step discipline; **reversibility Phase B** still needs its recorded operator decision; the **swept-level-set certified cut** is a new named new-proposal candidate.

## 2026-08-23T04:55:00Z — Fiedler Phase B: the certified conductance cut (the first consumer of the Cheeger retirement)

**Run:** `20260823T044903Z-run-1`  
**Session:** `ses_fd30cfa3effedhPliQNP3CHfHI`  
**Status:** superseded  
**Milestone:** The in-progress record for this run's Phase B work — superseded by the completed entry above (same run, same session).

## 2026-08-23T00:29:17Z — Cheeger hard-direction Step 1a delivered: the pure-algebra component, with the survey's constant budget corrected

**Run:** `20260823T001333Z-run-1`  
**Session:** `ses_fd40f0fb2fferjXqdE5FUMcbVE`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1a — the spike-verified pure-algebra component transferred to `Cheeger.lean` at public shape with QA, **zero new axioms** (count stays 10; `#print axioms` on all five new public theorems and eight QA headlines reads only `propext, Classical.choice, Quot.sound`). The delivery's sharpest output is a **constant-budget correction to the survey record**, found by the pre-edit re-derivation before any statement was frozen: the survey's step-5 summation (`E'(u), E'(v) ≤ E'(x)` summed to `2E'(x)`) is loose by exactly the factor `2` the statement's `/2` spends, and its step-6 normalization `R = E'/(d‖x‖²)` omits `laplacian_quadForm`'s `/2` — as recorded the two errors cancel, which is why the twice-hand-checked writeup looked exact.

**Changes:** `GraphTheory.Cheeger` — Component A `core_sum_abs_sq_sub_sq` (verbatim from the spike, `IsSymm` guard), the fused median-part contraction `sq_posPart_sub_add_sq_negPart_sub_le` + `sum_edgeWeight_sq_posPart_add_sq_negPart_le` (the *tight* form: the pointwise pair-summed identity whose cross-edge slack `(u+v)² ≥ u²+v²` pays for carrying both parts, translation invariance absorbed into its RHS — the separate translation-invariance lemma the sketch named is inert and was not added), the regularity bridge `sum_deg_mul_eq_of_regular`, and the normalization `rayleigh_regularNormalizedLaplacian_eq` (`R = E'/(2d‖x‖²)`). `Cheeger_QA.lean` 33 → 59: Component A on `K₂` with all three quantities independently computed (the degree sum through the new bridge, load-bearing) and the strict gap `4 < 8` pinned; the contraction on `C₄` in an equality case (`4 + 4 = 8`) and a strict case (`4 + 4 < 16`); the normalization cross-checked against the independently pinned `λ₂(L_sym) = 2`; and two guard refutations — `IsSymm` at the nonnegative asymmetric `!![0,1/10;1,0]` (`121/100 ≤ 44/100` false, the column-vs-row-sum mismatch at vertex `0`), nonnegativity at the symmetric negative `!![0,-1;-1,0]` (`-1 ≤ -2` false) — each with the surviving structure proved to hold on the fixture. Records: the proposal (Step-1a delivery record, the inline dated correction at the survey's step 6 so 1b/1c cannot follow the loose route, status header, open-next-step → 1b), `proposals/README.md` (Medium row, no-High-rows paragraph), SGT index map (Cheeger section +4 rows + program note), README (1404, the trust-surface sentence), radar (QA axis held 4.0, count synced 1378/39 → 1404/39, hold logged), scoreboard (both Direct rows, `lake build` row, lint date, interpretation bullet), the execution plan, this log.

**Decisive commands and outcomes:** `lake env lean Scaffold/Mathlib/GraphTheory/Cheeger.lean` — zero errors (only the documented pre-existing `unusedSectionVars` warning at `regularNormalizedLaplacian_symmetric`, verified identical in HEAD by a `git stash` round-trip); `lake env lean Scaffold/QA/SpectralGraph/Cheeger_QA.lean` — zero errors, zero warnings; `lake build` on both targets ✔; `#print axioms` via `wip/` check files — the five public and eight QA headline declarations each `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2232 targets, "Build completed successfully")**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1404/10/0**, idempotent under re-run. Two pin-specific proof notes for the record: `max_eq_left ha` mis-instantiates when `ha` is the *threshold* comparison rather than `0 ≤ a−m` (side conditions written `(by linarith)` throughout), and `field_simp` mangles the Rayleigh-normalization goal into disjunctive junk — the robust route is `← div_div` + `simp only [div_eq_mul_inv]` + `ring`.

**Verification:** every changed module elaborates directly and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional, and `cheeger_lower_bound` remains admitted, visible, and cited. The new theorems are load-bearing on the shelf they consume (`laplacian_quadForm`'s exact `/2`, `quadForm_regularNormalizedLaplacian`, `Finset.sum_mul_sq_le_sq_mul_sq`, `deg`'s row-sum shape): the QA normalization witness would fail if the `/2` were wrong, and the guard refutations tie each statement guard to a refuted hypothesis-free form at a fixture satisfying every other hypothesis.

**Remaining risk:** the corrected constant chain is now machine-checked at both endpoints (Component A, the fused contraction, the normalization) but its *middle* — the per-part combination `φ²d‖y‖² ≤ E'(y)` — lands with Step 1b's co-area core, still hand mathematics; the K₂/C₄ numeric pins above constrain it but do not prove it. Step 1b is rated moderate-high risk (no finite-sum/interval-integral interchange in the pin; ~30 lines of Finset-induction Fubini priced in). Step 1c must consume the corrected shapes per the proposal's inline annotation.

**Next handoff:** **Cheeger Step 1b** — the co-area core (`½ ∑ A |y i² − y j²| ≥ φ d ∑ y i²` for minority-level-set `y ≥ 0`), its own dedicated run per the Davis–Kahan precedent; then Step 1c (median + assembly) retires `cheeger_lower_bound` at the unchanged statement. Approximate spectral projection still needs its Step 0; the PF consumers (irreducible stationary distributions, PageRank) are new-proposal candidates. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-23T00:13:33Z — Cheeger hard-direction Step 1a: the pure-algebra component (transfer run)

**Run:** `20260823T001333Z-run-1`  
**Session:** `ses_fd40f0fb2fferjXqdE5FUMcbVE`  
**Status:** superseded  
**Milestone:** The in-progress record for this run's Step-1a work — superseded by the completed entry above (same run, same session).

## 2026-08-22T23:05:59Z — Cheeger hard-direction Step 0 surveyed: decisive positive-with-large-cost, the gate opened

**Run:** `20260822T224324Z-run-1`  
**Session:** `ses_fd45b5b09ffeCDr541zsEJofYM`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` open next step — the mandated per-axiom Step 0 tractability survey of `cheeger_lower_bound` (`Cheeger.lean:88`, `φ²/2 ≤ λ₂(L_sym)`, d-regular), the last remaining perturbation axiom after the Weyl (2026-08-20) and Davis–Kahan (2026-08-21) retirements. Top Medium row with no High rows and the plan's recorded next handoff naming it first. Delivered as survey + spike only, no Cheeger source edits, per the Davis–Kahan one-step precedent; the proposal's own gate now authorizes Step 1 as dedicated runs.

**Changes:** the survey record in the proposal (status header; the full record replacing the "unsurveyed" placeholder; per-axiom item 3; open-next-step → Step 1a) — the route with tight constants, the half-volume obstruction recorded with its counterexample shape so no future run re-derives the median trick, the pin facts with their traps, the 1a/1b/1c decomposition with cost estimates (550–900 lines over 2–3 runs); `proposals/README.md` (Medium row, no-High-rows paragraph); the execution plan; this log. The green spike `wip/cheeger_spike.lean` (git-ignored): the Cauchy–Schwarz core at final shape, the shifted-positive-part contraction, the variational-assembly skeleton in hypothesis form, and the scalar FTC primitive — every `#print axioms` clean.

**Decisive commands and outcomes:** `lake env lean wip/cheeger_spike.lean` — zero errors, `CheegerSpike.core_sum_abs_sq_sub_sq`, `abs_posPart_sub`, `assembly_skeleton` each depend on `propext, Classical.choice, Quot.sound` only; `lake build Scaffold.Mathlib.GraphTheory.Cheeger` ✔ (untouched module; no `Scaffold/**` file changed this run, so the spike's direct elaboration is the decisive check and the umbrella build certifies nothing new); `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated with zero diff (idempotent, 1378/10/0). Survey findings: the sInf reduction through the proved `secondEval_variational` dissolves the eigenvector/spectral side entirely; the two-median-part norm split `‖u‖²+‖v‖² = ‖x‖² + nm²` makes the factor-2 budget exactly the statement's `/2` — constants reconstructed and hand-checked twice, with the K₂-equality QA pin prescribed before Step 1's statements freeze.

**Verification:** the survey's positive verdict rests on elaboration-verified primitives (the spike), shelf lemmas read at their exact statements (`secondEval_variational`, `regularNormalizedLaplacian_psd`, `regularNormalizedLaplacian_mulVec_onesVec`, `conductance_ge_cheegerConstant`, `vol_eq_of_regular`, `laplacian_quadForm`, `quadForm_regularNormalizedLaplacian` — all already proved), and hand mathematics that remains unproved until Step 1 lands. Nothing here claims the axiom discharged; `cheeger_lower_bound` is still admitted, visible, and cited.

**Remaining risk:** the hand-verified constant chain is not machine-checked — the recorded mitigation is the numeric QA witness (K₂ equality, strict C₄/P₃) before Step 1's statements freeze, this repository having been burned by a false Cheeger shape before. The co-area core (Step 1b) is rated moderate-high risk; no finite-sum/interval-integral interchange exists at this pin (priced in as ~30 lines of Finset induction).

**Next handoff:** **Cheeger Step 1a** — transfer the spike-verified pure-algebra component into `Cheeger.lean` at its public shape (with the `IsSymm` statement guard) plus QA; then 1b (the crux) and 1c as dedicated runs. Approximate spectral projection still needs its Step 0; the PF consumers (irreducible stationary distributions, PageRank) are unblocked as new-proposal candidates. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T22:53:19Z — Cheeger hard-direction Step 0: the survey that gates the last perturbation axiom

**Run:** `20260822T224324Z-run-1`  
**Session:** `pending`  
**Status:** superseded  
**Milestone:** The in-progress record for this run's survey work — superseded by the completed entry above (same run, same session once established).

## 2026-08-22T21:42:53Z — Perron–Frobenius admitted: the directed axis' second spectral toolkit

**Run:** `20260822T211552Z-run-1`  
**Session:** `ses_fd4b02ef7ffeucven25tSq36wL`  
**Status:** completed  
**Milestone:** `proposals/admit-perron-frobenius.md` — the scoped admission delivered: `Matrix.IsIrreducible` (combinatorial, global, Fintype-free) plus the admitted Horn–Johnson 8.4.4 axiom at the irreducible-case qualification level, QA with the mandated imprimitive-cycle negative witness, and the index/coverage/count records. One new explicit cited axiom (9 → 10) — the first admission since the 2026-08-19 scope decision, and deliberately so: the directed-operators program's PSD refutation showed the undirected positivity layer does not transfer, and this is the nonnegative-matrix theory that replaces the symmetric `evals` toolkit on the directed axis. No consumer work (stationary distributions, PageRank stay named follow-ons).

**Changes:** the new `Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean` (namespace `Scaffold.LinearAlgebra`) and `Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean` (36 declarations, the first LinearAlgebra-domain QA file); umbrella import + doc entry in `Scaffold.lean`; Horn–Johnson source-index row (Theorem 8.4.4) + scope note; the new `index/map/linear_algebra.md` + map README row; coverage map's named-absent Perron–Frobenius row updated to "Absent (upstream) / Admitted (Scaffold)"; backlog item 8 third update; README (10 axioms, 1378 QA, trust surface, module table); radar QA-axis sync (1342/38 → 1378/39, held 4.0); scoreboard (counts, both Direct rows, `lake build` row, lint row, interpretation bullet); the proposal's status header + full delivery record; `proposals/README.md` (row retired, paragraph rewritten, Delivered row); the execution plan. Statement-shape decisions recorded before stating: the `hex` degeneracy guard (exactly the missing strength at `card V ≤ 1`, derivable from irreducibility at `n ≥ 2`), `rootMultiplicity`-over-ℝ simplicity, the strong uniqueness clause with the explicit `μ = r` conjunct, spectral radius encoded through complex charpoly roots (no matrix spectral radius in the pin), and no strict-dominance clause.

**Decisive commands and outcomes:** `lake env lean` on the module and QA — zero errors, zero warnings each; explicit `lake build` targets for both ✔; `#print axioms` — the five axiom-consuming QA theorems (`perron_frobenius_P_QA`, `perron_frobenius_D_QA`, the only-eigenvalue cross-check, both domination instantiations) list exactly `Scaffold.LinearAlgebra.perron_frobenius` + `propext, Classical.choice, Quot.sound`, while the eleven hand theorems (including the centerpiece `strict_dominance_refuted_QA` and both hand-only only-eigenvalue theorems) read only the standard three; **full `lake build` ✔ (2232 targets, "Build completed successfully", zero errors, detached)**; `lint_axioms`, `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1378/10/0**, idempotent under re-run. QA highlights: on the positive witness `!![1,2;1,0]` the Perron root is *derived to be exactly 2* from the axiom's eigen-equation on its unknown witness, with simplicity and complex-domination clauses pinned against hand factorizations; on the asymmetric directed 2-cycle `!![0,4;1,0]` the strengthening's `|μ| < r` is refuted at `|−2| = 2 = r` while the admitted `|−2| ≤ r` holds with equality — the fence the proposal's Calibration section demanded. Pin-specific techniques recorded in the proposal for future fixtures: plain `open Polynomial` (not `open scoped`) activates `X`/`C`; eta-expanded `fin_cases` indices need explicit `show`; C-numerals must be normalized to numerals before `ring` (this pin's `C_mul` points opposite to modern Mathlib, `C_eq_natCast` misses OfNat literals); scalar `2 • x` needs `(2:ℝ)` annotation; `charpoly_map`'s RingHom argument does not match `coe_algebraMap`'s coerced form — compute mapped charpolys directly.

**Verification:** the axiom is admitted, not proved — nothing here is described as foundationally established, and the QA's role is interface pinning plus the falsification fence, not validation of the axiom's truth. The axiom-transparency split is machine-checked: every axiom-consuming QA theorem shows the dependency, every hand theorem does not.

**Remaining risk:** low. The statement is guarded exactly where this repository has been burned before (no strict dominance; `hex` for the degenerate sizes), and the QA refutes the canonical misstatement. The named residuals are the follow-on consumers (irreducible stationary distributions, PageRank), each requiring its own proposal, and the standing note that an upstream Mathlib Perron–Frobenius would trigger the replacement lifecycle (a global `Matrix.IsIrreducible` from Scaffold would then be renamed).

**Next handoff:** the Medium rows by leverage — the **Cheeger hard-direction Step 0 survey** (known-hard; the last perturbation-axiom remainder) and **approximate spectral projection** (Step 0 first). The PF consumers are unblocked as new-proposal candidates. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T21:15:52Z — Perron–Frobenius admission: the directed axis' second toolkit

**Run:** `20260822T211552Z-run-1`  
**Session:** `ses_fd4b02ef7ffeucven25tSq36wL`  
**Status:** in-progress  
**Milestone:** `proposals/admit-perron-frobenius.md` scoped admission — irreducibility via directed reachability, the Horn & Johnson 8.4.4 axiom at the irreducible-case qualification level (no strict-dominance clause), QA with the mandated imprimitive-cycle negative witness, and the index/coverage/axiom-count records. Top-ranked Medium row, Active table holding no High rows, and the recorded next handoff of the directed-operators completion (whose PSD refutation names this as what the directed spectral theory needs). One new explicit cited axiom (9 → 10); no consumer work.

**Changes:** intent recorded in the execution plan (pre-edit survey + statement-shape decisions: the `hex` degeneracy guard, the strong uniqueness clause, `rootMultiplicity`-over-ℝ simplicity, global `Matrix.IsIrreducible`, rational QA fixtures). Lean work pending below (`Scaffold/Mathlib/LinearAlgebra/PerronFrobenius.lean` + `Scaffold/QA/LinearAlgebra/PerronFrobenius_QA.lean`).

**Verification:** pending — module + QA elaboration, `#print axioms` on the axiom's QA consumers (must list the new axiom), explicit builds, full `lake build`, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** low — the statement is scoped by a proposal whose Calibration section was written against exactly the misstatement this repository has made before; the QA plan's negative witness is designed to fence it.

**Next handoff:** delivery record, records sync, terminal entry.

## 2026-08-22T20:10:13Z — Directed operators Step 2 delivered: the symmetrized normalized Laplacian; the proposal's Lean content complete

**Run:** `20260822T194020Z-run-1`  
**Session:** `ses_fd5032572ffe4qTynTCxjNs6hi`  
**Status:** completed  
**Milestone:** `proposals/directed-graph-operators.md` Step 2 (the directed normalized Laplacian `I − ½(SAS + SAᵀS)` at the Step-0-recorded out-degree-symmetrized convention) plus the Step-3 agreement brick (folded in per the Step-0 record's "one line from decision (b)" scoping) — the proposal's Lean content is complete. Top-ranked Medium row, Active table holding no High rows. Zero new axioms (count stays 9).

**Changes:** `GraphTheory.Directed` extended with `directedNormalizedLaplacian` (the shelf's `degreeInvSqrt`/`degreeSqrt` reused verbatim — `deg` *is* the out-degree), the entry form, **hypothesis-free symmetry** (the two defining halves are transposes of each other; the directed axis' one symmetric operator), the acceptance-bar agreement `= normalizedLaplacian` under `A.IsSymm`, and the square-root-free conjugate `√D L_dir √D = degreeMatrix A − ½(A + Aᵀ)`. QA `Directed_QA.lean` 41 → 88: all nine `L_dir dirA` entries computed from the entry form (exactly `[[1,−1,−1/2],[−1,1,0],[−1/2,0,1]]`), the symmetry theorem instantiated on asymmetric input, the conjugate's two sides independently hand-checked at `−2`, the symmetric-edge agreement pinned raw both sides, and the two new negative witnesses — undirected reuse (`L_dir ≠ normalizedLaplacian` on directed input, `−1 ≠ −3/2`) and the **PSD refutation**: on `dirB = !![0,4;1,0]` (nonnegative, positive out-degrees, symmetric `L_dir`) `quadForm L_dir 1 = −1/2 < 0` — symmetric does not mean PSD; the positivity layer of the undirected toolkit provably does not transfer, and the directed spectral theory needs Perron–Frobenius (the proposal's Calibration boundary, now witnessed numerically). Records: the proposal (status COMPLETE, Step-2 delivery record), `proposals/README.md` (row, progress paragraph, Delivered table), backlog item 8, the SGT index map, README (1342, proved list, module table), radar (QA count 1295/38 → 1342/38, held 4.0), scoreboard (both Direct rows, `lake build` row, interpretation bullet), the execution plan, and this log. Nothing committed.

**Decisive commands and outcomes:** `lake env lean` on the module and QA — zero errors, zero warnings each (after one rebuild of the module olean; QA elaboration had initially consumed the stale olean); explicit `lake build` targets for both modules ✔; `#print axioms` on the five new public and nineteen headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2230 targets, "Build completed successfully", zero errors, detached)**; `lint_axioms` (9), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1342/9/0**, idempotent under re-run. Pin-specific QA techniques recorded in the proposal for future fixtures: `Real.sqrt_eq_iff_eq_sq` for numerals (`norm_num` alone does not evaluate `Real.sqrt 4`); the entry form's conditional discharges by `if_pos rfl`/`if_neg (by decide : ¬(i = j))` — `Matrix.one_apply_ne (by decide)` elaborates with metavariables and fails; ground `Fin`-index `if`s inside entry computations need full `simp` (`norm_num` leaves residue); `rw` rewrites all occurrences of an instantiated pattern at once, so duplicate lemma mentions in a `rw` list fail.

**Verification:** fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere; the QA is load-bearing in both directions (the hypothesis-free symmetry instantiated on asymmetric input would fail to elaborate against a definition that secretly needed `IsSymm`; the conjugate's two sides were computed independently and must match; the PSD refutation exercises the shelf's `quadForm` interface against the new operator).

**Remaining risk:** low. The named residual is unchanged and now witnessed: the convention forfeits Chung's directed-Cheeger content, and the PSD refutation shows the undirected positivity layer does not transfer — any directed spectral statement must wait for Perron–Frobenius. The Mathlib coverage map needed no correction.

**Next handoff:** the Medium rows by leverage — **the Perron–Frobenius admission** (`admit-perron-frobenius.md` — decoupled by the Step-0 record; its imprimitive-cycle negative witness is the centerpiece its QA plan mandates; the natural continuation of the directed axis), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T19:40:20Z — Directed operators Step 2: the symmetrized normalized Laplacian, closing the proposal

**Run:** `20260822T194020Z-run-1`  
**Session:** `ses_fd5032572ffe4qTynTCxjNs6hi`  
**Status:** in-progress  
**Milestone:** `proposals/directed-graph-operators.md` Step 2 (the directed normalized Laplacian `I − ½(SAS + SAᵀS)` at the Step-0-recorded out-degree-symmetrized convention) plus the Step-3 agreement brick (recorded by Step 0 as one line from decision (b)) — on delivery the proposal's Lean content is complete. Top-ranked Medium row, Active table holding no High rows. Zero new axioms.

**Changes:** intent recorded in the execution plan; Lean work pending below (`GraphTheory.Directed` + `Directed_QA.lean`).

**Verification:** pending — module + QA elaboration, `#print axioms`, explicit builds, full `lake build`, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** low — the convention is decided, the consumed shelf lemmas (`degreeSqrt`/`degreeInvSqrt` cancellation pair, `normalizedLaplacian`) were read at their exact signatures during the Step-0 survey and again this run.

**Next handoff:** delivery record, records sync, terminal entry.

## 2026-08-22T18:17:01Z — Directed operators Step 0 + Step 1: convention decisions and the degree layer

**Run:** `20260822T181701Z-run-1`  
**Session:** `ses_fd5521f76ffeRFs1v4dJctUmET`  
**Status:** in-progress  
**Milestone:** `proposals/directed-graph-operators.md` Step 0 (the mandated survey and convention decisions, coordinated with `proposals/admit-perron-frobenius.md` per the scoped-together instruction) + Step 1 (the degree layer `outDeg`/`inDeg`, directed handshaking, and the asymmetric-input certification of the pre-existing walk operators) — the top-ranked Medium program with the Active table holding no High rows. Zero new axioms.

**Changes:** Step 0 record written into the proposal (decisions (a)/(b)/(c) plus the discovery that `deg`/`walkTransitionMatrix`/`walkLaplacian` are already the out-degree walk operators, hypothesis-free); intent recorded in the execution plan. Lean: new `Scaffold/Mathlib/GraphTheory/Directed.lean` and `Scaffold/QA/SpectralGraph/Directed_QA.lean` pending below.

**Verification:** pending — module + QA elaboration, `#print axioms`, oleans, umbrella import, full `lake build`, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** low — every consumed shelf lemma was read at its exact signature during the Step-0 survey; the convention decision (b) decouples rather than couples, so no build-order hazard.

**Next handoff:** delivery record, records sync, terminal entry.

## 2026-08-22T18:39:13Z — Directed operators Step 0 + Step 1 delivered: the directed axis is open, decoupled from Perron–Frobenius

**Run:** `20260822T181701Z-run-1`  
**Session:** `ses_fd5521f76ffeRFs1v4dJctUmET`  
**Status:** completed  
**Milestone:** `proposals/directed-graph-operators.md` Steps 0+1 — the three mandated Step-0 convention decisions recorded before any statement, then Step 1 (the run's one Lean step): the directed degree layer in the new `Scaffold.Mathlib.GraphTheory.Directed` plus the asymmetric-input QA certification of the pre-existing walk operators. Zero new axioms (count stays 9). The Step-0 convention decision **decouples this program from `admit-perron-frobenius.md`** (out-degree-symmetrized normalized Laplacian, not Chung's Perron-vector form, so no admitted axiom becomes a prerequisite of a definition).

**Changes:** new `Scaffold/Mathlib/GraphTheory/Directed.lean` (seven public declarations: `outDeg`, `inDeg`, the two `rfl` identifications with the shelf's `deg` and its transpose, the symmetric-cone agreements, directed handshaking `∑ outDeg = ∑ inDeg`) and new QA `Scaffold/QA/SpectralGraph/Directed_QA.lean` (41 declarations: the genuinely-directed fixture `!![0,3,1;1,0,0;1,0,0]` with a nine-entry `rfl` table, both degree functions pinned raw `outDeg = (4,1,1)` / `inDeg = (2,3,1)`, handshaking `6 = 6` by both routes, the symmetric-edge agreement witness, the load-bearing instantiation of `walkTransitionMatrix_row_sum` and `walkLaplacian_mulVec_one_eq_zero` **on asymmetric input** with a raw cross-check, and the two negative witnesses `outDeg 0 ≠ inDeg 0` and `¬ (walkTransitionMatrix dirA).IsSymm`). Umbrella import added. Records: the proposal (status header, Step-0 record, Step-1 delivery record with the pin-specific QA technique), `proposals/README.md` (Medium row + progress paragraph), backlog item 8, the SGT index map (Directed section), README (1295, proved list, module table), radar (QA axis held at 4.0, count synced 1254/37 → 1295/38), scoreboard (both Direct rows, the `lake build` row, a new interpretation bullet), the execution plan, and this log. Nothing committed; prior-run uncommitted deliveries preserved untouched.

**Decisive commands and outcomes:** `lake env lean` on the module and on the QA file — zero errors, zero warnings each; explicit `lake build` targets for both modules ✔; `#print axioms` on the seven public and twelve headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2230 targets, "Build completed successfully", zero errors, detached log + poll)**; `lint_axioms` (**9**, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1295/9/0** (`Directed_QA` a new file row at 41). One QA-engineering detour recorded for future fixture work on this pin: `simp only` unfolds of *new* degree defs against matrix literals leave `vecHead/vecTail` residue (while the same list through the shelf's `deg` behaves), and `show` cannot kernel-reduce `Finset.sum` — the deterministic route is a `rfl` entry table plus `Fin.sum_univ_three` splitting with table rewrites, now recorded in the proposal.

**Verification:** the delivery is fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere, and the QA is load-bearing in both directions: the asymmetric-input instantiations would fail if the pre-existing walk operators had secretly depended on symmetry (that dependence-absence is the certification's whole point), and both negative witnesses refute the hypothesis-free forms (`outDeg = inDeg`; walk-matrix symmetry) that undirected habits would suggest.

**Remaining risk:** low. The named residual is Step 2's to carry: the chosen convention forfeits Chung's directed-Cheeger content (recorded honestly in the Step-0 record); any future directed-isoperimetric work must adopt Chung's convention there or prove its own bounds. The Mathlib coverage map needed no correction — the Step-0 re-survey confirmed its rows.

**Next handoff:** the Medium rows by leverage — **directed operators Step 2** (the normalized Laplacian at the recorded convention; unblocked), **the Perron–Frobenius admission** (decoupled; its imprimitive-cycle negative witness is the centerpiece its QA plan mandates), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T17:12:56Z — Subgaussian tail bound retired by repair: the Step 0 spike proved the old axiom materially false

**Run:** `20260822T164518Z-run-1`  
**Session:** `ses_fd5aa3374ffeR6W0kz6WrMW4ho`  
**Status:** completed  
**Milestone:** `proposals/prove-subgaussian-tail-bound.md` — the mandated Step 0 spike plus the repair-and-retire in one run: `subgaussian_tail_bound` is a proved theorem, **explicit axioms 10 → 9** (the first measure-theoretic axiom retirement), delivered as the Woodbury-precedent emergency correctness repair after the spike proved the old statement materially false.

**Changes:** `Subgaussian.lean` — `axiom subgaussian_tail_bound` became `theorem` at the same name and conclusion (including the `2K²` constant) with honest hypotheses `(hK : 0 < K)`, MGF integrability at `K`, and the MGF bound at `K`; the `subgaussianNorm` docstring's junk-behavior paragraph corrected with a dated note (unbounded tails make the defining set *full*, not empty — `integral_undef` junk-zero integrals); `hoeffding_lemma`'s stale QA-note (referencing the nonexistent `hoeffding_lemma_zero_QA`) fixed. `Scalar_QA.lean` 6 → 17 declarations: the zero fixture through the new hypotheses, the proposal-mandated nonzero instance (constant-1, `K = 2`, `t = 1` on `dirac 0`; moment `exp (1/4) ≤ 2` via the pinned `Real.log_two_gt_d9`; event and bound sides pinned raw), and the four-piece refutation family (`3 • δ₀` fixture; the empty-set junk mechanism exhibited as a theorem; the old hypotheses proved satisfiable-vacuously; the old conclusion `3 ≤ 2` refuted). Records: both index files, scoreboard (counts, Direct rows, `lake build` row, lint row, interpretation bullet), radar (axiom-minimization synced to 9, trend extended, hold logged; QA count 1254/37, held), README, architecture §12, the proposal (full delivery record with the pin-specific API notes and the adjacent-hazard residual), the execution plan, and this log. The operator-side worktree change (the `proposals/README.md` Low row) preserved untouched; nothing committed.

**Decisive commands and outcomes:** the Step 0 spike (`wip/subgaussian_spike.lean`, git-ignored) elaborated green with `#print axioms subgaussian_tail_bound` reading only `propext, Classical.choice, Quot.sound` — confirming both falsity mechanisms against the pin (`Real.sInf_empty` at Archimedean.lean:190; `integral_undef` at Bochner.lean:743) before the module was touched; `lake env lean` on the module (only the pre-existing `unused variable K` warning, verified identical in HEAD via a HEAD elaboration) and on the QA file (zero errors; nine remaining warnings = the pre-existing set, verified by a stashed-HEAD elaboration); `#print axioms` on the retired theorem and all twelve touched/new QA theorems — three standard axioms only; `lake build` on both targets ✔; **full `lake build` ✔ (2229 targets, "Build completed successfully", detached log + poll)**; `lint_axioms` (**9**), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1254/9/0**, idempotent.

**Verification:** the delivery is fully proved hard crust at the repaired statement; the QA is load-bearing in both directions — the nonzero instance pins the bound's two sides raw (a wrong `2K²` constant or hypothesis orientation would break it), and the refutation family falsifies the old shape with its hypotheses proved satisfied (the Woodbury/old-Cheeger falsification pattern). One operational lesson re-confirmed: QA files elaborate against built oleans, so the module must be rebuilt before its QA consumer sees a changed interface (the QA's first failure was the stale axiom-shaped olean, not the code).

**Remaining risk:** low for what is delivered. The named residual — the same junk-integral mechanism likely touching `hoeffding_inequality`/`bernstein_inequality`'s mean hypotheses on infinite measures and the `MatrixMDS` set-integrals — is recorded in the proposal and architecture §12 for their own Step 0s. `hoeffding_lemma` remains an admitted axiom (statement unchanged); the repaired theorem no longer consumes it, so its only remaining consumer is the `subgaussian_norm_zero_QA` cross-coherence check.

**Next handoff:** the Medium rows by leverage — **Perron–Frobenius + directed operators** (scoped together, Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard working assumption), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T16:45:18Z — Subgaussian tail bound: Step 0 spike (and contingent repair-and-retire)

**Run:** `20260822T164518Z-run-1`  
**Session:** `ses_fd5aa3374ffeR6W0kz6WrMW4ho`  
**Status:** superseded (by the completed delivery entry above)  
**Milestone:** `proposals/prove-subgaussian-tail-bound.md` — the proposal's mandated Step 0 (Lean spike against the pinned Mathlib: `Real.sInf_empty`, `integral_undef`, `mul_meas_ge_le_integral_of_nonneg` at exact signatures; the monotone-in-`K` moment transfer; the Markov assembly), with Step 1 (retire `subgaussian_tail_bound`, axioms 10 → 9) to follow in this run if the spike confirms tractability. Pre-edit reading surfaced two junk hazards in the axiom's current shape (empty-`sInf` vacuity on measures of mass > 2; junk-zero Bochner integrals making the defining set full for heavy tails) — if the spike confirms either, the run executes the Woodbury-precedent repair-and-retire with the decision recorded before stating.

**Changes:** intent recorded in the execution plan (hazards, contingent route, next action). No Lean or record edits yet beyond that.

**Verification:** pending — spike elaboration, then module + QA elaboration, `#print axioms`, full `lake build`, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** the falsity hazards, if confirmed, convert this from a proof task to a correctness repair; the repaired statement's shape (moment+integrability hypotheses at `K`, conclusion unchanged) is already drafted in the execution plan.

**Next handoff:** spike results and the go/no-go on the repair route.

## 2026-08-22T14:07:07Z — Relative entropy and Shannon entropy delivered: the finite-distribution program complete

**Run:** `20260822T134800Z-run-1`  
**Session:** `ses_fd64842bdffeLZUnmAoGML8Wh3`  
**Status:** completed  
**Milestone:** `proposals/finite-relative-entropy.md` — both steps in one run per the proposal's own operating instruction: Gibbs' inequality in both directions (`klDiv_nonneg`, `klDiv_eq_zero_iff`), the uniform bridge, and the entropy maximum with its equality case (`shannonEntropy_le_log_card`, `shannonEntropy_eq_log_card_iff`), all pure hard crust in the new `Scaffold.Mathlib.InformationTheory.Entropy` — zero new axioms (count stays 10). Closes the entropy half of backlog item 6 (reversibility half landed earlier the same day).

**Changes:** new public module `Scaffold/Mathlib/InformationTheory/Entropy.lean` (namespace `Scaffold.InformationTheory`; nine public theorems around the scalar `klTerm` carrying the proposal-mandated visible `a = 0 ↦ 0` junk convention) and new QA `Scaffold/QA/InformationTheory/Entropy_QA.lean` (31 declarations, the first InformationTheory-domain QA file). **Route decision recorded before stating:** the mandated Jensen survey found the whole shelf present (`ConcaveOn.le_map_sum`, `StrictConcaveOn.lt_map_sum`/`eq_of_map_sum_eq`/`map_sum_eq_iff'`; `strictConcaveOn_log_Ioi` — stop-and-record clause not triggered), but the delivered proof is the term-wise information inequality (`Real.one_sub_inv_le_log_of_pos` + `Real.log_lt_sub_one_of_pos` at the reciprocal) — the same Cover–Thomas 2.6.3 route with no Finset-`smul` plumbing and no support filtering; the junk case is discharged inside the per-term bound, where its strictness is *stronger* (gap `= b > 0`), so the equality case needs no `∑_{support} q` argument. QA: the biased coin's divergence and entropy hand-computed to closed log-forms (`¼·log(27/16)`, `¼·log(256/27)`) with strict positivity pinned; the equality case exercised in both directions against raw computations; **the uniform bridge numerically cross-checked** at the fair coin (`¼·log(27/16) = log 2 − ¼·log(256/27)`, both sides independently pinned); the maximum attained at uniform two ways and **strictly missed** by the non-uniform `Fin 4` distribution — strictness only through the equality-case iff, the proposal-prescribed load-bearing use; the delta distribution's entropy exactly `0` exhibiting the junk convention. Records: proposal (status header + full delivery record with pin-specific API notes), `proposals/README.md` (Medium row → Delivered; progress paragraph), new `index/map/information_theory.md` + map README row, scoreboard (1243/10/0 regenerated; both Direct rows prepended; a new interpretation bullet), radar (QA axis held at 4.0, count synced 1243/37, sync logged), README (counts, module table, proved list, and the stale conditional-on-Davis–Kahan persistence note corrected), backlog item 6, the umbrella import + docstring, the execution plan, this log.

**Decisive commands and outcomes:** `lake env lean` on `Entropy.lean` and `Entropy_QA.lean` — zero errors, zero warnings each (final re-elaboration after the reachability probe); explicit target builds of both modules ✔; `#print axioms` on the nine public and thirteen headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2229 targets, "Build completed successfully", zero errors)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated idempotently (**1243 QA declarations / 10 explicit axioms / 0 sorries**). **Build-reachability fact recorded (content-change probe: appending a comment to a QA file leaves `lake build` with nothing to do):** the default target is the `Scaffold.lean` umbrella closure — it certifies every public module including the new one but does not itself compile the QA tree; QA modules are certified by direct elaboration and explicit targets, and the scoreboard's `lake build` row now states this scope precisely.

**Verification:** the delivery is fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere. The QA is load-bearing in both directions: every headline quantity is pinned through the theorems *and* by raw log algebra independent of them (a wrong bridge constant or sign would break the numerical cross-check), and the strictness witness is derivable only through the equality-case iff — exactly the strict-route use the proposal's QA plan demands.

**Remaining risk:** low — the area is self-contained and every consumed Mathlib lemma was verified at its exact signature before stating. Pin-specific API notes for future QA are recorded in the proposal: `Real.log_pow`/`Real.log_inv` take explicit arguments (no hypotheses), `Finset.sum_one` is absent at that name (use `Finset.sum_const` + `Finset.card_univ` + `Nat.smul_one_eq_cast`), coefficient-atom identities need `ring_nf` rather than `norm_num`, and `Finset.sum_sub_distrib` is oriented `∑ (f − g) = ∑ f − ∑ g`.

**Next handoff:** the Medium rows by leverage — **the subgaussian tail bound** (the 2026-08-22 operator-directed addition — run its Step 0 first), **Perron–Frobenius + directed operators** (Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T13:48:00Z — Relative entropy and Shannon entropy: the finite-distribution program

**Run:** `20260822T134800Z-run-1`  
**Session:** `ses_fd64842bdffeLZUnmAoGML8Wh3`  
**Status:** superseded (by the completed delivery entry above)  
**Milestone:** `proposals/finite-relative-entropy.md` — Step 1 (`klDiv`, Gibbs' inequality `klDiv_nonneg`, the equality case `klDiv_eq_zero_iff`) and Step 2 (`shannonEntropy`, the maximum `shannonEntropy_le_log_card`, its equality case), both in one run per the proposal's own operating instruction. Closes the entropy half of backlog item 6; zero new axioms (pure hard crust from proved Mathlib scalar lemmas).

**Changes:** intent, pre-edit surveys, route decision, statement shapes, and QA plan recorded in the execution plan before any edit. Surveys done: the pinned Jensen shelf is fully present (`ConcaveOn.le_map_sum`, `StrictConcaveOn.lt_map_sum`/`eq_of_map_sum_eq`/`map_sum_eq_iff'` at Jensen.lean:71/145/169/233; `strictConcaveOn_log_Ioi` at SpecificFunctions/Basic.lean:63) — the proposal's stop-and-record clause is not triggered — but the delivered route is the term-wise information inequality (`Real.one_sub_inv_le_log_of_pos`, `Real.log_lt_sub_one_of_pos`), the same Cover–Thomas 2.6.3 proof without the Finset-`smul`/support-filter plumbing. Placement decided: new `Scaffold/Mathlib/InformationTheory/Entropy.lean` + `Scaffold/QA/InformationTheory/Entropy_QA.lean`, namespace `Scaffold.InformationTheory`.

**Verification:** pending — module + QA elaboration, `#print axioms`, full build, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** low — every consumed Mathlib lemma verified present at its exact signature before stating; the QA strictness witness depends on the equality-case iff exactly as designed (that is its point).

**Next handoff:** Lean implementation, QA, verification, records.

## 2026-08-22T12:43:09Z — Mixing-time Step 3, component 2 delivered: the χ² assembly; the mixing-time program is complete

**Run:** `20260822T115239Z-run-1`  
**Session:** `ses_fd6b75575ffejcx9dFsZqxgnLo`  
**Status:** completed  
**Milestone:** `proposals/mixing-time-bound.md` Step 3, component 2 of 2 — the χ² assembly and the program's closing statement `chiSquareDistance_le_of_connected`: `χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)` on connected symmetric-nonnegative positive-degree networks under the rate hypothesis. Pure hard crust, zero new axioms; the proposal's radar axis-5 re-score trigger fired (3.0 → 3.5).

**Changes:** three public modules extended — `GraphTheory.Normalized` (+3: the constant fix `walkTransitionMatrix_mulVec_one`, the `√D`/`1/√D`-action entry lemmas), `GraphTheory.Mixing` (+4: the centered evolution `walkDensity_sub_one`, the mass-conservation pairing, the connectivity mode derivation — the kernel of `L_sym` transferred through the proved congruence `√D L_sym √D = L` to the shelf's combinatorial kernel theorem, then collapsed by mass conservation, the mode hypothesis *derived* rather than assumed — and the headline bound); `Mixing_QA.lean` 67 → 117 declarations: the final statement instantiated on both fixtures (K₃ with the bound attained *exactly* at `t = 1, 2`; P₃ with the rate derived basis-independently from two sum-of-squares certificates pinning every eigenvalue into `[0, 2]`), cross-checks of the centered evolution and the connectivity-derived mode fact against the component-1 hand computations, and the two negative witnesses — connectivity load-bearing on the triangle⊕self-loop `Fin 4` fixture (spectrum `{0, 0, 3/2, 3/2}` derived basis-independently so the rate hypothesis provably holds at `r = 1/2` — the loop's `μ = 0` mode excluded from the rate hypothesis by design, exactly the hole connectivity plugs — while `χ²(3) = 3/8 > 3/64` refutes the conclusion), and the rate load-bearing at `r = 1/4` on K₃ (hypothesis unsatisfiable by the trace, conclusion refuted). Records: proposal (status header COMPLETE, the full component-2 delivery record including two pin-specific API discoveries, open-next-step → none with the three optional items named), `proposals/README.md` (Medium row retired to the Delivered table, progress paragraph rewritten, and the duplicate reversibility row — 2026-08-19 drift — removed), scoreboard (1212/10/0, both Direct rows prepended, the `lake build` row extended, a new interpretation bullet), radar (axis 5 **re-scored 3.0 → 3.5** with the full re-score log entry, the weakest-axes paragraph rewritten, QA count synced 1212/36), README (1212, the proved list gains the closing mixing bound, module table, coverage snapshot axis 5 → 3.5), SGT index map (Mixing program-complete header + 4 rows + entry-lemma note), backlog item 2 (program complete), the execution plan, this log. The worktree's unrelated operator-side changes (the untracked `proposals/prove-subgaussian-tail-bound.md` + its README row) and the uncommitted-but-delivered Step-2/Phase A/component-1 work remain preserved untouched.

**Decisive commands and outcomes:** `lake env lean` on `Normalized.lean` (only the documented pre-existing `congr 1` note), `Mixing.lean`, and `Mixing_QA.lean` — the latter two zero errors, zero warnings; `#print axioms` on the seven new public and twelve headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2228 targets, "Build completed successfully", detached log + poll, zero errors)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1212 QA declarations / 10 explicit axioms / 0 sorries**; `Mixing_QA` a 67 → 117 file row).

**Verification:** the delivery is fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere. The QA is load-bearing in both directions: the K₃ positive witness pins the final bound's both sides by raw literal arithmetic with the bound attained exactly at two time steps (the engine's Parseval exactness carrying through the χ² identification unchanged), and the disconnected negative witness is the strongest kind this program supports — every hypothesis of the final theorem except connectivity proved to hold on the fixture (including the rate, via a basis-independent spectrum derivation), with the conclusion refuted, demonstrating that the value-based rate exclusion cannot detect the second kernel mode and connectivity genuinely must be assumed.

**Remaining risk:** low — the program is closed and every interface it built is QA'd. Two pin-specific API hazards are recorded in the proposal for future QA work: this snapshot's `Finset.mul_sum`/`Finset.sum_mul` take arguments `(s) (f) (a)` with `mul_sum : a * ∑ f = ∑ (a * f)` (different argument order and orientation than the standard statement; explicit-argument `have`s are the robust route), and the matrix-literal far-corner entry (`!![…; 0,0,0,2]`-shaped) normalizes through the notation's empty default row and defeats both `rfl` inside `fin_cases` and `norm_num` — the robust routes are an `fin_cases + rfl`-proved entry table consumed as a simp lemma, or a scalar-multiple route avoiding entrywise evaluation.

**Next handoff:** the Medium rows by leverage — **Relative Entropy** (Gibbs' inequality and the entropy maximum from Mathlib's proved strict-concavity machinery), **the subgaussian tail bound** (Step 0 first), **Perron–Frobenius + directed operators** (Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T11:52:39Z — Mixing-time Step 3, component 2: the χ² assembly

**Run:** `20260822T115239Z-run-1`  
**Session:** `ses_fd6b75575ffejcx9dFsZqxgnLo`  
**Status:** superseded (by the completed delivery entry above)  
**Milestone:** `proposals/mixing-time-bound.md` at its recorded open next step — Step 3, component 2 of 2, the χ² assembly and the program's closing statement `χ²(t, x) ≤ (λ*)^{2t} · ((π x)⁻¹ − 1)`: the centered density evolution, the connectivity kernel characterization of `L_sym` (the shelf's `laplacian_kernel_eq_span_onesVec` transferred through the proved congruence), and the gluing into the delivered contraction. Pure gluing plus one real-content piece; zero new axioms; this is the proposal's radar axis-5 re-score trigger.

**Changes:** intent, route, statement-shape decisions, and QA plan recorded in the execution plan before any edit. Pre-edit interface reading done: the contraction's `hmode`/`hrate` shapes, `chiSquareDistance_eq_sum_smul`, `chiSquareDistance_zero`, `exists_const_of_laplacian_mulVec_eq_zero`, and `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt` all confirmed on the shelf at the exact needed shapes; the QA connectivity technique (`SimpleGraph.connected_iff_exists_forall_reachable` + explicit walks) confirmed from `Connectivity_QA.lean`.

**Verification:** pending — module + QA elaboration, `#print axioms`, full build, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** the P₃ rate derivation needs two SOS certificates with `√2` atoms (the `path_one_add_one_QA` normalization-bridge technique may be needed); the disconnected-fixture spectrum derivation needs the "orthogonal to `e₃`" step through symmetry (`L_sym *ᵥ e₃ = 0` on that fixture) — both planned in the plan's QA section.

**Next handoff:** Lean implementation in `Normalized.lean` (+3 entry lemmas) and `Mixing.lean` (+4 theorems), then QA, verification, records.

## 2026-08-22T10:42:00Z — Mixing-time Step 3, component 1 delivered: the geometric decay engine

**Run:** `20260822T095344Z-run-1`  
**Session:** `ses_fd71c43f4ffeFVBbJiOzNG01En`  
**Status:** completed  
**Milestone:** `proposals/mixing-time-bound.md` Step 3, component 1 of 2 — the geometric decay engine (the authorized sub-decomposition of the program's hardest step): conjugated walk powers through the proved similarity, eigencoordinate evolution via a new generic center lemma, the Parseval-exact decay identity, and the hypothesis-shaped ℓ²(π) contraction under value-based mode exclusion. Pure hard crust, zero new axioms; component 2 (the χ² assembly) is the recorded open next step, all gluing on this delivery.

**Changes:** three public modules extended — `GraphTheory.Spectral` (+1 generic: `eigvecOf_dotProduct_one_sub_mulVec`, the `1 − M` eigenaction), `GraphTheory.Normalized` (+2: the commutation form `√D · P = (1 − L_sym) · √D` and the conjugated-power transfer `√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)`), `GraphTheory.Mixing` (+5: eigencoordinate evolution, the Parseval-exact identity, the norm-form contraction, the π-norm bridge, and the π-form headline contraction); `Mixing_QA.lean` 33 → 67 declarations (the triangle K₃ with basis-independent eigen-facts and *exact* decay `2 → 1/2 → 1/8` at rate `1/2`; the P₃ λ* = 1 oscillation cross-check tying the engine to the pinned `χ²(2) = 1`; the mode-hypothesis negative witness). Records: proposal (status header, delivery record, open-next-step → numbered component-2 list), `proposals/README.md` (Medium row, progress paragraph, Delivered row), scoreboard (1162/10/0, narrative rows, interpretation bullet), radar (axis-5 hold entry + QA count sync 1162/36, held), README (counts, proved list, module table), SGT index map (+5 rows and supporting-additions note), backlog item 2, the execution plan, this log. The worktree's unrelated operator-side changes (the untracked `proposals/prove-subgaussian-tail-bound.md` + its README row) and the uncommitted-but-delivered Step-2/Phase A work are preserved untouched.

**Decisive commands and outcomes:** `lake env lean` on `Spectral.lean`, `Normalized.lean`, `Mixing.lean`, `Mixing_QA.lean` — zero errors each; `Mixing`/`Mixing_QA` zero warnings, `Spectral`/`Normalized` only their documented pre-existing diagnostics; `#print axioms` on all eight new public theorems and thirteen headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2227 targets, "Build completed successfully", detached log, zero errors)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1162 QA declarations / 10 explicit axioms / 0 sorries**; `Mixing_QA` a 33 → 67 file row).

**Verification:** the delivery is fully proved hard crust — nothing axiom-backed was added, no `sorry` anywhere. The QA is load-bearing in both directions: the K₃ positive witness pins the contraction's both sides by raw literal arithmetic with the bound *attained exactly* at two time steps (the decay is genuinely geometric at rate `1/4` per step-pair), and the negative witness refutes the hypothesis-free form while separately proving the mode hypothesis unsatisfiable at the kernel index. The eigen-facts the instances consume are derived without controlling Mathlib's classical eigenbasis (unit norm + entrywise eigen equation + linear arithmetic; the kernel index's existence from trace vs `9/2`).

**Remaining risk:** low for what is delivered — every interface component 2 consumes is now on the shelf and QA'd. The component-2 risks are named in the proposal's open-next-step list: the kernel characterization `ker L_sym = span{√D·1}` under connectivity (transferring the shelf's `laplacian_kernel_eq_span_onesVec` through the similarity) is the one piece with real content left. One pin-specific API discovery recorded in the plan for future QA: this snapshot's sum-subtraction lemma is `Finset.sum_sub_distrib`, and `linear_combination` takes the exact coefficient expression (sign mattered).

**Next handoff:** mixing-time **Step 3, component 2** — the χ² assembly (centered evolution `h_t − 1 = Pᵗ(h₀ − 1)`; connectivity kernel-orthogonality; the final `χ²(t, x) ≤ (λ*)²ᵗ · ((π x)⁻¹ − 1)` instantiated on the existing K₃/P₃ fixtures) — per the proposal's numbered gluing list. Or the other Medium rows by leverage (Relative Entropy; the subgaussian tail bound Step 0; Perron–Frobenius + directed operators Step 0; the Cheeger hard-direction survey; approximate spectral projection Step 0).

## 2026-08-22T10:02:19Z — Mixing-time Step 3, component 1: the geometric decay engine

**Run:** `20260822T095344Z-run-1`  
**Session:** `unavailable` (to be established before the terminal entry)  
**Status:** in-progress  
**Milestone:** `proposals/mixing-time-bound.md` at its recorded open next step — Step 3, executed as the sub-decomposition the proposal itself licenses ("likely the hardest single step... may need its own sub-decomposition across runs"). Component 1 of 2: the decay engine — conjugated matrix powers through the proved similarity, eigencomponent evolution, the Parseval-exact decay identity, and the hypothesis-shaped ℓ²(π) contraction. Zero new axioms; hard crust load-bearing on the Step-1 transfer, the shelf's eigenbasis layer, and Parseval. Component 2 (the χ² assembly with the connectivity kernel characterization) stays a later dedicated run.

**Changes:** intent and route recorded in the execution plan (statement-shape decisions made before stating: value-based mode exclusion over index-based — it keeps the theorem true unconditionally on degenerate graphs; hypothesis-shaped rate `r`; no decorative sign hypothesis; π-form headline). Pre-edit API survey done: `Matrix.dotProduct_sub`, `pow_le_pow_left`, `sq_le_sq'`, `Matrix.mulVec_mulVec`, `pow_succ'` all present on the pin; the generic `1 − M` eigenaction lemma is absent from the shelf (to be added to `Spectral.lean`).

**Verification:** pending — module + QA elaboration, `#print axioms`, full build, lint/citation/link checks, scoreboard regeneration at the milestone boundary.

**Remaining risk:** the K₃ QA mode/rate derivations go through Mathlib's classically-chosen eigenbasis; the plan avoids naming basis vectors (only unit-norm, the eigen equation, and entrywise linarith), the DavisKahan_QA technique.

**Next handoff:** Lean implementation, then verification and record updates.

## 2026-08-21T22:51:25Z — Davis–Kahan Step 1, component 1 delivered: the equal-rank projector identity

**Run:** `unavailable` (interactive completion; the autonomous continuation run that did the Lean work was `20260821T175629Z-run-1`)  
**Session:** `unavailable`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Davis–Kahan Step 1, component 1 of 2 — the equal-rank projector identity `‖P − Q‖ = ‖(I−Q)P‖` for real symmetric idempotent matrices of equal rank, in the new public module `Analysis/OperatorTheory/Perturbation/ProjectionGap.lean`, zero new axioms, with QA. This closes out the milestone the two prior 2026-08-21 runs (`20260821T133507Z-run-1`, `20260821T175629Z-run-1`) left in progress: both hit their step limit mid-verification — the first left the module drafted but unelaborated, the second elaborated it clean (~1570 lines, all five sections) and wrote QA down to a single remaining `rewrite` failure before running out of steps.

**Changes:** (1) Fixed the one remaining QA error in `ProjectionGap_QA.lean` (`max_form_unequal_rank_QA`, line 585): the rewrite list's final item, `diff_one_opNorm_QA`, was redundant — by that point the goal had already collapsed to the numeric tautology `0 ⊔ 1 = 0 ⊔ 1` via the preceding three rewrites, so the pattern it hunted for no longer existed; dropped it from the list. Also removed a dead `all_goals try norm_num` (line 534, flagged by the linter as never executed). (2) Wired the umbrella: `Scaffold.lean` now imports `Analysis.OperatorTheory.Perturbation.ProjectionGap`. (3) Records: `docs/EXECUTION_PLAN.md` milestone closed (component 1 DELIVERED, component 2 opened as the next milestone), `proposals/discharge-perturbation-axioms.md`'s "Open next step" updated, `proposals/README.md`'s Medium row and progress paragraph updated, `index/map/perturbation.md` gained a new "Equal-Rank Projector Identity" section (4 declarations), `README.md`'s module table and QA count updated, scoreboard regenerated. The SGT Radar was deliberately left unchanged — `davis_kahan_sin_theta` itself is still an admitted axiom (only one of its two required components is delivered), and this repo's convention re-scores an axis only when a capability actually lands, not on partial progress toward it.

**Decisive commands and outcomes:** `lake env lean` on both changed files — zero errors, zero warnings on each; `#print axioms` on every public `ProjectionGap` theorem (from the prior run's record, re-confirmed by the clean compile): `propext, Classical.choice, Quot.sound` only; full `lake build` — **2186/2187 targets, "Build completed successfully"**, only the documented pre-existing `Derived/ProjectorDrift.lean` `hγ` warning; `lint_axioms` (**11**, unchanged), `check_citations`, `check_markdown_links` all pass; scoreboard regeneration — QA declarations **998 → 1035** (37 new: the `ProjectionGap_QA` file), axioms unchanged at 11. The `scaffold-pursue` LaunchAgent was deliberately unloaded (`launchctl bootout`) before this work began, to avoid a collision with the hourly autonomous trigger while editing shared state files, and is to be re-bootstrapped after this entry is committed.

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added. `#print axioms` confirms no hidden trust boundary. The QA fixture (30°-rotation realized as the 3-4-5 Pythagorean triple, `sin θ = 3/5`) pins the headline identity by two independent routes plus a rank-mismatch guard refuting the hypothesis-free form.

**Remaining risk:** low for what's delivered — the one-line fix was a mechanical redundant-rewrite removal, not a proof-shape change, and the surrounding ~1570/600 lines were already elaborated clean by the prior run. The larger open risk is unchanged from the Step-0 survey: component 2 (the Duhamel/FTC assembly) is the harder, less-predictable half, not yet started.

**Next handoff:** Davis–Kahan Step 1, **component 2** — the Duhamel/FTC assembly consuming this identity plus the spike-verified semigroup primitives (`wip/dk_spike.lean`) — as its own dedicated run, per the proposal's one-step-per-run discipline. Do not bundle it with component 1's cleanup in the same run in the future; today's two runs each hit their step limit on a single component alone.

## 2026-08-21T13:35:07Z — Davis–Kahan Step 1, component 1: the equal-rank projector identity (hard crust)

**Run:** `20260821T133507Z-run-1`  
**Session:** `ses_fdb8aca45ffe3YCyELhEpdARZv`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` at its recorded open next step — Davis–Kahan Step 1, executed as the authorized two-component split's first half: the equal-rank projector identity `‖P − Q‖ = ‖(I−Q)P‖` for real symmetric idempotent matrices of equal rank, as its own hard-crust delivery (new public module, zero new axioms, QA). Shrinks the path to the largest remaining axiom retirement; the Duhamel/FTC assembly (component 2) stays a later dedicated run.

**Changes:** intent recorded in the execution plan. Pre-edit shelf survey (read-only): this Mathlib pin has **no** AB/BA characteristic-polynomial lemma (Charpoly files read; `Analysis/Matrix.lean` is sup/Frobenius norms only) — but `Analysis/CStarAlgebra/Matrix.lean` has the whole `Matrix.L2OpNorm` C*-layer (`l2_opNorm_conjTranspose_mul_self`, `l2_opNorm_mul`, `l2_opNorm_mulVec`), and Scaffold's own Courant–Fischer counting lemmas plus Parseval/eigenaction identities (`dotProduct_eigvecOf`, `dotProduct_eigvecOf_mulVec`, `eigvecOf_expansion_apply`, `finrank_span_eigvecOf_finset`, `card_filter_eigvalOf_lt_evals_le`) route the entire proof without charpoly machinery. Route recorded in the plan before any module edit.

## 2026-08-21T07:43:00Z — Davis–Kahan Step 0 survey delivered; citation mislocation repaired; route spike-verified

**Run:** `20260821T072042Z-run-1`  
**Session:** `ses_fdcda3324ffeLkwyWOg7bVGO07`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` at its recorded open next step — the Davis–Kahan Step 0 survey (top Medium item; no High rows remain). Delivered as a decisive **positive-with-large-cost** record: the YWS paper read in full, the proof route named and its primitives spike-verified proved, the 600–1000-line Step-1 estimate recorded, and the citation mislocation the survey surfaced repaired in four files. No axiom statements changed; explicit axioms stay 11; no `sorry` anywhere.

**Changes:** (1) **Citation repair**: the axiom's provenance note paired "YWS Theorem 2" with "constant 1" — a pairing absent from the paper, whose actual Theorem 2 is population-gap/Frobenius/constant-2 (Weyl + Wielandt–Hoffman + Kronecker Sylvester); the repo's mixed-gap operator-norm constant-1 statement is the paper's **Theorem 1** (classical DK restated, operator-norm variant noted there) at the bottom cluster — single-pair δ equivalence by sortedness re-verified, constant-1 tightness re-verified numerically (2×2 rotation family: sinθ ≈ 0.0985 vs bound ≈ 0.0990, asymptotically attained). Corrected with dated notes: `DavisKahan.lean` docstring, `index/sources/davis_kahan_1970.md`, `index/map/perturbation.md`, `docs/2_ARCHITECTURE.md` §12. (2) **Route record** in the proposal: the entrywise eigenbasis-coordinate identity caps at Frobenius shape (√(k+1) constant — exactly YWS Thm 2's `d^{1/2}` numerator) so it cannot discharge the exact statement; constant-1 operator-norm needs the Duhamel/exponential integral `(I−Q)P = ∫₀^∞ e^{-tÃ}(I−Q)E e^{tA}P dt` (the mixed gap *is* side separation ⇒ `e^{-tδ}` decay; semigroups at vector level, no `Matrix.exp`) plus the equal-rank projector identity `‖P−Q‖ = ‖(I−Q)P‖` (principal angles; required since the reverse cross-gap degrades through Weyl to `δ − 2‖E‖`; the tempting `(P−Q)²` decomposition refuted by a worked 2×2 example). (3) **Spike** `wip/dk_spike.lean` (git-ignored): five primitives PROVED, all `#print axioms`-clean — `heatApply` (damped-eigenbasis semigroup), its adjoint/expansion workhorse, Parseval damping, eigenaction, `HasDerivAt` in `t` (this pin needs explicit `Analysis.Calculus.Deriv.Add` + `Analysis.SpecialFunctions.ExpDeriv` imports — not transitive through `GraphTheory.Spectral`), and the reducing commutation `spectralProjector M hM c * M = M * spectralProjector M hM c` (+`mulVec` form; `Matrix.IsSymm.apply` for entry symmetry). (4) Proposal Status header, per-axiom item 2 closed, Open-next-step → authorized Step 1 as a dedicated run; `proposals/README.md` Medium row + progress paragraph (top next candidate now the Step 1 retirement itself); scoreboard regenerated (idempotent, 998/11/0).

**Decisive commands and outcomes:** `lake env lean` on the changed module and both consumers — `DavisKahan.lean` zero errors/warnings (docstring-only change), `DavisKahan_QA.lean` clean, `Derived/ProjectorDrift.lean` only the documented pre-existing `hγ` warning; the spike elaborates end-to-end with all three `#print axioms` reads = `propext, Classical.choice, Quot.sound`; `lint_axioms` (11), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (998/11/0). Environment healthy at run start (5387 Mathlib oleans at the corrected path; no fetch needed).

**Verification:** the survey gate is satisfied per the proposal's own contingency pattern — findings recorded in the proposal *before* any Step-1 edit, and Step 1 was not started. Nothing axiom-backed was added or altered; the delivery is a survey record plus proved spike primitives (scratch) plus a citation-fidelity repair with no statement changes.

**Remaining risk:** the Step-1 estimate is an estimate — the equal-rank projector identity is the least-predictable component (moderate-large; principal-angles route), and the FTC assembly carries analysis-API friction (scalar `intervalIntegral`, improper limit). The spike covered the semigroup/algebra layer only, not the integration. The citation repair rests on the paper as published at arXiv:1405.0680v1 (Annals of Statistics 43(3):2028–2061); the Davis–Kahan 1970 primary-source §3 locator remains section-level as before.

**Next handoff:** Davis–Kahan **Step 1** — authorized, dedicated run, optionally split (equal-rank lemma first as its own hard-crust delivery, then the Duhamel assembly); or the other Medium rows by leverage (mixing-time Step 1; Reversibility Phase A; Relative Entropy; Perron–Frobenius + directed operators Step 0; Cheeger hard-direction survey under its known-hard assumption; approximate spectral projection Step 0; Fiedler Phase B awaits an operator decision).

## 2026-08-21T07:22:00Z — Davis–Kahan Step 0 survey (sin-Θ tractability)

**Run:** `20260821T072042Z-run-1`  
**Session:** `ses_fdcda3324ffeLkwyWOg7bVGO07`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` at its recorded open next step — the Davis–Kahan Step 0 survey (no High rows remain in the Active table; this is the top Medium item by the recorded leverage ranking, shrinking the mushy center). Scope: what a proof at the axiom's exact statement needs vs. the shelf, a scratch spike of the decisive primitive, findings recorded in the proposal before any Step-1 edit, plus the citation repair the survey itself surfaced.

**Changes:** intent recorded in the execution plan. Survey evidence gathered: the YWS paper (arXiv:1405.0680) fetched and read in full — finding: the axiom's provenance note mislocates the statement (the paper's Theorem 2 is population-gap/Frobenius/constant-2; the repo's mixed-gap/operator-norm/constant-1 statement is the paper's Theorem 1 with its noted operator-norm variant, at the bottom cluster — the single-pair-δ equivalence by sortedness still holds). Route analysis: the entrywise eigenbasis-coordinate identity closes only at Frobenius shape (√(k+1) constant); constant-1 operator-norm needs the Duhamel/exponential-integral representation plus the equal-rank projector identity. Spike to follow in `wip/dk_spike.lean` (ignored); then the proposal's Step-0 record, the docstring/index citation fix, and verification.

## 2026-08-21T04:59:08Z — Spectral band projectors, Step 4 delivered (the Hilbert-projection specialization); program complete

**Run:** `20260821T040302Z-run-1`  
**Session:** `ses_fdd8410deffe43MaMPuIN14Gyc`  
**Status:** completed  
**Milestone:** The Active priority table's only High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 4, the program's last — delivered as pure hard crust, **zero new axioms** (count stays 11; `#print axioms` on all three new public theorems reads only `propext, Classical.choice, Quot.sound`). The band-projector program is complete: Steps 1–3 on 2026-08-20, Step 4 on 2026-08-21, one step per run throughout.

**Changes:** `GraphTheory.Band` gained the Step-4 section (with the two Mathlib imports `Analysis.InnerProductSpace.{Projection,PiL2}`): `bandProjector_residual_dotProduct_eq_zero` (the residual-orthogonality engine `(x − B*ᵥx) ⬝ᵥ (B*ᵥz) = 0` — load-bearing on exactly the two Step-1 facts, symmetry and idempotence), `bandProjector_toEuclidean_apply_eq_orthogonalProjection` (the identification: Mathlib's `orthogonalProjection` at `LinearMap.range (toEuclideanLin B)` *is* the band-filtered signal — the SGT center's first consumption of `Analysis/InnerProductSpace/Projection.lean`), and `norm_sub_bandProjector_apply_le` (the closest-point property over the band's fixed space, from `orthogonalProjection_minimal` + the conditionally-complete `ciInf_le`). Statement shapes recorded before stating: at `EuclideanSpace ℝ V` (the bare `V → ℝ` default norm is the sup norm), fixed-point hypothesis form over the membership existential, range form over an eigenspace-span form (coincide for idempotent self-adjoint projectors; span-form agreement is the proposal's named residual). QA `SpectralGraph/Band_QA.lean` +25 (109 in file, 998 total): the identification pinned to the packaged band image; minimality **attained** (distance exactly `4`), **strict over the zero signal** (`4 ≤ 5`, the 3-4-5 triangle), **generic over the whole range line** (`4 ≤ √((3−t)²+16)`) with `band_diag13_hilb_min_line_raw` reproducing the identical inequality from bare square-positivity — an independent hand-check; the high band instantiated; the residual engine by theorem and raw routes; and the **fixed-space guard** refuting the hypothesis-free form at the unfiltered signal (`0 < 4`, not band-fixed). Records: module/QA/umbrella docstrings, scoreboard (998/11/0, both Direct rows + the `lake build` row prepended/extended with the Step-4 slice, new interpretation bullet, provenance run events), radar (**axis 2 re-scored 4.0 → 4.5** — the capability dimension the Step-1/Step-3 records explicitly reserved as the trigger; QA 998/34, QA axis **held at 4.0**; both logged), README (998/11; proved list extended; coverage snapshot's spectral-linear-algebra row synced 3.5 → 4.5, stale since the Tikhonov re-score), SGT index map (Band section header + 3 rows), proposal (program-complete status header, Step-4 delivery record, open-next-step → none), `proposals/README.md` (High row removed, Delivered row added, progress paragraph rewritten — **no High rows remain**), execution plan. The operator's concurrent plist path edit is preserved untouched.

**Decisive commands and outcomes:** `lake env lean` on `Band` and `Band_QA` — zero errors, zero warnings (public module after two argument-shape fixes: this snapshot's `LinearMap.mem_range` has no explicit arguments and `orthogonalProjection_minimal` takes its submodule implicitly; `iInf_le` does not apply over ℝ — `ciInf_le` with a `BddBelow` witness of `0` does; QA after three proof-shape fixes: a simp-closes-goal `norm_num` trap, a symbolic dot-product `ring` residue, and a `rw`-all-occurrences scope trap replaced by `calc`); `#print axioms` on 3 public + 9 headline QA theorems — only `propext, Classical.choice, Quot.sound`; oleans built during iteration (`lake build Scaffold.Mathlib.GraphTheory.Band` / `…Band_QA`); **all thirty-four QA modules batch-elaborated — BATCH-DONE total=34 fail=0** (one mid-batch restart at the 10-minute tool timeout — no state damage, `lake env lean` does not replay traces); **full `lake build` ✔ (2186 targets, "Build completed successfully")**, detached log + poll per the recorded procedure; `lint_axioms` (11), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (**998/11/0**). Environment healthy at run start (correct-path olean check: 5387 present, no fetch).

**Verification:** every changed module elaborated directly with zero errors/warnings and linked in the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The identification and minimality are load-bearing on the Step-1 algebra (the residual engine consumes symmetry and idempotence exactly), and the fixed-space hypothesis is refutable-on-omission (the QA guard). The proposal's mandatory signature survey found the entire needed shelf in the pinned Mathlib; the stop-and-record clause was not triggered.

**Remaining risk:** low — Step 4 is one orthogonality computation plus Mathlib's projection API over the already-QA'd band machinery, with an independent raw-arithmetic cross-check and the hypothesis guard. The `a > b` junk region remains documented-not-guarded (no theorem claims anything there). The span-form agreement (range vs. in-band-eigenspace span) is the proposal's named residual, not delivered.

**Next handoff:** with no High rows remaining, the next run selects among the Medium rows by leverage (as ranked in `proposals/README.md`): the Davis–Kahan Step 0 survey (`discharge-perturbation-axioms.md` — shrinking the mushy center, tractability genuinely unknown), mixing-time Step 1, Reversibility Phase A, Relative Entropy, Perron–Frobenius + directed operators (Step 0 first), or approximate spectral projection (Step 0 first). Fiedler Phase B still needs an operator decision.

## 2026-08-21T04:08:11Z — Spectral band projectors, Step 4 (the Hilbert-projection specialization)

**Run:** `20260821T040302Z-run-1`  
**Session:** `ses_fdd8410deffe43MaMPuIN14Gyc`  
**Status:** in-progress  
**Milestone:** The Active priority table's only High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 4, the Hilbert-projection specialization, the program's last step: the band projector's output is the closest point in its range to the input, by instantiating Mathlib's Hilbert projection theorem at the band's range. Pure hard crust, zero new axioms (the proposal forbids them and mandates a recorded obstruction if the shelf lacks needed machinery).

**Changes:** intent + route recorded in the execution plan. The proposal's mandatory pre-step survey ran against the pinned snapshot and found everything needed: `eq_orthogonalProjection_of_mem_of_inner_eq_zero` (the identification lemma), `orthogonalProjection_minimal` + `iInf_le` (minimality), `HasOrthogonalProjection.ofCompleteSpace` (instance), and the `inner_piLp_equiv_symm` (`rfl`) + `toEuclideanCLM_piLp_equiv_symm`/`toLin'_apply` transport spine — the resolvent Step-0 precedent. Route: the residual-orthogonality engine `(x − B*ᵥx) ⬝ᵥ (B*ᵥz) = 0` (symmetry + idempotence, both Step-1 facts) feeding the identification at `K = range (toEuclideanCLM B)`; statements at `EuclideanSpace ℝ V` (the bare `V → ℝ` norm instance is the sup norm — deliberately not used). Planned QA: minimality attained with equality in-band and strict on the 3-4-5 signal (`4 < 5`), identification instantiated, fixed-space guard refuting the hypothesis-free form. Environment healthy at run start (5387 Mathlib oleans; the pruned-oleans state did not recur). Lean work to follow in `GraphTheory/Band.lean` and `QA/SpectralGraph/Band_QA.lean`.

## 2026-08-21T00:51:34Z — Spectral band projectors, Step 3 delivered (completeness under a partition)

**Run:** `20260820T210049Z-run-1`  
**Session:** `ses_fdf0afe0cffeISDycxodu6Lgfc`  
**Status:** completed  
**Milestone:** The Active priority table's only remaining High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 3, completeness under a partition — delivered as pure hard crust, **zero new axioms** (count stays 11; `#print axioms` on all four new public theorems reads only `propext, Classical.choice, Quot.sound`). The proposal's one-step-per-run rule was honored: Step 4 (the Hilbert projection specialization) untouched.

**Changes:** `GraphTheory.Band` gained the Step-3 section: `sum_range_bandProjector_eq_sub` (the **unconditional telescoping law** `∑_{k<n} B(t_k, t_{k+1}) = P_{t_n} − P_{t_0}` for *any* threshold sequence, ordered or not — range-succ induction with an `abel` residue, load-bearing on the band definition's exact difference shape), `sum_range_bandProjector_eq_one` (**completeness**: a family starting strictly below every eigenvalue and ending at-or-above them all resolves the identity — exactly the two endpoint covering hypotheses, both load-bearing), `bandProjector_mul_bandProjector_eq_zero_of_monotone` (distinct members of a **monotone** family compose to zero — the recorded statement-shape decision: monotonicity is deliberately *not* a hypothesis of the sum identity since telescoping does not consume it; it is exactly what this theorem consumes via Step 2's disjointness, making the family a *partition* rather than a sequence), and `sum_range_bandProjector_mulVec_eq_self` (the consumer's form `∑ B_k *ᵥ x = x`, through the inlined `mulVec` analog of `Matrix.sum_mul`). QA `SpectralGraph/Band_QA.lean` +41 (84 in file, 973 total): the covering two-band family summed to the identity through the theorem *and* from independently pinned band values; a three-band partition with an **empty middle band** and its top threshold exactly touching the top eigenvalue (the closed right endpoint); the **two endpoint guards** — a family starting above the lowest mode and a family truncated below the highest each provably fails to sum to the identity, each violated covering hypothesis separately refuted (the design note's "silently ignores modes" failure mode, witnessed in both directions); the **non-monotone telescoping witness** (family `4, 0, 4`: junk band `−1` cancelling covering band `1`, both sides independently `0`); and the vector decomposition on a concrete signal by both routes. Records: module/QA/umbrella docstrings, scoreboard (973/11/0, both Direct rows prepended with the Step-3 slice, the `lake build` row extended, the Step-3 interpretation bullet, the provenance note amended with a **wrong-path olean-presence-check correction** — the layout has no `lean/` level, so the old check pattern returns 0 with the full set present; the correct check is a `find`-based count at the package build root), radar (axis 2 completeness layer, **held at 4.0** per protocol — same-family completion, with Step 4 named the natural re-score trigger as it consumes Mathlib's inner-product-space machinery; QA 973/34, **held at 4.0**; both holds logged), README (973; proved list gains partition completeness), SGT index map (Band section +4 rows, Steps 1–3), proposal (Step-3 delivery record + status header + open-next-step → Step 4), `proposals/README.md` (High row note, Delivered row, progress paragraph — Step 4 now the top of the Active table), execution plan.

**Decisive commands and outcomes:** `lake env lean` on `Band` and `Band_QA` — zero errors, zero warnings (public module first pass; QA after two proof-shape fixes: this snapshot's `Finset.sum_range_succ` appends the new term on the *right* (`f 0 + f 1 + …`, with no `Finset.sum_range_two`/`Nat.cast_mono` available), and the `rw`-closes-`3 ≤ 3`-by-itself linter trap behind one warning); `#print axioms` on 4 public + 13 QA headline theorems — only `propext, Classical.choice, Quot.sound`; oleans produced by the recorded fast `lean -o` path; **all thirty-four QA modules batch-elaborated — BATCH-DONE total=34 fail=0**; **full `lake build` ✔ (2186 targets, "Build completed successfully")**, executed detached (log + poll) after the run's first invocation was killed at its 300 s tool timeout during Mathlib trace replay — the olean set verified intact afterward by the corrected presence check, so no re-fetch was needed (one redundant idempotent re-fetch had already run); `lint_axioms` (11), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (973/11/0).

**Verification:** every changed module elaborated directly with zero errors/warnings and linked in the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The completeness statement is load-bearing on the band definition's exact difference shape (the non-monotone QA witness would fail against a sign-flipped or transposed definition), and both covering hypotheses are refutable-on-omission (the two endpoint guards).

**Remaining risk:** low — Step 3 is one induction plus endpoint algebra over the already-QA'd projector machinery, with dual-route summation checks and both endpoint guards. The `a > b` junk region remains documented-not-guarded (no theorem claims anything there). Step 4 of the proposal (the Hilbert projection specialization — survey `Analysis/InnerProductSpace/Projection.lean` signatures first) remains open.

**Next handoff:** the same proposal's Step 4 — the Hilbert-projection-theorem specialization (the program's last step; the `toEuclideanCLM` transport spine from the resolvent Step-0 record is the precedent for the `EuclideanSpace`-to-matrix transport); or the queued Medium rows (Fiedler Phase B — needs an operator decision; mixing-time Step 1; Reversibility A and B; Relative Entropy; Perron–Frobenius + directed operators; discharge-perturbation — the Davis–Kahan Step 0 survey; approximate spectral projection).

## 2026-08-20T21:00:49Z — Spectral band projectors, Step 3 (completeness under a partition)

**Run:** `20260820T210049Z-run-1`  
**Session:** `ses_fdf0afe0cffeISDycxodu6Lgfc`  
**Status:** in-progress  
**Milestone:** The Active priority table's only remaining High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 3, completeness under a partition: for a threshold family covering the spectral range, the sum of the consecutive band projectors is the identity — pure hard crust, zero new axioms (count stays 11; the proposal's one-step-per-run rule keeps Step 4 queued).

**Changes:** intent + route recorded in the execution plan. Route: an *unconditional* telescoping law `∑_{k<n} B(t_k, t_{k+1}) = P_{t_n} − P_{t_0}` (range-succ induction, `abel` residue — load-bearing on the band definition's exact difference shape); completeness from the two endpoint covering hypotheses only; monotone-family orthogonality as its own theorem (where monotonicity is load-bearing, per the no-decorative-hypotheses discipline); consumer vector form `∑ B_k *ᵥ x = x`. Planned QA: partition witness (theorem + independent band-value routes), empty-middle three-band partition touching the closed top endpoint, both endpoint guards (refuting the hypothesis-free form — the design note's "silently ignores modes" failure mode), non-monotone telescoping witness, vector form. Environment: the pruned-oleans state recurred at run start; the recorded interpreted cache fetch restored 5685 ("Unpacked in 22688 ms"). Lean work to follow in `GraphTheory/Band.lean` and `QA/SpectralGraph/Band_QA.lean`.

## 2026-08-20T20:23:00Z — Spectral band projectors, Step 2 delivered (orthogonality of disjoint bands)

**Run:** `20260820T171956Z-run-1`  
**Session:** `ses_fdfd37fa6ffeT8EAoVx1GrUhr4`  
**Status:** completed  
**Milestone:** The Active priority table's only remaining High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 2, orthogonality of disjoint bands — delivered as pure hard crust, **zero new axioms** (count stays 11; `#print axioms` on all four new public theorems reads only `propext, Classical.choice, Quot.sound`). The proposal's one-step-per-run rule was honored: Steps 3–4 untouched. (Count correction: the in-progress entry above said 12 — the verified count has been 11 since the operator-directed `spectral_persistence` removal earlier on 2026-08-20; the scoreboard authority confirms 11.)

**Changes:** `GraphTheory.Band` gained the Step-2 section: `bandProjector_mul_bandProjector_eq_zero` / `_eq_zero'` (bands over disjoint intervals compose to zero in **both orders**, by exactly the paved route — the Step-1 cross-law's ordered forms expand `(P_b − P_a)(P_d − P_c)` to the four-term expression that collapses under the ordering; the flipped theorem is a direct expansion through `_of_le'`, not a transpose wrapper), `bandProjector_inner_eq_zero` (the consumer's form: `(B_{a,b} *ᵥ x) ⬝ᵥ (B_{c,d} *ᵥ y) = 0`, the first band moved across the dot product through `vecMul_transpose`/`dotProduct_mulVec`/`vecMul_vecMul`), and `eq_zero_of_bandProjector_mulVec_eq_self` (the subspace-level reading of the step's "they share no eigenvector": a vector fixed by two disjoint bands is zero). The hypothesis set is folded to `a ≤ b`, `c ≤ d`, `b ≤ c` — `b ≤ c` is exactly interval disjointness and is load-bearing. QA `SpectralGraph/Band_QA.lean` +16 (43 in file, 932 total): composition to zero through the theorem *and* by raw literal multiplication in both orders; image orthogonality by both routes with the **same-band counter-witness** (`1 ≠ 0`, separating disjointness from fixture zeros); the composed action annihilating a filtered signal; and the **overlap guard** — bands `(−1, 3]` and `(1, 4]` sharing the eigenvalue `3` compose to the provably nonzero `diag(0,1)`, refuting the hypothesis-free form. Records: module/QA/umbrella docstrings, scoreboard (932/11/0, both Direct rows prepended with the Step-2 slice, `lake build` row extended, Step-2 interpretation bullet, cache-provenance invocation note, two stale narrative counts fixed — lint row 12 → 11 axioms, QA-definition line 917 → 932), radar (axis 2 orthogonality layer, **held at 4.0** per protocol; QA 932/34, **held at 4.0**; both holds logged), README (status table synced to the scoreboard authority 11/932; proved list extended), SGT index map (Band section +3 rows, Steps 1–2), proposal (Step-2 delivery record + status header + open-next-step → Step 3), `proposals/README.md` (High row note, Delivered row, progress paragraph), execution plan.

**Decisive commands and outcomes:** `lake env lean` on `Band` and `Band_QA` — zero errors, zero warnings (public module first pass; QA needed three small proof-shape fixes, one traced to `rw` closing `3 ≤ 3` unassisted, the cause of the only linter warning seen); `#print axioms` on 4 public + 12 QA headline theorems — only `propext, Classical.choice, Quot.sound`; oleans produced directly during iteration; **all thirty-four QA modules batch-elaborated — BATCH-DONE fail=0**; **full `lake build` ✔ (2186 targets, "Build completed successfully")**, executed detached from the tool timeout (log + poll) with the only diagnostic the documented pre-existing `hγ` warning in `ProjectorDrift.lean`; `lint_axioms` (11), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (932/11/0). Environment: the pruned-oleans state recurred at run start; the interpreted cache fetch restored 5387 ("Unpacked in 21270 ms"); invocation note recorded — under `lake --dir`, the `--run` file argument resolves relative to the cwd, so invoke from the repo root with the full package-relative path.

**Verification:** every changed module elaborated directly with zero errors/warnings and linked in the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional; the orthogonality statements are load-bearing on the Step-1 cross-law (a wrong cross-law would leave a nonzero four-term residue and fail both the theorem route and the raw-literal QA route).

**Remaining risk:** low — Step 2 is four-consequence algebra over the already-QA'd cross-law, with both composition orders dual-route-checked and the overlap guard refuting the hypothesis-free form. The `a > b` junk region remains documented-not-guarded (no theorem claims anything there). Steps 3–4 of the proposal (partition completeness, the Hilbert projection specialization) remain open.

**Next handoff:** the same proposal's Step 3 — completeness under a partition of the spectrum (the two-band covering instance `bandProjector_eq_one` already exists; Step 2 is the pairwise half), then Step 4 (survey `Analysis/InnerProductSpace/Projection.lean` signatures first); or the queued Medium rows.

## 2026-08-20T17:20:30Z — Spectral band projectors, Step 2 (orthogonality of disjoint bands)

**Run:** `20260820T171956Z-run-1`  
**Session:** `ses_fdfd37fa6ffeT8EAoVx1GrUhr4`  
**Status:** in-progress  
**Milestone:** The Active priority table's only remaining High row (`proposals/spectral-band-projectors.md`) at its recorded open next step — Step 2, orthogonality of disjoint bands: for bands `(a, b]` and `(c, d]` with `b ≤ c`, the two band projectors compose to zero in both orders and their images are orthogonal — pure hard crust, zero new axioms (count stays 12; the proposal's one-step-per-run rule keeps Steps 3–4 queued).

**Changes:** intent + route recorded in the execution plan (the Step-1 nestedness cross-law's ordered forms expand the band product to the collapsing four-term expression; `b ≤ c` is exactly interval disjointness, so the hypothesis is load-bearing — the QA plan includes an overlap guard refuting the hypothesis-free form). Environment: the pruned Mathlib-oleans state recurred at run start (0 present); the recorded interpreted cache fetch is running in the background. Lean work to follow in `GraphTheory/Band.lean` and `QA/SpectralGraph/Band_QA.lean`.

## 2026-08-20 — Strip "dynamic spectral persistence" framing from strategy docs (operator-directed, interactive session)

**Run:** `unavailable` (interactive Claude Code session)  
**Session:** `unavailable`  
**Status:** completed  
**Milestone:** Follow-up to the `spectral_persistence` axiom removal above.
The operator asked where else "spectral persistence" appears in the
repository; the answer was that it's a named strategic direction in
`AGENTS.md`'s Mission and Priority-order sections, in
`docs/1_STRATEGY.md`, and in `Azuma.lean`'s docstring — distinct from the
axiom itself, since the underlying proved modules
(`Derived/EventStream.lean`, `Derived/ProjectorDrift.lean`) rest on
legitimate axioms (Davis–Kahan, matrix Azuma-Hoeffding) and were not in
question. Given a choice between leaving it, stripping the framing while
keeping the proved math, or deleting the modules outright, the operator
chose **strip the framing, keep the math** — scoped explicitly to
`AGENTS.md`, `docs/1_STRATEGY.md`, and the `Azuma.lean` docstring; no
other file in the broader "persistence" grep footprint (`docs/2_ARCHITECTURE.md`,
`docs/3_SPECTRAL_THEORY.md`, `Spectral.lean`, the proposals mentioning
it) was touched, since they were outside the selected option.

**Changes:** `AGENTS.md` — the Mission sentence no longer names "dynamic
spectral persistence" and "x90 applications" as a direction to radiate
toward (replaced with a pointer to `docs/3_SPECTRAL_THEORY.md`'s own
retained-example status, which already disclaims itself as a roadmap
goal); Priority order item 6 reworded from "Advance dynamic persistence
and application work" to "Advance application-facing work." This also
fixes a standing internal inconsistency: `AGENTS.md` was telling
autonomous runs to advance toward persistence as a destination, while
`docs/1_STRATEGY.md` and `docs/3_SPECTRAL_THEORY.md` already said the
opposite ("not Scaffold's research goal," "do not extend... merely
because... available"). `docs/1_STRATEGY.md`'s paragraph reworded to
drop "already developed elsewhere" (inaccurate — it was developed in
this repository's own derived layer) while keeping the substantive
disclaimer. `Azuma.lean`'s docstring reworded to introduce matrix
Azuma–Hoeffding on its own terms (a real, independently citable
theorem) rather than via the persistence narrative, with a factual
pointer to its actual consumer (`eventStreamTail`) instead.

**Verification:** `lake env lean` on `Azuma.lean` — zero errors (the
other two edits are prose-only, in `.md` files);
`scripts/check_markdown_links.py` passes.

**Remaining risk:** none identified. This was a framing/wording change
with no effect on any theorem, axiom, or QA declaration; counts are
unchanged from the prior entry (11 axioms, 916 QA declarations).

**Next handoff:** none opened by this change.

## 2026-08-20 — `spectral_persistence` removed (operator-directed, interactive session)

**Run:** `unavailable` (interactive Claude Code session, not an
`opencode-pursue`/OpenCode wrapper invocation)  
**Session:** `unavailable`  
**Status:** completed  
**Milestone:** Remove the `spectral_persistence` axiom
(`Scaffold/Mathlib/GraphTheory/Dynamics.lean`) and its sole QA consumer,
per explicit operator instruction. Editorial removal, not a proof-based
retirement: the operator's stated criterion was that the axiom is not
well-established published math, unlike this repository's other
axioms — distinct from every prior retirement, which discharged a
citation-backed axiom by proof. A broader initial request to also scrub
all mentions from `research/archive/` was raised earlier in the same
session and declined (conflicts with `AGENTS.md`'s archive-immutability
rule and would falsify historical QA-coverage records); this narrower
Lean-source-only removal was carried out instead, at the operator's
explicit re-scoping ("remove the lean").

**Changes:** deleted `axiom spectral_persistence` and its docstring
section from `Dynamics.lean`; deleted its sole consumer
`persistence_zero_perturbation_QA` (and the `set_option
linter.deprecated false in` it required) from `Dynamics_QA.lean`; updated
both files' module docstrings to drop the persistence framing. Fixed a
dangling reference in `Scaffold/Derived/ProjectorDrift.lean`'s docstring
(previously named the axiom as an available-but-unused per-step route).
`TimeVaryingGraph`, `laplacianSequence`, `IsEventDriven`, and
`laplacianSequence_symmetric` are untouched — confirmed still consumed
by `Derived/EventStream.lean` and `Derived/ProjectorDrift.lean`/their QA
files via grep before editing, since those are the load-bearing building
blocks the derived layer's proved two-endpoint persistence chain
(`davisKahanTwoPoint`, `eventStreamProjectorDrift`) actually uses.
Synced: `index/map/spectral_graph.md` (removed the axiom's table row),
`index/map/perturbation.md`, `index/sources/davis_kahan_1970.md`
(removed the axiom's citation-mapping row; the `davis_kahan_sin_theta`
citation itself is untouched, since that axiom still stands),
`docs/2_ARCHITECTURE.md`, `docs/7_SGT_RADAR.md` (axiom-minimization trend
line), `README.md` (status table and trust-surface prose),
`docs/5_QA_SCOREBOARD.md` (regenerated metrics via
`scripts/generate_qa_scoreboard.py`, plus a new dated narrative bullet
and a trimmed now-resolved priority item), `docs/6_SGT_BACKLOG.md`
(appended an update note to the existing entry, not rewritten), and
`docs/EXECUTION_PLAN.md`. `cdx-clean-assess.md` (a dated point-in-time
audit snapshot) and `research/archive/` were deliberately left
untouched — both are historical record, not live documentation.

**Decisive commands and outcomes:** `lake env lean` on the three touched
Lean modules individually — zero errors on all three; one pre-existing,
unrelated `unused variable 'hγ'` warning in `ProjectorDrift.lean`
(confirmed present before this change, in code untouched by this edit —
the only change to that file was a documentation comment).
`scripts/generate_qa_scoreboard.py` regeneration: explicit axioms 12 →
11, QA declarations 917 → 916 (`Dynamics_QA.lean` 6 → 5). A full `lake
build` was not run for this change — not requested, and the edit makes
no signature changes to anything another module imports, so isolated
elaboration of the three touched files is the relevant check.

**Remaining risk:** low for correctness (the removed axiom had zero
non-QA consumers by its own deprecation record, confirmed again here by
grep before deletion). The larger judgment call — whether "not
well-established math" is the right bar for what belongs in this
repository's axiom set, and whether it should be applied to any other
axiom — was not evaluated here; this entry documents one instance
executed on explicit, scoped operator instruction, not a new standing
policy.

**Next handoff:** none opened by this change; the Active priority table
in `proposals/README.md` and the Active milestone in
`docs/EXECUTION_PLAN.md` (Spectral Band Projectors Steps 2–4) are
unaffected.

## 2026-08-20T13:39:48Z — Spectral band projectors, Step 1 (two-sided band projector)

**Run:** `20260820T133553Z-run-1`  
**Session:** `ses_fe0a0f4b6ffeOdvy2Pf5lWRbOv`  
**Status:** in-progress  
**Milestone:** The Active priority table's only remaining High row
(`proposals/spectral-band-projectors.md`) at its recorded open next step —
the two-sided band projector `bandProjector M hM a b := spectralProjector M hM b − spectralProjector M hM a`
with idempotence and self-adjointness, pure hard crust (zero new axioms), the
frequency-selective bandpass object named by the proposal's external consumer.

**Changes:** intent + route recorded in the execution plan (pre-edit survey:
the projector lemma set already has symmetry/idempotence/extremes — the
load-bearing missing piece is the nestedness cross-law
`P_{c₁} * P_{c₂} = P_{min c₁ c₂}`, from which band idempotence and the old
idempotence both derive). Environment: the pruned Mathlib-oleans state
recurred at run start (0 present); the recorded interpreted cache fetch
restored 5685 (`lake --dir=.lake/packages/mathlib env lean --run <pkg>/Cache/Main.lean get`).
Lean work starting in `GraphTheory/Spectral.lean` (cross-law + action pair)
and the new `GraphTheory/Band.lean` + `QA/SpectralGraph/Band_QA.lean`.

## 2026-08-20T16:26:39Z — Spectral band projectors, Step 1 (two-sided band projector)

**Run:** `20260820T133553Z-run-1`  
**Session:** `ses_fe0a0f4b6ffeOdvy2Pf5lWRbOv`  
**Status:** completed  
**Milestone:** The Active priority table's only remaining High row
(`proposals/spectral-band-projectors.md`) at its recorded open next step —
the two-sided `(a, b]` band projector with idempotence and self-adjointness,
pure hard crust (zero new axioms; count stays 12).

**Changes:** the new `Scaffold/Mathlib/GraphTheory/Band.lean`
(`bandProjector M hM a b := spectralProjector M hM b − spectralProjector M hM a`,
parameterized by interval per the design note, total definition with the
`a > b` junk documented; symmetry, idempotence at `a ≤ b`, the mode-selection
action interface — in-band fixed, below-/above-band annihilated — the
below-spectrum special case, the covering band `= 1`); enabling lemmas in
`GraphTheory.Spectral` (the nestedness cross-law
`spectralProjector_mul_spectralProjector` `P_{c₁} * P_{c₂} = P_{min c₁ c₂}`
with ordered forms — the pre-edit survey's route finding: idempotence of a
*difference* needs the cross-law, not just idempotence of the factors; the
old `spectralProjector_idempotent` re-derived from it at unchanged
statement, its 50-line proof now one rewrite; and the complete action
description `spectralProjector_mulVec_eigvecOf` with specializations); the
new `QA/SpectralGraph/Band_QA.lean` (27 declarations); the umbrella import
+ docstring; records (scoreboard, radar, README, SGT index map, proposal
status/delivery record/open-next-step, proposals README High row + Delivered
row + progress note, execution plan).

**Decisive commands and outcomes:** `lake env lean` on `Spectral`,
`Band`, and `Band_QA` — zero errors, zero warnings on the two new modules
(`Spectral`'s only diagnostics are the documented pre-existing
section-variable warnings); `#print axioms` on the seven public and nine
headline QA theorems — only `propext, Classical.choice, Quot.sound`; **all
thirty-four QA modules batch-elaborated, zero errors**; **full `lake build`
✔ — "Build completed successfully", 2186 targets, zero errors** (executed
detached from the tool timeout, log + poll, per the recorded recovery
procedure; the Mathlib residue replay ~2 h); `lint_axioms` (12),
`check_citations`, `check_markdown_links` pass; scoreboard regeneration
idempotent (**917/12/0**; `Band_QA` a new file row at 27). Environment: the
pruned-oleans state recurred at run start; the interpreted cache fetch
restored 5685 before any elaboration (`lake --dir=.lake/packages/mathlib env
lean --run <pkg-path>/Cache/Main.lean get` — `--dir` from the repo root,
since direct `cd` into the package is sandboxed). Implementation notes for
future projector QA: `fin_cases` eta-expanded `Fin` indices defeat
`rw`/`linarith` atom matching (coerce back with defeq-tolerant `have`s or
`show`, the recorded trap); `rw ... at` accepts only local hypotheses, not
theorem names (copy with `have` first); `linear_combination` likewise wants
local fvar atoms; `Finset.sum_ite_eq` matches `if b = x` and `sum_ite_eq'`
matches `if x = b`; `(if P then f else 0) k` distributes via `ite_apply`
(root namespace), not `apply_ite`; un-ascribed `!![..]` literals elaborate
as ℕ — ascribe `(!![..] : Matrix (Fin 2) (Fin 2) ℝ)`; type-ascribed `have`
is the bridge for `eigvecOf`/`eigvalOf` defs versus Mathlib's raw
`WithLp`-coerced spectral-theorem terms (the center's own idiom).

**Verification:** every changed module elaborated directly and built in the
full default build; QA covers both mode-selection directions with the
excluded-mode-not-fixed witness and the between-eigenvalues zero band (the
gapped-definition guard), the band values pinned against hand-computed
outer products on a diagonal fixture whose spectrum is pinned from
trace+determinant independent of the machinery under test.

**Remaining risk:** low — Step 1 is one-consequence algebra over the
already-QA'd projector machinery, with the new cross-law itself numerically
instantiated in both orders. The `a > b` junk region is documented, not
guarded; no theorem claims anything there. Steps 2–4 of the proposal
(orthogonality of disjoint bands, partition completeness, the Hilbert
projection specialization) remain open.

**Next handoff:** the same proposal's Step 2 — orthogonality of disjoint
bands (`a ≤ b ≤ c ≤ d`; the cross-law's ordered forms already expand
`(P_b − P_a)(P_d − P_c)` to the collapsing four-term expression), then
Steps 3–4; or the queued Medium rows.

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

## 2026-08-17 — Concentration-bridge repair

**Status:** in-progress  
**Milestone:** Recover the probability/concentration bridge (all six
`Probability.Concentration` modules) on real Mathlib probability interfaces,
certify its QA, and restore umbrella reachability.

Direct elaboration confirmed the recorded failures (invalid binder
annotations from undefined `ZeroOmega`, `expected token` parses from the
ill-typed probability side `(ω : Ω) ↦ … ≤ …`, undefined `Independent`, `Prob`,
`Matrix.spectral_norm`, and an `MRV n n` arity mismatch). A scratch
elaboration probe against the pinned Mathlib (v4.14.0, a pruned checkout
without `Filtration`/`Adapted`/`condexp`) validated the replacement
interfaces: plain `Ω → ℝ` / `Ω → Matrix V V ℝ` functions, explicit
`μ : Measure Ω` with `IsProbabilityMeasure`, `ProbabilityTheory.IndepFun`,
a new product-σ-algebra measurable-space instance for `Matrix`, scoped
`Matrix.L2OpNorm` for the spectral norm, `Matrix.PosSemidef` for the
semidefinite order, and an elementary comap-based natural filtration with
set-integral conditional mean zero for matrix Azuma. Next: write modules,
QA, and index updates, then verify each module directly.

## 2026-08-17 — Concentration bridge restored and certified

**Status:** completed  
**Milestone:** Recover the probability/concentration bridge (all
`Probability.Concentration` modules) on real Mathlib probability
interfaces, certify its QA, and restore umbrella reachability.

**Changes:** all three scalar modules and all three matrix modules were
restated over plain `Ω → ℝ` / `Ω → Matrix V V ℝ` functions, an explicit
`Measure` with `IsProbabilityMeasure`, `ProbabilityTheory.IndepFun`,
the spectral norm via scoped `Matrix.L2OpNorm`, `Matrix.PosSemidef` for
the semidefinite order, and a new product-σ-algebra `MeasurableSpace`
instance on real matrices (new `Matrix/Basic.lean`; Mathlib ships none).
`subgaussian_norm` (an axiom-typed hole) became the real definition
`subgaussianNorm`; `hoeffding_iid` and `bernstein_iid` became proved
derived theorems; five unconsumed subgaussian axioms (moment growth,
linear combination, centering, sum bound) were removed from the trust
boundary. Matrix Azuma is stated through a new `MatrixMDS` structure
(comap past σ-algebras plus set-integral conditional means) because the
pinned Mathlib snapshot has no filtration/conditional-expectation API.
Both concentration QA files were rewritten to instantiate each axiom at
degenerate zero sequences (constant independence, `PosSemidef.zero`,
empty-event measures) and to check cross-axiom subgaussian coherence.

**Decisive commands and outcomes:** direct `lake build` of each of the
seven public modules (six repaired plus `Matrix/Basic`) and both QA
targets passed; the full `lake build` umbrella passed after re-adding
the subtree; `generate_qa_scoreboard.py`, `lint_axioms.py`,
`check_citations.py`, and `check_markdown_links.py` all pass.

**Verification:** 59 QA declarations (up from 48) with zero
`sorry`/`admit` anywhere under `Scaffold/`; explicit axiom count reduced
from 26 to 19, all cited and indexed; the long-standing
`matrix_azuma_hoeffding` citation/index warnings are closed.

**Trust boundary:** the concentration tail bounds (Hoeffding, Bernstein,
empirical, subgaussian lemma/tail, matrix Hoeffding/Bernstein/Azuma)
remain explicit cited axioms; QA checks their interfaces and degenerate
consequences, not their truth.

**Remaining risk:** the two-sided (factor-2) spectral-norm forms and the
MGF characterization of `subgaussianNorm` involve documented constant-level
differences from the cited sources; `MatrixMDS` should be restated through
Mathlib filtrations once available. The dynamic frontier still does not
consume the bridge.

**Next handoff:** derive the first `Scaffold/Derived/` theorem — an
event-stream cumulative-perturbation tail for `IsEventDriven` graph
streams from the concentration axioms — then the Horn–Johnson/Chung
page-level citation review.

## 2026-08-17T19:22:51Z — Derived event-stream tail (with inward Azuma repair)

**Run:** `20260817T191152Z-run-2`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Implement `Scaffold/Derived/EventStream.lean`, the first
derived-layer theorem: an Azuma tail bound on the cumulative Laplacian
perturbation `‖L_m - L_0‖` of a random event-driven graph stream.

Preparing the derivation exposed an inner defect: `matrix_azuma_hoeffding`
was stated with denominator `8 R²`, independent of the number of summands
`m`. Tropp's Theorem 7.1 variance statistic accumulates; the uniform-bound
specialization is `σ² = m R²`, and without the `m` factor the statement is
false for `m ≥ 2` (Rademacher sum counterexample). Per the center-out
policy the axiom is repaired before any consumer is built on it. Plan:
repair the axiom and its QA, add the proved telescoping identity plus the
random event-stream model and derived tail theorem, certify with
degenerate-stream QA, then umbrella and hygiene updates.

## 2026-08-17T19:31:02Z — Derived event-stream tail completed

**Run:** `20260817T191152Z-run-2`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** First derived-layer theorem: an Azuma tail bound on the
cumulative Laplacian perturbation of a random event-driven graph stream,
connecting the dynamic frontier to the concentration bridge.

**Changes:** repaired `matrix_azuma_hoeffding` to carry the cumulative
variance factor (`8 m R²` denominator); without it the statement was false
for `m ≥ 2` (Rademacher-sum counterexample) and had no consumers at repair
time. New `Scaffold/Derived/EventStream.lean`: proved telescoping identity
`sum_range_telescope`, the increment process `randomLaplacianIncrement`,
the proved interface lemma
`randomLaplacianIncrement_bounded_iff` (uniform bound ↔ pointwise
`IsEventDriven`), and the axiom-backed derived theorem `eventStreamTail`
bounding `P {‖L_m - L_0‖ ≥ t}`. New `Scaffold/QA/Derived/EventStream_QA.lean`
(seven declarations): telescoping at 0/1, constant-stream interface
coherence, and the derived tail instantiated at a zero-increment stream
with exact empty-event measures. Umbrella, README, architecture, scoreboard,
and the probability-concentration index updated.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.Probability.Concentration.Matrix.Azuma`,
`Scaffold.QA.Concentration.Matrix_QA`, `Scaffold.Derived.EventStream`,
`Scaffold.QA.Derived.EventStream_QA` all pass individually; full `lake
build` passes; `generate_qa_scoreboard.py`, `lint_axioms.py`,
`check_citations.py`, `check_markdown_links.py` all pass.

**Verification:** 66 QA declarations (up from 59), zero `sorry`/`admit`
anywhere under `Scaffold/`, 19 explicit cited axioms; the derived module is
certified through the umbrella.

**Trust boundary:** `eventStreamTail` is a checked deduction conditional
on `matrix_azuma_hoeffding` (Tropp 2012, Thm 7.1, uniform-bound
specialization `σ² = m R²`); it is not a foundationally proved result. The
Azuma repair is documented in the scoreboard interpretation section.

**Remaining risk:** `MatrixMDS` uses the elementary comap filtration; a
future Mathlib filtration API should replace it. The projector-drift
combination may expose interface friction on the perturbation side
(cumulative vs per-step bounds).

**Next handoff:** derived step 2 — high-probability cumulative
projector-drift corollary combining `eventStreamTail` with
`spectral_persistence`/Davis–Kahan under a spectral gap; then the
Horn–Johnson/Chung page-level citation review.

## 2026-08-17T19:26:48Z — Derived projector drift (concentration → DK)

**Run:** `20260817T192354Z-run-3`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Derived step 2: high-probability projector-drift bound
combining `eventStreamTail` (Azuma) with Weyl and Davis–Kahan, completing
the `‖Σₖ Eₖ‖ / γ` chain without adding any new axiom.

Design decision recorded before editing: the honest composition is
two-endpoint. Davis–Kahan is a two-point statement and Azuma controls the
two-endpoint displacement `‖L_m − L_0‖`; the DK separation hypothesis is
discharged pointwise from `weyl_inequality` plus proved `evals_sorted`
monotonicity and a base-gap hypothesis. The derivation exposes one inner
interface need — `initialProjector_congr` (proof-irrelevance transport of
projectors along matrix equalities), which will be added as a proved
theorem in the SGT center `GraphTheory.Spectral`. New modules:
`Scaffold/Derived/ProjectorDrift.lean` (`davisKahanTwoPoint`,
`eventStreamProjectorDrift`) plus `Scaffold/QA/Derived/ProjectorDrift_QA.lean`.

## 2026-08-17T19:36:43Z — Projector drift derived; persistence chain complete

**Run:** `20260817T192354Z-run-3`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Derived step 2: high-probability projector-drift bound,
completing the `‖Σₖ Eₖ‖ / γ` persistence chain end-to-end without adding
any new axiom.

**Changes:** new `Scaffold/Derived/ProjectorDrift.lean` with
`davisKahanTwoPoint` (Davis–Kahan two-point form, separation discharged
from `weyl_inequality` plus proved `evals_sorted` monotonicity under a
base-gap hypothesis `δ ≤ gap_B − ‖C−B‖`) and `eventStreamProjectorDrift`
(`μ{‖P_{L_m} − P_{L_0}‖ ≥ s/(γ−s)} ≤ 2 d exp(−s²/(8 m R²))` for
martingale event streams with base gap ≥ γ and `0 < s < γ`), the latter
combining the wrapper with `eventStreamTail` through an event inclusion.
One proved center theorem added to `GraphTheory.Spectral`:
`initialProjector_congr` (projector transport along matrix equalities by
proof irrelevance), exposed by the derivation and used to restate DK's
`A + E` conclusion at `L_m`. New `Scaffold/QA/Derived/ProjectorDrift_QA.lean`
(four declarations): wrapper at `C = B`, constant-stream instantiation of
the drift theorem, and empty-drift-event tightness. Umbrella, README,
architecture, scoreboard, and index updated. Design decision recorded:
the composition is two-endpoint (DK is a two-point statement and Azuma
controls the two-endpoint displacement), answering the
cumulative-vs-per-step interface question.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.GraphTheory.Spectral`, `Scaffold.Derived.ProjectorDrift`,
`Scaffold.QA.Derived.ProjectorDrift_QA` all pass individually; full `lake
build` passes; `generate_qa_scoreboard.py`, `lint_axioms.py`,
`check_citations.py`, `check_markdown_links.py` all pass.

**Verification:** 70 QA declarations (up from 66), zero `sorry`/`admit`
anywhere under `Scaffold/`, 19 explicit cited axioms (unchanged — the
milestone added hard crust only).

**Trust boundary:** `davisKahanTwoPoint` is conditional on
`davis_kahan_sin_theta` and `weyl_inequality`; `eventStreamProjectorDrift`
additionally on `matrix_azuma_hoeffding` (via `eventStreamTail`). Neither
is foundationally proved.

**Remaining risk:** the drift theorem assumes the spectral gap at the base
`L_0` only; a gap-along-the-path variant would need the per-step
`spectral_persistence` axiom or pathwise Weyl bookkeeping. The eigenbasis
facts behind `spectralProjector` remain unproved in the center.

**Next handoff:** prove spectral-projector idempotence and eigenbasis
orthonormality in the SGT center (projector algebra), then the
Horn–Johnson/Chung page-level citation review; the x90 observable
specification is now unblocked by a credible inner chain.

## 2026-08-17T19:40:12Z — Spectral-projector algebra in the center

**Run:** `20260817T193702Z-run-4`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Prove the projector algebra behind `spectralProjector`
(eigenbasis orthonormality and completeness, projector idempotence, extreme
thresholds) in the SGT center, replacing facts currently consumed through
the admitted perturbation interfaces with hard crust. No new axioms.

Design recorded before editing: pairwise orthonormality and completeness
of `eigvecOf` come from the pinned Mathlib `OrthonormalBasis` API
(`OrthonormalBasis.orthonormal`, `OrthonormalBasis.sum_repr'`, with
`PiLp.inner_apply` reducing inner products to coordinate sums);
idempotence follows entrywise through `Finset.sum_mul_sum`, sum
reordering, and the orthonormality relation; extreme-threshold theorems
are hypothesis-gated (empty/full filter sets). QA composes the extreme
cases with idempotence; thin-QA rationale documented since these are
theorems rather than axioms.

## 2026-08-17T19:59:41Z — Projector algebra proved in the SGT center

**Run:** `20260817T193702Z-run-4`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Prove the spectral-projector algebra behind
`spectralProjector` in the SGT center, replacing structural facts
previously consumed implicitly through the admitted perturbation
interfaces. No new axioms; hard crust only.

**Changes:** in `GraphTheory.Spectral`, proved `eigvecOf_inner`
(eigenbasis orthonormality from `OrthonormalBasis.orthonormal` with
`PiLp.inner_apply`), `eigvecOf_complete` (completeness from
`OrthonormalBasis.sum_repr'` at `EuclideanSpace.single`,
`EuclideanSpace.inner_single_right` for the coefficients),
`spectralProjector_idempotent` (entrywise expansion: `Finset.sum_mul_sum`,
sum reorder, orthonormality collapse via `Finset.sum_eq_single`),
`spectralProjector_eq_zero` / `spectralProjector_eq_one` (hypothesis-gated
extreme thresholds), and `initialProjector_idempotent`. The
`WithLp`/`EuclideanSpace` type-synonym coercions required explicit
Pi-typed ascriptions (`(∑ … : V → ℝ) b`) since the pruned snapshot lacks
direct sum-application lemmas; the delicate proofs were validated in a
scratch elaboration probe before being transplanted. New QA file
`SpectralGraph/Projector_QA.lean` (5 declarations): unit-norm diagonals of
the two basis relations and extreme-threshold compositions with
idempotence. Scoreboard, architecture debt list, README, and the SGT
index map updated. An operator checkpoint (`4181d07`) landed mid-run and
absorbed the earlier uncommitted work; my scratch probe file swept into
it was deleted as intended hygiene.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.GraphTheory.Spectral` and
`Scaffold.QA.SpectralGraph.Projector_QA` pass; every QA module target
(thirteen) rebuilt individually; full `lake build` passes;
`generate_qa_scoreboard.py`, `lint_axioms.py`, `check_citations.py`,
`check_markdown_links.py` all pass.

**Verification:** 75 QA declarations (up from 70), zero `sorry`/`admit`
anywhere under `Scaffold/`, 19 explicit cited axioms (unchanged).

**Trust boundary:** unchanged — the perturbation inequalities
themselves (`weyl_inequality`, `davis_kahan_sin_theta`,
`spectral_persistence`, Cheeger/interlacing/variational axioms) remain
admitted; only the projector algebra around them became hard crust.

**Remaining risk:** the two basis relations are stated through the
repo's `eigvecOf` coercion; if `eigvecOf`'s definition is ever restated
through a different `WithLp` conversion, the `rfl`-steps need revisiting.
Citation page-level locators remain pending.

**Next handoff:** citation hygiene (Horn–Johnson/Chung page locators,
assumption tightening review), then the `spectral_persistence`
fold-or-deprecate decision, then the x90 observable specification.

## 2026-08-17T20:03:37Z — Citation honesty audit + perturbation tightening

**Run:** `20260817T200010Z-run-5`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Citation hygiene with two interface tightenings: fix the
citation-audit findings on the perturbation/SGT axiom surface, and convert
`spectral_gap_stability` from an admitted axiom into a theorem proved from
`weyl_inequality` (axiom count 19 → 18 at zero trust cost).

Audit findings so far: the Chung index's provenance note ("earlier
revisions recorded Theorem 2.1 p. 42, Theorem 2.2 p. 44") is contradicted
by git history — the initial commit cited only "Theorem 2.2" without a
page and no pre-rebuild index file exists; the Weyl axiom lacks a
statement-differences note explaining that its Lean form is the
spectral-norm corollary of the cited general theorem; the Davis–Kahan
separation hypothesis is stated in a pairwise form whose binding instance
(by `evals_sorted`) is the single-pair cluster separation the cited
Yu–Wang–Samworth Theorem 2 actually uses. Plan: replace the false note
with accurate history (no invented page numbers), add the Weyl note,
tighten the DK hypothesis to the single-pair form (updating the derived
wrapper and QA), and prove `spectral_gap_stability` from Weyl.

## 2026-08-17T20:09:50Z — Citation hygiene completed; axioms 19 → 18

**Run:** `20260817T200010Z-run-5`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Citation honesty fixes on the perturbation/SGT axiom
surface, Davis–Kahan hypothesis tightening, and conversion of
`spectral_gap_stability` from an admitted axiom into a theorem proved
from `weyl_inequality`.

**Changes:** (1) Chung index provenance note corrected — git history
shows the claimed earlier page-level locators ("Theorem 2.1 p. 42,
Theorem 2.2 p. 44") were never recorded (initial commit cited
"Theorem 2.2" without a page); theorem/page numbering now explicitly
unconfirmed, no numbers invented. (2) `weyl_inequality` doc now records
that its Lean form is the spectral-norm corollary of the cited general
Weyl inequality. (3) `davis_kahan_sin_theta` separation tightened to the
single-pair two-cluster form `λ_{k+1}(A+E) − λ_k(A) ≥ δ` (the form of
the cited Yu–Wang–Samworth Theorem 2); `davisKahanTwoPoint` simplified
to one Weyl fact at the gap index (sortedness no longer needed);
DavisKahan QA reduces the pairwise hypothesis via `evals_sorted`.
(4) `spectral_gap_stability` proved from `weyl_inequality` (Weyl at both
gap endpoints plus `linarith`) — identical statement shape, explicit
axioms 19 → 18. Perturbation index map updated to distinguish axiom vs
proved declarations.

**Decisive commands and outcomes:** direct builds of
`Perturbation.Weyl`, `Perturbation.DavisKahan`,
`Derived.ProjectorDrift`, and QA modules `Weyl_QA`, `DavisKahan_QA`,
`Derived.{ProjectorDrift,EventStream}_QA` all pass; full `lake build`
passes; all four hygiene scripts pass; scoreboard confirms 18 explicit
axioms.

**Verification:** 75 QA declarations, zero `sorry`/`admit` under
`Scaffold/`; every axiom cited and indexed.

**Trust boundary:** unchanged in substance for the inequalities
themselves — `weyl_inequality` and `davis_kahan_sin_theta` remain the
admitted perturbation boundary; `spectral_gap_stability` is now a
checked consequence of it rather than a parallel admission.

**Remaining risk:** Horn–Johnson/Chung locator confirmation still needs a
physical or publisher copy. Note: the operator reoriented the execution
plan mid-run toward a broad-SGT backlog (persistence retained only as a
compatibility example); this run's edits preserved that concurrent
reorganization and closed the citation-hygiene item within it.

**Next handoff:** first broad-SGT backlog (weighted/normalized Laplacian
interoperability, random-walk/Markov interfaces, expansion/cut
interfaces, spectral algorithms), ranked by concrete reuse.

## 2026-08-17T20:12:04Z — Broad-SGT backlog + random-walk interfaces

**Run:** `20260817T200846Z-run-6`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Deliver the first broad-SGT backlog (ranked by concrete
reuse, center-first) together with its top-ranked item implemented:
random-walk/transition-matrix interfaces for `d`-regular graphs, bridging
the combinatorial Laplacian center to the normalized/Cheeger world and to
future Markov-chain consumers. Pure hard crust, no new axioms.

Design: `transitionMatrix A d := d⁻¹ • A` (real definition); proved
symmetry, row-stochasticity `∑ j P i j = 1` under `deg A i = d` and
`0 < d`; `randomWalkLaplacian A d := 1 - transitionMatrix A d`; proved
identity with `regularNormalizedLaplacian` (interop by theorem, not by
definition-sharing) and the scaling bridge
`randomWalkLaplacian = d⁻¹ • laplacian` for `d`-regular graphs. QA
instantiates everything at a concrete two-vertex graph.

## 2026-08-17T20:17:06Z — Broad-SGT backlog published; random-walk interfaces delivered

**Run:** `20260817T200846Z-run-6`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Deliver the first broad-SGT backlog (ranked by concrete
reuse, center-first) and implement its top-ranked item: random-walk /
Markov interfaces for `d`-regular graphs, bridging the combinatorial
Laplacian center to the normalized/Cheeger world. Pure hard crust, no
new axioms.

**Changes:** new `docs/6_SGT_BACKLOG.md` (six ranked items, each naming
consumers, dependency paths, and gates; standing decisions on
`spectral_persistence` and re-admissions; linked from the README
canonical-docs list). New `Scaffold/Mathlib/GraphTheory/RandomWalk.lean`
(all proved): `transitionMatrix` (`d⁻¹ • A`), `transitionMatrix_symmetric`,
`transitionMatrix_row_sum` (row-stochasticity for `d`-regular graphs —
the interface Markov-chain consumers need),
`randomWalkLaplacian`, `randomWalkLaplacian_symmetric`,
`randomWalkLaplacian_eq_regularNormalizedLaplacian` (interop with the
Cheeger bridge by theorem, not definition-sharing),
`randomWalkLaplacian_eq_smul_laplacian` (bridge to the combinatorial
center: `L_rw = d⁻¹ • L`). New QA
`SpectralGraph/RandomWalk_QA.lean` (7 declarations): a concrete
two-vertex edge graph with fully computed symmetry, degree,
row-stochasticity, transition entries, both bridge identities, and the
Laplacian entries. Umbrella, SGT index map, README maturity list, and
scoreboard updated.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.GraphTheory.RandomWalk` and
`Scaffold.QA.SpectralGraph.RandomWalk_QA` pass; full `lake build`
(including the new umbrella import) passes; all four hygiene scripts
pass.

**Verification:** 82 QA declarations (up from 75), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; the increment adds only proved
statements. The Cheeger axioms remain the admitted boundary for the
normalized world.

**Remaining risk:** the bridges are restricted to the `d`-regular cone;
the irregular adapters (backlog item 2) are gated on representing
`D^{-1/2}` without a pinned-Mathlib square root.

**Next handoff:** backlog item 2 — irregular normalized-Laplacian
adapters (walk-form statements plus spectral similarity transfer), then
expansion/cut interfaces as consumers emerge.

## 2026-08-17T20:19:58Z — Irregular normalized-Laplacian adapters

**Run:** `20260817T201730Z-run-7`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Backlog item 2: the general (irregular) symmetric
normalized Laplacian as a real definition, removing the `d`-regular
restriction of the current normalized surface without any matrix square
root.

Key design decision: only a *diagonal* square root is needed
(`√deg A i` per vertex), which `Real.sqrt` supplies directly — the
pinned-Mathlib matrix-square-root gap never applies. New module
`GraphTheory.Normalized`: `degreeSqrt`/`degreeInvSqrt` diagonal matrices,
`normalizedLaplacian A = 1 - S⁻¹ A S⁻¹`, proved symmetry, the congruence
`S * L_sym * S = laplacian A` (square roots cancel), and agreement with
`regularNormalizedLaplacian` on the regular cone. QA at a 3-vertex path
(genuinely irregular, `√2` entries) and the regular edge. Spectral
similarity transfer to the walk view deferred to the next slice.

## 2026-08-17T20:31:08Z — Irregular normalized Laplacian delivered

**Run:** `20260817T201730Z-run-7`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Backlog item 2 (core): the general (irregular) symmetric
normalized Laplacian as a real definition, removing the `d`-regular
restriction of the normalized surface without any matrix square root.
Pure hard crust, no new axioms.

**Changes:** new `Scaffold/Mathlib/GraphTheory/Normalized.lean` (all
proved): `degreeSqrt`/`degreeInvSqrt` — the observation that only a
diagonal square root is needed (`Real.sqrt` per vertex), bypassing the
recorded pinned-Mathlib gap; `normalizedLaplacian A = 1 - (1/√D) A (1/√D)`;
`degreeSqrt_mul_degreeSqrt` (`√D √D = degreeMatrix`); inverse-factor
theorems; `normalizedLaplacian_symmetric` (transpose algebra through
`diagonal_transpose`); the congruence
`degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`
(`√D L_sym √D = laplacian A`, square roots cancel — the
square-root-free-shaped bridge to the combinatorial center); and
`normalizedLaplacian_eq_regularNormalizedLaplacian` (regular-cone
agreement). New QA `SpectralGraph/Normalized_QA.lean` (11 declarations)
at a concrete 3-vertex path (genuinely irregular: degrees 1, 2, 1; the
`-1/√2` adjacent entries computed symbolically) and the regular
two-vertex edge. Umbrella, backlog item 2 status, SGT index map,
scoreboard, and README updated.

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Normalized` and
`Scaffold.QA.SpectralGraph.Normalized_QA` pass (the diagonal-algebra
proofs were probe-validated before transplantation); full `lake build`
passes; all four hygiene scripts pass.

**Verification:** 93 QA declarations (up from 82), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; the increment adds only proved
statements. The Cheeger axioms remain the admitted boundary for the
normalized world.

**Remaining risk:** spectral similarity transfer to the walk form and
irregular row-stochasticity are still open (recorded in backlog item 2);
QA entry computations rely on the pinned snapshot's `!!`-notation
evaluation behavior.

**Next handoff:** finish backlog item 2 (walk-form similarity:
`evals`-invariance interface plus irregular row-stochasticity), then
expansion/cut interfaces as consumers emerge.

## 2026-08-17T20:34:12Z — Irregular walk form: row-stochasticity + similarity

**Run:** `20260817T203130Z-run-8`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Finish backlog item 2's walk half: the general
(irregular) walk transition matrix with proved row-stochasticity (the
named Markov consumer) and the similarity identity
`√D · L_walk · (1/√D) = L_sym` as proved hard crust.

Evidence check recorded before editing: the walk Laplacian `I − D⁻¹A`
is not symmetric for irregular graphs, so Scaffold's `evals` (defined
only for `IsSymm`) does not apply to it; the deferred eigenvalue
transfer needs charpoly-roots machinery for non-symmetric matrices,
absent from the pinned Mathlib. The similarity *identity* is therefore
the honest stopping point, with the transfer documented as a precisely
named gap rather than a vague TODO.

## 2026-08-17T20:43:20Z — Irregular walk form completed (backlog item 2 closed)

**Run:** `20260817T203130Z-run-8`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Close the walk half of backlog item 2: the general
(irregular) walk transition matrix with proved row-stochasticity and the
similarity identity to the symmetric normalized Laplacian. Pure hard
crust, no new axioms.

**Changes:** in `GraphTheory.Normalized`: `walkTransitionMatrix`
(`D⁻¹A`, positive degrees), `walkTransitionMatrix_row_sum`
(row-stochasticity on irregular graphs — removing the `d`-regularity
restriction of the RandomWalk module's version; the named Markov
consumer), `walkLaplacian` (`I − D⁻¹A`, documented as non-symmetric in
general), and `degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`
(`√D · L_walk · (1/√D) = L_sym`, proved via the diagonal-algebra lemma
`√D · D⁻¹ = 1/√D`). QA extended (96 declarations total): row sums on
the 3-vertex path, computed walk entries (`P 1 0 = 1/2`, `P 0 1 = 1`),
and the similarity identity instantiated entrywise. Backlog item 2
marked closed with the eigenvalue-list transfer recorded as the
precisely named residual gap.

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Normalized` and
`Scaffold.QA.SpectralGraph.Normalized_QA` pass; full `lake build`
passes; all four hygiene scripts pass.

**Verification:** 96 QA declarations (up from 93), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** the eigenvalue-list transfer needs a charpoly-roots
interface for non-symmetric matrices (absent in the pinned Mathlib);
until then, spectral statements about the walk form route through the
similarity identity plus the symmetric `L_sym`.

**Next handoff:** backlog item 3 (expansion/cut interfaces with named
consumers) or the `spectral_persistence` retain-or-deprecate decision.

## 2026-08-17T20:46:15Z — spectral_persistence deprecation decision

**Run:** `20260817T204342Z-run-9`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Close the standing `spectral_persistence`
retain-or-deprecate decision (ready-queue item) from consumer evidence,
per the architecture's upstream-replacement lifecycle.

Evidence: grep shows zero non-QA consumers — the derived layer references
it only in a comment, its only use is the QA deliberately exercising the
compatibility surface, and the derived two-endpoint chain covers the
motivating use. Decision: deprecate with a migration note (axiom retained
through the compatibility window; removal is a later release decision,
not a breaking change now). `@[deprecated]` probe-verified to apply to
`axiom` declarations in this toolchain. Plan: annotate + migration note,
linter-silence the deliberate QA use, update indexes/docs (davis_kahan
source, SGT and perturbation maps, backlog standing decision,
architecture debt, scoreboard).

## 2026-08-17T20:49:57Z — spectral_persistence deprecated (decision closed)

**Run:** `20260817T204342Z-run-9`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Close the standing `spectral_persistence`
retain-or-deprecate decision from consumer evidence, per the
architecture's deprecation lifecycle; no new mathematics.

**Changes:** `spectral_persistence` annotated `@[deprecated (since :=
"2026-08-17")]` with a migration note in its doc (zero non-QA consumers;
derived two-endpoint chain covers the motivating use; migration path:
sum the two-endpoint bound over consecutive times or consume
`davisKahanTwoPoint` directly). The attribute's applicability to `axiom`
declarations was probe-verified first. `Dynamics_QA.lean` continues to
exercise the deprecated compatibility surface with
`set_option linter.deprecated false in` scoped to that one lemma (doc
records why). Updated: davis_kahan source index, SGT and perturbation
map entries, backlog standing decision, architecture §12 debt item,
scoreboard interpretation (axiom count stays 18 until the compatibility
window closes). Bonus hygiene: the derived module's use of Mathlib's
deprecated `div_lt_div_iff` upgraded to `div_lt_div_iff₀`.

**Decisive commands and outcomes:** `lake build` on
`Scaffold.Mathlib.GraphTheory.Dynamics`,
`Scaffold.QA.SpectralGraph.Dynamics_QA`, and
`Scaffold.Derived.ProjectorDrift` pass; full `lake build` passes with
zero deprecation warnings; all four hygiene scripts pass.

**Verification:** 96 QA declarations, zero `sorry`/`admit` under
`Scaffold/`; 18 explicit cited axioms (unchanged — deprecation, not
removal).

**Trust boundary:** effectively reduced by one admitted-but-unconsumed
statement; formally unchanged until the compatibility window closes and
the axiom is removed in a permitted release.

**Remaining risk:** none new; the migration note must be revisited at
the removal release.

**Next handoff:** backlog item 3 — expansion and cut interfaces
(edge-boundary and uniform-weight conductance variants), each admitted
only with a named algorithm consumer.

## 2026-08-17T20:53:04Z — Cut duality (hard crust)

**Run:** `20260817T205021Z-run-10`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Backlog item 3, first slice: the cut-duality structural
facts (volume complementarity, boundary and conductance invariance under
complementation, degenerate-cut guards) as proved statements in the SGT
center. No axioms — the Cheeger inequalities remain the admitted
boundary.

Named consumers: spectral-partitioning sweep cuts and sparsest-cut
statement shapes (backlog items 3–4) both assume cuts are
partition-valued (invariant under choosing the other side); the Cheeger
minimizer canonicalization consumes conductance invariance.

## 2026-08-17T21:01:11Z — Cut duality delivered (backlog item 3, first slice)

**Run:** `20260817T205021Z-run-10`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Backlog item 3, first slice: the cut-duality structural
facts in the SGT center — a cut is a property of the partition, not the
chosen side. Pure hard crust, no new axioms; the Cheeger inequalities
remain the admitted boundary.

**Changes:** in `GraphTheory.Spectral`: `vol_compl` (volume
complementarity via `Finset.sum_add_sum_compl`),
`boundary_compl` (boundary invariance under complementation for
symmetric weights, via `Finset.sum_comm` + `IsSymm`),
`conductance_compl` (conductance invariance — the Cheeger minimizer can
be canonicalized to either side, the interface sweep-cut consumers
require), `boundary_empty` / `boundary_univ` (degenerate-cut guards).
New QA `SpectralGraph/Cuts_QA.lean` (11 declarations) at the 3-vertex
path: degrees (1,2,1), the singleton cut's boundary computing to `1`
via row-sum-minus-diagonal, duality and conductance invariance
instantiated, total volume `4`, guards evaluated. SGT index map,
backlog item 3 "Have" list, scoreboard, and README updated.

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Spectral` and
`Scaffold.QA.SpectralGraph.Cuts_QA` pass; full `lake build` passes with
zero deprecation warnings; all four hygiene scripts pass.

**Verification:** 107 QA declarations (up from 96), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** none new. Backlog item 3's further variants
(edge-boundary and uniform-weight conductance) remain gated on named
algorithm consumers.

**Next handoff:** remaining backlog item 3 variants with named
consumers, or the backlog item 4 gating review (spectral algorithms).

## 2026-08-17T21:09:41Z — SGT coverage radar (operator direction)

**Run:** `20260817T210736Z-run-1`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Deliver the operator-directed coverage assessment from
`cdx-sgt-radar-axes.md`: two radars — eight subject axes and a separate
assurance-quality radar — scored by usable, verified coverage rather
than declaration count, each score justified by named declarations with
their proved/admitted/absent status.

Method: evidence-first scoring against the current tree (18 explicit
axioms, 107 QA declarations, proved/admitted status per module); the
weakest axes feed the backlog (subject axis 6 — combinatorial and
electrical structure — is entirely absent; assurance-side downstream
reuse is weakest since RandomWalk/Normalized lack consumers). Deliverable
`docs/7_SGT_RADAR.md` plus backlog/README integration; no Lean changes,
verification via the doc-hygiene suite.

## 2026-08-17T21:11:09Z — SGT coverage radar delivered

**Run:** `20260817T210736Z-run-1`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Deliver the operator-directed coverage assessment
(`cdx-sgt-radar-axes.md`): two radars — eight subject axes and a
separate assurance-quality radar — scored by usable, verified coverage,
each score justified by named declarations with proved/admitted/absent
status.

**Changes:** new `docs/7_SGT_RADAR.md` (linked from the README
canonical-docs list): subject scores — models 2.5, spectral algebra 3.5,
variational 2.5, cuts/expansion 2.5, walks 2.5, electrical 0.5,
perturbation/randomness 3.0, adjacent systems 1.0; assurance scores —
proved depth 3.5, axiom minimization 3.5 (26 → 19 → 18 trend),
Mathlib interop 3.5, QA 3.0 (skews degenerate-case), citation fidelity
3.5, downstream reuse 2.5 (RandomWalk/Normalized unconsumed). Includes
weakest-axis findings and a re-scoring protocol (scores move only with
usable, verified coverage, recorded with the causing milestone).
Backlog: new gated candidate item 7 (combinatorial/electrical structure
— axis entirely absent, admission deferred until a named consumer
states the identity it needs) and a downstream-reuse standing decision.
No Lean changes.

**Decisive commands and outcomes:** axiom inventory re-verified by grep
(18 explicit, including the deprecated one) before scoring;
`generate_qa_scoreboard.py`, `lint_axioms.py`, `check_citations.py`,
`check_markdown_links.py` all pass; scoreboard metrics unchanged (107
QA declarations, 0 `sorry`/`admit`).

**Verification:** doc-only change; every score's cited declarations
exist in the current tree.

**Trust boundary:** unchanged; the radar explicitly labels which
neighborhoods rest on admitted statements.

**Remaining risk:** scores are judgment calls over cited evidence; the
re-scoring protocol constrains drift, and milestone entries must record
future changes.

**Next handoff:** radar-driven next milestone — the first downstream
consumer for the walk/normalized interfaces (weakest assurance axis),
or remaining backlog item 3 variants with named consumers.

## 2026-08-17T21:13:57Z — Stationary structure (first walk/normalized consumer)

**Run:** `20260817T211135Z-run-2`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Close the radar's weakest assurance axis (downstream
reuse): the first module consuming the `RandomWalk`/`Normalized`
interfaces — the stationary-structure theorems, proved from the bridge
lemmas. No new axioms.

Content: `L_sym *ᵥ √deg = 0` (kernel of the general normalized
Laplacian) and `Pᵀ *ᵥ deg = deg` (the degree measure is stationary for
the walk — `π ∝ deg` is the stationary distribution, the Markov-mixing
consumer interface). Both reduce to the diagonal algebra plus
`A *ᵥ 1 = deg`.

## 2026-08-17T21:16:50Z — Stationary structure delivered (reuse gap closing)

**Run:** `20260817T211135Z-run-2`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Close the radar's weakest assurance axis (downstream
reuse): `Scaffold.Mathlib.GraphTheory.Stationary`, the first module
consuming the walk/normalized interfaces. Pure hard crust, no new
axioms.

**Changes:** new `GraphTheory.Stationary` (imports `Normalized`):
`mulVec_one_eq_deg` (`A *ᵥ 1 = deg`, row sums in vector form),
`normalizedLaplacian_mulVec_sqrtDeg_eq_zero` (kernel of the general
normalized Laplacian is `√deg` — the normalized counterpart of the
combinatorial `laplacian_ones_in_kernel`, proved through the
`degreeInvSqrt` diagonal algebra), and
`walkTransitionMatrix_transpose_mulVec_deg` (`Pᵀ *ᵥ deg = deg`: the
degree measure is stationary for the walk, i.e. `π ∝ deg` — the named
Markov-mixing consumer interface). New QA
`SpectralGraph/Stationary_QA.lean` (6 declarations) at the 3-vertex
path, including a fully computed center kernel entry. Umbrella, SGT
index map, scoreboard, and README updated. SGT radar downstream-reuse
score re-scored 2.5 → 3.0 with the causing milestone recorded per the
radar's protocol; backlog standing decision updated (remaining reuse
gap: `RandomWalk`'s regular-case bridges).

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Stationary` and
`Scaffold.QA.SpectralGraph.Stationary_QA` pass; full `lake build`
passes; all four hygiene scripts pass.

**Verification:** 116 QA declarations (up from 107), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** none new; `RandomWalk`'s regular bridges remain
unconsumed outside QA (noted in backlog standing decisions).

**Next handoff:** a consumer for `RandomWalk`'s regular bridges (e.g. a
regular-graph Cheeger consequence restated through the walk view), or
remaining backlog item 3 variants with named consumers.

## 2026-08-17T21:19:52Z — Walk-Laplacian kernel (RandomWalk consumer)

**Run:** `20260817T211717Z-run-3`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** in-progress  
**Milestone:** Close the remaining reuse gap: make `Stationary` the
demonstrated consumer of `RandomWalk` as well as `Normalized`, via the
walk-Laplacian kernel facts `(I − P) *ᵥ 1 = 0` (regular and irregular
variants) — conservation of mass, the base statement of diffusion and
mixing arguments.

Scoping evidence: the heavier spectral-transfer consumer
(`evals (c • M) = c • evals M`) requires excavation through Mathlib's
`irreducible_def` eigenspace decomposition; recorded as a named backlog
candidate rather than attempted speculatively.

## 2026-08-17T21:22:27Z — RandomWalk consumer delivered; reuse axis closed

**Run:** `20260817T211717Z-run-3`  
**Session:** `ses_feef5b005ffeSm12pxYFaQuzoE`  
**Status:** completed  
**Milestone:** Close the remaining downstream-reuse gap:
`GraphTheory.Stationary` extended to consume `RandomWalk` in addition
to `Normalized`, via the walk-Laplacian kernel (conservation-of-mass)
facts. Pure hard crust, no new axioms.

**Changes:** `Stationary` now imports `RandomWalk` and proves
`randomWalkLaplacian_mulVec_one_eq_zero` (regular case; consumes
`RandomWalk.transitionMatrix_row_sum`) and
`walkLaplacian_mulVec_one_eq_zero` (irregular case; consumes
`Normalized.walkTransitionMatrix_row_sum`) — both the statement
`(I − P) *ᵥ 1 = 0`, total probability preserved by each walk step.
QA extended (119 declarations total): the irregular path and the
regular edge instantiate the two variants. Radar: downstream reuse
re-scored 3.0 → 3.5 (recorded per protocol); the weakest assurance
axis is now QA depth (3.0, degenerate-case skew). Backlog records the
named future consumer candidate (`evals (c • M) = c • evals M`,
gated on Mathlib's `irreducible_def` eigenspace excavation). SGT index
map, scoreboard, and README updated.

**Decisive commands and outcomes:** direct builds of
`Scaffold.Mathlib.GraphTheory.Stationary` and
`Scaffold.QA.SpectralGraph.Stationary_QA` pass; full `lake build`
passes; all four hygiene scripts pass.

**Verification:** 119 QA declarations (up from 116), zero `sorry`/`admit`
under `Scaffold/`, 18 explicit cited axioms (unchanged).

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** `Stationary` is the sole consumer of both interface
modules — breadth of reuse is the new constraint, not existence.

**Next handoff:** breadth consumers (second consuming module, e.g.
variational Rayleigh bounds through the congruence bridge), the QA
assurance lever (property-based/falsification QA), or backlog item 3
variants with named consumers.

## 2026-08-17T21:29:30Z — Exhaustive/falsification QA for the SGT center

**Run:** `20260817T212523Z-run-1`  
**Session:** `ses_fee6294b2ffembnC8DMWLp0fQN`  
**Status:** in-progress  
**Milestone:** Raise the weakest assurance axis (QA 3.0 — degenerate-case
skew, no property-based/negative QA) by delivering exhaustive,
kernel-checked-coverage sweeps over *all* cuts of two fixtures plus
negative witnesses, in a new QA module. Pure hard crust, no axiom
changes.

Scoping evidence: existing QA instantiates theorems at one or two cuts
and mostly applies the general theorem being tested (e.g.
`path_boundary_compl_QA` rewrites with `boundary_compl`), so a
self-consistent mis-definition would pass. Backlog item 3 variants are
gated on named consumers; reuse just re-scored to 3.5 — QA depth is the
named next assurance lever.

## 2026-08-17T21:48:42Z — Exhaustive/falsification QA delivered (QA axis 3.0 → 3.5)

**Run:** `20260817T212523Z-run-1`  
**Session:** `ses_fee6294b2ffembnC8DMWLp0fQN`  
**Status:** completed  
**Milestone:** Raise the weakest assurance axis (QA, 3.0 — degenerate-case
skew) by delivering `Scaffold/QA/SpectralGraph/Exhaustive_QA.lean`:
exhaustive, kernel-checked sweeps over all cuts of two fixtures, computed
from the definitions rather than by applying the general theorems, plus
negative witnesses. Pure hard crust, no axiom changes.

**Changes:** 87 new QA declarations (206 total across 18 modules).
(a) Coverage certificates `cuts3_eq`/`cuts4_eq`: the listed cuts are
exactly `Finset.univ.powerset` on `Fin 3`/`Fin 4`, decided by the kernel —
"exhaustive" is verified, not asserted. (b) Boundary and volume tables
for every cut of the 3-vertex path and the 4-cycle, each entry evaluated
from `boundary`/`vol`/`conductance` on concrete data (`norm_num` on the
unfolded sums; no use of `boundary_compl`/`vol_compl` on the path from
definition to value). (c) Duality recomposed from the independently
computed tables (`exh_boundary_duality_QA`, `cyc_boundary_duality_QA`,
`exh_vol_complementarity_QA`). (d) Negative witnesses: conductance
separates adjacent-pair (`1/2`) from opposite-pair (`1`) cuts on the
cycle; Rayleigh separates `8/3` from `0` on the path; an asymmetric
two-vertex weight (`A 01 = 2`, `A 10 = 1`) shows `boundary_compl`'s
symmetry hypothesis is load-bearing (`2 ≠ 1`). (e) Walk row sums
computed per row, independently of `walkTransitionMatrix_row_sum`.
Radar QA axis re-scored 3.0 → 3.5 per protocol (stale 107/16 evidence
count refreshed to the current tree); execution plan and scoreboard
updated.

**Decisive commands and outcomes:** `lake env lean` on the module
(zero output — clean elaboration); `lake build
Scaffold.QA.SpectralGraph.Exhaustive_QA` ✔; full `lake build` ✔;
`lint_axioms`, `check_citations`, `check_markdown_links` all pass;
`generate_qa_scoreboard` regenerated (206 declarations, 0 placeholders).

**Verification:** all 87 new declarations compile with no
`sorry`/`admit`; 18 explicit cited axioms unchanged; umbrella build
unaffected (QA modules are leaf builds, built directly).

**Trust boundary:** unchanged; hard crust only. Implementation note
recorded: `degreeMatrix`'s diagonal conditional elaborates with a
classical `Decidable` instance (defined at generic `V`), so the Rayleigh
checks compose the proved Dirichlet identity and kernel theorem; the
checked values are still fully computed.

**Remaining risk:** no parametric (randomized) property QA and no
computational eigenvalue checks (Mathlib's spectral-theorem API is not
computable) — both named as the residual QA-depth gap on the radar.

**Next handoff:** breadth consumers (second consuming module for
walk/normalized, e.g. Rayleigh bounds through the congruence bridge),
the gated `evals (c • M) = c • evals M` excavation candidate, or
backlog item 3 variants once an algorithm consumer is named.

## 2026-08-17T21:51:19Z — Variational transfer (second interface consumer)

**Run:** `20260817T214929Z-run-2`  
**Session:** `ses_fee6294b2ffembnC8DMWLp0fQN`  
**Status:** in-progress  
**Milestone:** Deliver the open milestone's named breadth consumer:
`GraphTheory.VariationalTransfer`, the second consuming module for the
`Normalized`/`Spectral` interfaces — quadratic-form and Rayleigh-quotient
transfer through the proved congruence `√D L_sym √D = L`, plus PSD
transfer. Addresses the downstream-reuse axis's stated constraint
(`Stationary` is the sole consumer). Pure hard crust, no new axioms.

Scoping evidence: all required Mathlib pieces exist in the pinned
snapshot (`dotProduct_mulVec`, `mulVec_transpose`, `mulVec_diagonal`,
`mulVec_mulVec`, `one_mulVec`, `diagonal_transpose`); no name
collisions for the planned declarations.

## 2026-08-17T21:56:15Z — Variational transfer delivered (reuse axis 3.5 → 4.0)

**Run:** `20260817T214929Z-run-2`  
**Session:** `ses_fee6294b2ffembnC8DMWLp0fQN`  
**Status:** completed  
**Milestone:** Deliver the open milestone's named breadth consumer:
`Scaffold.Mathlib.GraphTheory.VariationalTransfer` — quadratic-form and
Rayleigh-quotient transfer between the combinatorial and normalized
Laplacians through the proved congruence `√D L_sym √D = L`, plus PSD
transfer. The second consuming module of the `Normalized`/`Spectral`
interfaces, addressing the reuse axis's stated constraint
("`Stationary` is the sole consumer"). Pure hard crust, no new axioms.

**Changes:** public module (7 proved declarations): `quadForm_congr`
(generic symmetric-congruence invariance of quadratic forms),
`degreeSqrt_isSymm`/`degreeSqrt_mulVec` (entrywise stretch),
`quadForm_laplacian_eq_quadForm_normalizedLaplacian` (Dirichlet-form
transfer), `dotProduct_degreeSqrt_mulVec` (degree-weighted
denominator), `degreeSqrt_mulVec_ne_zero`,
`rayleigh_normalizedLaplacian_degreeSqrt` — the headline
irregular-graph normalized Rayleigh quotient
`rayleigh L_sym (√D y) = (yᵀ L y) / ∑ deg i · y i²`, which the
regular-only Cheeger axioms cannot express — and
`normalizedLaplacian_psd` (PSD transferred from `laplacian_psd` by
un-stretching through `1/√D`). QA
`SpectralGraph/VariationalTransfer_QA.lean` (15 declarations at the
3-vertex path): entrywise stretch computes to `-√2`; the denominator
computes to `4` both through the lemma and as a bare sum; the headline
instantiates to the classical value `rayleigh L_sym (√D (1,-1,1)) =
8/4 = 2` — the largest eigenvalue of the normalized path Laplacian,
obtained without any spectral theorem (a defect in the congruence
bridge, stretch, or denominator lemma would move this value). Umbrella
import added; SGT index map gains the module section; radar re-scored
per protocol: downstream reuse 3.5 → 4.0 (two consuming modules),
subject axis 3 (variational) 2.5 → 3.0.

**Decisive commands and outcomes:** `lake env lean` on both files
(zero output after fixes — clean elaboration, zero warnings);
`lake build` of module and QA ✔; full `lake build` ✔ (1997 targets);
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated: 221 QA declarations, 0 placeholders, 18 axioms
unchanged.

**Verification:** all 7 public declarations proved from the center
(consumes `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt`,
`degreeSqrt_mul_degreeInvSqrt`, `laplacian_psd`); Mathlib pieces used
(`dotProduct_mulVec`, `mulVec_transpose`, `mulVec_diagonal`,
`mulVec_mulVec`, `one_mulVec`, `diagonal_transpose`) all exist in the
pinned v4.14.0 snapshot.

**Trust boundary:** unchanged; hard crust only.

**Remaining risk:** no admitted-axiom consumer yet (Cheeger bounds
still regular-only); the transfer statement shapes are available for a
future irregular Cheeger family. `evals (c • M)` excavation still
gated.

**Next handoff:** the `evals (c • M) = c • evals M` Mathlib-excavation
candidate; an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs a precise source and
consumer); or backlog item 3 variants once an algorithm consumer is
named.

## 2026-08-18T02:10:53Z — Cheeger axiom statement-shape repair (in progress)

**Run:** `20260818T020953Z-run-1`  
**Session:** `ses_fed696611ffe0yiCxJU9cqgq3S`  
**Status:** in-progress  
**Milestone:** Repair a materially false statement shape at the admitted
boundary: both Cheeger axioms pass `regularNormalizedLaplacian A d` to
`lambda2`, which is `evals (laplacian ·) 1` — so the asserted spectral
quantity is `λ₂(L(L_sym)) = λ₂(-L_sym)`, not `λ₂(L_sym)`. On the
two-vertex edge the lower-bound instance reads `1/2 ≤ 0`, false; the
documented and cited intent is Chung Ch. 2's `φ²/2 ≤ λ₂(L_sym)`. Leverage:
the admitted Cheeger interface is the core of radar axis 4's admitted
half; a false admitted statement is an emergency-repair case
(architecture §9) and the top center-out priority.

Scoping evidence: `lambda2` consumers grep-verified (only `Cheeger.lean`
misuses it; `lambda2_variational` uses it correctly); Mathlib v4.14
provides the repair kit (`Matrix.IsHermitian.eigenvalues_eq` Rayleigh
form for the refutation bound; `det_eq_prod_eigenvalues`,
`Matrix.trace_mul_cycle`, `unitary.coe_star_mul_self`,
`Multiset.sort_eq`, `Finset.sum_eq_multiset_sum` for value pinning).
Plan: `secondEval` + `lambda2_eq_secondEval` + `eigvalOf_sum_eq_trace`
proved in the center; axioms restated at unchanged names/hypotheses with
corrected RHS; QA refutes the old shape, pins the corrected value
`λ₂(L_sym) = 2` on the edge, and re-instantiates coherence; dangling QA
reference `cheegerConstant_le_two_QA` in the upper-bound docstring fixed.

## 2026-08-18T02:54:12Z — Cheeger statement-shape repair delivered (QA 3.5 → 4.0)

**Run:** `20260818T020953Z-run-1`  
**Session:** `ses_fed696611ffe0yiCxJU9cqgq3S`  
**Status:** completed  
**Milestone:** Repair a materially false statement shape at the
admitted boundary: both Cheeger axioms passed
`regularNormalizedLaplacian A d` to `lambda2`, which is
`evals (laplacian ·) 1` — so the asserted spectral quantity was
`λ₂(L(L_sym)) = λ₂(-L_sym)`, not `λ₂(L_sym)`. On the two-vertex edge
the lower-bound instance reads `1/2 ≤ 0`, false; the documented and
cited intent is Chung Ch. 2's `φ²/2 ≤ λ₂(L_sym) ≤ 2φ`. Delivered as an
emergency repair (architecture §9) at unchanged names and hypotheses.

**Changes:** `GraphTheory.Spectral` gains five proved declarations:
`secondEval` (matrix-facing second sorted eigenvalue — the correct
spectral side for operators that are not adjacency matrices),
`lambda2_eq_secondEval` (adjacency-facing bridge),
`evals_mem_eigvalOf` (sorted-spectrum ↔ eigenbasis connection),
`eigvalOf_sum_eq_trace` (trace from the unitary diagonalization), and
`eigvalOf_le_of_quadForm_nonpos` (one-sided Rayleigh eigenvalue
bound). `GraphTheory.Cheeger` restates both axioms at
`secondEval (regularNormalizedLaplacian A d) …` with the correction
recorded in the docstrings. `Cheeger_QA.lean` (26 declarations, +19)
adds the `Fin 2` edge fixture (`edgeAdj`), the **proved refutation**
`old_cheeger_lower_bound_refuted_QA` (old instance on `K₂` implies
`1/2 ≤ 0` via the Rayleigh bound on `L(L_sym) = -L_sym` and
`cheegerConstant = 1`), the **value pinning**
`edge_normLap_secondEval_eq_two_QA` (`λ₂(L_sym) = 2`, computed from
trace + determinant + sortedness through `Multiset.sort_eq` — no
axiom, no spectral-theorem computation), `cheeger_bounds_edge_QA`
(the corrected sandwich on the fixture: `1/2 ≤ 2 ≤ 2`), and the
coherence lemmas at the corrected shape. Scoreboard, radar, SGT index
map, and Chung source index updated with the correction record.

**Decisive commands and outcomes:** `lake env lean` on Spectral,
Cheeger, and Cheeger_QA (zero output — clean elaboration, zero
warnings); `lake build Scaffold.Mathlib.GraphTheory.{Spectral,Cheeger}`
✔; all nineteen QA modules + the changed public modules built directly
✔; full `lake build` ✔ (2161 targets); `lint_axioms`,
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(240 QA declarations, 0 placeholders, 18 axioms unchanged).

**Verification:** the refutation and the value pinning are both proved
statements, conditional on no axiom; the corrected axioms' conclusions
are exercised on a fixture where the old and new shapes separate
numerically (`0` vs `2`). Consumers were grep-audited before the change:
only `Cheeger_QA.lean` used the axioms; `lambda2_variational` and all
other `lambda2` uses are correct and untouched.

**Trust boundary:** unchanged in size (18 explicit cited axioms); both
Cheeger axioms remain admitted and downstream use stays conditional on
them. The repair changes *what* is asserted, aligning the Lean
statement with the cited source; it is not a proof of the axioms.

**Remaining risk:** the corrected axioms are regular-graph statements;
the irregular Cheeger shape (through
`rayleigh_normalizedLaplacian_degreeSqrt`) remains open and needs a
precise source and consumer. Eigenvalue pinning is so far limited to
two-point fixtures; `evals (c • M)` excavation remains gated (though
the new trace/membership tools lower its cost).

**Next handoff:** the `evals (c • M) = c • evals M` excavation; an
irregular Cheeger statement shape with a named consumer; or backlog
item 3 variants with named algorithm consumers.

## 2026-08-18T03:18:31Z — Electrical-crust step 1: connectivity/kernel characterization (in progress)

**Run:** `20260818T031831Z-run-1`  
**Session:** `ses_fed249ea1ffeNPR0xYcQVtoj2z`  
**Status:** in-progress  
**Milestone:** Operator-directed: `proposals/electrical-structure-crust.md`
step 1 ONLY — prove the converse of `laplacian_ones_in_kernel`: for a
connected weighted graph, `ker (laplacian A)` is exactly the constants.
Pure hard crust, no new axioms; obstruction goes to
`docs/6_SGT_BACKLOG.md` if unprovable. Proposal steps 2–5 (effective
resistance, Rayleigh monotonicity, Foster) out of scope.

**Pre-edit decision (recorded in the execution plan):** connectivity is
adopted as Mathlib `SimpleGraph.Connected` via a `WAdj → SimpleGraph`
adapter `supportGraph A hA` (`Adj i j ↔ i ≠ j ∧ 0 < A i j`; looplessness
forces the conjunct, and positive diagonal self-loops cancel in `D − A`).
Rationale: reuses Mathlib's walk induction for propagation, the
`Connected` field `Nonempty` discharges the empty-type case, avoids
duplicating `Walk`/`Reachable`, and creates the first WAdj→SimpleGraph
bridge (the radar's standing interop deviation). Cost: two new Mathlib
imports in `Spectral.lean`, mitigated by the `supportGraph_adj`
interface lemma.

**Planned proof path:** kernel vector ⇒ zero quadratic form ⇒ termwise
`(f i − f j)² = 0` on positive weights (via `laplacian_quadForm` +
nonneg weights) ⇒ `f` constant along support-graph walks ⇒ constant on
`V` by connectivity; then assemble
`ker (mulVecLin (laplacian A)) = span ℝ {onesVec}`. QA with connected
positive witness (3-path) and disconnected negative witness
(two-component `Fin 4` graph: component indicator in kernel, not
constant).

## 2026-08-18T03:38:08Z — Electrical-crust step 1 delivered: kernel = constants on connected graphs (completed)

**Run:** `20260818T031831Z-run-1`  
**Session:** `ses_fed249ea1ffeNPR0xYcQVtoj2z`  
**Status:** completed  
**Milestone:** `proposals/electrical-structure-crust.md` step 1 ONLY —
the converse of `laplacian_ones_in_kernel`: for symmetric nonnegative
weights whose support graph is connected, `ker (laplacian A)` is
exactly the constants. Delivered as pure hard crust; **no new axioms**
(explicit axiom count unchanged at 18). Proposal steps 2–5 untouched.

**Changes:** `GraphTheory.Spectral` (new section 5; sections 5–6
renumbered to 6–7; two Mathlib imports added:
`Combinatorics.SimpleGraph.Path`, `LinearAlgebra.Matrix.ToLin`): the
`supportGraph` adapter (`WAdj → SimpleGraph`, `Adj i j ↔ i ≠ j ∧
0 < A i j`; the `i ≠ j` conjunct is forced by looplessness — positive
diagonal self-loops cancel in `D − A`) with interface lemma
`supportGraph_adj`; `eq_of_laplacian_mulVec_eq_zero_of_pos_weight`
(zero Dirichlet energy ⇒ `(f i − f j)² = 0` termwise on positive
weights, via `laplacian_quadForm` + `Finset.sum_eq_zero_iff_of_nonneg`);
`eq_of_supportGraph_walk` (propagation by induction on
`SimpleGraph.Walk`); `exists_const_of_laplacian_mulVec_eq_zero` (anchor
vertex from `Connected`'s bundled `Nonempty`; value propagated along
walks); `laplacian_mulVec_const`; iff form
`laplacian_mulVec_eq_zero_iff_exists_const`; headline span form
`laplacian_kernel_eq_span_onesVec`
(`ker (mulVecLin (laplacian A)) = span ℝ {onesVec}` — the shape
effective-resistance uniqueness will consume). New QA
`SpectralGraph/Connectivity_QA.lean` (15 declarations): connected
witness at the 3-vertex path (connectivity by explicit walks through
the center; both iff directions; constant recovered and pinned to `5`;
non-constant `![1,0,0]` computed out of the kernel entrywise) and
disconnected negative witness at two disjoint `Fin 4` edges (component
indicator `![1,1,0,0]` computed into the kernel yet not constant;
support graph proved not connected via a walk block invariant) — the
connectivity hypothesis is load-bearing. Docs: backlog item 7 records
step 1 delivered with named step-2 consumers; SGT index map, scoreboard
(static counts + verification record + interpretation bullet) updated;
radar re-scored per protocol (see below).

**Decisive commands and outcomes:** `lake env lean` on
`GraphTheory.Spectral` — zero errors, zero new warnings (six
pre-existing linter notes in untouched code); `lake env lean` on
`QA.SpectralGraph.Connectivity_QA` — zero output; `lake build Scaffold
.QA.SpectralGraph.Connectivity_QA` ✔ (2009 targets); full `lake build`
✔ (2171 targets); `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated: 255 QA
declarations (+15), 0 placeholders, 18 axioms unchanged.

**Verification:** every new declaration is a Lean-checked theorem
conditional on no Scaffold axiom; QA includes both the connected
positive witness and the disconnected negative witness the direction
required. Radar re-scored only after proof + QA landed, per protocol:
subject axis 6 (electrical) 0.5 → 1.0 (connectivity hinge proved; no
electrical quantity defined yet), subject axis 1 (models) 2.5 → 3.0
(first `SimpleGraph` adapter), assurance Mathlib interop 3.5 → 4.0
(the matrix-first deviation is bridged one direction and genuinely
consumed by the center theorem). The README coverage snapshot's two
affected cells were synced to the radar (the snapshot was added
concurrently during this run; its other content untouched).

**Trust boundary:** unchanged in size (18 explicit cited axioms); this
slice added no axioms and consumes none.

**Remaining risk:** `supportGraph` is one-directional (`toWAdj` still
open); the span theorem's `hconn` hypothesis is phrased through the
adapter, so future refactors of that definition touch consumers (the
`supportGraph_adj` lemma is the stable interface). Concurrent operator
edits during this run (README snapshot, proposal re-sequencing,
`cdx-sgt-radar-axes.md` deletion) were preserved untouched except the
two README score cells synced above.

**Next handoff:** proposal step 2 — effective resistance by the
potential equation (`IsEffectiveResistance A u v r ↔ ∃ f,
laplacian A *ᵥ f = e u − e v ∧ f u − f v = r`), whose
well-definedness consumes `laplacian_kernel_eq_span_onesVec`; or the
open earlier candidates (`evals (c • M)` excavation; irregular Cheeger
shape; backlog item 3 variants).

## 2026-08-18T04:27:41Z — SimpleGraph→WAdj interoperability adapter (in progress)

**Run:** `20260818T042204Z-run-1`  
**Session:** `ses_fece519a1ffeRIOcnxA00ZWV1f`  
**Status:** in-progress  
**Milestone:** `proposals/electrical-structure-crust.md` step 1 under the
2026-08-18 re-sequenced numbering — deliver `SimpleGraph.toWAdj`, the
`SimpleGraph → WAdj` adapter the proposal calls "the highest compounding
multiplier available". SGT leverage: converts every proved Scaffold
theorem into something callable on Mathlib `SimpleGraph` objects,
completes the two-directional adapter surface begun with `supportGraph`,
and folds in the neutral re-export of Mathlib's unweighted
kernel/component results. Pure hard crust, no new axioms; one step per
run (steps 2–6 untouched).

**Scope note:** the previous run's operator direction predated the
proposal re-sequencing; effective resistance is now step 5 and gated
behind step 4 (solvability), so the plan's earlier "next: effective
resistance" handoff is superseded by this step-1 delivery.

**Planned:** new module `GraphTheory/SimpleGraphAdapter` with
`toWAdj G = G.adjMatrix ℝ`, proved agreement (`toWAdj_symm`,
`toWAdj_nonneg`, `deg_toWAdj`, `vol_toWAdj` + handshake,
`laplacian G.toWAdj = G.lapMatrix ℝ`, boundary as crossing-edge count),
roundtrip `supportGraph (toWAdj G) = G`, connected-`G` kernel corollary,
and the two Mathlib re-exports (kernel/reachable iff, component-count
finrank). QA at the 3-vertex path plus the two-edge `Fin 4` negative
witness (component indicator in kernel but outside `span {onesVec}`).

## 2026-08-18T06:13:31Z — SimpleGraph→WAdj interoperability adapter delivered (completed)

**Run:** `20260818T042204Z-run-1`  
**Session:** `ses_fece519a1ffeRIOcnxA00ZWV1f`  
**Status:** completed  
**Milestone:** `proposals/electrical-structure-crust.md` step 1 under
the 2026-08-18 re-sequenced numbering — `SimpleGraph.toWAdj`, the
`SimpleGraph → WAdj` adapter, completing the two-directional Mathlib
bridge begun with `supportGraph`. Pure hard crust; **no new axioms**
(explicit count unchanged at 18). One step per the proposal's operating
instructions; steps 3–6 untouched.

**Changes:** new `Scaffold/Mathlib/GraphTheory/SimpleGraphAdapter.lean`
(16 declarations, all proved): `SimpleGraph.toWAdj` (deliberately
defined as Mathlib's `adjMatrix ℝ` so no parallel matrix construction
can drift out of agreement) with interface lemma `toWAdj_apply`;
`toWAdj_symm`, `toWAdj_nonneg` (0/1 weights discharge every `hnonneg`
hypothesis of the center); agreement family `deg_toWAdj` (via
`degree_eq_sum_if_adj`), `vol_toWAdj_eq_sum_degrees`, handshake
`vol_toWAdj_univ_eq_two_mul_card_edges` (Mathlib's
`sum_degrees_eq_twice_card_edges` transferred), headline
`laplacian G.toWAdj = G.lapMatrix ℝ`, boundary as the crossing-edge
count (`boundary_toWAdj_eq_sum_neighbors`,
`boundary_toWAdj_eq_sum_card_neighbors` — each crossing edge counted
exactly once); neutral re-exports `laplacian_toWAdj_mulVec_eq_zero_iff_reachable`
and `finrank_ker_laplacian_toWAdj` (Mathlib's unweighted kernel and
component-count results transferred by one-two rewrites); roundtrip
`supportGraph_toWAdj_eq_self`; connected-`G` corollary
`laplacian_toWAdj_kernel_eq_span_ones` (the delivered span theorem
applied to Mathlib graphs through the roundtrip). New QA
`SpectralGraph/SimpleGraphAdapter_QA.lean` (38 declarations): 3-vertex
path `SimpleGraph` fixture with weights, degrees (1,2,1), Laplacian
entries, *both* Laplacian sides, boundary `{1} = 2`, volume `4`,
handshake `4 = 2·2`, kernel span/iff instances, constant-in-kernel
pinned to `5`, and `![1,0,0]` computed out of the kernel entrywise;
disconnected `Fin 4` negative witness with the component indicator
computed into the kernel, not constant, outside `span {onesVec}`, and
the kernel proved ≠ `span {onesVec}` — connectivity load-bearing
through the adapter. Umbrella, SGT index map, scoreboard, backlog
item 7, radar, README updated.

**Decisive commands and outcomes:** environment repair first — the
local `.lake/build` was found pruned (Mathlib oleans 1795/5685, all
modules this slice needs missing); re-ran the recorded interpreter
cache fetch (`lake env lean --run Cache/Main.lean get` from the
mathlib package root: 5685 files, 100% success), then `lake build
Scaffold.Mathlib.GraphTheory.Spectral` recompiled the 2008-target
residue to completion. `lake env lean` on the new public module —
zero errors/warnings after fixes (named-argument forms for
`isSymm_adjMatrix`/`degree_eq_sum_if_adj`, cast bookkeeping in the
card-form boundary, `omit`s for unused section variables); `lake env
lean` on the new QA module — zero output; `lake build` of both targets
✔; full `lake build` ✔ (2177 targets); all 21 QA modules built
directly in one batch (exit 0); `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated: 293 QA
declarations (+38), 0 placeholders, 18 axioms unchanged.

**Verification:** every new declaration is a Lean-checked theorem
conditional on no Scaffold axiom; the QA computes adapter values from
the definitions (not by rewriting with the agreement theorems), per
the falsification-QA standard, and includes both the connected
positive witness and the disconnected negative witness the step
required. Radar re-scored only after proof + QA landed, per protocol:
Mathlib interop 4.0 → 4.5 (both directions tied by a proved roundtrip;
Mathlib kernel/component results transferred; remaining deviation only
`MatrixMDS`/filtration), subject axis 1 (models) 3.0 → 3.5; QA axis
text updated to 293 declarations / 21 modules (score unchanged). README
coverage-snapshot cell and maturity bullet synced.

**Trust boundary:** unchanged in size (18 explicit cited axioms); this
slice added no axioms and consumes none.

**Remaining risk:** the component-count transfer covers only 0/1
weights (`finrank_ker_laplacian_toWAdj` is about `toWAdj G`) — the
weighted generalization is exactly proposal step 3
(`ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)`); `toWAdj`
QA fixtures are small graphs only (no parametric QA — standing QA-axis
gap). Concurrent operator edits in the tree (AGENTS.md, strategy
revision, new proposals `get-outside-signal.md`,
`prove-lambda2-variational.md`, `sell-the-methodology.md`, untracked
coverage map) were preserved untouched.

**Next handoff:** proposal step 3 — the kernel-equality bridge for
weighted graphs, inheriting Mathlib's `lapMatrix_ker_basis` and
`card_ConnectedComponent_eq_rank_ker_lapMatrix`; then step 4
(potential solvability — the hinge; resistance is forbidden before it
lands). Or the open earlier candidates: `evals (c • M)` excavation;
irregular Cheeger shape with a named consumer; backlog item 3
variants.

## 2026-08-18T06:23:17Z — Electrical-crust step 3: kernel-equality bridge (in progress)

**Run:** `20260818T061620Z-run-1`
**Session:** `ses_fec7cb0f5ffe66xyhhSJgVZ1IY`
**Status:** in-progress
**Milestone:** Operator direction: advance
`proposals/electrical-structure-crust.md` **step 3 only** — prove the
kernel-equality bridge `ker (laplacian A) = ker ((supportGraph
A).lapMatrix ℝ)` and inherit Mathlib's component-indexed kernel facts
(`lapMatrix_ker_basis`, `card_ConnectedComponent_eq_rank_ker_lapMatrix`)
for the weighted Laplacian; one step per run, no new axioms, step 4 out
of scope.

**Pre-implementation survey (recorded):** pinned Mathlib
`LapMatrix.lean` provides the unweighted kernel/rank/basis family;
`Matrix.toLin'_apply'` (ToLin.lean:310) identifies `toLin' M` with
`mulVecLin M`; `Real.decidableLT` (noncomputable, Real/Basic.lean:539)
makes `DecidableRel (supportGraph A hA).Adj` elaborable for free;
`SimpleGraph.Adj.reachable` (Path.lean:664) converts adjacency to
reachability. The bridge's weighted side needs one new center fact —
the no-connectivity characterization `L *ᵥ f = 0 ↔ f constant on
support-graph components` (step 2 delivered only the connected case);
direction "component-constant ⇒ kernel" is new and goes entrywise
through a diffusion-form identity for `(L *ᵥ f) i`.

**Next action:** implement (a) center lemmas in `Spectral.lean`, (b)
bridge + transfers in `SimpleGraphAdapter.lean`, (c) QA
`SpectralGraph/KernelBridge_QA.lean` on the `Connectivity_QA`
fixtures, then verify by direct elaboration and full build.

## 2026-08-18T06:45:01Z — Electrical-crust step 3 delivered: kernel-equality bridge (completed)

**Run:** `20260818T061620Z-run-1`
**Session:** `ses_fec7cb0f5ffe66xyhhSJgVZ1IY`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 3 only" — the
kernel-equality bridge and the inherited Mathlib component facts for
the weighted Laplacian. One step per run; step 4 (potential
solvability) was not started, per the proposal's scope fence.

**Changes.** Center (`Scaffold/Mathlib/GraphTheory/Spectral.lean`):
`laplacian_mulVec_apply` (diffusion-form entrywise action; self-loops
cancel), `laplacian_mulVec_eq_zero_of_forall_reachable`
(component-constant ⇒ kernel, entrywise, no connectivity hypothesis),
`laplacian_mulVec_eq_zero_iff_forall_reachable` (component-form
characterization — the weighted counterpart of Mathlib's unweighted
iff). Bridge (`GraphTheory/SimpleGraphAdapter.lean`):
`supportGraphAdjDecidable` (decidability prerequisite for Mathlib's
`lapMatrix` API, invisible through the `supportGraph` projection;
`Real.decidableLT`), the headline `ker_laplacian_eq_ker_
supportGraph_lapMatrix` (`ker (laplacian A) = ker ((supportGraph
A).lapMatrix ℝ)`), `finrank_ker_laplacian_eq_card_supportGraph_
components` (kernel dimension = component count for weighted graphs),
and the transported component-indicator basis `laplacian_ker_basis` /
`laplacian_ker_basis_apply`. New QA
`Scaffold/QA/SpectralGraph/KernelBridge_QA.lean` (14 declarations)
reusing the `Connectivity_QA` fixtures. Docs: execution plan, this
journal, backlog item 7, radar (subject axis 6 re-scored 1.0 → 1.5
per protocol; QA-axis counts updated to 307/22), proposal checklist
marked step 3 delivered with a delivery note (including the recorded
decidability prerequisite), scoreboard (regenerated + verification
rows and a dated provenance note), SGT index map.

**Verification.** `lake env lean` zero errors/zero warnings on
`SimpleGraphAdapter` and `KernelBridge_QA`; zero errors on `Spectral`
(no new warnings — the six pre-existing linter notes untouched);
`lake build Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter` ✔; full
`lake build` ✔ (2177 targets); all twenty-two QA modules elaborated
directly in one batch (zero failures); no `sorry`/`admit` under
`Scaffold/`; `lint_axioms`, `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (307 QA declarations, 18 explicit
axioms — unchanged; the slice is pure hard crust).

**Trust boundary:** unchanged (18 explicit cited axioms); this slice
added no axioms and consumes none. The inherited basis/count facts are
Mathlib theorems transferred through a proved bridge, not new trust.

**Remaining risk.** The transported `laplacian_ker_basis` requires a
`DecidableEq ConnectedComponent` instance at use sites (classical
suffices; QA uses it without incident). The QA fixtures are small
graphs only — no parametric property QA (standing QA-axis gap). The
bridge inherits Mathlib's component *count/basis* but not any
electrical quantity: solvability (step 4) is still open, and the
proposal forbids defining effective resistance before it lands.

**Next handoff:** proposal step 4 — potential solvability for
zero-sum demand (`∃ f, L *ᵥ f = b` when `∑ b = 0`; specialize to
`b = e u − e v`), recording the route decision (orthogonality vs
constructive eigenbasis) before stating; then step 5 (resistance
uniqueness, consuming `laplacian_kernel_eq_span_onesVec`). Or the
open earlier candidates: `evals (c • M)` excavation; irregular
Cheeger shape with a named consumer; backlog item 3 variants.

## 2026-08-18T07:01:06Z — Electrical-crust step 4 started: potential solvability

**Run:** `20260818T070106Z-run-1`
**Session:** `ses_fec5a1003ffeuJmMzrd6DtYfoa`
**Status:** in-progress
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 4 only" — the potential
solvability hinge (`∃ f, laplacian A *ᵥ f = b` for zero-sum `b` on a
connected graph), which the proposal gates ahead of any definition of
effective resistance.

**Pre-implementation survey and route decision (recorded before
stating):** constructive eigenbasis route chosen over the orthogonality
route. The pin has no ready-made `range = (ker)ᗮ` lemma for the
function-type spaces the center uses (targeted search over
`Analysis/InnerProductSpace/` this run; same finding as the proposal's
own survey), while the center already proves orthonormality
(`eigvecOf_inner`), completeness (`eigvecOf_complete`), the eigenvector
equation (`mulVec_eigenvectorBasis`), and the kernel span theorem
(`laplacian_kernel_eq_span_onesVec`, proposal step 2). The witness
`f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b / λᵢ) • vᵢ` consumes all of them, making the
solvability theorem load-bearing on the step-2 kernel shape exactly as
the strategy's falsifiability principle asks. Supporting lemma: the
reciprocity identity `w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ f`
(`Matrix.dotProduct_mulVec` + Laplacian symmetry).

**Next action:** center block in `GraphTheory.Spectral` (reciprocity,
kernel corollary, main existence theorem, unit-demand specialization),
QA `SpectralGraph/PotentialSolvability_QA.lean` with positive and both
negative witnesses (non-zero-sum unsolvable on a connected fixture;
zero-sum unsolvable on the disconnected fixture), then direct
elaboration, target builds, full build, hygiene scripts, scoreboard.

## 2026-08-18T07:27:05Z — Electrical-crust step 4 delivered: potential solvability (completed)

**Run:** `20260818T070106Z-run-1`
**Session:** `ses_fec5a1003ffeuJmMzrd6DtYfoa`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 4 only" — the potential
solvability hinge: on a connected graph (symmetric, nonnegative
weights), every zero-sum demand `b` admits a potential `f` with
`laplacian A *ᵥ f = b`, specialized to the unit demand `e u − e v`.
One step per run; step 5 (effective resistance) was not started, per
the proposal's scope fence — the proposal forbids defining resistance
before this hinge lands, and it now has.

**Route decision (executed as recorded before stating).** Constructive
eigenbasis: witness `f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b / λᵢ) • vᵢ`. The pin
(re-surveyed) still lacks a ready-made `range = (ker)ᗮ` lemma for the
center's function-type spaces, while the route consumes the proved
eigenbasis algebra and the step-2 kernel theorem — load-bearing on
both, per the strategy's falsifiability principle.

**Changes.** Center (`Scaffold/Mathlib/GraphTheory/Spectral.lean`):
`laplacian_dotProduct_mulVec` (reciprocity / discrete Green identity),
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (kernel vectors
certify unsolvability), `mulVec_eigvecOf_sum_apply` (entrywise action
on eigenbasis combinations), `exists_mulVec_eq_of_zero_comp`
(constructive spectral inversion), `exists_laplacian_mulVec_eq_of_sum_
eq_zero` (the hinge), `exists_laplacian_mulVec_eq_single_sub_single`
(unit demand; step 5's defining equation). New QA
`Scaffold/QA/SpectralGraph/PotentialSolvability_QA.lean` (12
declarations): edge fixture + `Connectivity_QA` fixtures; computed
potentials `![1,0]` and `![1,0,−1]`; theorem instantiations; proved
*unsolvability* witnesses for both hypotheses (non-zero-sum `e₀` on
the connected edge via the all-ones certificate; zero-sum
cross-component `e₀ − e₂` on the disconnected fixture via the
component-indicator certificate). Docs: execution plan, this journal,
backlog item 7, radar (subject axis 6 re-scored 1.5 → 2.0 per
protocol — the potential equation is now completely characterized on
connected graphs; QA-axis counts updated to 319/23), scoreboard
(regenerated; verification rows and a solvability interpretation
bullet), SGT index map, README snapshot, proposal checklist marked
step 4 delivered with the route decision and one implementation note
(`rw [Finset.mul_sum]` instance-matching quirk; `simp only` used).

**Verification.** `lake env lean` zero errors/zero new warnings on
`GraphTheory.Spectral` (eight pre-existing linter notes untouched);
zero errors/zero warnings on `PotentialSolvability_QA`; `lake build`
of the QA target and of `SimpleGraphAdapter` (downstream consumer) ✔;
full `lake build` ✔ (2177 targets); all twenty-three QA modules
elaborated directly in one batch (zero failures); no `sorry`/`admit`
under `Scaffold/`; `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (319 QA
declarations, 18 explicit axioms — unchanged; pure hard crust).

**Trust boundary:** unchanged (18 explicit cited axioms); this slice
added no axioms and consumes none. The solvability theorems are
unconditional proved hard crust.

**Remaining risk.** The unsolvability direction is QA-witnessed, not
yet a center theorem (`∃ kernel-certificate ⇔ unsolvable` is the
natural next center statement; reciprocity makes it short). No
parametric property QA (standing QA-axis gap). Environment: ~300
Mathlib oleans pruned at run start (recorded debt); everything this
slice needed was present, so no cache fetch was required — but the
pruning may recur and cost a later run the recorded interpreter fetch.

**Next handoff:** proposal step 5 — define `effectiveResistance` by
the potential equation (`IsEffectiveResistance A u v r ↔ ∃ f, L *ᵥ f
= e u − e v ∧ f u − f v = r`): existence from step 4, uniqueness of
`r` from `laplacian_kernel_eq_span_onesVec`; then symmetry,
nonnegativity, `R u u = 0`, and the energy identity (proposal
authorizes splitting step 5 across two runs if needed). Or the open
earlier candidates: `evals (c • M)` excavation; irregular Cheeger
shape with a named consumer.

## 2026-08-18T11:25:36Z — Electrical-crust step 5 started: effective resistance

**Run:** `20260818T112536Z-run-1`
**Session:** `ses_feb641df5ffenZ7eBJVWZpWAtK`
**Status:** in-progress
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 5 only" — effective
resistance by the potential equation (`IsEffectiveResistance A u v r ↔
∃ f, laplacian A *ᵥ f = e u − e v ∧ f u − f v = r`), now unlocked by
the delivered step-4 solvability hinge; existence consumes step 4,
uniqueness of `r` consumes the step-2 kernel theorem, making the new
definition load-bearing on both per the falsifiability principle.

**Pre-implementation decisions (to be recorded in the plan):** new
public module `GraphTheory/Electrical.lean` (keeps the 1198-line
`Spectral.lean` from growing; mirrors Mathlib's topic layout), QA
`SpectralGraph/EffectiveResistance_QA.lean` reusing the
`Connectivity_QA`/`PotentialSolvability_QA` fixtures. Mathlib survey
for an existing effective-resistance result runs before writing the
proof, per the proposal's operating instructions.

**Next action:** survey the Mathlib pin (record either way), then the
module (relation, existence, uniqueness of `r`, total
`effectiveResistance` + agreement, energy identity, symmetry,
nonnegativity, `R u u = 0`), QA with positive, fallback-honesty, and
non-unique-potential/unique-`r` witnesses, then direct elaboration,
target builds, full build, hygiene scripts, scoreboard, and doc
updates (backlog item 7, radar subject axis 6, SGT index map, proposal
checklist).

## 2026-08-18T11:38:59Z — Electrical-crust step 5 delivered: effective resistance (completed)

**Run:** `20260818T112536Z-run-1`
**Session:** `ses_feb641df5ffenZ7eBJVWZpWAtK`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 5 only" — effective
resistance as a defined, well-determined quantity: the
potential-equation relation `IsEffectiveResistance A u v r`, a total
`effectiveResistance` with proved agreement, the energy identity at
solution and function level, symmetry, nonnegativity, and `R u u = 0`.
One step per run; step 6 (the one-sided Dirichlet bound) was not
started. No new axioms (count unchanged at 18) — pure hard crust.

**Mathlib survey (recorded before stating, per the proposal's
operating instructions):** no effective-resistance or "resistance"
declaration anywhere in the pin; no Moore–Penrose pseudoinverse —
the potential-equation definition is the only available route.

**Changes.** New public module
`Scaffold/Mathlib/GraphTheory/Electrical.lean` (17 declarations, all
proved): `IsEffectiveResistance`; hypothesis-free diagonal
characterization `isEffectiveResistance_self_iff`; hypothesis-free
relation symmetry `isEffectiveResistance_symm`; existence
`exists_isEffectiveResistance` (consumes step 4's unit-demand
solvability); uniqueness `isEffectiveResistance_unique_of_reachable` —
stated at reachability-pair strength through step 3's component-form
kernel characterization, so it holds within a component of a
disconnected graph (strictly stronger than the proposal's connected
sketch) — with the connected corollary; the total function
`effectiveResistance` (classical choice; junk fallback `0` **stated,
not hidden** via `effectiveResistance_eq_zero_of_not_exists`);
agreement theorems (`effectiveResistance_eq_of_reachable`,
`effectiveResistance_eq`); the energy identity at solution level
(`quadForm (laplacian A) f = f u − f v` for any solution, no
hypotheses) and function level (`effectiveResistance_eq_quadForm`);
`effectiveResistance_nonneg` (from `laplacian_psd`);
`effectiveResistance_symm`; `effectiveResistance_self`. New QA
`Scaffold/QA/SpectralGraph/EffectiveResistance_QA.lean` (17
declarations, reusing the `Connectivity_QA`/`PotentialSolvability_QA`
fixtures): values computed from the definitions (unit edge `R 0 1 = 1`,
3-path `R 0 2 = 2` — series edges add), the energy identity
cross-checked against an energy computed independently from the raw
definitions, the junk fallback pinned on the disconnected fixture
(cross-component pair: no value exists, proved from the step-4
unsolvability witness, while the function reads `0` — fallback, not
measurement), and same-component witnesses (two distinct potentials
pinning one value `1` through the reachability-form agreement where
the connected theorem's hypothesis fails). Docs: umbrella, execution
plan, this journal, scoreboard (336 QA declarations, 24 modules; new
interpretation bullet; QA-target row updated), SGT index map (new
`Electrical` section), backlog item 7, radar (subject axis 6 re-scored
2.0 → 2.5 per protocol — the first electrical quantity; below 3.0
while the Dirichlet bound, monotonicity, metric inequality, and
Matrix–Tree/Kirchhoff are absent), README snapshot (counts, umbrella,
crust description, axis cell), and the proposal checklist (steps 1–5
of 6 delivered, with the delivery note recording the two strengthening
deviations and the named definiteness residual).

**Verification.** `lake env lean` zero errors/zero warnings on
`GraphTheory.Electrical` and on `EffectiveResistance_QA`; `lake build`
of the QA target and of `SimpleGraphAdapter` (downstream consumer) ✔;
full `lake build` ✔ (2178 targets); all twenty-four QA modules
elaborated directly in one batch (zero failures); no `sorry`/`admit`
under `Scaffold/` (tactic-level scan; textual matches are prose only);
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (336 QA declarations, 18 explicit axioms —
unchanged).

**Trust boundary:** unchanged (18 explicit cited axioms); this slice
added no axioms and consumes none. The resistance package is
unconditional proved hard crust, load-bearing on the step-2/3 kernel
characterization and the step-4 solvability theorem (a defect in
either would break uniqueness or agreement rather than pass beside
them).

**Remaining risk.** `effectiveResistance` is noncomputable (classical
choice), so QA pins values through the agreement theorems rather than
`decide` on the function itself — the standard trade for totality.
Component-restricted *solvability* is still implicit (agreement needs a
witness in hand; on a disconnected graph, same-component existence is
QA-witnessed but not yet a center theorem). No parametric property QA
(standing QA-axis gap).

**Next handoff:** proposal step 6 — the one-sided Dirichlet bound
`R u v ≥ (f u − f v)² / quadForm (laplacian A) f` (Cauchy–Schwarz
over the energy identity; the direction applications use to
lower-bound resistance), plus the cheap definiteness residual
`R u v = 0 ↔ u = v` (reachable pair). Or the still-open earlier
candidates: `evals (c • M)` excavation; irregular Cheeger shape with
a named consumer.

## 2026-08-18T14:06:54Z — Electrical-crust step 6 started: one-sided Dirichlet bound

**Run:** `20260818T140654Z-run-1`
**Session:** `ses_fead1b54bffecXkdKzAHJaWoVS`
**Status:** in-progress
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 6 only" — the one-sided
Dirichlet bound `(f u − f v)² / quadForm (laplacian A) f ≤
effectiveResistance A u v` for any test potential `f` with positive
energy. Leverage: it is the direction every application uses to
lower-bound resistance, and its proof is load-bearing on `laplacian_psd`
(polarization of the PSD quadratic form) and on the step-4/step-5
solvability-and-energy chain — per the falsifiability principle, an
error in those would break this proof rather than pass beside it.

**Route (recorded before stating):** expand `quadForm L (f − t • g)`
via the proved reciprocity `laplacian_dotProduct_mulVec`; nonnegativity
for all `t` (from `laplacian_psd`) forces the discriminant bound at
`t = c/E` (degenerate `E = 0` case separately); the cross term is
`f u − f v` through the step-4 potential and the solution-level energy
identity. No attained supremum — the full Dirichlet principle stays
deferred per the proposal.

**Next action:** survey the Mathlib pin for a usable PSD Cauchy–Schwarz
(record either way), implement in `GraphTheory.Electrical`, QA in
`EffectiveResistance_QA.lean` (equality/strict positive witnesses,
reverse-inequality refutation, zero-energy disconnected guard witness),
direct elaboration + target builds + full build + hygiene scripts, then
proposal checklist, backlog item 7, radar, index map, scoreboard, README
snapshot.

## 2026-08-18T14:21:59Z — Electrical-crust step 6 delivered: one-sided Dirichlet bound; program complete (completed)

**Run:** `20260818T140654Z-run-1`
**Session:** `ses_fead1b54bffecXkdKzAHJaWoVS`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/electrical-structure-crust.md`, step 6 only" — the one-sided
Dirichlet bound `(f u − f v)² / quadForm (laplacian A) f ≤
effectiveResistance A u v`, delivered as the proposal's final step;
steps 1–6 are now all proved hard crust, axiom count 18 throughout.

**Mathlib survey (recorded before proving):** the pin's only
Cauchy–Schwarz is the definite inner-product-space one; the Laplacian
form is semidefinite, unusable without quotienting the kernel; no
`QuadraticForm` C–S at these function types — polarization route taken.

**Changes.** `Scaffold/Mathlib/GraphTheory/Electrical.lean` +4 proved
declarations: `sq_le_mul_of_forall_zero_le_sub` (nonnegative-everywhere
quadratics have nonpositive discriminants), `quadForm_laplacian_sub_smul`
(polarization; mixed terms collapse via the proved reciprocity),
`laplacian_cauchy_schwarz` (`(f ⬝ᵥ L g)² ≤ quadForm L f · quadForm L g`,
no connectivity hypothesis — reusable), and the headline
`effectiveResistance_ge_sq_div_quadForm` (division guarded by
`0 < quadForm`). Load-bearing chain: cross term = `f u − f v` through
the step-4 demand potential, energy = `R u v` through the step-5 energy
identity, C–S through `laplacian_psd`. QA
`SpectralGraph/EffectiveResistance_QA.lean` +9 (345 total): attainment
at both harmonic potentials (edge `1/1 = 1`, path `4/2 = 2`, energies
computed from raw definitions), strictness at a non-harmonic potential
(`1 < 2`), the reverse inequality refuted numerically (`2 ≤ 1` false —
one-sidedness forced), and the `0 <` energy guard witnessed on the
disconnected fixture (zero-energy indicator with voltage difference
`1`). Docs: scoreboard, radar (subject axis 6 re-scored 2.5 → 3.0 per
protocol after proof + QA landed; QA count synced 345/24), backlog item
7 (program complete, definiteness residual named), SGT index map,
README snapshot, proposal checklist (all six steps ✅ with delivery
note).

**Verification.** `lake env lean` on `GraphTheory.Electrical` and
`EffectiveResistance_QA` — zero errors, zero warnings; `lake build` of
the QA target ✔ (2012) and full `lake build` ✔ (2178 targets); all 24
QA modules elaborated directly (zero errors; remaining outputs are
pre-existing `unusedSectionVars` warnings in untouched modules);
345 QA declarations, no `sorry`/`admit` under `Scaffold/` (prose-only
matches); 18 cited axioms unchanged; `lint_axioms`, `check_citations`,
`check_markdown_links`, scoreboard regeneration all pass.

**Concurrent-change note:** `docs/traction-plan.md` was modified
outside this run at 14:21Z (references this milestone's module as the
release-example candidate) and an untracked
`proposals/eng-use-cases.md` present at run start was removed; both
left exactly as found, not authored or reverted by this run.

**Remaining risk.** None new in the delivered slice; the axis-6
residuals stay as recorded (full Rayleigh monotonicity needs the
attained-supremum Dirichlet principle; resistance metric /
definiteness residual `R u v = 0 ↔ u = v`; Matrix–Tree/Kirchhoff
absent).

**Next handoff.** Cheap electrical residual `R u v = 0 ↔ u = v`
(reachable pair, reusing the step-2 zero-energy ⇒ constant argument);
or the standing earlier candidates: `evals (c • M) = c • evals M`
Mathlib excavation, an irregular Cheeger statement shape through
`rayleigh_normalizedLaplacian_degreeSqrt` (needs source + consumer), or
backlog item 3 variants with named consumers.

## 2026-08-18T14:46:27Z — lambda2_variational retirement started: prove in the matrix world; false-shape repair found

**Run:** `20260818T144627Z-run-1`
**Session:** `ses_feaba2b1dffeDvdW2qjgt9LQjm`
**Status:** in-progress
**Milestone:** Operator direction "advance
`proposals/prove-lambda2-variational.md`" — retire the
`lambda2_variational` axiom (18 → 17). Survey finding recorded before
stating anything: the axiom as admitted is materially false — symmetry
alone does not make `onesVec` a bottom eigenvector; on `Fin 2` with
`A = [[0,−1],[−1,0]]` the Laplacian has sorted spectrum `[−2, 0]`, so
`lambda2 = 0` while the Rayleigh sInf side is `−2`. Repair: add
`hnonneg : ∀ i j, 0 ≤ A i j` (matching `laplacian_psd`) at the same
name, then prove it — axiom retirement and emergency statement-shape
repair in one slice. Leverage: closes the radar axis-3 named gap
("λ₂ variational characterization admitted"), removes the stated
blocker of `proposals/prove-cheeger-easy-direction.md`, and every
consumer of the axiom inherits a proved foundation.

**Route (recorded before proving):** matrix-world proof through the
repo's proved eigenbasis machinery (Parseval expansion, spectral
resolution of `quadForm`, eigenvector–`onesVec` orthogonality, two
sorted-multiset counting lemmas via `Multiset.sort_eq` +
`filter_map`), not the proposal's LinearMap bridge — its step-5
multiplicity pin is exactly the counting done here, at lower cost.

**Next action:** implement in `GraphTheory.Spectral` (new proved
section; axiom → theorem), QA in `Variational_QA.lean` (old-shape
refutation on the negative-weight fixture, `K₂` exact instantiation,
disconnected `λ₂ = 0` instantiation), direct elaboration + target
builds + full build + hygiene scripts, then radar/index/source/proposal
and scoreboard updates.

## 2026-08-18T15:54:16Z — lambda2_variational delivered: proved Courant–Fischer, false axiom shape repaired, axioms 18 → 17 (completed)

**Run:** `20260818T144627Z-run-1`
**Session:** `ses_feaba2b1dffeDvdW2qjgt9LQjm`
**Status:** completed
**Milestone:** Operator direction "advance
`proposals/prove-lambda2-variational.md`" — delivered. The
`lambda2_variational` Courant–Fischer characterization of the algebraic
connectivity is now a **proved theorem** (same name, hypothesis
`hnonneg : ∀ i j, 0 ≤ A i j` added); the admitted axiom is retired and
the explicit axiom count drops 18 → 17.

**Falsity finding (recorded before stating):** the pre-repair axiom
assumed only symmetry. On `Fin 2` with `A = [[0,−1],[−1,0]]` it
asserted `0 = −2` (sorted spectrum `[−2, 0]`, every constraint vector a
multiple of `(1,−1)` with Rayleigh quotient `−2`). Same defect class as
the 2026-08-18 Cheeger repair; repaired per architecture §9 at the same
name.

**Route (matrix world; the proposal's LinearMap bridge was never
built):** new proved hard crust in `GraphTheory.Spectral` —
`eigvecOf_expansion_apply`, `dotProduct_eigvecOf` (Parseval),
`dotProduct_eigvecOf_mulVec`, `quadForm_eigvalOf` (spectral
resolution), `quadForm_eigvecOf_self`, `eigvecOf_ortho_onesVec`, the
two multiplicity pins `evals_one_le_max_of_ne` /
`exists_ne_eigvalOf_of_evals_head_eq` (the proposal's step-5
"argument to write", done by `Multiset.sort_eq`-based counting), and
`lambda2_variational`. `exists_mulVec_eq_of_zero_comp` refactored to
consume the extracted expansion lemma.

**Changes.** `Scaffold/Mathlib/GraphTheory/Spectral.lean` (axiom →
theorem + 12 supporting proved declarations; §7 now admits exactly one
statement); `Scaffold/QA/SpectralGraph/Variational_QA.lean` (+26
declarations: old-shape refutation on the negative-weight fixture,
`K₂` exact instantiation with `λ₂ = 2` computed twice independently,
disconnected `λ₂ = 0` on two disjoint edges, path bound `λ₂(P₃) ≤ 1`).
Docs: scoreboard (17/371/0 + retirement note), radar (subject axis 3:
3.0 → 3.5; axiom minimization 3.5 → 4.0, first axiom removed by proof;
proved-depth and QA text/count updated), Chung and Horn–Johnson source
indexes and SGT index map (rows marked theorem), README snapshot, both
proposals' status notes (delivered + normalized-instance scope caveat:
the Cheeger proposal's `secondEval L_sym` intermediate follows from
this plus the proved congruence transfer, but that step is not yet
written).

**Verification.** `lake env lean` on both changed modules — zero
errors, zero new warnings; `lake build` of the QA target ✔; full
`lake build` ✔ (2178 targets); all 24 QA modules elaborated directly
(zero failures); 371 QA declarations, no `sorry`/`admit` under
`Scaffold/` (prose-only matches); 17 cited axioms; `lint_axioms`,
`check_citations`, `check_markdown_links`, scoreboard regeneration all
pass.

**Concurrent-change note:** `proposals/electrical-structure-crust.md`
was re-statused outside this run and three untracked proposals
(`discovery-mcp-server.md`, `fiedler-partitioning.md`,
`mixing-time-bound.md`) appeared at run start (timestamps 07:33–07:42Z,
before this run began at 14:46Z); all left exactly as found, not
authored or reverted by this run.

**Remaining risk.** None new in the delivered slice. Recorded caveats:
the normalized-Laplacian variational instance (`secondEval L_sym`) is
one proved-transfer step away and not delivered; `lambda2_variational`'s
nonnegativity hypothesis means consumers must now supply it (no
in-repository consumers existed at retirement).

**Next handoff.** The normalized-instance transfer (combinatorial λ₂
variational + `rayleigh_normalizedLaplacian_degreeSqrt` → variational
characterization of `secondEval L_sym`), which is exactly the remaining
intermediate for `proposals/prove-cheeger-easy-direction.md`; the cheap
electrical residual `R u v = 0 ↔ u = v` (reachable pair); or the still
open `evals (c • M) = c • evals M` Mathlib excavation.

## 2026-08-18T17:01:01Z — Retire cheeger_upper_bound (Cheeger easy direction)

**Run:** `20260818T170101Z-run-1`
**Session:** `ses_fea3405d0ffeBFONeKeIHb6OtE`
**Status:** in-progress
**Milestone:** Prove the Cheeger easy direction (`λ₂(L_sym) ≤ 2φ`,
repo name `cheeger_upper_bound`) from a generalized Courant–Fischer
(`secondEval_variational` for any symmetric PSD `M` with
`M *ᵥ onesVec = 0`), retiring the axiom 17 → 16. Top High item in
`proposals/README.md`; the proposal's named missing intermediate is
exactly the normalized-Laplacian variational instance.

**Changes (planned):** `GraphTheory/Spectral.lean` (generic
`secondEval_variational` + generic orthogonality twin;
`lambda2_variational` becomes a corollary at unchanged shape),
`GraphTheory/Cheeger.lean` (axiom → theorem at identical
name/hypotheses), QA extension, then scoreboard/index/proposal updates.

## 2026-08-18T17:32:07Z — cheeger_upper_bound retired: easy direction proved

**Run:** `20260818T170101Z-run-1`
**Session:** `ses_fea3405d0ffeBFONeKeIHb6OtE`
**Status:** completed
**Milestone:** The Cheeger easy direction (`λ₂(L_sym) ≤ 2φ`, repo name
`cheeger_upper_bound`) proved and retired from axiom (17 → 16) — the
top High item in `proposals/README.md`, executed per
`prove-cheeger-easy-direction.md`.

**Changes:** `GraphTheory.Spectral`: the `lambda2_variational`
Courant–Fischer argument generalized to any symmetric PSD matrix with
`onesVec` in its kernel (`secondEval_variational`; generic
`eigvecOf_ortho_onesVec_of_mulVec_eq_zero`; `lambda2_variational`
re-proved as a corollary at unchanged shape; new consumer form
`secondEval_le_rayleigh`). `GraphTheory.Cheeger`: regularity scaling
bridges (`d • L_sym = laplacian A`, PSD transfer, row-sum kernel,
vol = d·card), the volume-centered `cutTestVector` interface
(orthogonality; the regularity-free cut energy identity
`xᵀLx = boundary · (vol V)²`; norm and Rayleigh values), and
`cheeger_upper_bound` as a theorem at the axiom's exact
name/hypotheses. QA `Cheeger_QA.lean` +7 (378 total; imports
`Exhaustive_QA` for the `C₄` tables): test vector pinned to `![1,-1]`
on `K₂`, Rayleigh value computed to `2` (= the pinned `λ₂(L_sym)`:
bound attained), theorem instantiated on `K₂` (`λ₂ = 2φ`) and on `C₄`
(`λ₂ ≤ 1` at conductance `1/2`). Docs: scoreboard (16/378/0 + note),
radar (axis 4 re-scored 2.5 → 3.0 per protocol; trend
26 → 19 → 18 → 17 → 16), Cheeger indexes, backlog item 3, README
snapshot, proposal moved to Delivered with named residuals (irregular
generalization needs the congruence-transfer route after all; the two
supporting moves stay live).

**Verification:** `lake env lean` on `Spectral`, `Cheeger`, and
`Cheeger_QA` — zero errors (only pre-existing linter notes in
untouched code); `lake build Scaffold.Mathlib.GraphTheory.Spectral`
and `Scaffold.Mathlib.GraphTheory.Cheeger` ✔; full `lake build` ✔
(2178 targets); all 24 QA modules elaborated directly in one batch
(zero failures); `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated. No `sorry`/`admit`
under `Scaffold/` (textual matches are prose).

**Remaining risk:** the hard direction (`cheeger_lower_bound`,
`φ²/2 ≤ λ₂`) remains admitted — the retirement is the easy direction
only, and QA consequences of the lower bound stay conditional on it.
The irregular-graph Cheeger statement remains future work (named
residual: the generalized engine's constraint set is `x ⊥ onesVec`,
not `x ⊥ √deg`).

**Next handoff:** Fiedler Phase A (A1/A2) — the remaining High item in
`proposals/README.md`, scoped as close to free, now composable with
the proved easy direction; or the named residuals; or the
`evals (c • M)` Mathlib-excavation candidate.

## 2026-08-18T18:14:05Z — Audit and finish the uncommitted normalized-Cheeger milestone

**Run:** `20260818T181405Z-run-1`
**Session:** `ses_fe9ed19c5ffedEJXC38yttHzNl`
**Status:** in-progress
**Milestone:** Operator direction (`scripts/finish-cheeger-milestone`):
audit and finish the current uncommitted Cheeger work only — the
`cheeger_upper_bound` retirement on the normalized Laplacian, whose
hard-direction twin `cheeger_lower_bound` correctly remains the sole
admitted Cheeger axiom — preserving unrelated working-tree changes, no
new proposal, no commit. Planned changes: strip the 6
trailing-whitespace metadata lines this milestone's own two newest
entries introduced into this log, then re-verify directly (changed
public modules + Cheeger QA elaboration and target builds, hygiene
scripts, scoreboard drift check, full `lake build`) and record the
outcome.

## 2026-08-18T18:16:54Z — Normalized-Cheeger milestone audited and finished

**Run:** `20260818T181405Z-run-1`
**Session:** `ses_fe9ed19c5ffedEJXC38yttHzNl`
**Status:** completed
**Milestone:** The uncommitted normalized-Cheeger milestone (the
`cheeger_upper_bound` retirement; `cheeger_lower_bound` correctly
remains the sole admitted Cheeger axiom) audited and finished per
operator direction — no new mathematics, no new proposal, no commit.

**Changes:** `docs/AGENT_ACTIVITY.md` only, in two kinds: (a) stripped
the 6 trailing-whitespace metadata lines this milestone's own two
newest entries (17:01/17:32Z) had introduced — the recent-convention
region of the log is now whitespace-free end to end, while older
committed entries and the template's illustrative hard breaks were
left untouched as unrelated records; (b) this run's own entries.
`docs/EXECUTION_PLAN.md` records the audit and its outcome. No Lean,
index, scoreboard, README, or proposal files changed — the audit found
them already consistent.

**Verification:** audit — the uncommitted Lean changes, scoreboard
(16/378/0), README snapshot, radar, indexes, and the proposal's
Delivered row are mutually consistent, and the recorded claims were
re-derived: direct elaboration (`lake env lean`) of
`GraphTheory.Spectral`, `GraphTheory.Cheeger`, and
`QA.SpectralGraph.Cheeger_QA` with zero errors (Cheeger QA zero
warnings; the remaining linter notes were checked to sit in
declarations present unchanged in HEAD, outside the diff hunks);
explicit `lake build` of those three targets ✔; `lint_axioms` (16
axioms covered), `check_citations`, `check_markdown_links` all pass;
scoreboard regeneration byte-identical to the recorded file (no
drift); `grep` confirms the 16 `axiom` declarations and that
`sorry`/`admit` textual matches are prose only; full `lake build` ✔
(2178 targets). Unrelated working-tree changes (`.opencode/`,
`AGENTS.md`, `scripts/opencode-pursue`, `scripts/README.md`,
`scripts/test_opencode_pursue.sh`, `scripts/finish-cheeger-milestone`,
`proposals/sell-the-methodology.md`,
`proposals/retire-the-mushy-center.md`, untracked
`proposals/README.md`) preserved untouched; nothing committed.

**Remaining risk:** none new — no source changed. The standing risk is
unchanged: the hard direction (`cheeger_lower_bound`, `φ²/2 ≤ λ₂`)
remains admitted; QA consequences resting on it stay conditional.

**Next handoff:** Fiedler Phase A (A1/A2) — the remaining High item in
`proposals/README.md`; or the named residuals (irregular Cheeger via
congruence transfer, the electrical definiteness residual); or the
`evals (c • M)` Mathlib excavation.

## 2026-08-18T18:26:12Z — Fiedler Phase A: vector and sign partition

**Run:** `20260818T182612Z-run-1`
**Session:** `ses_fe9e0c143ffexTpz2rHUkp92Bm`
**Status:** in-progress
**Milestone:** Deliver `fiedler-partitioning.md` Phase A (A1/A2) — the
remaining High item in `proposals/README.md` and the plan's open next
milestone: the Fiedler-vector interface (existence + the induced
sign-pattern partition with nonempty/proper sanity), hard crust, no new
axioms. Leverage: backlog item 4's named first application-ring
candidate, and a load-bearing consumer of the electrical program's
kernel characterization.
- *2026-08-18T18:26:12Z entry continues (Fiedler Phase A).* Status
  update: **completed** as of 2026-08-18T19:07:28Z (same run, same
  session).

**Changes:** new `Scaffold/Mathlib/GraphTheory/Fiedler.lean` (18
declarations, all proved, no new axioms — axiom count stays 16):
`fiedlerIndex`/`fiedlerIndex_eigvalOf` (the eigenbasis index carrying
`lambda2`, fixed by classical choice — the proposal's build-order
sketch indexed `eigvecOf` by a sorted-spectrum position, which is not
that function's type; deviation recorded in the module docstring),
`fiedlerVector` with the eigenvector equation `fiedlerVector_eigen`,
unit norm, nonvanishing, `fiedlerVector_quadForm`,
`fiedlerVector_ortho_onesVec`/`_sum_eq_zero`; the algebraic-connectivity
certificate `lambda2_pos_of_connected` (connected ⇒ `0 < lambda2`,
consuming `laplacian_kernel_eq_span_onesVec`, PSD, and both
multiplicity pins — load-bearing on all three); and `fiedlerPartition`
with sanity facts at interface strength (`_nonempty_of_pos`,
`_ne_univ_of_pos`, through the zero-sum identity) and connectivity
corollaries. New QA `Scaffold/QA/SpectralGraph/Fiedler_QA.lean` (57
declarations): `K₂` partition pinned to a singleton half; the `P₄`
barbell (two `K₂` near-cliques joined by a bridge) with `lambda2 ≤ 1`
via the proved Rayleigh engine, `lambda2 ≠ 1` via the eigen equations,
and the partition *derived* to be exactly the known good cut `{0,1}`
(or complement): boundary `1`, volume `3`, conductance `1/3`; the
disconnected negative witness (`lambda2 = 0`; `onesVec` a nonzero
eigenvector there whose sign filter is `univ` — hypothesis
load-bearing). Records updated: umbrella, scoreboard (435/16/0),
radar (subject axis 4 re-scored 3.0 → 3.5 per the proposal's protocol;
QA count 435/25), SGT index map, backlog item 4, README snapshot cell,
proposal delivery record, `proposals/README.md` (Fiedler → Medium).

**Verification:** `lake env lean` on `GraphTheory.Fiedler` and
`QA.SpectralGraph.Fiedler_QA` — zero errors, zero warnings (build
diagnostics filtered to the two new files: none; the remaining build
notes are the documented pre-existing linter notes in untouched
modules, verified present unchanged in HEAD); `lake build` of both
targets ✔; full `lake build` ✔ (2179 targets); all twenty-five QA
modules elaborated directly in one batch (zero failures); 435 QA
declarations, no `sorry`/`admit` anywhere under `Scaffold/` (textual
matches are prose); 16 explicit cited axioms (unchanged); `lint_axioms`,
`check_citations`, `check_markdown_links` all pass; scoreboard
regenerated (435/16/0).

**Remaining risk:** Phase A is existence and sanity, not quality — the
Fiedler partition exists and is a genuine bipartition on connected
graphs, but no conductance guarantee is claimed (Phase B, deliberately
not started; it would be axiom-backed on the still-admitted Cheeger
hard direction). The `fiedlerIndex` choice is classical, so
`fiedlerVector` is fixed only up to the eigenbasis; every theorem is
choice-independent (stated through `fiedlerIndex_eigvalOf`-style
interfaces). Phase B needs the operator decision the proposal names.

**Next handoff:** the new High item
(`proposals/repair-and-retire-woodbury.md`, appeared mid-run from the
operator; preserved untouched) — the admitted Woodbury axiom is
verified false and Mathlib carries the correct proof, so this is a
correctness repair with axiom-count reduction. Then Fiedler Phase B
(Medium, decision-gated), the electrical definiteness residual, or the
`evals (c • M)` excavation.

## 2026-08-18T19:19:06Z — Fiedler Phase A milestone audit and finish

**Run:** `20260818T191906Z-run-1`
**Session:** `ses_fe9b0cceeffev1a5nLrF4bDxcy`
**Status:** in-progress
**Milestone:** Finish the uncommitted Fiedler Phase A milestone only
(operator direction): audit the delivered `GraphTheory.Fiedler` and
`Fiedler_QA.lean` changes, verify them proportionately (direct module
builds, hygiene suite, scoreboard drift check, full `lake build`),
update only the corresponding records, and close the milestone — no
new mathematics, no new proposal, no commit. Unrelated work (the
untracked Woodbury proposal, `scripts/next-steps`, and all other
working-tree changes) preserved untouched.

## 2026-08-18T19:22:00Z — Fiedler Phase A milestone audit and finish

**Run:** `20260818T191906Z-run-1`
**Session:** `ses_fe9b0cceeffev1a5nLrF4bDxcy`
**Status:** completed
**Milestone:** The uncommitted Fiedler Phase A milestone (the new
`GraphTheory.Fiedler` module, `Fiedler_QA.lean`, and their record
updates) audited, verified, and closed per operator direction — no new
mathematics, no new proposal, no commit.

**Changes:** `docs/7_SGT_RADAR.md` only, one cell: the subject-axis-4
score, stale at `3.0`, synced to `3.5` — the value every other record
of the re-score already carried (the radar's own trailing prose, the
README snapshot, the execution plan, the proposal delivery record, the
activity log). Plus this run's own entries in
`docs/AGENT_ACTIVITY.md` and `docs/EXECUTION_PLAN.md`. No Lean, index,
scoreboard, README, or proposal content changed — the audit found them
already mutually consistent (57 Fiedler QA declarations, 16 explicit
axioms, 25 QA modules, re-derived from source).

**Verification:** `lake env lean` on `GraphTheory.Fiedler` and on
`QA.SpectralGraph.Fiedler_QA` — zero errors, zero warnings; `lake
build` of both targets ✔; full `lake build` ✔ ("Build completed
successfully" — the 22 Scaffold-side linter notes are the documented
pre-existing ones in untouched committed modules, none in the two new
Fiedler files; the ~2980 further notes are Mathlib-package `docPrime`
warnings over recompiled Mathlib residue, the recorded pruned-cache
environment debt, not Scaffold code); scoreboard regeneration
byte-identical (435/16/0 re-derived, no drift); `lint_axioms` (16
covered), `check_citations`, `check_markdown_links` all pass.
Unrelated working-tree changes (untracked
`proposals/repair-and-retire-woodbury.md`, `scripts/next-steps`, and
all pre-existing modifications) preserved untouched; nothing
committed.

**Remaining risk:** none new — one stale documentation cell repaired,
no source changed. The standing risks are unchanged: the Cheeger hard
direction (`cheeger_lower_bound`) remains admitted (Phase B of the
Fiedler proposal would rest its lower-bound half on it), and the
Fiedler vector is fixed only up to the classical eigenbasis/index
choice (every theorem is stated through choice-independent
interfaces).

**Next handoff:** the High item — repair and retire the Woodbury
identity axiom (`repair-and-retire-woodbury.md`: the admitted axiom is
verified false; Mathlib's `Matrix.invOf_add_mul_mul` carries the
correct proof). Then Fiedler Phase B (Medium, decision-gated), the
electrical definiteness residual, or the `evals (c • M)` excavation.

## 2026-08-18T19:30:04Z — Repair and retire the false Woodbury identity axiom

**Run:** `20260818T193004Z-run-1`
**Session:** `ses_fe9a84ffbffef90p4oMoglfP5k`
**Status:** in-progress
**Milestone:** Execute the High priority item
(`proposals/repair-and-retire-woodbury.md`): the admitted
`woodbury_identity` axiom is verified false (scalar counterexample
`A=1, U=V=1, C=0`), so repair its statement shape to the standard
middle factor `C⁻¹ + V A⁻¹ U` with the three explicit `IsUnit …det`
hypotheses, then prove it from Mathlib's `Matrix.invOf_add_mul_mul`
plus the `NonsingularInverse` bridges — an emergency trust-base repair
per architecture §9, retiring an axiom (16 → 15). QA: refutation of the
old scalar shape without consuming the axiom, plus positive scalar and
non-scalar instances. Correctness repair outranks consumers here: a
false axiom is dangerous precisely while still unconsumed
(`GraphTheory/Dynamics.lean` names it as its intended future consumer).

## 2026-08-18T19:50:11Z — Woodbury identity repaired and retired (axiom 16 → 15)

**Run:** `20260818T193004Z-run-1`
**Session:** `ses_fe9a84ffbffef90p4oMoglfP5k`
**Status:** completed
**Milestone:** The High priority item delivered: the verified-false
admitted `woodbury_identity` retired to a proved theorem at the same
name (explicit axioms 16 → 15), an emergency correctness repair per
architecture §9, with the false old shape refuted in QA and the
corrected theorem proved from Mathlib.

**Changes:** `Scaffold/Mathlib/Core/MatrixUpdates.lean` — the axiom is
now a theorem with the standard middle factor `(C⁻¹ + V * A⁻¹ * U)⁻¹`
and exactly the three hypotheses `IsUnit A.det`, `IsUnit C.det`,
`IsUnit (C⁻¹ + V * A⁻¹ * U).det`; the old `IsUnit (A + U C V).det`
hypothesis was dropped as *derivable* (Mathlib's
`Matrix.invertibleAddMulMul` constructs the sum's `Invertible`
instance — a strengthening beyond the proposal's three-hypothesis
sketch). Proof is pure upstream reuse: `Matrix.invOf_add_mul_mul` plus
`Matrix.invertibleOfIsUnitDet`/`Matrix.invOf_eq_nonsing_inv`, no new
imports needed. Module and theorem docstrings carry the repair record;
`sherman_morrison` untouched (out of scope by the proposal). New QA
file `Scaffold/QA/Core/MatrixUpdates_QA.lean` (8 declarations, the
first Core-domain QA): `old_woodbury_identity_refuted_QA` negates the
retired axiom's own statement at `Fin 1`/`ℚ` and refutes it *without
consuming any axiom*; `old_woodbury_middle_hyp_holds_QA` /
`old_woodbury_sum_hyp_holds_QA` prove the retired hypotheses *held* at
the counterexample (the refutation is of a genuinely applicable
statement); `corrected_C_hyp_excludes_counterexample_QA` proves the new
`IsUnit C.det` hypothesis excludes it; positive instances at scalars
(`1/5` both sides, right side pinned by consuming the theorem) and at
the non-scalar rank-one update `diag 2 2` + all-ones (both sides
`!![3/8,-1/8;-1/8,3/8]`, middle `(1+1)⁻¹ = 1/2` computed). Records:
both indexes, scoreboard (15/443/0, milestone bullet, verification
rows), radar (axiom-minimization re-scored 4.0 → 4.5 per protocol —
the first retirement motivated by verified falsity; QA 443/26;
proved-depth text), README (15 axioms, 443 QA), the proposal's delivery
record, and `proposals/README.md` (item → Delivered).

**Verification:** `lake env lean` on `Core.MatrixUpdates` and
`QA.Core.MatrixUpdates_QA` — zero errors, zero warnings (the Woodbury
theorem elaborated clean on the first pass; the QA file needed three
iterations — a stale-olean artifact, `Ring.inverse` blocking kernel
`decide` evaluation of `Matrix.inv`, and bare `Fin 2` literals
defaulting to `ℕ`, all resolved: 1×1 inverses via
`Matrix.inv_eq_left_inv` cancellation, 2×2 via the adjugate formula,
literal noise eliminated by fixture definitions); `lake build
Scaffold.Mathlib.Core.MatrixUpdates` ✔; full `lake build` ✔ (2179
targets); all twenty-six QA modules elaborated directly in one batch
(zero errors; only the documented pre-existing `unusedSectionVars`
notes in untouched modules); 443 QA declarations, no `sorry`/`admit`
under `Scaffold/` (textual matches are prose); 15 explicit axioms
(−1); `lint_axioms` (15 covered), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated from source
(15/443/0).

**Remaining risk:** none from the retired axiom — the false statement
is deleted, not deprecated, and had zero consumers (a compatibility
alias would have to restate a falsehood). `sherman_morrison` remains
admitted: the proposal's own text and the priority table note it is
correctly shaped per its statement, but it has not had the full
fidelity review the Woodbury one got before its falsity was found; the
`retire-sherman-morrison.md` proposal (now unblocked) covers it.

**Next handoff:** the operator's new High item
(`proposals/prove-courant-fischer.md`, with four named downstream
consumers), or the Sherman–Morrison retirement (Medium, the cheapest
remaining retirement, QA scaffolding now in place). Fiedler Phase B
stays Medium and decision-gated; the electrical definiteness residual
and the `evals (c • M)` excavation remain open. Concurrent
working-tree changes preserved untouched (the operator's
`proposals/{prove-courant-fischer,retire-sherman-morrison,admit-perron-frobenius}.md`
additions and the `scripts/next-steps` deletion).

## 2026-08-18T21:03:46Z — General Courant–Fischer min–max (proof)

**Run:** `20260818T210346Z-run-1`
**Session:** `ses_fe9562e17ffe4hhby1PpujPSnj`
**Status:** in-progress
**Milestone:** Prove the general Courant–Fischer min–max theorem for the
sorted spectrum of any real symmetric matrix (the High item in
`proposals/README.md`, `proposals/prove-courant-fischer.md`), generalizing
the fixed-k=2 `secondEval_variational` engine to every index. Pure hard
crust — no axiom is retired (general min–max was never admitted), axiom
count stays 15 — but it is the proof substrate the proposal names for four
downstream consumers (interlacing retirement, Rayleigh monotonicity, the
Cheeger hard direction, Fiedler Phase B).

**Plan (recorded before editing):** the proposal's open next step — survey
the pin for the dimension-intersection lemma — is resolved affirmatively
this run: `Submodule.finrank_sup_add_finrank_inf_eq`,
`Finset.exists_smaller_set`, `finrank_span_eq_card` (Fintype-family form),
`Fintype.linearIndependent_iff`, `Module.finrank_pi`, and
`Submodule.ne_bot_iff` are all present in the v4.14.0 pin. Route: two
witness-form theorems (existence of an optimal `(k+1)`-dimensional
subspace; every `(k+1)`-dimensional competitor contains a test vector with
Rayleigh quotient ≥ `evals k`), proved through the existing eigenbasis
algebra (`quadForm_eigvalOf`, `dotProduct_eigvecOf`,
`eigvecOf_inner`), plus the packaged `sInf` equality. New general-k
multiplicity pins (index-filter cardinalities vs `k`) as public center
API. QA: computable fixture `!![2,1;1,2]` (spectrum `[1,3]` pinned by
trace/determinant/sortedness, mirroring `edge_normLap_secondEval_eq_two_QA`),
both directions instantiated, attainment and non-attainment negative
witnesses (wrong subspace refuted; dimension hypothesis witnessed
load-bearing), and a `Fin 3` path-Laplacian instantiation.

## 2026-08-18T21:52:24Z — General Courant–Fischer min–max proved

**Run:** `20260818T210346Z-run-1`
**Session:** `ses_fe9562e17ffe4hhby1PpujPSnj`
**Status:** completed
**Milestone:** The High item `proposals/prove-courant-fischer.md` delivered:
the `k`-th sorted eigenvalue of any real symmetric matrix characterized at
every index — pure hard crust, axiom count unchanged at 15 (general
min–max was never admitted), so this is load-bearing proof growth rather
than trust-surface reduction; it is the named proof substrate for four
follow-ons (interlacing retirement, Rayleigh monotonicity, the Cheeger
hard direction, Fiedler Phase B), none claimed here.

**Changes:** `GraphTheory.Spectral` gained a `CourantFischer` section
(~450 lines): public center API — general-`k` multiplicity pins
(`card_filter_eigvalOf_lt_evals_le`, `succ_le_card_filter_eigvalOf_le`),
orthonormal-family tools (`eigvecOf_dotProduct`,
`linearIndependent_eigvecOf_finset`, `finrank_span_eigvecOf_finset`),
component-form Rayleigh bounds
(`rayleigh_le_evals_of_forall_dotProduct_eq_zero`,
`evals_le_rayleigh_of_forall_dotProduct_eq_zero`), and span-orthogonality
(`dotProduct_eigvecOf_eq_zero_of_mem_span`); plus the three headline
forms — `exists_submodule_forall_rayleigh_le`,
`exists_ne_mem_rayleigh_ge_of_finrank_eq`, `evals_min_max` —
symmetry-only, reusing the proved eigenbasis algebra plus the pin's
`Submodule.finrank_sup_add_finrank_inf_eq` (the proposal's open survey
step, resolved affirmatively before committing). New QA file
`SpectralGraph/CourantFischer_QA.lean` (33 declarations): spectrum `[1,3]`
pinned from trace/determinant/sortedness on `!![2,1;1,2]`; both
directions instantiated, including the derived top-eigenvalue-domination
universal (existence direction + `eq_top_of_finrank_eq`) and exact
attainment of `evals 1` through both directions; negative witnesses —
wrong line refuted (`3 ≤ 1`), dimension hypothesis load-bearing
(conclusion false on a one-dimensional subspace at index `1`), interior
index `k = 1 < n−1` exercised on the path Laplacian (wrong
two-dimensional subspace refuted at `4/3`; cross-check against the older
`secondEval_le_rayleigh` engine). Records: scoreboard (15/476/0,
milestone bullet), radar (subject axis 3 re-scored 3.5 → 4.0 per
protocol; QA count 476/27; proved-depth text), README (axis cell, counts,
maturity), SGT index map, proposal delivery record,
`proposals/README.md` (High item → Delivered; no High remains).

**Verification:** `lake env lean` on `GraphTheory.Spectral` (zero errors;
no new warnings after silencing the one new-code section-variable note
with `omit`) and on `QA.SpectralGraph.CourantFischer_QA` (zero errors,
zero warnings); targeted `lake build` of both targets ✔; full
`lake build` ✔ (2179 targets); all twenty-seven QA modules elaborated
directly in one batch (zero failures); 476 QA declarations (+33), no
`sorry`/`admit` anywhere under `Scaffold/` (textual matches are prose);
15 explicit cited axioms (unchanged); `lint_axioms`, `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (15/476/0) and
re-checked idempotent after the manual prose edits.

**Remaining risk:** none identified in the delivered proof — it is
kernel-checked with no new axioms or admissions, and the QA falsifies
nearby wrong statements rather than merely instantiating the theorem.
The four named consumers are open follow-ons needing their own scoping
(the proposal explicitly forbids claiming them); the packaged
`evals_min_max` expresses the within-subspace maximum as the infimum of
dominating values, an honest but non-standard packaging documented in
its docstring.

**Next handoff:** no High item remains in `proposals/README.md`.
Candidates for the next run: the Sherman–Morrison retirement (Medium,
cheapest remaining); the interlacing retirement through the new min–max
theorem (its first named consumer); full Rayleigh/Dirichlet monotonicity;
Fiedler Phase B (Medium, decision-gated). Unrelated working-tree changes
(the operator's `scripts/opencode-pursue` and
`scripts/test_opencode_pursue.sh` modifications) preserved untouched;
nothing committed.

## 2026-08-18T22:33:14Z — Sherman–Morrison axiom retirement (proof)

**Run:** `20260818T223314Z-run-1`
**Session:** `ses_fe900e85affegpNCBrauKLr1L5`
**Status:** in-progress
**Milestone:** Retire the `sherman_morrison` axiom (the Medium item
`proposals/retire-sherman-morrison.md`, named the cheapest remaining axiom
retirement and unblocked by the Woodbury repair) by specializing the proved
`woodbury_identity` at `k = Fin 1`, at the axiom's current name and
hypotheses — explicit axiom count 15 → 14, pure trust-surface reduction.
Per the proposal's verified finding, this is a proof task, not a
correctness repair: the statement was already checked correct against the
corrected Woodbury shape.

**Plan (recorded before editing):** Mathlib survey done — the pin has
`Matrix.mul_smul`/`Matrix.smul_mul`, `Matrix.det_fin_one`,
`Matrix.inv_eq_left_inv` (`B * A = 1 → A⁻¹ = B`), `Matrix.dotProduct`;
`Matrix.inv_one` does not exist (derived instead). Route: rank-one
packing `u`/`v` into `Fin 1` column/row matrices, 1×1 middle factor with
entry `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)` (`Fin.sum_univ_one` computation), unit
determinant from `hv`, scalar-inverse 1×1 inverse, matrix-level
`mul_smul`/`smul_mul` reshaping to the entrywise statement. QA: positive
instance at the existing `A2 = diag 2 2` rank-one fixture (value
computed independently via the adjugate), negative witness at the
excluded denominator (`v ⬝ᵥ (A⁻¹ *ᵥ u) = -1`, where the update is
singular). Records to follow: module docstring, both indexes, scoreboard,
radar, README, `proposals/README.md`, proposal delivery record. The
operator's concurrent changes (`.gitignore`, clean-room proposals,
`cdx-clean-assess.md`, mushy-center priority row) preserved untouched.

## 2026-08-18T22:44:25Z — Sherman–Morrison axiom retired (proved)

**Run:** `20260818T223314Z-run-1`
**Session:** `ses_fe900e85affegpNCBrauKLr1L5`
**Status:** completed
**Milestone:** `proposals/retire-sherman-morrison.md` delivered — the
`sherman_morrison` axiom retired to a proved theorem at unchanged name,
hypotheses, and statement (explicit axiom count 15 → 14), as the
`k = Fin 1` specialization of the proved `woodbury_identity`. Pure
trust-surface reduction; per the proposal's verified pre-check, a proof
task, not a correctness repair.

**Changes:** `Core.MatrixUpdates` — the axiom replaced by a theorem
proved from the repository's own Woodbury theorem: `Fin 1` column/row
packing (`U * V` equals the entrywise outer product, a
`Fin.sum_univ_one` computation as calibrated), the 1×1 middle factor
identified with the scalar denominator `1 + v ⬝ᵥ (A⁻¹ *ᵥ u)` (via
`Matrix.dotProduct_mulVec`), its unit determinant from `hv` through
`Matrix.det_fin_one`, its inverse as the 1×1 scalar inverse
(`Matrix.inv_eq_left_inv`; `Matrix.inv_one` absent from the pin,
derived instead), and the shape matched by `Matrix.mul_smul` /
`Matrix.smul_mul` algebra. The specialization is load-bearing on the
Woodbury repair. QA `Core/MatrixUpdates_QA.lean` +4 (480 total):
adjugate-independent positive instance at `diag 2 2` + all-ones
(`!![3/8,-1/8;-1/8,3/8]`, denominator computed to `1`), and the
excluded-denominator negative witness (`v ⬝ᵥ (A⁻¹ *ᵥ u) = -1` attained
at a `Fin 1` fixture where the update is the singular zero matrix).
Docs: module docstring, both indexes, scoreboard (14/480/0 + milestone
bullet + verification rows), radar (trend extended to 26 → … → 14; QA
count 480/27), README (14/480), `proposals/README.md` (→ Delivered),
proposal delivery record.

**Verification:** `lake env lean` on both changed modules — zero
errors, zero warnings; targeted `lake build` of both targets ✔ (the QA
file is the module's only direct consumer, verified by import search);
full `lake build` ✔ (2179 targets); 480 QA declarations, no
`sorry`/`admit` anywhere under `Scaffold/`; `lint_axioms` (14 covered)
and `check_citations` pass; `check_markdown_links` reports only the
operator's untracked `cdx-clean-assess.md` links (pre-existing at run
start, outside this milestone); scoreboard regeneration idempotent
after the prose edits.

**Remaining risk:** none identified — the retired statement is
unchanged (it was verified correct before the proof), the theorem is
kernel-checked with no new axioms, and zero consumers existed to
migrate. The singular-witness QA pins that the excluded denominator is
exactly where the update loses invertibility.

**Next handoff:** no High item remains in `proposals/README.md`.
Candidates: Fiedler Phase B (Medium, needs its named operator
decision), the mixing-time program (Medium), the min–max theorem's
named consumers as separately scoped runs (interlacing retirement;
Rayleigh/Dirichlet monotonicity), the electrical definiteness residual,
or the `evals (c • M)` excavation. Unrelated working-tree changes (the
operator's `.gitignore`, clean-room proposal files,
`cdx-clean-assess.md`, and the mushy-center priority row) preserved
untouched; nothing committed.

## 2026-08-18T23:05:12Z — Cauchy interlacing axiom retirement (proof)

**Run:** `20260818T230335Z-run-1`
**Session:** `ses_fe8e869ffffekg9H8jzuweYEGJ`
**Status:** in-progress
**Milestone:** Retire the `eigen_interlacing_principal_submatrix` axiom
(the min–max theorem's first named consumer; explicit axiom count target
14 → 13) by proving Cauchy interlacing from the proved Courant–Fischer
engine. Pure trust-surface reduction and load-bearing growth: the proof
consumes both CF witness directions, so a defect in the new engine would
surface here rather than pass beside it. Pre-check: the admitted
statement is the textbook true window — a proof task, not a repair.

**Plan (recorded before editing):** padding bridge (extend-by-zero,
Rayleigh-preserving), lower bound via CF existence on the submatrix +
competitor on the ambient, upper bound via CF existence on the ambient
at `i + d` + the dimension-intersection count (the same
`finrank_sup_add_finrank_inf_eq` pattern CF used) + basis extraction for
the exact competitor dimension. QA: numeric instantiation at `K₂` with a
singleton submatrix (strict window, both naive one-sided bounds
refuted). Records to follow: module docstring, both index rows,
scoreboard, radar, README, coverage map, Courant–Fischer proposal note,
`proposals/README.md`.

## 2026-08-18T23:43:10Z — Cauchy interlacing axiom retired (proved from Courant–Fischer)

**Run:** `20260818T230335Z-run-1`
**Session:** `ses_fe8e869ffffekg9H8jzuweYEGJ`
**Status:** completed
**Milestone:** `eigen_interlacing_principal_submatrix` retired from
axiom to proved theorem at unchanged name/hypotheses/statement —
explicit axiom count **14 → 13**. A pure proof task per the recorded
pre-check (the admitted statement was the true textbook window
`λᵢ ≤ μᵢ ≤ λᵢ₊ₙ₋ₘ`), and the Courant–Fischer min–max engine's first
named consumer: the proof consumes both witness directions, so a defect
in the new engine would surface here (load-bearing growth).

**Changes:** `GraphTheory.Spectral` — the axiom replaced by a theorem
proved through a new extend-by-zero padding bridge (`padVec`/
`padVecLinear` with `dotProduct_padVec_self`, `quadForm_padVec`,
`rayleigh_padVec` — Rayleigh preservation needs no symmetry) plus
subspace bookkeeping (`finrank_map_eq_of_injective`,
`finrank_comap_eq_of_le_range`, `exists_submodule_finrank_eq_of_le`).
Lower bound: CF-existence on the submatrix, image under padding,
CF-competitor on the ambient. Upper bound: CF-existence on the ambient
at `i + d`, the dimension count `finrank (U ⊓ range pad) ≥ i + 1` (the
proposal's warned subspace-intersection step, via the same
`Submodule.finrank_sup_add_finrank_inf_eq` the min–max proof used),
exact-dimension extraction, comap transfer, back through
`rayleigh_padVec`. One new import (`Mathlib.Algebra.Module.Submodule.Range`).
The module now carries zero `axiom` declarations. QA
`SpectralGraph/Interlacing_QA.lean` (+4 public, 484 total): `K₂`
spectrum `[0,2]` and singleton-submatrix spectrum `[1]` pinned from
trace/determinant/sortedness independent of the theorem; window
instantiated to the strict `0 ≤ 1 ≤ 2`; both collapsed one-sided bounds
refuted in proved form — superseding the axiom-era "no thin QA exists"
note (the machinery did not exist then). Docs: module docstring and
section header, scoreboard (13/484/0 + milestone bullet + verification
rows), radar (axis-2 interlacing proved; axiom-minimization trend → 13;
QA 484/27; proved-depth and reuse text), README (13 axioms, 484 QA),
Horn–Johnson source index and SGT index map, coverage map,
Courant–Fischer proposal delivery note, `proposals/README.md`.

**Verification:** `lake env lean` on both changed modules — zero errors
(new-code section-variable notes silenced with `omit`; remaining notes
are the documented pre-existing ones); targeted `lake build` of both
targets ✔; full `lake build` ✔ (2179 targets); 484 QA declarations, no
`sorry`/`admit` anywhere under `Scaffold/`; 13 explicit cited axioms;
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated and idempotent after the prose edits.

**Remaining risk:** none identified — the retired statement is
unchanged (verified true before the proof), kernel-checked with no new
axioms, and zero consumers existed to migrate. The 1×1/2×2 QA fixtures
pin the window only at small sizes; the interlacing statement's index
arithmetic (`hn`) is exercised at the singleton instance.

**Next handoff:** the operator's new High item
(`proposals/electrical-flow-routing.md`, indexed mid-run — electrical
flows, Thomson's principle, Rayleigh monotonicity; step 0 is its
representation/Mathlib survey) is the next run's milestone per the
operator's own note. Alternatives: mixing-time step 1 (Medium),
Rayleigh/Dirichlet monotonicity (cheaper now through the padding
bridge), Fiedler Phase B (decision-gated). The operator's concurrent
`proposals/electrical-flow-routing.md` and its priority row preserved
untouched; nothing committed.

## 2026-08-19T00:30:01Z — Electrical-flow routing, step 0 (representation survey) + step 1 (Kirchhoff conservation)

**Run:** `20260819T003001Z-run-1`  
**Session:** `ses_fe897785cffejcLqL4bSCUd1j6`  
**Status:** in-progress  
**Milestone:** Open the High item `proposals/electrical-flow-routing.md`: run its step 0 (pin and record the flow representation against a fresh Mathlib survey) and then its step 1 — the smallest independently useful Lean slice (electrical current, divergence, flow predicates, the Kirchhoff bridge from unit-demand potentials to unit flows). Zero new axioms; turns the delivered potential-based resistance API into a routing object. Steps 2–5 are not started this run.

## 2026-08-19T00:41:19Z — Electrical-flow routing steps 0–1 delivered (representation + Kirchhoff conservation)

**Run:** `20260819T003001Z-run-1`  
**Session:** `ses_fe897785cffejcLqL4bSCUd1j6`  
**Status:** completed  
**Milestone:** Open the Active table's High item `proposals/electrical-flow-routing.md`: step 0 (representation survey/decision, recorded before any Lean) and step 1 (the flow interface and Kirchhoff bridge — the resistance API becomes a routing object). Zero new axioms (13 unchanged); steps 2–5 not started.

**Changes:** step 0 recorded in the proposal first — fresh pin survey found no flow/circulation/max-flow API, no graph-native divergence (only continuum divergence theorems), nothing electrical, and no usable oriented-edge API (`SimpleGraph.Dart` is counting machinery), so the matrix representation `EdgeFlow V = Matrix V V ℝ` was pinned with conductance orientation, the zero-conductance support as an explicit `IsFlowOn` conjunct, and the `1/2` ordered-pair factor reserved for step-2 `flowEnergy`; target module the new focused `GraphTheory.ElectricalFlow` (coverage map's electrical row re-surveyed, same absence verdict). Step 1: `electricalCurrent`, `flowDivergence`, `IsFlowOn`, `IsUnitFlow`, `electricalCurrent_antisymm`, `electricalCurrent_eq_zero_of_weight_eq_zero`, the Kirchhoff bridge `flowDivergence_electricalCurrent` (a one-line load-bearing consumer of `laplacian_mulVec_apply`'s exact sign convention), `isFlowOn_electricalCurrent`, and the headline `isUnitFlow_electricalCurrent` (a unit-demand potential induces a valid unit flow). QA `SpectralGraph/ElectricalFlow_QA.lean` (16 declarations): `K₂` and 3-path currents/divergences computed from raw definitions (internal vertex `0`), plus negative witnesses for both proposal-named traps — asymmetric network `!![0,2;1,0]` refutes current antisymmetry (`2 ≠ 1`), and an edgeless-network phantom (antisymmetric, unit divergence) excluded by the support conjunct alone. Umbrella import added; scoreboard (500/13/0), radar (QA 500/28; subject axis 6 evidence extended, score held at 3.0 per protocol and recorded), README, SGT index map, coverage map, proposal, and `proposals/README.md` progress note updated.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors/warnings (three `omit` clauses for unused section variables); `lake build` of both targets ✔; full `lake build` ✔; all 28 QA modules batch-elaborated with zero failures; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration byte-idempotent.

**Remaining risk:** the flow interface is plumbing — its mathematical payoff (Thomson, Rayleigh monotonicity) is steps 3–4 and depends on step 2's `flowEnergy` landing with the `1/2` factor QA-witnessed; the zero-edge trap's energy-level refutation is deferred to step 2 by design (no energy definition exists yet to refute with).

**Next handoff:** proposal step 2 — `flowEnergy` (explicit zero branch, mandatory `1/2` factor), the agreement `flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`, and the double-counting QA fixture; then steps 3–4 as separate runs. Concurrent operator additions preserved untouched: the uncommitted `proposals/README.md` interlacing-row edit and the new untracked `proposals/decidable-spectral-certificates.md` (a High proposal not yet indexed in the priority table — the next run should treat the table, kept current by the operator, as authoritative). Nothing committed.

## 2026-08-19T01:32:28Z — Electrical-flow routing, step 2 (flow energy and the energy agreement)

**Run:** `20260819T013200Z-run-1`  
**Session:** `ses_fe85dc2beffepvHWCJsEF2D4JJ`  
**Status:** in-progress  
**Milestone:** Continue the Active table's top High item `proposals/electrical-flow-routing.md` at its recorded next step — step 2: `flowEnergy` with the explicit zero branch and the mandatory `1/2` ordered-pair factor, the energy agreement `flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`, the unit-demand corollary equating it with `effectiveResistance`, and the QA double-counting/zero-energy-competitor fixtures the proposal mandates. Zero new axioms; steps 3–5 not started this run.

## 2026-08-19T01:46:30Z — Electrical-flow step 2 delivered (flow energy and the energy agreement)

**Run:** `20260819T013200Z-run-1`  
**Session:** `ses_fe85dc2beffepvHWCJsEF2D4JJ`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/electrical-flow-routing.md`, step 2: `flowEnergy` with the explicit zero branch and the mandatory `1/2` ordered-pair factor, the energy agreement with the Dirichlet energy, `flowEnergy_nonneg`, and the unit-demand identity equating the current's dissipated energy with the effective resistance it routes. Zero new axioms (13 unchanged); steps 3–5 not started.

**Changes:** `GraphTheory.ElectricalFlow` gained the step-2 section — `flowEnergy` (ordered-pair sum of squared current over conductance, explicit zero branch, halved for double counting), `flowEnergy_electricalCurrent` (agreement `flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`: termwise `(c x)²/c = c x²` on the nonzero branch, zero-on-zero on the branch, `laplacian_quadForm` at the end — **symmetry-only**, a recorded statement-shape deviation: nonnegativity is not needed for the agreement, and QA witnesses both sides), `flowEnergy_nonneg` (squares over positive conductances — nonnegativity load-bearing, QA exhibits energy `-1` on a symmetric negative-weight network), and `flowEnergy_electricalCurrent_eq_effectiveResistance` (connected graphs: a unit-demand current dissipates exactly the resistance it routes). QA `ElectricalFlow_QA.lean` (+25, 41 in file): energies `1`/`2` computed from the raw definition on `K₂`/`P₃`, each meeting the independently computed Dirichlet energy and pinned resistance value; the **mandatory double-counting fixture** (raw ordered-pair sum `2 ≠ 1` = Dirichlet energy — omitting the `1/2` factor would numerically break the agreement); the step-1 phantom's deferred zero-energy pinning; and the **zero-energy competitor** — an antisymmetric unit-divergence flow routing through zero-conductance pairs on a real-edge-plus-isolated-vertex network, energy `0 < 1` = the real resistance, excluded by `IsFlowOn`'s support conjunct alone (Thomson's step-3 statement would read `1 ≤ 0` over the support-dropped flow class). Fixture note: all-zero-row matrices defined by the repo's entrywise-`if` pattern (matrix notation's zero-function normalization leaves `vecTail` leftovers). Docs: module/QA docstrings, scoreboard (525/13/0 + milestone bullet + verification rows), radar (QA 525/28; subject axis 6 evidence extended, score held at 3.0 per protocol and recorded — an identity, not a new inequality; proved-depth text), README, SGT index map, proposal step-2 delivery record + deviation, `proposals/README.md` progress note.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors/warnings; `lake build` of both targets ✔; full `lake build` ✔ (2180 targets); all 28 QA modules batch-elaborated, zero errors (only the documented pre-existing notes in untouched modules); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (525/13/0).

**Remaining risk:** the energy agreement is plumbing for the variational payoff — Thomson (step 3) and Rayleigh monotonicity (step 4) remain unproved, and the recorded axis hold reflects that; the support conjunct's Thomson-criticality is witnessed at the energy level (the zero-energy competitor) but the inequality itself is not yet stated. The symmetry-only agreement strength is deliberate and QA-pinned; if a later consumer needs the nonnegativity hypothesis present for uniformity, that is a statement-shape decision, not a defect.

**Next handoff:** proposal step 3 — Thomson's principle (`effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow; electrical current as minimizer, `flowEnergy_nonneg` on the divergence-free difference, with the discrete integration-by-parts lemma split out if it deserves a reusable interface); then steps 4–5. Alternatives: Foster Phase A (High; needs its pseudoinverse-free statement-shape spike) or decidable-certificates Step 0 (High; convention decision + ℚ-`decide` spike, both scoped in its proposal). The operator's uncommitted `proposals/README.md` sparsification-split rows, untracked `icebox/`, and untracked `proposals/spectral-graph-sparsification.md` preserved untouched; nothing committed.

## 2026-08-19T02:10:23Z — Electrical-flow routing, step 3 (Thomson's principle)

**Run:** `20260819T021023Z-run-1`  
**Session:** `ses_fe838cdecffeVErTeYOC0y9H9f`  
**Status:** in-progress  
**Milestone:** Continue the Active table's top High item `proposals/electrical-flow-routing.md` at its recorded next step — step 3: **Thomson's principle**, `effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow `θ` (electrical current as the energy minimizer; discrete integration by parts kills the cross term on the divergence-free difference; `flowEnergy_nonneg` closes). Zero new axioms; steps 4–5 not started this run.

## 2026-08-19T02:59:09Z — Electrical-flow step 3 delivered (Thomson's principle)

**Run:** `20260819T021023Z-run-1`  
**Session:** `ses_fe838cdecffeVErTeYOC0y9H9f`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/electrical-flow-routing.md`, step 3: **Thomson's principle** — `effectiveResistance A u v ≤ flowEnergy A θ` for every valid unit flow; the electrical current is the energy minimizer. Zero new axioms (13 unchanged); steps 4–5 (Rayleigh monotonicity, the ICP example) not started.

**Changes:** `GraphTheory.ElectricalFlow` gained the step-3 section — flow-space linearity (`flowDivergence_sub`, `isFlowOn_sub`), the **divergence-free superposition lemma** `flowEnergy_add_of_flowDivergence_eq_zero` (a zero-divergence flow perturbation of a current adds exactly its own energy; the discrete integration-by-parts cross term reduces by Ohm's law to `∑ i j, (f i − f j) * d i j`, whose row sums vanish by zero divergence and whose column sums are the negated row sums by antisymmetry — split out as its own reusable interface per the proposal's suggestion), and the headline `effectiveResistance_le_flowEnergy`. Route exactly as proposed: competitor minus unit-demand current is a divergence-free flow (Kirchhoff bridge + demand equation), superposition adds the difference's energy, `flowEnergy_nonneg` discards it, and the step-2 identity evaluates the current's energy as the resistance — load-bearing on the whole chain. **Statement-shape deviation recorded:** the superposition lemma is stated with **no hypotheses on `A`** (not even the symmetry the proposal's sketch assumed) — only the perturbation's flow properties enter. No `sInf` packaging, per the proposal's instruction. QA `ElectricalFlow_QA.lean` (+18, 59 in file): the new triangle `K₃` fixture (two parallel routes — unit flows non-unique) with resistance `2/3` and the **split current** (`2/3`/`1/3` across the routes) whose energy *attains* `2/3` from the raw definitions; the **detour competitor** (valid `IsUnitFlow`, all conjuncts computed, energy `2`) making Thomson's bound **strict** (`2/3 < 2` — the inequality is not vacuous); and the superposition decomposition composed as `2 = 2/3 + 4/3` with all three energies computed independently of the lemma. Docs: module/QA docstrings, scoreboard (543/13/0, milestone bullet, verification rows), radar (subject axis 6 re-scored **3.0 → 3.5** per protocol — the step-0/2 recorded reservation for Thomson fired; QA count 543/28 with the step-3 kind; proved-depth text; weakest-axes paragraph), README (surgical count/score sync inside the operator's uncommitted rewrite, otherwise untouched), SGT index map (4 new rows), proposal step-3 delivery record + deviation, and `proposals/README.md` progress note.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors/warnings; `lake build` of both targets ✔; full `lake build` ✔ (2180 targets); all 28 QA modules batch-elaborated, zero errors; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (543/13/0). Implementation notes: `Finset.mul_sum` rewrote reliably only via expected-type elaboration (`(Finset.mul_sum _ _ _).symm`), not `rw ←`; the triangle/detour fixtures use the entrywise-`if` pattern (the recorded matrix-notation `vecTail` trap).

**Remaining risk:** Thomson's statement requires `supportGraph`-level connectivity because the consumed solvability theorem does; the proof would go through unchanged at reachability strength for same-component pairs of disconnected graphs (the generalization is a statement-shape option, not a defect — the step-2 cheat fixture is excluded by the support conjunct, not by connectivity). Rayleigh monotonicity (step 4) remains unproved; the axis-6 score stays below 4.0 for exactly the recorded reasons (no Rayleigh, resistance metric, or Matrix–Tree/Kirchhoff).

**Next handoff:** proposal step 4 — Rayleigh monotonicity in conductance form (`A ≤ B` entrywise ⇒ `R_B ≤ R_A`, both graphs connected; the `A`-electrical unit flow as competitor on `B` + Thomson on `B`; orientation binding — conductances, not resistances; QA plan item 2, the capacity-increase `1 → 1/2` fixture, belongs there); then step 5 (the ICP capacity-reinforcement example). Alternatives: Foster Phase A (High; needs its statement-shape spike) or decidable-certificates Step 0 (High; convention decision + ℚ-`decide` spike, both scoped in its proposal). The operator's uncommitted README rewrite preserved (only the QA-count and axis-6 score cells synced); nothing committed.

## 2026-08-19T04:08:36Z — Electrical-flow routing, step 4 (Rayleigh monotonicity)

**Run:** `20260819T040836Z-run-1`  
**Session:** `ses_fe7cd9bc4ffeMTQNRZ8PY6Rdff`  
**Status:** in-progress  
**Milestone:** Continue the Active table's top High item `proposals/electrical-flow-routing.md` at its recorded next step — step 4: **Rayleigh monotonicity in conductance form**, entrywise `A ≤ B` ⇒ `effectiveResistance B u v ≤ effectiveResistance A u v` on connected symmetric nonnegative networks (the `A`-electrical unit flow as a competitor on `B`; its `B`-energy is at most its `A`-energy because every conductance increased; Thomson on `B` closes). Orientation binding: weights are conductances, so the inequality direction is `R_B ≤ R_A` — reversing it is a statement bug. Zero new axioms; step 5 (the ICP example) not started this run.

## 2026-08-19T05:44:53Z — Electrical-flow step 4 delivered (Rayleigh monotonicity in conductance form)

**Run:** `20260819T040836Z-run-1`  
**Session:** `ses_fe7cd9bc4ffeMTQNRZ8PY6Rdff`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/electrical-flow-routing.md`, step 4: **Rayleigh monotonicity in conductance form** — entrywise `A ≤ B` on connected symmetric nonnegative networks gives `effectiveResistance B u v ≤ effectiveResistance A u v`. Zero new axioms (13 unchanged); step 5 (the ICP example) not started.

**Changes:** `GraphTheory.ElectricalFlow` gained the step-4 section — `isFlowOn_of_le` (**flow-space growth**: a flow supported on `A` is a flow on every entrywise larger `B ≥ A ≥ 0`; support load-bearing — a `B`-zero entry above a nonnegative `A` entry squeezes the latter to zero, so the transferred current carries nothing there), `flowEnergy_le_of_le` (**raising conductances lowers dissipated energy**, termwise `θ²/B ≤ θ²/A` on nonzero branches since every denominator increased; support load-bearing a second time on the `A i j = 0 < B i j` branch, where the `B`-term would otherwise exceed the zeroed `A`-branch — the same zero-conductance trap as steps 2–3, now guarding the comparison), and the headline `effectiveResistance_le_of_le`, proved exactly by the proposed route: the `A`-unit-demand potential's current is a unit flow *on `B`* (growth + the Kirchhoff bridge), Thomson's principle (step 3) on `B` bounds `R_B` by its `B`-energy, the comparison bounds that by its `A`-energy, and the step-2 identity evaluates it as `R_A` — load-bearing on solvability, the Kirchhoff bridge, support, Thomson, and the energy identity. The conductance orientation is as the proposal binds; the optional `supportGraph B`-from-`A` connectivity adapter was deliberately not attempted (non-blocking per the proposal; noted for step 5's packaging if wanted). QA `ElectricalFlow_QA.lean` (+20, 79 in file): the proposal's QA item 2 — conductance `1 → 2` on the unit edge with the resistance decrease `1 → 1/2` certified from an independent potential witness, monotonicity instantiated, the decrease certified strict, and the **orientation guard** refuting the reverse inequality numerically (`1 ≤ 1/2` false — a resistance-direction restatement would be a false statement on this fixture); the competitor transfer instantiated on computed objects (the `edgeAdj`-current a unit flow on `edge2Adj`, cross-network energy `1/2 ≤ 1` from the raw definitions); and a partial increase on the triangle (one edge's conductance doubled: `2/3 → 2/5` strict, the new value pinned by the independent potential `![2/5, 0, 1/5]`). Docs: module/QA docstrings, scoreboard (563/13/0, verification rows, step-4 milestone bullet, cache-provenance note extended), radar (subject axis 6 re-scored **3.5 → 4.0** per the step-3 recorded reservation — Thomson and Rayleigh both landed; QA count 563/28 with the step-4 kind; proved-depth text; weakest-axes paragraph), README (counts, axis-6 cell 4.0, last-assessed date), SGT index map (3 new rows, header to steps 0–4), backlog item 7 (stale "deferred Rayleigh" note corrected — the conductance-form theorem is delivered via the flow route, only the Dirichlet-principle route remains deferred), proposal step-4 delivery record, and `proposals/README.md` progress note.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors, zero warnings; `lake build` of both targets ✔; full `lake build` ✔ (2180 targets); all 28 QA modules batch-elaborated with zero errors (only the documented pre-existing linter notes in untouched modules); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (563/13/0). Environment: the pruned Mathlib-oleans state recurred at run start (Mathlib build dir empty; the earlier 10/15-minute elaboration timeouts were the cold import chain, not a defect) — the recorded interpreted cache fetch (`lake env lean --run Cache/Main.lean get` from the mathlib package) restored all 5685 and the builds then elapsed normally (~15 s for the QA module); recorded in the scoreboard's provenance note. Implementation notes: `div_le_div_iff₀` needs the denominators in goal order (B then A); `div_le_div_right` is deprecated for `div_le_div_iff_of_pos_right`; the `B i j = 0` comparison branch must derive `A i j = 0` first (both branches then read `0 ≤ 0`) — `zero_le` on the unresolved `if` fails with a stuck instance.

**Remaining risk:** the headline hypothesizes connectivity of both graphs (the proposal's initial shape); the proof would compose unchanged with a reachability-strength Thomson if that generalization is ever wanted, and the adapter deriving `B`'s connectivity from `A`'s plus `A ≤ B` remains unwritten by design. The orientation guard witnesses the direction on one fixture, not a proof that no restatement could flip it silently — the statement-shape defense is the docstring's explicit conductance note plus the guard. Step 5 is packaging, so the program's mathematical content is now complete; the axis-6 residual gaps (resistance metric, Matrix–Tree, Kirchhoff network theorems) are unchanged.

**Next handoff:** proposal step 5 — the ICP capacity-reinforcement example (`effectiveResistance (increaseConductance A i j δ) u v ≤ effectiveResistance A u v` on a small `SimpleGraph.toWAdj` or weighted fixture, short enough for release documentation), completing the electrical-flow program; or the other High items (Foster Phase A — needs its pseudoinverse-free statement-shape spike; decidable-certificates Step 0 — convention decision + ℚ-`decide` spike, both scoped in its proposal). Concurrent operator additions preserved untouched: the new priority rows in `proposals/README.md` (Reversibility Phase A Medium, Relative Entropy Medium, Weighted Matrix-Tree Low), the untracked proposal files, the `icebox/` additions, and `why-sgt.md`. Nothing committed.

## 2026-08-19T06:01:17Z — Electrical-flow routing, step 5 (the ICP capacity-reinforcement example)

**Run:** `20260819T060117Z-run-1`  
**Session:** `ses_fe767f27affe0rGkDcONmxu57b`  
**Status:** in-progress  
**Milestone:** Complete the Active table's top High item `proposals/electrical-flow-routing.md` at its recorded final step — step 5, the ICP capacity-reinforcement example: `effectiveResistance (increaseConductance A i j δ) u v ≤ effectiveResistance A u v` as a one-hypothesis theorem (only the original network's connectivity is assumed; the increased network's connectivity is derived), plus the release-documentation QA fixture on a `SimpleGraph.toWAdj` path network with the decrease certified numerically. Packaging of step 4, not new mathematics; zero new axioms (13 unchanged). With step 5 the electrical-flow program is complete.

## 2026-08-19T06:17:20Z — Electrical-flow step 5 delivered (ICP capacity reinforcement); program complete

**Run:** `20260819T060117Z-run-1`  
**Session:** `ses_fe767f27affe0rGkDcONmxu57b`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/electrical-flow-routing.md`, step 5 — the ICP capacity-reinforcement example: `effectiveResistance (increaseConductance A i j δ) u v ≤ effectiveResistance A u v` as a one-hypothesis theorem (only the original network's connectivity hypothesized; the reinforced network's derived), plus the release-documentation QA fixture on the Mathlib path graph through `toWAdj`. Zero new axioms (13 unchanged); **with this step the electrical-flow program is complete** (all six steps, 0–5, delivered across five runs).

**Changes:** `GraphTheory.ElectricalFlow` gained the step-5 section — `increaseConductance` (raise one undirected pair's conductance by `δ`, both ordered entries together, symmetry/nonnegativity-preserving) with entry interfaces and structural lemmas (`increaseConductance_apply_of_reinforced`/`_of_not_reinforced`, `le_increaseConductance` for `0 ≤ δ`, `increaseConductance_isSymm`, `increaseConductance_nonneg`); the step-4-recorded optional adapter delivered as the packaging companion — `supportGraph_le_of_le` (support graphs grow along entrywise domination, stated with **no nonnegativity hypothesis**: `0 < A i j ≤ B i j`) and `supportGraph_connected_of_le` (capacity growth preserves connectivity, through Mathlib's `SimpleGraph.Connected.mono`, found in the pin — no local walk induction needed); and the one-hypothesis headline `effectiveResistance_le_increaseConductance`, composing step 4's monotonicity with the adapter. QA `ElectricalFlow_QA.lean` (+9, 88 in file) — the release-facing example on the Mathlib `Fin 3` path graph through `SimpleGraph.toWAdj`: adapter weights bridged entrywise to the weighted-fixture world; the reinforcement computed to exactly the concrete doubled-path matrix; the reinforced resistance `3/2` pinned by the independent potential witness `![1/2, 0, −1]` with connectivity from explicit walks (independent of the adapter the theorem consumes); the headline instantiated one-hypothesis; the decrease certified strict `3/2 < 2` against the pinned original `2`. Docs: module/QA docstrings, scoreboard (572/13/0, verification rows, step-5 milestone bullet), radar (QA 572/28; axis-6 evidence extended to program-complete, score **held at 4.0** per protocol — packaging, not new mathematics; step-4's 3.5 → 4.0 re-score added to the re-scoring log for continuity; proved-depth clause; header date), README (572), SGT index map (4 new rows, header to steps 0–5), backlog item 7 (program-complete note), proposal step-5 delivery record + status/open-next-step closure, and `proposals/README.md` (row moved to the Delivered table; progress note rewritten — Foster Phase A is now the top High item). Mid-run repair, recorded: a `True`-placeholder stub inserted by a bad edit was replaced with the real section before any verification ran.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.ElectricalFlow` and `ElectricalFlow_QA` — both zero errors/warnings (targeted `omit` clauses on unused section variables; note the QA re-elaboration required `lake build` of the module first — the direct elaboration had loaded the stale olean); `lake build` of both targets ✔; full `lake build` ✔ (2180 targets); all 28 QA modules batch-elaborated, zero errors; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (572/13/0). Implementation notes: the `WAdj` abbrev accepts only named application (`WAdj (V := V)`), not positional; `omit` must precede the doc comment and cannot drop an instance the `if`-condition's `Decidable` instance actually references (`DecidableEq V` is load-bearing in the entry lemmas); the path fixture's vertex 2 is reached through vertex 1 (no direct 0–2 edge — the triangle pattern does not transfer).

**Remaining risk:** none identified for the delivered statement — it is packaging of the step-4 theorem, whose orientation guard, strictness, and value pinning carry the falsification load, and the QA pins the packaged values (`2 → 3/2`) from independent potential witnesses. The axis-6 residual gaps are unchanged and recorded (resistance metric/triangle inequality, Matrix–Tree, Kirchhoff network theorems); the definiteness residual `R u v = 0 ↔ u = v` remains the family's cheap open item.

**Next handoff:** the Active table's top High item is now **Foster's Theorem Phase A** (`spectral-graph-sparsification.md`) — first run is its recorded pseudoinverse-free statement-shape spike (eigenbasis expansion + the proved one-dimensional kernel characterization); alternative: decidable-certificates Step 0 (convention decision + ℚ-`decide` spike, scoped in its own proposal). Operator's Medium/Low rows and the untracked `why-sgt.md` preserved untouched; nothing committed.

## 2026-08-19T06:35:36Z — Foster's Theorem Phase A (pseudoinverse-free eigenbasis route)

**Run:** `20260819T063536Z-run-1`  
**Session:** `ses_fe74f52a5ffeEdk04vfmw17jU0`  
**Status:** in-progress  
**Milestone:** The Active table's top High item `proposals/spectral-graph-sparsification.md`, **Phase A only**: Foster's theorem `(∑ i, ∑ j, A i j * R i j) / 2 = card V − 1` as pure hard crust via the proposal's pseudoinverse-free route — eigenbasis expansion of the unit-demand potential, summation swap, `quadForm(L, v_k) = λ_k` per unit eigenvector, and the proved one-dimensional kernel characterization for the `n − 1` count. Zero new axioms (13 unchanged); Phase B not started (blocked on the proposal's matrix-Chernoff scope decision). Environment: the pruned Mathlib-oleans state recurred at run start; the recorded interpreted cache fetch restored 5387 oleans before any elaboration.

## 2026-08-19T07:52:00Z — Foster's Theorem Phase A delivered; pure hard crust via the eigenbasis route

**Run:** `20260819T063536Z-run-1`  
**Session:** `ses_fe74f52a5ffeEdk04vfmw17jU0`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/spectral-graph-sparsification.md`, **Phase A only**: Foster's theorem `(∑ i, ∑ j, A i j * effectiveResistance A i j)/2 = card V − 1` proved as pure hard crust in the new `GraphTheory.Foster` — zero new axioms (13 unchanged; `#print axioms` confirms only `propext, Classical.choice, Quot.sound`), via the proposal's pseudoinverse-free eigenbasis route. Phase B not started (blocked on the proposal's matrix-Chernoff scope decision).

**Changes:** `GraphTheory.Foster` (5 declarations, all proved): `card_filter_eigvalOf_laplacian_eq_zero` (exactly one eigenbasis index lies in the kernel — at most one by orthonormality against the one-dimensional kernel `laplacian_kernel_eq_span_onesVec`, at least one because `onesVec` is a nonzero kernel vector whose nonzero-eigenvalue components die by self-adjointness), `effectiveResistance_eq_sum_eigbasis` (`R u v = ∑_k (v_k u − v_k v)²/λ_k` over nonzero eigenvalues; energy identity + `quadForm_eigvalOf` + `dotProduct_eigvecOf_mulVec`), `foster_theorem` (stated at full strength — no cardinality hypothesis; the `card V = 1` case degenerates to `0 = 0`), `leverageScore` (the Phase-B-facing importance-sampling object; junk below `2 ≤ card V` documented), and `sum_leverageScore_eq_two` (ordered scores sum to exactly `2`; unordered `1` — the probability-distribution statement, `hcard` as division guard). The proof swaps the double sum, evaluates the per-eigenvector Dirichlet sum to exactly `2 λ_k` (`laplacian_quadForm` + `quadForm_eigvecOf_self`), and counts the nonzero-eigenvalue indices — load-bearing on solvability, the kernel characterization, the spectral resolution, and eigenbasis orthonormality; an error in any breaks the proof. The `electrical-structure-crust.md` removal stands reconciled: it rejected the `L⁺` route, and no pseudoinverse is formed anywhere. QA `Foster_QA.lean` (53 declarations): `K₃`/`K₄`/`P₃`/3-leaf star, every resistance pinned by explicit potential witnesses (`K₄` via the general-pair potential `(e i − e j)/4`, proved to solve the unit demand for *every* pair through the entrywise `L = 4I − J` structure — all twelve ordered terms pinned by one lemma), ordered sums computed independently of the theorem (`4`/`6`/`4`/`6`) and cross-checked against `card V − 1` (`2`/`3`/`2`/`3`), the **double-counting factor refuted-on-omission on both cliques** (`4 ≠ 2`, `6 ≠ 3` — dropping the `/ 2` would falsify either side), non-edge pairs provably absent, leverage pinned (`1/3` edge / total `2` on `K₃`; `1/6` on `K₄`). Docs: module/QA docstrings, umbrella + its docstring, scoreboard (625/13/0, verification rows, milestone bullet), radar (subject axis 6 re-scored **4.0 → 4.5** per protocol — a new theorem family (global network identities), not packaging; QA 625/29; weakest-axes paragraph; re-scoring log), README (625, axis-6 cell 4.5, Foster added to the proved list and module table), SGT index map (5 new rows), backlog item 7, proposal Phase A delivery record + status header, `proposals/README.md` (row moved to Delivered; progress note rewritten — decidable-certificates Step 0 is now the top High item). Implementation notes: `Pi.single` applied at an index leaves its dependent function type unresolved in standalone statements — write function-level `Pi.sub` and distribute with `Pi.sub_apply` (the repo's own demand-equation style); `Finset.sum_div` is stated in the expanding direction, so collapsing sums needs `← Finset.sum_div`; conditional per-pair lemmas do not fire reliably as `simp only` rewrites after a fixture def is unfolded — use a per-term `hpair` case lemma or two-phase simp (`simp only [value lemmas]` before `simp [fixture]`).

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.Foster` and `Foster_QA` — both zero errors, zero warnings (five QA lemmas carry targeted `set_option linter.unreachableTactic/unusedTactic false in` where `simp` closes some `fin_cases` branches); `#print axioms` on all four public theorems — only the three standard axioms; `lake build Scaffold.Mathlib.GraphTheory.Foster` ✔; full `lake build` ✔ (2181 targets); all 29 QA modules batch-elaborated, zero errors (only the eight documented pre-existing section-variable warnings in untouched modules); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (625/13/0). Environment: the pruned Mathlib-oleans state recurred at run start; the recorded interpreted cache fetch restored 5387 oleans before any elaboration.

**Remaining risk:** the leverage-score def deliberately omits a cardinality parameter (matching the proposal sketch) — the junk value at `card V ≤ 1` is documented but not hypothesis-guarded; the corollary carries the guard. The axis-6 re-score to 4.5 rests on Foster opening the global-identity family; Matrix–Tree and the Kirchhoff loop/cut-space theorems remain absent, as does the resistance metric (triangle inequality, definiteness residual `R u v = 0 ↔ u = v`). Phase B stays blocked exactly as recorded — the leverage scores define its distribution but nothing probabilistic exists yet.

**Next handoff:** the Active table's top High item is now **decidable spectral certificates Step 0** (`decidable-spectral-certificates.md` — the adjacency-vs-Laplacian eigenvalue convention decision plus the ℚ-`decide` kernel spike, both scoped in the proposal; Step 1 must not begin before both are recorded). Medium alternatives: Fiedler Phase B (needs an operator decision on the admitted hard direction), mixing-time Step 1, Reversibility Phase A, Relative Entropy. The operator's Medium/Low rows and the untracked `why-sgt.md` preserved untouched; nothing committed.

## 2026-08-19T13:24:13Z — Decidable spectral certificates, step 0 (convention decision + ℚ-decide spike)

**Run:** `20260819T132413Z-run-1`  
**Session:** `ses_fe5d101b1ffeAcbY8TX1lYR3o7`  
**Status:** in-progress  
**Milestone:** Open the Active table's top High item `proposals/decidable-spectral-certificates.md` at its recorded gate: **step 0** — decide the adjacency-vs-Laplacian eigenvalue convention for `expander_mixing_lemma` (survey-backed, recorded in the proposal with a restated theorem signature) and spike whether plain kernel `decide` actually verifies a rational spectral certificate on a concrete `Fin n` graph (n = 4 and n = 6), the two unaddressed gaps the proposal itself names as blocking Step 1. If both land cleanly, deliver Step 1's smallest independently useful Lean slice (the `edgeWeight` discrepancy core and the indicator decomposition) in the new `GraphTheory.Expander`, following the electrical-flow steps 0–1 precedent. Zero new axioms (13 unchanged); steps 2–4 not started this run.

## 2026-08-19T14:30:11Z — Decidable-certificates steps 0–1 delivered (convention + decide spike + the Expander discrepancy core)

**Run:** `20260819T132413Z-run-1`  
**Session:** `ses_fe5d101b1ffeAcbY8TX1lYR3o7`  
**Status:** completed  
**Milestone:** The Active table's top High item `proposals/decidable-spectral-certificates.md`, its Step 0 gate (convention decision + ℚ-`decide` spike, both recorded in the proposal) and Step 1 (`GraphTheory.Expander`: `edgeWeight`, the centered-indicator decomposition, and the `d`-regular main-term split — the discrepancy core of the Expander Mixing Lemma). Zero new axioms (13 unchanged); steps 2–4 not started.

**Changes:** **Step 0** — (1) convention decided **Laplacian-first through the `d`-regular bridge**, with the survey evidence recorded (no adjacency-eigenvalue interface exists in the codebase; the certificate half is already Laplacian; the generic symmetric engine applies to adjacency for free, so the bridge `A = d•1 − L` needs no new interface; no named consumer wants adjacency eigenvalues) and the restated `expander_mixing_lemma` signature pinned in Laplacian terms (the `√`-form as the mathematical statement, squaring recorded as a Step-2 implementation option); (2) the ℚ-`decide` spike found a genuine wall, not a slow path: plain kernel `decide` **cannot** verify the proposal's ℚ-arithmetic certificate because `Rat` operations never unfold in elaborator reduction (`((2:ℚ) + 2) = 4` is already stuck at `(Rat.add 2 2).num` — ℚ literals are opaque kernel literals; controls `Nat.gcd`, ℕ-sums over `Fin`, and ℤ arithmetic all decide fine; `#eval` works but is native, not kernel-checked; `native_decide` excluded by the proposal's own rule) — adopted fallback recorded: the **integer cross-multiplied twin** (`rawNumer ≤ 2 * bound * denom`, all data in ℤ), kernel-decided clean on `C₄` (`Fin 4`, attained `λ₂ = 2`, accept + all three reject paths) and `C₆` (`Fin 6`, attained `λ₂ = 1`) plus the fractional-bound clearing form, ~sub-second decide overhead; (3) Ramanujan QA scope resolved to the existing `Kₙ`/`Cₙ` fixtures (both small Ramanujan instances). **Step 1** — the new `GraphTheory.Expander` (all proved): `edgeWeight` with degenerate/degree-sum interfaces, the hypothesis-free matrix form `edgeWeight_eq_dotProduct`, `edgeWeight_symm`; `indicatorVec`/`centeredIndicator` with the decomposition and **unconditional** orthogonality to `onesVec` (empty-type case handled, no `Nonempty` hypothesis); and the headline `edgeWeight_eq_regular_add_centered` (`e(S,T) = d·|S|·|T|/n + centered cross term`), symmetry load-bearing through `Matrix.dotProduct_mulVec`'s transpose and regularity through the `A *ᵥ onesVec = d` evaluation. QA `Expander_QA.lean` (22 declarations, fresh `C₄` fixture): all values from the raw definitions, the decomposition instantiated on adjacent (`1 = 1/2 + 1/2`) and opposite (`0 = 1/2 − 1/2`) cuts with independently computed cross terms, and three negative witnesses (main-term-only refuted `0 ≠ 1/2`; wrong degree `1 ≠ 3/4`; asymmetric weight breaks cut symmetry `2 ≠ 1`). Docs: module/QA docstrings, umbrella, scoreboard (647/13/0, verification rows, milestone bullet), radar (QA 647/30 with the new QA kind; QA axis **held at 4.0** per protocol with the hold recorded — decisions and plumbing, the parametric-QA gap untouched), README (647, cuts-and-expansion row), SGT index map (new `Expander` section), proposal Step-0 record + Step-1 delivery record, `proposals/README.md` progress note.

**Decisive commands and outcomes:** `lake env lean` on `GraphTheory.Expander` and `Expander_QA` — both zero errors, zero warnings; `#print axioms` on all seven public theorems — only `propext, Classical.choice, Quot.sound`; `lake build` of both targets ✔; full `lake build` ✔ (2182 targets); all thirty QA modules batch-elaborated, zero errors; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (647/13/0). Environment: the pruned-oleans state recurred (mathlib empty; Batteries only partially restored by the cache fetch — an explicit `lake build Batteries` was needed before `Mathlib.Tactic` imports would resolve); the full cold build elapsed ~33 min; recorded in the plan for the next run. Spike implementation notes recorded: `.decide` field notation is invalid on `Prop`-typed expressions (use `decide (...)`); `omit`/`set_option ... in` must precede doc comments.

**Remaining risk:** the integer-twin re-scoping changes Step 3's deliverable shape (ℚ soundness statement + ℤ twin + proved bridge lemma); the twin has been spiked but its soundness bridge is unproved. The Step-2 bridge (eigenvalue hypothesis → Rayleigh-form operator bound on `x ⊥ 1`) is unbuilt and is the next load-bearing dependency; the radar holds reflect that the mixing lemma itself is not yet stated. The restated EML signature is recorded but not yet elaborated.

**Next handoff:** proposal Step 2 — the Expander Mixing Lemma: the bridge layer (eigenvalue hypothesis → `|xᵀAx| ≤ μ xᵀx` on `x ⊥ 1` via the eigenbasis/Courant–Fischer machinery), the centered-cross-term bound by Cauchy–Schwarz, packaged at the restated signature; then Step 3 (certificate module with the ℤ twin + soundness bridge) and Step 4 (QA incl. kernel-`decide` demonstrations). Medium alternatives queued (Fiedler Phase B — decision-gated; mixing-time Step 1; Reversibility Phase A; Relative Entropy). The operator's untracked `adversarial.md`, `sgt-gaps.md`, and `why-sgt.md` preserved untouched; nothing committed.

## 2026-08-19T15:01:42Z — Decidable spectral certificates, Step 2 (Expander Mixing Lemma)

**Run:** `20260819T150142Z-run-1`  
**Session:** `ses_fe57b012dffeLl1r2RrcTtsu8E`  
**Status:** in-progress  
**Milestone:** Deliver Step 2 of `proposals/decidable-spectral-certificates.md` (top High item): the Expander Mixing Lemma as hard crust — the bridge from the Laplacian-form eigenvalue hypothesis to the Rayleigh-form operator bound on `1⊥`, the centered cross-term bound, and the packaged restated `expander_mixing_lemma` signature, with C₄ QA including equality sharpness witnesses. Leverage: the theorem the proposal exists to deliver and the layer Step 3's certificates compose with.

**Changes:** intent recorded; Lean work starting (generic `evals`-last facts in `Spectral.lean`, bridge layer + headline in `GraphTheory/Expander.lean`, QA extension in `SpectralGraph/Expander_QA.lean`).

## 2026-08-19T16:25:49Z — Decidable spectral certificates Step 2 delivered (the Expander Mixing Lemma)

**Run:** `20260819T150142Z-run-1`  
**Session:** `ses_fe57b012dffeLl1r2RrcTtsu8E`  
**Status:** completed  
**Milestone:** Step 2 of `proposals/decidable-spectral-certificates.md` (top High item): the Expander Mixing Lemma proved as hard crust — the classical discrepancy bridge between Laplacian spectral gaps and combinatorial pseudorandomness, and the layer Step 3's certificates compose with.

**Changes:** `GraphTheory.Expander` extended with the Step-2 bridge layer and the headline `expander_mixing_lemma` (at the Step 0 restated `√` signature, minus the found-unnecessary `hloop` hypothesis — deviation recorded in the proposal); `GraphTheory.Spectral` gains the generic `eigvalOf_le_evals_last`, `quadForm_le_evals_last` (top Rayleigh domination, multiplication form), and a public `dotProduct_self_pos`; `Expander_QA.lean` +19 declarations (derived spectral hypothesis, EML instantiations, sharpness witnesses); scoreboard, radar (axis 4 re-scored 3.5 → 4.0, logged; QA held at 4.0 per protocol), README (666 counts, axis-4 cell), SGT index map, umbrella, and both proposal records updated.

**Verification:** `lake env lean` on both changed public modules and the QA module — zero errors, zero warnings; `#print axioms` on the nine new public theorems — only `propext, Classical.choice, Quot.sound` (zero new axioms, count stays 13); full `lake build` ✔ (2182 targets); all thirty QA modules batch-elaborated, zero errors; `lint_axioms`, `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (666/13/0).

**Remaining risk:** the derived-`μ` QA derives `μ = 2` via bounds rather than exact spectrum pinning on `C₄` (exact pins are Step 4's planned route); `Mathlib.cons_val`-style literal evaluation required the pinned simp set (`cons_val_two`, no `vecTail` unfolding) — recorded here for future QA on 4-vertex fixtures.

**Next handoff:** proposal Step 3 — the certificate module (ℚ-facing soundness statement + the kernel-verifiable integer cross-multiplied twin, bridged by a proved cross-multiplication lemma), then Step 4 QA. The operator's concurrent changes (untracked `governance/ADVERSARIAL_REVIEW.md`, six new untracked proposals including `directed-graph-operators.md`, and edits to `1_STRATEGY.md`, `6_SGT_BACKLOG.md`, `CONTRIBUTING.md`, `admit-perron-frobenius.md`, `electrical-flow-routing.md`) were observed mid-run and preserved untouched.

## 2026-08-19T16:55:00Z — Decidable spectral certificates, Step 3 (certificate module)

**Run:** `20260819T164730Z-run-1`  
**Session:** `ses_fe5173fcbffeWuvtINn3O7CbOt`  
**Status:** in-progress  
**Milestone:** Deliver Step 3 of `proposals/decidable-spectral-certificates.md` (top High item): the computable certificate module — the ℚ-facing checker with its soundness theorem `lambda2_le_of_certificate` (a load-bearing consumer of the proved `lambda2_variational`), the kernel-verifiable ℤ cross-multiplied twin, and the proved bridge between them — plus the C₄ kernel-`decide` QA core. Leverage: closes the extraction gap the proposal exists for; first end-to-end proof-carrying-certificate chain (integer arithmetic → kernel `decide` → proved ordered-field bridge → real spectral center).

**Changes:** intent recorded in the execution plan; environment restored (pruned oleans state recurred; interpreted cache fetch re-applied, 5685 files unpacked); Lean work starting in `GraphTheory/SpectralCertificates.lean` and `SpectralGraph/SpectralCertificates_QA.lean`.

## 2026-08-19T17:58:00Z — Decidable spectral certificates Step 3 delivered (the certificate module)

**Run:** `20260819T164730Z-run-1`  
**Session:** `ses_fe5173fcbffeWuvtINn3O7CbOt`  
**Status:** completed  
**Milestone:** Step 3 of `proposals/decidable-spectral-certificates.md` (top High item): the computable certificate module — the ℚ specification checker with its soundness theorem `lambda2_le_of_certificate` (the flagship load-bearing consumer of the proved `lambda2_variational`), the kernel-verifiable ℤ cross-multiplied twin and its fractional variant, and the proved cross-multiplication bridges — plus the C₄ kernel-`decide` QA core. Leverage: closes the proposal's extraction gap inside Lean; first end-to-end proof-carrying-certificate chain (integer arithmetic → kernel `decide` → proved bridge → real spectral bound).

**Changes:** new `GraphTheory.SpectralCertificates` (transport layer with the `rfl` hinge `algebraMap_apply`; `lambda2_le_rayleigh` consumer form; the ℚ checker + soundness; the ℤ twins; sound-and-complete integer bridge + fractional cross-multiplication bridge with the `0 < den` hypothesis external — genuinely needed for the reverse direction; kernel-facing corollaries via the `subst`-based `lambda2_le_of_matrix_eq` transfer); new `SpectralCertificates_QA.lean` (22 declarations); umbrella, SGT index map (new section, 11 rows), scoreboard (688/13/0 + verification rows + milestone bullet), radar (axis 7 re-scored 3.0 → 3.5, logged; QA count 688/31, held at 4.0 per protocol), README, proposal Step-3 delivery record, and `proposals/README.md` (High row → Step 4) updated.

**Verification:** `lake env lean` on both new modules — zero errors, zero warnings; `#print axioms` on the eight headline public theorems and five key QA theorems — only `propext, Classical.choice, Quot.sound` (zero new axioms, count stays 13); all thirty-one QA modules batch-elaborated, zero errors; full `lake build` ✔ (2183 targets, one more than before; 6:27 wall); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (688/13/0).

**Remaining risk:** the C₄ QA pins the certified bound to the test vector's exact Rayleigh quotient and witnesses accept/reject sharpness, but `lambda2 (C₄) = 2` itself is not pinned (the exact lower bound is Step 4's natural completion, with the `C₆`/Ramanujan fixtures); the fractional bridge's reverse direction needs the external `0 < den` (recorded in the theorem docstring); the ℚ checker remains evaluation-unreachable by the kernel by design — every consumer must go through a bridge, which is the recorded architecture, not a defect. Environment: the pruned-oleans state recurred at run start; the recorded interpreted cache fetch re-applied before elaboration; the full build replayed the trace chain cleanly.

**Next handoff:** proposal Step 4 — QA and extraction demonstration: `C₆` kernel-`decide` demonstrations, the `Kₙ`/`Cₙ` Ramanujan fixture family (drop-if-awkward fallback per the Step 0 scope decision), exact spectrum pins making the certified bounds' sharpness checkable against `lambda2` itself, and the Acceptance-Criterion-4 documentation notes (traction-plan included). The operator's other queued items (the new resolvent-calculus/Tikhonov/band-projector High rows with their Step-0 spikes; Fiedler Phase B still decision-gated) are unchanged; nothing committed.

## 2026-08-19T18:57:27Z — Decidable spectral certificates, Step 4 (QA and extraction demonstration)

**Run:** `20260819T185727Z-run-1`  
**Session:** `ses_fe4a17e43ffeA287ckVygl1V11`  
**Status:** in-progress  
**Milestone:** Deliver Step 4 of `proposals/decidable-spectral-certificates.md` (top High item, the program's final step): QA expansion — the `C₆` kernel-`decide` demonstrations, the `Kₙ`/`Cₙ` Ramanujan fixture family per the Step 0 scope decision, exact spectrum pins (`lambda2 (C₄) = 2` — the C₄ QA pins the quotient, not the value; the exact lower-bound pin via a C₄ Poincaré inequality is this step's named completion), and the Acceptance-Criterion-4 documentation notes (scoreboard/radar/traction-plan). Leverage: makes the Step-3 certificate chain's bounds witnessed-sharp against `lambda2` itself. Zero new axioms (13 unchanged); QA-only changes.

**Changes:** intent recorded; environment verified healthy at run start (5382 Mathlib oleans present — no cache fetch needed this run); Lean QA work starting in `SpectralCertificates_QA.lean` and `Expander_QA.lean`.

## 2026-08-19T19:28:41Z — Decidable spectral certificates Step 4 delivered; program complete (QA and extraction demonstration)

**Run:** `20260819T185727Z-run-1`  
**Session:** `ses_fe4a17e43ffeA287ckVygl1V11`  
**Status:** completed  
**Milestone:** Step 4 of `proposals/decidable-spectral-certificates.md` (top High item, the program's final step): QA and extraction demonstration — the `C₆` kernel-`decide` demonstrations at the second required size, exact spectrum pins making the certified bounds witnessed-sharp against `lambda2` itself (`lambda2 (C₄) = 2` via a Poincaré inequality through the *lower* half of `lambda2_variational`), the `Kₙ`/`Cₙ` Ramanujan fixture family per the Step 0 scope decision, and the Acceptance-Criterion-4 documentation notes (scoreboard/radar/traction-plan). With this step all five steps (0–4) are delivered and the proposal's acceptance criteria 1–4 are met. Zero new axioms (13 unchanged); QA-only changes.

**Changes:** `SpectralCertificates_QA.lean` (+17 declarations, 39 in file): the `C₆` fixture and the whole certificate chain kernel-decided (accept at the attained bound `1`, reject at `0`, fractional `3/2` accepted / `1/2` rejected, arithmetic pinned from the raw definitions — `rawNumer = 8`, `denom = 4`, quotient `8/(2·4) = 1` — the ℚ specification reached only through the proved bridge, end-to-end `lambda2 (C₆) ≤ 1` and `≤ 3/2`); the `C₄` Poincaré inequality (`2‖x‖² ≤ xᵀLx` on `1⊥`, by the Wirtinger identity `E = 2Σx² + 2(x₀+x₂)²` under `Σx = 0`) consumed through `le_csInf` — the proved `lambda2_variational`'s first QA consumer in the `≥` direction — pinning `lambda2 (C₄) = 2` exactly, with `cert4_certificate_exact_QA` stating the chain's exact tightness (the kernel checker accepts precisely at the true `lambda2` and rejects the integer bound `1` below it). `Expander_QA.lean` (+47, 88 in file): the exact `C₄` pins (`λ₂ = 2` Poincaré-below/test-vector-above; `λ_max = 4` by the alternating vector through the generic `quadForm_le_evals_last`), so `μ(C₄) = 2` exactly and the Ramanujan bound `2√(d−1)` is attained with equality; the `K₃` fixture (entry-table + the exact clique energy identity `xᵀLx = 3‖x‖² − (Σx)²`, pinning `λ₂ = λ_max = 3` and `μ(K₃) = 1` — strictly Ramanujan — with the EML attained exactly on both cuts tested, both sides computing to `2/3`); the `C₆` EML with derived `μ ≤ 2` (test vector `λ₂ ≤ 1`, the energy identity `xᵀLx = 4‖x‖² − Σ_edges(xᵢ+xᵢ₊₁)²` for `λ_max ≤ 4`, PSD below), attained exactly on the alternating cut `({0,2,4},{0,2,4})` (both sides compute to `3`). Docs: scoreboard (752/13/0, verification rows + step-4 milestone bullet), radar (QA axis 752/31 with the exact-pin/second-size kinds described; subject axes 4 and 7 evidence extended with scores **held at 4.0/3.5 per protocol** and the holds logged; remaining-gap note updated), traction plan (dated note recording that the extraction-gap revisit precondition it names is now met — planning provenance, respecting the document's clean-room boundary), README (752), proposal Step-4 delivery record + status header (program complete), and `proposals/README.md` (row moved to the Delivered table; progress note rewritten — the three `sgt-gaps`-promoted High rows are now the top of the Active table).

**Decisive commands and outcomes:** `lake env lean` on both changed QA modules — zero errors, zero warnings; `#print axioms` on all 22 new headline theorems — only `propext, Classical.choice, Quot.sound` (zero new axioms, count stays 13); all thirty-one QA modules batch-elaborated, zero errors; full `lake build` ✔ (2183 targets); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (752/13/0). Environment healthy at run start (full Mathlib oleans present — the pruned-oleans state did not recur).

**Remaining risk:** the `C₆` Ramanujan statement is the inequality (`μ ≤ 2`), not the exact pin `μ = 2` — the exact value needs the `C₆` Wirtinger/Poincaré constant (genuinely nonlinear, not attempted; recorded in the delivery record as the named residual). The exact pins exist only on `C₄`/`K₃`; nothing generalizes the Poincaré inequalities beyond fixtures, and the radar's QA-axis named gap (parametric/randomized QA) is untouched — the QA axis hold reflects that. Implementation note for future 6-vertex QA (recorded in the proposal): the `cons_val` simp family stops at index four — a `rfl`-provable `vecCons_val_five` helper bridges index five when both indices are `OfNat`-literals from sum expansion, but `fin_cases`-produced `Fin.mk` row indices defeat the chain (row sums proved per row by `show` up to defeq instead); ℤ structural facts evaluate by `decide` where ℝ ones cannot.

**Next handoff:** the Active table's top High rows are now the three `sgt-gaps`-promoted items with their recorded entry points — Resolvent Calculus for PSD Matrices (Step 0 first: the unverified `IsSelfAdjoint.spectralRadius_eq_nnnorm` thread for the operator-norm bridge), Tikhonov Regularization in the Laplacian Eigenbasis (no gate), and Spectral Band Projectors (no gate — the difference of two existing `spectralProjector` calls). Medium rows queued behind them (Fiedler Phase B still decision-gated; mixing-time Step 1; Reversibility A/B; Relative Entropy; Perron–Frobenius + directed operators; discharge-perturbation; approximate spectral projection). Nothing committed.

## 2026-08-19T20:32:40Z — Resolvent calculus steps 0–1 (norm-bridge spike + invertibility/resolvent identity)

**Run:** `20260819T203139Z-run-1`  
**Session:** `ses_fe44b2290ffeeaVzXvL7dNQOvY`  
**Status:** in-progress  
**Milestone:** Deliver Steps 0 and 1 of `proposals/resolvent-calculus-psd.md` (top High item). Step 0's spike is already decisive: the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is structurally inapplicable to real matrices (`CStarAlgebra` extends `NormedAlgebra ℂ A`; elaboration-verified missing), so the operator-norm bridge falls back to the from-scratch eigenbasis route (Parseval + eigenaction + `l2_opNorm` bookkeeping). Step 1: `A + t•1` invertible for PSD symmetric `A` and `0 < t`, plus the resolvent identity. Leverage: the bridge is a one-time cost shared by the resolvent norm/Lipschitz bounds (items 2/4) and the `discharge-perturbation-axioms.md` Weyl target. Zero new axioms (13 unchanged).

**Changes:** intent recorded in the execution plan; environment restored (pruned oleans recurred — interpreted cache fetch re-applied, 5387 Mathlib oleans); Lean work starting in `Analysis/OperatorTheory/Resolvent.lean` and `QA/OperatorTheory/Resolvent_QA.lean`.

## 2026-08-19T21:46:39Z — Resolvent calculus steps 0–1 delivered (operator-norm bridge + invertibility/resolvent identity)

**Run:** `20260819T203139Z-run-1`  
**Session:** `ses_fe44b2290ffeeaVzXvL7dNQOvY`  
**Status:** completed  
**Milestone:** Steps 0 and 1 of `proposals/resolvent-calculus-psd.md` (top High item). Step 0's spike was decisive: the C*-algebra thread `IsSelfAdjoint.spectralRadius_eq_nnnorm` is structurally inapplicable to real matrices (`CStarAlgebra` extends `NormedAlgebra ℂ A`/`StarModule ℂ A`; `NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℝ)` fails to synthesize — elaboration-verified), so the operator-norm bridge was proved from scratch per the proposal's own contingency: `l2OpNorm_eq_max_abs_evals` (`‖M‖ = max |evals hM 0| |evals hM last|` for every real symmetric matrix) with both directions (`abs_eigvalOf_le_l2OpNorm` via the unit eigenvector through `toEuclideanCLM`; `l2OpNorm_le_of_abs_eigvalOf_le` via Parseval + the eigenaction identity), consuming the new center mirror lemma `evals_first_le_eigvalOf`. Step 1: `M + t•1` invertible for any matrix with nonnegative quadratic form and `t > 0` (kernel-vector route, **no symmetry needed** — a recorded strengthening) plus the `t = 1` instance, and the resolvent identity `(A+1)⁻¹ − (B+1)⁻¹ = (A+1)⁻¹(B−A)(B+1)⁻¹`. The bridge is the shared route for Step 2's bounds and the `discharge-perturbation-axioms.md` Weyl target. Zero new axioms (13 unchanged).

**Changes:** new `Analysis.OperatorTheory.Resolvent` (8 public theorems, all proved; the Step-0 route decision recorded in the module docstring); one generic addition to `GraphTheory.Spectral` (`evals_first_le_eigvalOf`); new `QA/OperatorTheory/Resolvent_QA.lean` (30 declarations: the `!![2,1;1,2]` spectrum pinned from trace/det/sortedness with `‖mat2‖ = 3` pinned by both bridge directions, the `¬(‖mat2‖ ≤ 1)` negative witness, shifted-PSD invertibility cross-checked against computed determinants with the unshifted-Laplacian-determinant-`0` shift guard, and the resolvent identity checked against both-sides-computed literal matrices); umbrella, scoreboard (782/13/0 + verification rows + milestone bullet; `OperatorTheory` a new QA domain), radar (axis 2 evidence extended, score held at 3.5; QA 782/32 held at 4.0; both holds logged), README (782 + proved list), Mathlib coverage map (the operator-norm row's verified finding), perturbation index map (Resolvent section), proposal Step-0 record + Step-1 delivery + status header, and `proposals/README.md` (High row → Step 2). The operator's concurrent edits (`governance/ADVERSARIAL_REVIEW.md`, `proposals/discharge-perturbation-axioms.md`) preserved untouched; nothing committed.

**Decisive commands and outcomes:** `lake env lean` on the three changed Lean modules — zero errors, zero warnings; `#print axioms` on all 8 public theorems + 6 QA headlines — only `propext, Classical.choice, Quot.sound`; all thirty-two QA modules batch-elaborated, zero errors; full `lake build` ✔ (2184 targets, "Build completed successfully"); `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (782/13/0). Environment: the pruned-oleans state recurred at run start (Mathlib build dir empty); the recorded interpreted cache fetch restored 5387 before elaboration; the full build replayed the Mathlib trace residue (~35 min).

**Remaining risk:** the bridge is stated for symmetric matrices through the `L2OpNorm` scoped instance — its consumption by the Weyl-discharge target will need the norm's statement-shape match re-checked when that run starts (the axiom's `‖E‖` was elaborated under the same scoped instance, so they should agree definitionally, but this is asserted, not yet consumed-in-anger); Step 2's eigenvalue transfer for `M + t•1`/`(A+1)⁻¹` (shared eigenvectors, shifted/inverted eigenvalues, and the sorted-spectrum bookkeeping) is unwritten and is the natural next cost; the QA fixtures are 2×2 only (the norm bridge is not exercised on a multi-eigenvalue non-attaining fixture).

**Next handoff:** Resolvent Step 2 — `‖(A+1)⁻¹‖ ≤ 1` and the Lipschitz bound `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖` (the latter is submultiplicativity `l2_opNorm_mul` + item 2 twice once the norm bound lands), then Step 3's one-line injectivity; or the ungated High rows (Tikhonov, Band Projectors). Medium rows queued behind them. Implementation notes for future L2OpNorm work are recorded in the execution plan (transport spine lemmas, the `rw`-with-bare-`1` trap, entrywise-vs-literal matrix computation, the `(2 : ℝ)` ascription for matrix smul).

## 2026-08-19T22:38:53Z — Resolvent calculus Step 2 (norm bound + Lipschitz bound)

**Run:** `20260819T223853Z-run-1`  
**Session:** `ses_fe3d60017ffeaZgd5m1Hx3kWAu`  
**Status:** in-progress  
**Milestone:** Deliver Step 2 of `proposals/resolvent-calculus-psd.md` (top High item): the norm bound `‖(A+1)⁻¹‖ ≤ 1` and the Lipschitz bound `‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖`, zero new axioms (13 unchanged). Planned route deviation to record at delivery: the energy route (`y = (M+t•1)⁻¹x` gives `t‖y‖² ≤ quadForm M y + t‖y‖² = yᵀx ≤ ‖y‖‖x‖` by dot-product Cauchy–Schwarz, packaged via the Step-0 `opNorm_le_bound` spine) instead of the sketched eigenvalue transfer — strictly stronger (no symmetry hypothesis, general `t`), cheaper; the sorted-eigenvalue transfer stays a named residual. The Lipschitz bound stays load-bearing on Step 1 (invertibility + the resolvent identity).

**Changes:** intent + route decision recorded in the execution plan; environment restore started (the pruned Mathlib-oleans state recurred; the recorded interpreted cache fetch is running in the background). Lean work to follow in `Analysis/OperatorTheory/Resolvent.lean` and `QA/OperatorTheory/Resolvent_QA.lean`.

## 2026-08-19T23:56:55Z — Resolvent calculus Step 2 delivered (norm bound + Lipschitz bound)

**Run:** `20260819T223853Z-run-1`  
**Session:** `ses_fe3d60017ffeaZgd5m1Hx3kWAu`  
**Status:** completed  
**Milestone:** Step 2 of `proposals/resolvent-calculus-psd.md` (top High item) delivered as pure hard crust, zero new axioms (13 unchanged; `#print axioms` on the three new public theorems reads only `propext, Classical.choice, Quot.sound`): the proposal's items 2 and 4. **Recorded route deviation:** the energy route instead of the sketched eigenvalue transfer — for `y = (M+t•1)⁻¹x`, `t‖y‖² ≤ quadForm M y + t‖y‖² = y ⬝ᵥ x ≤ ‖y‖‖x‖` (dot-product Cauchy–Schwarz through the bridge's own `opNorm_le_bound` spine) gives the **strictly stronger general-`t`** `l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg` (`‖(M+t•1)⁻¹‖ ≤ t⁻¹`, **no symmetry hypothesis**; the energy inequality itself holds for any `t`), the `t=1` instance `l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg`, and the **Lipschitz bound** `l2OpNorm_resolvent_sub_le_of_quadForm_nonneg` (`‖(A+1)⁻¹ − (B+1)⁻¹‖ ≤ ‖A−B‖`) — Step-1 resolvent identity + the scoped `NormedRing` submultiplicativity + the norm bound twice, load-bearing on Step 1's invertibility and identity. The sorted-eigenvalue transfer stays a named residual (mixing-time is the named consumer).

**Changes:** `Analysis.OperatorTheory.Resolvent` extended (3 public theorems + 2 private helpers; docstring to steps 0–2); `QA/OperatorTheory/Resolvent_QA.lean` +45 declarations (75 in file): the norm bound **attained with route agreement** (`‖(L(K₂)+1)⁻¹‖ = 1` exactly — the energy-route theorem and the eigenvalue-bridge route independently meeting at the pinned spectrum `{1/3,1}`; `‖(L+2•1)⁻¹‖ = 1/2` exactly at `{1/4,1/2}`), the Lipschitz instance with both sides independently pinned (`2/3 ≤ 2`), the **shift guard** (invertible PSD `(1/4)I` unshifted has `‖A⁻¹‖ = 4 > 1` — the proposal's QA item 3), and the **hypothesis guard** (`-(3/4)I`'s shift is invertible with inverse norm `4 > 1`, the violated quadForm exhibited at `-3/4 < 0`). Records: scoreboard (827/13/0, verification rows + milestone bullet), radar (axis-2 evidence completed, **held at 3.5** — family completion; QA 827/32 **held at 4.0**; both holds logged; proved-depth extended), README (827, proved list), perturbation index map (+3 rows; deferred narrowed to Step-3 injectivity), proposal Step-2 delivery record + open-next-step (Step 3), `proposals/README.md` (High row → Step 3). The operator's concurrent untracked `governance/mathlib-standards.md` preserved untouched; nothing committed.

**Decisive commands and outcomes:** `lake env lean` on the changed public module and its QA — zero errors, zero warnings; `#print axioms` on 3 public + 8 QA headline theorems — three standard axioms only; all thirty-two QA modules batch-elaborated — zero errors (only the eight documented pre-existing section-variable warnings in untouched modules); **full `lake build` ✔ (2184 targets, exit 0)**; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (827/13/0). Environment: the pruned-oleans state recurred at run start; the recorded interpreted cache fetch restored 5685 oleans (~4 min) before any elaboration; fast-`lean -o` olean production used during iteration. Implementation notes (coercion/parse traps: `prod_eq_multiset_prod`, `simpa`-only coercion removal in `det_eq_prod_eigenvalues`, `abs_of_nonneg` with explicit side proofs, `-2/3` and `1/4 * 1/2` parse shapes, the generalized two-point pin) recorded in the execution plan.

**Remaining risk:** the QA fixtures are 2×2 (the bounds are not exercised on a larger PSD family — though attainment and both guards are witnessed); the norm bound's `t⁻¹` form assumes exact arithmetic (no rounding model — out of scope); the Weyl-discharge target still needs its own additive-bound spike (the bridge and the now-proved submultiplicativity pattern are available to it).

**Next handoff:** Resolvent Step 3 — injectivity (`A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹`, one line from the Step-1 identity), completing the program; or the ungated High rows (Tikhonov Regularization, Spectral Band Projectors). Medium rows queued behind them.

## 2026-08-20T01:02:00Z — Resolvent Step 3: injectivity (program completion)

**Run:** `20260820T010200Z-run-1`  
**Session:** `ses_fe35034fbffezAyn8Uof2QyQBn`  
**Status:** in-progress  
**Milestone:** Resolvent Calculus for PSD Matrices Step 3 — the proposal's item 5, `A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹`, the recorded open next step of the Active table's top High item and the program's final step. Zero new axioms; load-bearing on Step 1's resolvent identity and invertibility theorem.

**Changes:** intent recorded in the execution plan; environment restored (pruned-oleans state recurred at run start — the recorded interpreted cache fetch re-applied, 5685 Mathlib oleans unpacked); Lean work starting in `Analysis/OperatorTheory/Resolvent.lean` and `QA/OperatorTheory/Resolvent_QA.lean`.

## 2026-08-20T03:08:46Z — Resolvent Step 3 delivered; program complete

**Run:** `20260820T010200Z-run-1`  
**Session:** `ses_fe35034fbffezAyn8Uof2QyQBn`  
**Status:** completed  
**Milestone:** Resolvent Calculus for PSD Matrices Step 3 — injectivity (`A ≠ B → (A+1)⁻¹ ≠ (B+1)⁻¹`), the recorded open next step of the Active table's top High item and the program's final step; zero new axioms, load-bearing on Step 1's resolvent identity and invertibility theorem.

**Changes:** `Analysis.OperatorTheory.Resolvent` gained the Step-3 section: `eq_of_inv_add_one_eq_inv_add_one` (the core form — equal resolvents of `+1`-invertible matrices force equal matrices, by the proposal's recorded route: the Step-1 identity collapses to `0`, and multiplying through by `A + 1` / `B + 1` cancels both invertible outer factors), `resolvent_map_injective_of_quadForm_nonneg` (the item-5 shape on quadForm-nonneg matrices), and `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg` (the certificate iff). QA `OperatorTheory/Resolvent_QA.lean` +19 (94 in file): two distinct PSD pairs instantiated (`lap2` vs `0`; `lap2` vs `mat2` with `mat2`'s PSD proved from `xᵀ(mat2)x = (x₀+x₁)² + x₀² + x₁²`), both resolvents left-inverse-pinned (`(mat2+1)⁻¹ = (1/8)!![3,−1;−1,3]` a new fixture), entry-verified distinctness (`1/3 ≠ 0`, `2/3 ≠ 3/8`), bridge lemmas from the theorem's output to the numeric facts, the iff consumed contrapositively, and the **invertibility guard**: the hypothesis-free implication refuted at `A = −1` vs `−1 + nilpotent` (both `+1` shifts singular — determinant `0` by a zero row — so both resolvents are the junk inverse `0` while the matrices differ).

**Decisive commands and outcomes:** `lake env lean` on the public module and QA module — zero errors, zero warnings; `#print axioms` on the three public and eleven QA theorems — only `propext, Classical.choice, Quot.sound`; all thirty-two QA modules batch-elaborated, zero errors (only the eight documented pre-existing section-variable warnings); **full `lake build` ✔ (2184 targets)**; `lint_axioms` (13), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (**846/13/0**).

**Verification:** program complete per the proposal's acceptance shape (all four steps, zero new axioms throughout — count stayed 13). Records updated: module/QA docstrings, scoreboard (verification rows, Step-3 interpretation bullet, provenance note), radar (axis 2 / proved-depth / QA evidence extended, scores **held** with the holds logged — completion within counted interfaces; QA count 846/32), README (846; proved list gains the injectivity), perturbation index map (3 new rows; Deferred Work updated), proposal (Step-3 delivery record, status header: program complete), `proposals/README.md` (row moved to Delivered; **Tikhonov Regularization is now the top High row**), execution plan.

**Remaining risk:** low — the step is one-consequence algebra over already-QA'd Step-1 interfaces, with the hypothesis guard refuted-on-omission. Environment note recorded in the scoreboard's provenance note: two `lake build` invocations killed at tool timeouts left the Mathlib olean dir wiped mid-replay (re-fetch restored; the final uninterrupted build passed), and a macOS case-insensitivity trap was diagnosed — creating `.lake/build/lib/lean/` shadows the toolchain's core `Lean/` tree; this repo's olean layout is `.lake/build/lib/Scaffold/...` directly.

**Next handoff:** the Active table's remaining High rows — Tikhonov Regularization (`tikhonov-shrinkage-filter.md`, no gate) and Spectral Band Projectors (`spectral-band-projectors.md`, no gate); the Medium rows stay queued behind them.

## 2026-08-20T03:39:00Z — Discharge the Weyl axiom: Step 0 spike, then retirement if positive

**Run:** `20260820T033600Z-run-1`  
**Session:** `ses_fe2c2a966ffe71pmKdtv7309zW`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` per explicit operator direction — `weyl_inequality` only. Step 0: spike the additive Weyl bound from `evals_min_max` and confirm composition with the proved `l2OpNorm_eq_max_abs_evals`; Step 1 only if positive: retire the axiom at its exact existing statement. `davis_kahan_sin_theta` and `cheeger_lower_bound` untouched. Zero new axioms; expected count 13 → 12.

**Changes:** intent recorded in the execution plan; environment verified healthy at run start (5387 Mathlib oleans present; no cache fetch needed); Lean spike starting in a scratch file against the delivered Courant–Fischer engine.

## 2026-08-20T04:12:00Z — Weyl axiom discharged: proved at its unchanged statement

**Run:** `20260820T033600Z-run-1`  
**Session:** `ses_fe2c2a966ffe71pmKdtv7309zW`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md`, Weyl target only (explicit operator direction). Step 0's additive-bound spike returned a decisive positive; Step 1 retired `weyl_inequality` from admitted axiom to proved theorem at the unchanged name, hypotheses, and conclusion. Explicit axioms **13 → 12**. `davis_kahan_sin_theta` and `cheeger_lower_bound` untouched.

**Changes:** `GraphTheory.Spectral` gained the bottom-Rayleigh-domination mirror `evals_first_mul_dotProduct_le_quadForm` (`λ_min • (x ⬝ᵥ x) ≤ xᵀMx`, the missing lower half of the Rayleigh sandwich). `Perturbation.Weyl` now contains no axiom: the public additive bounds `weyl_additive_upper`/`weyl_additive_lower` (`λᵢ(A) + λ₁(E) ≤ λᵢ(A+E) ≤ λᵢ(A) + λₙ(E)`, proved from the Courant–Fischer engine's two witness forms — upper: the witness subspace for `A` exhibited as a member of the competitor set defining `λᵢ(A+E)` through `evals_min_max`; lower: the competitor direction for `A` run inside the witness subspace for `A+E`), composed into the retired `theorem weyl_inequality` through the proved `l2OpNorm_eq_max_abs_evals` bridge. `spectral_gap_stability` unchanged and now fully hard crust. QA `Weyl_QA.lean` 4 → 18 declarations: nonzero fixture `A = E = !![2,1;1,2]` with both spectra pinned independently (trace/det/sortedness) and `‖E‖ = 3` via the bridge — bound attained exactly at the top index (`|6−3| = 3`), strict at the bottom (`1 < 3`, the proposal's required non-vacuity witness), additive bounds instantiated at both indices, and the window-endpoint guard (`λ₁(E)` for `λₙ(E)` refuted: `6 ≤ 4` false).

**Decisive commands and outcomes:** `lake env lean` on both changed public modules and the QA module — zero errors, zero warnings (oleans produced directly); `#print axioms`: `weyl_inequality`, both additive bounds, `spectral_gap_stability`, and all nine QA theorems read only `propext, Classical.choice, Quot.sound`; derived consumers verified — `davisKahanTwoPoint` now depends on `davis_kahan_sin_theta` only, `eventStreamProjectorDrift` on two axioms instead of three; all thirty-two QA modules batch-elaborated, zero errors; **full `lake build` ✔ twice** (2184 targets; once after the Lean edits, once after the `ProjectorDrift` docstring updates); `lint_axioms` (**12**), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (**860/12/0**).

**Verification:** the Step-0 spike ran first in a scratch file (`wip/weyl_spike.lean`, ignored) and confirmed the proposal's caution — the additive bound is *not* free from the norm bridge (it consumes both witness directions plus both domination bounds, the bottom one newly added) — before any module edit; the cost estimate (~120 lines) was recorded in the proposal, and the spike transferred verbatim. The retirement is at the exact axiom statement, verified by the unchanged downstream code re-linking against the theorem.

**Remaining risk:** low — the proof is the same Courant–Fischer engine shape as the delivered interlacing retirement, with QA pinning both perturbed spectra and the norm independently of the theorem; the derived layer's remaining conditionality (Davis–Kahan, Matrix Azuma) is unchanged and honestly labeled. Davis–Kahan and Cheeger-hard remain unsurveyed — this run's positive outcome does not transfer to them (the proposal's own ranking).

**Next handoff:** the Active table's two ungated High rows (Tikhonov Regularization; Spectral Band Projectors), or the Davis–Kahan Step 0 survey on this proposal's track.

## 2026-08-20T05:11:00Z — Tikhonov regularization in the Laplacian eigenbasis

**Run:** `20260820T051000Z-run-1`  
**Session:** `ses_fe26f8e52ffesMKokGJkYgb5OS`  
**Status:** in-progress  
**Milestone:** Deliver `proposals/tikhonov-shrinkage-filter.md` (the Active priority table's top High row, unblocked, no gate) as pure hard crust in a new `GraphTheory.Tikhonov`: the eigenbasis-defined minimizer, its closed-form eigencoefficient identity, minimality/uniqueness, the shrinkage-factor layer, and the not-a-projection distinction — zero new axioms (12 unchanged). Definition route decided per the proposal's standing rule: the explicit eigenbasis formula over `Classical.choice` strict convexity. Step-3 deviation identified in advance for honest recording: the proposal's "never exactly 1" fails at `λ = 0` (kernel factor is exactly 1 — that is mean preservation); the corrected statements will be delivered instead.

**Changes:** intent recorded in the execution plan; the pruned Mathlib-oleans state recurred at run start and the recorded interpreted cache fetch is running in the background; Lean work to follow in `Scaffold/Mathlib/GraphTheory/Tikhonov.lean` and `Scaffold/QA/SpectralGraph/Tikhonov_QA.lean`.

## 2026-08-20T09:02:00Z — Tikhonov regularization delivered; program complete in one run

**Run:** `20260820T051000Z-run-1`  
**Session:** `ses_fe26f8e52ffesMKokGJkYgb5OS`  
**Status:** completed  
**Milestone:** `proposals/tikhonov-shrinkage-filter.md` (the Active priority table's top High row), all three build steps delivered in one run as pure hard crust — zero new axioms (12 unchanged; `#print axioms` on all 18 public theorems reads only `propext, Classical.choice, Quot.sound`).

**Changes:** new public module `GraphTheory.Tikhonov` + QA `SpectralGraph/Tikhonov_QA.lean` (+30 declarations, 890 total). Definition route decided per the standing rule: the minimizer **defined by the eigenbasis formula** (not `Classical.choice` strict convexity), so the eigencoefficient identity is hypothesis-free orthonormality (via a generic reusable filter workhorse `dotProduct_eigvecOf_filter`), the **normal equation holds both ways** (`(L+π•1) *ᵥ x* = π•y` plus the converse characterization — the QA-pinning interface), and minimality/uniqueness both fall out of the single strict-convexity decomposition `obj(x)−obj(x*) = ∑_k (1+λ_k/π)(d_k−d*_k)²`. Two recorded statement-shape corrections to the proposal's Step 3: the attenuation factor is **exactly 1 at λ = 0** (the kernel mode passes through untouched — that *is* mean preservation, `sum_tikhonovMinimizer_eq_sum`, needing symmetry and `π ≠ 0` only), and "not a projection" is a theorem (idempotence failure `T(T v) ≠ T v`, with the sketch's nonnegativity hypothesis found unnecessary and deleted). QA on `K₂`: minimizer pinned against a **hand-solved 2×2 system** through the converse characterization (spectral construction and Gaussian elimination independently meet at `![2/3,1/3]`), objective pinned exactly (`1/3` vs `1`), exact shrinkage at the pinned spectrum `{0,2}` (factors `1`, `1/3`), `T² ≠ T` numerically, mean preservation twice, and the `hπ` guard refuted-on-omission at `π = 0`. Records: scoreboard (890/12/0 + rows), radar (subject axis 2 re-scored **3.5 → 4.0** — the axis's first constructed application-facing operator family; QA axis held at 4.0 with the hold logged), README (890, proved list), SGT index map (new section, 18 rows), proposal (DELIVERED + delivery record with both deviations), `proposals/README.md` (row moved to Delivered; **Spectral Band Projectors is now the top High row**), umbrella, execution plan.

**Decisive commands and outcomes:** `lake env lean` on the public module and QA — zero errors, zero warnings; `#print axioms` on 18 public + 14 QA headline theorems — three standard axioms only; **all thirty-three QA modules batch-elaborated, zero errors** (only the documented pre-existing section-variable warnings in untouched modules); **full `lake build` ✔ (2185 targets, "Build completed successfully")**; `lint_axioms` (12), `check_citations`, `check_markdown_links` pass; scoreboard regeneration idempotent (890/12/0). Environment: the pruned-oleans state recurred at run start; the recorded interpreted cache fetch restored 5387 before elaboration. Operational note recorded in the scoreboard: one `lake build` invocation was killed at its tool timeout mid-replay (the known hazard; Mathlib oleans survived this time — no re-fetch needed) and the build completed on a re-run executed **detached from the tool timeout** (log file + poll), now recorded as the recovery procedure alongside direct `lake env lean`.

**Verification:** every changed module elaborated directly with zero errors/warnings; axiom surface unchanged (12); no `sorry`/`admit` anywhere under `Scaffold/`; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional.

**Remaining risk:** low — the module is eigenbasis algebra over already-QA'd center interfaces, with the minimizer cross-checked against hand computation; `tikhonovMinimizer_eigvecOf` is not numerically instantiated in QA (`eigvecOf` entries are not kernel-computable; its content is covered transitively by the two normal-equation pins) and the Shuman et al. citation remains unverified and out of committed docstrings, as the proposal requires.

**Next handoff:** the Active table's remaining High row — **Spectral Band Projectors** (`spectral-band-projectors.md`, no gate: the two-sided band as the difference of two existing `spectralProjector` calls); the Medium rows stay queued behind it.

## 2026-08-21T23:08:00Z — Davis–Kahan Step 1, component 2: the Duhamel/FTC assembly

**Run:** `20260821T230647Z-run-1`  
**Session:** `ses_fd974e0c2ffef31j2LiAyA9JZx`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Davis–Kahan Step 1, component 2 — the Duhamel/FTC assembly consuming the delivered equal-rank identity plus the spike-verified semigroup primitives, to retire `davis_kahan_sin_theta` at its exact existing statement (explicit axioms 11 → 10; `davisKahanTwoPoint` becomes hard crust, `eventStreamProjectorDrift` conditional on `matrix_azuma_hoeffding` alone). Pre-edit route decision recorded in the execution plan, including the new tie-handling case split (both threshold-tie cases collapse through the proved Weyl bound to `δ ≤ ‖E‖` + `‖P−Q‖ ≤ 1`; Duhamel only needed in the no-tie case where component 1's rank equality holds).

**Changes:** intent recorded in the execution plan and here; environment verified healthy at run start (5382 Mathlib oleans present). Lean work to follow in a new `Analysis/OperatorTheory/Perturbation/Duhamel.lean`, then the `DavisKahan.lean` retirement rewrite and `DavisKahan_QA.lean` extension.

## 2026-08-22T03:17:00Z — Davis–Kahan retired: the Duhamel/FTC assembly delivered; the perturbation-bridge trust surface is empty

**Run:** `20260821T230647Z-run-1`  
**Session:** `ses_fd974e0c2ffef31j2LiAyA9JZx`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Davis–Kahan Step 1, component 2 — the Duhamel/FTC assembly — delivered as the milestone's dedicated run, completing the Davis–Kahan target: `davis_kahan_sin_theta` retired from admitted axiom to proved theorem at the unchanged name, hypotheses, and conclusion. Explicit axioms **11 → 10**; `davisKahanTwoPoint` is now fully hard crust; `eventStreamProjectorDrift` is conditional on `matrix_azuma_hoeffding` alone (both verified by `#print axioms`).

**Changes:** the new public module `Analysis/OperatorTheory/Perturbation/Duhamel.lean` (~900 lines, zero new axioms): the spike's heat-semigroup layer transferred (`heatApply` + expansion/adjoint, Parseval damping, eigenaction, differentiability, and the new `t = 0` eigenbasis-expansion identity `heatApply_zero`), the sorted-spectrum step `evals_succ_le_of_lt` (the interior companion of the two extreme pins), the projector coefficient filter `dotProduct_eigvecOf_spectralProjector_mulVec`, the two cluster-filtered decay bounds, the pairing (duality) norm reduction `l2OpNorm_le_of_abs_dotProduct_le` (self-application: the bound at `y := M *ᵥ x` forces `‖M x‖ ≤ c‖x‖`), the headline `l2OpNorm_one_sub_spectralProjector_mul_spectralProjector_le` (`‖(1 − Q) * P‖ ≤ ‖E‖/(b − a)` — the scalar Duhamel pairing whose derivative is exactly the integrand `−⟨e^{-t(A+E)}z_y, E e^{tA}z_x⟩` by the symmetry shuffle, FTC with the explicit exponential majorant, boundary decay at `T → ∞`), the rank layer, and the `‖P − Q‖ ≤ 1` gap endpoint. `Perturbation/DavisKahan.lean` rewritten: the `axiom` is now a `theorem` proved by the pre-edit-recorded three-way eigenvalue-tie case split — **a route discovery the survey did not need to resolve**: `initialProjector` includes whole tied eigenspaces, so ties make the two projector ranks differ and block the equal-rank identity; both tie cases collapse through the proved `weyl_additive_upper` to `δ ≤ ‖E‖` and finish via `≤ 1`, while the no-tie case consumes the delivered component 1 (`l2OpNorm_sub_eq_of_rank_eq`) and the Duhamel bound. QA `Perturbation/DavisKahan_QA.lean` 3 → 20 declarations: the strict non-vacuity witness (`dkA = diag(0,2)` perturbed by `dkE = [[0,3/4],[3/4,0]]`; both spectra and `‖dkE‖ = 3/4` pinned independently; eigenvector directions pinned from the eigen equations; both projectors pinned to literals `Q = (1/10)!![9,−3;−3,1]`, `P = diag(1,0)`; the bound instance `‖Q − P‖ ≤ 1/3` against the exact pinned distance `1/√10 < 1/3` — strict, and exercising the no-tie branch). Records: the two index files, README (10/1061, proved list, module table), architecture §12, the scoreboard (counts 1061/10/0, the lint/build/Direct rows, an interpretation bullet), radar (axis 7 re-scored **3.5 → 4.0** — the axis's first calculus-based proof technique as a new capability family, logged per protocol; axiom-minimization trend → 10; proved-depth/QA syncs), the proposal (status header, full Step-1 delivery record with the tie-case discovery, open-next-step → the Cheeger hard-direction survey), `proposals/README.md`, the umbrella import, the execution plan, and this log. Nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Duhamel.lean`, `DavisKahan.lean`, and `DavisKahan_QA.lean` — zero errors, zero warnings on each (Duhamel's headline proof under `set_option maxHeartbeats 2000000`); `#print axioms`: `davis_kahan_sin_theta`, the Duhamel headline, every QA headline — only `propext, Classical.choice, Quot.sound`; derived consumers verified — `davisKahanTwoPoint` three standard axioms only, `eventStreamProjectorDrift` + `matrix_azuma_hoeffding`; `lake build` on the two new modules ✔; **all thirty-five QA modules batch-elaborated, zero errors (BATCH-DONE fail=0)**; **full `lake build` ✔ (2227 targets, "Build completed successfully", detached log + poll)**; `lint_axioms` (no issues), `check_citations`, `check_markdown_links` pass; scoreboard regeneration reflects **1061 QA declarations / 10 explicit axioms / 0 sorries**.

**Verification:** the retirement is at the exact axiom statement (downstream code re-linked with no changes); the delivery is fully proved hard crust — nothing axiom-backed was added. The QA fixture pins every quantity by two independent routes (trace/determinant/sortedness for spectra, the eigen equations for directions, the proved bridge for the norm), so a wrong statement shape would fail its pins.

**Remaining risk:** low for what is delivered. The Cheeger hard-direction Step 0 survey is this proposal's only remaining target and is under a known-hard working assumption — the Weyl and Davis–Kahan outcomes do not transfer to it. The Duhamel bound's `hcl` side condition (every eigenvalue above `c'` is at least `b`) is supplied from `evals_succ_le_of_lt` at the retirement; other consumers with genuinely mixed clusters would need their own sortedness argument.

**Next handoff:** the Medium rows by leverage — mixing-time Step 1, Reversibility Phase A, Relative Entropy, Perron–Frobenius + directed operators (Step 0 first), the Cheeger hard-direction Step 0 survey, approximate spectral projection (Step 0 first); Fiedler Phase B still needs an operator decision.

## 2026-08-22T04:25:00Z — Mixing-time Step 1: eigenpair transfer to the walk matrix

**Run:** `20260822T042339Z-run-1`  
**Session:** `ses_fd84f61efffeGLtzSLjEXLM22W`  
**Status:** in-progress  
**Milestone:** `proposals/mixing-time-bound.md` Step 1 at its recorded open next step (top Medium row; no High rows remain) — transfer eigenpairs between the symmetric normalized Laplacian `L_sym` and the non-symmetric walk form `L_walk = 1 − D⁻¹A` through the already-proved similarity identity `√D · L_walk · (1/√D) = L_sym`, closing `Normalized.lean`'s own named residual gap and building the interface the proposal's Step 3 decay bound consumes. Zero new axioms.

**Changes:** intent + pre-edit survey recorded in the execution plan. Survey outcome: the pinned Mathlib has no general similar-matrices-share-eigenvalues interface (no `IsSimilar`, no charpoly-conjugation invariance under `Mathlib/LinearAlgebra/`), so the direct diagonal-case transfer is the route — both directions via `mulVec` algebra, eigenbasis instantiation via `IsHermitian.mulVec_eigenvectorBasis`, completeness via `eigvecOf_expansion_apply` + the invertibility shuffle. Lean work to follow in `GraphTheory/Normalized.lean` and `SpectralGraph/Normalized_QA.lean` (P₃ fixture, both-direction transfers, raw cross-checks, untransformed-vector guard).

## 2026-08-22T05:39:43Z — Mixing-time Step 1 delivered: eigenpair transfer to the walk matrix

**Run:** `20260822T042339Z-run-1`  
**Session:** `ses_fd84f61efffeGLtzSLjEXLM22W`  
**Status:** completed  
**Milestone:** `proposals/mixing-time-bound.md` Step 1 at its recorded open next step (top Medium row; no High rows remain) — the eigenpair transfer between the symmetric normalized Laplacian `L_sym` and the non-symmetric walk form through the already-proved similarity identity, delivered as pure hard crust in `GraphTheory.Normalized` (its own named residual gap), **zero new axioms** (count stays 10; `#print axioms` on all nine new public theorems reads only `propext, Classical.choice, Quot.sound`). Radar axis 5 re-scored 2.5 → 3.0 per the proposal's own gate.

**Changes:** (1) **Mandatory Mathlib survey, recorded before any edit**: no general similar-matrices-share-eigenvalues interface exists in the pin (no `IsSimilar`, no charpoly-conjugation invariance under `Mathlib/LinearAlgebra/`) — the proposal's anticipated branch, so the direct diagonal-case transfer was the route; the coverage map needed no correction (it already records the upstream absence). (2) **`GraphTheory.Normalized`** gained the eigenpair-transfer section: `walkLaplacian_mulVec_degreeInvSqrt` / `normalizedLaplacian_mulVec_degreeSqrt` (both directions, same eigenvalue, eigenvector conjugated by `1/√D`/`√D` — pure `mulVec` algebra, no characteristic polynomial, dissolving the module docstring's recorded charpoly obstruction), `walkTransitionMatrix_mulVec_degreeInvSqrt` (the `(1 − μ)` transition reflection), the eigenbasis instantiations via `IsHermitian.mulVec_eigenvectorBasis`, `walk_eigvec_expansion` (completeness of the transferred family — the diagonalizability interface Step 3 consumes, from `eigvecOf_expansion_apply` + the invertibility shuffle), `walkEvals` + `exists_eigenvector_walkTransitionMatrix_eq_walkEvals` (every transferred spectrum entry certified a genuine eigenvalue of `P` with an explicit nonzero witness), and the support lemmas `eigvecOf_ne_zero`, `degreeInvSqrt_mulVec_ne_zero`. (3) **QA** `Normalized_QA.lean` 14 → 34 declarations: P₃ hand eigenpairs verified by raw computation, transferred through the theorems, cross-checked by raw arithmetic on the conjugated vectors, both directions; the `walkEvals` existential at every index; a hand-solved spanning witness; and two shortcut guards refuted in proved form (skip-the-conjugation; unreflected eigenvalue). QA-infrastructure note recorded in the proposal: the `√(1+1)`-vs-`√2` simp atom mismatch is bridged by a pinned `1 + 1 = 2` rewrite (`path_one_add_one_QA`), reusable for future `√`-arithmetic QA on this fixture. (4) **Records**: scoreboard (both Direct rows + `lake build` row prepended, new interpretation bullet, counts 1081/10/0), radar (axis 5 evidence row rewritten + re-score 2.5 → 3.0 with the proposal-gate justification; QA axis synced 1081/35, held, both logged in the re-scoring log), README (status table, proved list, coverage snapshot date + axis-5 row), SGT index map (new Normalized transfer section, 9 rows), `docs/6_SGT_BACKLOG.md` (item 2's residual marked closed with the survey re-confirmation), the proposal (status header, full delivery record, open-next-step → Step 2 with its decide-and-record gate named), `proposals/README.md` (Medium row + progress paragraph), the execution plan, and this log. Nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Normalized.lean` and `Normalized_QA.lean` — zero errors, zero warnings (the module's only diagnostic is the pre-existing `congr 1` linter note on untouched code, identical in HEAD; the QA file reached zero warnings after restructuring the finishers to `all_goals`-style per the linter's own guidance); `#print axioms` on the nine public and seven headline QA theorems — `propext, Classical.choice, Quot.sound` only; oleans built (`lake build` on both targets); **full `lake build` ✔ (2227 targets, "Build completed successfully", executed detached from the tool timeout per the recorded procedure — only the documented pre-existing `hγ` warning in `Derived/ProjectorDrift.lean`)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1081 QA declarations / 10 explicit axioms / 0 sorries**; `Normalized_QA` 14 → 34).

**Verification:** every changed module elaborates directly with zero errors and zero new warnings and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The transfer theorems are load-bearing on the proved similarity identity and the diagonal invertibility lemmas (an error in either would make them fail to typecheck), and both QA guards witness that the conjugation and the eigenvalue reflection are not decorative. The prior run's Davis–Kahan delivery was preserved untouched (its uncommitted worktree state is intact; this run's changes are disjoint files except the shared records, which were extended not rewritten).

**Remaining risk:** low for what is delivered. The mixing-time program's hard part remains: Step 3 (the geometric decay of `‖Pᵗ δₓ − π‖`) is rated by the proposal's own calibration as at least as hard as the electrical program's solvability step, and Step 2's ℓ²-proxy scoping decision (ℓ² alone vs. TV conversion) is deliberately left as a recorded decision for the next run, not made here. The transferred expansion is stated over the non-orthogonal transferred family (coefficients carry `√D`); consumers needing orthonormal coordinates must rescale — a named residual, not a defect.

**Next handoff:** the Medium rows by leverage — **mixing-time Step 2** (the ℓ²-mixing proxy; make and record its decide-and-record scoping choice first), **Reversibility Phase A** (cheap, zero new axioms, composes existing `Stationary`/`Normalized` lemmas), **Relative Entropy**, **Perron–Frobenius + directed operators** (Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard working assumption), **approximate spectral projection** (Step 0 first). Fiedler Phase B still needs an operator decision.

## 2026-08-22T06:14:00Z — Reversibility Phase A: detailed balance for the weighted-graph walk

**Run:** `20260822T061043Z-run-1`  
**Session:** `ses_fd7ef370fffennYqCBfQGsm4In`  
**Status:** in-progress  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase A (both steps in one run per its own operating instruction) — prove detailed balance `π i * P i j = π j * P j i` for the simple random walk on a weighted undirected graph with positive degrees, in `GraphTheory.Stationary` (deg form, π/vol form, the symmetrizability matrix form, and the regular-case uniform-measure corollary), zero new axioms, no new definitions. Selected by the inner-dependency test: the higher-ranked mixing-time Step 2's ℓ²(π) proxy consumes exactly this interface, and Phase A is the cheaper strictly-inner dependency (the mixing-time proposal itself defers reversibility to this companion proposal). Closes one of radar axis 5's three named-absent items and one half of backlog item 6's gate.

**Changes:** intent recorded in the execution plan (route + QA plan + a records defect found during pre-edit reading: radar axis 5's table row and "Weakest axes" paragraph were not synced by the 2026-08-22 mixing-time re-score — repair planned alongside the Phase A radar update). Pre-edit survey findings: `transitionMatrix_symmetric` already on the shelf in `RandomWalk.lean` (the regular case's content), `vol` at `Spectral.lean:697`, no detailed-balance/reversibility machinery anywhere in the pinned Mathlib (coverage map already records the absence). Lean work to follow in `Scaffold/Mathlib/GraphTheory/Stationary.lean` and `Scaffold/QA/SpectralGraph/Stationary_QA.lean`.

## 2026-08-22T07:03:21Z — Reversibility Phase A delivered: detailed balance for the weighted-graph walk

**Run:** `20260822T061043Z-run-1`  
**Session:** `ses_fd7ef370fffennYqCBfQGsm4In`  
**Status:** completed  
**Milestone:** `proposals/reversibility-and-heat-semigroup.md` Phase A (both steps in one run per its own operating instruction) — detailed balance `π i * P i j = π j * P j i` for the simple random walk on a weighted undirected graph with positive degrees, delivered as pure hard crust in `GraphTheory.Stationary`, **zero new axioms** (count stays 10; `#print axioms` on all four new public theorems plus the new `Normalized.walkTransitionMatrix_apply` reads only `propext, Classical.choice, Quot.sound`) and **no new definitions** (the proposal's own mandate). Selected by the inner-dependency test: the higher-ranked mixing-time Step 2's ℓ²(π) proxy consumes exactly this interface. Closes one of radar axis 5's three named-absent items (reversibility) and the reversibility half of backlog item 6's gate; radar axis 5 **held at 3.0** per protocol (composed identity within the walk-operator family counted at the same day's mixing-time re-score; hold + triggers logged).

**Changes:** (1) **Pre-edit survey recorded**: no detailed-balance/reversibility machinery anywhere in the pinned Mathlib (coverage map already correct); `transitionMatrix_symmetric` already on the shelf in `RandomWalk.lean` (the regular case's content — so Phase A Step 2 was delivered as the uniform-measure corollary *composed* from it, not a re-proof). (2) **`GraphTheory.Stationary`** gained the detailed-balance section: `walk_detailed_balance` (degree-measure form, both sides exactly `A i j`), `walk_detailed_balance_measure` (the stationary-measure π-form at `π = deg/vol`, by side-condition-free division — **no volume-positivity hypothesis carried**, strictly more general than drafted), `diagonal_deg_mul_walkTransitionMatrix_isSymm` (reversibility *is* symmetrizability: `D * P` symmetric — the self-adjointness interface the mixing program consumes), `transitionMatrix_detailed_balance_uniform`. **`Normalized.lean`** gained the entry lemma `walkTransitionMatrix_apply` (`P i j = (deg A i)⁻¹ * A i j`) and its stale "Named gap (deferred)" similarity docstring was corrected to point at the delivered 2026-08-22 eigenpair transfer. Two Lean findings worth the record: bare `univ` in a statement elaborates as an auto-bound *local* arbitrary finset (not `Finset.univ`) — the explicit house form is now used; and `Finset.sum_pos'` was rendered unnecessary by the division route. (3) **QA** `Stationary_QA.lean` 12 → 26 declarations, the proposal's two prescribed witnesses: positive (P₃, every index pair through the theorems *and* raw literal arithmetic — `1 = 1` degree form, `1/4 = 1/4` π-form with `vol = 4` pinned independently, symmetrized off-diagonal entries both `1`, uniform form at the edge) and negative (the asymmetric `!![0,2;1,0]` with positive degrees: hypothesis-free balance refuted `2 ≠ 1`, symmetry hypothesis provably violated at the same pair — `hA` load-bearing). (4) **Records repaired alongside**: the radar axis-5 *table row* and "Weakest axes" paragraph, which the same day's earlier mixing-time run had left stale at score 2.5 with the closed gap still named, were synced to the recorded 3.0 state. Records updated: proposal (status header, Phase A delivery record with both statement-shape notes, open-next-step → Phase B's operator gate only), `proposals/README.md` (Phase B-only row + Delivered row + progress paragraph), scoreboard (both Direct rows prepended, new interpretation bullet, **1095/10/0**), radar (table row + weakest-axes repair, narrative hold entry), README (1095, proved list), SGT index map (Stationary section, 4 rows + entry-lemma note), backlog item 6 (reversibility half delivered), the execution plan, and this log. An unrelated operator-side worktree change — the new `proposals/prove-subgaussian-tail-bound.md` and its `proposals/README.md` row, appearing mid-run with no second agent process or session in evidence — was preserved untouched and left uncommitted, per the preserve-unrelated-changes rule. Nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Normalized.lean`, `Stationary.lean`, `Stationary_QA.lean` — zero errors; Stationary's two warnings verified pre-existing in HEAD via `git stash` round-trip; `#print axioms` on the five public and eight headline QA theorems — `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2227 targets, "Build completed successfully", detached log + poll)** — every QA module compiled as a library target; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1095 QA declarations / 10 explicit axioms / 0 sorries**; `Stationary_QA` 12 → 26). One build invocation hit the recorded trace-replay timeout mid-run and was re-executed detached per the recorded procedure; the Mathlib oleans survived (no re-fetch).

**Verification:** every changed module elaborates directly and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The balance theorems are load-bearing on the exact shapes of `walkTransitionMatrix` (`D⁻¹A`), `deg`, and `hA.apply`; the QA negative witness ties the failed identity to the violated symmetry hypothesis at the same entry pair.

**Remaining risk:** low for what is delivered. Phase B (the heat semigroup) remains gated on the operator decision the proposal itself records — an autonomous run must not start it. The mixing-time program's hard part is untouched: Step 2's ℓ²-proxy scoping decision and Step 3's decay bound (rated at least as hard as the electrical program's solvability step) remain; the delivered interface is their input, not their substitute.

**Next handoff:** the Medium rows by leverage — **mixing-time Step 2** (make and record its decide-and-record scoping choice first; the detailed-balance interface is now available to it), **Relative Entropy**, **the subgaussian tail bound** (the 2026-08-22 operator-directed addition; Step 0 first), **Perron–Frobenius + directed operators** (Step 0 first per the convention-choice gate), the **Cheeger hard-direction Step 0 survey** (known-hard), **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-22T08:20:00Z — Mixing-time Step 2: the ℓ²-mixing proxy (definitions + evolution interface)

**Run:** `20260822T081458Z-run-1`  
**Session:** `ses_fd7805c03ffeHnziia1UMh3sgq`  
**Status:** in-progress  
**Milestone:** `proposals/mixing-time-bound.md` Step 2 at its recorded open next step — the ℓ²-mixing proxy, with its decide-and-record scoping gate made first (ℓ² alone satisfies the goal, TV stays a separate further step; within ℓ², the weighted χ² form is primary because Step 3's decay bound is Parseval-exact only in the π-weighted inner product where the transferred eigenbasis is orthogonal). New `GraphTheory/Mixing.lean` (`stationaryVec`, `walkDistribution`, `walkDensity`, `chiSquareDistance` + evolution/stationarity/characterization interface, zero new axioms) + `Mixing_QA.lean`. First consumer of the Phase A detailed-balance interface. Lean work to follow.

**Changes:** intent recorded in the execution plan (scoping decision, route, QA plan). Pre-edit Mathlib survey (this run): no chi-square/total-variation/mixing-time/Markov-stationarity objects in the pin — coverage map already records the absence, no correction needed. Worktree inspected: the uncommitted 2026-08-22 Phase A + Step 1 deliveries are prior completed runs' output (terminal entries recorded), preserved untouched and left uncommitted per house rule.

## 2026-08-22T08:52:32Z — Mixing-time Step 2 delivered: the ℓ²-mixing proxy with its evolution interface

**Run:** `20260822T081458Z-run-1`  
**Session:** `ses_fd7805c03ffeHnziia1UMh3sgq`  
**Status:** completed  
**Milestone:** `proposals/mixing-time-bound.md` Step 2 at its recorded open next step — the ℓ²-mixing proxy, delivered as pure hard crust in the new `GraphTheory.Mixing` (**zero new axioms**, count stays 10; `#print axioms` on all fourteen new public theorems reads only `propext, Classical.choice, Quot.sound`). The step's own decide-and-record scoping gate was made *before any statement* (the record the proposal authorizes a run to make): (1) ℓ² alone satisfies the proposal's goal, TV conversion stays a separate further step per the proposal's own Step-4 framing; (2) within ℓ², the *weighted* χ² form `∑ (ν_t − π)²/π` is primary because Step 3's decay bound is Parseval-exact only in the π-weighted inner product where the Step-1 transferred eigenbasis is orthogonal — the plain Euclidean sketch-shape is delivered as the corollary bridge `sum_sub_sq_walkDistribution_le` instead.

**Changes:** (1) New `Scaffold/Mathlib/GraphTheory/Mixing.lean` (14 public theorems + 4 definitions): `stationaryVec` (π = deg/vol; `vol_univ_pos`, `stationaryVec_pos`, `sum_stationaryVec`, the unpacking lemma, and `walk_isStationary` composed from the proved degree-form stationarity), `walkDistribution` (`(Pᵀ)ᵗ *ᵥ δₓ`; `walkDistribution_zero`/`_succ`; `sum_walkDistribution` mass conservation load-bearing on row-stochasticity), `walkDensity` with **`walkDensity_succ`** — the density evolution `h_{t+1} = P *ᵥ h_t`, *the first consumer of the same day's Phase A detailed-balance interface* and the exact coordinate in which the transferred eigenbasis diagonalizes the mixing evolution — and `chiSquareDistance` (nonneg; `= 0 ↔ ν_t = π`; the `t = 0` value `(π x)⁻¹ − 1`, Step 3's normalization; the density-form equivalence; the plain-ℓ² bridge). Two statement-shape notes recorded in the proposal: the adjoint orientation of `walkDistribution` matches the house stationarity theorem's (`Pᵀ *ᵥ deg = deg`), and the χ² junk value at `π i = 0` is documented with every theorem carrying the positivity hypothesis that rules it out. (2) New `Scaffold/QA/SpectralGraph/Mixing_QA.lean` (33 declarations, all proved) at the P₃ fixture. (3) Umbrella import; records: proposal (status header, scoping record, full Step-2 delivery record, open-next-step → Step 3 with the consumed interfaces named), `proposals/README.md` (Medium row, progress paragraph, Delivered row), scoreboard (both Direct rows prepended, `lake build` row, interpretation bullet, lint dates; regenerated **1128/10/0**), radar (axis-5 evidence row + weakest-axes extended, **held at 3.0** per the proposal's own no-re-score-before-Step-3 gate — the mixing *statement* is Step 3's decay bound; hold logged with the QA count synced 1128/36), README (1128, proved list, module table, span list), SGT index map (new Mixing section, 17 rows + status list), backlog item 2 (Step 2 delivered; Step 3 named the remaining piece), the execution plan, and this log. The worktree's unrelated operator-side change (`proposals/prove-subgaussian-tail-bound.md` + its README row, uncommitted) preserved untouched; nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Mixing.lean` and `Mixing_QA.lean` — zero errors, zero warnings each (six elaboration rounds on the module — orientation quirks of this pin resolved: `pow_succ'` for the adjoint-power recursion, `← Finset.sum_div`/`Finset.sum_mul` orientations, `← mul_div_assoc`, the hypothesis-free `div_eq_zero_iff`, `Finset.not_mem_erase`; one real statement bug caught by the planned numeric check: the first draft of the `walkDensity_succ` termwise identity had the two matrix entries swapped, which the P₃ hand computation `P *ᵥ (4,0,0) = (0,2,0)` refutes); `#print axioms` on the fourteen public and twelve headline QA theorems — `propext, Classical.choice, Quot.sound` only; `lake build Scaffold.Mathlib.GraphTheory.Mixing` and `…Mixing_QA` ✔; **full `lake build` ✔ (2227 targets, "Build completed successfully", detached log + poll)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regeneration reflects **1128 QA declarations / 10 explicit axioms / 0 sorries** (`Mixing_QA` a new file row at 33).

**Verification:** every changed module elaborates directly with zero errors/warnings and is linked into the full default build (the umbrella now imports `GraphTheory.Mixing`); the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional. The QA pins every headline quantity through the theorems *and* by raw literal arithmetic (π, the t = 0/1/2 laws, the density evolution, both χ² routes, the plain-ℓ² bridge), and the two negative witnesses tie the load-bearing hypotheses to refuted hypothesis-free forms: the asymmetric positive-degree matrix refutes hypothesis-free stationarity at the entry where symmetry provably fails (`1/3 ≠ 2/3`, `hA` load-bearing), and the zero adjacency refutes the hypothesis-free vanishing characterization (`χ² = 0` junk beside `ν₀ ≠ π`, degree positivity load-bearing).

**Remaining risk:** low for what is delivered. Step 3 (the geometric decay bound) is the program's rated-hardest single step and remains open — the delivered interface is its input, not its substitute; the P₃ QA already pins the λ* = 1 bipartite non-decay (`χ²(1) = χ²(2) = 1`) that a correct Step-3 statement must reproduce rather than contradict, and this constraint is now recorded in the proposal's open-next-step. Phase B proposals (reversibility heat semigroup, Fiedler) still await operator decisions.

**Next handoff:** the Medium rows by leverage — **mixing-time Step 3** (the decay bound `χ² ≤ (λ*)²ᵗ · normalization`, consuming `walkDensity_succ` + `chiSquareDistance_eq_sum_smul` + `chiSquareDistance_zero` + the Step-1 transfer theorems; the matrix-power layer is its new work and may need sub-decomposition across runs), **Relative Entropy**, **the subgaussian tail bound** (Step 0 first), **Perron–Frobenius + directed operators** (Step 0 first), the **Cheeger hard-direction Step 0 survey** (known-hard), and **approximate spectral projection** (Step 0 first). Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-23T01:35:00Z — Cheeger hard-direction Step 1b: the co-area core

**Run:** `20260823T013007Z-run-1`  
**Session:** `ses_fd3c2b96dffeJA31TMVEK4VXBm`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1b at its recorded open next step (the top Medium row; no High rows) — the co-area core, the crux of retiring the last perturbation axiom: for `y` whose nonempty superlevel sets `{i : y i² > t}` are all minority-side, `2 * (φ * d * ∑ y i²) ≤ ∑ i j, A i j * |y i² − y j²|`. Zero new axioms. Consuming the Step-1a interfaces at their corrected constant budget; the spike (`wip/cheeger1b_spike.lean`) decides the pin's analysis-API route first (the `Ι = Ioc` right-endpoint indicator-drop trap vs the ae-congruence route, and whether `integral_finset_sum`/`integral_congr_ae` exist at this pin to replace the priced 30-line hand Fubini).

**Changes:** intent recorded in the execution plan and here; no Lean source touched yet. Planned next: spike, then `Cheeger.lean` (co-area section) + `Cheeger_QA.lean` (K₂ equality pin, strict C₄ witness, minority-hypothesis refutation).

## 2026-08-23T02:21:00Z — Cheeger hard-direction Step 1b delivered: the co-area core, with the priced hand Fubini found in the pin

**Run:** `20260823T013007Z-run-1`  
**Session:** `ses_fd3c2b96dffeJA31TMVEK4VXBm`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1b at its recorded open next step (the top Medium row; no High rows) — the co-area core, the crux of the last perturbation axiom's discharge — delivered as pure hard crust in `GraphTheory.Cheeger`, **zero new axioms** (count stays 10; `#print axioms` on all twelve new public theorems and seven QA headlines reads only `propext, Classical.choice, Quot.sound`). QA 1404 → 1423 (`Cheeger_QA` 59 → 78). The hard direction is now reduced to its final component: Step 1c (median + assembly) retires `cheeger_lower_bound` at the unchanged statement.

**Changes:** `GraphTheory.Cheeger` — the closed level step `indicatorLE` (`1_{t ≤ c}`) with the two layer-cake primitives (`integral_indicatorLE`: `∫₀^R 1_{t≤c} = c`; `integral_abs_indicatorLE_sub`: `∫₀^R |1_{t≤c} − 1_{t≤d}| = |c−d|`), integrability helpers, the closed-superlevel cut identity `sum_pairAbs_eq_two_boundary` (`= 2·boundary S_t`), minority conductance `boundary_ge_of_minority`, the indicator↔cardinality dictionary, the per-level bound, and the headline `coarea_core` (`2·(φ·d·∑y i²) ≤ ∑ i j, A i j·|y i² − y j²|` for any `y` whose nonempty closed superlevel sets at positive levels are minority-side). QA: the K₂ **equality** pin (both sides independently `2` — any defective constant in the chain breaks it), the strict multi-level C₄ witness (`20φ ≤ 10 < 16` via the exhaustively computed adjacent-pair conductance), the dictionary's closed-set semantics pinned at a boundary level, and the minority refutation-on-omission (`4 ≤ 0` at `![1,1]`, hypothesis provably unsatisfiable at `t = 1`). Records: the proposal (status header, a second inline dated survey correction at the Fubini note, the full Step-1b delivery record with pin-specific technique notes, open-next-step → 1c), `proposals/README.md` (Medium row + progress paragraph), the SGT index map (Cheeger section +7 rows + program note), README (1423, trust-surface paragraph), the radar (QA axis held 4.0, count synced 1404/39 → 1423/39, hold logged; the row-head count drift left by earlier syncs repaired), the scoreboard (both Direct rows, `lake build` row, lint row, interpretation bullet), the execution plan, this log.

**Decisive commands and outcomes:** `lake env lean Scaffold/Mathlib/GraphTheory/Cheeger.lean` — zero errors (only the documented pre-existing `unusedSectionVars` warning); `lake env lean Scaffold/QA/SpectralGraph/Cheeger_QA.lean` — zero errors, zero warnings; `lake build` on both targets ✔; `#print axioms` via `wip/cheeger1b_axcheck.lean` — twelve public + seven QA declarations each `propext, Classical.choice, Quot.sound` only; **full `lake build` ✔ (2250 targets, "Build completed successfully", detached)**; `lint_axioms` (10, unchanged), `check_citations`, `check_markdown_links` pass; scoreboard regenerated **1423/10/0**. Spike discipline followed: the development landed green in `wip/cheeger1b_spike.lean` first (with the API probes against the pin), then transferred.

**Verification:** every changed module elaborates directly and is linked into the full default build; the delivery is fully proved hard crust — nothing axiom-backed was added, so nothing here is conditional, and `cheeger_lower_bound` remains admitted, visible, and cited (its retirement is Step 1c's business alone). The chain is load-bearing end to end: the K₂ equality pin ties the FTC constants, the cut identity's factor 2, the conductance step's volume arithmetic, and the assembly's endpoints to independently computed values, and the refutation ties the minority guard to a refuted hypothesis-free form at a fixture satisfying every other hypothesis.

**Remaining risk:** moderate-low for what is delivered. Step 1c is rated moderate by the survey: median existence over the sorted value multiset and the `{u ≥ t} ⊆ {x > m}` inclusion (at `t > 0`) are the two genuinely new pieces, both finite-combinatorial; the constant arithmetic they must reproduce is now machine-checked at both endpoints (1a's normalization cross-checked against `λ₂(L_sym) = 2`; 1b's K₂ equality), so an assembly slip cannot hide. Pin-specific hazards for 1c recorded in the proposal (the `(0:ℝ)..R` Float lexing, the `Set.indicator_of_mem` membership-direction trap, the `IntervalIntegrable.sum` Pi-application whnf loop with its `Finset.sum_apply` route).

**Next handoff:** the Medium rows by leverage — **the Cheeger hard-direction Step 1c** (median + assembly; the final component, retiring the last perturbation axiom, explicit axioms 10 → 9) and **approximate spectral projection** (Step 0 first). The PF consumers (irreducible stationary distributions, PageRank) are unblocked as new-proposal candidates, each needing its own document per the one-step discipline. Reversibility Phase B and Fiedler Phase B still need operator decisions.

## 2026-08-23T03:25:00Z — Cheeger hard-direction Step 1c: median + assembly (the final component)

**Run:** `20260823T032137Z-run-1`  
**Session:** `ses_fd35d053bffeK4X8H9SR0loehr`  
**Status:** in-progress  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1c at its recorded open next step (the top Medium row; no High rows) — the final component: median existence, the level-set inclusions supplying `coarea_core`'s `hy`, the norm split, and the assembly into the sweep lemma `φ²/2 ≤ R(x)`, retiring `cheeger_lower_bound` at the unchanged statement (explicit axioms 10 → 9). Consumes the delivered 1a/1b interfaces at their corrected constant budget. Zero new axioms.

**Changes:** intent recorded in the execution plan (route + QA plan); no Lean source touched yet. Planned next: develop green in `wip/cheeger1c_spike.lean`, transfer to `Cheeger.lean`, QA (`Cheeger_QA.lean`), then the record sweep (proposal, proposals/README, README, radar, scoreboard, SGT index map, citation index status). The worktree's uncommitted Step-1b delivery (prior run, terminal entry recorded) is preserved untouched.

## 2026-08-23T03:48:30Z — Cheeger hard-direction Step 1c delivered: the axiom retired, the discharge program complete

**Run:** `20260823T032137Z-run-1`  
**Session:** `ses_fd35d053bffeK4X8H9SR0loehr`  
**Status:** completed  
**Milestone:** `proposals/discharge-perturbation-axioms.md` Step 1c (median + assembly, the final component) — **`cheeger_lower_bound` retired from admitted axiom to proved theorem at the unchanged name, hypotheses, and conclusion, explicit axioms 10 → 9**, the discharge program COMPLETE (Weyl 2026-08-20, Davis–Kahan 2026-08-21, Cheeger easy 2026-08-18, Cheeger hard 2026-08-23 — all proved hard crust). Pure hard crust in `GraphTheory.Cheeger`'s new Step-1c section; QA 1423 → 1449 (`Cheeger_QA` 78 → 104). Radar axis 4 re-scored 4.0 → 4.5 (both directions of the axis's central isoperimetric–spectral family now proved).

**Changes:** (1) `GraphTheory.Cheeger` — the axiom block replaced by the proved theorem at the identical statement, with a new Step-1c section: median existence `exists_median` by pure Finset arithmetic (*no sorting* — a route simplification over the survey's `Finset.sort`+`get` sketch: the at-most-half set is nonempty at a maximizing vertex, a minimal-value member works, the failure case self-refuting through the lower level set's maximizer lying in `T` below the `T`-minimum; the empty-type case separate), the level-set inclusions `{t ≤ (x−m)⁺²} ⊆ {x > m}` / `{t ≤ (m−x)⁺²} ⊆ {x < m}` at `t > 0` (supplying `coarea_core`'s `hy` in its delivered closed-set form), the per-part bound `hardDirection_perPart` (`φ²·d·∑y² ≤ E'(y)` — the 1b co-area core squared and composed with the 1a Cauchy–Schwarz core, `cheegerConstant_nonneg` for the squaring, zero-norm case by nonnegativity), the norm split `median_parts_norm`, the sweep lemma `cheeger_sweep`, and the retirement through `secondEval_variational` + `le_csInf` at the `Pi.single` witness. (2) `Cheeger_QA.lean` +26 declarations: the median forced into `[−1,1]` on the tie-heavy `![1,1,−1,−1]`, the per-part bound at the 1b K₂ equality data (`1 ≤ 2` both sides raw), the norm split's `+4m²` remainder pinned at two medians, the sweep on K₂ (`1/2 ≤ 2`, against the pinned λ₂) and C₄ at `d = 2` (`φ²/2 ≤ 1/8 < 1 = R`), and the retirement instance `1/2 ≤ λ₂ = 2` through the proved theorem. (3) Records: the proposal (status COMPLETE, Step-1c delivery record with pin-specific technique notes), `proposals/README.md` (Medium row → Delivered table; progress paragraph), the Chung source index (proved-not-axiom row), the SGT index map (+5 rows, program-complete note), README (9 axioms, 1449, both Cheeger inequalities proved), the radar (axis-4 re-score with the log; axiom-minimization trend `... → 9 → 10 → 9` with the row-head count drift from the PF admission repaired; QA sync 1449/39; downstream-reuse gap clause), the scoreboard (both Direct rows, `lake build` row, lint row, retirement bullet — **1449/9/0**), backlog item 4's Phase-B trust note, the execution plan, this log. The prior run's uncommitted Step-1b delivery preserved untouched; nothing committed.

**Decisive commands and outcomes:** `lake env lean` on `Cheeger.lean` (only the documented pre-existing `unusedSectionVars` warning) and `Cheeger_QA.lean` (zero errors, zero warnings); `lake build` on both targets ✔; `#print axioms` via `wip/cheeger1c_axcheck.lean` — the retired theorem, all ten new public theorems, all nine new QA headlines, and the two *pre-existing* axiom-consuming QA theorems (which compiled unchanged and silently shed the dependency) each read only `propext, Classical.choice, Quot.sound`; **full `lake build` ✔ (2250 targets, "Build completed successfully", detached)**; `lint_axioms` (**9**), `check_citations`, `check_markdown_links` pass; scoreboard regenerated (**1449 QA declarations / 9 explicit axioms / 0 sorries**; `Cheeger_QA` 78 → 104). Spike discipline followed: green in `wip/cheeger1c_spike.lean` first, then transferred.

**Verification:** every changed module elaborates directly and is linked into the full default build; the delivery is fully proved hard crust — the retirement removes an axiom rather than adding trust surface, so nothing new is conditional. The chain is load-bearing end to end: the tie-heavy median pin would fail on any defective counting in `exists_median`; the per-part and sweep instances are computed against independently pinned endpoint values (the 1b K₂ equality data, the pinned `λ₂(L_sym) = 2`, the raw `E' = 8`/`‖x‖² = 2` on C₄); and the retirement instance exercises the exact statement that was previously admitted.

**Remaining risk:** low for what is delivered. The proposal's program is closed; the residual Cheeger-adjacent items are the Fiedler Phase B operator decision (whose composition would now be hard crust if run) and the irregular-graph statement shape (needs a matrix square root absent from the pin). The remaining 9 admitted axioms: the concentration family (with the recorded junk-integral residual on `hoeffding_inequality`/`bernstein_inequality`/`MatrixMDS` mean hypotheses), Perron–Frobenius, and Hoeffding's lemma.

**Next handoff:** the Medium rows by leverage — **approximate spectral projection** (Step 0 first; a negative tractability finding is a valid recorded outcome). The PF consumers (irreducible stationary distributions, PageRank) are unblocked as new-proposal candidates, each needing its own document per the one-step discipline. Reversibility Phase B and Fiedler Phase B still need operator decisions.
