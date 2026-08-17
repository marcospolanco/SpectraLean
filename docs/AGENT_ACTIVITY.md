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
