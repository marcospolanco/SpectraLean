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
