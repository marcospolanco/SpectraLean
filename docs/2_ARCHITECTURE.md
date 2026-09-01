# Formal Architecture and Axiom Engineering

**Status:** Canonical technical and policy specification  
**Last reviewed:** August 17, 2026

## 1. Scope and assurance

Scaffold is a mathlib-compatible Lean library that exposes selected published results as explicit axioms. The architecture makes the trust boundary visible and supports later replacement by proved upstream theorems.

Scaffold guarantees only what the artifacts establish:

- Lean compilation checks types and proofs relative to imported declarations and axioms.
- A proof that depends on an axiom is conditional on that axiom.
- QA lemmas test interface usability and selected consequences; they do not prove the axioms or certify citation fidelity.
- Citations are provenance for human review, not machine-checked evidence.

## 2. Implemented repository layers

### Layer 1: public axiom APIs

Location: `Scaffold/Mathlib/**`

This subtree mirrors Mathlib topics where practical. It contains real definitions and explicit axioms for results not yet proved locally. Public declarations should be narrow enough to replace independently.

### Layer 2: QA proofs

Location: `Scaffold/QA/**`

QA files contain fully elaborated proofs of small properties, special cases, or cross-interface consequences. They must contain no `sorry` or `admit`. A QA lemma is useful when failure would reveal an API-shape, assumption, or composability problem.

### Layer 3: derived research and retained examples

Location: `Scaffold/Derived/**`. The first two modules assemble the
persistence example end-to-end. `Scaffold/Derived/EventStream.lean`
contains the proved telescoping identity, the boundedness/event-driven
interface lemma, and the axiom-backed derived theorem `eventStreamTail`:
an Azuma tail bound on the cumulative Laplacian perturbation of a random
event-driven graph stream. `Scaffold/Derived/ProjectorDrift.lean` contains
`davisKahanTwoPoint` (Davis–Kahan in two-point form with the separation
discharged from Weyl and a spectral gap) and the axiom-backed derived
theorem `eventStreamProjectorDrift`: a high-probability bound on the
endpoint rotation of the invariant spectral subspace,
`μ{‖P_{L_m} − P_{L_0}‖ ≥ s/(γ−s)} ≤ 2 d exp(−s²/(8 m R²))`.

Both are proved from admitted axioms (`matrix_azuma_hoeffding`,
`davis_kahan_sin_theta`) plus proved steps — including, since the
2026-08-20 Weyl retirement, the *proved* `weyl_inequality` — and are
conditional on those axioms; they must not be described as foundationally
proved. Novel work may also live in a downstream repository. Derived
claims must distinguish proved Lean theorems from axiom-backed results. The
persistence package is not a roadmap goal: new derived work is selected for
its broad SGT leverage.

`Scaffold/Trusted/` currently contains explanatory material; it is not the public axiom location.

## 3. Public API contract

The public API consists of declarations reachable through `Scaffold.Mathlib.*` imports. Changes should follow these rules:

- prefer Mathlib types, predicates, and naming conventions;
- use focused modules and minimal imports;
- state all mathematical preconditions explicitly;
- preserve names and statement shapes within a compatible release line;
- avoid umbrella imports for narrow downstream use;
- document edge cases and fallback behavior for partial operations.

The matrix-first spectral graph representation uses `Matrix V V ℝ` because it composes directly with finite-dimensional linear algebra, perturbation bounds, and event updates. This does not eliminate the need for adapters to Mathlib graph structures.

## 4. Definition standards

Core mathematical objects must be real definitions, not constants chosen merely to make a file elaborate. In particular:

- do not define a spectrum, norm, quotient, or projector as an unconditional `0` placeholder;
- do not use `True` as the type of an intended mathematical result;
- guard division by zero and state invertibility or positivity requirements;
- preserve symmetry, diagonal, and sign invariants by construction when feasible;
- document deliberately noncomputable definitions and their mathematical meaning.

Legacy declarations that violate these rules are migration debt and must be reported in the QA pillar. The policy is a target enforced on new changes, not a claim that all current source already complies.

## 5. Axiom admission policy

An axiom is admissible only when all of the following hold:

1. It unlocks a concrete downstream use case.
2. Its conclusion is meaningful and composable.
3. Its assumptions include dimensions, symmetry, positivity, independence, measurability, boundedness, or spectral gaps as applicable — **and its degenerate corners have actually been checked, not assumed benign.** Every real defect found in an admitted axiom so far has come from a boundary the source paper's prose leaves implicit rather than from the main inequality being wrong. Before admission, check the axiom's exact hypothesis set against each hazard class evidence has so far produced:
   - **Empty or degenerate-cardinality instantiation** (`Fintype.card V = 0`, `n = 0`, an empty index type): does every hypothesis remain simultaneously satisfiable while a conclusion-side prefactor or denominator collapses to something the hypotheses no longer justify? (`matrix_hoeffding`/`matrix_bernstein`/`matrix_azuma_hoeffding` were genuinely inconsistent — `1 ≤ 0` — at exactly this corner until repaired 2026-08-28; the fix was an explicit `[Nonempty V]` guard.)
   - **Unconstrained measure mass** (a `Measure` argument with no `IsProbabilityMeasure` or finiteness constraint): can the measure's total mass be scaled to make a hypothesis vacuous while the conclusion is a bound on that same measure? (`subgaussian_tail_bound`'s original shape broke this way via `Real.sInf_empty` on a mass-3 point measure.)
   - **Junk-valued integrals** (`MeasureTheory.integral_undef`: a Bochner integral over a non-integrable or non-measurable function silently evaluates to `0`): does every integral appearing in a hypothesis have integrability forced by the *other* hypotheses (boundedness plus measurability plus finite measure), or can it default to `0` and make the hypothesis vacuously true? (This broke the same subgaussian axiom a second, independent way, and was the exact mechanism `hoeffding_lemma` was later found to still carry — missing both the measure and measurability guard — before its 2026-08-28 repair.)
   - **A wrong constant on an otherwise-correct hypothesis shape**: does the source's exact classical constant appear in the Lean statement, or was one interpolated/assumed? (`hoeffding_lemma`'s repair also corrected `a → √6·a` — a real derivation error, not a hypothesis gap, caught only because a genuinely non-junk refutation fixture was built and checked, not because the hypothesis shape looked wrong on inspection.)
   - **Strictness mismatches** (`≤` vs `<`, a boundary value like `t = 0` or `K = 0` treated as excluded when the source allows it or vice versa).

   This list grows as new hazard classes are found; treat it as a floor, not a ceiling, and update it when a future audit or repair discovers a mechanism not already named here. The signature-visible half of the first two classes is checked mechanically: `scripts/lint_axioms.py`'s degenerate-corner guard check (added 2026-08-28, `proposals/lint-axiom-degenerate-corner-guards.md`) flags every axiom with a `Fintype`-carried index type or a `Measure` argument lacking a visible guard, with an allowlist that records why each flagged axiom is accepted — run it before an axiom lands and make the allowlist decision once, deliberately, at admission time. The check is a prompt to look, not a claim the axiom is wrong; it does not replace the adversarial-fixture Step 0.

   Two further audit checks (both 2026-08-30,
   `proposals/axiom-audit-tooling.md`) flank an admitted axiom's whole
   lifecycle. `scripts/check_refutation_independence.py` verifies that
   every QA declaration tagged `-- @refutes: <axiom>` does not, in its
   proof term, depend on that axiom — a refutation cannot consume what
   it refutes — so the adversarial fixtures this policy demands stay
   honest evidence; tags name only currently admitted axioms and come
   off with retirement. `scripts/lint_axioms.py`'s replacement-path
   documentation check requires every axiom's docstring to carry a
   labeled `Replacement path:` note — the theorem, engine, or Mathlib
   gap that would retire it, or an explicit no-known-route statement —
   so the retirement plan §9 assumes is recorded on the axiom itself.
4. Its documentation cites an authoritative source precisely enough to locate the result.
5. The documentation explains any difference between the source statement and the Lean statement.
6. The axiom has a small blast radius and does not bundle unrelated facts.
7. Relevant source and topic indices are updated.
8. At least one QA obligation is identified, or the review explains why no useful thin QA exists.

Use `axiom` for an intentional trust boundary. Do not disguise that boundary with `theorem := by sorry` in public modules.

## 6. QA contract

A QA proof must:

- compile with no `sorry` or `admit`;
- exercise a real definition or public axiom;
- check a mathematically meaningful property;
- remain small enough to diagnose interface failures;
- avoid claiming that a trivial consequence validates the source theorem.

Proof length is a heuristic, not a correctness criterion. A longer elementary proof may belong in QA when Lean requires bookkeeping; a one-line tautology does not become valuable because it is short.

Useful categories include structural invariants, nonnegativity, zero-update cases, dimensional compatibility, edge-case behavior, and cross-axiom coherence.

## 7. Quality review

Reviewers assess five dimensions:

| Dimension | Questions |
| --- | --- |
| Definitions | Are core objects real, guarded, and mathematically recognizable? |
| Statement shape | Are assumptions explicit and conclusions usable? |
| API design | Is naming consistent, scope narrow, and organization coherent? |
| Mathlib compatibility | Are standard types and predicates reused where practical? |
| Documentation | Are limitations, citations, and modeling choices clear? |

Event-driven modules additionally review whether updates preserve required invariants and whether perturbation bounds refer to the same representation and norm as the update model.

## 8. Citation and index policy

Every public axiom should include author, title, theorem or section locator, and edition/page where relevant. Files under `index/sources/` map references to Lean identifiers; files under `index/map/` map subject areas to declarations. Large quotations or copyrighted source text do not belong in the repository.

The citation checker is a hygiene tool. Human mathematical review remains necessary.

## 9. Upstream replacement lifecycle

When Mathlib or another accepted dependency provides a proved replacement:

1. Compare assumptions, conclusion, conventions, and namespace—not just the theorem name.
2. Add an adapter theorem if the shapes differ but are equivalent.
3. Run the affected QA and downstream checks against the replacement.
4. Deprecate the Scaffold declaration with a migration note.
5. Retain compatibility for the documented deprecation window unless the declaration is unsound or unsafe.
6. Remove the axiom and update citation/topic indices in the next permitted release.

An emergency removal is appropriate for a materially false statement, an inconsistent assumption set, or a declaration that creates unacceptable trust exposure. Release notes must identify the impact. Every instance of this — every axiom or theorem statement actually found false or inconsistent, not merely unproved — is recorded in [Errata](9_ERRATA.md); an emergency removal that never gets an entry there defeats the purpose of keeping the list.

## 10. Toolchain and verification

The repository pins Lean and Mathlib in `lean-toolchain` and `lakefile.lean`. The default build, direct module checks, QA placeholder scan, axiom lint, citation check, Markdown link check, and build-completeness reconciliation measure different properties and must be reported separately.

A full `lake build` exit status alone does not certify every on-disk source: the default target builds the umbrella's import closure, so a file merely present on disk (an interrupted run's fresh draft) is silently outside the checked set. `scripts/check_build_completeness.py` runs after every full build and fails nonzero when any `Scaffold/**/*.lean` source has a missing or mtime-stale `.olean` artifact; its docstring records the remediation calibrated against Lake's content-hash up-to-date semantics.

Documentation freshness has the same shape: the transit map's two hand-maintained data tables (`scripts/generate_scaffold_map_svg.py` and `docs/scaffold_map.html`) once drifted from ground truth for days while the pre-commit hook re-rendered the SVG on every commit. `scripts/check_scaffold_map_freshness.py` reconciles both tables against each other, against the scoreboard's generated numbers, and against each station's cited proposal's own `**Status:**` line; the hook runs it report-only and the verification ladder is the blocking enforcement.

Axiom signatures get the same structural treatment: `scripts/lint_axioms.py`'s degenerate-corner guard check (2026-08-28, `proposals/lint-axiom-degenerate-corner-guards.md`) flags every `Scaffold/Mathlib` axiom whose effective signature carries a `Fintype`-carried index type or a `Measure` argument with no visible guard, unless a per-axiom allowlist entry in the script records why the corner is accepted. Both 2026-08-28 axiom defects had exactly this gap visible in the signature alone; the check runs on every `lint_axioms.py` invocation in the ladder, and new admissions settle their allowlist entry when they land.

Axiom evidence and public boundaries get structural treatment too (both 2026-08-30, `proposals/axiom-audit-tooling.md`): `scripts/check_refutation_independence.py` checks that every QA declaration tagged `-- @refutes: <axiom>` has a proof term free of that axiom — the refutation-independence discipline every repair record had verified by hand — and `scripts/check_public_reachability.py` walks the import graph from the umbrella `Scaffold.lean` and fails if any module under `wip/` (the only non-public Lean directory, confirmed by that proposal's Step-0 survey) is reachable from the public API. The independence check runs `#print axioms` through a generated `lake env lean` file, so it presumes built oleans; the reachability check is purely static.

Backlog freshness gets the same clock-based treatment as the transit map, but weaker: `docs/6_SGT_BACKLOG.md` is free prose, not a structured table, so a content checker isn't cheaply buildable the way the map's station-to-proposal cross-check is. `scripts/check_backlog_freshness.py` (2026-09-01, found stale after a two-week gap during which dozens of completed deliveries landed while several backlog items still read "conditional" or "entirely absent") instead fails if the backlog's "Last reviewed" date has fallen more than seven days behind the latest `docs/AGENT_ACTIVITY.md` entry. It certifies that someone has looked recently, not that every claim is still accurate — reconciling the prose itself stays a human or steward task, triggered by this check rather than performed by it.

The generated [QA scoreboard](5_QA_SCOREBOARD.md) is the authority for current counts and recorded check results.

## 11. Contribution workflow

A change to the public axiom layer should include:

- the SGT obligation or consumer it unlocks and why it outranks nearer load-bearing work;
- the declaration and documentation;
- citation and topic-index updates;
- QA coverage or a stated reason it is not applicable;
- a successful check of the changed module and its consumers;
- a compatibility note when changing an existing declaration.

Community process is defined by `governance/CONTRIBUTING.md`, `MAINTAINERS.md`, and `RELEASES.md`.

## 12. Known architectural debt

- The probability concentration subtree was repaired on 2026-08-17 and is
  certified through the umbrella; matrix Azuma is expressed through the
  elementary `MatrixMDS` structure (comap past σ-algebras plus set-integral
  conditional means) because the pinned Mathlib snapshot has no
  filtration/conditional-expectation API. If a later Mathlib provides one,
  restating `MatrixMDS` through `Filtration`/`Adapted` is the intended
  upstream alignment. `subgaussian_tail_bound` was retired from axiom to
  proved theorem on 2026-08-22 as a correctness repair
  (`proposals/prove-subgaussian-tail-bound.md`): the old
  `subgaussianNorm ≤ K`-mediated shape was materially false through two
  junk mechanisms (`Real.sInf_empty` vacuity; `integral_undef` making the
  MGF integral junk-zero, hence the defining set full, for heavy tails),
  and the theorem now states the moment integrably. A recorded residual:
  the same junk-integral surface touches the `MatrixMDS` set-integrals —
  their own future Step 0 must check it (the scalar side was audited
  safe on 2026-08-28 with proved integrability discharges; see
  `proposals/audit-scalar-concentration-integrability-hazard.md`; the
  `hoeffding_inequality`/`hoeffding_empirical` half of the scalar
  residual was fully discharged by the 2026-08-30 retirement — both are
  now proved theorems whose engine routes every mean hypothesis through
  `integrable_of_bounded_measurable` before integrating,
  `proposals/prove-hoeffding-inequality-mgf.md` — and the
  `bernstein_inequality`/`bernstein_bounded_variance` half was
  discharged by the 2026-08-30 repair-and-retirement (Errata §8,
  `proposals/repair-and-retire-bernstein-pair.md`): the admitted forms'
  *uncentered* bound hypothesis materially understated the Bennett
  price, both were repaired to the source-faithful centered bound and
  proved by the local Bennett MGF engine with every hypothesis-side
  integral discharged honestly — the scalar junk-integral residual is
  now fully worked).
  The matrix side's own Step 0 check (2026-08-28,
  `proposals/matrix-hoeffding-spectral-gap-estimation.md`) found a
  different, larger defect: **all three matrix concentration axioms
  (`matrix_hoeffding`, `matrix_bernstein`, `matrix_azuma_hoeffding`) were
  inconsistent at the degenerate dimension** — at `Fintype.card V = 0`,
  `t = 0` each instantiates to the provable `1 ≤ 0` (the tail event is
  all of `Ω`; the `2 · card V` prefactor collapses the bound to `0`).
  All three were repaired in place with the `[Nonempty V]` guard the
  cited Tropp statements carry implicitly, with hypothesis-form
  refutation records in `Matrix_QA.lean`; `matrix_hoeffding` carries no
  integral clauses at all, so the junk-integral surface does not reach
  it — the defect there was purely the missing nondegeneracy guard.
  A third defect in `matrix_hoeffding` alone was found and repaired
  2026-08-30 (Errata §9, `proposals/repair-matrix-hoeffding-centering.md`):
  the statement carried **no centering clause** (its docstring even claimed
  the source needs none), while the sibling `matrix_bernstein` has carried
  `h_mean` since admission — the deterministic constant-ones family
  satisfies every other hypothesis genuinely (self-domination at
  equality) and refutes the tail at `V = Fin 1`, `n = 2`, `t = 2`
  (`1 ≤ 2·exp(−1) < 1`), refuted in hypothesis form with an exclusion
  fence in `Matrix_QA.lean`. Repaired in place with
  `h_mean : ∀ i, ∫ ω, X i ω ∂μ = 0`; the window family's design
  discharges it through the proved
  `integral_perturbSummand_eq_zero`, and every conditional consumer's
  public statement is unchanged (only the generic passthrough
  `matrix_hoeffding_quadForm` gains the matching hypothesis). The
  2026-08-30 scalar Bernstein audit had checked `matrix_bernstein` safe
  on exactly this axis and never run it on the sibling — the §5
  hazard-class list is a floor, and each audit must cover every axiom
  its class touches.
  The `MatrixMDS` half of the residual was then run as its own Step 0
  on 2026-08-29 (`proposals/audit-matrix-azuma-mds-measurability-hazard.md`,
  Errata §7) and found real: the structure's `adapted` field was
  content-free (`mdsFiltration` is the comap σ-algebra the `X j`
  generate themselves) and nothing forced ambient strong measurability,
  so the `cond_mean_zero` set-integrals were junk zeros and
  `matrix_azuma_hoeffding` was satisfiable by a bounded non-measurable
  drift (refuted in hypothesis form at a 33-point caterpillar fixture).
  Repaired in place — `adapted` replaced by the honest
  `measurable : ∀ k, StronglyMeasurable (X k)` field, both Derived
  consumers threaded to ambient `h_meas`, with the exclusion fence
  proving the repaired field rejects the refuting fixture — leaving
  the scalar-side residual sentence above as the only remaining open
  half, already audited safe.
- Spectral-projector idempotence and eigenbasis orthonormality/completeness
  behind `spectralProjector` are proved locally
  (`eigvecOf_inner`, `eigvecOf_complete`, `spectralProjector_idempotent`,
  `spectralProjector_eq_zero`, `spectralProjector_eq_one`), from the
  Mathlib spectral-theorem API; the admitted perturbation interfaces
  remain the trust boundary for the perturbation inequalities themselves.
- The persistence example is assembled end-to-end in the derived layer
  (`eventStreamTail`, `davisKahanTwoPoint`, `eventStreamProjectorDrift`).
  `davisKahanTwoPoint` is fully hard crust since 2026-08-21
  (`davis_kahan_sin_theta` proved that day — retired from axiom by the
  Duhamel/exponential-integral route of
  `proposals/discharge-perturbation-axioms.md`: the equal-rank projector
  identity `Perturbation.ProjectionGap` plus the Duhamel bound
  `Perturbation.Duhamel`, with eigenvalue-tie cases collapsed through the
  proved Weyl additive bound); `eventStreamProjectorDrift` is conditional
  on `matrix_azuma_hoeffding` alone (`weyl_inequality` proved since
  2026-08-20).
  The per-step `spectral_persistence` axiom was deprecated on 2026-08-17
  (zero non-QA consumers; the derived chain covers the motivating use)
  and removed on 2026-08-20 at the end of its compatibility window.
- Page-level locators remain pending for Horn–Johnson (section-level
  recorded) and Chung (chapter-level recorded); the 2026-08-17 citation
  audit corrected an inaccurate provenance note in the Chung index and
  confirmed no in-repository page numbers were ever recorded. Locator
  numbers are to be confirmed against physical or publisher copies, not
  invented. `weyl_inequality` is proved (retired from axiom on 2026-08-20
  — the additive window from the Courant–Fischer engine composed with the
  `l2OpNorm_eq_max_abs_evals` bridge), so `spectral_gap_stability` is
  fully hard crust; `davis_kahan_sin_theta` states its separation
  hypothesis in the single-pair two-cluster form of the cited
  Yu–Wang–Samworth Theorem 1 (operator-norm variant, bottom cluster; the
  locator was corrected from "Theorem 2" by the 2026-08-21 Step-0 survey —
  the paper's Theorem 2 is a population-gap constant-2 result).
- There is no executable target; the former `scaffold` executable referenced a missing `Main.lean` and was removed from the default build until a real driver exists.

These are tracked as facts, not hidden by the target architecture.

## Source provenance

This document consolidates the archived [full project specification](../research/archive/governance/PROJECT_SPEC.md) and former policies for [design](../research/archive/governance/SCAFFOLD_DESIGN.md), [axioms](../research/archive/governance/AXIOM_POLICY.md), [QA](../research/archive/governance/QA_POLICY.md), [deprecation](../research/archive/governance/DEPRECATION_POLICY.md), and [quality](../research/archive/governance/QUALITY_CRITERIA.md).
