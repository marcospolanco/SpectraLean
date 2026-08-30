# Proposal: Axiom Stress Testing and Quarantine

**Status:** Proposed governance extension. This document authorizes no Lean
changes, tooling changes, axiom disposition changes, or publication on its
own — see **Decision needed** below.

**Provenance:** Originally drafted as a standalone `governance/` policy
document (2026-08-30). Reviewed by the commit steward and revised into a
proposal here: most of its vocabulary is sound, but two sections overstated
what the repository currently does, and it did not yet account for two
mechanisms that already cover part of the same ground — `docs/9_ERRATA.md`
and `docs/arch/commit-steward-protocol.md`, both also written 2026-08-30.

**Scope:** Public Scaffold, downstream experiments, and autonomous
formalization runs.

## Executive decision

Scaffold may use a **mushy center** of explicit, cited axioms while it grows a
proved **hard crust** around them. This policy does not require every frontier
result to be proved before it is useful.

It does require a sharper distinction:

- an **unproved but source-faithful axiom** is an acceptable temporary trust
  boundary;
- an **under-specified or known-false Lean statement** is a quarantined
  experiment, not an acceptable public axiom;
- a compiled downstream theorem is evidence about the deduction relative to
  its assumptions, not evidence that the assumptions are true.

The purpose of stress testing is to put independently checked weight on an
axiom's exact interface so that missing hypotheses, wrong signs, degenerate
cases, and incompatible definitions surface before promotion.

## 1. Critique of the current governance

The existing contribution and architecture documents already establish useful
foundations:

- explicit cited axioms are allowed;
- public axioms require meaningful statements, documentation, indices, and
  QA;
- QA may not use `sorry` or `admit`;
- derived work may depend conditionally on the axiom layer;
- center-out and load-bearing work are preferred.

Those rules are necessary but do not fully specify the autonomous,
falsification-oriented workflow. In particular, they do not currently define:

1. a status for a statement known to have a countermodel;
2. a required negative-witness or edge-case attack;
3. the difference between an axiom-free refutation and QA that merely imports
   the axiom under test;
4. machine-only acceptance gates when no maintainer reviews every definition;
5. the response when downstream pressure exposes a bad interface; or
6. the transition from an ignored WIP experiment to a public API.

This document supplies those missing operational rules. It complements
[`docs/1_STRATEGY.md`](../docs/1_STRATEGY.md) and
[`docs/2_ARCHITECTURE.md`](../docs/2_ARCHITECTURE.md); it does not replace
their trust model.

**What has since been built that overlaps this proposal.** Since this
document was first drafted, two lighter mechanisms landed that already cover
part of items 1, 4, and 5:

- [`docs/9_ERRATA.md`](../docs/9_ERRATA.md) is the disposition record for
  axioms found materially false after publication (entries 6–9 so far: a
  pairwise-independence defect, a self-referential measurability defect, and
  two uncentered-bound defects). It gives every such finding a status
  (open/closed), a commit reference, and a "how this is maintained" rule —
  independently of whether this proposal's `quarantined` vocabulary is
  adopted.
- [`docs/arch/commit-steward-protocol.md`](../docs/arch/commit-steward-protocol.md)
  is the human verification gate that currently substitutes for this
  proposal's §4 "machine-only" gates: independent re-derivation of
  `#print axioms`, the sorry/admit sweep, and the build-completeness check
  are all already required there, run by a human-in-the-loop rather than
  fully autonomously.

Neither of these adopts this proposal's vocabulary or 6-stage lifecycle.
Both independently solve a piece of the problem this proposal names. See
**Decision needed**.

## 2. Vocabulary

### Mushy center

The smallest set of explicit assumptions needed to state and connect a
research result whose proof is not yet available in Lean. A mushy-center
declaration must still have a precise type, source provenance, intended use,
and replacement path.

### Hard crust

Definitions, lemmas, derived theorems, tests, and interfaces whose proof terms
are checked by Lean. A hard-crust result may be conditional on mushy-center
axioms. Its claim is then a checked deduction relative to those axioms.

### Pressure

An independently checked obligation that is sensitive to the exact statement
or definition under test. Pressure can be positive or negative:

- a positive concrete instance exercises a claimed consequence;
- an edge case tests a boundary condition;
- a negative witness proves that dropping a stated hypothesis makes a
  conclusion fail;
- an independent cross-interface derivation checks that two representations
  agree;
- a consumer whose proof depends on the exact definition tests whether the
  declaration is load-bearing rather than merely reachable.

The number of declarations is not a pressure metric. A large tower of
restatements does not substitute for an independent witness.

### Axiom-free witness

A theorem or executable check whose proof dependency does not include the
axiom being tested. It may use the underlying definitions and proved
Mathlib/Scaffold facts. Its dependency status must be auditable with
`#print axioms` or an equivalent checker.

### Quarantined statement

A declaration retained for diagnosis or downstream planning after a stress
test finds a known countermodel, materially missing hypothesis, or unresolved
semantic mismatch. A quarantined statement is not evidence of a valid
mathematical result and must not enter the public umbrella or promotion path.

**Quarantine vs. in-place repair.** Every defect Scaffold has actually found
in an axiom so far (`docs/9_ERRATA.md` entries 6–9) turned out to be a
hypothesis-shape error: the source's true claim, mis-stated in Lean with a
missing or wrong hypothesis. In every one of those cases the fix was an
in-place repair — tighten the hypothesis to the source-faithful shape, keep
the same public declaration name and location, add an Errata entry — not a
move to `wip/` quarantine. Quarantine, as defined here, is for the narrower
and more severe case where the statement cannot be repaired by tightening
hypotheses alone: the theorem is simply the wrong theorem, a parameter that
should be graph-derived is left free, or there is an unresolved semantic
mismatch with the source. Reach for in-place repair plus an Errata entry
first; quarantine is the fallback when repair is not honestly possible
without changing what the axiom claims to be.

## 3. Axiom lifecycle

Every proposed axiom or theorem-shaped placeholder follows this lifecycle.

### Stage 0: intake

Record:

- the source and exact locator;
- the intended mathematical claim;
- the Lean representation and modeling choices;
- the concrete SGT obligation or consumer it unlocks;
- known prerequisites and intended proved replacement;
- whether the statement is source-faithful, provisional, or only a target
  shape.

If the statement is only a target shape, label it as such before writing
downstream claims.

### Stage 1: typed admission

Before admitting the result, check:

- all mathematical preconditions are explicit;
- dimensions, finiteness, symmetry, positivity, connectivity, independence,
  measurability, spectral gaps, and nondegeneracy appear where required;
- partial operations have defined edge behavior;
- free scalar parameters are tied to graph or analytic data when the source
  requires that relationship;
- the statement does not bundle unrelated results;
- the Lean type does not silently generalize away the source's domain.

An axiom may remain unproved. It may not remain semantically undefined.

### Stage 2: hard-crust load

Add at least one proved consumer that:

- uses the exact public declaration;
- derives a meaningful consequence rather than restating its conclusion;
- is sensitive to the relevant definitions or hypotheses; and
- has a small, independently inspectable proof.

For a WIP experiment, the consumer may remain downstream of the root package,
but its conditional status must be explicit.

### Stage 3: adversarial stress

Construct pressure in the following order where applicable:

1. zero, one, diagonal, empty, and boundary cases;
2. a small positive instance with independently computed expected values;
3. a case violating each important hypothesis;
4. a representation or sign-convention cross-check;
5. a consumer using the result in a nontrivial composition.

Negative witnesses should be proved without using the axiom under test. If a
negative witness contradicts an admitted universal statement, that is
evidence for quarantine or in-place repair (see §2), not a reason to hide the
witness or weaken the QA label.

The absence of a discovered counterexample is not proof that an axiom is
true. It is only a record of the tests performed.

### Stage 4: disposition

After stress testing, assign one status:

| Status | Meaning | Allowed use |
| --- | --- | --- |
| `candidate` | Not yet sufficiently typed or tested | WIP only; no public claim |
| `admitted` | Unproved, source-faithful, and sufficiently tested | Public conditional use |
| `quarantined` | Known countermodel, missing semantics, or unresolved mismatch, not repairable by tightening hypotheses alone | Diagnosis only; excluded from promotion |
| `proved` | Replaced by a checked proof with equivalent scope | Public use |
| `retired` | Removed or superseded with a migration record | Compatibility only if documented |

`quarantined` is not a failure of the mushy-center policy. It is the policy's
required response to a bad interface discovered before publication. A defect
repairable by tightening a hypothesis does not need this status at all — see
§2's quarantine-vs-repair distinction and `docs/9_ERRATA.md` for the repair
path actually in use.

### Stage 5: promotion or replacement

Promotion from WIP to public API requires:

- source-faithful statement and explicit assumptions;
- no unresolved known countermodel;
- direct compilation of the changed module and closest consumers;
- positive QA and proportionate adversarial QA;
- an axiom dependency audit;
- source and topic-index updates;
- documentation that distinguishes conditional deductions from proofs;
- a record of remaining trust and modeling risk.

When a proof becomes available, compare its hypotheses and conventions before
replacing the axiom. A theorem with a different scope needs an adapter or a
new declaration; it must not silently overwrite the old interface.

## 4. Machine-only acceptance gates

An autonomous run may perform the lifecycle without a human checking every
step, but the machine gates must be stronger than compilation alone.

The minimum gate set for an axiom-bearing change is:

1. changed modules and closest QA consumers elaborate directly;
2. the relevant build target passes;
3. no forbidden `sorry` or `admit` appears in the governed scope;
4. every public axiom has source and topic-index coverage;
5. every axiom has a documented QA consumer or a reviewed not-applicable
   rationale;
6. positive QA results are independently computed where the domain permits;
7. negative witnesses are present for known omitted-hypothesis risks, or the
   absence is recorded with a reason;
8. `#print axioms` or an equivalent audit identifies the exact trust cone;
9. no quarantined declaration is reachable from the public umbrella; and
10. promotion is blocked if an axiom-free witness refutes the proposed public
    statement.

**Current state, as of 2026-08-30 (not aspirational):** gates 1–3 and 8 are
already enforced, but by a human-in-the-loop (the commit steward re-deriving
`#print axioms` independently and running the sorry/admit sweep — see
`docs/arch/commit-steward-protocol.md`), not by an unattended machine check.
Gates 4 and 5 are partially enforced by `scripts/lint_axioms.py`'s citation
and degenerate-corner checks and `scripts/check_citations.py`. Gates 6–7 are
exercised by convention in every axiom-bearing delivery's own QA, but no
script verifies they were done. Gates 9 and 10 have no dedicated check at
all. Do not read this section as describing tooling that already exists in
full; §7 lists exactly which gates still need a script.

A machine pass certifies that these checks ran and that the deductions
elaborate. It does not certify citation fidelity or the truth of an external
axiom. Those limitations belong in the generated report.

## 5. Quarantine rules

A declaration must be quarantined when any of the following is established
**and the defect cannot be closed by tightening a hypothesis in place** (see
§2):

- a concrete instance satisfies its Lean hypotheses but falsifies its
  conclusion;
- a required source hypothesis is absent and the statement is consequently
  broader than the cited result;
- a parameter described by the source as graph-derived is free in Lean;
- a definition has multiple plausible meanings and downstream results do not
  identify which one is intended;
- a purported paper theorem is only a scalar, tautological, or unrelated
  consequence; or
- a dependency or citation claim cannot be reproduced.

Quarantined work may:

- remain in `wip/` or another explicitly non-public experiment;
- be used to generate counterexamples and repair targets;
- be referenced as a failed or incomplete formalization;
- retain compiled artifacts for local diagnosis.

It may not:

- be imported by the public umbrella;
- be counted as a proved theorem;
- be described as faithful to the source;
- serve as positive validation of the quarantined statement; or
- be promoted without a new disposition record.

If the quarantine is caused by a missing hypothesis, repair the interface in
place and rerun the stress suite — do not quarantine it (§2). If it is caused
by a wrong definition or sign, preserve the counterexample and retire the
invalid shape rather than adding a compatibility theorem that repeats it.

## 6. WIP experiment contract

An ignored WIP directory may move faster than the public library, but it
should contain:

- a README identifying its status and public-build boundary;
- a source citation and formalization map;
- an explicit axiom file or equivalent trust-boundary record;
- a gap document naming missing reusable interfaces;
- at least one hard-crust consumer;
- a verification command sequence;
- quarantine labels for known-bad or target-shaped declarations.

WIP QA should distinguish:

- a theorem that consumes an axiom;
- a theorem that independently tests the underlying definition; and
- a negative witness that attacks the axiom's current scope.

These categories must not be collapsed into a single "validated" count.

## 7. Recommended repository changes

To make this proposal enforceable, the repository should eventually:

1. ~~add a short reference to this policy from
   `governance/CONTRIBUTING.md`~~ — superseded: this document is a proposal,
   not an adopted policy, until the decision in the next section is made;
2. add `candidate` and `quarantined` terminology to the architecture and
   QA documentation;
3. extend the axiom linter to require status, source, intended replacement,
   and QA references for governed public declarations;
4. add an axiom-audit command that checks negative witnesses do not depend on
   the axiom they refute;
5. add a public-umbrella reachability check that rejects quarantined modules;
6. make autonomous run reports record the disposition and remaining pressure
   for every touched axiom; and
7. add a promotion checklist for WIP experiments.

These are implementation follow-ups, not claims that the current scripts
already enforce all of them. None of items 2–7 should be started
unprompted — they are only worth building if **Decision needed** below is
resolved in favor of adopting this proposal's vocabulary and lifecycle.

## 8. Decision rule

The governing rule is:

> Defer the proof if necessary; never defer the statement's accountability.

Scaffold may pile hard-crust deductions, examples, cross-checks, and
counterexamples onto a mushy-center assumption. When the center survives,
the result is a better-tested conditional interface. When it breaks, the
failure is a useful formalization result and the declaration is quarantined
or repaired in place (§2) until resolved.

## Decision needed — resolved in part, 2026-08-30

The operator was offered three options: adopt the full vocabulary and
6-stage lifecycle as standing policy; keep only the lighter combination
already in place (`docs/9_ERRATA.md` for the repair case,
`docs/arch/commit-steward-protocol.md` for the verification-gate case); or
adopt just §7's concrete tooling items without the vocabulary.

**The operator chose the third option.** §7 items 3–5 — the axiom linter
extension, the negative-witness independence checker, and the
public-umbrella reachability check — are split into their own proposal,
[`axiom-audit-tooling.md`](axiom-audit-tooling.md), indexed **High** in
`proposals/README.md`. That proposal is self-contained and does not require
adopting this document's vocabulary or lifecycle to execute.

**What remains genuinely undecided:** whether to additionally adopt the
`candidate`/`admitted`/`quarantined`/`proved`/`retired` disposition
vocabulary and the 6-stage lifecycle (§§2–6) as standing policy governing
future axiom admissions, on top of the tooling above. That question is not
queued for any run and stays a Low/human-decision-required item — the same
posture the adjacent
[Retire the Mushy Center Systematically](retire-the-mushy-center.md)
proposal takes toward its own heavier apparatus.
