# Strategy

**Status:** Canonical project strategy  
**Last reviewed:** August 17, 2026

## Mission

Scaffold is a Lean library for making selected, modern applied-mathematics results usable before their foundational proofs are available in Mathlib. It exposes those results as explicit, cited axioms with mathlib-compatible types and tests their interfaces with small, fully proved QA lemmas.

The project optimizes for transparent assumptions and replaceable APIs. It does not claim that an axiom has been formally proved, that a citation has been independently verified merely because it is present, or that a QA lemma establishes the truth of its dependencies.

## Who it serves

- Applied researchers who want Lean to check new deductions while treating established literature as an explicit trust boundary.
- Lean developers who need stable interfaces for concentration, perturbation, and spectral graph theory.
- Formalizers looking for a structured backlog of useful results that may later be proved upstream.
- Research collaborators evaluating SGT questions and executable research
  pipelines.

## Ecosystem pacing

The internal shorthand “rabbit” describes a pacing choice, not competition with Mathlib. Mathlib prioritizes proved, reusable foundations and community review. Scaffold can move faster in a narrow applied domain because it admits cited statements at an explicit axiom boundary. The tradeoff is reduced assurance: downstream proofs are conditional on those axioms.

Scaffold should therefore stay subordinate and interoperable:

1. Reuse Mathlib definitions and naming where practical.
2. Admit only the smallest statements needed for current applications.
3. Record citations and modeling differences.
4. Replace Scaffold declarations when suitable proved upstream results appear.

## Why spectral graph theory is a useful focus

The intended applications cross several formal domains: finite graph combinatorics, matrices and operator norms, probability and concentration, and perturbation theory. A usable result often depends on all four. That intersection makes API alignment as important as theorem availability. See the [Mathlib Coverage Map](8_MATHLIB_COVERAGE_MAP.md) for a dated survey of how well the pinned Mathlib itself covers each of these tendrils — the admitted-axiom surface below traces that map closely.

Spectral persistence is already developed elsewhere and is retained here only
as an existing compatibility/example package. It is not Scaffold's research
goal or the criterion for choosing new work. Scaffold's agenda is to grow a
broad, reusable neighborhood around SGT, so future research can start from
well-specified graph, spectral, probabilistic, and operator-theoretic APIs.

## Center-out prioritization

Spectral graph theory is the organizing center for ongoing work. The repository expands outward only along dependencies that unlock a concrete SGT theorem, research experiment, or downstream application.

The working rings are:

1. **SGT center:** graph and Laplacian definitions, quadratic and Rayleigh forms, spectra, variational characterizations, Cheeger theory, and buildable QA.
2. **Mathematical bridges:** perturbation theory, matrix concentration, probability, and update identities needed by a center obligation.
3. **Reusable SGT extensions:** general interfaces and tools with more than
   one plausible SGT consumer.
4. **Research applications:** domain observables and experiments that name
   their needed SGT interfaces.

Work may proceed outward only when the inward dependency path is explicit.
When adjacent or application work reveals an ambiguous definition, missing
assumption, placeholder, or broken interface, the priority moves inward to
the nearest load-bearing defect.

### Leverage test

Compare proposed work using these questions:

- How many concrete SGT proof obligations or consumers does it unlock?
- Does it repair a load-bearing definition or reduce the axiom/admission surface?
- Is it load-bearing on something not yet stress-tested — would an error in
  an earlier definition make this fail to typecheck or fail a
  negative-witness QA, rather than sit beside it unaffected? (See
  [Load-bearing growth](#load-bearing-growth-the-path-to-falsifiability).)
- Will the interface be reused across multiple SGT results?
- Does it improve alignment with Mathlib and make upstream replacement easier?
- Can progress be verified through a focused proof, build, citation review, or experiment?
- Is the expected gain worth its implementation and maintenance cost?

Build health, meaningful statement shapes, real definitions, and source fidelity outrank new breadth. Adjacency to SGT is not sufficient by itself; the dependency and leverage case must be documented in the issue or pull request.

## Load-bearing growth: the path to falsifiability

*Added 2026-08-18.* Scaffold's growth strategy does not treat outside
review — Mathlib merges, external users — as the primary mechanism for
trusting the substrate (see `proposals/get-outside-signal.md` for the
external-review track, which stays live but is not this section's
subject). Lean's kernel is already a genuine adversary: a proof either
type-checks against its exact stated type or it does not, independent of
social consensus. Growth should be chosen to exploit that adversary, not
merely to avoid tripping it.

**Height is not evidence.** A declaration that compiles and sits beside
existing work, without depending on the precise correctness of any
specific earlier definition, adds surface area but tests nothing. Scaffold
has direct evidence of this failure mode: the original `cheeger_lower_bound`
axiom shape typechecked, was admitted, and sat in the tower undisturbed —
and was false (`old_cheeger_lower_bound_refuted_QA`, recorded in
`docs/AGENT_ACTIVITY.md`, 2026-08-18: the pre-repair shape evaluated to
`1/2 ≤ 0` on `K₂`). What caught it was not the tower staying balanced; it
was a QA witness engineered specifically to try to knock that block over.

**The principle.** Prefer work whose success is *contingent* on an earlier
definition or proof being exactly right — where getting the substrate
wrong would make the new proof fail to typecheck, or a paired
negative-witness QA lemma fail to hold, loudly and immediately. Each new
load-bearing layer is a falsification attempt against the layer below it;
a layer that stays standing after real weight is placed on it is evidence
about that layer, not merely about itself.

**What this looks like in practice:**

- A theorem whose statement or proof would have to change if an earlier
  definition's *exact shape* — not just its existence — were wrong. Example:
  `laplacian_kernel_eq_span_onesVec`'s exact one-dimensionality claim is
  load-bearing for effective-resistance well-definedness
  (`proposals/electrical-structure-crust.md` step 5): if the kernel
  characterization were off by even "at most one dimension" instead of
  "exactly one," resistance uniqueness would fail to prove.
- A derivation that consumes an axiom to produce a proved corollary whose
  statement is independently checkable against a concrete example, not
  merely a restatement of the axiom in different notation.
- Negative-witness QA: a fixture built specifically to fail if a hypothesis
  is dropped (see `Connectivity_QA.lean`'s disconnected witness), not only
  positive examples a wrong theorem might pass by accident.

**What this rules out as a growth priority.** New declarations chosen
because they are reachable in one run and do not conflict with anything,
without naming which existing definition's correctness they would falsify
if wrong. That work is not useless — it is connective tissue, per
`proposals/prove-cheeger-easy-direction.md`'s finding — but it should not
be scored as evidence of substrate trustworthiness, because it has not
tested any.

**Relation to the leverage test.** This sharpens, rather than replaces, the
leverage test's existing "repair a load-bearing definition" question:
prioritize not only repairing known-broken load-bearing definitions but
*creating new load-bearing consumers* of definitions not yet stress-tested,
so that being wrong would surface on its own.

## Conjecture pathfinding

The project uses a disciplined search loop for turning an application goal into formal targets under incomplete information:

1. **State the observable.** Define the quantity the application can actually measure.
2. **State the desired guarantee.** Express the operational success condition as a typed mathematical relation.
3. **Build the dependency graph.** Identify definitions, textbook results, bridge lemmas, and genuinely novel claims.
4. **Classify every edge.** Mark it as proved upstream, axiom-backed, locally proved, experimentally supported, or conjectural.
5. **Choose the smallest frontier cut.** Admit or investigate only the missing statements that unlock the next testable result.
6. **Run falsification checks.** Exercise edge cases, dimensions, zero denominators, symmetry assumptions, and small examples.
7. **Promote carefully.** Move a claim from hypothesis to theorem only when its proof and dependencies justify that status.

This process treats conjecture generation as constrained search. It is a prioritization method, not an automated proof of novelty or correctness.

## Success measures

Scaffold is succeeding when:

- downstream work can import narrow APIs without importing unrelated assumptions;
- every public axiom has precise provenance and an explicit trust cost;
- QA exercises meaningful consequences without `sorry` or `admit`;
- current build and coverage status can be reproduced;
- upstream replacements reduce, rather than expand, the axiom surface;
- research hypotheses are connected to measurable experiments and formal proof obligations;
- new work is load-bearing on the substrate it builds on — see
  [Load-bearing growth](#load-bearing-growth-the-path-to-falsifiability) —
  rather than merely coexisting with it.

## Source provenance

This document distills the archived [project assessment](../research/archive/gem-scaffold-assessment.md) and [pathfinding transcript](../research/archive/pathfinding.md). Those files preserve historical reasoning; this document controls current strategy.
