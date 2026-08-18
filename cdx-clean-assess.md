No. I would not assess that `spectral-proof` was “never used,” especially if inspiration counts.

The evidence supports three distinct conclusions:

- Current source dependency: none found. No live import, symlink, manifest dependency, or source reference connects the candidate SGT core to `spectral-proof/`. Current Mathlib is a normal directory pinned from GitHub in `lakefile.lean:8`.

- Historical build reuse: confirmed. Archived records explicitly say Scaffold used a Mathlib installation symlinked from the `spectral-proof` project: `research/archive/status/STATUS.md:25` and `research/archive/status/QA_SCOREBOARD.md:120`. That is dependency-cache reuse, not proof of source copying.

- Historical inspiration/motivation: strongly indicated. The initial repository included an “Oil Strategy” that described `spectral-proof/` as the proprietary application layer built on Scaffold and instructed work to bridge its `strict_gap` and `reconstruction` gaps through Scaffold definitions: `research/archive/oil-strategy.md:23`. The later “clearer purpose” commit made spectral persistence and x90 the repository’s explicit research objective, closely matching that roadmap.

So the defensible assessment is:

> There is no evidence of a current code-level dependency, but there is affirmative evidence of historical build-environment reuse and strong evidence that `spectral-proof` influenced Scaffold’s original requirements, priorities, and research direction.

Without inspecting and comparing the quarantined source, we cannot establish whether code, theorem shapes, terminology, or implementation ideas were copied. For clean-room purposes, the SGT files should therefore be treated as provenance-uncertain—not independently derived merely because they contain no textual `spectral-proof` reference.

## Follow-up: direct comparison against `spectral-proof/` (2026-08-18)

The comparison this document called for was performed directly, before
`spectral-proof/` was removed from the working tree. Findings, evidence-based
rather than inferential:

- **Zero code-level dependency, confirmed independently.** No imports,
  symlinks, or path references from tracked Scaffold source into
  `spectral-proof/` were found.
- **Near-zero declaration-name overlap.** All 215 declaration names across
  `spectral-proof/`'s 22 Lean files (5,028 lines, module names including
  `FederationRisk`, `PredictiveLeakage`, `ShadowprintStability`,
  `PredictiveBottleneckStability`, `ContractionBiophysics`,
  `SpectralBiophysics`) were diffed against all 755 declaration names in the
  tracked Scaffold tree. Exactly 4 exact matches: `vol`, `vol_nonneg`,
  `conductance`, `conductance_nonneg`. Both sides state the standard Chung
  1997 textbook definitions (volume = sum of weighted degrees; conductance =
  boundary weight over min volume) but on materially different type
  architecture — `spectral-proof` hardcodes `WGraph n` over `Fin n`; Scaffold
  is polymorphic `WAdj (V := V)` over an abstract `Fintype`. This is what
  independent formalization of a decades-old public definition looks like,
  not derivation.
- **None of `spectral-proof`'s distinctively proprietary vocabulary appears
  anywhere in tracked Scaffold.** A repository-wide search for
  `FederationRisk`, `PredictiveLeakage`, `ShadowprintStability`,
  `PredictiveBottleneckStability`, `ContractionBiophysics`,
  `SpectralBiophysics`, and `ManifoldProjection` found zero hits outside
  `spectral-proof/` itself.
- **Every axiom's citation checks out against real, independent literature**
  — confirmed by `scripts/check_citations.py` passing and direct spot-checks
  (Chung, Horn–Johnson, Fiedler, Davis–Kahan 1970, Weyl 1912/Bhatia, Tropp,
  Vershynin, Wainwright, Higham). None cite `spectral-proof` or anything
  proprietary.

**The one exception found is motivational, not mathematical.** The retained
persistence package (`GraphTheory/Dynamics.lean`,
`Derived/{EventStream,ProjectorDrift}.lean`) has one axiom,
`spectral_persistence` (deprecated 2026-08-17, zero non-QA consumers) — its
citation is the genuine, published "projector form of Davis–Kahan," same
literature family as the rest of the repository. The math is clean. What
traces back to `spectral-proof` is why this module exists at all:
`docs/3_SPECTRAL_THEORY.md` openly cites its own archived
`oil-strategy.md`/`x90-algorithm.md` provenance, and `oil-strategy.md`
explicitly names `spectral-proof` as "the proprietary application layer"
this pipeline was built to serve.

**Revised assessment.** Every theorem and axiom currently in this repository
traces to well-known public literature, with no exception found. The one
real connection to `spectral-proof` is to research motivation, not to any
proved or admitted mathematical statement — and it was already open
knowledge, not a hidden dependency, and already exactly what
`clean-room-sgt-export.md` and `traction-plan.md` exclude ("do not
reference... persistence work, or prior application rationale"). This
technical finding is strong supporting evidence, not a legal clearance; the
export proposal's Phase 0 counsel-sign-off gate is unaffected by it.

`spectral-proof/` was removed from the working tree after this comparison
was completed and recorded (`rm -rf`, untracked and gitignored throughout,
2026-08-18) — the provenance-uncertainty question this document opened with
is resolved for the current tracked codebase, and the quarantined material
itself no longer needs to sit in this working tree to keep it that way.
