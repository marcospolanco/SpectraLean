# Icebox: Non-Mathlib Lean Dependencies — What Exists, and Why Using It Is a Different Decision Than It Looks

**Status:** Technical/governance finding, not a proposal. No priority; not
something an autonomous run should act on. Written 2026-08-19 while scoping
`proposals/weighted-matrix-tree-theorem.md`, prompted directly by the
question "is Mathlib our only acceptable dependency? Does none of this
machinery exist in other Lean projects on GitHub?" Kept here because the
finding is general — it bears on every icebox entry and every future gap
this project surveys, not just Matrix-Tree.

## The question this answers

Two related questions:

1. Does any of the machinery named absent in this project's icebox entries
   (Matrix-Tree, Golden-Thompson/Lieb, Cauchy–Binet, ODE-trajectory
   calculus) already exist in some *other* Lean 4 project on GitHub, even
   if not in Mathlib itself?
2. If it does, is using it just a matter of adding a `require` line to
   `lakefile.lean`?

The answer to (1) is yes, for at least some of it. The answer to (2) is no,
and the reasons why are worth recording once rather than re-litigating at
every future gap.

## What this repository's own policy actually says

`lakefile.lean` currently `require`s only Mathlib. Every icebox survey to
date (`matrix-chernoff-formalization-gap.md`,
`lyapunov-stability-formalization-gap.md`,
`stochastic-calculus-and-log-sobolev-gap.md`, and
`weighted-matrix-tree-theorem.md`'s own survey) checked only the pinned
Mathlib tree, never the wider Lean ecosystem. That is a *practice*, not a
documented rule: `docs/2_ARCHITECTURE.md` §9 explicitly says "when Mathlib
**or another accepted dependency** provides a proved replacement,"
leaving the door open in principle. No file anywhere in this repository
defines what "accepted" means or names an acceptance process. There is no
precedent of this project ever using a second dependency. In short:
Mathlib-only has been a habit, not a rule — and the rule, if the project
ever wants one, doesn't exist yet either.

## What was found (verified only at the level stated — see caveats)

A web search on 2026-08-19, not a source-code review, turned up:

- **Matrix-Tree / Kirchhoff's theorem:** two independent repositories.
  `boonsuan/FerrersBound` has a graph-side "Kirchhoff matrix-tree bridge"
  (`FerrersBound/Graph/KirchhoffMatrixTree.lean`,
  `algebraicSpanningTreeCount_eq_spanningTreeCount`), and
  `Boussetta/MatrixTreeTheorem` is a dedicated repository on the same
  theorem.
- **Golden–Thompson / Lieb's concavity** (the hardest gap named in
  `matrix-chernoff-formalization-gap.md`): a paper, *"Lean-Quantum:
  Toward AI-Assisted Formalization of Quantum Information"*
  (arXiv:2607.05492), references formalization work on Lieb's concavity
  theorem and Jensen's operator inequality inside a quantum-information
  Lean project.
- **Cauchy–Binet** (the gap named in this proposal's own Route A): an
  "algebraic-combinatorics blueprint" project
  (`faabian.github.io/algebraic-combinatorics`) has a dedicated section
  on it. Blueprint projects typically target eventual Mathlib
  upstreaming, so this may already be moving toward closing the gap
  through the normal channel rather than needing to be consumed
  separately.

## Caveats — read before treating any of this as usable

- **None of these repositories' Lean source has been read by this
  project.** The evidence above is search-result-level (repo
  descriptions, a paper abstract) — exactly the kind of unverified
  citation this project's own discipline (catching the false
  `matrix_chernoff_upper_lower` citation in
  `spectral-graph-sparsification.md`, verifying every Mathlib lemma name
  before citing it) says should not be trusted without opening the file.
- **`FerrersBound`'s own description states it was "formalized by Harmonic
  Aristotle under the guidance of GPT-5.4 Pro."** Not disqualifying on
  its own — this project's own proposals are AI-authored too — but it
  means there is no Mathlib-style community review, CI, or maintainer
  sign-off standing behind it. The same verification discipline this
  project applies to its own work would need to apply *at least* as
  strictly here, and nothing like that has been done yet.
- **A blueprint is not a proof.** The Cauchy–Binet blueprint entry may be
  a stated plan, a partial formalization, or a completed one — the
  search did not distinguish, and this finding does not claim to know
  which.

## Why using an external dependency is a bigger decision than it looks

Four distinct costs, independent of whether the target repository turns
out to be correct:

1. **Trust asymmetry with this project's own model.** Scaffold's entire
   assurance story rests on two visible categories: proved theorems
   (hard crust) and explicitly cited, reviewed axioms (mushy center). A
   wrong axiom is visible by design — it says `axiom` in the source and
   is listed in the trust table. An unsound or subtly mismatched external
   dependency, consumed as if it were ordinary "proved" material, is
   invisible in exactly the way the axiom boundary is built to prevent.
   This is a materially different — and larger — trust decision than
   admitting a well-cited axiom, not a smaller one.
2. **Definitional mismatch is close to guaranteed.** Any external
   project's graph or matrix representation will differ from Scaffold's
   own `WAdj`/`laplacian A := degreeMatrix A - A` convention — the exact
   problem `SimpleGraphAdapter.lean` exists to solve for *Mathlib's own*
   `SimpleGraph`. Bridging a second, independently-designed
   representation could easily cost as much proof effort as reproving
   the target theorem directly against Mathlib, the same calculation
   `electrical-structure-crust.md`'s own corrections already made once
   for a Mathlib-internal transport decision.
3. **No pin-stability story.** `lean-toolchain` and `lakefile.lean`
   currently guarantee one reproducible build against one pinned,
   actively-maintained dependency. An individual's GitHub repository
   carries no comparable guarantee — it can go stale against the Lean
   version, be abandoned, or disappear outright, with no equivalent of
   Mathlib's release process to fall back on.
4. **No acceptance process exists to make the call.** `docs/2_ARCHITECTURE.md`
   §9's "or another accepted dependency" phrase presumes a decision
   process this repository has never built. Using one today would mean
   inventing that process ad hoc, under the pressure of one specific
   gap, rather than deciding it deliberately.

## Three real paths forward, honestly ordered by cost

1. **Read, don't depend.** Treat an external repo's Lean source the way
   this project already treats a textbook citation — informative for
   proof-route sketching (e.g., seeing how `FerrersBound` structures its
   matrix-tree bridge could sharpen
   `weighted-matrix-tree-theorem.md`'s own Step 3 before it's written) —
   without adding it as a build dependency. Zero governance cost, most of
   the practical benefit.
2. **Watch, don't act.** For gaps where the found project targets
   eventual Mathlib upstreaming (the Cauchy–Binet blueprint is the
   candidate here), simply re-check the pinned Mathlib version's coverage
   on the normal `docs/8_MATHLIB_COVERAGE_MAP.md` cadence rather than
   trying to consume the in-progress work directly.
3. **Formally adopt a second dependency.** Real, and not ruled out by
   anything found here — but its own governance proposal: name the
   specific repository, actually read and review its source against this
   project's own quality dimensions (`docs/2_ARCHITECTURE.md` §7), and
   define the acceptance process itself (versioning/pinning story,
   review bar, deprecation/removal path mirroring §9's existing
   Mathlib-replacement lifecycle) before consuming anything from it. Not
   a decision an autonomous run should make by adding a `require` line.

## Re-survey trigger

If any of the three gaps this session has iceboxed (Golden-Thompson/Lieb,
Cauchy–Binet, Matrix-Tree) becomes newly load-bearing for a proposal an
operator has adopted, re-run this search *and* actually open the target
repository's source before citing it as available — a repo existing is
not the same claim as a repo being correct, reviewed, or compatible, and
this entry should not be cited as having established any of those three.
