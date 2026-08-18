# Proposal: A Spectral Mixing-Time Bound

**Status:** Proposed. Assistant's assessment of project direction, requested
2026-08-18 (surface-area follow-up for the formal-methods/high-assurance
audience). Authorizes no Lean changes, axiom admissions, document
rewrites, or external publication.

Companion to [Grow the Crust Through Electrical
Structure](electrical-structure-crust.md) — same "grow the crust" premise,
different target: backlog item 4's other named candidate shape, "walk
mixing through the transition spectrum." Independent of [Prove λ₂'s
Variational Characterization](prove-lambda2-variational.md): this proposal
needs only the *value* of the spectral gap via `evals`, not its variational
description, so it does not gate on that proposal landing.

Assessed from `Scaffold/Mathlib/GraphTheory/{RandomWalk,Normalized,
VariationalTransfer,Spectral}.lean`, `docs/6_SGT_BACKLOG.md` item 2's
"residual gap" note, `docs/7_SGT_RADAR.md` axis 5, `docs/8_MATHLIB_COVERAGE_MAP.md`
(random walks/Markov chains: absent upstream), and a fresh search of
`.lake/packages/mathlib/Mathlib/{Probability,MeasureTheory}` for
total-variation-distance or mixing-time machinery (none found).

## Recommendation

Prove that the random walk's distance to its stationary distribution
decays geometrically in the number of steps, at a rate governed by the
walk matrix's second-largest eigenvalue modulus — the concrete gap named
in `docs/7_SGT_RADAR.md` axis 5 ("Absent: mixing-time statements... the
walk-spectrum transfer is the named Mathlib gap") and backlog item 4.

## Why this axis

This is the specific surface-area gap identified for the formal-methods/
distributed-systems audience: it turns Scaffold's existing walk and
spectral machinery into an actual usable convergence-rate guarantee — "how
many rounds until my gossip protocol converges" — rather than more
foundational SGT with no application-layer consumer. It composes with real
proved assets already on the shelf: `walkTransitionMatrix`/
`transitionMatrix` row-stochasticity (`RandomWalk.lean`, 0 axioms), and,
critically, the already-proved similarity identity `√D · L_walk · (1/√D) =
L_sym` (`Normalized.lean:224`).

## Calibration

Two very different difficulty levels hide inside "mixing-time bound." Do
not treat them as one slice.

- **Step 1 (eigenvalue transfer) is likely cheap.** `L_walk` and `L_sym`
  are related by a genuine *similarity* transform (conjugation by the
  invertible diagonal `√D`), so they share the same eigenvalues with
  multiplicity — standard linear algebra. `Normalized.lean`'s own comment
  already names this as "the precisely named residual gap" from backlog
  item 2; it is not a new discovery, just unstarted work.
- **Step 2 (the actual decay bound) is not cheap.** Mathlib has zero
  Markov-chain or total-variation-distance infrastructure — verified
  against the coverage map and a fresh search this session (only unrelated
  `MeasureTheory/Decomposition/*` files matched "variation"). This is
  substantially original Scaffold work. Treat it as at least as hard as
  the electrical program's step 4 (potential solvability) was scoped to
  be — a multi-run project, not a single slice.

## Build order

### 1. Transfer eigenvalues to the walk matrix, via similarity

Prove a similarity-invariance fact — either generally (`A` and `S⁻¹AS`
share eigenvalues, for invertible `S`) or, more cheaply, directly for
Scaffold's specific diagonal case. Since `L_sym = √D · L_walk · (1/√D)`
and `L_sym` is symmetric with a known sorted spectrum `evals`, define the
walk matrix's eigenvalues through that identity: `∀ i`, the walk matrix's
eigenvalue at index `i` equals `1 - evals L_sym i`. **Survey Mathlib
first** for a general similar-matrices-share-eigenvalues lemma before
reproving it, per this repository's own "survey before proving" rule — but
judge transport on cost, not reflex: the specific diagonal case may be
cheaper to prove directly than to instantiate a general lemma, the same
way `electrical-structure-crust.md` step 2 found direct proof cheaper than
transport from Mathlib's unweighted kernel theorem.

### 2. Define an ℓ²-mixing proxy, not total variation, first

Full total variation distance needs `MeasureTheory.Measure` machinery
Scaffold has never touched. A cheaper, still-meaningful first target: the
ℓ²-distance `‖Pᵗ δₓ − π‖₂` between the walk distribution after `t` steps
and the stationary distribution `π`, expressed directly through Scaffold's
own `deg`/`vol`/eigenbasis machinery — no new measure-theoretic
definitions. This is the standard "spectral mixing lemma" shape most
textbooks prove before converting to TV via Cauchy–Schwarz. **Decide and
record** whether the ℓ² statement alone satisfies this proposal's goal, or
whether the ℓ² → TV conversion is scoped as a further step, before writing
the statement.

### 3. The geometric decay bound

Prove `‖Pᵗ δₓ − π‖₂ ≤ (λ*)ᵗ · (normalization)`, where `λ*` is the maximum
absolute value among the non-principal eigenvalues transferred in step 1.
This is the actual mixing-time statement: it composes the eigenvalue
transfer, the eigenbasis-projector algebra already proved in
`Spectral.lean` (`spectralProjector`, `eigvecOf_complete`), and an
induction on `t` for the matrix-power decay. Likely the hardest single
step in this program; may need its own sub-decomposition across runs, the
same way the electrical program split steps 4 and 5.

### 4. (Optional, higher cost) Convert to total variation

Only after step 3 lands, and only if a named consumer needs TV
specifically rather than ℓ². Requires a probability-measure wrapper
Scaffold has never used before — treat as its own proposal-scale decision,
not a default continuation of this one.

## Deferred and removed

- **General (non-diagonally-similar) walk mixing** — out of scope. This
  proposal covers only walks whose transition matrix is diagonally similar
  to a symmetric matrix, which is true of every `WAdj`-based walk Scaffold
  currently defines.
- **Reversibility as its own theorem** — radar axis 5 lists it absent
  alongside mixing time; not addressed here. A natural companion proposal,
  not a prerequisite of this one.

## Operating instructions for an autonomous run

- One step per run; step 3 may need more than one, per the electrical
  program's own precedent for its hardest steps.
- **No new axioms.** If step 2's ℓ² decay bound turns out to need genuinely
  new real-analysis machinery not extractable from what is on the shelf,
  stop and record the precise obstruction in `docs/6_SGT_BACKLOG.md` rather
  than admitting anything.
- Survey Mathlib before proving each step; update
  `docs/8_MATHLIB_COVERAGE_MAP.md` if the survey finds something that map
  missed.
- QA: a positive witness (a small graph where the bound is checked
  numerically against a hand-computed mixing rate) and a negative witness
  showing the bound fails without the eigenvalue-transfer hypothesis.
- Do not re-score `docs/7_SGT_RADAR.md` axis 5 until a step's proof lands
  and its QA passes.

## Open next step

Scope step 1 in detail — specifically, whether Mathlib already has any
general similar-matrices-eigenvalues lemma usable off the shelf, since
that changes step 1's cost materially — before committing a run.
