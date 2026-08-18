# Proposal: Grow the Crust Through Electrical Structure

**Status:** Proposed; steps 1–5 of 6 delivered (2026-08-18, see
checklist below). Assistant's assessment of project direction,
requested 2026-08-17; substantially re-sequenced 2026-08-18 after
review (see [Corrections](#corrections)). Authorizes no Lean changes,
axiom admissions, document rewrites, or external publication.

Companion to [Prove One Named Inequality](prove-cheeger-easy-direction.md).
That proposal argues for *shrinking the mushy center*; this one takes the
opposite premise — the center stays fixed — and asks where the hard crust
should grow. The two are independent and either may be adopted alone.

**This document is the complete brief for an autonomous run.** It carries its
own scope fence, constraints, and stop conditions in
[Operating instructions](#operating-instructions-for-an-autonomous-run); an
operator directing a run against it should not need to restate them.

**Clean-room note.** This document is not exportable. Per the inclusion test
in [Clean-Room SGT Export](clean-room-sgt-export.md), it is dense with radar
scores, axiom counts, run history, and internal planning rationale. If the
program here is carried into the new repository, restate it from public
mathematical requirements; do not copy this file.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean`,
`docs/6_SGT_BACKLOG.md` (items 3, 4, 7), `docs/7_SGT_RADAR.md`, the Mathlib pin
in `lakefile.lean` (v4.14.0), and that pin's
`Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean`.

## Recommendation

Grow the crust into **combinatorial and electrical structure** — the radar's
axis 6, currently scored 0.5 and described as entirely absent — beginning with
the interoperability adapter that the rest of the program needs anyway.

## Why this axis

It is the one major SGT neighborhood whose core theorems are provable with
**no axioms at all**. This is structural, not accidental: Cheeger, Weyl,
Davis–Kahan, and interlacing are hard to formalize because they are
inequalities requiring real analysis. Electrical network theory is linear
algebra — solvability, energy identities, orthogonality. It is the largest
theorem-dense region reachable without touching the mushy center.

It also composes with the repository's strongest existing asset. The proved
Dirichlet identity `laplacian_quadForm` (`Spectral.lean:531`),

```
quadForm (laplacian A) x = (∑ i, ∑ j, A i j * (x i - x j)^2) / 2
```

*is* the electrical energy. Every resistance theorem below is a consumer of
that single identity. This satisfies the center-out policy in
[Strategy](../docs/1_STRATEGY.md) on its merits, and answers backlog item 7's
gate by naming the consumers up front.

**Calibration.** "No axioms required" is not "cheap." Earlier drafts of this
document described the variational steps as completing-the-square exercises.
The repository's own evidence contradicts that: `lambda2_variational`
(`Spectral.lean:785`) is an **admitted axiom** — a variational characterization
of exactly this shape was not proved here because it was not easy. Effective
resistance below is a coherent mini-project of four or five slices, not a
handful of near-free lemmas.

## Corrections

**2026-08-18 (first) — step 1 was scoped wrong.** The original text directed a
from-scratch walk-propagation proof of the kernel characterization; the sketch
it gave was verbatim the induction Mathlib already runs at
`LapMatrix.lean:115-118`. On closer costing, transport turned out to be
roughly a wash for the *weighted* statement (see
[step 2](#2-the-weighted-kernel-characterization)), but the survey changed the
plan elsewhere and settled the connectivity-predicate question.

**2026-08-18 (second) — the existence error.** The original step on effective
resistance asserted that well-definedness "is a corollary of step 1." That is
false. The kernel characterization gives **uniqueness modulo constants**; it
says nothing about whether a potential solving `L f = e u - e v` exists at all.
Existence is a separate solvability result and is the real hinge of the
electrical program. It now has its own step
([step 4](#4-potential-solvability-the-hinge)) placed before any definition of
resistance. Without it, every downstream theorem would be conditional on a
hypothesis that might be unsatisfiable, and could be proved vacuously.

**2026-08-18 (third) — sequencing.** The `SimpleGraph` adapter was described as
the "highest compounding multiplier available" and then sequenced last. It is
now step 1. Rayleigh monotonicity and Foster's theorem were over-promised as a
"gated stretch"; Foster is removed from the program and monotonicity is
deferred, with only its cheap one-sided fragment retained.

## What the pinned Mathlib already provides

`Mathlib/Combinatorics/SimpleGraph/LapMatrix.lean`, at the v4.14.0 pin, on
`G.lapMatrix R = G.degMatrix R - G.adjMatrix R`:

| Mathlib declaration | Line | Scaffold's counterpart |
| --- | ---: | --- |
| `lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable` | 120 | absent — target of step 2 |
| `card_ConnectedComponent_eq_rank_ker_lapMatrix` | 191 | absent — inherited at step 3 |
| `lapMatrix_ker_basis` | 184 | absent — inherited at step 3 |
| `lapMatrix_toLinearMap₂'` (Dirichlet form) | 77 | `laplacian_quadForm` |
| `posSemidef_lapMatrix` | 92 | `laplacian_psd` |
| `isSymm_lapMatrix` | 52 | `laplacian_symmetric` |
| `lapMatrix_mulVec_const_eq_zero` | 63 | `laplacian_ones_in_kernel` |

**The gap is weight.** Mathlib's `degMatrix` is built from `G.degree`, a `ℕ`
count, and `adjMatrix` is `0`/`1`. Scaffold's `WAdj` carries real weights, so
Mathlib does not discharge Scaffold's statements in general.

**Duplication finding (for the radar).** The bottom four rows are Scaffold
independently reproving Mathlib. `docs/7_SGT_RADAR.md` scores Mathlib
interoperability 3.5 and describes the matrix-first representation as a
documented deviation; it does not record that the deviation costs duplicated
proofs. That belongs in the interoperability evidence, and it is part of why
the adapter is now step 1.

## Two adapters, not one

These are different objects and the program needs both. Conflating them was
part of the original sequencing error.

| | Direction | Purpose | Step | Status |
| --- | --- | --- | ---: | --- |
| `toWAdj` | `SimpleGraph → WAdj` | Lets an outside user bring their graph in; lets Scaffold's theorems apply to Mathlib's objects | 1 | ✅ delivered |
| `supportGraph` | `WAdj → SimpleGraph` | Lets a *weighted* graph have a connectivity predicate at all | 2 | ✅ delivered |

## Build order

- [x] **1. The `SimpleGraph → WAdj` interoperability adapter** — delivered
  2026-08-18: `Scaffold/Mathlib/GraphTheory/SimpleGraphAdapter.lean`
  (`toWAdj`, `toWAdj_symm`, `toWAdj_nonneg`, degree/volume/handshake
  agreement, `laplacian_toWAdj_eq_lapMatrix`, boundary agreement, the two
  Mathlib re-exports, and the `supportGraph_toWAdj_eq_self` roundtrip).
- [x] **2. The weighted kernel characterization** — delivered 2026-08-18:
  `supportGraph`, `supportGraph_adj`, `eq_of_supportGraph_walk`,
  `laplacian_kernel_eq_span_onesVec` in `Spectral.lean`, proved directly
  per [Corrections](#corrections), not by transport; QA in
  `SpectralGraph/Connectivity_QA.lean` with connected and disconnected
  witnesses.
- [x] **3. The kernel-equality bridge** — delivered 2026-08-18: the
  center gained the component-form characterization
  `laplacian_mulVec_eq_zero_iff_forall_reachable` (`Spectral.lean`,
  no connectivity hypothesis); the bridge
  `ker_laplacian_eq_ker_supportGraph_lapMatrix` plus the inherited
  `finrank_ker_laplacian_eq_card_supportGraph_components` and the
  transported `laplacian_ker_basis` live in `SimpleGraphAdapter.lean`;
  QA in `SpectralGraph/KernelBridge_QA.lean` (connected coherence +
  disconnected count/basis computed).
- [x] **4. Potential solvability (the hinge)** — delivered 2026-08-18:
  `exists_laplacian_mulVec_eq_of_sum_eq_zero` and
  `exists_laplacian_mulVec_eq_single_sub_single` in `Spectral.lean`,
  by the constructive eigenbasis route (decision recorded below); QA
  in `SpectralGraph/PotentialSolvability_QA.lean` with positive,
  non-zero-sum negative, and disconnected zero-sum negative witnesses.
- [x] **5. Effective resistance, uniqueness, and energy** — delivered
  2026-08-18: `Scaffold/Mathlib/GraphTheory/Electrical.lean`
  (`IsEffectiveResistance` by the potential equation, the total
  `effectiveResistance` with agreement theorems and a QA-witnessed
  junk fallback, reachability-strength uniqueness, both energy
  identities, symmetry, nonnegativity, `R u u = 0`); QA in
  `SpectralGraph/EffectiveResistance_QA.lean` (values computed on the
  edge and path, energy cross-check, fallback and same-component
  witnesses). Delivery note below.
- [ ] **6. The one-sided Dirichlet bound** — not started.

### 1. The `SimpleGraph → WAdj` interoperability adapter — ✅ delivered

Deliver `SimpleGraph.toWAdj` with proved agreement on the objects Scaffold
already defines: `deg = G.degree`, symmetry, `laplacian (toWAdj G) =
G.lapMatrix ℝ`, and `boundary S` equal to the edge count across the cut.

This is first because it is the highest-leverage item in the document and
because everything after it is easier once Mathlib's graphs are addressable.
It converts every theorem already in the repository into something an outside
user can call, and it is the prerequisite that makes
[the traction plan](../docs/traction-plan.md) executable at all. Folding in
the neutral re-export of Mathlib's unweighted kernel and component results
belongs here rather than in a slice of its own.

### 2. The weighted kernel characterization — ✅ delivered

`laplacian_ones_in_kernel` (`Spectral.lean:127`) gives one direction. The
converse — kernel elements are constant on connected components, hence
constant when the graph is connected — is absent from Scaffold.

**Connectivity predicate: decided, not open.** Adopt Mathlib's
`SimpleGraph.Connected` (`Path.lean:762`, a structure over `Preconnected` +
`Nonempty V`, with `Reachable u v` defined as `Nonempty (G.Walk u v)` at
`Path.lean:643`) through a `supportGraph A` with
`Adj i j ↔ i ≠ j ∧ 0 < A i j`. A native predicate over `WAdj` was the
alternative and is rejected. Requires `0 ≤ A i j` throughout, matching
`laplacian_psd`'s existing `hnonneg` hypothesis (`Spectral.lean:687`);
negative weights would contribute to the quadratic form while staying
invisible to the support graph.

**Prove it directly; do not transport.** Mathlib's theorem is about
`G.lapMatrix ℝ`, a *different* (unweighted) matrix, so there is no transport
by equality. Bridging would first require
`laplacian A *ᵥ f = 0 ↔ (supportGraph A).lapMatrix ℝ *ᵥ f = 0`, whose route
runs through exactly the termwise argument the direct proof needs anyway —
`quadForm = 0` forces `A i j * (f i - f j)^2 = 0`, hence `f i = f j` wherever
`0 < A i j`. Transport would save Mathlib's four-line walk induction while
adding positive-semidefinite zero-iff plumbing. Read `LapMatrix.lean:110-127`
for the pattern; do not import from it.

**This step yields uniqueness only.** It characterizes the kernel. It does not
establish that any particular equation has a solution. See
[step 4](#4-potential-solvability-the-hinge).

### 3. The kernel-equality bridge — ✅ delivered

Prove

```
ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)
```

and inherit `lapMatrix_ker_basis` and
`card_ConnectedComponent_eq_rank_ker_lapMatrix` for the weighted Laplacian in
one step. These are genuinely absent from Scaffold and not cheap to re-derive:
they give a basis for the kernel and identify its dimension with the number of
connected components. After step 2 both sides are known to equal "constant on
components," so the bridge itself is short.

**Delivered 2026-08-18.** The "constant on components" weighted side needed
one more center fact than step 2's *connected* statement:
`laplacian_mulVec_eq_zero_iff_forall_reachable` (no connectivity
hypothesis), whose new direction — component-constant ⇒ kernel — goes
entrywise through the diffusion-form identity `laplacian_mulVec_apply`
(`(L *ᵥ f) i = ∑ j, A i j * (f i − f j)`). With it, the bridge is the
predicted one-rewrite composition with Mathlib's iff; the dimension
count and basis transfer exactly as scoped (`Basis.map` over
`LinearEquiv.ofEq`). One unforeseen prerequisite, recorded here for
reuse: Mathlib's `lapMatrix` API requires `DecidableRel G.Adj`, which
instance search cannot see through the `supportGraph` projection —
provided once as `supportGraphAdjDecidable` (via `Real.decidableLT`).
QA computes the disconnected fixture's component count to `2`
independently of the transferred theorem and pins both basis vectors
to the component indicators.

### 4. Potential solvability (the hinge) — ✅ delivered

Prove that for a connected graph and any **zero-sum demand** `b` (that is,
`∑ i, b i = 0`), there exists `f` with `laplacian A *ᵥ f = b`. Then specialize
to `b = e u - e v`, which is zero-sum by inspection.

**Delivered 2026-08-18.** Route decision recorded before stating (as
required): the **constructive eigenbasis** route. The pin still has no
ready-made `range = (ker)ᗮ` lemma over these function types
(re-surveyed this run), while the center's proved eigenbasis algebra
(`eigvecOf_inner`, `eigvecOf_complete`, `mulVec_eigenvectorBasis`) and
the step-2 kernel theorem are exactly the needed tools, so the witness
`f = ∑_{λᵢ ≠ 0} (vᵢ ⬝ᵥ b / λᵢ) • vᵢ` is load-bearing on both. New
center declarations: `exists_mulVec_eq_of_zero_comp` (general spectral
inversion, with the helper `mulVec_eigvecOf_sum_apply`),
`exists_laplacian_mulVec_eq_of_sum_eq_zero`,
`exists_laplacian_mulVec_eq_single_sub_single`, plus the reciprocity
identity `laplacian_dotProduct_mulVec` and its kernel certificate
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` — the latter two power
the QA's proved unsolvability witnesses (non-zero-sum demand on the
connected edge; zero-sum cross-component demand on the disconnected
fixture via the component indicator), so both hypotheses are shown
load-bearing, not assumed. No axioms. One implementation note: `rw
[Finset.mul_sum]` fails to fire on some instance-heavy goals where
`simp only [Finset.mul_sum]` succeeds; the proofs use the latter.

This is the step the original document omitted. Two routes:

1. **Orthogonality.** For symmetric `L`, `range L = (ker L)ᗮ`, so zero-sum
   demand is exactly the solvability condition once step 2 identifies
   `ker L` with the constants. A search of the pin did not surface a
   ready-made `range = (ker)ᗮ` lemma, so this route carries real plumbing
   cost.
2. **Constructive, via Scaffold's own spectral tools.** The eigenbasis
   orthonormality/completeness and projector algebra in `Spectral.lean` are
   already proved. Build `f` explicitly as `∑_{λᵢ ≠ 0} (⟨vᵢ, b⟩ / λᵢ) • vᵢ`
   and verify `L f = b` using zero-sum to kill the kernel component.

Route 2 reuses the center and is likely cheaper. Decide and record which
before writing the statement.

### 5. Effective resistance, uniqueness, and energy — ✅ delivered

With step 4 in hand, define resistance by the equation it solves rather than
by a pseudoinverse — the Mathlib pin has **no** Moore–Penrose pseudoinverse
(verified 2026-08-18: a repository-wide search finds one hit, a comment at
`LinearAlgebra/Matrix/NonsingularInverse.lean:17` stating pseudoinverses are
not considered):

```
IsEffectiveResistance A u v r  ↔  ∃ f, laplacian A *ᵥ f = e u - e v ∧ f u - f v = r
```

- **Existence** of a witness: step 4.
- **Uniqueness** of `r`: step 2 — two solutions differ by a kernel element,
  which is constant, so `f u - f v` agrees.
- Together these justify a total function `effectiveResistance A u v : ℝ`.
- **Energy identity** `R u v = quadForm (laplacian A) f`, one step from
  `laplacian_quadForm` and the defining equation; then symmetry
  `R u v = R v u`, nonnegativity, and `R u u = 0`.

Split across two runs if the definitional plumbing and the energy identity do
not land together.

**Delivered 2026-08-18, both halves in one run.** Mathlib survey recorded
before stating (per the operating instructions): no effective-resistance
or "resistance" declaration anywhere in the pin, confirming the
potential-equation route. Two strengthening deviations from the sketch,
both cheaper than the sketch itself: uniqueness is stated at
**reachability-pair** strength (via step 3's component-form
characterization rather than the connected form), so it holds within a
component of a disconnected graph — QA pins `effectiveResistance 0 1 = 1`
on the disconnected fixture, beyond the connected theorems' reach; and
the energy identity is stated at the **solution level**
(`quadForm (laplacian A) f = f u − f v` for *any* solution, no
hypotheses — the definitional unfolding of `quadForm` plus
`Matrix.dotProduct_single`), with the function-level `R u v = energy`
form as its corollary. The total function is defined by classical
choice with junk value `0` when the relation is unsatisfiable; the
fallback is not hidden — `effectiveResistance_eq_zero_of_not_exists`
states it, and the QA proves on the disconnected fixture that no
cross-component value exists while the function reads `0` (fallback,
not measurement). The diagonal is characterized exactly
(`IsEffectiveResistance A u u r ↔ r = 0`) with no hypotheses at all.
Named residual, cheap and deferred: definiteness (`R u v = 0 ↔ u = v`
on a reachable pair) — the natural completion of nonnegativity, kept
out of this run by the one-step scope fence.

### 6. The one-sided Dirichlet bound — not started

For any test potential `f`, `R u v ≥ (f u - f v)^2 / quadForm (laplacian A) f`.
This is Cauchy–Schwarz over the energy identity and needs no attained
supremum, so it survives the deferral below and is worth having: it is the
direction every application actually uses to lower-bound resistance.

## Deferred and removed

- **Full Rayleigh monotonicity — deferred.** It needs the Dirichlet principle
  as an attained variational characterization, which is the shape this
  repository already found hard enough to admit as an axiom
  (`lambda2_variational`). Step 6 keeps the cheap half.
- **Foster's theorem — removed from the program.** `∑ over edges,
  A i j * R i j = n - 1` needs a rank/trace identity of pseudoinverse
  character. Earlier text called it a "gated stretch," which understated it by
  a wide margin. Re-admit only as its own proposal, with a dependency path.

**Net effect if the program lands:** the adapter, the kernel characterization
and its basis/rank family, solvability, a total `effectiveResistance` with the
energy identity, and the one-sided Dirichlet bound. Axiom count unchanged at
18. Axis 6 moves off 0.5 on genuine usable coverage, and axis 1 and the
interoperability score move with step 1.

## Operating instructions for an autonomous run

Applies to any run directed at this document.

- **One step per run.** Steps are numbered above; a run advances exactly one
  and stops. Landing a single step cleanly is a success, not a partial result.
  Do not continue into the next step because time remains. Steps 4 and 5 may
  each need more than one run.
- **No new axioms.** Every step here is hard crust. If a step cannot be
  proved, record the precise obstruction in `docs/6_SGT_BACKLOG.md` and stop
  rather than admitting anything.
- **Do not define resistance before step 4 lands.** Existence is not implied
  by the kernel characterization; see [Corrections](#corrections). A
  definition resting on an unsatisfiable hypothesis admits vacuous proofs that
  still typecheck.
- **Survey Mathlib before proving.** Search the pin under
  `.lake/packages/mathlib/` for an existing result before writing a proof.
  Record what the survey finds either way — but judge transport on cost, not
  reflex: an upstream theorem about a *different* matrix may cost more to
  bridge than to reprove, as step 2 illustrates.
- **QA is part of the step.** Add QA under `Scaffold/QA/SpectralGraph/`
  exercising a positive witness and a negative witness that shows the
  hypothesis is load-bearing (for step 2: a connected graph, and a
  disconnected one where a non-constant kernel element exists; for step 4: a
  non-zero-sum demand with no solution).
- **Do not re-score `docs/7_SGT_RADAR.md`** unless the step's proof lands and
  its QA passes. The duplication finding above is the exception: record it
  against the interoperability axis whenever it is read, since it is an
  evidence correction rather than a score increase.
- Standard repository rules in `AGENTS.md` continue to apply, including the
  execution-plan and activity-log obligations.

## What not to grow

- **QA breadth on modules that already have it.** `Exhaustive_QA` is past
  the point of diminishing returns; further sweeps add declarations, not
  assurance.
- **Axis 8 (adjacent systems).** Deliberately gated, and the gate is
  correct.
