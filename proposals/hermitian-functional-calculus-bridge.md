# Proposal: A Scaffold–Mathlib Hermitian Functional-Calculus Bridge

**Status:** COMPLETE — Steps 0+1 (all of 1–3) delivered in one run
(2026-08-25, run `20260825T125600Z-run-1`); see the delivery record at
the end. Steps 4–5 remain separate gated proposals, now unblocked at
their own gates (the complex-half precondition discharged by the QA
witness). Per the project's own priority discipline this queues behind
whatever is currently the Active priority table's High row (at proposal
time, the Hoffman independence-number bound
[expander-independence-number-bound.md](expander-independence-number-bound.md));
start this only once that table is empty of higher rows, or on
deliberate reprioritization. This document authorizes no Lean changes,
axiom admissions, commits, or external publication on its own — Step 0
(confirming the exact Mathlib API shape below) must land before Step 1
begins.

## The obligation this discharges

Scaffold's spectral machinery has grown several independent, hand-built
notions of "a function of a symmetric matrix" — `spectralProjector`/
`bandProjector` (`GraphTheory/Spectral.lean:346`, `GraphTheory/Band.lean:102`),
the Chebyshev/polynomial filter layer (`GraphTheory/PolyFilter.lean`),
the heat semigroup (`GraphTheory/Heat.lean`), and the Tikhonov shrinkage
filter (`GraphTheory/Tikhonov.lean`) — each proved independently from
the eigenbasis rather than as instances of one shared calculus. Mathlib
already has the general tool these all specialize:
`Mathlib/LinearAlgebra/Matrix/HermitianFunctionalCalculus.lean`
(`Matrix.IsHermitian.cfc`, a continuous functional calculus at finite
spectrum via unitary diagonalization `A = U·diag(λ)·U*`, giving
`f(A) = U·diag(f(λᵢ))·U*`) — present in the pinned Mathlib but omitted
from `docs/8_MATHLIB_COVERAGE_MAP.md`'s original survey (corrected
2026-08-25 alongside this proposal). This is a real gap in the
project's own map of its foundation, not just an opportunity.

## What this is, precisely — and what it is not

**Is:** an adapter and consolidation layer — a stable Scaffold-facing
functional-calculus interface, specialized to the real-symmetric and
complex-Hermitian matrices this shelf actually uses, proved compatible
with the existing eigenbasis-filter machinery, with one existing
definition recovered as a calculus instance to prove the bridge is
real rather than decorative.

**Is not**, and must not be described as, any of the following in any
delivery record, docstring, or summary:
- **Not** a re-proof of the finite-dimensional spectral theorem from
  scratch — Mathlib's `cfc` is consumed, not rebuilt.
- **Not** a path to retiring Scaffold's ten explicit axioms. Two
  (`perron_frobenius`, `primitive_power_tendsto`) concern nonnegative,
  generally non-Hermitian and non-normal matrices — Hermitian spectral
  calculus is not their missing foundation. The remaining eight are
  scalar/matrix concentration inequalities (Hoeffding, Bernstein, Azuma
  families) — a different mathematical domain entirely, untouched by
  this bridge. **Zero of the ten axioms are addressed by this
  proposal**, and no delivery record may claim otherwise.
- **Not** a replacement for Krylov/Chebyshev approximation. The
  calculus gives exact semantics and proof rules for `f(A)`; it does
  not make approximate/iterative computation of `f(A)` unnecessary —
  `Krylov.lean`'s Kaniel–Paige program and `PolyFilter.lean`'s
  Chebyshev layer remain the computational-approximation machinery,
  now with a calculus to state their *target* against more cleanly, not
  a replacement for their reason to exist.
- **Not** a claim of "universal downstream application." It is a
  shared vocabulary for the Hermitian/normal case specifically; the
  directed axis (Perron–Frobenius, PageRank, DirectedMixing, the
  Magnetic Laplacian's own non-Hermitian companion questions) still
  needs its own, separate bridges where it needs them at all.

## Assessed from

`.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/HermitianFunctionalCalculus.lean`
(`cfcAux`, `eigenvalues_eq_spectrum_real`, the finite-spectrum-implies-
continuous argument that lets `cfc` accept a bare `ℝ → ℝ` function) and
`Mathlib/LinearAlgebra/Matrix/Spectrum.lean` (the underlying eigenbasis
this shelf's own `Spectral.lean` is already built on — same foundation,
different API surface); `Scaffold/Mathlib/GraphTheory/Spectral.lean`
(`spectralProjector`, `bandProjector`, `dotProduct_eigvecOf_filter` — the
existing arbitrary-filter expansion this bridge must agree with),
`Tikhonov.lean` and `Heat.lean` (the two candidate recovered instances),
and `Magnetic.lean` (`magneticLaplacian_isHermitian` — a genuinely
complex-Hermitian object already proved hypothesis-free, the shelf's
first real consumer of the complex half of this calculus).

## Build order (Steps 1–3 only; Steps 4–5 are separate, gated proposals)

1. **Import and expose Mathlib's Hermitian calculus** as a thin Scaffold
   wrapper (`GraphTheory.FunctionalCalculus` or similar — Step 0 decides
   the exact namespace and whether real-symmetric and complex-Hermitian
   share one definition or two thin specializations of `cfc`).
2. **Prove the eigenvector action**: `f(A) v_i = f(λ_i) • v_i` at each
   basis eigenvector, in Scaffold's own `eigvecOf`/`eigvalOf` naming —
   the load-bearing bridge everything downstream needs.
3. **Prove equality with Scaffold's existing arbitrary-filter expansion**
   (`dotProduct_eigvecOf_filter` in `Spectral.lean`) — the calculus's
   `f(A)` and the shelf's hand-built filter sum must be the *same
   operator*, not merely analogous. This is the proposal's actual
   mathematical content and its falsifiability test: a wrong calculus
   specialization or a mismatched eigenbasis convention breaks this
   equality loudly.

Steps 4 (recovering an existing definition — Tikhonov or Heat — as a
calculus instance) and 5 (a genuinely complex Magnetic Laplacian
consumer) are **not authorized here**. Each is a separate named
consumer of Steps 1–3 and gets its own document once this foundation
lands, per the one-shape-per-proposal discipline this shelf already
follows for Krylov/Chebyshev and the PF family:
- [hermitian-calculus-consumer-tikhonov-heat.md](hermitian-calculus-consumer-tikhonov-heat.md)
- [hermitian-calculus-consumer-magnetic.md](hermitian-calculus-consumer-magnetic.md)

## Step 0 (required before Step 1)

- Confirm the exact real-symmetric vs. complex-Hermitian API split in
  `HermitianFunctionalCalculus.lean` — does one `cfc` definition cover
  both via a type-class parameter, or are they genuinely separate
  declarations needing separate Scaffold wrappers?
- Confirm `Matrix.IsHermitian.cfc`'s exact continuity/domain hypotheses
  match "any `ℝ → ℝ` function" as the finite-spectrum argument claims,
  with no hidden global-continuity requirement that would block the
  discontinuous-at-zero filters Scaffold sometimes uses (Tikhonov's
  hard-filter limit, `tikhonovShrinkage_tendsto_zero`, approaches a
  discontinuity as a *limit*, not as a filter value — check this
  doesn't collide with `cfc`'s domain).
- Price the eigenbasis-convention reconciliation cost between Mathlib's
  `Spectrum.lean` eigenbasis and Scaffold's own `eigvecOf`/`eigvalOf` —
  `Spectral.lean` was already built by bridging these once; reuse that
  precedent rather than re-deriving it.

### Step 0 verdict (delivered 2026-08-25, run `20260825T125600Z-run-1`, from the pinned sources before any shelf Lean was written)

1. **One definition, no split.** `Matrix.IsHermitian.cfc` is stated at
   `variable {n 𝕜 : Type*} [RCLike 𝕜]` — the *same* declaration
   (file line 163) covers real-symmetric (`𝕜 = ℝ`) and
   complex-Hermitian (`𝕜 = ℂ`) input, with `RCLike.ofReal` the only
   seam. Consequence for the bridge: **one thin real-symmetric
   wrapper** at the shelf's `Matrix V V ℝ`/`IsSymm` convention
   suffices; no second wrapper is added for the complex half, and the
   gated magnetic consumer (whose own precondition is "the
   complex-Hermitian half confirmed working by Step 0's API-split
   check") is unblocked to use `cfc` at `𝕜 = ℂ` directly — the whole
   supporting API (`eigenvectorUnitary`, `spectral_theorem`,
   `eigenvalues_eq_spectrum_real`) is stated at the same `RCLike`
   generality.
2. **No continuity hypothesis on the bare-function form.** The
   protected def takes `(f : ℝ → ℝ)` with no hypothesis at all; its
   docstring records exactly the finite-spectrum argument (every
   function is continuous on a finite spectrum). The generic
   `cfc f A hA` API's `ContinuousOn f (spectrum ℝ A)` side condition is
   discharged for matrices by `continuousOn_iff_continuous_restrict`
   on the finite spectrum (file line 171 does exactly this inside
   `cfc_eq`). A discontinuous-at-a-point filter is therefore admitted
   *as a value* — `cfc` only ever evaluates `f` at eigenvalues — so
   Tikhonov's limit-shaped discontinuity concern does not collide with
   the calculus's domain.
3. **Eigenbasis reconciliation is free.** Scaffold's `eigvecOf`/
   `eigvalOf` (`Spectral.lean:235,240`) are *literally* Mathlib's
   `eigenvectorBasis`/`eigenvalues` under `isHermitian_of_isSymm` — the
   same objects `cfc` conjugates by, not a rival basis needing an
   adapter. The entire glue needed is two existing `Spectrum.lean`
   lemmas: `eigenvectorUnitary_apply` (entries of the unitary are the
   basis vectors) and `star_eigenvectorUnitary_mulVec` (`U* *ᵥ v_k =
   π.single k 1`). Cost: zero new reconciliation machinery.

   One provenance repair found during the check: this proposal's
   "Assessed from" section places `dotProduct_eigvecOf_filter` in
   `Spectral.lean`; it lives in `Tikhonov.lean` (line 194). The
   equality target is unchanged.

## QA obligations (draft — refine after Step 0)

1. A small fixture (K₂ or a 3×3 diagonal matrix) where `f(A)` computed
   via the new calculus wrapper is checked equal, entrywise, to the
   same function applied via Scaffold's existing `spectralProjector`/
   filter-sum route — two independent API paths to one value, this
   session's established discipline.
2. The eigenvector-action identity instantiated at a non-basis vector
   (a linear combination of two eigenvectors), confirming linearity is
   inherited correctly, not just the single-eigenvector case.
3. A boundary case at a repeated eigenvalue (multiplicity ≥ 2), since
   `cfc`'s unitary-diagonalization route and Scaffold's own eigenbasis
   machinery may make different but compatible choices of basis within
   the eigenspace — confirm `f(A)` agrees regardless of which orthonormal
   basis either route picks.

## Acceptance bar

- Step 0 delivers a written verdict on the three checks above before
  any shelf Lean is written.
- Zero new axioms — this consumes Mathlib's proved `cfc`, adds no
  admission of its own.
- No delivery record, docstring, or summary describes this as
  addressing any of Scaffold's ten axioms, replacing Krylov/Chebyshev,
  or as a "universal" bridge — see "What this is not" above; this is a
  hard acceptance-bar item, not a style note.
- `docs/8_MATHLIB_COVERAGE_MAP.md`'s Hermitian-calculus correction
  (already applied 2026-08-25) is cross-referenced, not re-litigated.

## Companion

[Verify Build Completeness](verify-build-completeness.md),
`docs/8_MATHLIB_COVERAGE_MAP.md` (the corrected survey row),
`proposals/decidable-spectral-certificates.md` (the prior session's
similar Mathlib-bridge precedent).

## Delivery record (Steps 0+1, 2026-08-25, run `20260825T125600Z-run-1`)

**Delivered — pure hard crust, zero new axioms (count stays 10;
`#print axioms` via `wip/hfc_axcheck.lean` on all 25 audited
declarations — 7 public + 18 QA: exactly `propext, Classical.choice,
Quot.sound`, every one — zero contact with any of the ten admitted
axioms, as the acceptance bar requires).** QA 2173 → 2189
(`FunctionalCalculus_QA` a new file at 16 by the generator metric).

**The module** `Scaffold/Mathlib/GraphTheory/FunctionalCalculus.lean`
(namespace `SpectralGraphTheory`; minimal imports Spectral + Tikhonov +
Mathlib's `HermitianFunctionalCalculus`; the umbrella importing it):

- **Step 1** — `spectralCalc M hM f := (isHermitian_of_isSymm hM).cfc f`,
  the thin wrapper at the shelf's real-symmetric convention; bare
  `ℝ → ℝ` functions, no continuity hypothesis (the Step-0 verdict's
  finding that `Matrix.IsHermitian.cfc` is already bare-function);
  **no second complex wrapper** (the Step-0 API-split verdict: Mathlib's
  `cfc` is one `RCLike`-generic definition).
- **Step 2** — `spectralCalc_mulVec_eigvecOf`: the hypothesis-free
  eigenvector action `f(M) *ᵥ v_k = f (eigvalOf M hM k) • v_k`,
  derived through the entry form + `eigvecOf_inner` (orthonormality),
  not the unitary action — a deliberate route choice.
- **Step 3** — three layers of the equality with the shelf's
  expansion: `spectralCalc_apply` (the entry form
  `f(M) a b = ∑ i, f (λᵢ) vᵢa vᵢb`, proved from the `cfc`
  definition's triple product by controlled rewrites — the
  atom-bridging `have … := rfl` technique for the WithLp-coe /
  type-ascription mismatch is this delivery's sharpest pin lesson);
  `spectralCalc_mulVec_apply` (the action form = the filter-sum vector
  of `dotProduct_eigvecOf_filter`); and
  `dotProduct_eigvecOf_spectralCalc_mulVec` — the shelf workhorse
  consumed **verbatim** as the coefficient bridge.
- The "one existing definition recovered" clause —
  `spectralCalc_indicator_eq_spectralProjector`: the shelf's
  hand-built `spectralProjector M hM c` *is* the calculus at the
  indicator of `(· ≤ c)`.
- `spectralCalc_id` (the calculus identity, via the spectral-theorem
  entry computation).

**QA (+16, all three mandated obligations + the complex witness):**
(A) two API paths to one value on the reused `diag13` fixture —
`fc_diag13_calc` for *arbitrary* `f` from the entry form + Band_QA's
eigenbasis pins (sign-free summands), the projector route through the
recovery theorem at the indicator, both pinned to `!![1,0;0,0]`, plus
the f-dependence fence (`3 ≠ 9` at entry (1,1), refuting any
`f`-independent implementation in proved form) and the zero-function
edge; (B) the non-basis eigenvector action — `fc_action_add`
generically at `v_i + v_j` and the `![1,1]` action by two independent
routes (pinned matrix raw vs the expansion theorem with
sign-cancelling coefficients); (C) the repeated-eigenvalue boundary on
`2 • 1` — `f(2•1) = f 2 • 1` by two genuinely independent routes
(entry form + completeness, no basis choice anywhere; raw unitary
conjugation, no completeness anywhere), the eigenvalue listing itself
derived from `star_mul_self_mul_eq_diagonal`; (D) the complex-half
witness `fcM2c_cfc_id` — `cfc` at `𝕜 = ℂ` on `[[0,i],[-i,0]]` through
the generic `cfc_id'`, discharging the gated magnetic consumer's
"complex half confirmed working" precondition with an artifact.

**Verification:** spike first (`wip/hfc_spike.lean`, several rounds to
green before any module touched; the complex witness spiked separately
in `wip/hfc_cx.lean`); `lake env lean` zero errors/warnings on the
module and the QA file; explicit `lake build` targets ✔ (2301/2301,
2304/2304); **full `lake build` ✔ (2385 targets, "Build completed
successfully"; the +~120-target jump over the previous 2264 is the
previously-unbuilt Mathlib CFC closure pulled by the new import, not
new Scaffold surface) immediately followed by
`check_build_completeness.py` — 106/106 fresh, 0 stale, 0 missing,
exit 0** (the mandatory post-build fence); `lint_axioms` (10),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(2189/10/0, idempotent by md5). Records updated: this document,
`proposals/README.md` (the Medium row retired to Delivered), README
(2189; the status paragraph's bridge clause; the module-table row),
the radar (QA axis synced 2173/54 → 2189/55, held 4.0), the scoreboard
(the verification row), `index/map/spectral_graph.md` (the
FunctionalCalculus section + 7 declaration rows), the coverage map's
cross-reference sentence, the umbrella `Scaffold.lean`, the execution
plan, and the activity log.

**Acceptance-bar compliance:** no delivery record, docstring, or
summary describes this as addressing any of the ten axioms (zero
`#print axioms` contact, machine-checked), as replacing
Krylov/Chebyshev, or as a universal bridge — the module docstring
carries the three NOT-clauses verbatim. The coverage map's correction
is cross-referenced (its row now notes the bridge delivered), not
re-litigated.

**Pin-technique list (for future consumers):** the two coe forms of
`eigenvectorBasis` application (Mathlib's `eigenvectorUnitary_apply`
produces the `WithLp.equiv` form; the shelf's `eigvecOf`
type-ascription produces the bare form — defeq, invisible to `ring`'s
atom abstraction): bridge with per-atom `have h : LHS = RHS := rfl`
then `rw [h]`, never `simp only [eigvecOf]` + `ring` (which strands
the summand); `Matrix.mul_apply` must NOT be simp-cascaded with
`Matrix.mul_diagonal` (double-`mul_apply` into a double sum) — outer
`mul_apply` as `rw`, then per-summand `mul_diagonal`/`star_apply`/
`star_trivial`/`comp_apply`; `linear_combination`'s "ring failed"
printout shows the *residual* (goal-difference minus the claimed
combination), so a wrong coefficient reads as a nonzero residual —
compute coefficients from the post-rewrite goal, and remember the
claimed expression's own atoms are *not* reduced by hypotheses; the
`show … from rfl` trap: `show A = B from rfl` elaborates `B` up to
unification with `A` (both become identical) — a *theorem-dependent*
bridge must be stated as a `have` with `by`-proof or with explicit
independent elaboration; `fin_cases` on `Fin 2` ext-binders leaves
beta-redexes `(fun i => i) ⟨0, _⟩` — close per-branch with a
definitional `show` at numeral indices; `Matrix.diagonal_apply_ne`
takes `d` explicitly (rw with only the hypothesis feeds `h` into
`d`'s slot — write `Matrix.diagonal_apply_ne _ h`).

**Priced follow-ons:** Steps 4–5 exactly as their own gated stubs name
them — recovering Tikhonov *or* Heat as a calculus instance (now
unblocked; the smaller reconciliation gap is Tikhonov's, since
`tikhonovShrinkage`'s minimizer is *defined* by the eigenbasis formula
`dotProduct_eigvecOf_filter` mediates, while `heatKernel` routes
through `NormedSpace.exp`), and the magnetic heat propagator as the
first complex consumer (its complex-half precondition discharged by
this delivery's QA witness).
