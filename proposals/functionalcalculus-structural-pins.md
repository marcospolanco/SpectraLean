# Proposal: The Functional-Calculus Structural Facts' Positive Pins

**Status:** COMPLETE (delivered in the opening run, run
`20260907T044936Z-run-1`, session `ses_f85e4fd87ffeIAk10HRoxt2F0J`;
delivery record below)

## Why this, why now

The prior terminal handoff's next cluster by size (per
`wip/census_20260907_post3.txt`, 44 never-touched): **the five
FunctionalCalculus structural theorems** — the calculus-bridge layer
spanning the real wrapper (`spectralCalc`) and the complex magnetic
propagator (`magneticHeat`), never consumed by any QA proof. The prior
handoff's selection keys (cluster size first) make this the natural
next target; the pins method's fifth application (after Tikhonov 11,
mixing-time interfaces 10, sparsification 9, Magnetic 6).

The gap is real: `FunctionalCalculus_QA.lean`'s sections A–F pin the
bridge's entry form (`fc_diag13_calc`/`fc_lapK2_calc`), the Tikhonov
and Heat reconciliations, and the π = −2 fence — all *beside* the five
structural theorems. The identity-function fix, the coefficient
bridge, the calculus-route resolvent twin, the propagator's entry
form, and the eigenbasis action were referenced by no QA proof term.

**SGT leverage:** the functional calculus is the join layer between
the shelf's eigenbasis machinery and Mathlib's `cfc` — every
calculus-semantic statement downstream (heat, Tikhonov, band filters,
the magnetic propagator) routes through it. The strongest pins here
are two-route joins: each puts two independent proof technologies
(calculus algebra vs eigenbasis arithmetic; calculus vs adjugate) on
one pinned concrete fact, so a divergence between the routes would
surface as two provable contradictory statements.

## Step 0: the census (exact)

The five never-consumed theorems:
`dotProduct_eigvecOf_spectralCalc_mulVec`, `magneticHeat_apply`,
`magneticHeat_mulVec_eigenvectorBasis`, `spectralCalc_id`,
`spectralCalc_tikhonovShrinkage_eq_smul_inv'`.

## Step 1: the pins (9 QA theorems, one section)

1. **The identity-function two-route join (`fcp_id_pin`)**: the
   theorem route (`spectralCalc_id`) says `f(L) = L` at `f = id`; the
   eigenbasis route (`fc_lapK2_calc`) computes `f(L)` at `id` as the
   pinned `!![1, -1; -1, 1]`. Composing: the `K₂` Laplacian IS the
   pinned matrix — each route failing independently breaks its own
   half.
2. **The coefficient bridge at the squared spectrum**
   (`fcp_coeffBridge_pin`, with the `fcp_sq_mulVec` value pin): the
   propagated vector `![2, -2]` pinned through the eigenbasis route,
   then the bridge's equality instantiated so both sides carry the
   SAME eigenvector — the `λ = 0` mode killed by `f(λ) = 0` on the
   right, the `λ = 2` mode by `f(L) *ᵥ y` on the left.
3. **The two-technology resolvent join**: `fcp_resolvent_calculus_pin`
   — the primed theorem's calculus route (`cfc_inv`; no matrix
   inverse, determinant, or cancellation anywhere) composed with the
   eigenbasis-pinned filter matrix DERIVES the shifted Laplacian's
   inverse as the concrete `!![2/3, 1/3; 1/3, 2/3]`, the value
   normally computed by adjugate arithmetic; `fcp_resolvent_raw` —
   the same value by plain `inv_def` + `det_fin_two` +
   `adjugate_fin_two`, touching no calculus anywhere.
4. **The magnetic propagator's structural pins** (general statements —
   the derivation IS the content; no eigenvalue identification
   needed): `fcp_magHeat_hermitian` — the propagator is Hermitian
   through the entry form's exact `U a i * conj (U b i)` placement
   (a swapped convention would derive the transpose instead);
   `fcp_magHeat_diag_real` — the diagonal is real, each entry a sum of
   real decay factors times `|U a i|²` via `z * conj z = ↑(normSq z)`;
   `fcp_magHeat_eigenpair` — the spectral-mapping content: for every
   basis index, `e^{-t·λⱼ}` is realized as an eigenvalue of the
   propagator, the nonzero eigenvector exhibited through
   `Basis.ne_zero` on the orthonormal eigenbasis (a wrong decay
   factor or wrong eigenvalue index breaks the exhibited equation);
   `fcp_magHeat_basis_semigroup` — the semigroup ON THE BASIS
   VECTORS through the action theorem three times (distinct from the
   already-consumed matrix-level `magneticHeat_mul_magneticHeat`).

## QA obligation

The pins are the QA. No shelf change; zero axiom contact.

## Delivery record (2026-09-07)

DELIVERED at the full designed scope in the opening run: 9 QA theorems
in `FunctionalCalculus_QA.lean`'s new `StructuralPins` section
(54 → 63 by the generator metric; QA 6606 → 6615), QA-only, zero axiom
contact (`#print axioms` via `wip/fcpins_axcheck.lean` on all 9 —
every one exactly `propext, Classical.choice, Quot.sound`; no
`-- @refutes` tags — theorem instantiations of an all-proved shelf;
the 24-tag independence check unchanged and clean).

**Consumption closure, verified by the tool**: the census re-run
(`wip/census_20260907_post4.txt`) shows exactly the 5 targeted
theorems leaving the inert set — value-consumed 1313 → 1318,
never-touched 44 → 39, every other module's inert set unchanged: no
bonus, no collateral.

Verification: spike-first (`wip/fcpins_spike.lean` — green after five
fix rounds; the recorded traps: the `Tikhonov_QA` fixtures' namespace
needing its own `open` inside the new section (mixed resolution makes
`rw` patterns fail opaquely); the bare `1 • 1` smul defaulting to `ℕ`
against the theorem's `(1 : ℝ)`; `Complex.starRingEnd_apply` not
existing in this snapshot — the `star`-vs-`conj` bridge being
`Complex.star_def`, with `map_mul`/`Complex.conj_conj`/
`Complex.conj_ofReal` already starRingEnd-native;
`mul_assoc` FORWARD (not backward) for the `z * conj z`
reassociation; `decide` getting classically stuck on `Real.decidableEq`
in matrix-literal entry goals — the `if_pos rfl`/`if_neg (by decide)`
route instead; and `congr 1` under a `Complex.ofReal` wrapper emitting
a stray `Try this: ring_nf` hint that pollutes the module output —
the `apply congrArg Complex.ofReal; apply congrArg Real.exp` cascade
instead). The landed module elaborates with zero errors/warnings;
explicit build ✔; **full `lake build` + `check_build_completeness.py`
— 135 source files, 135 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 axioms unchanged); `check_refutation_independence`
(24-tag clean); `check_public_reachability` (63 modules);
`check_citations`; `check_markdown_links`; `check_qa_name_uniqueness`
(the new `fcp_*` names collision-free); `check_backlog_freshness`
clean; scoreboard regenerated (6615) with the verification row; map
freshness exit 0 after the 6606 → 6615 stats sync in both map data
tables and SVG regeneration (49 stations, no status change — none
owed).

Remaining risk: none owed — QA-only, no axiom disposition changed, no
public statement changed. QA proves consequences relative to the
substrate; it does not prove the substrate (no axiom touched). Honest
scope: the real-wrapper pins at the `K₂` Laplacian fixture and one
shift (`π = 1`); the magnetic-propagator pins are general-statement
derivations; the eigenpair pin's nonzeroness routes through the
eigenbasis orthonormality rather than an explicit vector.
