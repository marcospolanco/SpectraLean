# Proposal: Resolvent Calculus for PSD Matrices

**Status:** Proposed; priority **High**. Assistant's assessment of project
direction, requested 2026-08-19, promoted from `sgt-gaps.md` item 2.
Authorizes no Lean changes, axiom admissions, or external publication.

Companion to `sgt-gaps.md` (the triage document this was promoted from)
and `docs/1_STRATEGY.md`'s leverage test. No backlog gate applies — this
composes directly with the already-proved PSD/eigenbasis machinery in
`GraphTheory.Spectral`, no scope decision needed.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard operator-theory sources
(Kato). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean` (`laplacian_psd`,
the eigenbasis/`evals` machinery), a search of
`.lake/packages/mathlib/Mathlib/Analysis/Normed/Algebra/` and
`Mathlib/Algebra/Group/Units` for existing resolvent/operator-norm
machinery (`Ring.inverse`, `IsUnit` confirmed present; no PSD-specific
norm bound or finite-dimensional operator-norm bridge found), and a
2026-08-19 spot-check into
`Mathlib/Analysis/CStarAlgebra/{Spectrum,ContinuousFunctionalCalculus/Order}.lean`
that surfaced `IsSelfAdjoint.spectralRadius_eq_nnnorm` — a promising but
**unverified-in-context** thread for the operator-norm bridge specifically
(see Calibration).

## External consumer

The resolvent `(A + I)⁻¹` is standard wherever a spectral gap cannot be
assumed — numerical linear algebra (iterative solvers), control theory
(the resolvent of a generator matrix), and as a gap-free alternative to
spectral projection generally. Real and well-established, independent of
anything else in this repository's current scope.

## Recommendation

For PSD `A, B : Matrix V V ℝ`, prove:

1. `A + I` is invertible (`IsUnit (A + 1)`, or the equivalent
   `Matrix.NonsingularInverse` route).
2. `‖(A + I)⁻¹‖ ≤ 1` in the operator norm (`Matrix.L2OpNorm`).
3. The resolvent identity: `(A+I)⁻¹ − (B+I)⁻¹ = (A+I)⁻¹ * (B − A) *
   (B+I)⁻¹`.
4. The Lipschitz bound: `‖(A+I)⁻¹ − (B+I)⁻¹‖ ≤ ‖A − B‖`.
5. Injectivity: `A ≠ B → (A+I)⁻¹ ≠ (B+I)⁻¹`.

## Why this is cheap

`A + I` for PSD `A` is strictly positive definite (eigenvalues shift from
`[0, ∞)` to `[1, ∞)`), so invertibility is a direct corollary of the
already-proved eigenbasis machinery — no PSD hypothesis subtlety beyond
what `laplacian_psd`-style arguments already handle. Items 3 and 5 are
elementary ring/field algebra once item 1 is in hand. **Items 2 and 4 are
the real content** — they need the finite-dimensional operator-norm
bridge (relating `Matrix.L2OpNorm` to eigenvalues), which has zero
existing coverage in Scaffold and is only tentatively promising in
Mathlib (see Calibration). This is why the item is rated small overall
despite two of its five bullets being genuinely new work: the norm bridge
is a one-time cost that pays for both bullets at once, not two separate
costs.

## Calibration — the norm bridge is the whole risk

`Mathlib.Analysis.CStarAlgebra.Spectrum` has
`IsSelfAdjoint.spectralRadius_eq_nnnorm` — a general C*-algebra fact that
a self-adjoint element's norm equals its spectral radius. This is
*exactly* the shape of bridge needed (operator norm ↔ largest-magnitude
eigenvalue), and `Matrix V V ℝ` under `Matrix.L2OpNorm` is plausibly an
instance of the relevant C*-algebra classes. **This was found by a
keyword search, not verified by elaboration** — Step 0 below is not
optional. Two live risks: (a) the instance chain (`NormedRing`,
`StarRing`, `CStarRing`, `ContinuousFunctionalCalculus`) may not resolve
for `Matrix V V ℝ` at the `L2OpNorm` instance Scaffold already uses
elsewhere (Weyl's admitted axiom imports the same file, for the same
reason, and has not verified this either); (b) even if it resolves, the
bridge speaks in terms of `spectrum ℝ A` / `nnnorm`, not Scaffold's own
`evals`/`eigvalOf` API, and connecting the two needs its own small lemma.

## Build order

### Step 0: Survey and spike (mandatory before Step 1)

Write a standalone lemma attempting
`(hA : A.IsSymm) → ‖A‖ = |evals hA i|` for the extremal index (largest or
smallest eigenvalue) using the C*-algebra thread above. Record whether it
elaborates, what instances it actually needed, and the exact statement
shape reachable. If the thread does not pan out, record the precise
obstruction and fall back to a from-scratch finite-dimensional argument
(the operator norm of a symmetric matrix over `Fin n → ℝ` equals its
largest singular value, provable directly from the eigenbasis expansion
already on the shelf — more code, but no exotic instance search).

### Step 1: Invertibility and the resolvent identity

Items 1 and 3 above — pure algebra once Step 0's norm bridge choice is
settled (these two do not actually depend on the bridge, so they may be
delivered even if Step 0's spike is inconclusive).

### Step 2: The norm bound and Lipschitz bound

Items 2 and 4, via whichever route Step 0 settled on.

### Step 3: Injectivity

Item 5 — a one-line consequence of Step 1.

## QA plan

- Positive witness: a concrete PSD `A` (e.g., `laplacian` of a small
  fixture), `(A+I)⁻¹` computed and its norm bound checked numerically.
- Lipschitz witness: two concrete PSD matrices `A, B`, the bound checked
  to hold with a nontrivial (non-degenerate) right-hand side.
- Negative witness: the bound refuted numerically when `A + I` is
  replaced by `A` alone (not shifted), showing the `+ I` shift is
  load-bearing, not decorative.

## Operating instructions for an autonomous run

- One step per run; Step 0 must land and be recorded before Step 2 begins.
- **No new axioms.** If Step 0's spike fails and the from-scratch fallback
  also proves substantially harder than expected, stop and record the
  obstruction in `docs/6_SGT_BACKLOG.md` rather than admitting anything —
  this proposal's entire cost case rests on the norm bridge being
  tractable one way or another.
- Survey Mathlib precisely (exact lemma signatures) before each step.

## Open next step

Step 0's survey/spike — unblocked now, no operator decision required.
