# Proposal: Resolvent Calculus for PSD Matrices

**Status:** **Delivered in full (program complete) — all four steps
(0–3) delivered 2026-08-19/20, zero new axioms throughout** (count
stays 13). Step 0: the C*-algebra thread is **structurally
inapplicable**; the from-scratch bridge is proved instead, as this
proposal's own contingency prescribed. Step 1: invertibility + the
resolvent identity. Step 2: the norm bound and the Lipschitz bound
(the recorded energy-route deviation). Step 3 (2026-08-20):
injectivity — the proposal's final item, completing the program.
Priority was **High**. Assistant's assessment of project
direction, requested 2026-08-19, promoted from `sgt-gaps.md` item 2.
Authorized no axiom admissions or external publication beyond what its
own steps delivered.

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

None — the program is complete (all four steps delivered; see the
delivery records). Follow-ons live elsewhere: the
sorted-eigenvalue-transfer residual is named for the mixing-time
program's similarity transfer, and `discharge-perturbation-axioms.md`'s
Weyl target consumes the delivered operator-norm bridge.

## Step 3 delivery record (2026-08-20)

Delivered in `Analysis.OperatorTheory.Resolvent`, the proposal's item
5, **zero new axioms** (count stays 13; `#print axioms` on all three
new public theorems reads only `propext, Classical.choice,
Quot.sound`) — exactly the route the Open-next-step section recorded:

- `eq_of_inv_add_one_eq_inv_add_one` (the core algebraic form): if
  both `+1` shifts are invertible and `(A + 1)⁻¹ = (B + 1)⁻¹`, then
  `A = B`. Proof: the Step-1 resolvent identity's left side collapses
  to `0`, so `(A+1)⁻¹ * (B − A) * (B+1)⁻¹ = 0`; multiplying through by
  `A + 1` on the left and `B + 1` on the right cancels both invertible
  outer factors (`Matrix.mul_nonsing_inv`, `Matrix.nonsing_inv_mul`),
  leaving `B − A = 0`. The two determinant hypotheses are exactly what
  the cancellation consumes — load-bearing, not decorative (the QA
  guard below refutes the hypothesis-free form).
- `resolvent_map_injective_of_quadForm_nonneg` (the proposal's item-5
  shape): on matrices with nonnegative quadratic form,
  `A ≠ B → (A + 1)⁻¹ ≠ (B + 1)⁻¹`; both determinant hypotheses are
  supplied by Step 1's `isUnit_det_add_one_of_quadForm_nonneg`.
- `inv_add_one_eq_inv_add_one_iff_of_quadForm_nonneg` (packaged): the
  resolvent map is injective *as an iff* — resolvent equality is a
  certificate of matrix equality, for contrapositive consumers.

**QA** (`OperatorTheory/Resolvent_QA.lean`, +19 declarations by the
scoreboard metric, 94 in file): the injectivity instantiated at **two
distinct PSD pairs** — `lap2` vs `0` and the less degenerate `lap2` vs
`mat2` (neither zero; `mat2`'s PSD proved from the sum-of-squares
identity `xᵀ(mat2)x = (x₀+x₁)² + x₀² + x₁²`) — with both resolvents
independently pinned by left-inverse witnesses
(`(mat2+1)⁻¹ = (1/8)!![3,−1;−1,3]`, a new fixture alongside the
existing `(lap2+1)⁻¹ = (1/3)!![2,1;1,2]`), distinctness verified by
entries (`1/3 ≠ 0`, `2/3 ≠ 3/8`), and bridge lemmas rewriting the
theorem's output to exactly those numeric facts; the packaged iff
consumed contrapositively; and the **invertibility guard**: the
hypothesis-free implication "equal resolvents → equal matrices" is
**refuted** at `A = −1` vs `B = −1 + E` with `E = !![0,1;0,0]`
nilpotent — `A + 1 = 0` and `B + 1 = E` are both singular (the
latter's determinant `0` by a zero row), so both resolvents are the
junk inverse `0` and equal, while the matrices differ (`A 0 1 = 0 ≠ 1
= B 0 1`).

## Step 2 delivery record (2026-08-19)

Delivered in `Analysis.OperatorTheory.Resolvent`, at the proposal's
item shapes 2 and 4, **zero new axioms** (count stays 13; `#print
axioms` on all three new public theorems reads only `propext,
Classical.choice, Quot.sound`):

- **Recorded route deviation** (the proposal sketched "the delivered
  bridge plus the shifted/inverted eigenvalue transfer"): delivered via
  the *energy route* instead. For `y = (M + t•1)⁻¹ *ᵥ x`, the
  quadratic-form hypothesis gives `t ‖y‖² ≤ quadForm M y + t‖y‖² =
  y ⬝ᵥ x ≤ ‖y‖‖x‖` (dot-product Cauchy–Schwarz, transported to
  `EuclideanSpace` inner products through the bridge's own spine),
  packaged by `ContinuousLinearMap.opNorm_le_bound` exactly as Step 0's
  upper direction was. This yields the **strictly stronger
  general-`t`** statement `‖(M + t•1)⁻¹‖ ≤ t⁻¹` with **no symmetry
  hypothesis** (the same strengthening style as Step 1's invertibility
  theorem — only the quadratic form at the resolvent's own argument is
  ever evaluated). The sorted-eigenvalue transfer for inverted
  matrices is thereby not needed by this step at all; it remains a
  named residual for a consumer that genuinely needs eigenvalue pins
  of transformed matrices (the mixing-time program's similarity
  transfer is the named such consumer). A bonus strengthening
  recorded in passing: the underlying energy inequality
  `t • (y ⬝ᵥ y) ≤ y ⬝ᵥ x` holds for *any* `t` (strict positivity
  enters only at the division step).
- `l2OpNorm_inv_add_smul_one_le_inv_of_quadForm_nonneg` (general `t`,
  above); `l2OpNorm_inv_add_one_le_one_of_quadForm_nonneg` (item 2,
  the `t = 1` instance); and `l2OpNorm_resolvent_sub_le_of_quadForm_nonneg`
  (item 4): the resolvent map is `1`-Lipschitz in the operator norm on
  the quadForm-nonneg matrices — the Step-1 resolvent identity, the
  scoped `NormedRing` submultiplicativity (`norm_mul_le`, resolving
  under `Matrix.L2OpNorm` — the instance Step 0 verified), and the norm
  bound on both factors. Load-bearing on Step 1 throughout: both
  determinant hypotheses are supplied by
  `isUnit_det_add_one_of_quadForm_nonneg`, and the factoring *is*
  `resolvent_identity_sub`.

**QA** (`OperatorTheory/Resolvent_QA.lean`, +57 declarations, 87 in
file): the proposal's three QA items plus tightness. The norm bound is
**attained, with route agreement**: `‖(L(K₂)+1)⁻¹‖ = 1` exactly, where
the theorem's energy route and the eigenvalue-bridge route meet at the
same value — the resolvent `(1/3)!![2,1;1,2]`'s spectrum `{1/3, 1}`
pinned from trace/determinant/sortedness (independent of both routes),
`‖·‖ = 1` by both bridge directions; likewise the general-`t` instance
`‖(L + 2•1)⁻¹‖ = 1/2` exactly (spectrum `{1/4, 1/2}`, `(1/8)!![3,1;1,3]`
pinned by an independent left-inverse witness). The Lipschitz bound
instantiated at `A = L`, `B = 0` with **both sides independently
pinned**: the difference `!![-1/3,1/3;1/3,-1/3]`'s spectrum
`{-2/3, 0}` pinned, norm `2/3`; `‖L‖ = 2` (spectrum `{0, 2}`); the
instantiated theorem therefore reads `2/3 ≤ 2` — a reversed or
badly-factored statement would produce a falsehood. **Shift
load-bearing (the proposal's QA item 3):** the invertible PSD
`(1/4)I` *without* the shift has `‖A⁻¹‖ = 4 > 1` (inverse `4I` by an
independent left-inverse witness, norm by the pinned spectrum `{4,4}`),
so the unshifted bound is refuted numerically. **Hypothesis
load-bearing (beyond the proposal's list):** the symmetric non-PSD
`-(3/4)I` has `+1` shift equal to `(1/4)I` — invertible, inverse norm
`4 > 1` — while `quadForm (-(3/4)I) ![1,0] = -3/4 < 0` exhibits the
violated hypothesis; dropping the PSD assumption breaks the bound.

## Step 0 delivery record (2026-08-19)

**The spike, decisive negative on the C*-algebra thread:**
`IsSelfAdjoint.spectralRadius_eq_nnnorm` is stated
`{A : Type*} [CStarAlgebra A] (ha : IsSelfAdjoint a) :
spectralRadius ℂ a = ‖a‖₊`, and `CStarAlgebra` extends
`NormedRing`, `StarRing`, `CompleteSpace`, `CStarRing`,
`NormedAlgebra ℂ A`, `StarModule ℂ A`. For `Matrix n n ℝ` the scoped
`Matrix.L2OpNorm` instances `NormedRing` and `CStarRing`
(`Matrix.instCStarRing`) resolve, but `CStarAlgebra (Matrix (Fin 2)
(Fin 2) ℝ)` fails to synthesize — elaboration-verified; the missing
piece is exactly `NormedAlgebra ℂ (Matrix (Fin 2) (Fin 2) ℝ)` (real
matrices are not a complex algebra, so this is a structural
obstruction, not an instance-search gap that a different search could
close; the ℝ→ℂ complexification route would be its own project).

**Fallback adopted and delivered** (this proposal's own contingency):
the from-scratch finite-dimensional bridge in the new module
`Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent`, proved from the
already-shelf eigenbasis machinery:

- `abs_eigvalOf_le_l2OpNorm` (lower direction): the unit eigenvector,
  packaged as a `EuclideanSpace` element, is scaled by `λ` under
  `toEuclideanCLM M`; `ContinuousLinearMap.le_opNorm` bounds every
  image norm, and `Matrix.cstar_norm_def` (`‖M‖ = ‖toEuclideanCLM M‖`,
  `rfl`) transfers to the matrix norm. Bookkeeping lemma:
  `norm_euclidean_sq` (the Euclidean norm of a packaged plain function
  squared is its dot product, through
  `EuclideanSpace.inner_eq_star_dotProduct`).
- `l2OpNorm_le_of_abs_eigvalOf_le` (upper direction): `‖M *ᵥ y‖²`
  resolves by Parseval (`dotProduct_eigvecOf`) and the eigenaction
  identity (`dotProduct_eigvecOf_mulVec`) to `∑ i, λ i² * c i²`, which
  is termwise bounded by `c² * ∑ i, c i² = c² ‖y‖²`; then
  `ContinuousLinearMap.opNorm_le_bound`.
- Sorted-spectrum forms `abs_evals_le_l2OpNorm` /
  `l2OpNorm_le_of_abs_evals_le`, consuming the new mirror lemma
  `evals_first_le_eigvalOf` added to `GraphTheory.Spectral` (the
  first-sorted-entry lower bound, mirror of `eigvalOf_le_evals_last`),
  and the packaged extremal identity `l2OpNorm_eq_max_abs_evals`
  (`‖M‖ = max |evals hM 0| |evals hM last|`) — this file's Step-0
  target statement.

**QA** (`Scaffold/QA/OperatorTheory/Resolvent_QA.lean`, 30
declarations): the `!![2,1;1,2]` fixture with its spectrum `[1, 3]`
pinned from trace/determinant/sortedness (independently of the
bridge); both directions instantiated to pin `‖mat2‖ = 3` exactly (the
literature spectral-norm value for this fixture); the packaged max
form instantiated at `max 1 3 = 3`; the **negative witness** `¬(‖mat2‖
≤ 1)` — bounding by one eigenvalue's absolute value instead of all of
them is refuted, so the `∀ k` hypothesis is load-bearing.

`#print axioms` on every public theorem: only `propext,
Classical.choice, Quot.sound`. Zero new axioms (count stays 13).

## Step 1 delivery record (2026-08-19)

Delivered in the same module, both at the proposal's item shapes:

- `isUnit_det_add_smul_one_of_quadForm_nonneg`: for any matrix with
  everywhere-nonnegative quadratic form and `t > 0`, `M + t • 1` has
  unit determinant. Route: a kernel vector `v ≠ 0` would force
  `quadForm M v + t * (v ⬝ᵥ v) = 0` with the first term nonnegative
  and the second positive — no symmetry hypothesis needed (the
  statement is *stronger* than the proposal's sketch, which assumed
  PSD of a symmetric matrix; the argument only evaluates the
  quadratic form at the one hypothetical kernel vector).
  `isUnit_det_add_one_of_quadForm_nonneg` is the `t = 1` instance
  (item 1).
- `resolvent_identity_sub` (item 3): `(A+1)⁻¹ − (B+1)⁻¹ = (A+1)⁻¹ *
  (B − A) * (B+1)⁻¹` for any two matrices whose `+1` shifts have unit
  determinants — pure `nonsing_inv` algebra (`mul_sub`,
  `nonsing_inv_mul`, `mul_nonsing_inv`), no symmetry or PSD enters.

**QA:** the `K₂` Laplacian `!![1,-1;-1,1]` (PSD through the center's
`laplacian_psd` at the unit-edge adjacency, transferred along the
computed `laplacian edge2 = lap2`); `IsUnit (L + 1).det` by the
theorem, cross-checked against the computed determinant `3 ≠ 0`; the
general-`t` instance at `t = 2` (determinant `8`); the
**shift-load-bearing witness**: the *unshifted* Laplacian has
determinant exactly `0`, so PSD alone gives no invertibility — the
`+1` is not decorative; and the resolvent identity at `A = L`, `B =
0` with `(L+1)⁻¹` computed to `(1/3)!![2,1;1,2]` by an independent
left-inverse witness, both sides of the identity independently
computed from the raw definitions to the same literal matrix
`!![-1/3, 1/3; 1/3, -1/3]` — a wrong factoring (order or sign) would
fail the check.
