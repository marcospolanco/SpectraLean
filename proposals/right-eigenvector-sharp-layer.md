# Proposal: The Right-Eigenvector Forms of the Sharp Layer

**Status:** COMPLETE — DELIVERED in the opening run (2026-09-06, run
`20260906T105019Z-run-1`, session `ses_f89c8b23effeTZ0dTR5mzKQYrT`);
the doubly-stochastic follow-on (its own priced item below) DELIVERED
same day, run `20260906T110500Z-run-1` (delivery records below)

## Why this, why now

The sharp `|λ₂| ≤ α` layer proposal
(`sharp-second-eigenvalue-layer.md`) closed COMPLETE the same day —
with one priced follow-up outstanding in its Slice 4 scope note: the
layer's statements are all at the left-eigenvector (`vecMulLinear`)
convention, the shelf's stationarity convention, and
"right-eigenvector forms (`mulVecLin`, `G *ᵥ v = c • v`) need either
the doubly-stochastic case or the charpoly-invariance route." Of the
standing frontiers named by the terminal handoff, this is the only
one that is not decision-gated (the QA axis's randomized half awaits
a design decision; the reverse TV → χ² calculus has no consumer
named).

**Consumer gate discharged by the parent proposal's own priced
follow-up** — and by the convention mismatch the shelf lives with:
stationarity is a left statement, power iteration a right one; every
`M^t *ᵥ x`-shaped consumer (the power-method family, `Derived`'s
drift pipelines) consumes eigenvalue control at the right convention.
Haveliwala–Kamvar state the bound convention-free.

## What the route is (spiked before commitment)

The priced "charpoly-invariance" route is heavier than needed. The
left/right spectrum coincidence is constructible from two
`ToLinearEquiv` bridges plus `det_transpose`:

- `Matrix.exists_mulVec_eq_zero_iff : (∃ v ≠ 0, M *ᵥ v = 0) ↔ det M = 0`
- `Matrix.exists_vecMul_eq_zero_iff` (its left twin)
- `Matrix.mulVec_transpose : Mᵀ *ᵥ v = v ᵥ* M`
- `Matrix.det_transpose`

Chain: a right-eigenpair `M *ᵥ v = c • v` at `v ≠ 0` is a nonzero
kernel vector of `c • 1 − M`, forcing `det (c • 1 − M) = 0`, hence
(by transpose) `det (c • 1 − Mᵀ) = 0`, hence a nonzero kernel vector
`μ` of `c • 1 − Mᵀ`, i.e. `Mᵀ *ᵥ μ = c • μ`, i.e. (the transpose
bridge) a left-eigenpair `μ ᵥ* M = c • μ`. No charpoly, no field
extension — one reusable general theorem:

**`Matrix.hasEigenvalue_mulVecLin_iff_vecMulLinear`** (any field, any
square matrix): the left and right eigenvalue sets coincide. This is
the eigen-API upgrade of the same left/right duality the
`walkTVPair`–Dobrushin join exploited at the law level.

## Scope (this run)

1. The general bridge (stated at `Field K`, proved by the chain
   above; home: `PageRank.lean`'s new section, its first consumer —
   generality noted in the docstring).
2. The right-convention ceiling:
   `googleMatrix_hasEigenvalue_mulVecLin_abs_le` (eigen-level) and
   `googleMatrix_abs_mulVec_eigen_le` (raw `G *ᵥ v = c • v` form) —
   the bridge composed with Slice 4's eigen-level ceiling.
3. The right-convention strictness:
   `googleMatrix_hasEigenvalue_mulVecLin_abs_lt_of_primitive` and its
   raw form — the bridge composed with Slice 5.
4. QA in `PageRank_QA.lean`: the two-cycle's right `-α` pair
   attained (`G(4/5) *ᵥ (1,−1) = −4/5 • (1,−1)` — the ceiling
   attained at the right convention on the periodic chain); the
   primitive fixture's right `-α/2` pair (`G(4/5) *ᵥ (5,−9) =
   −2/5 • (5,−9)` — strictness instantiated); the bridge itself
   pinned at the walk matrix (right `-1/2` pair `(1,−2)` ⟹ left
   `HasEigenvalue` at `-1/2`); and two honest boundary witnesses —
   the right-eigenvector's NONZERO mass (why the left route's mass
   lemma cannot transfer: `(5,−9)` has mass `−4`) and the
   no-right-shadow witness (`(5,−9)` is NOT a `-1/2` right-eigenpair
   of the walk — teleportation shifts right-eigenvectors off the
   shadow, unlike the left case).

## Out of scope, priced

- The doubly-stochastic right-shadow (apply the left theorems at
  `A := Pᵀ` under `∀ j, ∑ i, P i j = 1`): nearly free but niche;
  route sketched here for a future run.
- The right-eigenvector shadow in general: FALSE (the QA
  no-right-shadow witness is the evidence; the mechanism — the
  teleportation term is rank-one on the right and moves
  eigenvectors — recorded in the module docstring).

## QA obligation

As in scope item 4; the boundary witnesses are the adversarial
content — they pin exactly why this delivery needed a new route (the
left machinery's two engines, mass and shadow, both fail at the
right convention).

## Delivery record (2026-09-06)

DELIVERED at the full scope in the opening run: seven public theorems
in `PageRank.lean`'s new `RightEigenvalue` section (functional
1336 → 1343) and eleven QA theorems plus the `prPrimRV` fixture in
`PageRank_QA.lean`'s new `RightEigenQA` section (QA 6420 → 6431),
zero axiom contact (`#print axioms` via `wip/righteigen_axcheck.lean`
on all 18 — every one exactly `propext, Classical.choice,
Quot.sound`).

The content:

1. `exists_mulVec_eq_smul_iff_det` / `exists_vecMul_eq_smul_iff_det`
   — the raw-pair↔determinant factoring lemmas (`M` has a nonzero
   right (resp. left) eigenpair at `c` iff `det (c•1 − M) = 0`).
2. **The bridge** `hasEigenvalue_mulVecLin_iff_vecMulLinear` — a
   square matrix's left and right eigenvalue sets coincide, stated
   for any field and any square matrix (reusable beyond the Google
   family; the eigen-API upgrade of the vecMul↔mulVec transpose
   duality the mixing layer's engine join exploits at the law
   level).
3. The right-convention ceiling (eigen-level
   `googleMatrix_hasEigenvalue_mulVecLin_abs_le` + raw
   `googleMatrix_abs_mulVec_eigen_le`) and strictness (eigen-level +
   raw `_abs_lt_of_primitive` / `_abs_mulVec_eigen_lt_of_primitive`)
   — Haveliwala–Kamvar at the power-method convention.

The QA: the two-cycle's right `-α` pair ATTAINED (`G(4/5)` pinned in
closed form, `G *ᵥ (1,−1) = −4/5 • (1,−1)`, ceiling instantiated),
the primitive fixture's right `-α/2` pair with strictness
`|−2/5| < 4/5` through the raw right theorem, the bridge pinned at
the walk matrix (raw right pair `(1,−2)` ⟹ left `HasEigenvalue` at
`−1/2`, load-bearing on the general bridge at a non-Google matrix),
and the two boundary witnesses: `prPrimRV_mass_ne` (the right
eigenvector's mass `−4 ≠ 0` — the left mass lemma cannot transfer)
and `prPrim_no_right_shadow_QA` (`(5,−9)` is NOT a `−1/2` right
eigenpair of the walk — the left shadow lemma is genuinely FALSE at
the right convention).

Technique findings:

1. **The priced "charpoly-invariance" route was heavier than
   needed**: the same conclusion follows from
   `Matrix.exists_mulVec_eq_zero_iff` (a `ToLinearEquiv` lemma) +
   `Matrix.det_transpose` + `Matrix.mulVec_transpose` — the
   kernel-level statement, no polynomial machinery.
2. **The transitive-import boundary trap, new instance**: the spike
   reached `exists_mulVec_eq_zero_iff` through the QA module's
   import closure, so the missing shelf import
   (`Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`) only surfaced at
   the landed module's build — spike against the LANDED module's own
   import list, not the QA module's.
3. **`Iff.mpr` vs `.mp` discipline under `(M := …)` ascription**:
   with the matrix ascription the two directions are easy to swap
   under refactor; the fix pattern is to build the det-hypothesis as
   an explicit `have` and convert through `det_transpose` backwards
   (`rw [← Matrix.det_transpose, ← hEq]`) rather than forward.
4. **`Module.End.hasEigenvector_iff`'s first conjunct is eigenspace
   MEMBERSHIP**, not the apply-equation — destructure with
   `obtain ⟨-, hv0⟩` and take the equation from
   `Module.End.HasEigenvector.apply_eq_smul`; construct with
   `show _ ∈ eigenspace; rw [mem_eigenspace_iff]`.

## Delivery record — the doubly-stochastic follow-on (2026-09-06)

DELIVERED same day (run `20260906T110500Z-run-1`): five public
theorems in `PageRank.lean`'s `RightEigenvalue` section (functional
1343 → 1348) and ten QA theorems plus two fixtures in
`PageRank_QA.lean`'s new `DoublyStochasticQA` section (QA
6431 → 6441), zero axiom contact (`#print axioms` via
`wip/dblstoch_axcheck.lean` on all 15 — every one exactly
`propext, Classical.choice, Quot.sound`).

The content — **on a column-stochastic walk (`∀ j, ∑ i, P i j = 1`),
the two engines that fail at the right convention in general DO hold
on the right**:

1. `walkTransitionMatrix_transpose_eq_of_col_sum_one` — setup: the
   transposed walk is its own walk matrix (its row sums are the
   walk's column sums).
2. `googleMatrix_transpose_eq_of_col_sum_one` — setup: the
   transport `googleMatrix Pᵀ α = (googleMatrix A α)ᵀ`, entrywise.
3. `googleMatrix_mulVec_mass_zero` — the right mass lemma.
4. `googleMatrix_mulVec_shadow` — the right shadow
   `P *ᵥ v = (c/α) • v`.
5. `googleMatrix_mulVec_of_shadow` — the right attainment twin.

All three transports go through the transpose bridge
(`Matrix.mulVec_transpose`) — no new mathematics beyond the priced
route.

QA: the two-cycle's `-1` right shadow DELIVERED by the theorem from
the pinned right `-α` pair, and round-tripped back to the pinned
Google pair through the twin; the end-mix `0`-pair at the complete
graph; and the NON-SYMMETRIC doubly-stochastic `Fin 3` fixture
`prDbl3` (the cyclic chain `(1/2,1/2,0)` shifted): `¬ IsSymm` pinned,
doubly stochastic at the walk level pinned — on `Fin 2` doubly
stochastic forces symmetry, so this is the smallest witness that the
hypothesis class is genuinely larger than the symmetric cone.

Technique findings:

1. **The Fin 3 literal's tail-tail is a CONSTANT function**: the
   junk `vecHead (vecTail fun _ => a)` is definitionally `a` — the
   def names `Matrix.vecHead, Matrix.vecTail` added to the norm_num
   set close it (no entry pins needed).
2. **`Matrix.IsSymm` is the equality `M = Mᵀ`, not a pointwise
   predicate** — extract entries by `rw [h]` into a two-sided entry
   goal, then `Matrix.transpose_apply`.
3. **A hand-arithmetic error caught by the spike** (the audit
   method's Step-0 discipline applied to fixture design): the
   fixture's rows already sum to one, so `walkTransitionMatrix prDbl3
   = prDbl3` by the row-sum bridge — the first draft's `3/2` degrees
   were wrong, and the wrong column sums would have produced a
   false QA statement.
