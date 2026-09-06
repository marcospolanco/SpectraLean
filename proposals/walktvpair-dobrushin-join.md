# Proposal: The `walkTVPair`–Dobrushin Engine Join

**Status:** COMPLETE (delivered 2026-09-06 by run `20260906T002623Z-run-1`,
session `ses_f8c5e42b3ffe41RPhC77iBiw0k`; delivery record below)

## Why this, why now

`proposals/directed-uniform-mixing-time.md` promoted the Dobrushin
contraction mechanism to the matrix level (`Mixing.lean`'s
`tvDobrushinCoeff`, `tvDistance_vecMul_le_tvDobrushinCoeff`,
`tvDobrushinCoeff_pow_add_le`) and priced the undirected join as "a
priced follow-on if a consumer names it". The consumer is the one the
handoffs have been naming since: the QA axis's randomized half and the
sharp `|λ₂| = α` layer both route through the two-start distance, and
every audit-program terminal entry since 2026-09-05 has named this
join the most concretely priced frontier. The audit method having no
remaining target, deferral, or survey gap (2026-09-06), this is the
next increment.

## The identity

`walkTVPair A t = tvDobrushinCoeff ((walkTransitionMatrix A) ^ t)` —
**no symmetry hypothesis**: `walkDistribution A t x` is
`(Mᵀ)^t *ᵥ eₓ` by definition, which is the `x`-column of `(Mᵀ)^t`,
which is the `x`-row of `((Mᵀ)^t)ᵀ = M^t` (by `Matrix.transpose_pow`
and involutivity). So the `sup'`-defining summands of the two sides
are *the same functions of `p : V × V`*, and the identity is a
`Finset.sup'_congr`. At a row-stochastic `M` the right side is LPW's
`d(t)` of the chain `M` drives — the engine's own docstring says so.

## The re-routes (public statements unchanged)

1. **`walkTVPair_submul`** (LPW's `d(s+t) ≤ d(s)d(t)`): the bespoke
   ~30-line chain (evolution equations, mass conservation, the
   walk-level contraction instantiated at the pair of `s`-step laws)
   becomes three identity rewrites plus the engine's
   `tvDobrushinCoeff_pow_add_le`, whose `hrow` is discharged by the
   existing `walkTransitionMatrix_row_sum` (so `hd` stays used).
2. **`tvDistance_pow_walkTransitionMatrixTranspose_mulVec_le`** (the
   sharp walk-level Dobrushin contraction): the bespoke ~50-line
   sign-statistic proof becomes the vecMul↔mulVec transpose bridge
   (`(Mᵀ)^t *ᵥ ω = ω ᵥ* M^t`, valid for any `M`) plus the engine's
   `tvDistance_vecMul_le_tvDobrushinCoeff` plus the identity.

The walk-level layer keeps its public statements, its hypothesis
shapes, and its names; only the proofs change, from bespoke
duplications of the engine's mechanism to engine instantiations.

## QA obligation

The identity is a new public theorem: pin both sides at the delivered
`triAdj` fixture, where `Mixing_QA.lean` already pins
`walkTVPair triAdj 1 = 1/2` and `walkTVPair triAdj 2 = 1/4` — the new
pins evaluate the engine side to the same closed forms, and the
submultiplicativity-attained instance at `triAdj` (`tri_pair_two_eq_QA`)
becomes an instance of the engine route.

## Delivery record

DELIVERED at the full priced scope. Shelf changes
(`Oversmoothing.lean`): the identity
`walkTVPair_eq_tvDobrushinCoeff` (the one new public theorem;
functional count 1312 → 1313); the `walkTVPair_submul` re-route (the
bespoke evolution/mass/contraction chain → three identity rewrites +
`tvDobrushinCoeff_pow_add_le`, `hd` discharged through
`walkTransitionMatrix_row_sum`); the sharp walk contraction re-route
(the bespoke sign-statistic proof → the `(Pᵀ)ᵗ *ᵥ ω = ω ᵥ* Pᵗ`
transpose bridge + `tvDistance_vecMul_le_tvDobrushinCoeff` + the
identity); the retired private pairing core
`tvDistance_mulVec_le_pair` deleted with a tombstone note — the
mechanism lives in the engine's own private core. Every existing
public statement, name, and hypothesis shape unchanged; both re-routed
theorems verified at `#print axioms` = the standard three.

QA (`Mixing_QA.lean`'s new `EngineJoin` section, +3): the engine-side
identity pins at the delivered `triAdj` fixture —
`tvDobrushinCoeff (walkTransitionMatrix triAdj ^ 1) = 1/2` and
`… ^ 2 = 1/4`, matching the pinned `walkTVPair` values through the
join — and the submultiplicativity-attained instance
`1/4 = 1/2 · 1/2` re-derived. QA count 6384 → 6387.

Technique findings:

1. **The identity needs no symmetry**: the transpose-power bridge
   works at any weighted adjacency — `walkDistribution`'s definition
   already IS the column-row transpose. The uniform-mixing delivery's
   "candidate future join" framing understated this: the join is
   strictly more general than the undirected family it was priced on.
2. **`Matrix.transpose_pow` points `(M^k)ᵀ = Mᵀ^k`** — the `←`
   direction is the one that eliminates `(Pᵀ)^t`-shaped terms.
3. **The scoped `*ᵥ`/`ᵥ*` notations require `open scoped Matrix`**
   in any consumer file — the spike's first error class.
