# Proposal: The Sharp-Layer Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered in the opening run's continuation, run `20260906T113139Z-run-1`, session `ses_f89c8b23effeTZ0dTR5mzKQYrT`; delivery record below)

## Why this, why now

The sharp `|λ₂| ≤ α` family — Slices 1–5 plus the three follow-ons of
`proposals/sharp-second-eigenvalue-layer.md` and
`proposals/right-eigenvector-sharp-layer.md`, sixteen public theorems
delivered 2026-09-06 — carries QA pins at both fixtures but **no
adversarial fence pass**: no hypothesis-necessity witness exists for
any clause except the two incidental ones (`prCyc_not_primitive` for
strictness's `hprim`; the `prPrim` boundary witnesses for the
doubly-stochastic `hcol`). This run's theorem-level QA-mention survey
(a new survey key — the module-level keys are exhausted) found the
family's theorems QA-mentioned through pins only; the audit method's
standing pattern (the census, then hypothesis-form fences) has not
been applied. **SGT leverage:** the family is the directed-rate
program's capstone — its two engines (mass lemma, shadow lemma) are
the mechanism every ceiling/strictness statement routes through.

## Step 0: the clause census (hand-checked)

Load-bearing clauses with NO negative witness (the fence targets):

1. **The mass lemma `googleMatrix_vecMul_mass_zero`**: `hc : c ≠ 1`
   (at `c = 1` the stationary pair has nonzero mass).
2. **The shadow lemma `googleMatrix_vecMul_shadow`**: `hc` (same
   witness); `hα : α ≠ 0` (at `α = 0` the shadow eigenvalue `c/α` is
   junk while the genuine `0`-pair's walk action is not zero).
3. **The ℓ¹ peripheral bound `abs_vecMulEigen_le_one`**: `hnn`
   (signed `M`), `hrow` (non-stochastic), `hμ0` (junk corner).
4. **The ceiling `googleMatrix_abs_eigen_le`**: `hα : 0 < α` (at
   `α = −1` the off-one eigenvalue `2` exceeds `|α|`); `hnn` (signed
   adjacency, eigenvalue `−12/5`); `hμ0` (junk corner); `hc`.
5. **The attainment twin `googleMatrix_vecMul_of_shadow`**: `hmass`
   (a walk pair of nonzero mass fails to map through).
6. **The characterization iff `googleMatrix_abs_eigen_eq_alpha_iff`**:
   `hc1 : c ≠ 1` (at `c = α = 1` the left side holds at the
   stationary pair while the right side's mass-zero peripheral pair
   does not exist).
7. **The sign-rigidity engine `vecMul_sign_coherent_of_abs_eq_pow_pos`**:
   `hrow` (a non-stochastic `M` with `M² > 0` and a mixed-sign
   peripheral pair at `−1`); `hk` (the swap: mixed-sign peripheral
   pair, no strictly positive power — reusing `prCyc_not_primitive`).
8. **The doubly-stochastic right trio**: `hcol` — the `prPrim`
   boundary witnesses already refute the dropped conclusions (the
   nonzero mass, the no-shadow); this audit wraps them in
   hypothesis-form fence statements.

Already fenced (recorded, not repeated): strictness's `hprim`
(`prCyc_not_primitive`); the doubly-stochastic `hcol` at the
`prPrim` boundary witnesses (this audit adds the explicit fence
forms).

## Step 1 (this run): the fences

Ten hypothesis-form fences in `PageRank_QA.lean`'s new `SharpFences`
section, each exhibiting every kept clause genuinely (the raw
eigen-equations proved) and killing the dropped clause's conclusion.
Fixtures: the delivered `prCyc`/`prPrim` plus three fresh ones (the
negative-α Google matrix at `prCyc`; the signed adjacency
`!![−1,2;2,−1]]`; the non-stochastic `!![0,2;1/2,0]]` with `M² = 1`).

## QA obligation

The fences are the QA. No shelf change; zero axiom contact expected.

## Delivery record (2026-09-06)

DELIVERED at the full census scope: 22 QA theorems plus 3 fixtures in
`PageRank_QA.lean`'s new `SharpFences` section (QA 6445 → 6467),
QA-only, zero axiom contact (`#print axioms` on all 21 nameable
audited declarations via `wip/sharpfences_spike.lean`'s audit block —
every one exactly `propext, Classical.choice, Quot.sound`; the
24-tag independence check unchanged and clean; the module elaborates
with zero warnings).

The fences, each with its genuine-hypotheses pin (the raw
eigen-equations proved beside the kill):

- **The mass lemma's / shadow's / ceiling's `hc`** at the constant
  vector's genuine `1`-pair of the two-cycle Google matrix (doubly
  stochastic there): mass `2 ≠ 0`, shadow `(1,1) ᵥ* P = (5/4) • (1,1)`
  against the swap's fix.
- **The shadow's `hα`**: at `α = 0` the Google matrix is `J/2` with
  the genuine `0`-pair, and the junk `0/0 = 0` shadow conclusion is
  refuted by the pair's true `-1` walk action.
- **The ceiling's `hα`**: negative `α` at the PRIMITIVE fixture —
  `G(−1) = [[1/2,1/2],[0,1]]`, the alternating pair at `1/2 ≠ 1`,
  `|1/2| ≤ −1` false. **Census finding, caught by the spike:** at the
  two-cycle `G(−1) = −swap + J = I` — its off-one spectrum is EMPTY,
  so no genuine off-one pair exists there and the negative-α fence
  must live where the walk's shadow eigenvalue is genuinely off-one.
  (Corollary of the shadow: at any nonnegative walk the off-one
  spectrum scales by `α`, so `|c| = |α|·|c'| ≤ |α|` — the clause
  `0 < α` is only ever load-bearing through the conclusion's
  ordering at `α < 0`.)
- **The ceiling's `hnn`**: the signed adjacency `!![−1,2;2,−1]]` with
  every degree genuinely positive, eigenvalue `−12/5` against
  `4/5`.
- **The ceiling's `hμ0`**: the zero-vector junk corner (every
  eigen-equation form trivially satisfied; the conclusion at `c = 5`
  refuted).
- **The twin's `hmass`**: the walk `1`-pair `(1,1)` of mass `2` does
  NOT map through (`(1,1) ᵥ* G = (1,1) ≠ (4/5) • (1,1)`).
- **The iff's `hc1`**: at `c = α = 1` the LEFT side holds (the
  stationary pair, `|1| = 1 = α`) while NO mass-zero `1`-pair of the
  swap exists (the mass-zero line is spanned by the alternating
  vector, which the swap negates) — the iff without `c ≠ 1` is
  false.
- **The engine's `hrow`**: the non-stochastic `!![0,2;1/2,0]]` with
  `M² = 1` pinned (strictly positive, `hk` genuine) and the genuine
  peripheral `−1`-pair `![1,−2]` — mixed-sign, so sign coherence
  fails.
- **The engine's `hk`**: the swap (row-stochastic, the alternating
  pair genuinely peripheral, mixed-sign) with no strictly positive
  power — `prCyc_not_primitive` consumed as the `hk` breaker.
- **The doubly-stochastic trio's `hcol`**: the delivered `prPrim`
  boundary witness in fence form (the right eigenvector's mass
  `−4 ≠ 0`); the shadow half screened by `prPrim_no_right_shadow_QA`.

Screened (already fenced at delivery): strictness's `hprim`
(`prCyc_not_primitive`).

Technique findings:

1. **The two-cycle `G(−1)` vacuity** (the headline census finding):
   fixture design for endpoint clauses must check the SHADOW scaling
   — the off-one spectrum is `α ×` the walk's mass-zero spectrum, so
   at `α < 0` the off-one clause can be vacuous exactly where the
   fence was first designed.
2. `norm_num` stalls on `|r| ≤ s` with negative-literal `r`: rewrite
   `abs_of_neg` (or `abs_of_pos`) first.
3. `funext` cannot apply to a negated equation — for `¬ (A = B)`
   fences, `intro h; have := congrFun h 0; ...; norm_num at this`.

Survey honesty note (recorded for future survey keys): the
theorem-level survey's DIRECT-mention half is exact and found this
audit's target; the transitive-closure half (crude per-theorem
body-splitting) produced false inert-declarations — e.g.
`abs_vecMulEigen_le_one` is exercised through the ceiling but was
listed inert — and drove nothing. Future closure-based surveys need
Lean-level consumption data, not string heuristics.
