# Proposal: Closing the Inert Census to Zero

**Status:** COMPLETE. Delivered 2026-09-07 (run `20260907T163721Z-run-1`,
session `ses_f83866b92ffeZMaPKRE7jkT5Jb`); QA-only, zero axiom contact.

## The census finding this closes

`scripts/consumption_survey.py`'s census
(`wip/census_20260907_post16.txt`) leaves the inert set at 4 — the
Azuma `MatrixMDS` structure fields (`cond_mean_zero`, `measurable`,
`norm_bound`; never consumed as projections: the delivered
constant-zero instance discharges them tautologically) and
`Core.l_infty_norm_nonneg` (never instantiated; the def
`l_infty_norm` itself also never value-consumed). This delivery takes
all four and closes the compiler-derived census's never-touched set
to **zero**: every one of the shelf's 1,374 theorem/lemma
declarations is value-consumed by some QA proof.

## What was delivered

### The Azuma half: the first genuine (nondegenerate) `MatrixMDS` in QA

Fifteen theorems + three defs in `Matrix_QA.lean`'s new
genuine-Rademacher section, on the delivered coin measure (`mcCoin`,
the fair Bernoulli product on `Fin 1 → Bool`) at `V = Fin 1`:

- **The instance** `mdsRadMDS`: `X 0` is the Rademacher ±identity
  matrix (the sign is the coin flip), the tail is zero, `R = 1` — the
  first instance whose fields carry content:
  - `measurable` through the shelf's
    `stronglyMeasurable_coord_matrix` at the `Bool`-indexed family —
    the honest field the 2026-08-29 repair put in place of the
    content-free `adapted` one;
  - `cond_mean_zero` through `mdsFiltration_zero_trivial` (the comap
    characterization at `k = 0`: the tuple map into the subsingleton
    `Fin 0 → Matrix` pulls back only `∅` and `univ`) plus
    `mdsRad_integral_zero` — **the genuinely computed mean-zero
    integral**, by raw atom enumeration through `PMF.integral_eq_sum`
    (masses `1/2` each through the pmf application, values `+1` and
    `−1`);
  - `norm_bound` attained with equality at both outcomes through the
    pinned `l2OpNorm_one_fin1_QA`.
- **The three field pins**, each consuming its projection at concrete
  witnesses:
  - `mdsRadMDS_meas_pin` — the strong measurability promoted to
    `AEStronglyMeasurable` (`StronglyMeasurable.aestronglyMeasurable`),
    the property whose absence made the pre-repair set-integrals junk
    zeros (Errata §7's exact mechanism);
  - `mdsRadMDS_cond_mean_pin` — the field consumed at the trivial
    past's `univ` (joined to the raw atom enumeration) and at the
    **nonempty past event `k = 1`** (the true cylinder, its
    past-measurability witnessed through the comap existential at the
    entry fiber `t 0 0 0 = 1`);
  - `mdsRadMDS_norm_pin` — `‖X 0 ![true]‖ = R` and `‖X 0 ![false]‖ =
    R`, the `≤` side through the field, the `≥` side raw.

### The Core half: the `l_infty_norm` module

Six theorems + one def in the new `Scaffold/QA/Core/Norms_QA.lean`
(the Core subtree's second QA module): the value pin
`lnX_norm_eq_two` — `l_infty_norm lnX = 2` at the two-outcome fixture,
both `sInf` directions raw (`csInf_le` by membership at `2`, `le_csInf`
by the maximal atom's lower bound); `lnX_norm_nonneg_pin` — the target
theorem `l_infty_norm_nonneg` consumed, with the raw arithmetic
companion (two routes, one fact); and `lnJunk` — the documented
unbounded junk corner (`sInf ∅ = 0` at the identity variable on `ℕ`
under the trivial σ-algebra, unboundedness by `exists_nat_gt`) — the
docstring's honest "consumers must establish boundedness" pinned as a
fact.

## Consumption closure (the tool's verdict)

The census re-run (`wip/census_20260907_post17.txt`, diffed against
`post16`) shows exactly the 4 targeted theorems leaving the inert set
— 1370 → 1374 value-consumed, **4 → 0 never-touched**, no bonus, no
collateral. The never-touched defs fall 3 → 1 (`RV` and `l_infty_norm`
now value-consumed; `MRV` remains — the matrix-valued synonym is
type-only by nature, with no value-level accessor to consume). The
pins method's fifteenth application, and the program milestone it
completes: the compiler-derived consumption census's inert set is
**zero** — every shelf theorem's interface has been exercised by at
least one genuine QA proof.

## Traps recorded (the spike's fix rounds)

- The `RV`-synonym breaks numeral/instance elaboration inside a
  definition whose declared codomain is `RV` — the fixture is stated
  at the raw function type (`Ω → ℝ`); `l_infty_norm` accepts it by
  unfolding.
- `Measurable f`'s app-form (`hf hs`) and `Measurable.comp` both
  leave `Function.comp`/unapplied-function shapes the elaborator
  cannot unify with stated lambdas at reducible transparency —
  `have`s with explicit `MeasurableSet` types and the
  preimage-preimage composition route.
- `measurableSet_singleton` takes the ELEMENT (its instance argument
  then lands at the element type), not the set; through the Matrix
  synonym no `MeasurableSingletonClass` fires — the entry-fiber route
  (two `measurable_pi_apply` compositions into `Set ℝ`).
- `rw` does not rewrite under binders (`StronglyMeasurable (fun ω =>
  …)`); `rw` picks ONE instantiation of a pattern variable per call
  (the two atom summands needed `simp only`); `csInf_le`/`le_csInf`
  take `BddBelow`/`Nonempty` in the opposite order to the `Real.`
  names that do not exist here.
- `AEStronglyMeasurable (f k) μ` needs the partial application
  parenthesized — the bare juxtaposition parses `f`, `k`, `μ` as
  three arguments of the two-argument definition.

## Residue

- The inert-census program is closed; the census remains the standing
  targeting instrument for newly delivered shelf theorems (every new
  public theorem should land consumed).
- `MRV` (the matrix-RV def synonym) stays never-value-consumed by
  construction — recorded, not actionable.
- The Rademacher instance is one-shot (`X k = 0` for `k ≥ 1`); a
  many-step martingale difference sequence with genuinely random tail
  differences is priced as future QA, not owed.
