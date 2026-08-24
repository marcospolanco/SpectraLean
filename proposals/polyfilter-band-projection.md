# Proposal: PolyFilter Band Projection — the Chebyshev Layer's Second Consumer

**Status:** **DELIVERED 2026-08-24** (run `20260824T064113Z-run-1`) —
Step 0 (the survey, the first half of this document) and Step 1 (the
module + QA) in one run per the PageRank/irreducible-stationary
Steps 0+1 precedent; see the delivery record at the bottom. Zero new
axioms (count stays 9; `#print axioms` on all 7 public + 30 QA
declarations via `wip/polyfilter_axcheck.lean` reads only `propext,
Classical.choice, Quot.sound`). QA 1804 → 1832 (`PolyFilter_QA` a new
file at 28 by the generator metric).

Assessed from `Scaffold/Mathlib/GraphTheory/Band.lean`,
`Scaffold/Mathlib/GraphTheory/Krylov.lean`,
`Scaffold/Mathlib/GraphTheory/Spectral.lean`, and
`Scaffold/Mathlib/Analysis/OperatorTheory/Resolvent.lean` (the exact
statement shapes cited below), with the pin-fact checks done in the
Step-0 spike.

## The obligation this discharges

`proposals/approximate-spectral-projection.md`'s Step-0 survey recorded
the Chebyshev/polynomial-filter shape as the **natural second consumer
of the same Chebyshev layer** — its original gate (the then-undelivered
band projectors) dissolved 2026-08-20/21 with
`proposals/spectral-band-projectors.md`'s delivery. This proposal is
that recorded follow-on: it makes the Krylov/Chebyshev layer a
*two-consumer* layer (the strategy's explicit "more than one plausible
SGT consumer" criterion, verbatim) and gives the Band module its first
approximation-theory consumer — the exact-side object of the recorded
statement shape

```
‖p_d(M) − bandProjector M hM a b‖₂ ≤ ε(d, gaps)
```

through the shelf's proved operator-norm bridge. This is ring-3
(reusable SGT extensions) work whose inward dependency path is entirely
explicit: Krylov's polynomial transfer, Band's projector action,
Spectral's Parseval/eigenbasis, Resolvent's norm spine.

Load-bearing growth per the strategy's falsifiability test: the transfer
theorem's proof *consumes the exact shapes* of four delivered layers at
once — `eigvecOf_dotProduct_aeval_mulVec` (Krylov 1b), the band
projector's eigenbasis action (Band Step 1), `dotProduct_eigvecOf`
Parseval (Spectral), and the `ContinuousLinearMap.opNorm_le_bound` /
`Matrix.cstar_norm_def` spine (Resolvent Step 0). A misstatement in any
one of them breaks the new theorem loudly — this is the first theorem
that makes all four hold one statement simultaneously.

## Step-0 survey findings (recorded before any statement was frozen)

1. **The norm bound needs no eigenvalues of the difference.** The naive
   route (eigenvalues of `p(M) − B` through the sorted-spectrum API) is
   unnecessary: the Resolvent upper-bridge route
   (`l2OpNorm_le_of_abs_eigvalOf_le`, Resolvent.lean:184) bounds
   `‖M‖ ≤ c` from `‖M *ᵥ y‖² ≤ c² ‖y‖²` for all `y` via Parseval +
   `ContinuousLinearMap.opNorm_le_bound`. Mirroring that spine at the
   difference matrix needs only *component identities*
   `v_i ⬝ᵥ (D *ᵥ y) = (p(λ_i) − χ_i) (v_i ⬝ᵥ y)` — and neither
   symmetry of the difference nor its eigenvalues appear anywhere.
   Both component facts are one rewrite each: the polynomial side is
   Krylov's delivered `eigvecOf_dotProduct_aeval_mulVec` (Krylov.lean:493)
   verbatim; the projector side needs one new interface lemma
   (`eigvecOf_dotProduct_bandProjector_mulVec`), provable in four lines
   from `Matrix.dotProduct_mulVec` + `bandProjector_symmetric` +
   Band's delivered eigenbasis action (`bandProjector_mulVec_eigvecOf_self`
   / `_eq_zero_left` / `_eq_zero_right`) exactly as
   `dotProduct_eigvecOf_mulVec` (Spectral.lean:1246) mirrors
   `eigvec_dotProduct_mulVec`.
2. **The explicit-`ε(d, gaps)` designs split by band shape.** The
   uniform-over-a-wide-band polynomial filter (Chebyshev pass-band
   designs) is genuine scalar minimax theory (Achieser/Schönhage
   two-interval approximation) — **absent from the pin and out of
   scope; recorded as the follow-on, not attempted.** But the
   *top-eigenspace band* — `(t, Ltop]` where every in-band eigenvalue
   equals `Ltop` — admits two classical designs whose scalar facts are
   already proved on the shelf:
   - **Power filter** `p_d(μ) = (μ/c)ᵈ` at `c = Ltop`: `p_d(Ltop) = 1`
     exactly, and `|p_d(μ)| ≤ (t/c)ᵈ` on the exterior `[0, t]` by
     monotonicity of powers — ε(d, gap) = `(t/Ltop)ᵈ`, the power-method
     rate.
   - **Chebyshev-damped filter** `p_d = T_d ∘ w / T_d(w(Ltop))` at
     `w = Krylov.bandMap t Lbot` (the delivered affine band map,
     Krylov.lean:531): `w` carries the exterior `[Lbot, t]` into
     `[−1, 1]` (`abs_bandMap_eval_le_one`) and `w(Ltop) ≥ 1`
     (`one_le_bandMap_eval`), so `abs_T_eval_le_one` +
     `one_le_eval_T_of_one_le` give `|p_d(μ)| ≤ 1/T_d(w(Ltop))` on the
     exterior with `p_d(Ltop) = 1` exactly — ε(d, gap) =
     `1/T_d(w(Ltop))`, the damped-iteration rate, strictly better than
     the power rate in the small-gap regime. **This is the statement
     that consumes Krylov's Chebyshev scalar layer as a second
     consumer** (`abs_T_eval_le_one`, `one_le_eval_T_of_one_le`,
     `bandMap` and its four pins — five delivered declarations).
3. **Statement-shape decisions (recorded before stating):**
   - The transfer theorem is stated **hypothesis-form and
     filter-agnostic**: per-eigenvalue filter-quality bounds in,
     operator-norm bound out. The `ε(d, gaps)` explicit constants land
     in the two instantiation theorems. This is the repo's precedented
     split (`chiSquareDistance_le_of_connected` with its rate
     hypothesis; `kanielPaigeSkeleton` with its five discharge sites)
     and it makes the engine reusable by any future filter design,
     including the minimax designs priced above.
   - The band is `(a, b]` in `bandProjector`'s own convention; the
     dichotomy hypothesis is stated as the exhaustive disjunction
     `eigvalOf ≤ a ∨ b < eigvalOf` (no ordering assumptions on `a ≤ b`
     needed by the engine — it is stated for the delivered
     `bandProjector` definition as-is).
   - The instantiations take the **top-eigenspace hypothesis** in the
     index-free form `∀ i, t < eigvalOf M hM i → eigvalOf M hM i = Ltop`
     plus `∀ i, eigvalOf M hM i ≤ Ltop` — no `Fin`-index or sorted-list
     juggling, everything at the `V`-indexed eigenbasis API the shelf
     uses.
   - The norm is the scoped `Matrix.L2OpNorm` spelling `‖·‖` the
     Resolvent bridge and its perturbation consumers use
     (`open scoped Matrix.L2OpNorm`).
   - No limiting statement (`d → ∞`) in the module — the Kaniel–Paige
     finite-`k` calibration, already tested there and found to hold.

## The statements (Step-1 committed shapes)

For `M : Matrix V V ℝ` symmetric, `a b : ℝ`, `p : ℝ[X]`, `ε ≥ 0`:

1. `eigvecOf_dotProduct_bandProjector_mulVec` — the component action
   `v i ⬝ᵥ (B_{a,b} *ᵥ y) = χ_{a,i,b} * (v i ⬝ᵥ y)` with the
   indicator splitting on the band dichotomy. (Interface lemma; the
   Band module's action is currently eigenvector-vector-form only.)
2. `aeval_sub_bandProjector_l2OpNorm_le` — **the transfer theorem**:
   if `|p(λ i) − 1| ≤ ε` for every in-band index and `|p(λ i)| ≤ ε`
   for every out-of-band index, then `‖p(M) − B_{a,b}‖ ≤ ε`.
3. `powFilter_l2OpNorm_le` — the power-method instantiation:
   eigenvalues in `[0, Ltop]`, in-band ⇒ `= Ltop`, `0 ≤ t`:
   `‖((Ltop⁻¹ • M))ᵈ − B_{t, Ltop}‖ ≤ (t / Ltop)ᵈ` at the polynomial
   `(C Ltop⁻¹ * X)ᵈ`.
4. `chebyshevFilter_l2OpNorm_le` — the Chebyshev-damped instantiation:
   eigenvalues in `[Lbot, Ltop]`, in-band ⇒ `= Ltop`, `Lbot < t <
   Ltop`: `‖T_d(w(M))/T_d(w(Ltop)) − B_{t, Ltop}‖ ≤ 1/T_d(w(Ltop))`.

## QA plan

All on one 2×2 diagonal fixture `diag41 = !![4, 0; 0, 1]` (eigenvalues
{4, 1} pinned by the trace/determinant route, eigenvector directions by
the eigen-equation — the `Band_QA` `diag13` pattern, reused):

1. **Transfer-theorem positive witness**: the constant polynomial
   `p = C 1` is a perfect band filter — `‖1 − B_{2,4}‖ ≤ 0`, i.e. the
   projector itself is recovered exactly through the engine.
2. **Power-filter instantiation**: at `t = 1`, `d = 1, 2` the bound
   `‖(M/4)ᵈ − B_{1,4}‖ ≤ 4⁻ᵈ` with the scalar analysis showing the
   per-mode error exactly `4⁻ᵈ` — the ε constant is attained and
   cannot be improved for this design; the filtered matrices pinned
   entrywise raw.
3. **Chebyshev instantiation + the comparison witness**: at `t = 2`,
   `d = 1`: `w = bandMap 2 1`, `w(4) = 5`, `T₁(5) = 5`, filter
   `(2M − 3)/5 = diag(1, −1/5)` pinned raw, bound `‖·‖ ≤ 1/5`, the
   scalar per-mode error exactly `1/5` (attained), and the power rate
   at the same gap `1/2 > 1/5` — the damped rate provably better,
   the first theorem-level comparison of the two designs.
4. **Fence (refutation)**: the out-of-band filter-quality hypothesis
   is load-bearing — the constant polynomial `p = C 1` (perfect
   in-band, `|p(4) − 1| = 0`) with ε = 1/2 has its out-of-band
   hypothesis false (`|p(1)| = 1 > 1/2`), and the hypothesis-free
   conclusion is refuted in proved form: `‖1 − B_{2,4}‖ > 1/2` through
   the vector-action lower bound (`ContinuousLinearMap.le_opNorm` +
   `Matrix.cstar_norm_def` at the unit vector the difference fixes).

## Operating instructions for an autonomous run

- No new axioms (this is pure hard crust; every input is proved on the
  shelf or proved in the module).
- Spike first (`wip/`), transfer only when the spike is green.
- If the `pow_le_pow_left₀`-class monotonicity fact is absent from the
  pin at the needed form, prove the scalar bound inline rather than
  admitting anything; if the Resolvent spine does not transport as
  surveyed, stop and record the obstruction.

## Open next step

**None — the proposal is COMPLETE** (Step 1 delivered 2026-08-24, run
`20260824T064113Z-run-1`). Recorded follow-ons that are *not* this
proposal's business:

- the uniform wide-band pass-filter designs (minimax two-interval
  approximation theory — Achieser/Schönhage class facts absent from
  the pinned Mathlib; needs its own scoping survey if a consumer
  names it);
- the cosh-form non-vacuity corollary of the damped rate (already the
  Krylov program's own recorded follow-on, not this one's);
- a `d → ∞` limit corollary (deliberately not stated, per the
  finite-`d` calibration both programs tested).

## Delivery record (Step 1, 2026-08-24)

**Delivered:** the new `Scaffold/Mathlib/GraphTheory/PolyFilter.lean`
(namespace `SpectralGraphTheory`; minimal imports Band + Krylov +
Resolvent; the umbrella importing it) — the two component-action
interface lemmas (`eigvecOf_dotProduct_spectralProjector_mulVec`,
`eigvecOf_dotProduct_bandProjector_mulVec`, the latter's `a ≤ b`
guard load-bearing for the indicator form and documented as such),
the **transfer theorem** `aeval_sub_bandProjector_l2OpNorm_le` at
exactly the Step-0 committed hypothesis-form shape, the power-filter
instantiation `powFilter_l2OpNorm_le` (ε = `(t/c)^d`), the
`chebyshevFilter` definition with its closed-form eval lemma, and the
**Chebyshev-damped instantiation** `chebyshevFilter_l2OpNorm_le`
(ε = `1/T_d(w(Ltop))`) — the Chebyshev scalar layer's second consumer,
consuming `abs_T_eval_le_one`, `one_le_eval_T_of_one_le`, `bandMap`
and three of its four pins.

**QA (+28 theorem declarations, `Scaffold/QA/SpectralGraph/
PolyFilter_QA.lean`, importing `Band_QA` for the `diag13` fixture —
the QA-to-QA reuse precedent):** all four proposal-mandated sections.
(1) Exact recovery: the affine filter `(X−1)/2` drives the engine to
`‖p(M) − B_{1,3}‖ = 0` (theorem route: ε = 0 + `norm_nonneg`; raw
route: both sides pinned entrywise to `diag(0,1)` — the matrix
homomorphism laws for one, the threshold-projector pins for the
other). (2) The power filter at `t = 1`, `c = 3`: instantiation for
every `d`, the ε constant *attained* at the low mode
(`p.eval 1 = (1/3)^d`), and the filtered action on the low mode
cross-checked by an independent raw route through the generic
eigenvector action (`![1,0]` is an eigenvector by literal
computation, not by the spectral theorem's choice). (3) The
Chebyshev-damped filter at `Lbot = 1`, `t = 2`, `Ltop = 3`: `d = 1`
(ε = `1/3`) and `d = 2` (ε = `1/17`) with the raw Chebyshev pins
`T₁(3) = 3`, `T₂(3) = 17`, `T₁(−1) = −1`, the damped filter values at
both modes pinned (exact `1` at top, `−1/3` at the low mode, ε
attained), and the rate comparison `1/17 < (2/3)^2 = 4/9` — the two
instantiations of the same engine compared numerically at one gap.
(4) The fence: the out-of-band filter-quality hypothesis is
load-bearing — the constant filter `1` (perfect in-band) has its
out-of-band hypothesis *refuted* at the low mode, and the
hypothesis-free conclusion is refuted in proved form
(`‖1 − B_{2,3}‖ ≥ 1 > 1/2`, the norm lower-bounded through the fixed
unit vector by the `abs_eigvalOf_le_l2OpNorm` vector technique, no
eigenvalue of the difference computed).

**Verification:** spike first (`wip/polyfilter_spike.lean` — the
transfer engine green on its first complete compile; the fixes
becoming this run's trap list below); `lake env lean` on the module
and the QA file — zero errors, zero warnings each; explicit
`lake build` targets both ✔; `#print axioms` via
`wip/polyfilter_axcheck.lean` on all 7 public + 30 QA declarations —
`propext, Classical.choice, Quot.sound` only; **full `lake build` ✔
(2259 targets, +1, "Build completed successfully"; zero warnings in
the changed modules)**; `lint_axioms` (**9**, unchanged),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1832/9/0**, idempotent). Records updated: this
proposal, `proposals/README.md`, README (1832; module-table row),
the radar (QA axis synced 1804/44 → 1832/45, held 4.0), the
scoreboard (all three verification rows + a new interpretation
bullet), the SGT index map (new section + 7 declaration rows), the
umbrella, the execution plan, and the activity log.

**Pin-technique findings (recorded for future runs):**

- **The transfer-engine route is the Resolvent upper-bridge mirrored
  at an arbitrary difference matrix** — no eigenvalues of `p(M) − B`
  are ever computed. The naive sorted-spectrum route would need the
  difference's own eigenvalue analysis; the Parseval route needs only
  per-mode component identities. This pattern generalizes to any
  operator-norm bound on an eigenbasis-diagonalizable difference.
- `rw [if_pos h, if_pos h]` (listed twice) rewrites *both* the
  vector-valued and the ℝ-valued `if` that share a condition;
  a single `simp` after the first `if_pos` mangles the second `if`
  through `ite_apply` — list the rewrites explicitly.
- **`rw` order follows syntactic appearance, not hypothesis
  fit**: an `if_neg` whose proof projects a conjunction landed on the
  wrong (non-conjunction) `if` first. Typed `have`s for each negated
  condition (the PageRun recorded technique) fix the unification.
- The **`ℤ`-cast trap's QA face**: instantiating the module's
  `(d : ℤ)` coercion at literal `d = 1, 2` produces `((1 : ℕ) : ℤ)`
  (natCast), while the pin's `T_one`/`T_two` are stated at OfNat
  literals — `rw`-incompatible though defeq. QA pins must be
  *stated* in the natCast spelling and bridged with
  `rw [show ((n : ℕ) : ℤ) = (n : ℤ) from by push_cast, T_one]`.
- The numeric-default trap re-hit at the statement level: an
  un-ascribed `(1 / 3) ^ d` in a `*ᵥ`-statement picks `ℕ` — ascribe
  `((1 : ℝ) / 3) ^ d`.
- `rw [h]` auto-closes goals that become `rfl` (`3 ≤ 3`), so
  `rw [h]; norm_num` errors on the branch where the rewrite closed —
  split per-branch, or use `norm_num [h]` which computes and closes
  either branch.
- `Fin 2` literal-matrix entries: `fin_cases a <;> fin_cases b <;>
  simp [diag13]` leaves smul-arithmetic goals (`2⁻¹ * (3 − 1) = 1`)
  — append `norm_num [diag13]` as a single combinator instead of
  `<;> simp ... <;> norm_num` (the linter flags the double `<;>`).
- `Matrix.zero_dotProduct` (left-zero) vs `Matrix.dotProduct_zero`
  (right-zero) — the component-action lemmas need the left one.
