# Proposal: Prove the Subgaussian Tail Bound

**Status:** DELIVERED 2026-08-22 — Step 0 (the mandated spike) and the
repair-and-retire in one run. `subgaussian_tail_bound` is a proved theorem
(explicit axioms **10 → 9**), but **not at the unchanged statement this
proposal's Step 2 envisioned**: the spike confirmed the old statement was
materially false (two independent junk mechanisms, both refuted in QA with
the old hypotheses proved satisfied). The retirement proceeded as the
Woodbury-precedent emergency correctness repair — same name and conclusion,
honest hypotheses — per `docs/2_ARCHITECTURE.md` §9. Full delivery record
below, after the original assessment text.

Assessed from
`Scaffold/Mathlib/Probability/Concentration/Scalar/Subgaussian.lean`
(`subgaussianNorm`, `hoeffding_lemma`, `subgaussian_tail_bound`) and the
pinned Mathlib's `MeasureTheory/Integral/Bochner.lean` and
`MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean`.

## Why this axiom, not one of the other nine

Ten axioms remain (`docs/5_QA_SCOREBOARD.md`). The Cheeger hard
direction is out of scope for a "low-hanging" search —
`discharge-perturbation-axioms.md` already calls it known-hard, not
merely unexplored. The three matrix-valued concentration axioms
(`matrix_hoeffding`, `matrix_bernstein`, `matrix_azuma_hoeffding`) need
trace-exponential machinery (Golden–Thompson, Lieb's concavity) that
`spectral-graph-sparsification.md` already found "neither remotely
available" in this pin — not a place to start. The two sum-of-variables
axioms (`hoeffding_inequality`, `bernstein_inequality`) look tempting
because Mathlib has real MGF machinery
(`ProbabilityTheory.IndepFun.mgf_add`), but their hypothesis is only
**pairwise** independence
(`∀ i j, i ≠ j → IndepFun (X i) (X j) μ`), while the standard proof
needs the MGF of a sum of more than two variables to factor into a
product — `IndepFun.mgf_add` is two-at-a-time, and pairwise independence
does not generally give the mutual independence a finite induction over
more than two terms would need. That mismatch needs its own Step 0
before anyone touches either axiom; it is not scoped by this proposal.

`subgaussian_tail_bound` has none of these problems: it is a
single-variable statement (no independence hypothesis of any kind), and
its "distribution" is Scaffold's own `subgaussianNorm`, already a real
definition (an `sInf`), not itself axiomatized.

## The finding

`subgaussianNorm X μ := sInf {K : ℝ | 0 < K ∧ ∫ ω, exp(X ω ^ 2 / K ^ 2) ∂μ ≤ 2}`.
The target axiom is exactly the "moment condition implies tail bound"
direction of Vershynin's Proposition 2.5.2 (the definition's own
docstring already cites this proposition for `hoeffding_lemma`'s
constant-loss disclaimer) — the *easier* of that proposition's two
directions; the reverse (tail bound implies a moment bound) is not
needed here and should not be attempted as a shortcut.

The route is direct Markov's inequality on the nonnegative function
`ω ↦ exp(X ω ^ 2 / K ^ 2)`, applied at the tail event
`{ω | t^2/K^2 ≤ X ω ^ 2 / K^2}`:

- **Markov's inequality itself is on the shelf**, general-measure, no
  probability-measure instance required (this file's `μ` carries none):
  `MeasureTheory.mul_meas_ge_le_integral_of_nonneg` (`Integral/
  Bochner.lean:1646`) — `ε * (μ {x | ε ≤ f x}).toReal ≤ ∫ x, f x ∂μ` for
  `f` a.e.-nonnegative and integrable. Applied at
  `f := fun ω => exp(X ω ^ 2 / K ^ 2)` and
  `ε := exp(t^2/K^2)`, this gives almost exactly the target after
  converting `.toReal`/`ENNReal.ofReal` and the event
  `{|X ω| ≥ t} = {X ω ^ 2 ≥ t^2}` (`sq_le_sq'`/`abs_le` territory, not
  free but routine).
- **The real plumbing is getting from `h_sub : subgaussianNorm X μ ≤ K`
  to the two facts Markov's inequality needs at that exact `K`**:
  integrability of `exp(X² / K²)` and the bound `∫ exp(X²/K²) ≤ 2`.
  Neither is handed to us — the hypothesis only bounds an infimum, and
  the defining set's witnesses are at whatever `K'` happen to satisfy
  the moment condition, not necessarily at `K` itself. Two small lemmas
  close this gap, and both are genuine (if short) proofs, not
  one-liners:
  1. **Monotonicity in `K`.** If `K' ≤ K` (both positive) then
     `X ω ^ 2 / K ^ 2 ≤ X ω ^ 2 / K'^2` pointwise (dividing a
     nonnegative quantity by a larger positive number), hence
     `exp(X²/K²) ≤ exp(X²/K'²)` pointwise (`Real.exp_le_exp` +
     monotonicity of division), hence `∫ exp(X²/K²) ≤ ∫ exp(X²/K'²)`
     (`MeasureTheory.integral_mono_ae` or `integral_mono_of_nonneg`,
     needing integrability of the dominating function — see below) —
     so the defining set `{K : 0 < K ∧ ∫ exp(X²/K²) ≤ 2}` is
     upward-closed once one point is known integrable-and-bounded.
  2. **Reaching the exact target `K` from `sInf ≤ K`.** If `K` equals
     the infimum exactly and the infimum is not itself attained, no
     finite `K'` in the defining set is `≤ K`, so upward-closure alone
     does not immediately place `K` in the set — this needs a limiting
     argument (approach `K` from above by set members and use
     `MeasureTheory.integral_mono_ae`'s dominated-convergence-adjacent
     machinery, or `Filter.Tendsto` continuity of `K ↦ ∫ exp(X²/K²)` at
     `K`, to transfer the `≤ 2` bound to the limit). If `K` is strictly
     above the infimum, a single witness `K' ∈ (subgaussianNorm X μ, K]`
     plus monotonicity suffices and the limiting case does not arise.
     Record whichever route is actually taken; do not assume the easy
     (strict-inequality) case covers the axiom's exact hypothesis
     (`≤`, not `<`).
  3. **Integrability transfers the same way**: `exp(X²/K²)` is
     dominated pointwise by `exp(X²/K'²)` for `K ≥ K' > 0`, so
     integrability at a witness `K'` gives integrability at `K` via
     `MeasureTheory.Integrable.mono'` — needed before Markov's
     inequality's own `hf_int` hypothesis can be discharged, and before
     the monotonicity step above can invoke `integral_mono_ae` (which
     itself needs an integrable dominating function).

None of this is exotic — it is finite real-analysis plumbing around an
`sInf`, structurally similar to how `retire-sherman-morrison.md` found
its rank-one specialization to be "real, but not hard" work rather than
a free corollary. Treat it the same way here: real, self-contained,
Mathlib-only, but not a one-line `exact`.

## Scope

1. **Step 0 (mandatory, not done by this document):** open a Lean
   session, confirm `mul_meas_ge_le_integral_of_nonneg`'s exact current
   signature against this pin (cited above from a text search, not a
   compiled check), and spike the two small lemmas above in a scratch
   file before touching the public module. Record the actual route
   taken for the `K = sInf` boundary case (§ finding, point 2) — it is
   the one genuinely open question this proposal does not resolve in
   advance.
2. Prove `subgaussian_tail_bound` at its **existing name, hypotheses,
   and conclusion** — no restatement, per this repo's standing Step 1
   contract (see `discharge-perturbation-axioms.md`'s Step 1 section for
   the precedent).
3. QA: the existing `subgaussian_tail_bound_zero_QA` fixture should
   still exercise the proved theorem unchanged; add one more instance
   with a genuinely nonzero `K`/`t` pair where the bound is not trivially
   satisfied (avoid a second vacuous-or-degenerate witness).
4. Update the scoreboard, `index/sources/vershynin_hdp.md` (already the
   citation source for this axiom's Chapter 2 material — this becomes
   its first proved-not-axiom row for this specific statement), and the
   explicit axiom count.

## Acceptance criteria

- No `axiom`, `sorry`, or `admit` introduced.
- The proved theorem's module and its QA elaborate directly; standard
  hygiene checks (`lint_axioms`, `check_citations`,
  `check_markdown_links`) and a full `lake build` pass.
- Axiom count decreases by one.
- The delivery record states explicitly which route closed the
  `K = sInf` boundary case (§ finding, point 2), since this proposal
  does not resolve it in advance.

## Non-goals

- `hoeffding_lemma` is a different axiom in the same file with a
  similar `subgaussianNorm`-mediated shape; it is *not* scoped by this
  proposal even though it looks adjacent — it goes the other direction
  (a bounded, zero-mean variable *has* small `subgaussianNorm`, i.e. the
  harder direction of the Proposition 2.5.2 equivalence this proposal
  deliberately avoids) and would need its own Step 0.
- `hoeffding_inequality` / `bernstein_inequality` (the pairwise-vs-mutual
  independence question above) are explicitly out of scope here.

---

## Delivery record (2026-08-22, run 1)

### Step 0 — the spike and its decisive finding

Spike: `wip/subgaussian_spike.lean` (git-ignored), elaborated end-to-end
against this pin. Every consumed Mathlib lemma was confirmed at its exact
signature *before* the module was touched.

**The finding that changed the plan: the old axiom was materially false,
in two independent ways.** The proposal's anticipated difficulty (the
`sInf`-boundary case) never arose; both falsity mechanisms are junk-value
defects, and both were confirmed in the pinned source and then refuted
in QA:

1. **`Real.sInf_empty` vacuity** (`Mathlib/Data/Real/Archimedean.lean:190`:
   `sInf (∅ : Set ℝ) = 0`). Take `μ := (3 : ℝ≥0∞) • δ₀` and `X := 0`.
   Every candidate MGF integral is `∫ 1 ∂μ = 3 > 2`, so the defining set
   is *empty*, the norm is the junk value `0`, and `h_sub :
   subgaussianNorm X μ ≤ K` holds for **every** `K ≥ 0` — while the
   conclusion at `t = 0`, `K = 1` reads `μ univ = 3 ≤ 2 * exp 0 = 2`.
   False. The axiom's `μ` carried no measure-class constraint, so
   nothing excluded this.
2. **Junk-zero Bochner integrals** (`Mathlib/MeasureTheory/Integral/
   Bochner.lean:743`: `integral_undef : ¬Integrable f μ → ∫ f ∂μ = 0`).
   For a heavy-tailed `X` whose MGF `exp (X²/K²)` is non-integrable at
   *every* scale (e.g. `X n = 3n` under a geometric law on `ℕ`), the
   defining condition `∫ exp (X²/K²) ∂μ ≤ 2` holds at every `K` — the
   integral is the junk `0` — so the defining set is **full**, not
   empty, the norm is `0`, and the old conclusion would claim subgaussian
   tails `μ {|X| ≥ t} ≤ 2 exp (−t²/(2K²))` for a polynomial-tailed
   variable. False *even under probability measures*. (This mechanism
   also falsified the `subgaussianNorm` docstring's recorded junk
   behavior — "unbounded tails → the index set is empty" is wrong; it is
   full — and the docstring was corrected with a dated note.)

**Repair decision (recorded before stating, per the Woodbury
precedent):** keep the name, the conclusion (including the `2K²`
constant and the `t`/`ht` arguments); replace the junk-tainted
`h_sub : subgaussianNorm X μ ≤ K` by the honest moment content —
`(hK : 0 < K)`, `h_int : Integrable (fun ω => Real.exp (X ω ^ 2 / K ^ 2)) μ`,
`h_mom : ∫ ω, Real.exp (X ω ^ 2 / K ^ 2) ∂μ ≤ 2` — exactly the
hypotheses Markov's inequality consumes. Strictly stronger than the old
shape whenever the old one was non-vacuous (a genuine `subgaussianNorm ≤
K` witness supplies both). The old `0 ≤ K` hypothesis's `K = 0` branch is
dropped: its bound evaluated to the junk-dependent `2 * exp 0 = 2`.

**The `K = sInf` boundary question dissolves.** The proposal's one
genuinely open question — which route closes the boundary case — has the
answer: *the repaired statement never touches the `sInf`*, so no limiting
argument (monotone convergence, Fatou, or `Filter.Tendsto` continuity of
`K ↦ ∫ exp (X²/K²)`) is needed. The boundary case was an artifact of the
junk-tainted hypothesis. (Recorded here because the acceptance criteria
demand it.)

### Step 1 — the proof (route and pin-specific facts)

Route, all verified at this pin's exact signatures:

- **Half-scale transfer:** `exp (X ω²/(2K²)) ≤ exp (X ω²/K²)` pointwise
  (`div_le_div_iff₀` + `nlinarith`), so `integral_mono_of_nonneg` gives
  the moment at the half scale.
- **Measurability without a measurability hypothesis:** the half-scale
  function equals `Real.sqrt ∘ (the MGF at K)` pointwise by
  `Real.exp_half : exp (x / 2) = √(exp x)` (this pin: no prime), so
  `Continuous.comp_aestronglyMeasurable` + `h_int.aestronglyMeasurable`
  give ae-strong-measurability at the half scale — `Integrable.mono'`
  then yields integrability. No hypothesis on `X`'s own measurability is
  needed or carried.
- **Markov:** `mul_meas_ge_le_integral_of_nonneg` (Bochner.lean:1646) —
  note this pin's signature has *no* `0 ≤ ε` hypothesis — applied at
  `f := exp (X²/(2K²))`, `ε := exp (t²/(2K²))`.
- **Finiteness:** `Integrable.measure_norm_ge_lt_top` (L1Space.lean:816)
  forces Markov's event to have finite measure — the step the
  `.toReal`-shaped Markov statement alone cannot give (at `μ B = ∞` it
  degenerates to `0 ≤ ∫ f`).
- **ENNReal conclusion:** `measure_mono` for the event containment
  (`sq_le_sq'` with `t ≤ |X ω|`, then `sq_abs` and `div_le_div_iff₀`),
  `← ENNReal.ofReal_toReal` at the finite measure, `ofReal_le_ofReal`,
  and `le_div_iff₀` + `inv_mul_eq_div` for the `2 / ε = 2 * exp (−…)`
  arithmetic.

Pin-specific API notes for future work: `div_eq_inv_mul`/`inv_mul_eq_div`
are inverse-first at this pin (`a / b = b⁻¹ * a`); bare `mul_comm` in a
`rw` chain flips the *first* multiplication in the goal (the divisor, not
the target) — pass explicit arguments; `sq_le_sq'` is the two-hypothesis
implication (`-b ≤ a`, `a ≤ b`), `sq_le_sq` the `|·|`-iff; `Real.log_two_gt_d9`
(`0.6931471803 < log 2`, `Mathlib/Data/Complex/ExponentialBounds.lean`)
is the numeric log-2 source; `Real.exp_le_exp.2` needs the RHS visibly in
`exp`-form (rewrite with `← Real.exp_log two_pos` first); scoped
`open scoped ENNReal` is required for `∞`/`ℝ≥0∞` tokens.

### Steps 2–4 — QA and records

QA (`Scaffold/QA/Concentration/Scalar_QA.lean`, 6 → 17 declarations;
`#print axioms` on all twelve touched/new theorems reads only
`propext, Classical.choice, Quot.sound`; the zero-QA family no longer
consumes `hoeffding_lemma`):

- `subgaussian_tail_bound_zero_hypotheses_QA` + the updated
  `subgaussian_tail_bound_zero_QA`: both new hypotheses discharged
  constructively at the constant-zero variable (the MGF integrand is the
  constant `1`, integral exactly `1` under any probability measure).
- The proposal's mandated nonzero instance:
  `subgaussian_tail_bound_instance_QA` — constant-1 variable, `K = 2`,
  `t = 1`, on `Measure.dirac 0`; the moment bound `exp (1/4) ≤ 2` proved
  via `Real.log_two_gt_d9` (`subgaussian_exp_quarter_le_two_QA`); the
  event side pinned raw to exactly `1` and the bound side raw
  (`1 ≤ 2 * exp (−(1/8))`) — genuinely non-degenerate on both sides.
- The refutation family: `refutationMeasure := (3 : ℝ≥0∞) • δ₀` with
  total mass and constant-1 integral pinned raw (both `3`);
  `old_subgaussian_tail_bound_norm_junk_QA` (the defining set is empty,
  `Real.sInf_empty` gives norm `0` — the junk mechanism exhibited);
  `old_subgaussian_tail_bound_hypotheses_QA` (the old hypotheses provably
  satisfiable — vacuously); `old_subgaussian_tail_bound_refuted_QA`
  (the old conclusion at `X = 0, K = 1, t = 0` reads `3 ≤ 2` — the
  Woodbury/old-Cheeger falsification pattern).

### Verification

`lake env lean` on the module (only the pre-existing `unused variable K`
warning, verified identical in HEAD) and on the QA file (zero errors; the
nine remaining warnings are the pre-existing set in untouched
hoeffding/bernstein/norm declarations, verified against HEAD);
`#print axioms` on the retired theorem and the twelve QA theorems —
three standard axioms only; module and QA oleans built explicitly;
**full `lake build` ✔ (2229 targets, "Build completed successfully",
detached)**; `lint_axioms` (**9**), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated
(**1254 QA declarations / 9 explicit axioms / 0 sorries**; `Scalar_QA`
6 → 17). Records updated: both index files
(`sources/vershynin_hdp.md` — the Chapter-2 row is now its first
proved-not-axiom row for this statement; `map/probability_concentration.md`
with the junk-behavior note), scoreboard (counts, both Direct rows,
`lake build` row, lint row, interpretation bullet), README, the module's
two docstrings (`subgaussianNorm`'s junk-behavior correction;
`hoeffding_lemma`'s stale QA-note fix — the referenced
`hoeffding_lemma_zero_QA` never existed), this proposal, and the
execution plan / activity log.

### Adjacent hazard recorded (not addressed — a named residual for the
remaining concentration axioms' own Step 0s)

**Followed up 2026-08-28:** see
`proposals/audit-scalar-concentration-integrability-hazard.md`, which
opens the Step 0 this note asked for on `hoeffding_inequality`,
`bernstein_inequality`, `bernstein_bounded_variance`, and the same-file
`hoeffding_lemma`. That proposal's structural read found three of the
four already carry `[IsProbabilityMeasure μ]` plus bounded+measurable
hypotheses that likely rule out both mechanisms below; `hoeffding_lemma`
carries neither guard and is the priority spike. Not yet Lean-verified
as of that proposal's own filing.

The junk-integral mechanism is not specific to this axiom.
`hoeffding_inequality` and `bernstein_inequality` state their
centering/mean hypotheses as Bochner integrals over an *unconstrained*
`μ`; on an infinite measure, a non-integrable `X i` satisfies
`∫ X i ∂μ = 0` by the same `integral_undef` junk, making those
hypotheses vacuous while the conclusion bounds a possibly-infinite
measure's tail by `≤ 2`. Any future retirement attempt of either must
run its own Step 0 against this hazard (the pairwise-independence
mismatch already recorded in this proposal's assessment is a second,
independent blocker there). The matrix trio
(`matrix_hoeffding`/`matrix_bernstein`/`matrix_azuma_hoeffding`) states
hypotheses through Scaffold's `MatrixMDS` structure (comap-past
σ-algebras plus set-integral conditional means), whose integrals carry
the same junk surface — same caveat.

### Open next step

None — the proposal is complete. Deferred items named above are
out-of-scope hazards for *other* axioms' proposals, recorded here so
their Step 0s start from evidence.
