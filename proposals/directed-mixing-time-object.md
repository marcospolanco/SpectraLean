# Proposal: The Directed (PageRank) `t_mix` Object and Its Empirical Sampling Capstone

**Status:** COMPLETE (delivered 2026-09-02, same-run proposal, run
`20260902T085334Z-run-1`, session `ses_f9eb22f83ffeDSq0pMZtCO5W5H`)

## The obligation

The standing handoff after the Doeblin TV contraction delivery named
this exact frontier: "a next consumer of the mixing program's growing
`t_mix` object family (plain/lazy/discrete/continuous/uniform — the
directed object is the missing sibling, gated on a named consumer)",
and the directed-mixing rate work's own delivery record had listed
"the ⌈log⌉-threshold depth form" and "a directed `t_mix` object" among
its consumer-gated items. This proposal discharges that gate by the
repo's name-the-consumer idiom and delivers both gated items as one
package whose halves discharge each other's gates — the object's
witness condition is exactly the delivered rate theorem's threshold,
and the named consumer (the empirical PageRank capstone) consumes the
object's own attainment specification.

## The named consumer

The empirical-stationary capstone's own framing — "an agent that can
only simulate the walk" — instantiated at the Google walk. On directed
input the *entire* symmetric `evals`/`eigvecOf` mixing toolkit is
unavailable (there is no symmetric operator to restrict to; the QA
calibration witness of the directed axis records this), so the
α-rate Doeblin certificate (`pageRank_tvDistance_le`, delivered the
same day) is the only mixing route the sampling program can consume
there. Concretely: **`empiricalPageRank_stationary_tail_of_depth`** —
past the directed mixing time at `ε/2`, `n` i.i.d. simulated
random-surfer trajectories of length `t₀` estimate the PageRank weight
`π i` to `ε` with failure probability at most `2 exp(−nε²/2)`. The
hypothesis `pageRankMixingTimeFrom A α π x (ε/2) ≤ t₀` is the object's
attainment condition, discharged through `_spec` — the same loop the
Poisson bridge closed for the discrete object.

## Statement design (pinned before Lean)

1. **The per-start law** `pageRankDistribution A α t x :=
   (Pi.single x) ᵥ* (G^t)` — the directed twin of `walkDistribution`,
   *not* a new probability construction: its certification is the
   power plumbing (`pow_nonneg_entries`, `pow_row_sum`) at the Google
   floor lemmas. A named law rather than an inline spelling, so the
   object and the empirical theorem state the same object.
2. **The object takes `π` as a parameter** — matching
   `pageRank_tvDistance_le`'s given-`π` design. The `∃!` stationary
   supplier is PF-conditional; the object consumes whatever stationary
   vector the caller holds, and every theorem in the package is hard
   crust (zero `perron_frobenius` contact, `#print axioms`-verified).
3. **The depth form** at *any* mass-one `ν` (not just Dirac starts):
   threshold `log(TV(ν,π)/ε)/log(1/α) ≤ t` gives `TV ≤ ε` — the
   exact shape of the undirected `walkDistribution_tvDistance_le_of_depth`
   at the Doeblin rate, so the ceiling composes through `Nat.le_ceil`
   identically to the undirected spectral ceiling.
4. **The strict window `0 < α < 1`** on the ceiling and depth form is
   honest: at `α = 0` the chain mixes in one step and the threshold's
   logarithm degenerates (`log(1/0)`); the sharp `|λ₂| = α` layer
   stays gated exactly as before.

## Corner analysis (Step-0 discipline, applied to a definition-only delivery)

- **No new axiom is admitted**, so no degenerate-corner audit of a new
  trust surface is owed. The object's own junk corner (unreachable
  `ε`, empty witness set, `sInf ∅ = 0` on `ℕ`) is *pinned and fenced*
  in QA (`PR_tmix_zero_junk_QA`) rather than merely documented —
  mirroring `k2_mix_junk_corner_QA` for the discrete object.
- The law lemmas hold at `α = 0` (`_nonneg` and `_sum` carry only
  `0 ≤ α, α < 1`) — the window is split honestly between the always-true
  law facts and the `0 < α` calculus facts.
- The new TV-toolkit lemma's constant is sharp and QA proves it so
  (both sides pinned `1/4` — a factor-`2` statement would read
  `1/4 ≤ 1/2`, true but slackful).

## What was delivered

- **`Mixing.lean`** — `abs_sub_le_tvDistance`: a single coordinate's
  deviation is at most the TV distance at equal masses
  (zero-mass triangle route: the complement's deviation mass is
  exactly `−d i`, so `2|d i| ≤ ∑|d| = 2·TV`). The constant is sharp.
  This is the entrywise extraction through a *TV-level* rate — the
  directed bias term's engine, since the directed program bounds TV,
  not χ² (the undirected program's entrywise extraction went through
  χ² summands).
- **`DirectedMixing.lean`** — the directed-mixing-time section:
  `piSingle_vecMul_apply` (the row bridge), `pageRankDistribution`
  with `_apply`/`_nonneg`/`sum_`/`_zero`, the private calculus twin
  `pow_mul_le_of_log_threshold'` (of Oversmoothing's public bridge —
  private so the directed module's import closure stays free of the
  undirected mixing stack; promote on a third consumer),
  **`pageRank_tvDistance_le_of_depth`**, and **the object
  `pageRankMixingTimeFrom`** with `_bddBelow`, `_le_of_cert`,
  **`_spec`** (the well-ordered attainment — `csInf_mem`, the discrete
  object's own advantage), **`_le_of_rate`** (the α-ceiling), `_anti`.
- **`Derived/EmpiricalStationary.lean`** — the `PageRankLimit`
  section: `empiricalPageRank_tail` (fixed-time, hard crust),
  `empiricalPageRank_stationary_tail` (bias-term form at the quoted
  bias `α^{t₀}·TV(δ_x,π)`), and **the capstone**
  `empiricalPageRank_stationary_tail_of_depth` (the named consumer;
  the object's `_spec` is load-bearing in its hypothesis).
- **QA** (+15, 3668 → 3683): `DirectedMixing_QA.lean`'s Section G —
  the law join to Section F's closed forms (`PR_law_eq_QA`,
  `PR_tv_eq_QA`: `TV_t = (1/2)^{t+1}` at every time), the antitone-pow
  helper, **the object `t_mix(1/8) = 2` pinned in both directions**
  (witness from the closed form; the lower bound from attainment — no
  time `≤ 1` is a witness since `TV_1 = 1/4 > 1/8`), **the α-ceiling
  attained exactly** (`⌈log 4/log 2⌉ = ⌈2⌉ = 2` = the object, through
  `Real.log_pow` at `log 4 = 2·log 2`), **the depth form attained with
  equality at the threshold time** (`TV_2 = 1/8`), the **entrywise
  extraction attained** (both sides `1/4`), the junk corner fenced at
  `ε = 0`; and `EmpiricalStationary_QA.lean`'s capstone section — the
  bias instance (`2 exp(−1/8)` at the quoted bias `1/4`) and the
  capstone instance (`2 exp(−1/32)` past the pinned `t_mix = 2`,
  joining the object pin to the consumer's bound).

## Verification

- Spike first (`wip/dtspike.lean` — shelf + full QA + the axiom audit
  block, iterated to zero errors/zero warnings before any shelf edit).
- `lake env lean` zero errors/zero warnings on all five touched
  modules; explicit `lake build` targets ✔ on all five.
- **`#print axioms` via `wip/dtaxcheck.lean` on all 34 audited
  declarations (15 shelf + 19 QA): every one exactly
  `propext, Classical.choice, Quot.sound`** — pure hard crust, zero
  admitted-axiom contact anywhere in the delivery.
- **Full `lake build` ✔ immediately followed by
  `check_build_completeness.py` — 133 source files, 133 fresh
  artifacts, 0 stale, 0 missing, exit 0** (the
  Derived-imports-shelf stale-olen boundary met once at the Directed
  olean, remediated per the completeness script's docstring, and once
  more at the full build's QA artifact).
- `lint_axioms` exit 0 (4 current axioms, unchanged; only the
  allowlisted-confirmed PF finding); `check_refutation_independence`
  (9-tag clean — no tags added, nothing touches an axiom);
  `check_public_reachability` clean (63 repo modules);
  `check_citations`; `check_markdown_links`; `check_backlog_freshness`
  all pass; scoreboard regenerated (**3683/4/0**); map-freshness
  exit 0 after the 3668 → 3683 stats sync in both map files and SVG
  regeneration (no station — no tier change).

## What is deliberately not here

- **The sharp `|λ₂| = α` layer** (Haveliwala–Kamvar) — a sharpness
  *theorem* for general primitive chains needs the complex spectral
  theory of non-symmetric matrices and stays gated exactly as before;
  the α-ceiling is the Doeblin bound, coarse off the Google fixture.
- **A directed uniform (worst-start) `t_mix` object** — a trivial
  sup-composition left consumer-gated, exactly as the undirected
  uniform object was before its submultiplicativity class named it.
- **The reverse comparability** (directed TV floors at eigenpairs) —
  the undirected floor family's engine is the symmetric eigenbasis;
  no directed analogue exists on the shelf, and no consumer names one.

## Technique findings (for the next run)

- **`Pi.single` needs its value**: `Pi.single x (1 : ℝ)`; the bare
  `Pi.single x` elaborates the codomain as a metavariable and surfaces
  as "function expected"-style errors far away. The nested ascription
  `(Pi.single x (1 : ℝ) : V → ℝ)` works in statements.
- **Missing scoped notation produces misleading parse errors**: a
  module that uses `ᵥ*` without `open scoped Matrix` reports
  "expected token" at a *column inside the preceding identifier*, not
  at the operator. Check the scoped opens before hunting character
  encoding.
- **`rfl` cannot equate `1/2` with `2⁻¹`** (`one_div` is not `rfl`);
  joins between a literal-spelled statement and a def body spelled
  with inverses close by `simp [Gd]` (definition unfolding) or
  `simp only [one_div]` first.
- **`Finset.sum_erase` in the pinned Mathlib is the `f a = 0`
  version** — useless for complement-splitting a general summand. The
  robust complement split is `conv_lhs => rw [show univ = insert i
  (univ.erase i) from (Finset.insert_erase _).symm]` then
  `Finset.sum_insert` — the plain `rw [← Finset.insert_erase ...]`
  rewrites the *inner* `univ` too and produces a nested garbage set.
- **`refine le_trans (measure_mono ?_) ?_` with the middle only
  determined by a later bullet** leaves the target measure set as a
  metavariable and dies in a deterministic `isDefEq` timeout
  (200k→1M heartbeats both fail). Elaborate the tail theorem as a
  standalone `have h := theorem args...` first (no expected-type
  pressure), then `refine le_trans (measure_mono ?_) (le_trans h ?_)`
  — the delivered QA's own idiom, rediscovered.
- **Implicit conclusion-only binders must be passed by name** when a
  `by`-block hypothesis is what determines them:
  `empiricalPageRank_stationary_tail (A := A2) (t := 1/2) ...` — the
  by-block otherwise elaborates against `1/4 < ?t` vacuously. (Same
  class as the Doeblin run's recorded finding.)
- **`Real.log_pow (2 : ℝ) 2`** in this pin carries no `≠ 0`
  hypothesis and takes `(x) (n)`; `pow_le_one₀` (not `pow_le_one`) is
  the non-deprecated `a ^ n ≤ 1`; `mul_div_cancel_left₀ hlog2ne` takes
  the proof with the value implicit, and `field_simp` is the robust
  route for `a * b / b = a` rewrites inside `⌈·⌉`.
- **The `unusedSectionVars` linter's output during a partially-broken
  elaboration is unreliable**: the omit commands it suggests can fail
  ("cannot omit referenced section variable") while later declarations
  still have errors; fix the errors first — the warnings may vanish
  (they did here).
- **Exponent arithmetic in measure instances**: state the evaluated
  closed form (`2 * Real.exp (-(1 : ℝ) / 32)`), obtain the theorem
  instance as a `have`, then `push_cast at h` plus `norm_num`-evaluated
  `e : ...` rewrites — never re-derive the exponent shape in the goal.
