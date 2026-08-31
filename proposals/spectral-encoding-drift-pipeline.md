# Proposal: The Rank-`k` Spectral-Encoding Drift Pipeline — Automatic `δ` Certification for the LapPE Stability Family

**Status:** Proposed and delivered in the same run (2026-08-31, run
`20260831T054849Z-run-1`), per the same-run pattern of
`hoeffding-inequality-degree-concentration.md`; see the delivery record
at the bottom.

## Why this, why now

`proposals/spectral-positional-encoding-stability.md` (delivered
2026-08-31) ends its honest-scope list with "the caller supplies (or
separately verifies) the gap `δ` — no method for computing or certifying
`δ` is included here," and its Deferred section prices exactly this
follow-on: "Any method for finding or tightening `δ` automatically
(e.g. via Weyl-type single-eigenvalue perturbation bounds already in
the shelf) — a separate proposal if wanted."

This is that proposal. The mechanism it prices is already on the shelf
twice over: the k=1 Fiedler-drift pipeline
(`Scaffold/Derived/EdgePerturbationDrift.lean`, delivered 2026-08-28)
discharges the Davis–Kahan separation *inline* from the base graph's
deterministic gap by the proved `weyl_inequality` on the concentration
tail event's complement — and the rank-`k` stability pair
(`spectralEncodingSubspace_stability`/`spectralEncoding_stability`,
`Fiedler.lean`) is now available as the deterministic side. What is
missing is the join: a high-probability drift statement at *arbitrary
encoding rank* `k`, the rank the ML-facing theorems were generalized
for and the k=1 pair cannot express.

Selection context (priority item 0): the Active table holds no
actionable rows above its gates — the Medium-High
empirical-stationary Step 2 is consumer-gated, every Low row is
decision-gated, and the GNN-sparsification Track A row was delivered.
The run therefore took the priced deferred follow-on with the clearest
precedent.

## SGT leverage

- **The consumer:** the general-rank stability pair, delivered 2026-08-31
  and so far exercised at one deterministic fixture
  (`Fiedler_QA`'s star-`K₁,₃ → K₄` instance). Its `δ` hypothesis is the
  statement's one caller-side obligation. A *random* consumer at
  parameterized rank — where `δ` no longer appears, replaced by the
  base graph's own rank-`k` spectral gap — is the falsifiability
  principle's exact use case: an error in the general-rank theorem's
  index convention, separation shape, or projector rank would break the
  drift statement's assembly, not sit beside it.
- **The Weyl discharge at rank `k`:** the k=1 helper
  `separation_of_norm_lt` is index-`⟨2⟩`-fixed; the general lemma runs
  `weyl_inequality` at index `k+1`, the first rank-parameterized
  exercise of that proved theorem.
- **The ML-facing sentence it unlocks:** under centered Bernoulli edge
  resampling, the `k`-dimensional positional-encoding subspace of the
  training graph stays within operator distance `s/(γ−s)` of the base
  graph's with the stated tail probability, where `γ` is any lower
  bound on the *base* graph's `evals ⟨k+1⟩ − evals k` — no
  perturbed-spectrum hypothesis anywhere.

## The statements (exact shapes)

In `Scaffold/Derived/EdgePerturbationDrift.lean`, mirroring the k=1
pair's structure:

1. `separation_of_norm_lt'` (private): the general-`k` Weyl discharge —
   on `‖∑ₑ perturbSummandₑ(ω)‖ < t`, from
   `t + δ ≤ evals (L A) ⟨k+1⟩ − evals (L A) k` conclude
   `δ ≤ evals (L (A + E_ω)) ⟨k+1⟩ − evals (L A) k`.
2. `edgePerturbation_spectralEncodingSubspace_drift`: at
   `k + 1 < card V`, `0 < δ`, `0 ≤ t`, `t + δ ≤` the base gap,
   `μ{‖P_k(L(A+E_ω)) − P_k(L A)‖ ≥ t/δ} ≤ 2·d·exp(−t²/(2‖∑ₑ L_e²‖))`.
3. `edgePerturbation_spectralEncoding_drift`: the kernel-isolated form
   (the ML-facing encoding component `P_k − P₀`), at the same stack
   plus the per-outcome nonnegativity/connectivity constraints the
   common-kernel identification needs — the exact per-outcome idiom of
   `edgePerturbation_fiedlerLine_drift`.
4. The sharpened matched-threshold forms `'` of both: at
   `0 < s < γ ≤` base gap, threshold `s/(γ−s)`, tail at `s` — the
   envelope-optimal instance, mirroring the k=1 `'` pair.

All four are CONDITIONAL ON THE `matrix_hoeffding` AXIOM via
`edgePerturbation_norm_tail` alone; the Davis–Kahan side, the Weyl
discharge, and the packaging identity are proved. Nothing here may be
described as foundationally proved.

## Degenerate-corner analysis (§5 policy, checked before stating)

- **Degenerate dimension:** the tail's prefactor `2·d` collapses at
  `card V = 0` — the same corner that broke the matrix trio (Errata
  class). The hypothesis `k + 1 < Fintype.card V` forces
  `card V ≥ k + 2 ≥ 2`, and `[Nonempty V]` is derived from it in the
  proof exactly as the k=1 theorems derive it from `3 ≤ card V`. No
  un-guarded instantiation exists.
- **`t = 0`:** threshold `0/δ = 0`; the event is all of `Ω` and the
  bound is `2d ≥ 4 ≥ 1 ≥ μ(Ω)` at `card V ≥ 2` — safe, matching the
  k=1 `t = 0` honesty lemma's situation.
- **Upper cluster nonempty:** `k + 1 < card V` is exactly
  `davis_kahan_sin_theta`'s own `hk` hypothesis — the same guard the
  deterministic theorems carry, at the same strength, no weaker.
- **`γ ≤ 0` / `s ≥ γ`:** excluded by `0 < s < γ`; `0 < γ` is derivable
  and is not carried as a separate hypothesis (the k=1 `'` idiom).
- **Measure side:** `bernPMF.toMeasure` is a probability measure by
  construction; no measure-side guard is needed (the same reasoning as
  every member of this family).

## QA plan

In `Scaffold/QA/Derived/EdgePerturbation_QA.lean`'s new `RankKDrift`
section, on the star `K₁,₃` at `k = ⟨2⟩` — a rank the k=1 drift family
cannot express:

- the variance proxy pinned exactly: `∑ₑ L_e² = 4 • L(star)` (the six
  ordered spoke pairs each squaring to `2 • vvᵀ`), `‖∑ₑ L_e²‖ = 16`
  through `l2OpNorm_eq_max_abs_evals` at the pinned top eigenvalue `4`;
- the design stack at `p ≡ ¼`: entry formula, per-outcome nonnegativity,
  support-graph preservation (every outcome keeps the star connected);
- the base gap pinned at the rank: `evals ⟨3⟩ − evals ⟨2⟩ = 4 − 1 = 3`;
- the **rank-load-bearing pin**: `evals ⟨2⟩ − evals ⟨1⟩ = 0` on the star
  (via the trace route) — at `k = ⟨1⟩` no positive `t + δ` fits, so the
  k=1 drift family is *vacuous* on this fixture; the `k = ⟨2⟩` cutoff
  is exactly what the tie structure demands;
- the closed-form subspace instance at `t = 1`, `δ = 2`:
  `μ{‖P₂' − P₂‖ ≥ 1/2} ≤ 8·exp(−1/32)`;
- the sharpened instance at `γ = 3`, `s = 1` (same threshold `1/2`, same
  bound — the matched-threshold form demonstrated);
- the kernel-isolated encoding instance at the same stack.

QA instantiates the conditional theorems; it does not prove
`matrix_hoeffding` and must not be read as certifying it.

## Acceptance criteria

- Zero new axioms, `sorry`, or `admit`; axiom count stays 5.
- `#print axioms`: the helper and all QA pins at exactly
  `propext, Classical.choice, Quot.sound`; the four drift theorems at
  the standard three plus `matrix_hoeffding` — nothing else.
- The star instance genuinely instantiates at `k = ⟨2⟩` with every
  hypothesis clause proved; the rank-vacuity pin lands.
- Full ladder passes: module elaboration, explicit targets, full
  `lake build` + `check_build_completeness.py`, `lint_axioms`,
  `check_refutation_independence`, `check_public_reachability`,
  `check_citations`, `check_markdown_links`, scoreboard regeneration,
  map-freshness after the stats sync.
- Records ladder completed in the same delivery: this proposal,
  `proposals/README.md`, README, radar QA axis, index maps, the QA
  module's purpose header, the execution plan, the activity log.

## Deferred / out of scope

- The Python certificate bridge exposure (gated on its own operator
  decision, as before).
- Any statement about *entrywise* eigenvector stability — the LapPE
  proposal already flagged that as the wrong question; nothing here
  reopens it.
- Non-uniform resampling designs or data-dependent `γ` certification
  (computing the base gap numerically) — no consumer has named these.

## Delivery record (2026-08-31, run `20260831T054849Z-run-1`)

Delivered as specified — zero new axioms (count stays 5), QA
3252 → 3275 (+23, `EdgePerturbation_QA.lean`'s RankKDrift section).

**The Lean.** Spike first: `wip/lappedrift_spike.lean` (shelf theorems +
QA section + axiom audit) iterated to zero errors and zero warnings
before any shelf edit. The shelf section of
`Scaffold/Derived/EdgePerturbationDrift.lean`: the general-`k`
separation helper `separation_of_norm_lt'` (the proved
`weyl_inequality` at index `k+1` — its first rank-parameterized
consumer; the `[Nonempty V]` the tail needs derived from
`k + 1 < card V` itself) and the four theorems
`edgePerturbation_spectralEncodingSubspace_drift{'}` /
`edgePerturbation_spectralEncoding_drift{'}` at the exact statement
shapes above, each proof the k=1 pipeline's structure verbatim with the
index generalized — `measure_mono` into `edgePerturbation_norm_tail`,
the helper's separation discharge, the general-rank stability theorem,
the packaging-identity norm rewrite, and the `t/δ` threshold squeeze.

**The QA.** On the star `K₁,₃` at `k = ⟨2⟩` (the Fiedler_QA fixture's
pinned spectrum `{0, 1, 1, 4}` consumed, not re-proved): the variance
proxy pinned exactly (`∑ₑ L_e² = 4 • L(K₁,₃)` by the sixteen-pair
enumeration — the six ordered spoke pairs each squaring to `2 • vvᵀ` —
with `‖∑ₑ L_e²‖ = 16` through `l2OpNorm_eq_max_abs_evals` at the pinned
top eigenvalue); the per-outcome stack at `p ≡ ¼` (entry formula,
nonnegativity, support-graph equality, connectivity — every outcome
keeps the star connected); the base gap pinned at the rank
(`evals ⟨3⟩ − evals ⟨2⟩ = 3`); the **rank-load-bearing vacuity pin**
`epStar4_k1_vacuity_QA` — `evals ⟨2⟩ − evals ⟨1⟩ = 0`, with
`evals ⟨1⟩ = 1` derived by the trace route
(`evals_sum_eq_trace` against `star4_trace = 6` and the three pinned
spectrum values) — so at `k = ⟨1⟩` *no* positive `t + δ` fits and the
k=1 drift family is vacuous on this fixture: the `k = ⟨2⟩` cutoff is
exactly what the λ₂ = λ₃ tie structure demands, the rank parameter
doing real work; and the three closed-form instances — the `t/δ`
subspace form at `t = 1`, `δ = 2`, the sharpened form at `γ = 3`,
`s = 1` (threshold `1/2`, the envelope point), and the
kernel-isolated encoding form — all
`μ{‖rotation‖ ≥ 1/2} ≤ 8 exp(−1/32)` (dimension factor `2 · 4`,
variance norm `16` in the denominator `2 · 16`).

**Axiom audit** (`wip/lappedrift_axcheck.lean`, 15 audited
declarations): the four drift theorems at exactly
`propext, Classical.choice, Quot.sound,
Scaffold.Mathlib.Probability.Concentration.Matrix.matrix_hoeffding`
— nothing else; all hard-crust QA pins (variance sums/norms, gaps,
trace route, vacuity, connectivity) at exactly the standard three; the
three instance pins honestly carrying `matrix_hoeffding`.

**Verification.** `lake env lean` zero errors on both touched modules,
the QA module's warning baseline verified unchanged (its recorded
three `Try this: ring_nf` notes, 3 = 3 against the HEAD file by pair
elaboration); explicit `lake build` targets ✔ on
`Scaffold.Derived.EdgePerturbationDrift` and
`Scaffold.QA.Derived.EdgePerturbation_QA`; full `lake build` ✔
(2407/2408) immediately followed by `check_build_completeness.py` —
131 source files, 131 fresh artifacts, 0 stale, 0 missing, exit 0;
`lint_axioms` (5, both PF findings allowlisted-confirmed);
`check_refutation_independence` (10-tag clean — no tags added, nothing
here repairs an axiom); `check_public_reachability` clean (62 modules);
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
at **3275/5/0**; `check_scaffold_map_freshness` exit 0 after the
3252 → 3275 stats sync in both map files and SVG regeneration (the new
proposal has no station).

**Technique findings.** (1) The stale-olen recurrence at the Derived
import boundary bit again: after editing the shelf drift module, the
QA module's `lake env lean` sees the old olean and the new theorems
are "unknown identifiers" — rebuild the shelf target first. (2)
`Fintype.card_fin` does not fire under `simp only` on the elaborated
index type `Fin (Fintype.card (Fin 4))`; bridge the defeq with an
explicit `have : ∑ i : Fin 4, …` type ascription instead. (3) The
ascription then re-types the summands' indices as `Fin 4`-literals,
which no longer match the `Fin (Fintype.card (Fin 4))`-typed spectrum
pins syntactically — re-pin each consumed lemma with a defeq `have`
(and close by `linarith` through an `rfl`-identity relating the goal's
index spelling to the sum's). (4) `!!`-literal matrix entries at
literal `Fin 4` indices need `Matrix.vecHead, Matrix.vecTail` in the
simp set (the Fiedler_QA idiom); the P₃-style variable-index entry
lemmas (symmetry, zero diagonal) need per-literal `fin_cases` instead.
(5) A tactic block `fun ω => by rw […]; exact …` split across a line
break mis-parses — keep it on one line.

**Honesty.** Every drift theorem is conditional on `matrix_hoeffding`
via the tail alone and must never be described as foundationally
proved; the Davis–Kahan side, the Weyl discharge, and the packaging
identity are proved. No existing public statement changed; the four
k=1 theorems are untouched (their statements and proofs identical).

