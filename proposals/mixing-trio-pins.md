# Proposal: The Mixing Trio's Positive Pins

**Status:** COMPLETE. Delivered 2026-09-07 (run `20260907T112036Z-run-1`,
session `ses_f84763143ffeAVPDc1KGOxyMgM`); QA-only, zero axiom contact.

## The census finding this closes

`scripts/consumption_survey.py`'s census (`wip/census_20260907_post9.txt`)
leaves the inert set at 28, with four 3-clusters: Mixing, AlonBoppana,
Expander, and Matrix.Azuma. Mixing wins on content weight — its three
are real mixing-program theorems, not helpers:

- `chiSquareDistance_eq_zero_iff` — the vanishing characterization of
  χ² (`χ² = 0 ↔ the walk law IS the stationary distribution`). Its
  `hd` degree-positivity fence exists on file, but the iff itself was
  never consumed: no QA proof had ever applied either direction.
- `walkDistribution_tvDistance_le_max_rate` — the plain TV shadow at
  the *computed* spectral rate. Its χ² twin
  (`chiSquareDistance_le_max_rate`, consumed at the triangle) and its
  lazy TV twin (`lazyWalkDistribution_tvDistance_le_of_connected`,
  consumed) both had instances; the plain TV form never did.
- `klDiv_lazyWalkDistribution_le` — the lazy entropy-decay twin of the
  consumed headline `klDiv_walkDistribution_le`.

## What was delivered

Fifteen QA declarations in `Mixing_QA.lean`'s new `StructuralPins`
section (QA 6670 → 6685), the first genuine consumption of all three:

- **The `K₂` spectrum helpers** (`k2_evals_last_eq`,
  `k2_spectral_rate_QA`) — the top sorted eigenvalue pinned in the
  card-form index the max-rate theorems carry, and the certificate
  `max(1 − λ₂, λ_max − 1) = 1` exactly (both branches pinned
  `λ₂ = λ_max = 2`): the periodic chain's honest `r = 1` corner — no
  decay, which is exactly right, the plain walk provably never mixes.
- **The plain TV shadow** (`mxp_k2_tv_max_rate_le_QA` /
  `mxp_k2_tv_max_rate_attained_QA` on `K₂`;
  `mxp_tri_tv_max_rate_le_QA` / `mxp_tri_tv_max_rate_value_QA` on the
  triangle) — the theorem instances with no hand-supplied rate: the
  certificate is computed from the pinned spectrum inside the bound.
  On `K₂` the bound is **attained with equality** (`TV = 1/2 =
  (1/2)·√(1²·1)`); on the triangle both sides are pinned (`1/3` vs
  the inner product `1/2`, i.e. `1/3 ≤ (1/2)·√(1/2)` — the honest
  Cauchy–Schwarz slack the delivered `tri_tv_rate_one_holds_QA`
  already proved, now reached through the computed certificate rather
  than the hand-supplied `r = 1/2` of `tri_tv_rate_one_QA`).
- **The lazy KL twin** (`mxp_k2_kl_lazy_le_QA` /
  `mxp_k2_kl_lazy_attained_QA`) — **both sides collapse to `0`**: the
  KL side because the lazy walk HAS reached stationarity at depth `1`
  (`k2_lazy_law_one_QA`; every KL summand is `(1/2)·log(1) = 0`), the
  bound side because the lazy rate `1 − λ₂/2 = 1 − 2/2 = 0` collapses
  the prefactor. Attained with equality at `0 ≤ 0` — the strongest QA
  shape a bound theorem can have.
- **The vanishing iff at the looped triangle** — the delivered
  `loopTriAdj` fixture (all-ones adjacency, loops breaking the
  period-2 obstruction): the plain one-step law is exactly uniform
  (`mxp_loopTri_law_value`, the plain-walk analogue of
  `k2_lazy_law_one_QA`), and **both directions of the iff are
  consumed, each fed by the other side's raw computation**:
  `mxp_loopTri_chi2_via_iff_QA` derives χ² `= 0` THROUGH the iff's ⇐
  from the raw stationarity; `mxp_loopTri_law_via_iff_QA` re-derives
  the stationarity THROUGH the iff's ⇒ from the raw zero χ² (direct
  summation, `mxp_loopTri_chi2_raw_QA`). Two routes, one value.
- **The contrapositive companion** (`mxp_k2_not_mixed_via_iff_QA`) —
  on the periodic `K₂` the χ² is the pinned `1 ≠ 0`, so through the
  iff's ⇐ the plain law provably has NOT mixed: the vanishing
  characterization used as a *non-mixing certificate*, the content
  that makes the looped fixture's vanishing non-accidental.

## Technique findings (Lean 4.14 / this Mathlib pin)

- **`secondEval M hM hcard` is *literally* `evals hM ⟨1, by omega⟩`**
  — the index `1`, not `card − 2`. On `Fin 2` the top sorted index
  `card − 1 = 1` IS the `secondEval` index, so the top-eigenvalue pin
  collapses to a one-line ascription of `k2_secondEval_QA` (the
  eigvalOf case analysis remaining only to confirm no other value is
  possible). The first spike round assumed `card − 2` and paid for it
  with a failed defeq ascription — the definition's literal shape is
  what makes the K₂ helper cheap.
- Direct type-ascription `have h : evals _ ⟨0, _⟩ = 2 :=
  k2_secondEval_QA` fails (secondEval's unfolding not accepted by
  `have :=` unification); the working routes are the `rfl`-show
  bridge (`show secondEval … = evals … ⟨1, _⟩ from rfl`, the
  Poincare-file idiom) or ascribing at the *matching* index.
- `fin_cases i <;> rw [pi_lemma i]` mis-binds (`i` renamed); the
  file's working idiom is `funext i; fin_cases i <;> simp [pi_lemma]`.
- The `loopTriAdj` one-step-law `simp [...]` leaves three
  `1 + 1 + 1 = 3` degree-sum goals on `Fin 3` — closed by a trailing
  `all_goals norm_num` (the `Fin 2` twin closed without it; `Fin 3`
  sums do not autofold).

## Verification

Spike-first (`wip/mxpins_spike.lean` — green after three fix rounds,
both traps above recorded); the landed module elaborates with zero
errors/warnings (the 3 `ring_nf` infos verified pre-existing at HEAD
via a stash round-trip); explicit build ✔; the 15-declaration axiom
audit (`wip/mxpins_axcheck.lean`) — every one exactly `propext,
Classical.choice, Quot.sound`; full `lake build` +
`check_build_completeness.py` (135/135 fresh — one mtime staleness
caused by the pre-existing-info check's stash round-trip, cured by
the documented artifact-removal remediation); `lint_axioms` exit 0 (4
axioms unchanged); `check_refutation_independence` (24-tag clean);
`check_public_reachability` (63 modules); `check_citations`;
`check_markdown_links`; `check_qa_name_uniqueness` (the new `mxp_*` /
`k2_evals_*` / `k2_spectral_rate_*` names collision-free);
`check_backlog_freshness` clean; scoreboard regenerated
(1369 / 6685 / 4 / 0); map freshness exit 0 after the stats sync;
**the census re-run (`wip/census_20260907_post10.txt`, diffed against
`post9`) shows exactly the 3 targeted theorems leaving the inert set
(1339 → 1342 value-consumed, 28 → 25 never-touched, the `Mixing (3)`
line gone, no bonus, no collateral)**.

## Honest scope

The TV shadow pins are at depth `1` on the two delivered fixtures; the
KL twin at the single depth where both sides vanish; the iff pins at
the one looped fixture and depth `1` (the plain `K₂` contrapositive
companion at depth `1`). No hypothesis-necessity fences owed (the
iff's `hd` fence and the max-rate family's certificate fences exist on
file from earlier audits). The certificate-computation content is at
`λ₂ = λ_max` fixtures only (the saturated corner and the triangle) —
a fixture where the two branches of the max select differently would
be a natural future pin, not owed here.
