# The Doeblin TV Contraction and the PageRank α^t Rate

**Status:** COMPLETE — delivered 2026-09-02 (same-run proposal; run
`20260902T071252Z-run-1`, session `ses_f9f10ddd4ffezAgpRkIbHhMHoF`).

**Goal.** The standing handoff's first-named frontier: a second,
load-bearing consumer of the now-public Doeblin engine
(`entryRange_mulVec_le_of_pos_entries`, whose only consumer since the
2026-09-02 retirement was the retired theorem's own proof), plus the
rate clause the directed mixing layer's own scope-honesty section
records as missing — delivered without the complex spectral theory
that gates the sharp layer.

## Why this and why now

- **Load-bearing growth.** The retirement turned the range engine
  public with exactly one consumer. The load-bearing-growth principle
  (`docs/1_STRATEGY.md`) prefers a second consumer on a *different
  mathematical surface*: the TV contraction consumes the engine
  through the dual/test-function pairing
  `z ⬝ᵥ s = w ⬝ᵥ (Q *ᵥ s)` (`Matrix.dotProduct_mulVec`) — a
  different proof shape than the retired theorem's coordinate
  convergence — so a wrong engine constant now fails a *second* family
  of QA attainment pins (`1/2 = (1 − 2·(1/4))·1` at the basis pair,
  `(1/2)^{t+1} = (1/2)^t·(1/2)` at every time).
- **The recorded scope gap, discharged at the coarse level.**
  `DirectedMixing.lean`'s scope-honesty section said: "No rate: the
  geometric convergence constant (`|λ₂|`, total variation, χ²) needs
  the complex spectral theory of non-symmetric matrices." The Doeblin
  coefficient delivers the *coarse explicit* rate — the retired
  proof's own byproduct, previously unpackaged — with the consumer
  named and delivered with it: **`pageRank_tvDistance_le`**
  (`TV(ν ᵥ* G^t, π) ≤ α^t · TV(ν, π)`), the field-standard PageRank
  power-method rate (the teleportation floor `(1−α)·|V|⁻¹` read as a
  Doeblin floor with coefficient exactly `α`). The *sharp* `|λ₂| = α`
  layer stays gated on a named consumer exactly as before; this
  proposal does not touch it.
- **The bridge.** The mixing program's TV toolkit (`tvDistance`,
  hypothesis-minimal) had no directed-side statement. This is the
  first: the directed axis joins the TV/mixing program.

## What was delivered

**The shelf** (`Mixing.lean`'s new `Doeblin TV contraction` section,
importing `LinearAlgebra.PrimitiveConvergence` — no cycle):

1. `sum_vecMul_eq_of_row_sum` — mass preservation under a
   row-stochastic row action.
2. `abs_dotProduct_le_half_entryRange_mul_sum_abs` — **zero-sum
   interval pinning**: a zero-mass functional pairs with any function
   to at most half the function's entrywise range times the `ℓ¹` mass
   (the constant shift dies against zero mass; the dual step behind
   the contraction).
3. `tvDistance_vecMul_le` — row-action TV non-expansiveness at the
   generic-matrix level (the adjoint-walk `mulVec` contraction's
   row-action twin).
4. **`tvDistance_vecMul_le_of_pos_entries`** — the Doeblin TV
   contraction: `TV(μ ᵥ* Q, ν ᵥ* Q) ≤ (1 − |V|δ)·TV(μ, ν)` at equal
   masses, hypothesis-minimal (no sign hypothesis on either vector —
   only the equal-mass pinning, which the proof makes zero-mass via
   `hw0`). Route: TV as `(1/2)·(z ⬝ᵥ s)` at the sign statistic `s`,
   the duality flip to `w ⬝ᵥ (Q *ᵥ s)`, the engine's range
   contraction on `Q *ᵥ s` (whose entries lie in `[−1, 1]`, range
   `≤ 2`), and the pinning lemma closing the constant.
5. `tvDistance_vecMul_pow_le_of_pos_entries` — the block-iterated
   form at `(1 − |V|δ)^q`.
6. **`tvDistance_vecMul_pow_le_of_pos_power`** — the assembly: with
   `P^m` entrywise `≥ δ`, `TV(ν ᵥ* P^t, π) ≤
   (1 − |V|δ)^(t/m)·TV(ν, π)` for any mass-one start against any
   mass-one stationary `π` — sign-free on `ν`; `π` enters through
   stationarity and mass alone (uniqueness is PF-conditional and
   deliberately not needed). The remainder split `t = t mod m +
   m·(t/m)`, each `P^m` block contracting, the `P^(t mod m)`
   remainder non-expansive on the pair `(ν, π)`.

**The consumer** (`DirectedMixing.lean`): **`pageRank_tvDistance_le`**
— `TV(ν ᵥ* G^t, π) ≤ α^t·TV(ν, π)` at `m = 1`, with the floor lemma
`(1−α)·|V|⁻¹ ≤ G i j` (one `le_add_of_nonneg_left` at the entry
form) and the coefficient identity
`1 − |V|·((1−α)·|V|⁻¹) = α` (mul_left_comm +
`mul_inv_cancel₀`). Hard crust, no `perron_frobenius` contact. The
module's scope-honesty section updated honestly: the coarse TV rate
is delivered; the sharp spectral layer remains gated.

**The QA** (`DirectedMixing_QA.lean`'s new Section F, +31, 3637 →
3668):

- **The contraction attained exactly** (`Qd_tv_attained_QA`):
  `TV(e₀ ᵥ* Qd, e₁ ᵥ* Qd) = 1/2 = (1 − 2·(1/4))·TV(e₀, e₁) = 1/2` —
  load-bearing on the exact coefficient.
- **The iterated bound attained at every time**
  (`Qd_tv_every_attained_QA`): the closed form
  `e₀ ᵥ* Qd^t = ud + (1/2)^{t+1}•yd` (mode decomposition +
  `Qd_pow_mulVec_yd` via symmetry) gives truth `TV = (1/2)^{t+1}`
  equal to the bound `(1/2)^t·(1/2)` at every `t`.
- **The floor-free refutation fence**
  (`P2_tv_no_floor_refuted_QA` + `P2_quarter_le_refuted_QA`): the
  permutation `P₂` — row-stochastic, masses matching — refutes the
  contraction conclusion at pinned values (`TV = 1 > 1/2`), with the
  entries-floor hypothesis provably failing (`P₂ 0 0 = 0 < 1/4`).
  Exactly `hle` is isolated.
- **The PageRank rate attained exactly at every time on the periodic
  fixture** (`Gd_tv_every_attained_QA`): the Google matrix `Gd` of
  the imported edge `A2` at `α = 1/2` (pinned `= !![1/4, 3/4; 3/4,
  1/4]`), the closed form through the alternating mode factor
  `−α = −1/2` (`Gd_mulVec_yd`), truth `TV = (1/2)·|−(1/2)^t| =
  (1/2)^{t+1}` equal to the bound at every `t`.
- **The plain-walk contrast** (`P2_tv_never_decays_QA`): on the same
  periodic fixture the raw walk's TV to uniform is `1/2` at *every*
  time (even/odd powers) — the never-decay pin beside the
  exactly-decaying Google rate: the periodicity fix in one picture,
  joining `P2_no_limit` (Section B) at the TV level.
- The theorem instances (`Qd_tv_instance_QA`, `Gd_rate_instance_QA`)
  beside the value pins, and the mass/stationarity plumbing pinned
  raw (`e0_sum`, `e0_e1_mass`, `u2_stationary_Gd`, `Gd_apply`).

## Statement design and corner analysis

- **Equal masses, not double mass-one**: the contraction's proof only
  needs `∑ μ = ∑ ν` (made zero-mass). Sign-free on both vectors —
  strictly more general than the probability-vector form.
- **`δ = 0` degenerates to non-expansiveness** (coefficient `1`): no
  falsity corner; `ρ = 1 − |V|δ ∈ [0, 1]` is derived inside every
  proof from the floor (the same `|V|δ ≤ 1` argument the engine
  carries), so no side condition leaks into statements.
- **`m = 0`**: the assembly statement keeps `t / m = 0` and remains
  provable (the `(P^m)^0 = 1` route is non-expansiveness); an `0 < m`
  hypothesis was carried in the first draft and dropped as unused.
- **Empty type**: all statements are `[Nonempty V]`-guarded in the
  engine-consuming forms, mirroring the engine.

## Technique findings (for the next run)

1. `Matrix.vecMul_add` is the **matrix**-addition distributivity;
   `(v + w) ᵥ* A = v ᵥ* A + w ᵥ* A` is `Matrix.add_vecMul`. Same for
   `Matrix.vecMul_sub` vs `Matrix.sub_vecMul` — the names read
   symmetrically and are not.
2. `∑ i, f i * a` with the *constant* on the right rewrites by
   `Finset.sum_mul`; with the constant on the left (`∑ i, a * f i`)
   it is `Finset.mul_sum`. Choosing the wrong one fails with an
   uninformative pattern message.
3. `rw [← Nat.mod_add_div]` fails (metavariable pattern); state
   `t = t % m + m * (t / m)` as `(Nat.mod_add_div t m).symm` and
   rewrite with `conv_lhs => rw [hteq]` — a bare `rw [hteq]` also
   rewrites the `t`s *inside* `t % m` and `t / m` on the other side.
4. `Q ^ q` in a statement needs `[DecidableEq V]` (matrix `Monoid`):
   `omit [DecidableEq V] in` on such a theorem fails with "cannot
   omit referenced section variable".
5. Implicit function arguments that appear only in a lemma's
   *conclusion* (`h` in `abs_dotProduct_le_half_entryRange_mul_sum_abs`)
   must be passed by name (`(h := Q *ᵥ …)`) — `have hpin := L hw0`
   cannot infer them from the hypotheses.
6. `norm_num` does not evaluate `|·|` of numerals (`|1/2|` blocks
   goals). The robust idiom: rewrite the inner value first
   (`rw [show a = b from by norm_num]`) and then
   `abs_of_nonneg`/`abs_neg`/`abs_one` explicitly. `Real.abs_eq_self`
   does not exist in the pinned snapshot; `abs_of_nonneg` is the
   route.
7. `rw [Nat.div_one, hcoef] at hmain` style finishing works when the
   coefficient lemma's RHS is syntactically the callee's coefficient;
   when the callee was stated at `P ^ m` with `m` implicit, an
   explicit `hfloor' : … ≤ (G ^ 1) i j` bridge (one `pow_one`) keeps
   unification honest.
8. `Nat.Even` in the pinned Mathlib is `∃ k, n = k + k` (not
   `n = 2 * k`): bridge with `show k + k = 2 * k from by omega`.
9. An `omit`-ed lemma whose *proof* calls `Matrix.vecMul_one`-style
   lemmas is fine, but `simp [tvDistance, pow_zero,
   Matrix.vecMul_one, mul_one]` in the `q = 0` base case closes what
   `simp [tvDistance]` alone leaves (`μ ᵥ* Q^0` needs the unfolding
   lemmas named).

## Verification

Spike first (`wip/doeblintv_spike.lean` — all shelf declarations, the
full QA section, and the axiom audit iterated to zero errors / zero
warnings before any shelf edit); `lake env lean` zero errors / zero
warnings on all three touched modules; explicit `lake build` targets ✔
on all three; **`#print axioms` via `wip/doeblintv_axcheck.lean` on
all 38 audited declarations (7 shelf + 31 QA): every one exactly
`propext, Classical.choice, Quot.sound`**; **full `lake build` ✔
immediately followed by `check_build_completeness.py` — 133 source
files, 133 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` exit 0 (4 current axioms — unchanged; only the
allowlisted-confirmed PF finding); `check_refutation_independence`
(9-tag clean — no tags added, nothing touches an axiom);
`check_public_reachability` clean (63 repo modules);
`check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (**3668/4/0**) with the verification row;
map-freshness after the 3637 → 3668 stats sync in both map files and
SVG regeneration.

## Remaining risk

None owed by the delivery — pure hard crust, no axiom disposition
changed, no existing public statement changed. Honest scope: the
`α^t` rate is the Doeblin bound — coarse for general primitive
chains (though the QA pins it *attained* on the Google fixture, and
on the Google matrix `α` is in fact the sharp spectral rate by
Haveliwala–Kamvar — a sharpness *theorem* for general chains is not
delivered and remains part of the gated sharp layer); the
⌈log⌉-threshold depth form and a directed `t_mix` object are natural
follow-ons, gated on a named consumer per the standing policy.
