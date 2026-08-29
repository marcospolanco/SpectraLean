# Proposal: Concentration of a Sampled Laplacian's Quadratic Form — a Real Consumer for Matrix Hoeffding

**Status:** COMPLETE 2026-08-28 (run `20260828T090419Z-run-1`): Steps 0
and 1 both delivered, plus the **degenerate-dimension repair of all three
matrix concentration axioms** that Step 0's defect check found mandatory
first (each of `matrix_hoeffding`, `matrix_bernstein`,
`matrix_azuma_hoeffding` was materially false — inconsistent — at
`Fintype.card V = 0`, `t = 0`; repaired with the `[Nonempty V]` guard the
cited Tropp statements carry implicitly). Zero new axioms (count stays
10); `matrix_hoeffding` now has its first theorem consumer. This document
authorizes no further Lean changes, admissions, commits, or external
publication on its own.

## The obligation this discharges

`matrix_hoeffding`
(`Scaffold/Mathlib/Probability/Concentration/Matrix/Hoeffding.lean`) is
one of the seven admitted axioms with **zero theorem consumers** —
referenced only by its own file and the thin zero-sequence QA check. Its
docstring already names an intended use ("the matrix concentration
statement consumed by Scaffold's event-stream frontier: bounded
per-event Laplacian perturbations with independent events") that has
never actually been discharged — a recorded intent, not a proof
obligation anyone has picked up. This proposal is that pickup: a small,
self-contained consumer distinct from and simpler than
[spectral-sparsification-via-leverage-scores.md](spectral-sparsification-via-leverage-scores.md)'s
`matrix_bernstein` route (Hoeffding needs no variance statistic, only a
semidefinite bound `X i ω² ⪯ A i²` per term — mechanically simpler to
instantiate, a good first exercise of the matrix-concentration axiom
family before the harder Bernstein-based sparsification argument).

## Assessed from

`Scaffold/Mathlib/Probability/Concentration/Matrix/Hoeffding.lean`
(the exact semidefinite-order hypothesis `Matrix.PosSemidef (A i * A i -
X i ω * X i ω)`, no centering required), `Scaffold/Mathlib/GraphTheory/
VariationalTransfer.lean` (`normalizedLaplacian_psd`,
`rayleigh_normalizedLaplacian_degreeSqrt` — itself a second
zero-real-consumer module, referenced only by its own file: this
proposal incidentally loads two under-exercised modules with one
theorem), and the event-stream frontier's own docstring pointer (name
only verified, content not yet read in detail — Step 0's first task).

## The statement (draft shape — subject to Step 0 correction)

Given `n` independent bounded per-event Laplacian perturbations
`X i : Ω → Matrix V V ℝ` (Hermitian, each satisfying the semidefinite
bound `X i ω * X i ω ⪯ A i * A i` for a fixed deterministic bound matrix
`A i`, e.g. a single-edge-weight perturbation bounded by its own
conductance), the target theorem composes `matrix_hoeffding` with the
normalized-Laplacian quadratic form to get a *scalar* concentration
statement usable by the rest of the graph-theoretic shelf without
carrying matrix-norm machinery downstream:

```
P {|quadForm (∑ i, X i ω) x| ≥ t * ‖x‖²} ≤
    2 * card V * exp (-t² / (2 ‖∑ i, A i ^ 2‖))
```

for a fixed test vector `x` (e.g. the Fiedler vector, or `onesVec`),
via `Matrix.L2OpNorm`'s operator-norm bound on the quadratic form
(`|quadForm M x| ≤ ‖M‖ * ‖x‖²`, a standard Cauchy–Schwarz-style
inequality — Step 0 must confirm this exact lemma or its equivalent is
in the pin under the `L2OpNorm` API before stating the corollary this
way).

**Step 0 must check:** (1) whether `‖M‖ * ‖x‖² ≥ |quadForm M x|` is
already in the pin for `Matrix.L2OpNorm`, or needs a short proof from
the operator norm's definition; (2) what the "event-stream frontier"
docstring pointer actually refers to — if there is already a partially-built
consumer elsewhere in the shelf (an event-driven Laplacian-update module
under `GraphTheory/Dynamics` per the discrete-affine proposal's naming
note), this proposal should compose with it rather than duplicate it;
(3) whether a fixed, non-random test vector `x` is a sufficient first
statement, deferring the sup-over-`x` / operator-norm-of-the-whole-sum
form (a strictly stronger and harder statement, likely its own follow-on).

## QA obligations (draft — refine after Step 0)

1. A small fixture (K₂ or a path on 3 vertices) with a hand-computable
   bound matrix `A i` and a concrete `x` (e.g. `onesVec` or the Fiedler
   vector on the fixture), the resulting scalar bound evaluated in
   closed form.
2. The `n = 0` degenerate case (empty sum, vacuous bound), consistent
   with the axiom's own zero-sequence QA pattern.
3. A boundary witness where the semidefinite hypothesis fails for one
   term — the hypothesis-free form refuted in proved form on the same
   fixture, per this session's established fence discipline.

## Acceptance bar

- Step 0 delivers a written verdict — including an explicit check of
  whether this duplicates unstarted event-stream-frontier work — before
  any shelf Lean is written.
- If Step 1 proceeds: zero new axioms; `matrix_hoeffding` appears
  honestly in `#print axioms` on the new public theorem;
  `VariationalTransfer.lean`'s existing PSD/Rayleigh lemmas are reused,
  not re-derived.
- `docs/7_SGT_RADAR.md` axis 7 (Algorithms/Randomness) is the natural
  re-score target.

## Companion

[Spectral Sparsification via Leverage-Score Sampling](spectral-sparsification-via-leverage-scores.md)
(the harder, Bernstein-based sibling consumer), `docs/6_SGT_BACKLOG.md`,
`docs/7_SGT_RADAR.md` axis 7.

## Delivery record (2026-08-28, run `20260828T090419Z-run-1`)

### Step 0 — the verdicts, recorded before any shelf Lean (spiked first: `wip/mh0_spike.lean`, iterated to zero errors/warnings)

1. **The junk/defect surface check (the charge the scalar audit's
   2026-08-28 residual added to this Step 0) found a materially false
   corner shared by all three matrix axioms.** `matrix_hoeffding` itself
   carries no integral clauses at all (centering-free — the
   `MatrixMDS`-shaped junk surface does not apply to it), but at
   `Fintype.card V = 0`, `t = 0` it instantiates to the provable
   `1 ≤ 0`: the tail event `{ω | ‖∑ X i ω‖ ≥ 0}` is all of `Ω`
   (nonnegativity of the norm), so a probability measure gives `1`,
   while the dimension prefactor makes the bound
   `2 · 0 · exp … = 0`. The same corner falsifies `matrix_bernstein`
   and `matrix_azuma_hoeffding` verbatim (identical prefactor and event,
   denominators irrelevant at `t = 0`). This is the
   pre-repair-`cheeger_lower_bound`/`hoeffding_lemma` failure class: an
   axiom inconsistent at a degenerate corner makes every conditional
   theorem vacuous, so the repair was mandatory *before* any consumer.
   Spike evidence: the refutation was elaborated directly against the
   then-current axiom (`hoeffding_refuted_fin0 : False`).
2. **The Step-0 checks of the draft statement:** (1) the norm→form
   transfer exists on the shelf — `abs_quadForm_le_of_l2OpNorm_le`
   (Sparsification Slice 3), no new proof needed; (2) the
   "event-stream frontier" pointer is `GraphTheory/Dynamics.lean` +
   `Derived/EventStream.lean`, the *Azuma* (martingale-difference)
   route — no Hoeffding consumer exists anywhere, so this proposal
   composes rather than duplicates (the hypothesis sets are genuinely
   disjoint: adapted sequences vs independent families); (3) a fixed
   non-random test vector suffices, **but it must be nonzero** — at
   `x = 0` the event is all of `Ω` and the quadratic-form corollary is
   false for large `t` (found in the spike; the guard `x ≠ 0` is in the
   delivered statements).
3. **Premise corrections:** the draft's `|quadForm …| ≥ t * ‖x‖²`
   uses the dot-product norm (delivered at `t * (x ⬝ᵥ x)`, matching the
   transfer lemma); the named `VariationalTransfer` lemmas
   (`normalizedLaplacian_psd`, `rayleigh_normalizedLaplacian_degreeSqrt`)
   are no longer zero-consumer (the irregular-Cheeger program consumed
   them in-file), so this delivery's fresh loading is
   `BernoulliProduct`'s matrix transfer layer (second consumer family),
   the `rankOne` algebra, `laplacian_add`-family engine, and
   `dotProduct_mulVec_comm_of_isSymm` (first consumer outside the
   projector-uniqueness layer).

### The repair (Slice A, delivered first)

- All three axioms repaired in place with the `[Nonempty V]` guard
  (statement-history docstrings record the refuting corner and the
  derivation that the cited Tropp theorems carry `d ≥ 1` implicitly).
  At `t = 0` the repaired statements are honest on nonempty `V`:
  `(1 : ℝ≥0∞) ≤ 2 d` (`two_card_bound_honest_QA`).
- Refutation records in `Matrix_QA.lean`, in hypothesis form (the old
  shape instantiated at the corner): `old_matrix_hoeffding_refuted_fin0_QA`,
  `old_matrix_bernstein_refuted_fin0_QA`, `old_matrix_azuma_refuted_fin0_QA`
  — each `False` from the instantiated old inequality, standard three
  axioms only.
- Consumer threading: `eventStreamTail` and the two
  `sparsification_*_tail` theorems take the guard as a binder;
  `eventStreamProjectorDrift` derives it internally from its own
  `k : Fin (Fintype.card V)` (no signature change); the three zero-QAs
  take it per-theorem. QA warning baselines unchanged (16/3, verified
  against the stashed pre-change tree).

### Step 1 — the consumer (Slice B)

- New `Scaffold/Mathlib/GraphTheory/EdgePerturbation.lean` (umbrella
  import added), three hard-crust layers: the single-edge algebra
  (`edgeAdj`, `deg_edgeAdj`, and `laplacian_edgeAdj` — the identity
  `L(edge i j w) = w • (e_i − e_j)(e_i − e_j)ᵀ` joining the design to
  the `rankOne` algebra, valid also at `i = j` where both sides
  vanish); the `Matrix.PosSemidef` helpers the pin lacks
  (`posSemidef_smul_nonneg`, `rankOne_posSemidef`,
  `posSemidef_mul_self_of_isSymm` — squares of symmetric matrices are
  PSD, through the self-adjoint coordinate form); and the centered
  Bernoulli edge-perturbation design (`perturbEdgeLap`,
  `perturbSummand = (δ_e − p_e) • L_e`) with every repaired-axiom clause
  *proved*: `stronglyMeasurable_perturbSummand`,
  `indepFun_perturbSummand` (both through BernoulliProduct's matrix
  transfer layer), `perturbSummand_isSymm`, and
  `perturbSummand_sq_le` (`X_e² ⪯ L_e²`).
- **Finding (statement-shape): the design is sign-free.** No hypothesis
  on the weight matrix `A` at all — not nonnegativity, not symmetry —
  because `L_e` is symmetric for every weight and squares of symmetric
  matrices are PSD; the only load-bearing hypothesis of the clause set
  is the sampling interval `p e ∈ [0, 1]` (through
  `(δ_e − p_e)² ≤ 1`). Fenced in QA at `p ≡ 2` (the clause provably
  fails); witnessed at a negative weight (`epNeg_clause_QA`).
- New `Scaffold/Derived/EdgePerturbationTail.lean` (umbrella import
  added): the generic **`matrix_hoeffding_quadForm`** (the fixed-nonzero-
  vector quadratic-form pullback of the axiom, `x ≠ 0` load-bearing) and
  the assembled **`edgePerturbation_norm_tail`** +
  **`edgePerturbation_quadForm_tail`** at the design, with the `Fin n`
  summand transport by `Fintype.equivFin` + `Equiv.sum_comp`
  (Sparsification's Finding-B pattern, second consumer). Both tails are
  conditional on `matrix_hoeffding` alone (`#print axioms` via
  `wip/mh_axcheck.lean`).
- QA `Scaffold/QA/Derived/EdgePerturbation_QA.lean` (+12; 2749 → 2765
  repo-wide with the Matrix_QA repair records): the variance statistic
  pinned **exactly** (`∑_e L_e² = 4 • v vᵀ`; `‖∑_e L_e²‖ = 8` — with the
  rank-one norm pin `‖v vᵀ‖ = 2` proved *two-sided*, the lower side by
  the squared-action bound); the design arithmetic at a concrete
  outcome (all-true at `p ≡ ½` sums to exactly the unit edge Laplacian,
  quadratic form `1` at `e₀`); the closed-form tail instance
  `4 exp(−1/16)`; the degenerate zero-weight graph (event empty at
  `t > 0`); the interval fence; and the sign-free witness.

### Technique findings (for future runs)

- This pin's `sub_smul` is `(r - s) • y = r • y - s • y` — to prove
  `M - c • M = (1 - c) • M`, drive the rewrite from the *equation's
  RHS* (`rw […, sub_smul, one_smul]` closes by rfl), not by seeking the
  difference form on the left.
- On `Fin 2`, the literal `2 • M` in a statement can elaborate as the
  ℕ-tower `nsmul` (`(2 : ℕ) • M`) rather than ℝ-smul — ascribe every
  scalar in such statements (`(2 : ℝ) • …`), or `rw`/`rfl` fail with a
  confusing display.
- `Matrix.IsSymm` is a def (`Aᵀ = A`), not a structure: anonymous
  constructors fail; `show (M)ᵀ = M` then prove the equation (and
  `Matrix.IsSymm.eq` for the converse direction).
- The `omit … in` must precede the docstring, not sit between it and
  the theorem.
- PosSemidef's quadratic-form clause at ℝ is *defeq* (not syntactic)
  `0 ≤ x ⬝ᵥ (M *ᵥ x)` with `star x ≡ x` — `show` transfers it, but
  `rw` cannot; restate at the dot-product form before rewriting.
- `ring` fails on `∑ x, -(f x ^ 2 * 12) = ∑ x, -12 * (f x * f x)`
  (bound-variable atoms); `Finset.sum_congr rfl (fun x _ => ring_nf …)`
  closes it.
- `Fintype.sum_prod_type` + `Fin.sum_univ_two` produce pair-literals
  that do not always syntactically match `(0, 0)`-spelled hypotheses —
  prefer per-branch `fin_cases` computation over rewriting by
  pair-facts when the fixture is small.

### Verification

Spike first (`wip/mh0_spike.lean`, all pieces to zero errors/warnings
before any shelf edit, including the live refutation against the
pre-repair axiom); `lake env lean` zero errors on every touched module
(the three axiom files, `Matrix_QA.lean` at its exact 16-warning
baseline, `EventStream_QA.lean` at 3, the new modules clean, the Derived
consumers clean); explicit `lake build` targets ✔; `#print axioms` via
`wip/mh_axcheck.lean` — engine and QA hard crust exactly
`propext, Classical.choice, Quot.sound`, the two Derived tails and the
two axiom-instantiating QA pins honestly carrying `matrix_hoeffding`
alone, the bernstein/azuma zero-QAs honestly carrying theirs; **full
`lake build` ✔ (2404/2405, "Build completed successfully") immediately
followed by `check_build_completeness.py` — after the documented
single-module remediation, 126/126 fresh, 0 stale, 0 missing, exit 0**;
`lint_axioms` (10, no issues), `check_citations`, `check_markdown_links`
pass; scoreboard regenerated idempotent (**2765/10/0**); **map freshness
exit 0** after the stats-stamp sync (mandatory — this delivery changes
the proposal's status header; the check caught the 2749 → 2765 drift on
first run, as designed).

### Residuals and priced follow-ons

- ~~The sampled-graph packaging (`∑_e (δ_e − p_e) • L_e` rewritten as
  `laplacian (sampledAdj ω) − laplacian (expectedAdj)` through
  `laplacian_smul`/`laplacian_sum` — the latter two engine lemmas are
  not yet on the shelf) is the natural next slice; the theorem's meaning
  currently rests on `laplacian_edgeAdj` identifying the blocks as
  single-edge Laplacians.~~ **DELIVERED 2026-08-28** (run
  `20260828T132541Z-run-1`) — the follow-on delivery record below.
- ~~The uniform (sup-over-x / existential-x) quadratic-form form —
  `sparsification_quadForm_tail`'s event shape — is an alternative
  packaging of the same bound.~~ **DELIVERED 2026-08-28** (run
  `20260828T214358Z-run-1`) — the eigenvalue-level follow-on delivery
  record below, whose
  `edgePerturbation_quadForm_uniform_tail` is exactly this packaging
  (with the `x ≠ 0` guard the refutation fence proves load-bearing).
- The `2 d` dimension prefactor is not tightened to the matrix-martingale
  golden factor anywhere in this family (a Tropp-source-level question,
  not a repair).

### Follow-on delivery record: the concentration → subspace-stability pipeline (2026-08-28, run `20260828T132541Z-run-1`)

The standing handoff's named next candidate after this delivery — the
first join of the two most recent center deliveries — **DELIVERED**:
`Derived/EdgePerturbationDrift.lean`'s
`edgePerturbation_fiedlerSubspace_drift` and
`edgePerturbation_fiedlerLine_drift` compose `fiedlerLine_stability` /
`fiedlerSubspace_stability` (2026-08-28) with `edgePerturbation_norm_tail`
(this proposal) in the `eventStreamProjectorDrift` inclusion idiom:
`μ{‖Fiedler rotation at ω‖ ≥ t/δ} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))`
whenever the base graph's gap satisfies `t + δ ≤ λ₃ − λ₂`. One interface
improvement over the precedent: the separation is discharged
per-outcome from the *deterministic base gap* via the proved
`weyl_inequality` on the tail event's complement (the helper
`separation_of_norm_lt`), so the drift theorems carry **no per-outcome
spectral hypothesis** — `eventStreamProjectorDrift`'s `hgap` is a
per-outcome hypothesis by contrast.

The priced follow-on above landed as the pipeline's deterministic
hinge: `Spectral.lean`'s `laplacian_smul`/`laplacian_sum` (with
`deg_smul`; delivered here, exactly the two engine lemmas the residual
named) and `EdgePerturbation.lean`'s `perturbWeight` — the random
*weight-space* perturbation `∑_e (δ_e − p_e) • edgeAdj_e` with entry
formulas (off-diagonal: the two ordered pairs on `{i, j}`; diagonal:
one, no double count) — satisfying the **packaging identity**
`laplacian (perturbWeight A p ω) = ∑_e perturbSummand A p e ω`, the
route through which the tail's Laplacian-level norm bound reaches the
graph-level perturbation the Davis–Kahan side consumes.

**QA +20 (2765 → 2785, `EdgePerturbation_QA.lean`'s drift section):** the
packaging identity pinned by two independent routes on K₂ (raw
weight-space arithmetic `perturbWeight = epK2 → laplacian = v vᵀ` vs
the design route through the identity theorem joined to the existing
`epK2_perturbSum_allTrue` — a wrong `laplacian_sum`/`laplacian_smul`
breaks exactly one); the three-path variance statistic exact
(`∑ₑ L_e² = 4 • L(P₃)` through the rank-one squares, `‖·‖ = 12` through
the pinned `λ₃ = 3` at the `l2OpNorm_eq_max_abs_evals` bridge — the K₂
`= 8` pin's ordered-pair bookkeeping checked on a two-edge graph); the
per-outcome stack at `p ≡ ¼` (entry formula with survival factor
`½ + δ_{ij} + δ_{ji}`, nonnegativity, and support-graph equality —
every edge survives in every outcome, the path's connectivity
load-bearing at every corner of the outcome space); and the
**closed-form Fiedler-line drift instance** `μ{‖rotation‖ ≥ 1} ≤
6 exp(−1/24)` (gap discharge `1 + 1 ≤ 3 − 1` through the two exact
spectrum pins).

**Verification:** spike first (`wip/csd_spike.lean`, every piece to
zero errors/warnings before any shelf edit); `lake env lean` zero
errors on all four touched files (Spectral at exactly its pre-existing
8-warning baseline); explicit `lake build` targets ✔; `#print axioms`
via `wip/csd_axcheck.lean` on all 29 audited declarations — 27 at the
standard three, exactly the two Derived drift theorems and the
drift-QA instance carrying `matrix_hoeffding` alone (the honest
conditional structure); **full `lake build` ✔ (2405/2406) immediately
followed by `check_build_completeness.py` — after the documented
single-module mtime remediation, 127/127 fresh, 0 stale, 0 missing,
exit 0**; `lint_axioms` (10, no issues), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated idempotent
(**2785/10/0**); **map freshness exit 0** after the stats-stamp sync
(the check caught the 2765 → 2785 drift on first run, as designed).

**Technique findings** (the spike's catch record): `fin_cases`-produced
`⟨k, ⋯⟩` constructor literals block both `rw` matching (lemma
instantiated at numeral `0 : Fin n` does not match `⟨0, ⋯⟩`
syntactically) and simp's evaluation of `Fin.val`-cast if-conditions —
the robust replacement is the disjunction-substitution idiom
`rcases (hfin : ∀ k : Fin n, k = 0 ∨ … ∨ k = n-1) i with rfl | … | rfl`
(proved by `fin_cases` on a *disjunctive* goal, where it works), which
substitutes genuine numerals; hypotheses with implicit `{i}{j}` binders
before explicit ones must be passed by name (`(hij := h)`) or the proof
lands in the first explicit slot; the positional-argument trap also
strikes numeric binders between proofs (a missing `δ : ℝ` value makes
`one_pos` land in a `Prop`-shaped slot with a confusing "numerals are
data" error); `simp (config := {decide := true})` is the working tool
for if-conditions at `Fin n × Fin n` numerals that plain `simp` leaves
half-normalized (`Prod.zero_default` canonicalizes `(0,0)` to the
product numeral, breaking `if_neg (by decide …)` patterns while the
goal still displays them as pairs); `Matrix.transpose_smul` (not
`smul_transpose`); `mul_le_mul_of_nonneg_right` + `linarith` where
`mul_nonpos` does not exist in this pin; `rw` with a `≤`-hypothesis is
a category error — `lt_of_le_of_lt` is the route; `Fin.ext (by simp)`
for the top-index conversion in `l2OpNorm_eq_max_abs_evals`; and the
stale-olen recurrence at every import boundary.

**Status: the follow-on delivered; this proposal remains COMPLETE.**

### Follow-on delivery record: the eigenvalue-level tail — spectral-gap concentration (2026-08-28, run `20260828T214358Z-run-1`)

The standing handoff's named "third concentration-axiom consumer"
candidate class, delivered in its SGT-native member — the join of the
delivered norm tail with the *proved* `weyl_inequality`, which is this
proposal's own filename namesake ("spectral-gap estimation") and the
sup-over-x form its Step-0 note 3 deferred. Four theorems in
`Derived/EdgePerturbationTail.lean`'s new eigenvalue section, all
**conditional on `matrix_hoeffding` via the norm tail alone** with the
transfer side pure hard crust (Weyl — proved since 2026-08-20 — plus
the packaging identity `laplacian_perturbWeight`, `laplacian_add`,
`evals_congr`, the `separation_of_norm_lt` idiom of the drift module):

- `edgePerturbation_eval_tail` — `μ{t ≤ |λᵢ(L(A+E_ω)) − λᵢ(L A)|} ≤
  2 d exp(−t²/(2‖∑ₑ L_e²‖))` at *every* sorted index: the resampled
  graph's whole Laplacian spectrum concentrates around the base's. This
  is the packaging the Cheeger/Fiedler/mixing interfaces read directly —
  the norm tail lands in operator language, the center's currency is
  `evals`.
- `edgePerturbation_eval_lower_tail` — the one-sided gap-survival form
  `μ{λᵢ(L̃_ω) ≤ λᵢ(L) − t} ≤ …` (event inclusion from the two-sided
  form: `λ' ≤ λ − t` forces `t ≤ |λ' − λ|`).
- `edgePerturbation_lambda2_lower_tail` — the λ₂-spelled corollary at
  the `lambda2` interface (`2 ≤ card V`), the Fiedler-facing robustness
  statement.
- `edgePerturbation_quadForm_uniform_tail` — the priced residual below,
  struck through on delivery: the existential-vector packaging whose
  complement reads `|xᵀ L(E_ω) x| < t (x ⬝ᵥ x)` for every nonzero
  vector simultaneously.

**QA +13 (2830 → 2843, `EdgePerturbation_QA.lean`'s spectral-gap
section):** the base and perturbed `K₂` spectra pinned exactly by the
kernel-plus-trace route (`λ₂ = 2`; `λ₂ = 4` at the all-true outcome
where the resampled graph is the weight-`2` edge —
`epK2_perturbed_allTrue_eq` joining the raw weight-space route to the
existing `perturbWeight` pin), **the Weyl transfer tight at a genuine
design outcome** (`epK2_weylTight_allTrue_QA`: `|4 − 2| =
‖L(E_ω)‖ = 2`, the two sides by independent routes — kernel-plus-trace
spectra vs the packaging pin joined to the two-sided rank-one norm; a
constant mistake anywhere on the transfer path breaks the equality),
the closed-form instances on `K₂` (`4 exp(−1/16)` eigenvalue and
uniform-form, `4 exp(−4/16)` λ₂) and the three-path (`6 exp(−1/24)` at
index 2), and the **`x = 0` guard fence**
(`epK2_uniform_guard_fence_QA`): the un-guarded existential event is
provably all of `Ω` (`x = 0` always witnesses `t · 0 ≤ |0|`) with
measure exactly `1`, while at `t = 7` the would-be bound
`4 exp(−49/16) < 1` (from `4 < 1 + 49/16 ≤ exp(49/16)` via
`Real.add_one_le_exp`) — the un-guarded statement *refuted* in proved
arithmetic, the guard load-bearing rather than decorative.

**Verification:** spike first (`wip/ept_spike.lean`, every piece to
zero errors/warnings before any shelf edit); `lake env lean` zero
errors/zero warnings on both touched modules (the Derived module after
its explicit olen rebuild — the stale-olen recurrence again — and the
QA file); `#print axioms` via `wip/ept_axcheck.lean` on all 17 audited
declarations: the 9 hard-crust QA lemmas (including the tightness pin
and the guard fence) exactly `propext, Classical.choice, Quot.sound`;
the four Derived theorems and the four closed-form QA instances
honestly carrying `matrix_hoeffding` alone; **full `lake build` ✔
(2405/2406) immediately followed by `check_build_completeness.py` —
127/127 fresh, 0 stale, 0 missing, exit 0**; `lint_axioms` (10, both
findings allowlisted-confirmed), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**2843/10/0**);
map freshness exit 0 after the stats-stamp sync.

**Technique findings** (this delivery's catch record, on top of the
recorded ones): the auto-bound-identifier trap — an unresolved fixture
name in a QA statement silently becomes an *auto-bound implicit
variable*, so the theorem typechecks while every later `rw` with the
concrete fixture's pin fails with a confusing pattern mismatch (the
fix is opening the fixture's namespace; the symptom is the pin's
constant displaying with a namespace prefix inside the rewrite
pattern); the `⟨0, by omega⟩ : Fin (Fintype.card V)` vs `(0 : Fin n)`
spelling split inside `linarith` — two defeq-but-syntactically-distinct
eigenvalue terms do not cancel, and the robust route is restating each
pinned value at the `Fin n` spelling through a type-ascribed `have`
(the `∑ i : Fin n, … := hsum` transport idiom) before any arithmetic;
`Matrix.trace` is `∑ i, M i i` by `rfl` but only after the matrix's
spelling is fully concrete — a `Finset.sum_congr` at an abstract
spelling leaves `2 * 2 = 4`-shaped numeral goals that `norm_num`
closes and `simp` alone displays unresolved; and the positional-binder
order trap between a `variable (A) (p)` section and a theorem's own
`(hA)` binder — the section variables prepend, so a spike proof
transplanted with its original argument order fails with "application
type mismatch" naming the second argument.

**Status: both follow-ons now delivered; the proposal's priced
residual list is empty. The matrix-martingale golden-factor question
(a Tropp-source-level question, not a repair) remains the only
unpriced observation on record.**

------

### Follow-on delivery record (2026-08-28, run `20260828T230752Z-run-1`): the Cheeger-window consumer of the λ₂ tail

The standing handoff's named "conductance/Cheeger-level consumer of the
new λ₂ tail" (priced, not owed, in the eigenvalue delivery's next-handoff
note) — **delivered as zero new axioms (count stays 10; `#print axioms`
via `wip/cheegerfloor_axcheck.lean` on all 16 audited declarations: the
two engine lemmas and ten hard-crust QA lemmas exactly `propext,
Classical.choice, Quot.sound`; the two Derived theorems and the two
closed-form QA instances honestly carrying `matrix_hoeffding` alone).
QA 2843 → 2855 (+12, `EdgePerturbation_QA.lean`'s Cheeger-window
section).**

Three pieces:

1. **The engine pair** (`GraphTheory/Cheeger.lean`, public API): the
   combinatorial-Laplacian spelling of both Cheeger bounds on
   `d`-regular graphs — `cheeger_lower_bound_laplacian`
   (`d · φ²/2 ≤ lambda2`) and `cheeger_upper_bound_laplacian`
   (`lambda2 ≤ 2 d φ`) — pure composition of the proved pair with the
   regularity bridge `smul_regularNormalizedLaplacian` (`L = d • L_sym`)
   and the positive-scaling lemma `secondEval_smul_of_pos` at
   `lambda2_eq_secondEval`. This closes the regular-Cheeger ↔ `lambda2`
   interface gap for every future consumer (the Fiedler, Alon–Boppana,
   and edge-perturbation families all read the combinatorial spelling).
2. **The Derived theorems** (`Derived/EdgePerturbationTail.lean`'s
   CheegerWindow section): `edgePerturbation_lambda2_cheeger_floor` —
   `μ {λ₂(L(A+E_ω)) ≤ d·φ(A)²/2 − t} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))` (a
   pure `measure_mono`: the floor-crossing event sits inside the
   delivered λ₂ lower-tail event because the base `λ₂` is above the
   floor) — and `edgePerturbation_connectivity_bracket`, the two-sided
   window: leaving `[d·φ²/2 − t, 2dφ + t]` implies leaving the
   two-sided eigenvalue tail event, at the *same* constant (no union
   bound needed — the window contains the eigenvalue ball
   `[λ₂ − t, λ₂ + t]`), with **both Cheeger directions load-bearing on
   the inclusion** (a wrong constant on either engine side breaks the
   corresponding half of the `measure_mono`).
3. **QA (+12)**: the φ(K₂) = 1 and 1-regularity pins transferred at
   definitional equality from `Cheeger_QA`'s fixture (the join point to
   the Cheeger QA stack), the base λ₂ = 2 at the `lambda2` interface,
   the engine window instantiated with the **ceiling attained at
   equality** (`λ₂ = 2 = 2·(1·φ)` — the third conjunct), the closed-form
   floor and bracket tail instances at `t = 1/2`
   (`4 exp(−1/64)`), the all-false outcome stack (perturbed adjacency
   = 0 entrywise; λ₂ = 0 by kernel-plus-trace), **non-vacuity witnesses
   for both window sides** (the all-false outcome below the floor with
   `λ₂ = 0` attained at equality; the all-true outcome above the
   ceiling at `λ₂ = 4 ≥ 5/2`).

**Verification:** spike first (`wip/cheegerfloor_spike.lean`, every
piece to zero errors/warnings before any shelf edit); direct `lake
build` targets ✔ on all three touched modules; `#print axioms` exactly
as designed (16 declarations); **full `lake build` ✔ (2405/2406)
immediately followed by `check_build_completeness.py` — 127/127 fresh,
0 stale, 0 missing, exit 0**; `lint_axioms` (10, both findings
allowlisted-confirmed), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**2855/10/0**); map freshness exit 0 after the
stats-stamp sync (2843 → 2855 in both map files).

**Technique findings** (small, this slice): the direct
`have h0 := laplacian_evals_zero …` keeps the lemma's `⟨0, by omega⟩`
spelling and thereby re-trips the recorded `Fin`-spelling linarith trap
— the type-ascribed `have h0 : … (0 : Fin 2) = 0 := …` restatement is
the fix, exactly as the previous delivery recorded; `(degreeMatrix 0
- 0).trace` needs the unfold order `rw [laplacian, sub_zero, hd0,
Matrix.trace_zero]` with an explicit `degreeMatrix 0 = 0` `have` (`simp
[degreeMatrix, deg]` alone does not unfold the `dite` under
`Matrix.trace`).

**Honesty note on fences:** the engine pair's guards (`hnonneg`,
`0 < d`) are inherited from the proved Cheeger pair and the scaling
lemma, and are *proof*-load-bearing there; at the two-vertex signed
1-regular fixture (`d = −1`) the un-guarded floor statement still holds
(`−1/2 ≤ 0` — both sides collapse), so no K₂-shaped refutation fixture
exists for the dropped-guard statement; the QA obligation is met by the
instances above (both theorem instances exercised, one bound attained
with equality) rather than by a fence.

**Status: the Cheeger-window consumer delivered; the proposal's priced
residual list remains empty (the matrix-martingale golden-factor
question, a Tropp-source-level observation, remains the only unpriced
item on record).**
