# hoeffding_inequality's first theorem consumer: vertex-degree concentration under edge resampling

**Status:** COMPLETE — created and delivered in one run (2026-08-29,
run `20260829T110514Z-run-1`), per the same-run pattern of
`proposals/degree-eigenvalue-sandwich.md`. Zero new axioms (count stays
10); QA 2963 → 2977 (+14, `EdgePerturbation_QA.lean`'s degreeTail
section). All priced follow-ons delivered the same day: the Bernstein
twin (run `20260829T125827Z-run-1`, QA → 2987), the admissibility
dissolution (run `20260829T142812Z-run-1`, QA → 3003 — the window
family's first unconditional measured event), and the dissolution
completion across the family's floor and swept-cut members (run
`20260829T155521Z-run-1`, QA → 3008 — every window-family measured
event now unconditional; see the three delivery records below).

## The obligation this discharges

Of the ten admitted axioms, four had **zero theorem consumers** outside
their own files after the 2026-08-28 integrability audit:
`hoeffding_inequality`, `bernstein_inequality`,
`bernstein_bounded_variance`, and `hoeffding_lemma`. The audit proved
their hypothesis sets safe (junk-integral-free, right constants) but
could not make them *load-bearing*: a misstated clause — wrong
denominator, wrong bound direction, wrong prefactor — would break
nothing downstream. This proposal gives `hoeffding_inequality` its
first consumer at the same centered Bernoulli edge-resampling design
the delivered window family lives on, closing the same gap class as
`matrix_bernstein` (sparsification, 2026-08-27),
`hoeffding_empirical` (empirical stationary distribution, 2026-08-27),
and `matrix_hoeffding` (edge perturbation, 2026-08-28).

## The SGT consumer it serves

The irregular Cheeger window family's honesty notes record that the
λ₂/norm tails carry **zero degree information** (`L(E_ω)·1 = 0`
identically — the Laplacian of any symmetric matrix kills the
constants), which is why `perturbAdmissible`'s degree clauses
(`dmin ≤ deg G_ω v ≤ dmax`) are event-internal hypotheses rather than
derived facts. The degree tail is the missing complementary
concentration: the λ₂ tail controls the operator, the degree tail
controls the window. The all-vertices union bound delivered here is
the first step toward deriving admissibility rather than hypothesizing
it; the full dissolution (union with the window bracket, plus the
nonnegativity design condition `p e + p eᵀ ≤ 1` making the resampled
adjacency nonnegative automatically) is the priced follow-on below.

## Assessed from

`Scaffold/Mathlib/Probability/BernoulliProduct.lean` (the sampling
space: `measurable_coord`, `indepFun_coord`, `integral_delta` — the
exact scalar clause machinery, none of it previously consumed at the
scalar codomain), `Scaffold/Mathlib/Probability/Concentration/Scalar/Hoeffding.lean`
(`hoeffding_inequality`, plus the audit's `integrable_of_bounded_measurable`
safety lemma), and `Scaffold/Mathlib/GraphTheory/EdgePerturbation.lean`
(the design: `perturbAdj`/`perturbWeight`, the entry formulas, and
`deg_edgeAdj`'s single-edge row sums).

## What was delivered

**Engine (pure hard crust, `EdgePerturbation.lean`'s new section 5 +
`Spectral.lean`):**

- `deg_add`/`deg_sum` (`Spectral.lean`, beside `deg_smul`): the
  degree-level linearity package the identity rides on.
- `degPerturbWeight A v e := if v ∈ {e.1, e.2} then A e.1 e.2 else 0`
  and `degPerturbSummand A p v e ω := (δ_e(ω) − p e) · w_v(e)` — the
  centered Bernoulli degree design.
- `deg_resampled`: **the degree-deviation identity**
  `deg (A + perturbWeight A p ω) v = deg A v + ∑ₑ degPerturbSummand A p v e ω`,
  through `deg_add`/`deg_sum`/`deg_perturbAdj`/`deg_edgeAdj` — a wrong
  entry formula or row-sum shape breaks exactly this.
- All four axiom clauses proved at the design:
  `measurable_degPerturbSummand` (`measurable_of_finite` composition —
  the same route as the matrix layer), `indepFun_degPerturbSummand`
  (`indepFun_coord.comp`), `degPerturbSummand_abs_le`
  (`|δ − p| ≤ 1` at `p ∈ [0,1]` — the design stays **sign-free**: no
  hypothesis on `A`), and `integral_degPerturbSummand_eq_zero`
  (the centering through `integral_delta` + the audit's
  `integrable_of_bounded_measurable`; no `p e ≠ 0` guard needed,
  unlike the sparsification design's division-based centering).

**Derived (conditional on `hoeffding_inequality` alone,
`EdgePerturbationTail.lean`'s degreeTail section):**

- `edgePerturbation_degree_tail`:
  `μ {|deg G_ω v − deg A v| ≥ t} ≤ 2 exp(−t²/(2 S_v))` at
  `S_v = ∑ₑ w_v(e)²` (both incident ordered pairs counted — the
  double count is the design's honest price; on symmetric `A` without
  loops `S_v = 2 ∑_u (A v u)²`), with the `Fin n` transport by
  `Fintype.equivFin` + `Equiv.sum_comp` (the established Finding-B
  pattern).
- `edgePerturbation_degree_tail_all`: the union bound over vertices,
  stated at the exact per-vertex sum. Collapsing to a uniform exponent
  `2|V| exp(−t²/(2B))` needs a per-vertex `0 < S_v ≤ B` — a vertex
  with `S_v = 0` is pair-isolated (its deviation is identically zero,
  but division-monotonicity is junk there), so the collapse is left to
  consumers whose graphs satisfy it and demonstrated numerically in QA
  where both statistics are equal.

**Degenerate-corner analysis (Step 0, before stating):** the scalar
axiom needed no repair and the tail needs no `Nonempty` guard: the
prefactor is the constant `2`, which — unlike the matrix trio's
`2 · card V` that collapsed to `0` at `card V = 0` — never collapses,
and at `S_v = 0` (junk division `−t²/0 = 0`) the bound reads `2 ≥ μ`,
trivially true while the event itself is empty at `t > 0`. This is
the transfer of the 2026-08-28 degenerate-dimension hazard analysis to
the scalar side: safe by structure, now with a consumer that would
fail to typecheck if the clause shapes were wrong.

**QA (+14, `EdgePerturbation_QA.lean`'s degreeTail section):**

- the variance statistic pinned exactly (`S₀ = 2` on `K₂`) with the
  single-counted statistic `1` **refuted** — the ordered-pair double
  count is load-bearing in the exponent;
- the deviation identity at the all-true outcome by **two independent
  routes** (raw weight-space: the resampled graph is `2 • K₂`, degree
  `2`; vs the design's identity `1 + ½ + ½` — a wrong identity breaks
  exactly route B) and at the all-false outcome (`0 = 1 − ½ − ½`,
  joined to the corner-audit's existing raw pin);
- the closed-form tail instance `μ {|dev| ≥ 1} ≤ 2 exp(−1/4)`;
- the **exact event measure** `1/2`: the deviation event at `t = 1` is
  the agreement event of the two incident coordinates, computed through
  the design's own independence machinery (`indepFun_coord` +
  `toMeasure_cyl`), independently of the tail theorem — so the bound's
  slack at fixture scale is on the record (`1/2 ≤ 2 exp(−1/4)`), the
  same junk-measure obstruction the window family records (no
  wrong-constant refutation exists at fixture scale; the exactness pins
  carry the falsification content);
- the union-bound instance, with the collapse to `4 exp(−1/4)`
  demonstrated numerically (both vertices' statistics equal on `K₂`)
  and the union event's measure pinned `1/2` — on `K₂` both deviations
  are the same function of the coordinates, so the union bound
  double-counts, honestly.

`#print axioms` (via `wip/degconc_axcheck.lean`, 23 declarations): all
engine and hard-crust QA lemmas exactly `propext, Classical.choice,
Quot.sound`; the two Derived tails and the two axiom-instantiating QA
pins honestly carrying `hoeffding_inequality` alone.

## Technique findings

- The `omit [Fintype V]` linter note on the scalar clause lemmas:
  `measurable_coord` is `measurable_pi_apply` (hypothesis-free), so
  unlike the matrix layer's `StronglyMeasurable.of_finite` route the
  scalar measurability clause genuinely needs no `Fintype` — omit it.
- `rw` cannot rewrite with a ∀-quantified hypothesis under the union
  bound's `∑ v` binder (`fun v => …` in the exponent); `simp only
  [hvar]` rewrites under binders and is the right tool there.
- `integral_sub` with explicit `(f := …) (g := …)` name-arguments is
  the reliable spelling for decomposing `∫ (δ_e − p_e) • w`: the
  anonymous form's higher-order pattern matching picks the wrong
  split.
- The pin has no `∫ (f · c) = (∫ f) · c` for Bochner real
  multiplication; `smul`-spelling the integrand (`(δ_e − p_e) • w`,
  `rw [smul_eq_mul]`) routes through `integral_smul_const` cleanly.
- The `(0, 1 : Fin 2 × Fin 2)` ascription parses as `(0, (1 : Fin 2 ×
  Fin 2))` and errors late; the parenthesized `((0, 1) : Fin 2 × Fin
  2)` is the required spelling.
- The QA module's `Try this: ring_nf` baseline moves from one note to
  three (two added by this delivery's `simp`/`norm_num` calls —
  cosmetic linter suggestions, no elaboration effect; recorded here so
  the next run's baseline comparison is honest).

## Remaining priced follow-on (not owed)

The **admissibility dissolution**: union the all-vertices degree tail
with `edgePerturbation_normalized_connectivity_bracket` to give an
*unconditional* high-probability window — needs (a) the degree-window
arithmetic (base degrees in a shrunk window + |dev| ≤ t ⇒ resampled
degrees in the base window, at the bracket instantiated on the widened
window), and (b) the nonnegativity conjunct derived from the design
condition `p e + p (e.2, e.1) ≤ 1` (then the resampled entry
`A i j (1 + δ_{ij} + δ_{ji} − p_{ij} − p_{ji})` is nonnegative at every
outcome; at the classical uniform design `p ≡ ½` this is exactly
satisfied). This dissolves the window family's recorded honesty note
("the admissibility window is proof-load-bearing, not
fixture-refuted") on its degree half. Gated on nothing — priced, not
owed, per the one-milestone-per-run discipline.

The **Bernstein twin**: the same design instantiates
`bernstein_inequality` (variance clause `∑ E[X_e²] = ∑ p(1−p) w²`
through `∫ δ_e² = ∫ δ_e = p e`) for the variance-adaptive degree tail
`2 exp(−t²/(2(v + at/3)))` — strictly stronger at small `p`; a second
consumer for the second zero-consumer scalar axiom at marginal clause
cost. Priced, not owed.

## Bernstein-twin follow-on — DELIVERED 2026-08-29 (run `20260829T125827Z-run-1`)

The priced follow-on above was delivered the same day by the next run,
closing the zero-consumer gap for **both** remaining Bernstein axioms in
one slice (not just `bernstein_inequality` — the budget corollary makes
`bernstein_bounded_variance` a consumer too; only `hoeffding_lemma`, whose
natural consumer is `bernstein_inequality`'s own proof, remains
zero-consumer).

**Engine** (two new lemmas, zero new axioms):
`BernoulliProduct.lean`'s `integral_sq_delta_sub` — the second-moment
companion of `integral_delta`, `∫ (δ_e − p e)² ∂μ = p e (1 − p e)`,
through the pointwise expansion `(δ − p)² = δ • (1 − 2p) + p²` (δ² = δ)
and the `f • c` spelling of `integral_smul_const` (the pin's shape —
the constant sits on the *right* of the smul; pulling a leading
constant out is `integral_const_smul`, a different lemma, and the
first spike iteration had them swapped); and
`EdgePerturbation.lean`'s `integral_sq_degPerturbSummand` —
`∫ X_e² ∂μ = w_v(e)² p e (1 − p e)` at the design.

**Derived** (`EdgePerturbationTail.lean`'s bernsteinTwin section):
`edgePerturbation_degree_tail_bernstein` —
`μ {|deg dev| ≥ t} ≤ 2 exp(−t²/(2 σ²_v + 2Mt/3))` at the true variance
statistic `σ²_v = ∑ₑ w_v(e)² p e (1 − p e)` and a magnitude budget
`M ≥ |w_v(e)|` (the axiom's uniform-bound clause; `0 ≤ M` derived from
`hM` at the incident pair `(v, v)`, so no spurious hypothesis) — and
`edgePerturbation_degree_tail_bernstein_budget` at any supplied budget
`σ²_v ≤ Vbud`. Two assembly differences from the Hoeffding twin,
both forced by the axioms' own shapes: the centering sits *inside*
`bernstein_inequality`'s event and variance statistic (not a separate
hypothesis), so both rewrites run through per-summand congruence
(`Finset.sum_congr` + `hmean i` + `sub_zero` — a whole-function
equation `rw` cannot reach under the sum's binder), and the magnitude
bound is a single scalar, hence the `hM` hypothesis shape.

**QA +10 (2977 → 2987**, the bernsteinTwin section): the true statistic
pinned exactly (`σ²₀ = ½` on K₂ at the fair coin) with the
Poisson-trial degeneration (`∑ w² p = 1`) **refuted** — a future edit
dropping the `(1 − p)` factor from the design's variance lemma breaks
exactly this; the fourfold variance reduction as an *equation*
(`σ²₀ = S₀/4` — sharp at the fair coin, joined to the delivered
Hoeffding statistic); the engine integral pinned at an incident pair
(`¼`); `M = 1` at the fixture; the **strict variance-adaptivity
improvement proved** (`epK2_bernstein_beats_hoeffding`:
`2 exp(−3/5) < 2 exp(−1/4)` by strict exp monotonicity at
`1/4 < 3/5`) — the cross-axiom coherence check, hard crust; the budget
relaxation pinned honest (`epK2_bernstein_exact_le_budget`, `≤`); and
the two closed-form conditional instances (`2 exp(−3/5)` exact,
`2 exp(−3/8)` at `Vbud = 1`).

**Degenerate-corner analysis** (recorded pre-statement, per the
2026-08-28 hazard discipline): the prefactor is again the constant `2`
(no dimension collapse — no `Nonempty` guard); `t = 0` is safe through
`zero_div` (`0/d = 0`, exponent `0`, bound `2 ≥ μ(·)`); empty `V` is
vacuous in `v`; the derived `0 ≤ M` and `0 ≤ Vbud` discharge the axioms'
nonnegativity clauses without new hypotheses.

**Verification:** spike first (`wip/berntwin_spike.lean`, every piece —
both engine lemmas, both tails, the full QA section, and the axiom
audit — iterated to zero errors/warnings before any shelf edit);
`lake env lean` zero errors on all four touched modules (the QA module
at its recorded three-note `Try this: ring_nf` baseline — this
delivery's `norm_num` calls add *none*, verified by elaborating the
stashed pre-delivery tree); explicit `lake build` targets ✔ on
`BernoulliProduct`, `EdgePerturbation`, `EdgePerturbationTail`,
`EdgePerturbation_QA`; `#print axioms` via `wip/berntwin_axcheck.lean`
on 14 declarations exactly as designed; full `lake build` ✔ (2403/2406)
followed by `check_build_completeness.py` — after the documented mtime
remediation (a stash-cycle for the baseline comparison touched five
source mtimes; remove artifact + rebuild once), 128 sources, 128 fresh
artifacts, 0 stale, 0 missing, exit 0; `lint_axioms` (10, both findings
allowlisted-confirmed), `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**2987/10/0**); map freshness exit 0 after the
stats-stamp sync (2977 → 2987 in both map files; no proposal status
header changed — the governing header's COMPLETE verdict is unchanged).

**Technique findings:**
- The pin's `integral_smul_const` is the `f • c` shape (constant on the
  right: `∫ x, f x • c ∂μ = (∫ x, f x ∂μ) • c`, no integrability
  hypothesis); the leading-constant pullout is a *different* lemma.
  Centering-shaped integrands want the `f • c` spelling with the
  Bernoulli factor as `f`.
- `Integrable.of_finite` (the `[Finite α] [IsFiniteMeasure μ]` simp
  lemma, no explicit argument) discharges integrability on the
  product-Bernoulli space for any real-valued factor through a
  coordinate — the BernoulliProduct file's own idiom, reused.
- A `rw` with `Finset.sum_sub_distrib` backwards fails on
  `∑ (f i − g i)` goals; the per-summand route
  (`Finset.sum_congr rfl fun i _ => by rw [hmean i, sub_zero]`) is the
  robust shape — and doubles as the event-side centering rewrite.
- `by_cases h2 : e.1 = e.2 <;> by_cases h1 : 0 = e.1 ∨ 0 = e.2 <;>
  simp [h1, h2]` closes the `Fin 2` magnitude-bound fixture without a
  trailing `norm_num` (which the linter flags as unreachable).

The admissibility dissolution remains the sole priced follow-on, now
with both tails (Hoeffding and Bernstein) available as the degree half's
engine — the Bernstein one is strictly sharper at interior `p`, so the
dissolution's window arithmetic can pick either.

## Admissibility-dissolution follow-on — DELIVERED 2026-08-29 (run `20260829T142812Z-run-1`)

The sole priced follow-on above was delivered by the next run: the
window family's first measured event with **no admissibility conjunct**
— `perturbAdmissible` is no longer hypothesized but *derived*, on both
halves at once.

**The engine** (`EdgePerturbation.lean`'s WeightSpace section, public
hard crust): `perturbWeight_entry_nonneg` — at the pair design
condition `p e + p (e.2, e.1) ≤ 1` every resampled entry is nonnegative
at *every* outcome. Off the diagonal the resampled entry is
`A i j · (1 + δ_{ij} + δ_{ji} − p_{ij} − p_{ji})` (symmetry identifies
the two ordered contributions; `δ ∈ {0,1}` and the pair sum at most
`1`); on the diagonal `A i i · (1 + δ_{ii} − p_{ii})` with `p_{ii} ≤
1`. The proof is `mul_nonneg` after a `ring` factorization on each
branch — no `hp0` hypothesis needed (`0 ≤ p` is never used: the factor
bounds come from `hpd`/`hp1` alone).

**The transfer and the theorem** (`EdgePerturbationTail.lean`'s new
AdmissibilityDissolution section):
`perturbAdmissible_of_degDev_lt` — base degrees in the shrunk window
`[dmin + s, dmax − s]` plus per-vertex deviations strictly below `s`
put the outcome inside `[dmin, dmax]` (no `0 ≤ s` hypothesis: the
strictness carries `s`'s sign implicitly through `abs_lt`) — and
`edgePerturbation_normalized_connectivity_bracket_unconditional`: at
exactly the bracket's hypothesis stack (with the base window replaced
by the shrunk one) plus the pair condition, **leaving the two-sided
normalized-connectivity window** — an *unconditioned* event — is
bounded by `2 d exp(−t²/(2‖∑ₑ L_e²‖)) + ∑_v 2 exp(−s²/(2 S_v))`. The
proof is the decomposition "some deviation ≥ s, or all < s and then
admissible" (`measure_mono` into a union, `measure_union_le`,
`add_le_add` of the delivered bracket and the delivered all-vertices
degree tail). **The family's first two-axiom member**: conditional on
`matrix_hoeffding` (via the bracket) *and* `hoeffding_inequality` (via
the degree tail), each via its own sub-theorem, `#print axioms`-verified
— recorded as deliberate, not drift.

**QA +16 (2987 → 3003**, the AdmissibilityDissolution section): the
pair condition pinned at both uniform designs; the boundary entry pin
(the `p ≡ ½` all-false off-diagonal entry exactly `0` — the engine's
inequality *tight* at the boundary); the **dropped-pair-condition
fence** (`p ≡ 9/10`: the entry exactly `−4/5`, nonnegativity genuinely
failing at a design legal in every other respect — the design condition
load-bearing); the transfer's positive witness (`p ≡ 1/10`: deviations
`|−1/5| < 1/2`, base degrees `1` in the shrunk window `[1, 2]`, the
derived degree `4/5` pinned by the design's own identity
`deg_resampled`); the strictness-boundary coherence (`p ≡ ½`
all-false: deviation `1 ≥ s = 1/2` — in the degree event exactly where
the transfer does not apply — and provably *not* admissible, so the
helper's strict `< s` is honest, not an artifact); the ∀-vertex degree
statistic `S_v = 2`; and the closed-form instance
`μ{exit} ≤ 4 exp(−1/4096) + 4 exp(−1/16)` on `K₂` at window
`[1/2, 5/2]`, `s = 1/2`, `t = 1/16` — conditional on both axioms,
honestly labeled.

**Degenerate-corner analysis** (recorded pre-statement, per the
2026-08-28 hazard discipline): the `s = 0` degeneration is harmless —
the deviation event `{∃ v, 0 ≤ |dev v|}` becomes all of `Ω` and the
bound vacuously true (the hypothesis stays `0 ≤ s` for interface
generality, not tightened to `0 < s`); `card V = 0` is fenced by the
inherited `hcard : 2 ≤ card V`; `t = 0` safe as recorded for both
parents; the diagonal corner of the pair condition (`p (i,i) +
p (i,i) ≤ 1`) is stronger than the diagonal entry needs (`p (i,i) ≤
1`) but satisfiable at every uniform design.

**Technique findings:**
- `norm_num` cannot normalize *inside* a `Real.exp` atom: exponent
  arithmetic (`−(1/2)²/(2·2) = −1/16`) must be proved as a standalone
  equation and `rw`-en (or `congrArg`-composed) before any
  ring-closing step treats the exponentials as atoms.
- `ENNReal.ofReal_add` carries `0 ≤ a`, `0 ≤ b` side hypotheses; using
  it backwards through `rw ←` leaves them as stray goals. The robust
  route is `Eq.trans (ENNReal.ofReal_add hA hA).symm (congrArg
  ENNReal.ofReal (by ring))` with `hA := by positivity`.
- A tactic-block argument *before* postponed `(by norm_num)` slots can
  silently slide into an instance-argument position (an extra
  `(by norm_num)` was consumed as the `[Nonempty V]` slot and reported
  as an `⊢ NNReal` mystery) — count named-hypothesis slots explicitly
  when instantiating long hypothesis stacks.
- The helper's `0 ≤ s` was dead on arrival: `|x| < s` already forces
  `0 < s` via `abs_lt`, so `linarith` never consulted it — hypotheses
  implied by other hypotheses' *shapes* should be dropped at statement
  time, not left decorative.

**Honesty note (residual):** the dissolution converts the admissibility
*conjunct* into a tail bound — the statement is now unconditional in
its measured event, but at the price of the extra degree term, and the
window family's *floor* and *sweep-cut* theorems still carry their own
admissibility conjuncts (dissolvable by the same decomposition, priced
not owed). The pair condition `p e + p eᵀ ≤ 1` is a genuine design
restriction — at uniform designs it means `p ≤ ½`, and the fence above
shows what breaks without it. No fixture-scale refutation of the
*dropped pair condition at theorem level* is claimed (on the `K₂`-class
fixtures the shrunk-window hypotheses cannot hold at any `s > 0`
without slack in the base window — the standing junk-window
obstruction); the piece-level fence carries the falsification content.

**Status: the priced follow-on delivered — the window family's honesty
note on its degree half is dissolved; the note's fixture-refuted half
(no dropped-window refutation fixture at fixture scale) stands as
recorded.**

---

## Delivery record 4 — the dissolution completion (floor and swept cut),
run `20260829T155521Z-run-1` (2026-08-29)

The dissolution's own honesty note priced this follow-on: "the window
family's *floor* and *sweep-cut* theorems still carry their own
admissibility conjuncts (dissolvable by the same decomposition, priced
not owed)." This delivery pays it — the decomposition applied verbatim
to both remaining members, completing the family.

**The theorems** (`Derived/EdgePerturbationTail.lean`'s
AdmissibilityDissolution section):

- `edgePerturbation_normalized_cheeger_floor_unconditional` — at the
  shrunk-window/pair-condition stack, the *unconditioned* floor event
  `μ {λ₂(L_sym G_ω) ≤ (dmin·φ²/2 − t)/dmax}` is bounded by the window
  tail at `t` plus the degree tail at `s`.
- `edgePerturbation_fiedler_sweep_cut_tail_unconditional` — the
  algorithm-facing capstone made unconditional: the failure of
  "connected with a swept level set of the resampled graph's own Fiedler
  sweep vector at `conductance² ≤ 2·(2·dmax·φ + t)/dmin`" is bounded
  the same way, at the same stack plus the floor-positivity guard.

Both are literally the bracket member's proof skeleton (the
`hsplit`/`measure_union_le`/`add_le_add` decomposition) at the two
conditional theorems — the entire new content is the set-comprehension
shapes; the decomposition itself was already load-borne by the bracket.
`#print axioms` (`wip/dissolve2_axcheck.lean`): both honestly carry
`matrix_hoeffding` AND `hoeffding_inequality` together, each via its
own sub-theorem — the family's two-axiom shape, now three members.

**QA (+5, 3003 → 3008, the AdmissibilityDissolution completion
subsection):**

- `epK2_allFalse_supportGraph_not_connected` — the all-false resampled
  graph (zero adjacency) is disconnected, by the contrapositive of
  `exists_const_of_laplacian_mulVec_eq_zero` at the indicator
  `![1, 0]`: the zero Laplacian kills every vector, so connectivity
  would force the non-constant indicator constant. Hard crust.
- `epK2_sweepUnconditional_strictly_larger_witness_QA` — **the
  strict-containment witness, the delivery's falsifiability content**:
  the all-false outcome is provably *in* the unconditional sweep bad
  event (via the disconnectedness above) while provably *not*
  admissible (`epK2_half_allFalse_not_admissible`, the previous
  delivery's own pin). Together: the dissolution genuinely enlarged the
  measured event — the degree-tail term is the honest price of exactly
  these outcomes, and a "dissolution" that quietly shrank the event
  (e.g. by keeping the conjunct inside the set) would break this
  witness. Hard crust: a negation and a non-membership, no axiom
  contact.
- `epK2_sweepUnconditional_allTrue_good_QA` — the good-outcome
  conjunction at the dissolution's window: the all-true resampled graph
  (the weight-`2` edge) is connected with a swept cut at
  `conductance² ≤ 2·λ₂ = 4`, well inside the ceiling
  `2·((2·(5/2·φ) + 1/16)/(1/2)) = 81/4` — the unconditional bad event
  is not all of `Ω`. Hard crust.
- The two closed-form instances
  (`epK2_floor_unconditional_closedForm_QA`,
  `epK2_sweepUnconditional_closedForm_QA`): `4 exp(−1/4096) +
  4 exp(−1/16)` each on `K₂` at `p ≡ 1/10`, window `[1/2, 5/2]`,
  `s = 1/2`, `t = 1/16` — a wrong constant anywhere in either chain
  (window prefactor, variance norm `8`, degree statistic `2`, the
  exponent arithmetic) breaks exactly these. The sweep instance's floor
  hypothesis genuinely holds (`0 < 1/2·φ²/2 − 1/16 = 3/16`). Both
  honestly carry the two axioms via instantiation.

**Degenerate-corner analysis** (recorded pre-statement): both theorems
inherit their parents' guards (`hcard : 2 ≤ card V` fences the empty
index type; the `Nonempty` instance comes with the conditional
theorems' own stacks), and the decomposition's `s = 0` degeneration is
harmless exactly as in the bracket member (the deviation event becomes
all of `Ω`, the bound vacuously true). The sweep member's
floor-positivity guard is untouched by the dissolution — it feeds the
*connectivity transfer*, not the admissibility window — and its C₄
dropped-guard refutation fixture (`epC4_sweepWindow_unguarded_refuted_QA`)
carries over verbatim, since the guard is a hypothesis of both members.

**Honesty note:** with this delivery the window family's measured
events are all unconditional, but the two new theorems are two-axiom
members (`matrix_hoeffding` + `hoeffding_inequality`) and must never be
described as foundationally proved. The pair condition remains a
genuine design restriction (the previous record's `p ≡ 9/10` fence),
and the shrunk-window hypotheses remain what they were — a real
regularity price on the base graph, not a vacuity.

**Status: the family completed — floor, bracket, and swept cut all
unconditional. The proposal's follow-on list is empty; no new priced
follow-ons recorded (the family's next natural frontier is a consumer
of the unconditional statements, which does not exist yet).**
