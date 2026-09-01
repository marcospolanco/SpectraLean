# Proposal: Continuous-Time χ² Mixing — the π-Weighted `L_sym` Heat-Variance Twin

**Status:** COMPLETE — proposed and delivered in the same run
(`20260831T194244Z-run-1`), per the same-run pattern of
`heat-variance-decay.md`. This is the heat-variance delivery's own
named deferred follow-on (its Remaining-risk record: "the π-weighted
`L_sym` twin (consumer-gated)") with the consumer gate discharged by
naming the consumer below. Zero new axioms: every statement is proved
from shelf engines; `#print axioms` on all 46 audited declarations
(28 shelf + 18 QA) reads exactly `propext, Classical.choice,
Quot.sound` (the spike's audit block, `wip/ctmix_spike.lean`).

Companion to [Strategy](../docs/1_STRATEGY.md), to the mixing-time
program (`mixing-time-bound.md`, whose module hosts the consumer), and
to the heat-semigroup program (`reversibility-and-heat-semigroup.md` +
`heat-variance-decay.md`, whose module hosts the semigroup layer).

---

## Clean-room boundary

This planning document is internal prioritization and analysis. If
counsel approves a public repository export, restate the technical
specifications independently from standard textbook sources
(continuous-time Markov-chain mixing is classical; see Sources). Do
not copy this proposal verbatim.

## The obligation this discharges

The heat-variance delivery (2026-08-31) proved the *uniform-measure*
variance decay `∑((e^{-tL}f) i − mean f)² ≤ e^{−2tλ₂(L)}∑(f i − mean f)²`
and recorded as its first deferred follow-on "the π-weighted `L_sym`
twin (consumer-gated on a named walk/heat statement needing it)".

### The consumer gate, discharged by naming (Step 0, settled before any Lean)

The named walk/heat statement needing the twin is the **continuous-time
χ² mixing bound** — the `t ∈ ℝ₊` statement of every textbook mixing
chapter (Levin–Peres–Wilmer ch. 20; Montenegro–Tetali, "General
Bounds via the Spectral Gap"): for the random walk run in continuous
time, the χ² distance from stationarity decays at exactly the spectral
gap,

```
χ²_cont(t, x) ≤ e^{−2t·λ₂(L_sym)} · ((π x)⁻¹ − 1)
```

at exactly `chiSquareDistance_le_of_connected`'s hypothesis set
(symmetric, nonnegative, positive degrees, connected) — and with **no
caller-certified rate at all**, where the delivered discrete-time
theorem needs an `r` dominating every walk factor `|1 − μ|`: the
continuous-time rate `e^{−λ₂ t}` is intrinsic. This is the same
gate-discharge pattern as the empirical-stationary Step-2 delivery
(name the field-standard consumer the shape serves) and the TV
conversion (name `t_mix`-style TV mixing as Step 4's consumer).

### Why the twin is *not* a corollary of the delivered combinatorial theorem

Recorded so it is not re-attempted: the π-weighted variance of
`e^{−tL_sym}`-evolved vectors is **not** reachable by the Euclidean
eigenbasis Parseval. The π-inner product is the Euclidean one after the
`√D`-conjugation of vectors (`∑ π g² = ‖√D g‖²/vol`), but
`√D e^{−tL_sym} ≠ e^{−tL_sym} √D` — the matrix does not commute with
its own conjugator. What the `√D`-conjugation *does* transfer is the
walk semigroup: `√D e^{−tL_walk} = e^{−tL_sym} √D` (the continuous
analogue of the shelf's similarity `√D L_walk D^{−1/2} = L_sym`). So
the π-variance decay of the **walk** semigroup `e^{−tL_walk}` — the
density evolution of the continuous-time walk, the honest Markov
object — is exactly the Euclidean contraction of `e^{−tL_sym}`, and
that *is* Parseval-exact. The delivery is therefore stated at the walk
generator, with the conjugation as the load-bearing new engine.

## Statement design (settled before any Lean)

The semigroup layer (`GraphTheory.Heat`, new section):

- `normalizedHeatKernel A t := NormedSpace.exp ℝ (-(t • normalizedLaplacian A))`
  with `normalizedHeatKernel_isSymm`, `normalizedHeatKernel_zero`, and
  the mode-decay/coordinate-damping/Parseval-exact clones at `L_sym`
  (the combinatorial section's proofs re-instantiated at the symmetric
  normalized Laplacian — `eigvalOf_mem_evals` and
  `dotProduct_eigvecOf` are already generic; the eigenvalue comparison
  and zero-mode lemma need `L_sym` twins through
  `normalizedLaplacian_evals_zero`,
  `normalizedLaplacian_mulVec_degreeSqrt_onesVec`,
  `normalizedLaplacian_psd`, and `secondEval_le_rayleigh_of_ker` at
  the kernel vector `√D *ᵥ onesVec`).
- `walkHeatKernel A t := NormedSpace.exp ℝ (-(t • walkLaplacian A))` —
  the walk semigroup `e^{−tL_walk}`, non-symmetric at irregular
  degrees.
- **The conjugation lemma**
  `degreeSqrt_mulVec_walkHeatKernel : √D *ᵥ (walkHeatKernel A t *ᵥ f) =
  normalizedHeatKernel A t *ᵥ (√D *ᵥ f)` — the exact continuous-time
  analogue of the shelf's conjugated-power transfer
  `degreeSqrt_mulVec_pow_walkTransitionMatrix`, proved by the
  `expSeries_hasSum_exp` + `HasSum.map` route (per-power conjugation
  `√D Mⁿ = Nⁿ √D` from the commutation `√D L_walk = L_sym √D`, then
  uniqueness of sums through the continuous additive action).
- **The headline twin** `walkHeatKernel_variance_decay`: for symmetric
  nonnegative `A` with positive degrees, `2 ≤ card V`, `t ≥ 0`:

  ```
  ∑ i, deg A i * ((e^{−tL_walk} f) i − (∑ j, deg A j * f j)/(∑ j, deg A j))²
    ≤ e^{−2t·λ₂(L_sym)} * ∑ i, deg A i * (f i − (∑ j, deg A j * f j)/(∑ j, deg A j))²
  ```

  the π-weighted variance decay (π = deg/vol; the statement is
  vol-free), hypothesis-minimal in the delivered theorem's sense — no
  connectivity, no gap positivity (at `λ₂(L_sym) = 0` the true rate-1
  statement), two branches over one Parseval identity.

The consumer layer (`GraphTheory.Mixing`, new `ContinuousTime`
section): `contWalkDensity A t x := walkHeatKernel A t *ᵥ walkDensity A 0 x`
(the continuous-time walk's π-density started at `x`),
`contChiSquareDistance A t x := ∑ i, π i (contWalkDensity A t x i − 1)²`,
the `t = 0` join to the discrete object, and the consumer theorem
`contChiSquareDistance_le_of_connected` at exactly the discrete
theorem's hypothesis set plus `2 ≤ card V`.

## Degenerate-corner analysis (the §5 floor, applied to statement design)

Not an axiom — pure theorem — but the same hazard classes checked
before stating:

- **`t = 0`**: both sides equal (`e^{−0} = 1`, kernel identity); QA
  pins the corner.
- **`t < 0`**: excluded by `0 ≤ t` (the backward semigroup grows).
- **`card V < 2`**: excluded by `hcard` (`secondEval`'s domain), as in
  the delivered combinatorial twin.
- **Zero degrees**: excluded by `hd` — the `√D` conjugation is an
  isometry exactly there (`degreeSqrt_mul_degreeInvSqrt`).
- **`λ₂(L_sym) = 0`** (disconnected): the nonpositive-gap branch gives
  the rate-1 statement; QA pins the disconnected fixture's exact closed
  form `1 + 3e^{−3t}` (triangle⊕self-loop) — decay at the
  within-component rate that the theorem honestly does not claim,
  limit `1` not `0` (the walk never crosses components).
- **Wrong-constant corners**: fenced in QA on both a connected fixture
  (K₃: pretending the gap is `2` reads `2e^{−3} ≤ 2e^{−4}`) and the
  disconnected one (pretending `λ₂ = 1` on the gap-zero fixture).

## Delivery record (2026-08-31)

- **The consumer is stronger than planned**: the delivered
  `contChiSquareDistance_le` needs *no connectivity hypothesis* (the
  twin is hypothesis-minimal; on disconnected input `λ₂(L_sym) = 0`
  and the rate-1 statement is true) — strictly stronger than the
  discrete theorem's shape, which needs connectivity for its
  caller-certified rate.
- **A fixture correction during QA**: the disconnected fixture's
  `3/2`-eigenvector is `(8, −4, −4, 0)/3` (a `triG` multiple), not the
  `(2, −2, −2, 0)` first sketched — the exact closed form is
  `χ²_cont(t, 0) = 1/3 + (8/3)·e^{−3t}` with limit `1/3`.
- **One deferral, delivered the same day**: the path (irregular-fixture)
  exact-decay QA (`χ²_cont(t, center) = e^{−4t}` at the top eigenvector
  `(−1, √2, −1)`) was deferred with its `λ₂(L_sym P₃) = 1` pin and
  delivered a few hours later as run `20260831T221623Z-run-1` (the
  follow-on record below).

### Follow-on delivery record (2026-08-31, run `20260831T221623Z-run-1`): the path-fixture QA — DELIVERED

The deferred item, at zero axiom cost (count stays 5; all 13 new
declarations at exactly the standard three, `wip/ctpath_spike.lean`),
`Mixing_QA.lean`'s path continuous-time section (QA 3420 → 3433):

- **The `λ₂(L_sym P₃) = 1` pin, trace route** (`path_secondEval_QA`):
  the three witnesses — `0` at the kernel `√D·1`
  (`normalizedLaplacian_mulVec_degreeSqrt_onesVec`), `1` at
  `(1, 0, −1)` (`path_lapsym_mulVec_w1_QA`), `2` at
  `(−1, √2, −1)` (`path_lapsym_mulVec_top_QA`, raw entrywise) — each
  pulled into the sorted spectrum through
  `exists_eigvalOf_eq_of_mulVec_eq_smul` + `eigvalOf_mem_evals`; the
  file's own SOS certificates (`path_eigvalOf_nonneg`/
  `path_eigvalOf_le_two`) bound every entry into `[0, 2]`; sortedness
  forces `evals 0 = 0` (the `0` member, `Fin.zero_le`) and
  `evals 2 = 2` (the `2` member), and the trace `3`
  (`path_trace`, diagonal `1 − 0` per vertex) closes `evals 1 = 1`.
- **The non-scalar conjugation pin** (`path_conj_centered_QA`):
  `√D(−1, 1, −1) = (−1, √2, −1)` — the centered center-start density
  conjugates to the top eigenvector. P₃ is the only fixture class in
  the whole continuous-time QA set where `√D` is non-scalar *and* the
  gap is positive (K₃ is regular, the disconnected fixture's triangle
  block is regular within itself), so this is the pin that exercises
  the delivery's centerpiece `degreeSqrt_mulVec_contWalkDensity_sub_one`
  at a genuinely irregular connected input.
- **The exact single-mode decay** (`path_cont_chi2_exact_QA`):
  `χ²_cont(t, center) = e^{−4t}` exactly, at every `t` — the
  conjugation shift, the eigenmode engine at `λ = 2`, `vol = 4`, and
  the raw norm pin `‖(−1, √2, −1)‖² = 4`.
- **The strict-slack witness** (`path_cont_slack_QA`):
  `e^{−4t} < e^{−2t}` for every `t > 0` — the center start is a pure
  top mode, so it decays at exactly twice the certified rate; the
  triangle's exact-attainment pin's twin (there value equals bound,
  here the rates genuinely separate).
- **Corners and fence**: the `t = 0` corner (`= 1 = (π c)⁻¹ − 1` at
  `π c = 1/2`), mass preservation on the irregular fixture, and the
  wrong-constant fence (pretend gap `3` reads `e^{−4} ≤ e^{−6}` at
  `t = 1`, refuted — the gap constant load-bearing on the irregular
  fixture as well).
- **Verification**: spiked first (`wip/ctpath_spike.lean`, zero
  errors/zero warnings, the audit block above); direct `lake env lean`
  zero errors/zero warnings; explicit build target ✔; full `lake build`
  ✔ + `check_build_completeness.py` 133/133 fresh, exit 0;
  `lint_axioms` (5), `check_refutation_independence` (10-tag clean),
  `check_public_reachability` (63 modules), `check_citations`,
  `check_markdown_links`, scoreboard regenerated (3433/5/0),
  map-freshness exit 0 after the stats sync.

### Technique findings (the follow-on spike, `wip/ctpath_spike.lean`)

1. **Rewriting a numeral RHS backward explodes hidden copies**:
   `rw [← hsq]` (`hsq : √2 * √2 = 2`) on a goal mentioning `√2` rewrites
   the `2` *under the sqrt* too, producing `(√(√2*√2))⁻¹ * …` junk.
   Route the identity forward inside a `calc` step instead:
   `= (√2)⁻¹ * (√2 * √2) := by rw [hsq]`.
2. **`norm_num` normalizes atom inverses but not nonlinear atom
   identities**: `−1 − (√2)⁻¹ * √2 = −2` closes at `norm_num` alone
   (it proves `a⁻¹ * a = 1` for atoms), while
   `√2 + (√2)⁻¹ * 2 = √2 * 2` needs `field_simp; nlinarith [hsq]`
   (clear the inverse, then the residual is linear in the atom-square
   that `hsq` names).
3. **The cardinal-coercion dependent-motive trap**: with
   `k2 : Fin (Fintype.card (Fin 3))`, rewriting
   `Fintype.card (Fin 3) = 3` inside `k2.isLt` fails ("motive is not
   type correct") because the coercion
   `@Fin.val (Fintype.card (Fin 3)) k2` mentions the cardinal. Route
   through `lt_of_lt_of_le k2.isLt (by simp : Fintype.card (Fin 3) ≤ 3)`.
4. **`omega` cannot see through the Fin-literal coercion**:
   `(2 : Fin (Fintype.card (Fin 3))) : ℕ` is an opaque atom to it.
   Supply `((2 : Fin (Fintype.card (Fin 3))) : ℕ) = 2` as a separate
   `have` (closed by `simp [Fintype.card_fin]`) before `omega`.
5. **The witness→spectrum membership chain**:
   `exists_eigvalOf_eq_of_mulVec_eq_smul` (raw eigenvector → some
   `eigvalOf` equals it) composed with `eigvalOf_mem_evals`
   (`eigvalOf i` occurs in the sorted `evals`) as `hk.trans hi` is the
   one-line bridge from a raw entrywise eigen-equation to a sorted-
   spectrum member — the piece the trace-route pin needed that the
   triangle's own proof built inline.
6. **`norm_num` decides small exp inequalities directly**: it refuted
   `Real.exp (-(4:ℝ)) ≤ Real.exp (-(6:ℝ))` on its own (exp
   monotonicity is inside its normalization), so the wrong-constant
   fence closes at `norm_num at h1` with no manual `exp_lt_exp`
   witness — unlike the triangle fence, which needed one.
7. **`(0:ℝ) • v` is `zero_smul`, not `smul_zero`** (the latter's
   pattern is `a • 0`); converting `M *ᵥ v = 0` into the
   `= μ • v` shape the witness lemma wants is cleanest as
   `by simpa using hker`.

### Technique findings (for the next run's spike)

1. **Unannotated smul-scalar literals default to ℕ**: `(3/2) • v` in a
   statement elaborates as `((3 : ℕ) / 2)`-cast smul — every downstream
   `rw`/`exact` against it fails with silent instance mismatch.
   Always write `(3/2 : ℝ) • v` (this single issue caused most of the
   spike's iteration).
2. `funext j` + `fin_cases j` leaves `(fun i => i) ⟨j, ⋯⟩` beta-redexes
   that derail entrywise `simp`; the file's own idiom (intro a plain
   `∀ j`-witness, `fin_cases` there, `funext; exact h j` at the end)
   avoids it.
3. `Matrix.smul_mulVec_assoc` (smul-matrix) vs `Matrix.mulVec_smul`
   (matrix-smul); `Matrix.mulVec_sub` (vector subtraction) vs
   `Matrix.sub_mulVec` (matrix subtraction) — the pin's names are
   swapped relative to intuition.
4. The eigenmode engine's hypothesis is cleanest closed by a
   standalone `have hstep2 : -(t • ((c : ℝ) • v)) = (-(t * c)) • v`
   proved entrywise (`Pi.neg_apply`/`Pi.smul_apply`/`smul_eq_mul` +
   `ring`), then `exact`-landed — direct `rw [smul_smul, neg_smul]`
   chains in-goal are instance-sensitive.
5. `field_simp` on expressions with exp-atoms from different rewrite
   lineages leaves commutativity residue that `ring` cannot close
   (the atoms differ invisibly); introducing the atom via `set E := …`
   first makes the arithmetic linear and closable.
6. `Fin (Fintype.card (Fin n))`-indexed sums do not fold to the
   3-term form by defeq-`have`; route spectrum sums through
   `have h3 : ∑ i : Fin n, evals hM i = c := hsum` (the
   `DegreeSandwich_QA` idiom, which works because the binder function
   is syntactically `fun i => evals hM i`).
7. The stale-olen import-boundary recurrence: landing Mixing.lean's
   Heat-importing section needs `lake build Scaffold.Mathlib.GraphTheory.Heat`
   first, or `walkHeatKernel` shows as a metavariable.

## QA obligations

In `Mixing_QA.lean`'s new continuous-time section (reusing the file's
`triAdj`/`triG`/`discAdj` fixture family and its pinned spectrum
facts):

1. **K₃ exact attainment at every time**: `χ²_cont(t, x) = 2e^{−3t}`
   exactly — both nonzero `L_sym` modes sit at `3/2`, so the bound is
   attained at *every* `t` (the strongest QA shape a bound theorem can
   have), through the rank-one-idempotent collapse
   `exp_eq_one_add_of_mul_self_eq_smul` at `L_sym(K₃)² = (3/2)·L_sym(K₃)`.
2. **P₃ center-start exact single-mode decay**: `χ²_cont(t, center) =
   e^{−4t}` exactly (the initial centered conjugated density is the
   top eigenvector `(−1, √2, −1)` of `L_sym(P₃)`, pinned by a raw
   entrywise eigen-equation), beside the theorem's `e^{−2t}` bound —
   honest slack witnessed.
3. **The wrong-constant refutation** on K₃ (gap `2`: `2e^{−3} ≤ 2e^{−4}`
   refuted).
4. **The disconnected exact form + gap-zero pin**: `χ²_cont(t, x) =
   1 + 3e^{−3t}` on the triangle⊕self-loop fixture with
   `λ₂(L_sym) = 0` pinned (non-connectedness through the shelf's
   `secondEval_normalizedLaplacian_eq_zero_of_not_connected`, `≥ 0` by
   PSD), and the rate-1 bound instance.
5. **The positive-gap fence on the gap-zero fixture** (pretending
   `λ₂ = 1` at `t = 1`: refuted), proving the gap hypothesis
   load-bearing.
6. **The `t = 0` corner** (both sides `((π x)⁻¹ − 1)`).
7. **Mass preservation** at the fixture (the continuous density stays a
   density: `∑ π contWalkDensity = 1`).

## Sources

- Levin, Peres, Wilmer, *Markov Chains and Mixing Times*, ch. 20
  (continuous-time mixing, `e^{−t·gap}` decay of distances).
- Montenegro, Tetali, "General Bounds Via the Spectral Gap", §3
  (continuous-time vs discrete-time mixing comparison).
- Chung, *Spectral Graph Theory*, ch. 1 (the normalized Laplacian and
  its heat semigroup on irregular graphs).

The Lean statements are proved locally from shelf engines; the sources
are provenance for the *shapes* (the continuous-time rate being
intrinsic at the spectral gap).

## Deferred

- ~~A continuous-time `t_mix(ε)` packaging joins the discrete
  program's own deferred `t_mix` object (still consumer-gated there;
  the same gate governs this side).~~ **Delivered 2026-08-31** (run
  `20260831T234308Z-run-1`, the follow-on delivery record below) with
  the gate discharged by naming the object's own field-standard
  consumers — the spectral ceiling
  `t_mix(ε) ≤ max 0 (ln(√C/(2ε))/λ₂(L_sym))` (Montenegro–Tetali's
  standard continuous-time bound, unstatable without the object) and
  ε-antitonicity — plus the exact K₂ closed form every textbook
  computes on the two-state chain. The *discrete* `t_mix` object
  stays deferred with its gate unchanged; the continuous↔discrete
  comparability theorem is the named follow-on that would justify it.
- ~~The heat-kernel TV ceiling's continuous-time twin is a one-step
  composition of the delivered TV conversion with this delivery's
  consumer once a consumer names it (the discrete TV ceiling's own
  consumer set already exists; the continuous side currently does not
  name one).~~ **Delivered 2026-08-31** (same run) with its consumer
  named: the mixing-time ceiling `contMixingTimeFrom_le_of_connected`
  — the field-standard continuous-time mixing statement every textbook
  mixing chapter states in TV form (LPW ch. 20 defines `d(t)` as TV).
- Hypercontractivity / log-Sobolev remain where axis 3's record holds
  them (consumer-gated on an entropy inequality composing the Gibbs
  bound) — this delivery does not touch them.

## Follow-on delivery record — the continuous-time mixing time
(2026-08-31, run `20260831T234308Z-run-1`, session
`ses_fa5d0d64bffeFq3NKI2tkhkmZV`)

**Deferred items 1+2 discharged together as one package.** Zero new
axioms (count stays 5); `#print axioms` via `wip/ctmixtime_axcheck.lean`
on all 37 audited declarations (10 shelf + 27 QA): every one exactly
`propext, Classical.choice, Quot.sound` — pure hard crust. QA
3433 → 3459 (+26, `Mixing_QA.lean`'s `ContMixingTime` section).

### The consumer-gate discharge (recorded before the Lean)

The two deferred items were mutually gating: the TV twin waited on a
consumer, and the `t_mix` packaging was the natural consumer. Both
gates discharged by the repo's established name-the-consumer idiom:
the TV twin's consumer is the mixing-time ceiling
`contMixingTimeFrom_le_of_connected` (every textbook continuous-time
mixing statement is TV-based — LPW ch. 20 defines `d(t)` as TV, and
`t_mix` from it); the object's own consumers are the statements
unstatable without it — the spectral ceiling
`t_mix(ε) ≤ max 0 (ln(√((πx)⁻¹−1)/(2ε))/λ₂(L_sym))` and
ε-antitonicity — plus the exact K₂ closed form. The discrete `t_mix`
object's gate is **unchanged**; the continuous↔discrete comparability
theorem is recorded as the named follow-on that would justify it (it
needs care: the non-lazy discrete walk on a periodic chain never mixes
in TV, so any comparison is conditional on the discrete side's
`r < 1` certificate exactly as the delivered discrete ceiling is).

### The shelf (`Mixing.lean`'s ContinuousTime section, 10 declarations)

- `contWalkDistribution A t x := fun i => π i · h_t i` — the
  continuous walk **law** (the discrete programme's `walkDistribution`
  twin: there the law is primitive, here the semigroup evolves the
  density, so the law is the weighting), with the `t = 0` join
  `contWalkDistribution_zero` (`π·(δ_x/π) = δ_x` — the
  wrong-weight detector).
- `contChiSquareDistance_eq_sum_div` — the χ² bridge into the
  `(ν − π)²/π` form `tvDistance_le_half_sqrt` consumes
  (per-summand `π(h−1)² = (πh−π)²/π`).
- `contWalkDistribution_tvDistance_le` — **the continuous-time ℓ²→TV
  conversion**, unconditional (no connectivity, no rate, sign-free on
  the law).
- `contWalkDistribution_tvDistance_le_of_decay` — the decay form
  `TV ≤ (1/2)·e^{−t·λ₂(L_sym)}·√((πx)⁻¹−1)` at exactly
  `contChiSquareDistance_le`'s hypothesis set, through the
  `√(e^{−2tλ₂}·C) = e^{−tλ₂}·√C` split.
- `contMixingTimeFrom A x ε := sInf {t | 0 ≤ t ∧ ∀ s ≥ t, TV s ≤ ε}` —
  the per-start mixing time at exactly LPW ch. 20's `∀ s ≥ t` reading
  (the honest form for a distance not assumed monotone in time);
  per-start mirroring the repo's oversmoothing family, the uniform
  sup-over-starts object left consumer-gated; the junk corner
  (`sInf ∅ = 0` at an unreachable `ε`) documented in the docstring —
  no theorem instantiates there.
- `contMixingTimeFrom_bddBelow` / `_le_of_cert` — the certificate
  interface (`0 ≤ T` and `∀ s ≥ T, TV ≤ ε` give `t_mix ≤ T`; the
  discrete ceiling's `pow_mul_le_of_log_threshold` analogue).
- `contMixingTimeFrom_le_of_connected` — **the spectral ceiling**, the
  honest two-case shape: below `ε = √C/2` the witness
  `T = ln(√C/(2ε))/λ₂` (where `e^{−Tλ₂} = 2ε/√C` closes the bound at
  exactly `ε`); above it, `t = 0` already certifies. Load-bearing on
  `secondEval_normalizedLaplacian_pos_of_connected` and the decay
  form.
- `contMixingTimeFrom_anti` — ε-antitonicity under a witness
  hypothesis (which the connected ceiling always discharges), by
  `csInf_le_csInf` set inclusion.

### The QA (`Mixing_QA.lean`'s `ContMixingTime` section, +26)

On `K₂`: the row-form engine pins (`k2_conj_mulVec_apply`,
`k2_normalizedLaplacian_mulVec_apply`, `k2_lapsym_mulVec_k2G` —
`(1,−1)` a `2`-eigenvector), the trace-route **gap pin
`λ₂(L_sym K₂) = 2`** (kernel pin + `∑ evals = trace = 2`), the exact
law `ν_t = ((1 ± e^{−2t})/2)`, **the exact TV value
`TV = e^{−2t}/2` at every time** (`k2_cont_tv_eq`) with the ceiling
**attained at every time** (`k2_cont_ceiling_attained_QA` —
Cauchy–Schwarz equality, `|h − 1|` constant), **the exact mixing-time
closed form** `t_mix(ε) = ln(1/(2ε))/2` for `0 < ε < 1/2`
(`k2_contMixingTimeFrom_eq` — the `sInf` pinned in *both* directions:
the closed form is a witness time whose `TV` is exactly `ε`, and every
witness time `t` has `TV(t) ≤ ε` hence `t ≥` the closed form, through
`Real.log_le_log` + `Real.log_exp`), the ceiling **attained exactly**
at `ε = e^{−2}/2` (`k2_contMixingTimeFrom_ceiling_le`:
`max 0 (ln(e²)/2) = 1 = t_mix` by `k2_contMixingTimeFrom_exp_eq`),
the **wrong-gap refutation** (pretending the gap is `3` claims
`t_mix ≤ ln(1/(2ε))/3 = 2/3` at that threshold against the pinned
`t_mix = 1`), the **big-`ε` corner** `t_mix(3/4) = 0`, and the
antitone instance `t_mix(1/4) ≤ t_mix(1/8)` with the closed-form
consistency pin (`ln 2/2` and `ln 4/2`). On the triangle: the scalar
conjugator `√D = √2`, the pure-`3/2`-mode centered density
(`tri_contWalkDensity_sub_one` — the `√2`-cancellation through
`mul_left_cancel₀`), **the exact TV value `(2/3)e^{−3t/2}` at every
time** (`tri_cont_tv_eq`), the ceiling instance at the pinned gap with
the **Cauchy–Schwarz slack proved strict** (`2/3 < √2/2`, via
`(4/3)² ≤ 2` and `Real.le_sqrt_of_sq_le`), and the `t = 0` join
`contWalkDistribution(0) = walkDistribution(0) = (1,0,0)`.

### Degenerate corners (the §5 floor, applied to the new statements)

These are theorems, not axioms, but the corner sweep was still run:
- `t = 0`: the join theorem plus the triangle raw pin.
- `ε` at/beyond the maximal TV distance `√C/2`: the ceiling's `max 0`
  branch exercised by the big-`ε` corner (`t_mix(3/4) = 0` on `K₂`
  where `√C/2 = 1/2`); the exact-pin theorem honestly excludes
  `ε ≥ 1/2` (there `t_mix = 0`, not `ln(1/(2ε))/2 ≤ 0`).
- Unreachable `ε` (empty witness set): no theorem instantiates; the
  def's junk value documented.
- Nonpositive `λ₂` (disconnected): excluded by the ceiling's
  connectivity hypothesis; the decay-form TV twin and the conversion
  remain unconditional and true there (rate `e^0 = 1`).

### Technique findings (spike `wip/ctmixtime_spike.lean`, for the next run)

1. `Real.sqrt_mul` in the pinned Mathlib **carries a hypothesis**
   `0 ≤ x` for the *first* factor — a bare `rw [Real.sqrt_mul]`
   leaves a metavariable side goal `0 ≤ ?a` assigned to the whole
   first factor; pass the nonnegativity explicitly
   (`Real.sqrt_mul (mul_nonneg h h)`), and note
   `Real.sqrt_mul_self (h : 0 ≤ x) : √(x * x) = x` is the mul-form
   (the `^2`-form is `Real.sqrt_sq`).
2. `Real.log_le_log (hx : 0 < x) (h : x ≤ y)` — the positivity is on
   the *left* argument; `Real.log_div (hx : x ≠ 0) (hy : y ≠ 0)`;
   `Real.exp_lt_one_iff : exp x < 1 ↔ x < 0`.
3. `one_le_div`/`one_lt_div (hb : 0 < b) : 1 ≤ a/b ↔ b ≤ a` — the
   clean way to `1 ≤ x/y` (not `div_le_iff₀`, which is for `x/y ≤ c`).
4. Term-mode `by rw [...]; exact ...` inside a `rw [...]` bracket of
   an *outer* rewrite fails to parse (the `;` escapes the bracket) —
   hoist the sign/positivity facts into `have`s and pass them by name
   (`abs_of_neg hneg2`), never inline `by` blocks with sequenced
   tactics inside brackets.
5. Elaboration order trap: passing `div_pos (Real.exp_pos _) (by
   norm_num)` for an *implicit* `{ε}` of an applied theorem whose ε is
   not yet determined leaves `by norm_num` against `0 < ?m` — hoist
   `have hε : 0 < <literal> := ...` first and pass the name.
6. `Fin.sum_univ_two/three` will not fire on a sum indexed by
   `Fin (Fintype.card (Fin n))` until re-ascribed
   (`have h' : ∑ k : Fin 2, f k = c := h` — defeq ascription), the
   same literal-vs-card index-type opacity the earlier continuous-time
   QA hit.
7. `rw`-with-a-`≤`-proof (`rw [Real.log_nonneg h]`) fails —
   "equality or iff proof expected"; use the lemma as a term
   (`div_nonneg (Real.log_nonneg h) (by norm_num)`).
8. The stale-olen import-boundary recurrence: elaborating the QA file
   against the edited-but-unrebuilt shelf resolves the new names to
   junk ("function expected … term has type ?m") — rebuild the shelf
   target first.
