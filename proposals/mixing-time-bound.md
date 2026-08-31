# Proposal: A Spectral Mixing-Time Bound

**Status:** COMPLETE — delivered 2026-08-22 in five runs, all pure hard
crust, **zero new axioms** (count stays 10 throughout): Step 1 (the
eigenpair transfer, closing `Normalized.lean`'s named residual gap),
Step 2 (the ℓ²-mixing proxy in the new `GraphTheory.Mixing`), Step 3
component 1 (the geometric decay engine) and Step 3 component 2 (the χ²
assembly — `chiSquareDistance_le_of_connected`, the program's closing
statement `χ²(t, x) ≤ (λ*)^{2t} · ((π x)⁻¹ − 1)`), the last under the
sub-decomposition this proposal itself licenses for its hardest step.
Radar axis 5 re-scored 2.5 → 3.0 (Step 1) → 3.5 (component 2, the
mixing statement's own landing). Originally proposed 2026-08-18
(surface-area follow-up for the formal-methods/high-assurance
audience).

Companion to [Grow the Crust Through Electrical
Structure](electrical-structure-crust.md) — same "grow the crust" premise,
different target: backlog item 4's other named candidate shape, "walk
mixing through the transition spectrum." Independent of [Prove λ₂'s
Variational Characterization](prove-lambda2-variational.md): this proposal
needs only the *value* of the spectral gap via `evals`, not its variational
description, so it does not gate on that proposal landing.

Assessed from `Scaffold/Mathlib/GraphTheory/{RandomWalk,Normalized,
VariationalTransfer,Spectral}.lean`, `docs/6_SGT_BACKLOG.md` item 2's
"residual gap" note, `docs/7_SGT_RADAR.md` axis 5, `docs/8_MATHLIB_COVERAGE_MAP.md`
(random walks/Markov chains: absent upstream), and a fresh search of
`.lake/packages/mathlib/Mathlib/{Probability,MeasureTheory}` for
total-variation-distance or mixing-time machinery (none found).

## Recommendation

Prove that the random walk's distance to its stationary distribution
decays geometrically in the number of steps, at a rate governed by the
walk matrix's second-largest eigenvalue modulus — the concrete gap named
in `docs/7_SGT_RADAR.md` axis 5 ("Absent: mixing-time statements... the
walk-spectrum transfer is the named Mathlib gap") and backlog item 4.

## Why this axis

This is the specific surface-area gap identified for the formal-methods/
distributed-systems audience: it turns Scaffold's existing walk and
spectral machinery into an actual usable convergence-rate guarantee — "how
many rounds until my gossip protocol converges" — rather than more
foundational SGT with no application-layer consumer. It composes with real
proved assets already on the shelf: `walkTransitionMatrix`/
`transitionMatrix` row-stochasticity (`RandomWalk.lean`, 0 axioms), and,
critically, the already-proved similarity identity `√D · L_walk · (1/√D) =
L_sym` (`Normalized.lean:224`).

## Calibration

Two very different difficulty levels hide inside "mixing-time bound." Do
not treat them as one slice.

- **Step 1 (eigenvalue transfer) is likely cheap.** `L_walk` and `L_sym`
  are related by a genuine *similarity* transform (conjugation by the
  invertible diagonal `√D`), so they share the same eigenvalues with
  multiplicity — standard linear algebra. `Normalized.lean`'s own comment
  already names this as "the precisely named residual gap" from backlog
  item 2; it is not a new discovery, just unstarted work.
- **Step 2 (the actual decay bound) is not cheap.** Mathlib has zero
  Markov-chain or total-variation-distance infrastructure — verified
  against the coverage map and a fresh search this session (only unrelated
  `MeasureTheory/Decomposition/*` files matched "variation"). This is
  substantially original Scaffold work. Treat it as at least as hard as
  the electrical program's step 4 (potential solvability) was scoped to
  be — a multi-run project, not a single slice.

## Build order

### 1. Transfer eigenvalues to the walk matrix, via similarity

Prove a similarity-invariance fact — either generally (`A` and `S⁻¹AS`
share eigenvalues, for invertible `S`) or, more cheaply, directly for
Scaffold's specific diagonal case. Since `L_sym = √D · L_walk · (1/√D)`
and `L_sym` is symmetric with a known sorted spectrum `evals`, define the
walk matrix's eigenvalues through that identity: `∀ i`, the walk matrix's
eigenvalue at index `i` equals `1 - evals L_sym i`. **Survey Mathlib
first** for a general similar-matrices-share-eigenvalues lemma before
reproving it, per this repository's own "survey before proving" rule — but
judge transport on cost, not reflex: the specific diagonal case may be
cheaper to prove directly than to instantiate a general lemma, the same
way `electrical-structure-crust.md` step 2 found direct proof cheaper than
transport from Mathlib's unweighted kernel theorem.

### 2. Define an ℓ²-mixing proxy, not total variation, first

Full total variation distance needs `MeasureTheory.Measure` machinery
Scaffold has never touched. A cheaper, still-meaningful first target: the
ℓ²-distance `‖Pᵗ δₓ − π‖₂` between the walk distribution after `t` steps
and the stationary distribution `π`, expressed directly through Scaffold's
own `deg`/`vol`/eigenbasis machinery — no new measure-theoretic
definitions. This is the standard "spectral mixing lemma" shape most
textbooks prove before converting to TV via Cauchy–Schwarz. **Decide and
record** whether the ℓ² statement alone satisfies this proposal's goal, or
whether the ℓ² → TV conversion is scoped as a further step, before writing
the statement.

### 3. The geometric decay bound

Prove `‖Pᵗ δₓ − π‖₂ ≤ (λ*)ᵗ · (normalization)`, where `λ*` is the maximum
absolute value among the non-principal eigenvalues transferred in step 1.
This is the actual mixing-time statement: it composes the eigenvalue
transfer, the eigenbasis-projector algebra already proved in
`Spectral.lean` (`spectralProjector`, `eigvecOf_complete`), and an
induction on `t` for the matrix-power decay. Likely the hardest single
step in this program; may need its own sub-decomposition across runs, the
same way the electrical program split steps 4 and 5.

### 4. (Optional, higher cost) Convert to total variation

Only after step 3 lands, and only if a named consumer needs TV
specifically rather than ℓ². Requires a probability-measure wrapper
Scaffold has never used before — treat as its own proposal-scale decision,
not a default continuation of this one.

**Delivered 2026-08-31 as its own proposal**
([`total-variation-mixing-conversion.md`](total-variation-mixing-conversion.md)):
both gates discharged there — the consumer named (the field-standard
`t_mix(ε)` statement, instantiated as the TV twin of the oversmoothing
ceiling), and the measure-wrapper cost estimate dissolved by scoping
(vector TV on the vertex type, no `MeasureTheory`). Zero new axioms;
the conversion constant attained exactly on `K₂`.

## Deferred and removed

- **General (non-diagonally-similar) walk mixing** — out of scope. This
  proposal covers only walks whose transition matrix is diagonally similar
  to a symmetric matrix, which is true of every `WAdj`-based walk Scaffold
  currently defines.
- **Reversibility as its own theorem** — radar axis 5 lists it absent
  alongside mixing time; not addressed here. A natural companion proposal,
  not a prerequisite of this one.

## Operating instructions for an autonomous run

- One step per run; step 3 may need more than one, per the electrical
  program's own precedent for its hardest steps.
- **No new axioms.** If step 2's ℓ² decay bound turns out to need genuinely
  new real-analysis machinery not extractable from what is on the shelf,
  stop and record the precise obstruction in `docs/6_SGT_BACKLOG.md` rather
  than admitting anything.
- Survey Mathlib before proving each step; update
  `docs/8_MATHLIB_COVERAGE_MAP.md` if the survey finds something that map
  missed.
- QA: a positive witness (a small graph where the bound is checked
  numerically against a hand-computed mixing rate) and a negative witness
  showing the bound fails without the eigenvalue-transfer hypothesis.
- Do not re-score `docs/7_SGT_RADAR.md` axis 5 until a step's proof lands
  and its QA passes.

## Delivery record

### Step 3, component 2 — the χ² assembly (DELIVERED 2026-08-22, run
`20260822T115239Z-run-1`; the program COMPLETE)

The closing statement, delivered exactly per the numbered gluing list
the component-1 record left — with item 2 (the connectivity kernel
characterization) carrying the real mathematical content, as forecast.

**Statement-shape decisions, made before stating:**

1. **Connectivity enters as the shelf kernel theorem's exact
   hypotheses** — `(supportGraph A hA).Connected` plus entrywise
   nonnegativity (`hnonneg`). Honest: mixing to *global* stationarity
   genuinely needs it, and the QA negative witness below demonstrates
   the conclusion is *false* without it even when the rate hypothesis
   genuinely holds. The mixing module had never carried a
   nonnegativity hypothesis before; the final bound does.
2. **The rate stays hypothesis-shaped `r`** (component 1's decision —
   the `sup'` packaging of λ* remains a consumer's business).
3. **`t = 0` needs no special case** — the bound reads
   `χ²(0) ≤ 1 · χ²(0)`.

Delivered, all proved, zero new axioms — `#print axioms` on every new
public theorem reads only `propext, Classical.choice, Quot.sound`:

- In `GraphTheory/Normalized.lean` (three entry lemmas):
  `walkTransitionMatrix_mulVec_one` (the constant fix `P *ᵥ 1 = 1`,
  row-stochasticity in vector form — the stationary direction of the
  density dynamics), `degreeSqrt_mulVec_apply` /
  `degreeInvSqrt_mulVec_apply` (the entry forms of the conjugating
  actions, factoring what QA had been proving inline).
- In `GraphTheory/Mixing.lean` (the χ² assembly section):
  `walkDensity_sub_one` (**centered evolution**: `h_t − 1 =
  Pᵗ *ᵥ (h₀ − 1)`, one induction from `walkDensity_succ` plus the
  constant fix through `Matrix.mulVec_sub`);
  `sum_deg_mul_walkDensity_sub_one_eq_zero` (**mass conservation in
  the conjugated pairing**: `∑ k, deg k · (h₀ k − 1) = 0` — termwise
  `deg · h₀ = vol · ν₀`, both sums evaluating to `vol`);
  `eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero`
  (**the connectivity mode derivation**: eigen equation at `μ = 0` →
  kernel transfer through the congruence `√D L_sym √D = L` (the inner
  `√D (1/√D)` cancels) → `exists_const_of_laplacian_mulVec_eq_zero`
  pins the pre-conjugated vector constant → `v k = √(deg k) · c`
  entrywise → the dot product collapses to
  `c · ∑ deg (h₀ − 1) = 0`. Load-bearing on the kernel
  characterization, the congruence, and mass conservation — an error
  in any surfaces here); and the headline
  `chiSquareDistance_le_of_connected`:
  **`χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)`** — density form → centered
  evolution → the delivered π-form contraction with the mode
  hypothesis supplied by connectivity → `chiSquareDistance_zero` for
  the normalization.

QA (`Mixing_QA.lean`, 67 → 117 declarations, all proved; `#print
axioms` on twelve headline QA theorems reads only the three standard
axioms):

- **K₃ — the bound attained *exactly*.** Connectivity by explicit
  walks; the one- and two-step laws and densities pinned raw
  (`ν₁ = (0, 1/2, 1/2)`, `ν₂ = (1/2, 1/4, 1/4)`;
  `χ²(1) = 1/2`, `χ²(2) = 1/8` recomputed termwise); the final theorem
  instantiated at `t = 1, 2` with the right side pinned to
  `(1/4)·2 = 1/2` and `(1/16)·2 = 1/8` — **equalities**, matching the
  engine's pinned π-norms `2 → 1/2 → 1/8` (the Parseval-exactness of
  the engine carries through the χ² identification unchanged).
- **The centered evolution cross-checked**: both sides of
  `h₁ − 1 = P *ᵥ (h₀ − 1)` pinned raw to `(−1, 1/2, 1/2)` (the
  pinned densities on the left, the pinned `tri_walk_pow_one` on the
  right).
- **The connectivity-derived mode fact *is* the hand-derived one**:
  the new theorem instantiated on K₃ and bridged to the component-1
  fixture-level `tri_mode_QA` through
  `walkDensity 0 0 − 1 = triG` — the general route reproduces the
  hand computation exactly.
- **P₃ — the λ* = 1 bound, rate derived basis-independently.** The
  rate hypothesis at `r = 1` needs every eigenvalue in `[0, 2]`,
  derived with no exact-spectrum computation and no control over
  Mathlib's basis: two sum-of-squares certificates for the quadratic
  form — the Dirichlet identity
  `v ⬝ L_sym v = (v₀ − v₁/√2)² + (v₂ − v₁/√2)²` and its companion
  `2‖v‖² − v ⬝ L_sym v = (v₀ + v₁/√2)² + (v₂ + v₁/√2)²` — evaluated
  at the unit eigenvector. The final theorem instantiated at `t = 1,
  2`; the numerics pinned: right side `1 · 3 = 3` against
  `χ²(1) = χ²(2) = 1` — no decay predicted, none observed, the bound
  honest and strict on the bipartite fixture.
- **Negative witness 1 — connectivity is load-bearing.** The
  triangle⊕self-loop fixture `discAdj` on `Fin 4` (all degrees `2`, so
  `π = (1/4, 1/4, 1/4, 1/4)`; support graph *disconnected* since a
  loop is not a support-graph edge). Its spectrum `{0, 0, 3/2, 3/2}`
  is derived basis-independently (row sums `2` give `μ(∑v) = 0`; the
  loop's `L_sym` row vanishes so `μ v₃ = 0`; the zero-sum unit-sphere
  quadratic form collapses the pair sum to `−1/2`, forcing
  `μ = 3/2`), so the **rate hypothesis provably holds at `r = 1/2`**
  — the loop's `μ = 0` mode is excluded from it *by design*, exactly
  the hole connectivity plugs. Yet the walk never leaves the triangle:
  `χ²(3) = 3/8` (raw, from the pinned three-step law
  `(1/4, 3/8, 3/8, 0)`) against the would-be bound `(1/2)^6 · 3 =
  3/64` — the conclusion **refuted** with every other hypothesis
  satisfied. No mixing to global stationarity is possible without
  connectivity; the value-based rate exclusion cannot detect the
  second `μ = 0` mode.
- **Negative witness 2 — the rate hypothesis is load-bearing.** At
  `r = 1/4` on K₃ the hypothesis is provably unsatisfiable (any
  `3/2` eigenvalue violates it and the trace forbids all-zero), and
  the conclusion fails with it: `χ²(1) = 1/2 > 1/8 = (1/16)·2`.

Verification: `lake env lean` on `Normalized.lean` (only its
documented pre-existing `congr 1` note), `Mixing.lean`, and
`Mixing_QA.lean` — zero errors, zero warnings on the latter two;
`#print axioms` on the seven new public and twelve headline QA
theorems ✔ (three standard axioms only); oleans built; **full
`lake build` ✔ (2228 targets, "Build completed successfully",
detached, zero errors)**; `lint_axioms` (10, unchanged),
`check_citations`, `check_markdown_links` pass; scoreboard
regenerated (**1212 QA declarations / 10 explicit axioms / 0
sorries**; `Mixing_QA` 67 → 117). Radar axis 5 **re-scored
3.0 → 3.5** per this proposal's own gate — the mixing *statement* is
the trigger, and its proof and QA have both landed.

Two pin-specific API discoveries recorded for future QA: this
snapshot's `Finset.mul_sum`/`Finset.sum_mul` take their arguments as
`(s) (f) (a)` with `mul_sum : a * ∑ f = ∑ (a * f)` (a different
argument order *and* orientation than the standard statement — the
`conv`-free workaround is explicit-argument `have`s); and the
matrix-literal far-corner entry (`!![…; 0,0,0,2] 3 2`-shaped)
normalizes through the notation's empty default row and defeats both
`rfl` inside `fin_cases` and `norm_num` — the robust route is an
`fin_cases + rfl`-proved entry table consumed as a simp lemma, or a
scalar-multiple route avoiding entrywise evaluation entirely.

### Step 3, component 1 — the geometric decay engine (DELIVERED
2026-08-22, run `20260822T095344Z-run-1`)

Executed as the sub-decomposition this proposal's own calibration
licenses for its hardest step ("may need its own sub-decomposition
across runs, the same way the electrical program split steps 4 and 5").
Component 1 is the mathematical core — the matrix-power/eigencomponent
layer in symmetrized coordinates; component 2 (the density-evolution
bridge, the connectivity kernel characterization, and the final χ²
statement) is deliberately left to a dedicated run.

**Statement-shape decisions, made before stating:**

1. **Value-based mode exclusion.** The non-decaying mode is excluded by
   `eigvalOf (L_sym) i = 0`, not by excluding spectral index 0. The
   index form is only correct when the kernel is one-dimensional (i.e.
   under connectivity); the value form keeps the contraction true
   unconditionally — on a disconnected graph the mode hypothesis
   honestly fails for a one-component start, which is exactly right:
   there is no decay to global stationarity, and the value-based
   hypothesis refuses to pretend otherwise.
2. **Hypothesis-shaped rate `r`** (`hrate : ∀ i, eigvalOf i ≠ 0 →
   |1 − eigvalOf i| ≤ r`) rather than a packaged `sup'` definition —
   QA instantiates with hand-computed rates; packaging the sup is
   component 2's business when the `walkEvals`-side instantiation is
   needed.
3. **No sign hypothesis on `r`.** The rate hypothesis already forces
   `r ≥ 0` whenever it is non-vacuous (`|1 − μ| ≥ 0`), and the vacuous
   case collapses term-wise; carrying `0 ≤ r` would be decorative.
4. **The public headline is the π-form contraction**
   `∑ π ((Pᵗ g) i)² ≤ r^{2t} ∑ π (g i)²`, with the Euclidean
   √D-conjugated engine beneath — per the Step-2 scoping record's
   weighted-form-is-primary decision.

Delivered, all proved, zero new axioms — `#print axioms` on every new
public theorem reads only `propext, Classical.choice, Quot.sound`:

- In `GraphTheory/Spectral.lean` (one generic center addition):
  `eigvecOf_dotProduct_one_sub_mulVec` — the eigenaction at `1 − M` for
  any symmetric `M`, composed from the shelf's
  `dotProduct_eigvecOf_mulVec` (self-adjointness in coordinates). The
  reflection-shaped operators consume this to evolve eigencoordinates
  stepwise.
- In `GraphTheory/Normalized.lean` (with the similarity): the
  commutation form `degreeSqrt_mul_walkTransitionMatrix_eq`
  (`√D · P = (1 − L_sym) · √D`, the one-line algebraic content of the
  similarity) and **the conjugated-power transfer**
  `degreeSqrt_mulVec_pow_walkTransitionMatrix` —
  `√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)` by induction, so the
  non-symmetric power is never diagonalized: it is moved across the
  similarity where the Step-1-certified eigenbasis of `L_sym` governs
  it. Load-bearing on `degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt`.
- In `GraphTheory/Mixing.lean` (the engine section):
  `eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix`
  (**eigencoordinate evolution**: the `i`-th eigencoefficient of the
  conjugated `t`-step evolution is the initial coefficient times
  `(1 − μ i)ᵗ` — a wrong similarity orientation or a wrong reflection
  would change the factor here);
  `dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix` (the
  **Parseval-exact decay identity**: the squared conjugated norm is the
  eigenvalue-weighted sum of squared initial eigencoordinates — no
  inequality lost);
  `dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix_le` (the
  **ℓ²(π) contraction, norm form** — kernel terms die by the mode
  hypothesis, decaying terms by the rate hypothesis, term-wise with no
  case split on `r < 1`);
  `sum_stationaryVec_smul_sq_eq` (the **π-norm bridge**
  `∑ π f² = vol⁻¹ · ‖√D f‖²` — degree nonnegativity only, no
  volume-positivity hypothesis since both sides carry the same factor);
  and the headline
  `sum_stationaryVec_smul_sq_pow_walkTransitionMatrix_le` (the
  **ℓ²(π) contraction** in mixing coordinates — the exact interface
  component 2 instantiates at `g = h₀ − 1` to obtain
  `χ²(t, x) ≤ (λ*)²ᵗ · ((π x)⁻¹ − 1)`).

QA (`Mixing_QA.lean`, 33 → 67 declarations, all proved):

- **The triangle K₃** (connected, non-bipartite — walk spectrum
  `{1, −1/2, −1/2}`, so λ* = 1/2 and the contraction has genuine
  content, unlike the path's λ* = 1). Every eigen-fact is derived
  *without naming Mathlib's classically chosen basis vectors* (the
  DavisKahan_QA technique): `tri_eigvalOf_cases` (every eigenvalue of
  `L_sym(K₃)` is `0` or `3/2` — summing the entrywise eigen equation
  over coordinates gives `μ · (∑ v) = 0` because the row sums collapse,
  and the quadratic form at the unit eigenvector pins
  `μ = 1 − (1/2)((∑ v)² − 1) = 3/2` when `∑ v = 0`);
  `tri_kernel_const` (a zero-eigenvalue eigenvector is constant —
  pairwise differences of the eigen equations force all coordinates
  equal); `tri_exists_kernel_index` (a zero eigenvalue must occur:
  `∑ eigvalOf = trace = 3` while three copies of `3/2` sum to `9/2`).
  The **mode hypothesis** is derived from these (the kernel direction
  is constant and `(1,1,1) ⬝ᵥ √D (2,−1,−1) = √2(2−1−1) = 0` — mass
  conservation meeting the engine, on the fixture); the **rate
  hypothesis** at `r = 1/2`. The contraction instantiated at `t = 1`
  and `t = 2` on the centered initial density `h₀ − 1 = (2,−1,−1)`,
  with both sides pinned raw: the π-norms `2 → 1/2 → 1/8` against the
  bounds `(1/4)·2` and `(1/16)·2` — **exact equalities**, the decay
  geometric at exactly rate `1/4` per step-pair.
- **The path P₃ retained** for the degenerate λ* = 1 oscillation
  cross-check: the engine's exact Parseval identity instantiated at
  `t = 2` on `h₀ − 1 = (3,−1,−1)` with the conjugated norm pinned raw
  to `4`, so the eigencomponent sum (a basis-independent quantity) is
  pinned to `4`; the π-norm bridge then ties the engine's two-step
  quantity to the already-pinned `χ²(2) = 1` (`1 = (1/vol)·4`, `vol = 4`)
  — no decay, exact oscillation, engine and χ² agreeing, exactly what a
  correct Step-3 statement must reproduce on a bipartite fixture.
- **The negative witness** (the mode hypothesis is load-bearing): at
  `g = 1` on K₃ the conclusion is refuted (`1 ≤ 1/4` false) *and* the
  hypothesis is provably unsatisfiable there — the kernel eigenvector
  (constant, `c ≠ 0` by unit norm) has coefficient `3·c·√2 ≠ 0` against
  `√D *ᵥ 1` — so the value-based exclusion is load-bearing, not
  decorative.

Verification: `lake env lean` on `Spectral.lean` (only its documented
pre-existing section-variable warnings), `Normalized.lean` (only the
documented pre-existing `congr 1` note), `Mixing.lean`, and
`Mixing_QA.lean` (zero errors, zero warnings each); `#print axioms` on
all eight new public theorems and thirteen headline QA theorems — three
standard axioms only; oleans built; **full `lake build` ✔ (2227
targets, "Build completed successfully", detached, zero errors)**;
`lint_axioms` (10, unchanged), `check_citations`,
`check_markdown_links` pass; scoreboard regenerated (**1162 QA
declarations / 10 explicit axioms / 0 sorries**; `Mixing_QA` 33 → 67).
Radar axis 5 **held at 3.0**: the proposal's own gate re-scores only
when a step's *proof* lands and its QA passes, and the mixing
*statement* — the χ² decay bound itself — is component 2; the hold and
its trigger are logged there.

### Step 2 — the ℓ²-mixing proxy (DELIVERED 2026-08-22, run
`20260822T081458Z-run-1`)

**The decide-and-record scoping gate, made before any statement (the
record this proposal authorizes a run to make):**

1. **The ℓ² statement alone satisfies this proposal's goal** for the
   mixing proxy; the ℓ² → TV conversion stays scoped as a further,
   separate step — exactly this proposal's own Step 4 framing ("own
   proposal-scale decision, not a default continuation").
2. **Within ℓ², the weighted form is primary.** The proxy is the χ²
   distance `χ²(t, x) = ∑ i, (ν_t i − π i)² / π i` with
   `π = deg/vol`, not the plain Euclidean
   `‖Pᵗ δₓ − π‖₂` of the original sketch. Reason: the geometric decay
   bound of Step 3 is Parseval-exact only in the π-weighted inner
   product — the one in which the transferred eigenbasis of Step 1 is
   orthogonal (D-orthogonality; the plain Euclidean inner product does
   not diagonalize the walk's adjoint evolution). The unweighted form
   is delivered as the corollary bridge
   `sum_sub_sq_walkDistribution_le` (any bound `c` on the stationary
   weights gives `∑ (ν−π)² ≤ c · χ²`; instantiating `c` at the largest
   stationary weight recovers the Euclidean statement), so consumers
   wanting the sketch's exact shape obtain it from the weighted proxy.

Delivered in the new `GraphTheory/Mixing.lean` (its own module — the
mixing objects are the named consumer topic of this proposal), all
proved, zero new axioms — `#print axioms` on every public theorem
reads only `propext, Classical.choice, Quot.sound`:

- **The mandatory Mathlib survey came back empty again**: no
  chi-square distance, no total-variation distance, no mixing-time or
  Markov-chain stationarity objects in the pinned snapshot (fresh
  search over `Mathlib/Probability` and `Mathlib/MeasureTheory`;
  the coverage map's recorded absence holds — no correction needed).
- `stationaryVec` (`π i = deg A i / vol A`) with `vol_univ_pos`,
  `stationaryVec_pos` (positive degrees + nonempty ⟹ strictly
  positive — the hypothesis that makes every χ² division meaningful),
  `sum_stationaryVec` (a probability vector), and `walk_isStationary`
  (the π-form stationarity, composed from the proved degree form
  `walkTransitionMatrix_transpose_mulVec_deg` by rescaling).
- `walkDistribution` (`(Pᵀ)ᵗ *ᵥ δₓ` — the adjoint action is the
  distributional one, matching the house orientation of the
  stationarity theorem) with `walkDistribution_zero`,
  `walkDistribution_succ` (via `pow_succ'` + `mulVec_mulVec`), and
  `sum_walkDistribution` (mass conservation, load-bearing on the
  row-stochasticity of `walkTransitionMatrix`).
- `walkDensity` (`ν_t/π`) with **`walkDensity_succ`**: in density
  coordinates the distributional evolution becomes the action of `P`
  *itself*, `h_{t+1} = P *ᵥ h_t` — the first consumer of the Phase A
  detailed-balance interface `walk_detailed_balance_measure`
  (delivered the same day by
  `reversibility-and-heat-semigroup.md` Phase A), and the interface
  Step 3 consumes: the transferred eigenbasis now governs the mixing
  evolution directly.
- `chiSquareDistance` with `chiSquareDistance_nonneg`, the vanishing
  characterization `chiSquareDistance_eq_zero_iff`
  (`χ²(t, x) = 0 ↔ ν_t = π`), the `t = 0` value
  `chiSquareDistance_zero` (`(π x)⁻¹ − 1` — Step 3's normalization
  constant), the density-form equivalence
  `chiSquareDistance_eq_sum_smul` (`∑ π (h_t − 1)²`, the exact
  quantity Step 3 computes by Parseval), and the plain-ℓ² corollary
  bridge `sum_sub_sq_walkDistribution_le`.
- Junk-value discipline: `walkDensity` and `chiSquareDistance` divide
  by `π i` and evaluate to `0` wherever `π i = 0`; every theorem
  carries the degree-positivity hypothesis that rules the case out,
  and QA refutes both hypothesis-free forms (below).

QA (`Mixing_QA.lean`, 33 declarations, all proved) on the P₃ fixture
(degrees 1, 2, 1 — genuinely irregular; `π = (1/4, 1/2, 1/4)` pinned
from degrees and volume): stationarity instantiated through the
theorem *and* cross-checked raw (`Pᵀ *ᵥ π = π`); the walk laws at
`t = 0, 1, 2` pinned (`δ₀`, `(0,1,0)`, `(1/2,0,1/2)`) with mass
conservation instantiated and recomputed from the pinned literal; the
density evolution instantiated and cross-checked raw
(`P *ᵥ (4,0,0) = (0,2,0)` — `P` itself, not its adjoint, exactly the
detailed-balance content); `χ²(0) = 3` by both routes (theorem
`(π 0)⁻¹ − 1` and the raw termwise sum `9/4 + 1/2 + 1/4`); `χ²(2) = 1`
raw — the bipartite *oscillation* (the law alternates
`(0,1,0) ↔ (1/2,0,1/2)`), never decaying, which is exactly the λ* = 1
behavior the Step-3 bound must reproduce on this fixture; the
density-form equivalence instantiated with its sum recomputed raw
(`1`); the plain-ℓ² bridge instantiated at `c = 1/2` with the
unweighted sum pinned to `3/8` (strict, `3/8 < 1/2`). Two negative
witnesses: the asymmetric `!![0,2;1,0]` (positive degrees, so only
`IsSymm` is missing) where hypothesis-free stationarity is refuted at
the entry where symmetry provably fails (`1/3 ≠ 2/3`); and the zero
adjacency where `χ²(0, 0) = 0` (junk division) while the law is the
point mass `≠ π` — refuting the hypothesis-free vanishing
characterization, so degree positivity is load-bearing.

Verification: `lake env lean` on the module and its QA — zero errors,
zero warnings each; `#print axioms` on all fourteen public and twelve
headline QA theorems — three standard axioms only; oleans built; **full
`lake build` ✔ (2227 targets, "Build completed successfully",
detached)**; `lint_axioms`, `check_citations`, `check_markdown_links`
pass; scoreboard regenerated (**1128 QA declarations / 10 explicit
axioms / 0 sorries**; `Mixing_QA` a new file row at 33). Radar axis 5
**held at 3.0** per this proposal's own gate (no re-score until a
step's *proof* lands and its QA passes — Step 2 is the definition and
evolution interface; the mixing *statement* itself is Step 3's decay
bound, which remains the re-score trigger).

### Step 1 — eigenpair transfer (DELIVERED 2026-08-22, run
`20260822T042339Z-run-1`)

Delivered in `GraphTheory/Normalized.lean` (its own named residual gap,
closed there), all proved, zero new axioms — `#print axioms` on every
new public theorem reads only `propext, Classical.choice, Quot.sound`:

- **The mandatory Mathlib survey came back empty**: no general
  similar-matrices-share-eigenvalues interface anywhere in the pinned
  snapshot (no `IsSimilar`, no charpoly-conjugation invariance under
  `Mathlib/LinearAlgebra/`) — exactly this proposal's anticipated
  branch, so the direct diagonal-case transfer was the cheaper route
  and no coverage-map correction was needed (the map already records
  the absence upstream).
- `walkLaplacian_mulVec_degreeInvSqrt` / `normalizedLaplacian_mulVec_degreeSqrt`
  — eigenpairs transfer **in both directions** through the similarity
  identity at the same eigenvalue, by conjugating the eigenvector
  (`(1/√D) *ᵥ v` forward, `√D *ᵥ w` backward). No characteristic
  polynomial is needed — the module docstring's recorded obstruction
  ("needs a charpoly-roots interface") turned out to be avoidable: pure
  `mulVec` algebra (`Matrix.mulVec_mulVec`, `Matrix.mulVec_smul_assoc`,
  the two inverse-factor lemmas, `Matrix.one_mulVec`) suffices.
- `walkTransitionMatrix_mulVec_degreeInvSqrt` — the transition form:
  a `μ`-eigenpair of `L_sym` gives a `(1 − μ)`-eigenpair of `P = D⁻¹A`.
- `walkLaplacian_mulVec_eigvecOf` / `walkTransitionMatrix_mulVec_eigvecOf`
  — the transfer instantiated at Mathlib's spectral-theorem eigenbasis
  of `L_sym` (`IsHermitian.mulVec_eigenvectorBasis`).
- `walk_eigvec_expansion` — completeness of the transferred family:
  every `w` is `∑ i, (v i ⬝ᵥ (√D *ᵥ w)) • ((1/√D) *ᵥ v i)` — the
  diagonalizability interface Step 3's decay bound consumes (built from
  `eigvecOf_expansion_apply` plus the invertibility shuffle).
- `walkEvals` (definition: `1 − evals (L_sym)`) with
  `exists_eigenvector_walkTransitionMatrix_eq_walkEvals` — every entry
  of the transferred walk spectrum is a genuine eigenvalue of `P` with
  an explicit nonzero conjugated-eigenvector witness (via
  `evals_mem_eigvalOf`); support lemmas `eigvecOf_ne_zero`,
  `degreeInvSqrt_mulVec_ne_zero`.

QA (`Normalized_QA.lean`, 14 → 34 declarations, all proved): the P₃
fixture (degrees 1, 2, 1 — genuinely irregular) with hand eigenpairs
`(1, √2, 1)`, `(1, 0, −1)`, `(1, −√2, 1)` at eigenvalues 0, 1, 2 — each
verified by raw computation, transferred **through the theorems**, and
cross-checked by raw arithmetic on the conjugated vectors `(1,1,1)`,
`(1,0,−1)`, `(1,−1,1)`; the backward transfer fed from the raw walk
eigenpair `(1,−1,1)`/eigenvalue 2 and pinned back to the hand
eigenvector; the `walkEvals` existential instantiated at every spectral
index; the transferred family's spanning witnessed by a hand-solved
combination reconstructing `(1,2,3)`; and the two guards the proposal's
negative-witness requirement motivates — **skipping the conjugation**
(`L_sym *ᵥ (1,−1,1) ≠ −1 • (1,−1,1)`) and **forgetting the `1 − μ`
reflection** (`P *ᵥ (1,−1,1) ≠ 2 • (1,−1,1)`), both refuted in proved
form. One QA-infrastructure note: the `√(deg)` atoms simp leaves behind
do not match hypothesis atoms written over `√2` (`√(1+1)` vs `√2`), so
the file pins a normalization bridge (`path_one_add_one_QA :
(1:ℝ) + 1 = 2`) consumed as a simp rewrite — future `√`-arithmetic QA
on this fixture reuses it.

Verification: `lake env lean` on the module and its QA — zero errors,
zero warnings (the module's only diagnostic is the pre-existing
`congr 1` note, identical in HEAD); `#print axioms` on all nine new
public theorems and seven headline QA theorems — three standard axioms
only; oleans built; **full `lake build` ✔ (2227 targets, detached)**;
`lint_axioms`, `check_citations`, `check_markdown_links` pass;
scoreboard regenerated (**1081 QA declarations / 10 explicit axioms /
0 sorries**); radar axis 5 re-scored 2.5 → 3.0 per the proposal's own
gate (proof landed, QA passed; the axis's named walk-spectrum gap
closed).

## Open next step

**None — the program is complete.** The optional items deliberately
*not* delivered, each a separate proposal-scale decision per this
document's own framing:

- the `sup'` packaging of λ* over `walkEvals` (component 1's recorded
  statement-shape decision: the theorem stays hypothesis-shaped and
  consumers instantiate; the multiset correspondence between
  `walkEvals` and the sorted reflected spectrum is a consumer's lemma,
  not a mixing statement);
- the ℓ² → total-variation conversion (Step 4's own framing: only if a
  named consumer needs TV specifically);
- the continuous-time comparison (heat kernels `e^{-tL}`, the
  reversibility proposal's gated Phase B).
