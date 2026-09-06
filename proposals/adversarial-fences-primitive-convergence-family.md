# Proposal: The Primitive-Convergence Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run `20260905T231333Z-run-1`,
session `ses_f8c5e42b3ffe41RPhC77iBiw0k`; delivery record below)

## Why this, why now

The prior terminal handoff's standing option: "a fresh consumption
survey for a new audit target (no pre-discipline QA family remains; a
survey would need to key on shelves without same-name QA — the
spectral-core audit's blind-spot lesson)". This run ran that survey
mechanically for the first time over DIRECT-import coverage: 58 shelf
modules, 51 directly imported by some QA file, 7 uncovered. Of the 7:

- `Probability.Concentration.Matrix.Basic` (14 transitive non-QA
  consumers) is a single instance declaration — no clause surface,
  classified;
- `GraphTheory.ClusterProjector` (1) and `GraphTheory.EdgePerturbation`
  (2) carry delivered audits (band-projector and sparsification-core
  respectively; their fences ride transitive QA imports — a keying
  artifact, not a gap);
- `Core` (0), `Core.Norms` (2), `Core.RandomVariable` (3) are small
  and deferred to the survey record below;
- **`LinearAlgebra.PrimitiveConvergence` (4 transitive non-QA
  consumers: `Mixing`, `Oversmoothing`, `DirectedMixing`, the
  `EmpiricalStationary` capstone) is the genuine gap**: 802 lines,
  ~24 theorems, the quantitative convergence engine of the whole
  directed axis — the Doeblin contraction, the entrywise-range
  engine, the primitive power-convergence theorem, and the
  primitivity suppliers — never per-clause fenced anywhere.

SGT leverage: every mixing/oversmoothing/PageRank-style statement
consumes this shelf's convergence or contraction interfaces; a wrong
clause shape here would poison the entire directed axis while all QA
stayed green (the sibling `IrreducibleStationary` shelf was audited
2026-09-05; this shelf was not).

## Step-0 census: the priced clause surface

Hypothesis-bearing theorems and their named clauses:

**The bookkeeping layer.** `pow_mulVec_one` (`hrow`),
`pow_nonneg_entries` (`hnn`), `pow_row_sum` (`hrow`),
`vecMul_pow_eq_of_vecMul_eq` (`h : π ᵥ* P = π`),
`exists_pos_le_of_finite` (`h : ∀ i ∈ s, 0 < f i`).

**The entrywise-range engine (Doeblin).** `mulVec_le_entrySup`,
`entryInf_le_mulVec`, `entryRange_mulVec_le` (each `hnn` + `hrow`);
`entryInf_le_dotProduct`, `dotProduct_le_entrySup` (each `hwnn` +
`hwsum`); `entryRange_mulVec_le_of_pos_entries` (`hrow`, `hle`);
`entryRange_pow_mul_le` (`hrow`, `hle` at the power).

**The convergence headline.** `primitive_power_tendsto`,
`primitive_entrywise_tendsto`, `primitive_vecMul_tendsto` (each
`hnn hrow hprim hπnn hπsum hπstat`).

**The primitivity suppliers.** `isPrimitive_of_pos` (`h`),
`reachable_of_pow_pos` (`hnn`), `isIrreducible_of_isPrimitive`
(`hnn`, `hprim`), `pow_entry_pos_of_pos` (`hnn h1 h2`),
`pow_entry_pos_bounce` (`hnn h1 hz1 hz2`),
`isPrimitive_of_pow_pos_of_odd_loop` (`hnn hreach htwo hodd`).

The `[Nonempty V]` guards on the entrySup/Inf/Range engine block the
empty corner at the type level (the degenerate-corner guard's own
recommended pattern) — the engine's empty instantiation cannot be
formed.

## Fixtures (three new, all `Fin 2`)

- `pcvCycle = !![0,1;1,0]]` — the docstring's own example: nonnegative,
  row-stochastic, irreducible, NOT primitive (powers alternate between
  the identity and the swap). Breaks `hprim`/`hodd`/`h`-stationarity
  clauses while keeping every stochasticity clause genuine; its
  oscillation `(P^t) *ᵥ e₀ = e₀/e₁/e₀…` is the non-convergence
  breaker for the convergence trio.
- `pcvSigned = !![2,-1;-1,2]]` — row-stochastic with negative entries:
  breaks `hnn` keeping `hrow` genuine (the range engine expands:
  `M *ᵥ (1,-1) = (3,-3)` escapes `entrySup`).
- `pcvDiag = !![2,0;0,0]]` — nonnegative with broken row sums: breaks
  `hrow` keeping `hnn` genuine (the range doubles on `y = (1,0)`).

Plus the weight-vector breakers for the dotProduct pair and the
zero-matrix breaker for `isPrimitive_of_pos`.

## Delivery record

DELIVERED at the full priced scope of the in-run cull — nineteen
hypothesis-form fences plus fixtures, pins, the oscillation engine,
and kept-clause companions in the NEW
`Scaffold/QA/LinearAlgebra/PrimitiveConvergence_QA.lean` (54
declarations = 50 theorems + 4 `def`s; +50 by the generator metric,
6270 → 6320), QA-only, zero axiom contact (`#print axioms` via
`wip/pcvfences_axcheck.lean` on all 54 — every one a subset of
`propext, Classical.choice, Quot.sound`; no `-- @refutes` tags —
theorem instantiations of an all-proved shelf; the 24-tag
independence check unchanged and clean; the module elaborates with
zero errors and zero warnings).

The fences, by layer:

1. **Bookkeeping.** `pow_mulVec_one`'s and `pow_row_sum`'s `hrow` at
   the doubling diagonal (`diag(2,0)^1 *ᵥ 1 = (2,0) ≠ 1` at `t = 1`);
   `pow_nonneg_entries`' `hnn` at the signed matrix (`(0,1)`-entry
   `-1 < 0`); `vecMul_pow_eq_of_vecMul_eq`'s stationarity `h` at
   `e₀ ᵥ* cycle = e₁ ≠ e₀`; `exists_pos_le_of_finite`'s positivity
   `h` at the zero-member function on `Fin 1`.
2. **The Doeblin entrywise-range engine.** `mulVec_le_entrySup`,
   `entryInf_le_mulVec`, `entryRange_mulVec_le` each fenced at BOTH
   breakers (signed: the range doubles `2 → 6`; diagonal: `1 → 2`);
   the dotProduct pair at the signed weight `(2,-1)` (mass one, one
   negative entry) and the mass-wrong weights (`(0,0)` and `(2,0)`);
   `entryRange_mulVec_le_of_pos_entries`' `hrow` at `δ = 0` (the
   range doubles against the claimed factor `1`) and its `hle` at the
   inflated `δ = 1` (the claimed factor is `-1` against a nonnegative
   range); `entryRange_pow_mul_le`' both clauses at the same kills.
3. **The convergence headline.** All three `hprim` clauses —
   `primitive_power_tendsto`, `primitive_entrywise_tendsto`,
   `primitive_vecMul_tendsto` — killed by the docstring's own
   directed 2-cycle: the `(0,0)` entry of the powers alternates
   `1,0,1,0…`, so the powers converge to nothing (the even/odd
   subsequence engine: `Tendsto (2·_)` and `Tendsto (2·_+1)` via
   `tendsto_atTop_atTop`, both composed limits pinned against
   `tendsto_const_nhds` by `tendsto_nhds_unique` — `c = 1 = 0`), with
   the vector and vecMul forms composed through `continuous_apply`;
   every kept clause genuine at the cycle (nonnegative,
   row-stochastic, the stationary `pcvHalf = (1/2,1/2)`).
4. **The primitivity suppliers.** `isPrimitive_of_pos`'s `h` at the
   cycle's zero entries; `isIrreducible_of_isPrimitive`'s `hprim` at
   the diagonal — nonnegative (kept clause genuine) but vertex `0`'s
   reachability stays at `0` by the `ReflTransGen` tail induction;
   `isPrimitive_of_pow_pos_of_odd_loop`'s `hodd` — the cycle is
   bipartite (no odd power has a positive diagonal) with `hreach` and
   `htwo` companions proving the kept clauses genuine, the conclusion
   failing by `pcvCycle_not_primitive` (even powers are the identity,
   odd powers the swap).

Deferred with priced mechanisms:

- **The convergence trio's `hnn`/`hrow`/`hπnn`/`hπsum`/`hπstat`
  clauses**: the `hnn` fence needs a signed row-stochastic PRIMITIVE
  matrix (the `2×2` signed stochastic matrices are never primitive —
  their off-diagonal power entries stay negative); the `hrow` fence
  needs a substochastic primitive matrix with a genuine mass-one
  stationary vector, which may not exist (substochastic primitivity
  forces spectral radius `< 1`, excluding nonzero stationary vectors —
  possibly truth-entangled through the theorem's own proof route,
  which derives a `Nonempty V` witness from `hπsum`); the `hπ*`
  clauses need a non-stationary or signed `π` at the cycle with the
  convergence still failing — priced, feasible at `π` NOT stationary
  (the conclusion's limit is then wrong even where powers converge).
- **The signed-cancellation walk classes** (`reachable_of_pow_pos`'s
  and `isIrreducible_of_isPrimitive`'s `hnn`,
  `pow_entry_pos_of_pos`'s `hnn`/`h1`/`h2`, `pow_entry_pos_bounce`'s
  clauses): each needs a matrix whose positive power-entries arise
  only through negative-product paths cancelling in the sum — a `3×3`
  design where the `k`-term of the convolution is positive but the
  other terms drive the total negative. Priced as a follow-up.

Technique findings recorded for future audits:

1. **The oscillation engine is one reusable lemma**: prove the
   no-limit fact ONCE for the alternating entry sequence, then get
   the vector and vecMul forms by composing with `continuous_apply`
   — no per-form filter work.
2. **`ReflTransGen`'s induction alternative is `tail`, not `trans`**
   (the recursor's minor premise is `tail : rest → step → motive`),
   and the IH is the LAST nameable argument.
3. **`rw` of a generic lemma (`entrySup y = max …`) rewrites only the
   first matched instantiation** — at multi-occurrence goals use
   `simp only [lemma]`, which rewrites all.
4. **`fin_cases` on a compound term is invalid syntax** — case the
   variable and spell the compound's values per case.


## Deferral-closure record: the π-clause cluster (2026-09-05)

The audit's priced π-clause follow-up ("feasible at `π` NOT
stationary — the conclusion's limit is then wrong even where powers
converge") delivered the same day: five hypothesis-form fences plus
the fixture, the power decomposition, the decay engine, and the
entanglement pin in `PrimitiveConvergence_QA.lean`'s new
`PiClauseFences` section (23 declarations = 22 theorems + the
fixture def; +22 by the generator metric, 6320 → 6342), QA-only,
zero axiom contact (`#print axioms` via `wip/pcvfences2_axcheck.lean`
on all 23 — every one a subset of `propext, Classical.choice,
Quot.sound`; the 24-tag independence check unchanged and clean).

**The engine.** The strictly-positive fixture
`pcvPos = !![3/4, 1/4; 1/4, 3/4]` — primitive by `isPrimitive_of_pos`,
doubly stochastic, symmetric — carries the two-idempotent spectral
decomposition `P = A + (1/2)·B` (`A = (1/2)J`, `B = I − (1/2)J`, both
idempotent with zero cross-products), here evaluated entrywise as the
explicit power identity `P ^ t = !![1/2 + r_t/2, 1/2 − r_t/2;
1/2 − r_t/2, 1/2 + r_t/2]` with `r_t = (1/2)^t` (proved by entrywise
induction; the smul-spelled algebraic form was abandoned after the
`smul_eq_mul` instance-diamond made entrywise evaluation erratic —
the explicit-entry spelling is the robust route). The ACTUAL limit of
`P ^ t *ᵥ x` is the averaging vector `![(x₀+x₁)/2, (x₀+x₁)/2]` (the
coordinate tendsto through the decay engine `(1/2)^t → 0`).

**The fences.** `primitive_power_tendsto`'s `hπstat` at the
non-stationary mass-one `π = e₀` (`e₀ ᵥ* P = (3/4, 1/4) ≠ e₀`,
pinned): the powers genuinely converge, the claimed limit
`(π ⬝ᵥ x) • 1` differs from the actual one, and
`tendsto_nhds_unique` makes `1 = 1/2`. Its `hπsum` at the stationary
mass-two `π = (1,1)` (stationarity pinned, mass `2 ≠ 1`): the claimed
limit doubles. `primitive_entrywise_tendsto`'s `hπstat`: the `(0,0)`
entry converges to `1/2`, the claimed limit at `e₀` is `1`.
`primitive_vecMul_tendsto`'s `hπstat` (via the power-symmetry
`pcvPos_pow_symm_apply`, through `Matrix.transpose_pow`) and its
`hνsum` at the mass-two `ν = (2,0)` with the genuine stationary
`pcvHalf` (the row action converges to `2 • (1/2, 1/2) = (1,1)`, not
`π`).

**The entanglement classification.** The `hπnn` clause cannot be
broken: `pcvPos_stationary_eq` proves the fixture's stationary space
is `span (1,1)` by two-by-two linear algebra, so every mass-one
stationary vector is the (nonnegative) uniform one — and in general,
primitivity of a stochastic matrix forces a strictly positive
one-dimensional stationary space (Perron), so no signed mass-one
stationary vector exists at ANY admissible fixture: breaking `hπnn`
requires breaking `hπstat` or `hπsum` too. Recorded as entangled,
not fenced.

**The survey's residual, classified.** `Matrix/Basic` (a single
instance declaration), `Scaffold.Mathlib.Core` (2 lines),
`Core/RandomVariable` (two type aliases `RV`/`MRV`), and
`Core/Norms` (one hypothesis-free theorem) are definition-only — no
clause surface. With this, the direct-import survey program is
CLOSED: every shelf module either has direct QA coverage or is
definition-only.

Remaining deferrals (unchanged, priced): the convergence trio's
`hnn` clause (a signed row-stochastic PRIMITIVE fixture — `2×2` signed
stochastic matrices are never primitive; a `3×3` design is priced)
and `hrow` clause (substochastic primitive with a mass-one
stationary vector — carries a nonexistence sketch: strict
substochasticity propagates through primitivity to contract every
row-sum of every power, contradicting stationarity at mass one;
possibly truth-entangled), and the signed-cancellation walk quartet.

Technique findings recorded for future audits:

1. **The smul-instance diamond kills entrywise evaluation**: the
   `•` produced by `Matrix.smul_apply` on ℝ-entries lives at a
   different instance (`DistribMulAction`-family) than
   `smul_eq_mul`'s, so simp silently fails to numericize — spell
   decomposition lemmas with explicit numeral entries instead.
2. **`tendsto_const_nhds` has no named-argument `c`** (it is
   implicit) — ascribe the constant tendsto via a typed `have`.
3. **A real-convergence contradiction needs the ACTUAL limit**: the
   claimed-vs-actual pattern (`tendsto_nhds_unique` of the
   fence-hypothesis against the proved limit) is the reusable kill
   shape for every wrong-limit fence class.


## Remainder-closure record: the walk quartet + the positive-clause
tail (2026-09-06)

The audit's remaining priced deferral, closed: ten hypothesis-form
fences plus fixtures and pins in `PrimitiveConvergence_QA.lean`'s new
`CancellationFences` section (52 declarations; +42 by the generator
metric, 6342 → 6384), QA-only, zero axiom contact (`#print axioms` via
`wip/pcvfences3_axcheck.lean` on all 52 — every one a subset of
`propext, Classical.choice, Quot.sound`; the 24-tag independence
check unchanged and clean). **The primitive-convergence family's
priceable clause surface is now closed in full.**

The signed-cancellation quartet (each fixture designed so every kept
clause stays genuine):

1. **`reachable_of_pow_pos`'s `hnn`** at `pcvCxl = !![1,-2;0,-2]]`:
   the `(P²) 0 1`-entry is `1·(-2) + (-2)·(-2) = 2 > 0` (pinned) —
   pure negative-product arithmetic — while the only positive
   single-edge is the loop `0 → 0`; the tail induction keeps
   reachability from `0` at `0`.
2. **`isIrreducible_of_isPrimitive`'s `hnn`** at
   `pcvAllNeg = !![0,-1;-1,-1]]`: no positive single-edge exists at
   all, yet `P² = [[1,1],[1,2]]` strictly positive (pinned), so
   primitivity is genuine and irreducibility fails at `(0,1)`.
3. **`pow_entry_pos_of_pos`'s `hnn`** at `pcvQch = !![1,1;0,-2]]`:
   both kept power-entry hypotheses genuine (`M 0 0 = M 0 1 = 1`),
   `(M²) 0 1 = 1·(1 + (-2)) = -1`.
4. **`pow_entry_pos_bounce`'s `hnn`** at
   `pcvBnc = !![0,1,-2;0,0,1;0,1,1]]`: every kept clause genuine
   (`M 0 1 = M 1 2 = M 2 1 = 1`), `(M³) 0 1 = 1 - 2 = -1` — the
   `k`-term of the convolution positive, the `-2` rider quenching
   the total.

The positive-clause tail (clauses the original audit's cull never
reached): `pow_entry_pos_of_pos`'s `h1` at `!![0,0;1,0]]` and `h2` at
`!![1,0;0,0]]` (cube entries zero, the twin clause genuine); the
bounce's `h1`/`hz1`/`hz2` at three degenerate 3×3 fixtures; and the
odd-loop supplier's `hreach` at `pcvSnk = !![0,1,0;1,1,0;0,1,1]]` —
every kept clause GENUINE (nonnegativity, `htwo` with every vertex in
a positive 2-cycle, `hodd` with odd returns pinned everywhere
including the length-3 return at vertex 0), yet `(0,2)` is reachable
by no power (the column-2 lemma, by induction: nothing but `2`
enters column 2, so `(P^a) 0 2 = 0` for all `a ≥ 1`) and primitivity
fails.

The convergence trio's own `hnn`/`hrow` clauses, CLASSIFIED (not
fenced):

- **`hnn` is truth-removable.** Primitive + row-stochastic (any
  signs) implies `P^K > 0` for some `K`; `P^K` is then a positive
  row-stochastic matrix, whose Perron spectrum is `ρ = 1` simple
  with every other eigenvalue `|λ| < 1`; since the spectrum of `P`
  is the `K`-th roots of that of `P^K`, the same holds for `P`, and
  the power sequence converges — the theorem's conclusion holds at
  every `hnn`-breaking fixture. The shelf proof's `hnn` consumption
  (the non-expansiveness remainder step) is a proof artifact, not a
  truth boundary. A formal proof would go through the spectral
  route — priced, not owed.
- **`hrow` has no admissible fixture.** A substochastic matrix with
  any strict row, raised to the primitivity power, is strictly
  row-substochastic in every row (positivity propagates the strict
  contraction through the positive power entries); a mass-one
  nonnegative stationary `π` then has its mass strictly contracted
  by `π ᵥ* P^K = π` — a contradiction. Sketch recorded; a formal
  proof is the strict-contraction induction, priced.

Technique findings: the cancellation fixtures were designed and
hand-verified numerically BEFORE any Lean was written (the audit
method's Step-0 discipline applied to fixture design); the
entrywise-evaluation trap from the π-clause run (`Matrix.of_apply`
needed for `!![...]`-lookups) recurred and is now recorded twice.
