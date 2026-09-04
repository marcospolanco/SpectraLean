# The Foster Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-04 by run `20260904T125102Z-run-1`,
session `ses_f938e9b51ffeRdmWnSpY1UCtgD`; see the delivery record).

## Scope

The prior terminal handoff's named next target: "`Foster_QA` (the
spanning-tree counting program — `foster_theorem` itself is proved hard
crust, `#print axioms`-verified in the ADVERSARIAL_REVIEW pilot, so its
QA family fences theorem instantiations like this run's)". This run
audits the whole of `Scaffold/Mathlib/GraphTheory/Foster.lean` — the
zero-eigenvalue count `card_filter_eigvalOf_laplacian_eq_zero`, the
per-pair spectral kernel `effectiveResistance_eq_sum_eigbasis`, Foster's
theorem itself, the leverage corollary `sum_leverageScore_eq_two`, and
the `leverageScore` object's division guard — together with its QA file
(`Foster_QA.lean`, delivered 2026-08-19-era as four positive fixtures:
`K₃`, `K₄`, `P₃`, the 3-leaf star, with the double-counting-factor
witnesses). The family's QA predates the adversarial-review discipline
and carries **zero hypothesis-form fences**: no clause of any Foster
theorem has a negative witness anywhere in the repository.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(eight precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger, regular
Cheeger, effective-resistance, electrical-flow) — re-read every
theorem's hypothesis clauses, identify those with no negative witness,
and close each with a hypothesis-form fence (the dropped-hypothesis
statement refuted at a fixture where every other hypothesis is genuine,
certified by an isolation companion), or record a non-fenceable with
its mechanism.

## Step-0 findings: the priced fence list

Nine fences at the two delivered electrical fixtures plus one new
one-vertex fixture; four `hA` clauses recorded non-fenceable. No new
fixtures of graph shape are needed — the prior day's
effective-resistance audit delivered exactly the signed rank-1 and
disconnected fixtures this family's clauses want, and this audit
consumes them (the consumption order the handoff named).

### The zero-eigenvalue count `card_filter_eigvalOf_laplacian_eq_zero`

The theorem says the zero-eigenvalue filter has exactly one element.
The Laplacian always kills the constants (`L *ᵥ 1 = 0` identically, row
sums vanish), so the count is always `≥ 1`; both fenceable clauses make
it **≥ 2** by exhibiting two **non-parallel** kernel vectors — the
inversion of the theorem's own "at most one index" orthogonality
argument: every kernel vector's eigen-expansion lives entirely on the
zero-eigenvalue eigvecs (a nonzero eigenvalue's component is killed by
`dotProduct_eigvecOf_mulVec` against the kernel equation), so if the
filter held ≤ 1 element, the whole kernel would lie on one line and
could not contain two non-parallel vectors.

- **Fence (`hnn`)** at `sgnK4Adj` (delivered: symmetric, connected
  support, negative entries): the kernel contains `1` and
  `![1,1,-1,-1]` (delivered `sgnK4_kernel`) — non-parallel, so the
  filter card is `≥ 2 ≠ 1`. Connected support does not keep the
  zero-eigenvalue count at one once signs enter.
- **Fence (`hconn`)** at `connDiscAdj` (delivered: symmetric,
  nonnegative, not connected): the kernel contains `1` and the
  component indicator `![1,1,0,0]` (delivered
  `connDisc_indicator_in_kernel_QA`) — non-parallel, so the filter card
  is `≥ 2 ≠ 1`. Each component contributes its own zero eigenvalue.
- Non-fenceable (`hA`): the conclusion display itself consumes
  `laplacian_symmetric A hA` (structural).

### The spectral kernel `effectiveResistance_eq_sum_eigbasis`

`R u v = ∑_k, ite (λ_k = 0) 0 ((v_k u − v_k v)² / λ_k)`. The fenceable
clauses fail through the junk fallback on the left against a
**strictly positive** right side. The engine, shared by both fences:
if `L *ᵥ u = c • u` is a genuine eigenvector equation with `c ≠ 0`,
then every zero-eigenvalue eigvec is orthogonal to `u`
(`dotProduct_eigvecOf_mulVec` gives `(c − λ_k)(v_k ⬝ u) = 0`), so
`u`'s eigen-expansion lives on the nonzero modes; if the whole RHS
were `0` (each nonzero-mode term nonnegative — the eigenvalues are
`≥ 0` by PSD-ness, at the signed fixture through a fixture-local SOS
identity), every nonzero-mode eigvec would satisfy `v_k u = v_k v`,
forcing `u a = u b` for the eigen-pair's own coordinates — refuted by
the eigenvector's computed coordinate difference.

- **Fence (`hnn`)** at `sgnK4Adj`, pair `(0, 2)`: the LHS is the
  delivered junk fallback `0` (`sgnK4_fallback_zero_QA`); the RHS is
  `> 0`. The eigenvector: `s = ![1,-1,-1,1]` with `L *ᵥ s = 4 • s`
  (the rank-1 structure `L = s sᵀ`), PSD by the SOS identity
  `quadForm L f = (s ⬝ f)²`, and `s 0 − s 2 = 2 ≠ 0`.
- **Fence (`hconn`)** at `connDiscAdj`, pair `(0, 2)`: the LHS is the
  delivered junk fallback `0` (`disc_fallback_zero_QA`); the RHS is
  `> 0`. The eigenvector: `u = ![1,-1,0,0]` with `L *ᵥ u = 2 • u`, PSD
  by `laplacian_psd` (the fixture is nonnegative), and `u 0 − u 2 =
  1 ≠ 0`.
- Non-fenceable (`hA`): the display consumes `laplacian_symmetric A hA`
  in every eigvalOf/eigvecOf slot (structural).

### Foster's theorem `foster_theorem`

`(∑ i j, A i j * R i j) / 2 = card V − 1`. Both fenceable clauses fail
by direct ordered-sum computation from pinned resistance values.

- **Fence (`hnn`)** at `sgnK4Adj`: **every off-diagonal demand is
  unsolvable** — the map `x ↦ (w₁ x, w₂ x)` with the two kernel
  generators `w₁ = ![1,1,-1,-1]`, `w₂ = ![1,-1,1,-1]` is injective on
  `Fin 4`, and a solvable demand pairs to zero against both, forcing
  `u = v`. So every off-diagonal `R` is the junk `0` (the diagonal is
  `0` unconditionally), the ordered sum is `0`, and the conclusion
  reads `0 = 3` — false.
- **Fence (`hconn`)** at `connDiscAdj`: the two within-block resistances
  are genuinely `1` (`R 0 1` delivered; `R 2 3` by a symmetric witness),
  every cross-block conductance weight is `0` (so no junk value even
  enters), the ordered sum is `4`, and the conclusion reads `2 = 3` —
  false. Two components each contribute their own `n_i − 1`; the
  identity off by exactly the missing component count.
- Non-fenceable (`hA`): `hconn`'s own statement consumes
  `supportGraph A hA`, so the symmetry clause cannot be dropped alone
  (the same entanglement mechanism the effective-resistance audit
  recorded for its `supportGraph`-consumers).

### The leverage layer (`leverageScore`, `sum_leverageScore_eq_two`)

- **Fence (`hcard`)** at a new **one-vertex fixture** (the zero matrix
  on `Fin 1`: symmetric, nonnegative, connected, `card V = 1`): the
  leverage score divides by `card V − 1 = 0`, and the junk `0/0` reads
  `0`, so the ordered sum is `0 ≠ 2` — the cardinality hypothesis is
  the division guard the docstring names, exercised at the object
  itself. A value-pin companion records `leverageScore = 0` there.
- **Fence (`hnn`)** at `sgnK4Adj`: the ordered sum is `0` (the `hnn`
  fence above), so the leverage sum is `0/3 = 0 ≠ 2`.
- **Fence (`hconn`)** at `connDiscAdj`: the ordered sum is `4`, so the
  leverage sum is `4/3 ≠ 2`.
- Non-fenceable (`hA`): `hconn`-entangled as for `foster_theorem`.

### Screening summary

Every other clause of the family is either a parameter (`u v`, `A`) or
consumed structurally. The positive-fixture QA already delivered
double-counting-factor witnesses (`fosterTri_factor_QA`,
`fosterK4_factor_QA`) that fence *statement-shape* changes (dropping
the `/ 2`); nothing in the repository fenced a *hypothesis* drop — that
is this audit's increment.

## Delivery plan

QA-only, zero axiom contact (count stays 4; every new declaration a
theorem instantiation — no `-- @refutes` tags, nothing admitted
consumed). Spike the whole section in `wip/fosterfences_spike.lean` to
zero errors/zero warnings, then land as a pure insertion in
`Foster_QA.lean`'s new `FosterFences` section (importing the delivered
QA substrate: `Connectivity_QA` for `connDiscAdj`,
`EffectiveResistance_QA` for `sgnK4Adj` and the delivered value pins).
Full ladder after landing.

## Delivery record (2026-09-04)

Delivered at the full priced scope — all nine fences closed with
isolation companions. QA-only: 4780 → 4817 (+37 by the generator
metric; 39 new declarations = 37 theorems + the two fixture `def`s
`foF_sgnMode`, `foF_oneAdj`). Zero axiom contact: `#print axioms` via
`wip/fosterfences_axcheck.lean` on all 39 landed declarations — every
one exactly `propext, Classical.choice, Quot.sound`; no `-- @refutes`
tags (theorem instantiations, nothing admitted consumed).

What landed, beyond the fences themselves:

- **Two generic eigen engines** (statement-level reusable, no graph
  hypotheses): `ff_eigvec_dotProduct_of_kernel` (a kernel vector has no
  component along a nonzero-eigenvalue eigenvector) and
  `ff_eigvec_dotProduct_of_eigen` (a genuine eigenvector is orthogonal
  to every zero-eigenvalue eigenvector off its eigenvalue) — both
  `dotProduct_eigvecOf_mulVec` applied to the relevant equation —
  composing into `ff_two_kernel_filter_card_ge_two` (two non-parallel
  kernel vectors force `≥ 2` zero eigenvalues: a filter of size `≤ 1`
  confines the kernel to one eigen-line, since every kernel vector's
  `eigvecOf_expansion_apply` expansion lives on the zero-eigenvalue
  indices only) and `ff_sum_eigbasis_pos` (under nonnegative
  eigenvalues, the Foster spectral sum over a coordinate pair is
  strictly positive whenever a genuine eigenvector distinguishes the
  coordinates — the expansion-and-vanish argument with
  `Finset.sum_eq_zero_iff_of_nonneg` doing the per-term extraction).
- **The fixture facts**: the second kernel generator
  `![1,-1,1,-1]` pinned (`foF_sgnK4_kernel_w2`); the rank-1 mode
  `s = ![1,-1,-1,1]` with its eigen-equation `L *ᵥ s = 4 • s`, the
  multiplication formula `L *ᵥ f = (s ⬝ f) • s`, and the SOS identity
  `quadForm L f = (s ⬝ f)²` (the fixture-local PSD form — the signed
  fixture cannot use `laplacian_psd`); the disconnected fixture's
  block-antisymmetric mode eigen-equation `L *ᵥ ![1,-1,0,0] = 2 • u`
  and its `laplacian_psd`-based eigenvalue nonnegativity; the three
  new within-block resistance pins `R 1 0 = R 2 3 = R 3 2 = 1` (the
  fourth, `R 0 1`, delivered); the one-vertex fixture's three
  structural facts; and three isolation companions packaging every
  other hypothesis's genuineness at each fixture.
- **The headline mathematical findings**: (1) on the signed rank-1
  fixture *every* off-diagonal demand is unsolvable — the coordinate
  map `x ↦ (w₁ x, w₂ x)` over the two kernel generators is injective on
  `Fin 4`, a stronger statement than the delivered single-pair
  unsolvability, and it collapses the entire Foster ordered sum to `0`
  in one sweep (`foF_sgnK4_ordered_sum_zero_QA`); (2) the spectral-sum
  identity's two fenceable clauses fail with the *same* shape on both
  fixtures — junk-fallback zero on the left, forced-strict-positivity
  on the right — through one generic engine, with PSD-ness supplied
  differently at the two fixtures (rank-1 SOS vs `laplacian_psd`),
  which is exactly the division of labor the engine factoring was for;
  (3) the leverage corollary's `hcard` clause is the repository's
  first exercised `0/0` junk corner at the *object* level (the score,
  not a bound consuming it) — the docstring's "must not be read as a
  probability" warning now has a pinned value witness.

Recorded non-fenceables: the four `hA` clauses (each statement either
displays `laplacian_symmetric A hA` in its conclusion or carries
`hconn` whose own statement consumes the symmetry proof — the
entanglement mechanism class the effective-resistance audit recorded;
no freely-stated dropped-`hA` conclusion exists for this family).

### Technique findings

1. **The self-substitution rewrite trap, at its purest.** From
   `hg₂ : g₂ = (v ⬝ g₂) • v`, `rw [hg₂]` rewrites *every* `g₂` —
   including the one inside the coefficient `v ⬝ g₂` itself —
   producing a circular term and a motive failure one step later. The
   robust idiom is function-extensional: `congrFun hg₂ a`, `Pi.smul_apply`
   normalization, then `field_simp`/`ring` per point. (The
   electrical-flow audit's "rw with a placeholder against an
   inaccessible index" is the same class; this is the coefficient
   instance.)
2. **`Finset.sum_nonneg` cannot infer the Finset.** Applied as
   `Finset.sum_nonneg fun k _ => h k`, the `s : Finset α` argument
   stays a metavariable and elaboration dies with "don't know how to
   synthesize implicit argument 's'". The `have` needs its full type
   ascribed. Same shape one lemma over:
   `Finset.sum_eq_zero_iff_of_nonneg` needs the membership-quantified
   `fun k _ => …` form, not the bare `∀ k`.
3. **Un-ascribed numeral scalars elaborate as ℕ in eigen-equation
   statements.** `L *ᵥ s = 4 • s` on `Fin 4 → ℝ` elaborated the `4` as
   ℕ through `Matrix.mulVec`'s literal-`Matrix.of` path — surfacing not
   there but at the *consuming* generic-engine application, as a
   `(4 : ℕ) • u` vs `(4 : ℝ) • u` type mismatch far from its cause (a
   new instance of the recorded cast-trap class: smul scalars join
   identifiers and `Nat`/`ℝ` casts).
4. **`simp_all` normalizes but does not discharge false numeric
   hypotheses.** The 12-case injectivity bash left six goals carrying
   `h1 : -1 - 1 = 0`; `simp_all` had evaluated the vector literals but
   would not itself derive `False` from the arithmetic. The finisher
   `<;> (try norm_num at h1) <;> (try norm_num at h2)` — the `try`
   guards needed because exactly one of the two pairings is violated
   per case.
5. **`field_simp` can leave a pure `ring` goal.** On
   `c₁ * x = c₁ * c₂⁻¹ * (c₂ * x)` with `c₂ ≠ 0` in context it cleared
   the denominator but did not reorder the products; a trailing `ring`
   closes what `field_simp` normalized. (Also: `Finset.sum_subset`
   with an explicit `.symm` is the clean way to restrict a
   `Finset.univ` sum to a filter whose complement terms are provably
   zero — used twice in the kernel-line engine.)
