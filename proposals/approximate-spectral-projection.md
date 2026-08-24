# Proposal: Approximate Spectral Projection with Error Bounds

**Status:** Step 0 DELIVERED 2026-08-23 (run `20260823T132040Z-run-1`),
**Step 1a DELIVERED 2026-08-23** (run `20260823T215632Z-run-1`),
**Step 1b DELIVERED 2026-08-23** (run `20260823T232953Z-run-1`), and
**Step 1c DELIVERED 2026-08-24 (run `20260824T012049Z-run-1`) — the
proposal is COMPLETE**: the **Lanczos/Kaniel–Paige shape is CLEARED**
as the one tractable shape — the exact finite-`k` statement, the full
machinery checklist, and a green axiom-clean skeleton spike are
recorded in the Step-0 record below; Nyström is deferred with its
obstruction named, and the Chebyshev-filter shape is recorded as the
natural second consumer of the same Chebyshev layer (to be attempted
only in its own run). Step 1 (the interface layer + spectral
discharge + statement + QA, priced below at ~600–800 lines across 2–3
runs) is authorized on the cleared shape only; **all three steps are
now delivered** — 1a (the interface layer), 1b (the spectral
discharge, culminating in the composite `kanielPaigeChebyshev`), and
1c (the final statement `kanielPaige` at the Step-0 recorded shape
plus the four proposal-mandated QA witnesses) — see the records
below. No new axioms anywhere in this proposal. Original scoping
header: proposed 2026-08-19, priority **Medium**, contingent on Step
0; assistant's assessment of project direction, requested 2026-08-19,
promoted from `sgt-gaps.md` item 7. Authorizes no axiom admissions or
external publication.

## Clean-room boundary

Internal prioritization and analysis. If counsel approves a public
repository export, restate from standard numerical-linear-algebra sources
(Saad; Trefethen & Bau). Do not copy this proposal verbatim.

Assessed from `Scaffold/Mathlib/GraphTheory/Spectral.lean`
(`spectralProjector`, the exact eigendecomposition machinery this
proposal's subject approximates), `icebox/lyapunov-stability-
formalization-gap.md` (the closest precedent in this repository for
"a genuinely different kind of math than what's already here"), and a
search of the pinned Mathlib for Lanczos/Chebyshev/Nyström machinery
(none found).

## Step 1c record (2026-08-24, run `20260824T012049Z-run-1`)

**DELIVERED** — the proposal COMPLETE — as pure hard crust in the new
Step-1c section of `Scaffold/Mathlib/GraphTheory/Krylov.lean` plus
`Scaffold/QA/SpectralGraph/Krylov_QA.lean` (extended 35 → 50) — zero
new axioms (count stays 9), QA 1606 → 1621.

**The theorem** (`#print axioms` the standard three, via
`wip/krylov1c_axcheck.lean` on it plus all 15 new QA): **`kanielPaige`**
at exactly the Step-0 recorded shape — symmetric `M`, unit top
eigenvector `u` at `Ltop`, **unit `b` with `u ⬝ᵥ b ≠ 0`** (the only
starting-vector hypothesis; no hand-supplied `c`/`s`/`g` — the
decomposition is internal via the 1b `exists_unit_decomposition`),
`Lbot < Ltwo ≤ Ltop`, the 1b eigenbasis-level band hypothesis `hpar`,
`k ≥ 1`; the conclusion: `∃ x ∈ krylovSpan M b k, x ≠ 0 ∧ Ltop −
rayleigh M x ≤ (Ltop − Lbot) · (1 − (u ⬝ᵥ b)²)/(u ⬝ᵥ b)² /
T_{k−1}(1 + 2γ)²` at `γ = (Ltop − Ltwo)/(Ltwo − Lbot)` — the classical
`tan²φ`/gap form. Composed from `kanielPaigeChebyshev` by exactly three
identifications, each a short lemma in the proof: `c = u ⬝ᵥ b`
(orthogonality kills the `g` term), `s² = 1 − c²` (the unit norm, by
`linear_combination`), and `w(Ltop) = 1 + 2γ` (the band map's closed
form against the gap arithmetic, `congr 1` + `field_simp`). The Saad
§6 locator now attaches to the statement's own docstring, with this
proposal's clean-room caveat carried verbatim (to be confirmed against
the physical copy before any committed external use; the statement is
proved, not admitted).

**QA (+15), the four witnesses the plan names plus the supporting
pins:**

- **the final-form instantiation + two-route constant agreement** on
  `diag(3,1,0)` at `k = 2` (`kanielPaige_diag310_QA`): every
  hypothesis discharged numerically (`u ⬝ᵥ b = 3/5 ≠ 0` the only new
  one), the γ-form Chebyshev value `T₁(5) = 5` proved raw (through
  `T_one`, independent of the band map) *and* equal to the 1b
  composite's `(T₁ ∘ w)(3) = 5` (`kanielPaige_final_chebValue_twoRoutes_QA`),
  the final bound **proved expression-equal to the composite's**
  (`kanielPaige_final_bound_eq_composite_QA` — a wrong `γ`-form or an
  inverted `tan²φ` anywhere in the restatement breaks the equality),
  both pinning `16/75` (`kanielPaige_diag310_final_value_QA`), with
  the raw true gap `32/241` proved strictly inside;
- **the `k = 1` degenerate case** (`kanielPaige_diag310_k1_QA`,
  `cheb_T0_degenerate_QA`, `rayleigh_diag310_bvec310_raw_QA`,
  `kanielPaige_diag310_k1_value_QA`): `T₀ ≡ 1` pinned at the γ-argument,
  the bound reduced to the plain Rayleigh-gap value
  `(Ltop − Lbot)·tan²φ = 16/3`, the actual gap at the only Krylov
  direction computed raw (`R(b) = 43/25`, so `3 − 43/25 = 32/25 ≤
  16/3`) — the Chebyshev acceleration provably contributes nothing at
  `k = 1`, exactly the classical one-step statement;
- **the `b = u` tightness witness** (`rayleigh_diag310_le_three_QA`,
  `kanielPaige_tightness_bEqU_QA`): the bound pinned `= 0` at
  `tan φ = 0`, and the delivered witness's Rayleigh value pinned to
  exactly `Ltop` from both sides — the theorem gives `3 − R(x) ≤ 0`,
  the raw entrywise ceiling (`3y₀² + y₁² ≤ 3(y₀²+y₁²+y₂²)`, by
  `nlinarith` at the two square hints) gives `R(x) ≤ 3` — bound
  attained, not merely satisfied;
- **the `λ₁ = λ₂` guard refuted in proved form** on the new
  top-multiplicity fixture `diag330 = diag(3,3,0)`: every eigenvalue
  `∈ {3, 0}` derived from the eigen-equation alone
  (`diag330_eigval_two_vals_QA`), the band `[14/5, 29/10]` containing
  neither, so `hpar` itself is **false**
  (`kanielPaige_topGuard_hpar_fails_QA`: it would make all three
  orthonormal eigenbasis vectors multiples of `e₁`, and `t₀t₁ = 0`
  contradicts `t₀² = t₁² = 1` — two orthogonal unit vectors cannot
  share a line); and the **hypothesis-free conclusion refuted**
  (`kanielPaige_topGuard_refuted_QA`) with every other hypothesis
  verified on the fixture: `u = e₁` a unit eigenvector at `3`, `b =
  (2/3, 2/3, 1/3)` unit with `u ⬝ᵥ b = 2/3 ≠ 0`, `14/5 < 29/10 ≤ 3`,
  `k = 1` — the `k = 1` Krylov space collapsed to the line `ℝ · b` by
  the span's own definition (the 1a degree-guard pattern), every
  nonzero vector on it carrying Rayleigh value exactly `8/3` computed
  by linearity (`smul_dotProduct`/`mulVec_smul`, not entrywise sums),
  so the true gap `1/3` provably exceeds the evaluated bound `1/4 =
  (3 − 14/5)·(5/4)/T₀(3)²`. The simple-top guard is load-bearing, not
  decoration.

**Pin-technique notes (this run's additions):**

- the refutation's Rayleigh computation routes through the smul
  linearity lemmas (`Matrix.smul_dotProduct`, `Matrix.mulVec_smul`,
  `Matrix.dotProduct_smul`, then `smul_smul`/`smul_eq_mul`) rather
  than entrywise sums — `rw [← hr, ...]` first (the membership
  equation `r • b = x` rewrites right-to-left to expose the smuls);
  the quotient cancellation is `rw [div_eq_iff hrr0]; ring` on a
  standalone `have` (`mul_div_cancel_left₀` exists at the pin but
  strands on a `MulDivCancelClass` metavariable inside `rw`).
- `zero_smul` (not `smul_zero`) kills `0 • b = x` in the nonzero
  derivation; `simp [huu, hgu]` closes the `c = u ⬝ᵥ b` orthogonality
  identity where an explicit `dotProduct_smul` chain strands on
  simp's having normalized the goal shape already.
- the `Fin 3` nested-if trap re-hit as recorded: `norm_num` alone
  strands `if 2 = 0 then …` in dot-product sums over nested if-form
  vectors — the robust closure is `simp [defs, Matrix.dotProduct,
  Fin.sum_univ_three]; norm_num` (plain `simp` decides the index
  equalities), with the `<;>` form flagged by the
  `unnecessarySeqFocus` linter when `simp` leaves exactly one goal.
- the guard refutation's eigenvalue dichotomy proof carries a
  by-contra structure the 1b `hpar` derivation did not: the `μ ∉ {3,0}`
  branch needs all three coordinate equations, and each
  `(3 − μ)v = 0` factorization goes through `linear_combination` +
  `mul_eq_zero` with the `absurd (by linarith : μ = 3) hμ3` shape.

## Step 1b record (2026-08-23, run `20260823T232953Z-run-1`)

**DELIVERED** as pure hard crust in `Scaffold/Mathlib/GraphTheory/
Krylov.lean` (the new `KrylovDischarge` section) plus
`Scaffold/QA/SpectralGraph/Krylov_QA.lean` (extended 19 → 35) — zero
new axioms (count stays 9), QA 1590 → 1606.

**The module** (every `#print axioms` the standard three, via
`wip/krylov1b_axcheck.lean` on all 14 new public theorems + the
`bandMap` definition + all 16 new QA):

- **the general-eigenvector transfer layer** — `eigvec_dotProduct_mulVec`
  (`u ⬝ᵥ (M *ᵥ y) = μ (u ⬝ᵥ y)` at `M *ᵥ u = μ • u` through the pin's
  `dotProduct_mulVec`/`mulVec_transpose` at `IsSymm`), the power
  version (`transpose_pow` + `Heat.pow_mulVec_smul`), and the
  polynomial version `eigvec_dotProduct_aeval_mulVec`
  (`u ⬝ᵥ (p(M) g) = (u ⬝ᵥ g) · p(μ)` by the monomial-sum
  decomposition) — **not tied to `eigvecOf`**, so any eigenvector
  qualifies; at `u ⊥ g` this is the `horth` site, and one
  self-adjointness instance closes `horthM`;
- **the component layer** — `eigvecOf_dotProduct_aeval_mulVec` (the
  `i`-th eigencomponent of `p(M) y` is `p(μ i)` times the `i`-th
  component of `y`), with the resolution identities
  `dotProduct_aeval_mulVec_self` (Parseval for polynomial images) and
  `quadForm_aeval_mulVec` — the `hband`/`hbottom` engines;
- **the affine band map** — `bandMap Ltwo Lbot :=
  C(2/(Ltwo−Lbot)) · (X − C((Ltwo+Lbot)/2))` with `bandMap_eval` (the
  closed form `(2μ − Ltwo − Lbot)/(Ltwo − Lbot)`), the endpoint pins
  (`w(Lbot) = −1`, `w(Ltwo) = 1`), `abs_bandMap_eval_le_one` (the band
  range), `one_le_bandMap_eval` (growth above the band), and
  `natDegree_bandMap = 1` — supplying `hp₁`/`hdeg`/`hTv` at the
  composed polynomial `T_{k−1} ∘ w` through `natDegree_T`,
  `natDegree_comp` (unconditional at this pin), and the 1a growth
  lemma;
- **`exists_unit_decomposition`** — unit `b` along unit `u`:
  `b = c • u + s • g` with `g ⊥ u`, `‖g‖² ≤ 1`, `c² + s² = 1`
  (`c = u ⬝ᵥ b` forced by orthogonality, `s = √(1−c²)`, the `s = 0`
  branch degenerating to `g = 0` — no existence assumption needed);
  `1 − c² = ‖b − (u⬝ᵥb)•u‖² ≥ 0` internally, no Cauchy–Schwarz
  required;
- **the capstone `kanielPaigeChebyshev`** — the full skeleton
  conclusion at `T_{k−1} ∘ w`, every spectral site discharged. The
  step's mathematical crux is the **band/parallel dichotomy**: the
  band hypothesis is stated eigenbasis-level (`hpar`: every
  eigenvector at an eigenvalue outside `[Lbot, Ltwo]` is a multiple of
  `u`; with `Ltwo ≤ Ltop` this says the only eigenvalue above `Ltwo`
  is the simple top one — and the multiplicity-2 counterexample shape
  `(v₁+v₂)/√2` shows why the weaker "every eigenvector ⊥ u is
  in-band" form would NOT suffice), and at `g ⊥ u` it forces every
  nonzero eigencomponent of `g` into the band, where `|T ∘ w| ≤ 1`
  caps the polynomial image's norm (hband, via Parseval) and the band
  floor lower-bounds its quadratic form (hbottom, via
  `quadForm_aeval_mulVec`), termwise at `Finset.sum_le_sum` with the
  zero-component indices discharged by cases.

**QA** (+16): the band-map pins **two routes** (the delivered
endpoint/degree theorems vs. the hand closed form `w(μ) = 2μ − 1` at
`Ltwo = 1, Lbot = 0`, all three values agreeing), the growth pair
`1 ≤ w(3) = 5` composed; the self-adjointness transfer **two routes**
at the eigenvector `e₁` of the 2×2 fixture (`e₁ ⬝ᵥ (M ![3,−5]) = 6` by
theorem vs. by hand `M ![3,−5] = ![6,0]`); the polynomial transfer
**two routes** (`e₁ ⬝ᵥ (p(M) ![1,−1]) = 5` by theorem vs. by hand
`p(M) = diagM² + 1 = !![5,0;0,1]`); and on the new 3×3 fixture
`diag(3,1,0)` — entrywise-encoded (`Matrix.diagonal` + if-form
vectors) per the recorded `Fin 3` cons-literal trap — the centerpiece:
**`diag310_hpar_QA` derives the band hypothesis from the
eigen-equation alone** (out-of-band below `μ < 0` vacuous — the
coordinates force the zero vector against the `eigvecOf_inner` unit
norm; above `1 < μ` forcing the `e₂`/`e₃` coordinates to vanish),
**the composite instantiated end-to-end** at `b = (3e₁ + 4e₂)/5`,
`k = 2`, with the delivered bound's value pinned `= 16/75` (through
`T₁(w(3)) = 5`), and **the independent raw route** — the actual Krylov
witness `x = (3, 4/5, 0)` exhibited as the generator combination
`2(Mb) − b` (membership by the span's own definition, no polynomial
interface) with its Rayleigh value computed raw to `691/241`, so the
true gap `32/241 ≈ 0.133` is *proved* strictly inside the delivered
`16/75 ≈ 0.213`; plus the unit-decomposition instantiation with both
content pins forced (`c = 3/5` by orthogonality, `s² = 16/25` by the
norm).

**Pin-technique notes (this run's additions, for 1c):**

- `T` does not resolve through `open Polynomial` (`open
  Polynomial.Chebyshev` would be needed) — and an unresolvable `T` in
  a statement silently **auto-bounds a universe variable named `T`**,
  surfacing later as "function expected at T". Write
  `Polynomial.Chebyshev.T` explicitly, as the 1a module already does.
- projection `.comp` binds tighter than application: `T ℝ (x).comp q`
  parses as `T ℝ (x.comp q)` — parenthesize the whole polynomial
  before `.comp`.
- `Matrix.dotProduct_sum` does not exist at this pin; the
  second-slot helper (`v ⬝ᵥ ∑ F i = ∑ v ⬝ᵥ F i`) is three lines of
  `Finset.induction`.
- the `⟨n, ⋯⟩`-form indices of `fin_cases` **resist `rfl`** (the
  recorded Heat trap, re-hit); `norm_num` strands `¬⟨2,⋯⟩ = 0`
  conditions that plain `simp` decides — on `Fin 3` the robust
  fixture encoding is entrywise (`Matrix.diagonal` + if-form vectors),
  closed by `simp [...] <;> norm_num` (norm_num for the fraction
  arithmetic simp leaves).
- `simp` on an *equation between two reducible-if expressions* can
  leave the decided conditions un-split; `simpa [...] using h` is
  robust because both sides get the same normalization.
- `Polynomial.C_ne_zero` is an iff at this pin; `pow_le_pow_left` is
  deprecated for `pow_le_pow_left₀`; `comp_X : p.comp X = p` while
  `X_comp : X.comp p = p` (the band-poly collapse needs the latter).
- `omit [DecidableEq V] in` must precede the docstring, and is
  rejected outright for theorems whose proofs reach `DecidableEq`
  through `mulVec_transpose`/`pow_mulVec_smul` chains (the pow/aeval
  transfers legitimately use it; `dotProduct_mulVec` does not).

## Step 1a record (2026-08-23, run `20260823T215632Z-run-1`)

**DELIVERED** as pure hard crust in the new
`Scaffold/Mathlib/GraphTheory/Krylov.lean` (namespace
`SpectralGraphTheory`, the shelf's `V : Type` interface matched per the
Step-0 finding) plus `Scaffold/QA/SpectralGraph/Krylov_QA.lean`
(a new file, 19 declarations) — zero new axioms (count stays 9), QA
1571 → 1590.

**The module** (every `#print axioms` the standard three, via
`wip/krylov1a_axcheck.lean` on all 8 public theorems + the definition +
all 19 QA):

- the Chebyshev layer, scalar: `abs_T_eval_le_one` (`|T_n(x)| ≤ 1` on
  `[-1,1]`, the spike's proof unchanged), **the first priced gap**
  `natDegree_T` (`(T ℝ (n:ℤ)).natDegree = n` — `Nat.twoStepInduction`
  at `T_add_two`, the degree arithmetic by
  `Polynomial.natDegree_sub_eq_left_of_natDegree_lt` with the
  nonzero-degree ≠ 0 route to `leadingCoeff ≠ 0`; note the pin's
  `twoStepInduction` hands the `n`-case first, `(n+1)` second), and
  **the second priced gap** `one_le_eval_T_of_one_le` (`1 ≤ T_m(x)` at
  `x ≥ 1`), proved through the private conjunction engine
  `eval_T_pair_mono` (`1 ≤ T_n(x) ∧ T_n(x) ≤ T_{n+1}(x)`) by
  *ordinary* induction — the recurrence's step
  `T_{n+2} − T_{n+1} = 2(x−1)T_{n+1} + (T_{n+1} − T_n)` needs nothing
  beyond the two previous conjunction instances, so no two-step
  induction is required;
- the Krylov layer: `sum_mulVec` (the priced pin-gap push, `omit
  [DecidableEq V]`), the real **`krylovSpan M b k`** definition (the
  span of `b, Mb, …, Mᵏ⁻¹b` — the hardening over the spike's inlined
  span expression, so 1b/1c statements read as mathematics), the
  helper `scalar_mul_eq_smul`, `aeval_mulVec_eq_eval_smul` (polynomial
  action on eigenvectors, through `Heat.pow_mulVec_smul`),
  `aeval_mulVec_mem_krylovSpan` (degree-`< k` membership, restated at
  `krylovSpan`), and `kanielPaigeSkeleton` at the spike's exact
  hypothesis form (the five named discharge sites `hp₁`/`horth`/
  `horthM`/`hbottom`/`hband` preserved verbatim — 1b's contract);
- the module docstring carries the survey note (pin gaps closed, the
  `V : Type` finding, the citation-boundary note: the Saad §6 citation
  stays with this proposal, which owns the statement, so no citation
  attaches to the interface pieces).

**QA** (19 declarations): the raw Chebyshev pins (`T₂(0) = −1`
endpoint, `T₃(1/2) = −1` *interior* band-bound equality through the
two-step recurrence, `T₂(1/4) = −7/8` strict, the band instance
composed with the raw value to `7/8 ≤ 1`); `natDegree` instances
(degrees 5 and 0); the growth pair two-route (`1 ≤ T₂(2)` from the
theorem, `T₂(2) = 7` raw — the bound strictly exceeded, so the lemma
is genuine growth); `sum_mulVec` on concrete matrices
(`!![1,2;3,4] ⊕ flipAdj` acting on `![1,-1]`, total `![-2,0]`); the
polynomial action **two routes to one statement** (the transfer
theorem vs. `aeval diagM (X²+1) = diagM²+1 = !![5,0;0,1]` computed by
hand) plus the annihilator witness (`(X − 2)(diagM) *ᵥ e₁ = 0` — the
eigenvalue shifted into the polynomial kills the eigenvector); Krylov
membership **two routes** (theorem at `p = X` vs. generator-direct at
`i = 1`); the **degree-guard refutation** (`¬(e₂ ∈ krylovSpan M e₁ 1)`
— the hypothesis-free form is false: membership in the line `ℝ·e₁`
forces the second coordinate to vanish; `hdeg` is load-bearing); the
**composed-use witness** (`(aeval M (T ℝ 5)) *ᵥ e₁ ∈ krylovSpan M e₁ 6`
with `hdeg` discharged by `natDegree_T 5` alone — Step 1b's exact
consumption pattern); and the **full skeleton instantiation** on
`diagM = diag(2,0)` with `b = ½(e₁+e₂)`, `k = 1`, `p = 1` — all twelve
hypotheses hand-discharged on literals, the bound constant pinned
`(2−0)(1/2)²/(1/2)²/1² = 2`, and the hidden witness's Rayleigh value
pinned raw (`rayleigh diagM b = 1`), so the instantiated bound reads
`2 − 1 = 1 ≤ 2` end-to-end.

**Pin-technique notes (this run's additions, for 1b/1c):**

- **the numeric-default trap's polynomial face**: an un-ascribed
  `C 1` (or bare `X`) in a *goal statement* elaborates the whole
  `aeval` at `ℕ[X]` — `Algebra ℝ (Matrix …)` never gets fixed, `rw`
  against the ℝ-statement fails with display-identical patterns, and
  only `pp.all` (or the `Algebra ?m …` stuck-instance error) exposes
  it. Ascribe `((X ^ 2 + C 1 : ℝ[X]))` in every statement; also
  ascribe smul numerals (`(2 : ℝ) • v` — the bare `2 • v` picks the
  ℕ-smul through `ℝ`'s `AddMonoid` nsmul, which does not unify with
  the ℝ-smul the theorems conclude).
- `Nat.twoStepInduction`'s `more` case receives `P n` (ih1) then
  `P (n+1)` (ih2) — the spike's naming had them reversed and the
  errors surface as "rewrite failed" one step later.
- `Polynomial.leadingCoeff_eq_zero` cannot rewrite a `≠`-goal
  directly (`Ne` is not a negation syntactically): `rw [Ne,
  Polynomial.leadingCoeff_eq_zero]` first.
- `(T ℝ 5)` (OfNat ℤ) and `(T ℝ ((5:ℕ) : ℤ))` (Nat.cast) are *not*
  rw-interchangeable — `natDegree_T`'s conclusion is in cast form, so
  composed-use statements must write the cast form (or `push_cast`
  first); `exact` tolerates the defeq, `rw` does not.
- matrix-literal `mulVec`/matrix-product tails that `norm_num` leaves
  as `vecHead ∘ …` cons-junk are robustly closed by `funext i;
  fin_cases i` + `norm_num [Matrix.mulVec, Matrix.dotProduct,
  Fin.sum_univ_two]`; literal matrix *selection* (`![m₀, m₁] 0`) is a
  `rfl` fact.

## Step 0 record (2026-08-23)

### The exact finite-`k` statement (Lanczos/Kaniel–Paige, top eigenvalue)

Let `M : Matrix V V ℝ` be symmetric with largest eigenvalue `λ₁` and
let `λ₂` bound every other eigenvalue (`λ₂ < λ₁`; equivalently the top
eigenspace is simple — this is a *hypothesis*, with the guard QA'd by
refutation), `λₙ` the smallest eigenvalue. Fix `k ≥ 1` and a starting
vector `b` with unit norm, decomposed along the top eigenvector `u`
(`‖u‖ = 1`) as `b = cos φ • u + sin φ • g`, `g ⊥ u`. Then the `k`-th
Krylov space `K_k(M, b) = span{b, M b, …, Mᵏ⁻¹b}` contains a nonzero
`x` with

```
λ₁ − R_M(x) ≤ (λ₁ − λₙ) · tan²φ / (T_{k−1}(1 + 2γ))²,
  γ = (λ₁ − λ₂) / (λ₂ − λₙ),
```

where `T_{k−1}` is the Chebyshev polynomial and the affine map
`w(λ) = (2λ − λ₂ − λₙ)/(λ₂ − λₙ)` sends the "spectral band"
`[λₙ, λ₂]` to `[−1, 1]` and `λ₁` to `1 + 2γ`. This is the classical
Kaniel–Paige bound (Saad, *Numerical Methods for Large Eigenvalue
Problems*, §6; citation to be verified against the physical copy
before any committed use, per this proposal's clean-room note).

**Statement-shape decisions recorded before Step 1:**

- **Existence form, no sup.** The theorem asserts `∃ x ∈ K_k`; the
  Rayleigh–Ritz *value* `θ_k = sup{R_M(y) : y ∈ K_k}` (what the
  tridiagonal Lanczos recurrence computes in exact arithmetic) is
  equivalent for this bound but drags in a real-number `sSup` over an
  uncountable set for no mathematical gain. The sup/definition form,
  if a consumer needs it, is a one-line corollary of the existence
  form.
- **No Lanczos iteration.** The three-term recurrence, the
  tridiagonal `T_k = Qᵀ M Q`, and finite-precision orthogonality loss
  are all *outside this statement*. What is certified is the exact-
  arithmetic variational content: polynomial images of `b` attain the
  bound. The algorithm-to-quantity correspondence is deliberately not
  claimed.
- **Chebyshev value left explicit.** `T_{k−1}(1+2γ)` stays in the
  statement; the exponential-in-`k` lower bound on it (via
  `cosh(k · arcosh(1+2γ))`) is a non-vacuity corollary, not part of
  the bound.
- **`λ₁`/`λ₂`/`λₙ` enter as hypotheses** (`λ₂`-bounds-every-non-top-
  eigenvalue + strict `λ₂ < λ₁`), not by indexing `evals`; deriving
  them from the sorted spectrum is consumer/QA work. (Naming note:
  `λ₁` is not a lexable Lean identifier — `λ` is reserved; the Lean
  names will differ.)

### Machinery checklist — every dependency verified against pin and shelf

Present on the shelf (all proved, all consumed by the spike):

- the orthonormal eigenbasis `eigvecOf`/`eigvalOf` (`eigvecOf_inner`,
  `eigvecOf_complete`), `quadForm_eigvalOf` (eigenvalue-weighted
  quadratic form), `dotProduct_eigvecOf` (Parseval) — together these
  discharge the skeleton's spectral-layer hypotheses;
- the Rayleigh sandwich both ends: `quadForm_le_evals_last`
  (`xᵀMx ≤ λ_max‖x‖²`) and `evals_first_mul_dotProduct_le_quadForm`
  (`λ_min‖x‖² ≤ xᵀMx`) — the skeleton's `hbottom`;
- `rayleigh` (junk-0 total Rayleigh quotient), and `Heat`'s
  `pow_mulVec_smul` (`(Mⁿ) *ᵥ v = μⁿ • v` at an eigenvector).

Present in the pin:

- `Polynomial.Chebyshev.T` with `T_real_cos`
  (`T_n(cos θ) = cos (n θ)`) — the entire Chebyshev band bound
  `|T_n| ≤ 1` on `[−1,1]` follows from it at `θ = arccos x` with
  `Real.cos_arccos` + `Real.cos_mem_Icc` (**proved in the spike**,
  6 lines);
- the polynomial-action layer: `Algebra ℝ (Matrix V V ℝ)`,
  `Polynomial.aeval_monomial`, `as_sum_range'`, `eval_eq_sum_range`
  — `p(M) v = p(μ) • v` at an eigenvector and `p(M) b ∈ K_k` are
  both **proved in the spike**;
- the `dotProduct`/`mulVec` additive lemmas (`add_dotProduct`,
  `dotProduct_add`, `smul_dotProduct`, `dotProduct_smul`,
  `mulVec_add`, `mulVec_smul`, `smul_mulVec_assoc`,
  `mulVec_mulVec`).

Shallow gaps, all priced (none blocks):

- **no `Matrix.sum_mulVec`** in the pin (the `(∑ Aᵢ) *ᵥ b = ∑ (Aᵢ *ᵥ b)`
  push) — a 4-line `Finset.induction`, **proved in the spike**;
- **no `natDegree (T ℝ n) = n`** lemma found — needs a short induction
  (or `Polynomial.natDegree_comp` bound for the affine-composed band
  polynomial, giving `natDegree < k` for `T_{k−1} ∘ w`); ~15 lines;
- **no cosh-form growth lemma** for `T` beyond `1` — only needed for
  the non-vacuity corollary `1 ≤ T_m(x)` at `x ≥ 1` (two-step
  induction from `T_add_two`); ~25 lines, not on the critical path.

### The skeleton spike (the composition test, hypothesis form)

`wip/asp_step0_spike.lean` (git-ignored, per the Cheeger Step-0
precedent) — **four declarations, all green, every `#print axioms` the
standard three** (`propext, Classical.choice, Quot.sound`):

1. `abs_T_eval_le_one` — the Chebyshev band bound (real proof);
2. `aeval_mulVec_eq_eval_smul` — polynomial action on eigenvectors
   (real proof, consuming `Heat.pow_mulVec_smul`);
3. `aeval_mulVec_mem_krylovSpan` — Krylov-span membership (real
   proof);
4. `kanielPaigeSkeleton` — the full bound assembled in hypothesis
   form: the spectral layer enters as five *named* discharge sites
   (`hp₁ : p.eval λ₁ = Tv`, `horth`, `horthM` — orthogonal-
   complement invariance under `M`, dischargeable via symmetry —
   `hbottom`, `hband`), and the skeleton proves the exact bound
   `λ₁ − R_M(x) ≤ (λ₁−λₙ)·s²/(c²Tv²)` composes from exactly those
   plus pieces 1–3. Getting this green required only the pin-technique
   fixes listed below — no mathematical obstruction surfaced at any
   point, which is the tractability evidence.

### Cost estimate and Step-1 decomposition

~600–800 lines total (module + QA), 2–3 runs:

- **Step 1a — interface layer** (~150–200 lines): the spike's real
  lemmas hardened into a new `Scaffold/Mathlib/GraphTheory/` module
  (Krylov span, polynomial action, `sum_mulVec`, the Chebyshev band
  bound and degree lemmas). Low risk — everything already elaborated
  green in the spike.
- **Step 1b — spectral discharge** (~200–300 lines): the
  eigenbasis-expansion layer (b's decomposition, `horth`/`horthM`
  through `IsSymm`, `hbottom` through the Rayleigh-sandwich mirror,
  `hband` through `quadForm_eigvalOf` + Parseval + `|T ∘ w| ≤ 1` on
  the band). Medium risk — all inputs exist; the work is the
  expansion plumbing, on the pattern of the shelf's own
  `quadForm_eigvalOf` proofs.
- **Step 1c — statement + QA** (~150–250 lines): the theorem at the
  recorded shape, with QA per this proposal's QA plan — positive
  witness on a diagonal 3×3 fixture (diagonal ⇒ `p(M)b` computable
  entrywise both through the theorem and raw; the bound checked
  numerically), the `k = 1` degenerate case (recovers the plain
  Rayleigh gap), the tightness witness `b = u` (`tan φ = 0`, bound
  attained), and the simple-top-eigenvalue guard refuted on a
  `λ₁ = λ₂` fixture (the hypothesis-free form is false).

### Decisions per shape (the Step-0 gate, item 4)

- **Lanczos/Kaniel–Paige: CLEARED** — the only shape Step 1 may
  attempt; the others are dropped from this proposal's *active* scope
  as the proposal itself directs.
- **Nyström: deferred, obstruction named.** The error bound in sample
  size is inherently probabilistic: it needs
  sampling-without-replacement matrix concentration, which neither
  the pin nor the shelf has (the repo's `matrix_bernstein`/
  `matrix_azuma` are the wrong tool class — independent-sum/
  martingale forms, not negative-association sampling bounds); and the
  deterministic core needs `Matrix.pinv`, absent from the pin
  (verified by search), plus column-space machinery the shelf lacks.
  Re-scoping this shape is a *new-proposal* decision once a
  concentration surface and a pseudoinverse exist — not forced here.
- **Chebyshev/polynomial filters: recorded follow-on, not attempted.**
  Its gate ("composes with the not-yet-delivered
  `spectral-band-projectors.md`") has *dissolved* since this proposal
  was written — the band projectors shipped 2026-08-20/21 with the
  two-sided band projector, orthogonality, partition completeness,
  and the Hilbert-projection specialization. The shape would state
  `‖p_d(M) − bandProjector M hM a b‖₂ ≤ ε(d, gaps)` through the
  shelf's proved `l2OpNorm_eq_max_abs_evals`
  (`Analysis/OperatorTheory/Resolvent.lean:296`) — matrix-level
  functional calculus (heavier linear algebra, lighter geometry than
  Kaniel–Paige). It shares this proposal's entire Chebyshev layer, so
  it is the natural *second consumer*; per the proposal's own
  operating instructions (one shape per run), it is not started here.

### Pin-technique findings (recorded for Step 1)

- **The shelf's SGT interface is `V : Type` (Type 0), not `Type*`.**
  Working at `Type*` made `rayleigh` and `Heat.pow_mulVec_smul` both
  fail to apply with postponed-instance stuck elaboration — four
  apparent "elaboration traps" resolved at once by matching the shelf
  at Type 0. Downstream consumers must do the same (or the shelf must
  grow universes — a separate decision).
- `λ₁`/`λₙ` are not lexable identifiers (`λ` is a reserved token) —
  the spike uses `Ltop`/`Lbot`.
- This pin's `pow_succ` factors `a^(n+1) = a^n * a` (use `←
  mulVec_mulVec`, `mulVec_smul`, then `mul_comm` before the closing
  `← pow_succ`); `mul_pow` is `a^m * b^m = (a*b)^m` (forward, not
  reversed).
- `div_le_div_iff` is deprecated → `div_le_div_iff₀`;
  `div_div_eq_mul_div` at this pin is the `a/(b/c)` form — the
  `(a/b)/c = a/(b*c)` identity is a `field_simp` one-liner.
- `Finset.induction`'s `insert` case names exactly 2 binders
  (`| insert ha ih =>`).
- `Finset.sum_comm` at this pin has the dependent
  `∀ i ∈ s, ∀ j ∈ t` signature — bare application sticks an
  `AddCommMonoid` metavariable; a `Finset.induction` on the sum (as in
  the spike's `sum_mulVec`) avoids it entirely.
- `nlinarith` on association-heavy quotient terms times out (200k
  heartbeats) — normalize first with `set` abbreviations (`Q`, `R`,
  `A` in the spike's ending), then the final chain is instant; the
  skeleton carries `set_option maxHeartbeats 800000`.
- `rw [rayleigh]` (equation-lemma rewrite of the def) works on the
  *first* pass only; the robust route is `unfold rayleigh` inside a
  standalone `have` stated in `dotProduct` terms, then rewrite with
  the `have`.

## External consumer

Large-scale spectral clustering, where Lanczos, Chebyshev/polynomial
filters, and Nyström approximation are literally how the exact
eigendecomposition this repository builds on gets replaced at scale in
practice; GNN pooling layers using the same approximations (Saad,
*Numerical Methods for Large Eigenvalue Problems*; Trefethen & Bau for
the polynomial-filter view — **citations unverified**, confirm before
committed use).

## Why this needed a correction from the original triage, not exclusion

`sgt-gaps.md`'s first pass toward this item recommended iceboxing it
rather than writing a proposal, on the grounds that it is fundamentally
about *iterative numerical algorithms and their convergence rates* — a
different kind of formalization than everything else delivered so far
(closed-form identities over finite-dimensional linear algebra). That
diagnosis stands, but exclusion was the wrong response to it: every other
item promoted from `sgt-gaps.md` earned its priority by being scoped, not
by being easy, and this item deserves the same treatment — a mandatory
Step 0 that either finds a tractable finite slice or records precisely
why there isn't one, the same pattern `decidable-spectral-certificates.md`
and this session's other Step-0-gated proposals already use. Recommending
icebox was treating uncertainty as disqualifying; the honest move is to
scope the uncertainty instead.

## The candidate shapes, precisely

Each method needs an error bound relating approximation quality to
iteration count or sample size:

- **Lanczos**: after `k` iterations on a symmetric matrix, the Ritz
  values approximate the extremal eigenvalues with an error bound in
  terms of the spectral gap and `k`.
- **Chebyshev / polynomial filters**: a degree-`d` polynomial
  approximation to a spectral indicator function (e.g., a band
  projector), with an error bound in `d` and the target function's
  smoothness at the polynomial's approximation region.
- **Nyström**: a low-rank approximation to a PSD matrix from a sampled
  subset of rows/columns, with an error bound in sample size.

## Calibration — why "finite-iteration" is the load-bearing scoping choice

The original assessment's own honesty is the key signal: "nothing else
in this list depends on this item." Combined with the different-kind-of-
math diagnosis above, the right target is not general asymptotic
convergence theory (which would need real-analysis machinery on
sequences and limits closer to `icebox/lyapunov-stability-
formalization-gap.md`'s caution about calculus-on-a-parameter than to
anything this repository has built) but a **fixed, finite iteration
count** statement: for a specific `k` (or `d`, or sample size), state and
prove a concrete numerical bound, not a limiting statement as `k → ∞`.
This stays inside Scaffold's existing finite-dimensional idiom — Step 0
below is where this distinction gets tested for real, not assumed.

*Step-0 outcome on this calibration: it held exactly.* The cleared
statement is finite-`k`, quantitative, and closed-form — no limiting
sequence anywhere. The "different kind of math" reduced, on inspection,
to a polynomial-eigenbasis action layer plus scalar Chebyshev facts,
both inside the existing idiom.

## Build order

### Step 0: Scope and survey (mandatory; may find nothing tractable)

**DELIVERED 2026-08-23 — see the Step-0 record above.** Outcome:
Lanczos/Kaniel–Paige cleared (skeleton spike green, axiom-clean);
Nyström deferred with obstruction; Chebyshev filters recorded as the
second consumer.

### Step 1 (only for whichever shape Step 0 finds tractable)

**Authorized for the Lanczos/Kaniel–Paige shape only**, at the
recorded statement shape, decomposed 1a (interface layer) → 1b
(spectral discharge) → 1c (statement + QA) as priced above. Likely
needs its own sub-decomposition across multiple runs — treat as at
least as hard as the electrical program's harder steps were scoped to
be, per this repository's own calibration precedent.

## QA plan

- Positive witness: a small fixture with a known spectrum, the
  approximation computed at a small concrete `k`/`d`/sample size and
  compared numerically against the exact `spectralProjector` (or `evals`)
  output, with the error bound checked to hold.
- Tightness witness, if feasible: a fixture where the bound is close to
  attained, distinguishing a real bound from a vacuously loose one.

*Step-1 instantiation (recorded):* the diagonal 3×3 fixture (diagonal ⇒
`p(M)b` entrywise, two independent routes to one number), the `k = 1`
degenerate case, the `b = u` tightness witness (bound attained at
`tan φ = 0`), and the `λ₁ = λ₂` guard refutation.

## Operating instructions for an autonomous run

- Step 0 is mandatory and may legitimately terminate this proposal
  without any Lean code landing — that is a valid, recorded outcome, not
  a failure. *(Step 0 landed a green spike rather than iceboxing — the
  outcome the scoping found, not a forced one.)*
- **No new axioms.** If Step 0 finds a shape tractable but Step 1 later
  hits missing machinery, stop and record the precise obstruction rather
  than admitting anything.
- Do not attempt more than one of the three candidate shapes in the same
  run, and do not attempt Step 1 on a shape Step 0 did not explicitly
  clear.

## Open next step

**None — the proposal is COMPLETE** (Step 1c delivered 2026-08-24, run
`20260824T012049Z-run-1`; see the Step-1c record above). Recorded
follow-ons that are *not* this proposal's business: the
Chebyshev/polynomial-filter shape (the natural second consumer of the
same Chebyshev layer, per the Step-0 decision — needs its own proposal
or run per the one-shape-per-run rule), the cosh-form non-vacuity
corollary (`T_{k−1}(1+2γ) ≥ cosh((k−1)·arcosh(1+2γ))`, priced off the
critical path in Step 0), and the Rayleigh–Ritz sup form (a one-line
corollary if a consumer names it).
