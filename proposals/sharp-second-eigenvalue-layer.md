# Proposal: The Sharp `|λ₂| = α` Layer

**Status:** COMPLETE — all five slices DELIVERED (Slice 1: run
`20260906T031341Z-run-1`; Slice 2 (a): run `20260906T032852Z-run-1`;
Slice 3 (a): run `20260906T040022Z-run-1`; Slice 4: run
`20260906T090512Z-run-1`; Slice 5: run `20260906T101924Z-run-1`;
plus three follow-ons: the characterization iff, run
`20260906T111951Z-run-1`; the sorted-spectrum forms (the literal
`λ₂` on regular graphs), run `20260906T114513Z-run-1`, session
`ses_f89c8b23effeTZ0dTR5mzKQYrT`; the separating 4-cycle fixture
(the sorted-spectrum follow-on's priced completion), run
`20260906T141850Z-run-1`, session `ses_f88f0e835ffe8QUbO4DxhGFxdB`
— see the follow-on records
below; delivery records below)

## Why this, why now

The sharp layer is the directed-rate program's only remaining item
(`proposals/directed-uniform-mixing-time.md`: "the sharp `|λ₂| = α`
layer (Haveliwala–Kamvar) stays gated"), named the top standing
frontier by every terminal handoff since the audit program closed
(2026-09-06), and the engine join makes its objects engine-native.
The delivery gate ("a named consumer") is discharged by the named
consumer in the handoff chain: the empirical PageRank capstone's rate
statements are the ceiling's consumer surface.

## What the layer is

Haveliwala–Kamvar ("The Second Eigenvalue of the Google Matrix",
Stanford DBPL tech report 2003-20, 2003 — the Stanford tech report
locator already on the `perron_frobenius` record): the Google
matrix's nontrivial spectrum is controlled by the damping coefficient
`α`. The full layer:

1. **The ceiling** (the inequality half, elementary): `|λ| ≤ α` for
   every eigenvalue `λ ≠ 1` of `G(α)`.
2. **The shadow characterization**: the off-one spectrum of `G(α)` is
   exactly `α ×` the mass-zero spectrum of the walk matrix `P`.
3. **The exact-equality layer** (`|λ₂| = α` attained): `G`'s second
   eigenvalue modulus equals `α` iff `P` has a peripheral (`|μ| = 1`)
   mass-zero left-eigenvalue — the periodic case; on aperiodic chains
   the inequality is strict.
4. **The rate connection**: composing the ceiling with the power
   method's convergence statements.

The gated remainder as previously recorded ("needs the complex
spectral theory of non-symmetric matrices") is required only by the
*eigenvalue-level* statements (3–4's full form); the eigenvector-level
statements need none of it.

## Slice 1 (this run): the ceiling at the vecMul level

All statements at the left-eigenvector (`vecMul`) level — the shelf's
own stationarity convention — so no eigen-API is needed:

- **The mass lemma**: `μ ᵥ* G = λ • μ` with `λ ≠ 1` forces
  `∑ μ = 0` (row-stochastic mass bookkeeping: the total mass is
  invariant under the left action, so `(λ − 1)·∑μ = 0`).
- **The shadow lemma**: with zero mass, the teleportation term of the
  entry form vanishes from the left action and
  `μ ᵥ* P = (λ/α) • μ` — G's off-one left-eigenvectors ARE P's
  mass-zero left-eigenvectors, with eigenvalues scaled by `1/α`.
- **The ℓ¹ peripheral bound**: a nonzero left eigenvector of a
  nonnegative row-stochastic matrix has `|λ'| ≤ 1` (the left action
  contracts the absolute sum).
- **The ceiling**: `|λ| = α·|λ/α| ≤ α` — Haveliwala–Kamvar's
  inequality half, at full generality (any `WAdj`, `0 < α ≤ 1`).
- **The attainment twin**: conversely a mass-zero P-left-eigenpair at
  `λ'` is a G-left-eigenpair at `α·λ'` — the layer's equality half at
  the eigenvector level, and the object the periodic-fixture QA pins
  (`μ = (1,−1)` at the 2-cycle: the `−α`-eigenpair, the ceiling
  attained).

Later slices (each its own run): the eigenvalue-level forms through
Mathlib's `Module.End` eigen-API, the strictness layer on aperiodic
chains, and the rate connection.

## QA obligation

Pins in `PageRank_QA.lean` at a fresh 2-cycle fixture: the raw
eigenvector equation `μ ᵥ* G = −α • μ` (the ceiling attained, mass
zero), and the end-mix `λ₂ = 0` case (the `J/n` walk's shadow at
`μ' = 0`).

## Delivery record — Slice 1 (2026-09-06)

DELIVERED at the full slice scope: five public theorems in
`PageRank.lean`'s new `SpectralCeiling` section (functional 1313 →
1318) and seven QA pins in `PageRank_QA.lean`'s new
`SpectralCeilingQA` section (QA 6387 → 6395), zero axiom contact
(`#print axioms` via `wip/sharp_axcheck.lean` on all 13 — every one
exactly `propext, Classical.choice, Quot.sound`); the shelf module
and its QA consumer elaborate with zero errors/warnings.

The five theorems: the mass lemma; the shadow lemma; the ℓ¹
peripheral bound (`abs_vecMulEigen_le_one`, stated for any
nonnegative row-stochastic matrix — reusable beyond the Google
family); the ceiling `googleMatrix_abs_eigen_le` (Haveliwala–Kamvar's
inequality half, `|c| ≤ α` at full generality); the attainment twin
`googleMatrix_vecMul_of_shadow`.

The QA pins at the fresh two-cycle fixture `prCyc` with the
alternating vector `prAlt = (1,-1)`: the `-1` shadow pair (raw), the
twin's image (the Google left-eigenpair at `α·(-1)`), the raw
instantiation at `α = 4/5` (`-4/5`-eigenpair), the ceiling instance
(load-bearing on the real `googleMatrix` definition — a mis-signed
teleport weight would break the mass collapse), and the end-mix
shadow at `K₂` (the `0`-pair, the strict side of the ceiling).

Technique findings:

1. **The mass mechanism needs the LEFT action**: right eigenvectors
   of a row-stochastic matrix carry no mass constraint (the
   bookkeeping sums columns); the shelf's vecMul convention is the
   one where `(c−1)·∑μ = 0` falls out.
2. **The ℓ¹ bound, not the ℓ∞ bound**: the left action of a
   row-stochastic matrix contracts the absolute SUM (row sums), not
   the max — the peripheral bound is one `Finset.sum_comm` away.
3. **`omit ... in` precedes the docstring** — the docstring is part
   of the declaration the omit modifies.

Later slices (unchanged): the eigenvalue-level forms, the strictness
layer, the rate connection.


## Delivery record — Slice 2 (a): the rate connection, the Dobrushin
shadow (2026-09-06)

DELIVERED at the adjusted slice scope: six public theorems in
`DirectedMixing.lean`'s new `DobrushinShadow` section (functional
1318 → 1324) and five QA pins in `DirectedMixing_QA.lean`'s new
`DobrushinShadowQA` section (QA 6395 → 6400), zero axiom contact
(`#print axioms` via `wip/dobrushin_axcheck.lean` on all 11 — every
one exactly the standard three).

The theorems: the pointwise Dobrushin shadow
(`tvDistance_googleMatrix_row_eq` — EXACT, entrywise: the
teleportation's uniform shift cancels in every row-pair difference,
so `TV(G_x, G_y) = α·TV(P_x, P_y)`); the shadow ceiling
(`tvDobrushinCoeff_googleMatrix_le`, the ≤-form); the walk Dobrushin
ceiling (`tvDobrushinCoeff_walkTransitionMatrix_le_one`); the `t = 1`
rate bound (`pageRankTVPair_one_le`); **the pair rate**
(`pageRankTVPair_le_pow : pageRankTVPair A α t ≤ (α·δ(P))^t` — the
existing Doeblin-floor `α^t` rate recovered through the engine at the
sharper constant); and the `α^t` corollary
(`pageRankTVPair_le_pow_alpha`).

The QA pins at the two-cycle fixture: `δ(P) = 1` pinned (swapped rows
are point masses — the walk Dobrushin ceiling attained), the `t = 1`
rate bound instantiated at `α = 4/5` THROUGH the pinned coefficient
(the bound IS `α` there), and the `α^t` corollary at `t = 2`.

**Scope adjustment, honestly recorded:** the exact shadow EQUALITY
`δ(G) = α·δ(P)` was designed first (the pointwise shadow is exact)
but its sup'-scaling step `sup'(α·f) = α·sup' f` needs sup'-attainment
(`le_sup'_iff` lives in a LinearOrder-index section; `Finset.univ` on
`V × V` has no LinearOrder without extra structure) — the ≤-form
carries every consumer of this slice, and the equality is priced as
a follow-up (routes: a `Fintype.card`-indexed attainment argument, or
`Finset.sup'_induction`).

Technique findings:

1. **The sup'-scaling/attainment gap**: `sup'(α·f) = α·sup' f` is
   unprovable from `sup'_le`/`le_sup'` alone — attainment needs the
   LinearOrder-indexed `le_sup'_iff` or an induction principle; the
   ≤-direction (`sup'_le` + pointwise) suffices for every ceiling
   consumer.
2. **`Finset.sup'_le`'s elaborator needs the `f`-binder's domain
   type explicit** (`fun p : V × V => …`), or whnf storms on the
   noncomputable matrix entries time out.
3. **Row-entry pins beat whole-matrix norm_num**: computing
   `walkTransitionMatrix dmxCyc 0 = ![0,1]` per-entry (fin_cases ×2)
   then the TV closed form is instant; the direct whole-matrix
   `norm_num` times out.

Slice 3 candidates (updated): the exact shadow equality (the
attainment route); the eigenvalue-level forms; the strictness layer.


## Delivery record — Slice 3 (a): the exact shadow equality (2026-09-06)

DELIVERED, closing Slice 2 (a)'s priced follow-up: three public
theorems in `DirectedMixing.lean`'s `DobrushinShadow` section
(functional 1324 → 1327) and one QA pin (QA 6400 → 6401), zero axiom
contact (`#print axioms` via `wip/exactshadow_axcheck.lean` — every
one exactly the standard three).

The route that closed the attainment gap:
`Finset.sup'_induction` with the `⊔`-closed induction property
`p z := α·z ≤ sup'(α·f)` — closure by the `max`-case
`mul`-monotonicity (`α·(x ⊔ y) = α·x ⊔ α·y` at `α ≥ 0`, proved by
`le_total` case analysis since ℝ is not unconditionally
`MulLeftMono`). **No LinearOrder on the index type is needed** —
the gap recorded in Slice 2 (a) was an artifact of reaching for
`le_sup'_iff` (which does need it), not a real obstruction.

The theorems: `scaleSupUnivEq` (the reusable sup'-scaling step);
`tvDobrushinCoeff_googleMatrix` (the EXACT Dobrushin shadow — the
pointwise shadow was exact all along, so the ≤-form upgrades);
`pageRankTVPair_one_eq` (the exact `t = 1` identity). QA:
`dmxCyc_one_eq_QA` — the identity pinned at the two-cycle through
the delivered `δ(P) = 1`: `pageRankTVPair dmxCyc (4/5) 1 = 4/5`.

Technique findings:

1. **`Finset.sup'_le _` with a metavariable `H` poisons the entire
   statement's elaboration** — the `SemilatticeSup ?m`-stuck error is
   reported at the STATEMENT, not the tactic; always pass the
   Nonempty witness explicitly.
2. **The `sup_eq_max` + `rw [max_eq_right h]` chain leaves a
   syntactical-form warning** in this Mathlib; the robust shape is
   `le_antisymm`-built sup-identities or `sup_le`.
3. **ℝ is not `MulLeftMono`**: `mul_sup` is unconditional only in
   ordered groups with monotone-left-multiplication; for ℝ the
   nonneg case analysis is unavoidable (three lines).

Remaining slices: the eigenvalue-level forms through Mathlib's
`Module.End` eigen-API; the strictness layer on aperiodic chains.


## Delivery record — Slice 4: the eigenvalue-level forms (2026-09-06)

DELIVERED: four public theorems in `PageRank.lean`'s
`SpectralCeiling` section (functional 1327 → 1331) and four QA pins
in `PageRank_QA.lean`'s `SpectralCeilingQA` section (QA 6401 → 6405),
zero axiom contact (`#print axioms` via `wip/eigen_axcheck.lean` —
every one exactly the standard three).

**The bridge is definitional**: `Matrix.vecMulLinear_apply :
M.vecMulLinear x = x ᵥ* M := rfl` — Slice 1's vecMul-level machinery
transfers to `Module.End.HasEigenvector`/`HasEigenvalue` with no new
mathematics; the spike was green in two rounds.

The theorems: `googleMatrix_hasEigenvector_abs_le` (the eigenvector
ceiling — the nonzero hypothesis Slice 1 carried is now supplied by
`HasEigenvector` itself); `googleMatrix_hasEigenvalue_abs_le` (the
eigenvalue ceiling via `exists_hasEigenvector` — directly consumable
by Mathlib spectral machinery: `HasEigenvalue.mem_spectrum` is one
application away); `googleMatrix_hasEigenvector_shadow` (a
G-eigenvector at `c ≠ 1` IS a P-eigenvector at `c/α`); and
`googleMatrix_hasEigenvector_of_shadow` (the attainment twin).

The QA pins: the `-α` pair at the two-cycle lifted to genuine
`HasEigenvector` and `HasEigenvalue` through the bridge, the ceiling
instantiated, and the eigen-level shadow pinned (the
`-4/5`-eigenvector of G is the `-1`-eigenvector of P).

Scope notes:

1. **The left-eigenvector convention**: the eigen-level forms are at
   `vecMulLinear` — the shelf's own stationarity convention, where
   Slice 1's machinery lives. Right-eigenvector forms (`mulVecLin`,
   `G *ᵥ v = c • v`) need either the doubly-stochastic case (where
   the mass lemma transfers) or the charpoly-invariance route
   (`Matrix.charpoly_transpose`) — priced as a follow-up.
2. **The strictness layer** (aperiodic chains, `|λ₂| < α` strictly)
   remains the proposal's last slice.

Technique finding: dot-notation `f.HasEigenvector` fails on
`vecMulLinear` (elaborated as a `LinearMap`, not `Module.End`, and
the abbrev lives in `Module.End` — full qualification or an explicit
type ascription is needed).

## Delivery record — Slice 5: the strictness layer (2026-09-06)

DELIVERED, closing the proposal COMPLETE: five public theorems in
`PageRank.lean`'s new `Strictness` section (functional 1331 → 1336)
and 15 QA theorems plus one fixture in `PageRank_QA.lean`'s new
`StrictnessQA` section (QA 6405 → 6420), zero axiom contact
(`#print axioms` via `wip/strict_axcheck.lean` on all 20 — every one
exactly `propext, Classical.choice, Quot.sound`).

**The route is the peripheral argument, elementary over ℝ — by
design, Perron–Frobenius is NOT consumed** (the gated remainder's
"needs the complex spectral theory of non-symmetric matrices" was
already known to apply only to the eigenvalue-level statements, and
Slice 4's bridge removed even that; the strictness needed neither):

1. `vecMul_pow_smul_eq` — the power-eigenpair engine: a
   left-eigenvector of `M` is a left-eigenvector of every power, at
   the powered eigenvalue (induction through
   `Matrix.vecMul_vecMul`/`Matrix.vecMul_smul`).
2. `vecMul_sign_coherent_of_abs_eq_pow_pos` — the peripheral
   sign-rigidity engine: on a row-stochastic matrix with a strictly
   positive power `M^k`, a peripheral (`|c| = 1`) left-eigenvector has
   all entries weakly of one sign. Mechanism: the ℓ¹ chain
   `∑|μ| = ∑|μ ᵥ* M^k| ≤ ∑|μ|` is tight, so equality holds in the
   triangle inequality at every column; at any one column the
   strictly positive weights force all `μ i` weakly of one sign
   (the two-case extraction: `∑(|μ i| − μ i)·w i = 0` or
   `∑(|μ i| + μ i)·w i = 0`, each summand nonneg, weights `> 0`).
3. `googleMatrix_abs_eigen_lt_of_primitive` — the strictness
   theorem: mass zero (Slice 1's mass lemma) + sign coherence
   forces `μ = 0`, contradicting eigenvectorhood; so `|c/α| = 1` is
   impossible, and the ceiling `|c| ≤ α` upgrades to `|c| < α`.
   Stated at both the `IsPrimitive` form (importing
   `LinearAlgebra.PrimitiveConvergence` — the new import edge,
   cycle-free: that shelf imports only `PerronFrobenius` + Mathlib)
   and the raw `_of_pow_pos` form.
4. `googleMatrix_hasEigenvalue_abs_lt_of_primitive` — the eigen-level
   twin (Slice 4's `exists_hasEigenvector` bridge).

QA: the fresh primitive two-vertex fixture `prPrim = !![1,1;1,0]]`
(self-loop + arc): `P = [[1/2,1/2],[1,0]]` pinned entrywise, `P²`
strictly positive pinned entrywise (`IsPrimitive` witnessed at
`k = 2`), the alternating vector's `-1/2` walk eigenpair, the Google
eigenpair at `-α/2` through the delivered attainment twin
(`googleMatrix_vecMul_of_shadow` — Slice 1's theorem consumed
load-bearing), strictness instantiated at both levels
(`|−2/5| < 4/5`, the eigen-level pin joining Slice 4's bridge to
Slice 5), and the necessity fence `prCyc_not_primitive`: the
two-cycle — where Slice 1 pinned the ceiling ATTAINED at `|−α| = α` —
provably fails primitivity (powers alternate identity/swap, the
even/odd characterization by `pow_mul`/`pow_add` induction),
exhibiting primitivity as exactly what strictness needs.

Technique findings:

1. **`Finset.sum_sub_distrib`'s direction is `∑(f − g) = ∑f − ∑g`**
   (the `to_additive` twin of `sum_div`) — and its RHS carries the
   lemma's own binder names, so downstream `rw`s can miss
   alpha-equivalent spellings; the robust pattern is to state the
   split `have` in your own binders and rewrite through that.
2. **rw-produced alpha-equivalent sums do not close by `rfl` in this
   context** — an explicit `sub_self` needs syntactic identity; route
   through a single `hsum : A = B` stated in your own spellings and
   rewrite both facts through it.
3. **The QA-elaboration stale-olen trap, general form**: a QA file
   referencing new shelf declarations fails with "unknown
   identifier" until the shelf module's olean is rebuilt
   (`lake build <shelf-module>` before `lake env lean <qa-file>`);
   the same symptom appears for fixture names when a spike section
   replicates only some of the landed QA's declarations.
4. `pow_mul` must be applied FORWARD (`P^(2*m)` → `(P^2)^m`); the
   `←` direction has no `(a^m)^n` pattern to find.

## Delivery record — the characterization iff follow-on (2026-09-06)

DELIVERED (run `20260906T111951Z-run-1`, session
`ses_f89c8b23effeTZ0dTR5mzKQYrT`): the layer's item 3 — the
exact-equality characterization — composed from its two delivered
halves (the "composed iff not stated as one theorem" honest-scope
note in the Slice 5 and right-eigenvector records), two public
theorems (functional 1348 → 1350) and four QA pins (QA
6441 → 6445), zero axiom contact (`#print axioms` via
`wip/iff_axcheck.lean` on all 6 — every one exactly
`propext, Classical.choice, Quot.sound`).

- **`googleMatrix_abs_eigen_eq_alpha_iff`** (the `Strictness`
  section): the Google matrix has an off-one left-eigenvalue AT
  modulus `α` iff the walk has a mass-zero peripheral (`|c'| = 1`)
  left-eigenpair at the shadow eigenvalue `c/α`. The ⇒ direction
  composes the mass lemma + the shadow lemma + the peripheral
  arithmetic; the ⇐ is the attainment twin with
  `α · (c/α) = c`. Equality is exactly the periodic-chain
  phenomenon.
- **`googleMatrix_mulVec_abs_eigen_eq_alpha_iff`** (the
  `RightEigenvalue` section): the doubly-stochastic right twin,
  composing the three transports.

QA: both directions instantiated at the two-cycle (the peripheral
`-1` pair ⟹ the attained `-α` Google pair; the pinned raw Google
pair ⟹ a mass-zero peripheral walk pair), the right twin
instantiated, and the negative witness at the primitive fixture —
`prPrim_no_peripheral_QA`: no mass-zero peripheral walk pair exists
there (the mass-zero line is spanned by the alternating vector, on
which the walk acts at `-1/2`) — strictness's contrapositive content
at the eigenpair level.

Technique findings:

1. **An iff over a fixed `c` keeps the `c/α` spelling
   un-normalized in instantiations** — state the instantiation at
   `(-4/5)/(4/5)` and convert witnesses with
   `rw [pair]; congr 1; norm_num`, not by restating the pair.
2. `nlinarith` closes the mass-zero-line eigenvalue pin
   (`ν 0 * (c' + 1/2) = 0` from the raw coordinate equation), and
   `abs_of_neg` finishes the `|-1/2| = 1` kill where `norm_num`
   alone stalls at `|1/2| = 1`.

With this delivery the layer's "What the layer is" list is fully
stated: the ceiling (item 1), the shadow characterization (item 2),
the exact-equality iff (item 3), and the rate connection (item 4) —
plus the strictness layer, the right convention, and the
doubly-stochastic twin.

## Delivery record — the sorted-spectrum follow-on: the literal `λ₂`
(2026-09-06)

DELIVERED (run `20260906T114513Z-run-1`, session
`ses_f89c8b23effeTZ0dTR5mzKQYrT`): nine public theorems in
`PageRank.lean`'s new `SortedSpectrum` section (functional
1350 → 1359) and seven QA theorems in `PageRank_QA.lean`'s new
`SortedSpectrumQA` section (QA 6467 → 6474), zero axiom contact
(`#print axioms` on all 16 — every one exactly `propext,
Classical.choice, Quot.sound`).

The layer is NAMED `|λ₂| ≤ α` but its statements were eigenpair
level; on regular input (symmetric `A`, equal degrees) the Google
matrix is symmetric, so the shelf's `evals`/`eigvalOf` machinery
applies and the ceiling becomes statements about spectrum objects:

1. `googleMatrix_isSymm_of_regular`, `googleMatrix_entry_pos` (the
   teleportation floor), `googleMatrix_mulVec_ones` — the setup.
2. **The `1`-eigenspace simplicity**
   `one_eigenspace_eq_smul_of_pos_isSymm` (the new mathematics, for
   any strictly positive symmetric row-stochastic matrix): the
   sign-rigidity engine gives a weak sign; the nonneg branch earns
   strict positivity entrywise (`pos_of_mulVec_eq_smul_of_nonneg`,
   one positive coordinate times strict positivity of the matrix);
   the min-ratio argument (a `Finset.image`-min over the ratios)
   then forces proportionality — no Perron–Frobenius.
3. `googleMatrix_eigvalOf_cases` (every eigenbasis eigenvalue is
   `1` or under the ceiling — the right-ceiling composed with the
   eigenbasis eigenpair).
4. **`googleMatrix_evals_top_eq_one`**: the top is exactly `1`
   (all `≤ 1` through the cases + the count engine; `≥ 1` through
   the constant vector and `exists_eigvalOf_eq_of_mulVec_eq_smul`).
5. **`googleMatrix_evals_second_le`**: `evals ⟨n−2⟩ ≤ α` — at most
   one eigenbasis index exceeds `α`, namely the simple top, by
   simplicity plus `eigvecOf_inner` orthogonality (a proportional
   pair of orthonormal eigenvectors is impossible), through the
   sdiff-partition count.
6. **`googleMatrix_evals_bot_ge`**: `-α ≤ evals ⟨0⟩` (the cases +
   `evals_mem_eigvalOf`).

QA at the two-cycle (2-regular symmetric): the `G(4/5)` symmetry
pinned, `evals ⟨1⟩ = 1` pinned, **the bottom `evals ⟨0⟩ = -4/5 = -α`
ATTAINED** through `evals_sum_eq_trace` and the pinned top, the
second-from-top instance, and the trace pin.

Technique findings:

1. **Statement-level `by omega` index proofs fail without
   cardinality facts**: `⟨k, by omega⟩` inside a theorem statement
   cannot see `Nonempty V`; supply `Fintype.card_pos` /
   `norm_num [Fintype.card_fin]` as the proof term.
2. **The dependent-domain rewrite block**: `rw [Fintype.card_fin]`
   inside `∑ i : Fin (Fintype.card V)` fails the motive check;
   bridge through a type-ascribed `have h' : ∑ i : Fin 2, ... := h`
   (defeq) and rewrite there.
3. **linarith's atoms are proof-term-sensitive**: `evals hG ⟨0, p₁⟩`
   and `evals hG ⟨0, p₂⟩` are different atoms (though defeq by
   proof irrelevance); normalize index spellings across hypotheses
   before `linarith`.
4. `Matrix.IsSymm`'s interface: `Matrix.IsSymm.ext` (pointwise
   proof), `hsymm.apply` (pointwise use), `hsymm.eq : Mᵀ = M`
   (matrix equality — the direction is transpose-first).

Priced follow-up: a `≥ 3`-vertex regular fixture (the 4-cycle
separates the second-from-top from the bottom) to pin the two bounds
at distinct indices. — DELIVERED as the fourth follow-on (see the
record below). Correction recorded at that delivery: this note's
parenthetical claim that "the triangle's Google matrix is
`α`-independent (`J/3`)" is wrong — `trace G(α) = 1 − α ≠ 1 =
trace (J/3)` — moot for the pricing (the 4-cycle carries it), but the
triangle does not have the claimed spectrum (its actual eigenvalues
are `1, −α/2, −α/2`, which like `n = 2` does not separate).

## Delivery record — the separating regular fixture: the 4-cycle
pins (2026-09-06)

DELIVERED (run `20260906T141850Z-run-1`, session
`ses_f88f0e835ffe8QUbO4DxhGFxdB`): the priced follow-up above —
39 QA theorems + 6 fixture `def`s in `PageRank_QA.lean`'s
`SortedSpectrumQA` section (QA 6474 → 6513), QA-only, zero axiom
contact (`#print axioms` via `wip/c4_axcheck.lean` on all 39 new
nameable theorems — every one exactly `propext, Classical.choice,
Quot.sound`).

The 4-cycle (`prC4` on `Fin 4`, 2-regular symmetric) is the smallest
regular graph whose Google matrix separates the second-from-top index
from the bottom: `G(4/5) = (2/5)·A + (1/20)·J` (entries `9/20`/`1/20`,
pinned as a concrete matrix through `prC4G_eq`), trace `1/5`, spectrum
ascending `{-4/5, 0, 0, 1}` with eigenvectors `![1,-1,1,-1]` at
`-4/5` and `![1,0,-1,0]`, `![0,1,0,-1]` at `0` (all three pairs
pinned entrywise from the concrete matrix).

The exact middle pins are the subspace Rayleigh–Ritz engine's
(`evals_le_of_linearIndependent`) first exercise on the PageRank
family:

- `evals ⟨1⟩ ≤ 0` at `k = 2`: the family `{e₀−e₂, e₁−e₃}` spans a
  subspace on which `G` acts as the ZERO map (both modes are `0`-
  eigenvectors), so the quadratic form vanishes identically.
- `evals ⟨2⟩ ≤ 0` at `k = 3`: adding the alternating mode,
  `quadForm G x = −(16/5)·c₂² ≤ 0` (the combination's action is
  `−(4/5)·c₂ •` alternating, and `x ⬝ᵥ alt = 4·c₂`).
- Both linear-independence proofs run through the numeric pairwise
  dot pins (the mode family's Gram matrix `diag(2, 2, 4)`, all
  off-diagonal `0`) — dot-both-sides of the zero combination.

On the extremes, the pins are load-bearing on BOTH the delivered
theorems and the fixture: `evals ⟨3⟩ = 1` (the delivered top
theorem), `evals ⟨0⟩ = −4/5 = −α` ATTAINED (the delivered bottom
theorem from below; the exhibited `−α` eigenpair through
`exists_eigvalOf_eq_of_mulVec_eq_smul` + `evals_first_le_eigvalOf`
from above). The exact middle values `evals ⟨1⟩ = evals ⟨2⟩ = 0` then
fall from the trace engine (`evals_sum_eq_trace` at the pinned
`1/5`) plus both family bounds. The separating content is stated
explicitly: `prC4G_second_ne_bot_QA` (`0 ≠ −4/5` — distinct values at
distinct sorted indices) and `prC4G_second_strict_QA`
(`|λ₂| = |0| < 4/5` STRICTLY inside the α-disk while the bottom
attains `|−α| = α` — both bounds of the family name instantiated at
distinct indices, the thing the `n = 2` coincident fixture could not
witness).

Technique findings:

1. **`rw` rewrites only same-metavariable instances**: a lemma whose
   LHS has term metavariables (`mulVec_smul`, `dotProduct_smul`,
   `smul_eq_mul`) fires once per DISTINCT parameter assignment —
   repeat it per instance in the list, or use `simp only [...]`
   (fixpoint retry). This is the mechanism behind several earlier
   runs' "pattern not found" failures after a partial rewrite.
2. **`fin_cases` on the `Fintype.linearIndependent_iff` binder leaves
   an eta-expanded index** (`(fun i => i) ⟨0, ⋯⟩`) that blocks
   rewriting inside hypotheses — take the literal-index congruences
   (the coordinate/dot equations at `0`, `1`, …) BEFORE the case
   split, and discharge the case goals by `exact` (defeq-tolerant),
   not `rw`/`linarith` on the goal.
3. **Symbolic goals need `rfl`-access lemmas, numeric goals
   `norm_num`**: matrix-literal indexing `![..] i` with symbolic
   coefficients survives `norm_num` (it can't ring-cancel) and blocks
   `ring` (atoms) — the robust split is numeric pairwise pins by
   `norm_num` (fully numeric) plus `rfl` family/entry access lemmas
   plus dot-linearity (`dotProduct_add`/`dotProduct_smul`/
   `smul_dotProduct` — note `dotProduct_smul`'s result is `•`, not
   `*`; `smul_eq_mul` still needed, and it too has the per-instance
   rewrite behavior).
4. `quadForm`/`dotProduct` are `rfl`-unfoldable to `∑ j, x j * (M *ᵥ
   x) j`-shaped sums, but rewriting under them at `Fin (Fintype.card
   V)` needs the type-ascribed `have` bridge (the sorted delivery's
   finding #2, re-encountered at `prC4G_sum`).
