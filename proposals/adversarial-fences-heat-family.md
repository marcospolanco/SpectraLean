# The Heat Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-05 by run `20260905T024254Z-run-1`,
session `ses_f909884d5ffeYcyOG4VIwyJJh3`; see the delivery record).

## Scope

The prior terminal handoff's standing survey numbers, re-run and
confirmed by this run's own independent reverse-import walk: **Heat is
the library's most-consumed unaudited shelf at 8 transitive non-QA
consumers** (`FunctionalCalculus`, `Krylov`, `Mixing`, `Oversmoothing`,
and `PolyFilter` directly; the closure adds `DirectedMixing`,
`BandDavisKahan`, and the `EmpiricalStationary` capstone) — ahead of
RandomWalk 5, Stationary 4, IrreducibleStationary 3, and Directed 3,
none previously surveyed. The shelf is
`Scaffold/Mathlib/GraphTheory/Heat.lean`: the general matrix-exponential
engines (square-zero collapse, eigenmode engine, kernel-vector engine,
scalar-matrix exponential, rank-one-idempotent collapse), the heat
semigroup proper (`heatKernel` and its symmetry/identity/semigroup/
conservation layer), eigenmode decay and the DC limit, the Phase C
derivative and first-order remainder bound, both variance-decay twins
(`heatKernel_variance_decay`, `walkHeatKernel_variance_decay`), and the
normalized/walk heat layer (`normalizedHeatKernel`, `walkHeatKernel`,
the `√D` conjugation, the π-isometry pair). All proved hard crust —
no axioms in this shelf.

Its QA (`Heat_QA.lean`, 1385 lines, delivered 2026-08-23 and
2026-08-31) predates the adversarial-review discipline: four scattered
negative witnesses exist (`heatKernel_asym_not_isSymm_QA`,
`heatKernel_asym_not_fix_nonkernel_QA`,
`heatKernel_edge_remainder_window_fenced_QA` — a hypothesis-falsity
witness, not a dropped-statement fence — and
`heat_variance_edge_wrong_constant_refuted_QA`, a constant refutation),
but **zero fence sections**: no hypothesis-necessity pass has covered
the shelf's clause surface.

Method: `governance/ADVERSARIAL_REVIEW.md`'s hypothesis-necessity pass
(seventeen precedents: TV/Dobrushin, lazy, entropy, Poisson-bridge,
primitivity-supplier (+ consumer follow-on), irregular Cheeger, regular
Cheeger, effective-resistance, electrical-flow, Foster,
sparsification-core, band-projector, Davis–Kahan core, normalized,
variational-transfer, resolvent, and Perron–Frobenius) — re-read every
declaration's hypothesis clauses, identify those with no negative
witness, and close each with a hypothesis-form fence (the
dropped-hypothesis statement refuted at a fixture where every kept
hypothesis is genuine, certified by pinned-value/isolation companions),
or record a non-fenceable with its mechanism.

Consumer case (the leverage): the heat shelf is the continuous-time
diffusion engine of the mixing program — every `e^{-tL}`-shaped
statement anywhere in the library (the mixing layer's continuous-time
χ² work, the oversmoothing ceilings' continuous analogues, Krylov and
PolyFilter's semigroup inputs, the derived-layer capstones) routes
through these declarations. The clause surface here is unusually rich
in *sign* and *degree* hypotheses (`hnn`, `hd`, `hnonneg`, `ht`) whose
dropped forms have never had negative witnesses; the audit closes them.

## Step-0 findings: the priced fence list

Clause census over the shelf's public surface, by family. Screened
(delivered witnesses already fence the clause): `heatKernel_isSymm`'s
`hA` (`heatKernel_asym_not_isSymm_QA`); `exp_mulVec_eq_of_mulVec_eq_zero`'s
`hM` class already has the engine-level witness
`heatKernel_asym_not_fix_nonkernel_QA` — but the sibling engines'
`hM` clauses do not, and are priced below.

### α — general exponential engines (the `hM : M *ᵥ v = μ • v` /
`M * M = 0`-shaped clauses)

1. `exp_eq_one_add_of_mul_self_eq_zero`'s `hM : M * M = 0`, at
   `M = (1 : Matrix (Fin 2) (Fin 2) ℝ)`: `exp 1 = e • 1 ≠ 1 + 1`
   through `matrix_exp_smul_one` and the pin `9/4 ≤ e` (two
   applications of `add_one_le_exp` at `1/2`). First negative witness
   for the clause anywhere.
2. `exp_neg_smul_eq_one_add_of_mul_self_eq_zero`'s `hM`, at the same
   `M`, `t = 1`: `e⁻¹ • 1 ≠ 1 − 1 = 0` (`Real.exp_pos`).
3. `pow_mulVec_smul`'s `hM : M *ᵥ v = μ • v`, at the zero matrix,
   `v = ![1, 0]`, `μ = 1`, `n = 1`: `0 ≠ ![1, 0]`.
4. `exp_mulVec_eq_smul_of_mulVec_eq_smul`'s `hM`, at the zero matrix,
   `v = ![1, 0]`, `μ = 1`: `exp 0 *ᵥ v = v ≠ e • v` (`9/4 ≤ e`).
5. `exp_mulVec_eq_of_mulVec_eq_zero`'s `hM`, at `M = 1`, `v = ![1, 0]`
   (`M *ᵥ v = v ≠ 0` genuinely fails): `(e • 1) *ᵥ v = e • v ≠ v`.
6. `tendsto_exp_neg_mul_atTop`'s `hμ : 0 < μ`, at `μ = 0`: the flow is
   the constant `1` and does not tend to `0` (eventually-below-`1/2`
   argument against `exp (-(t · 0)) = 1`).

### β — the rank-one-idempotent collapse

7. `exp_eq_one_add_of_mul_self_eq_smul`'s `hc : c ≠ 0`, at `c = 0` with
   the genuinely-satisfiable `hM` (`M * M = 0 • M` at the new nilpotent
   fixture `hfNz = !![0, 1; 0, 0]]`): the dropped statement's
   coefficient `(e⁰ − 1)/0` is *junk zero* (`0/0 = 0`), collapsing the
   claim to `exp M = 1`, refuted by the square-zero collapse
   `exp M = 1 + M ≠ 1` (`hfNz ≠ 0`). The junk-division corner class.
8. Same theorem's `hM : M * M = c • M`, at the same fixture with
   `c = 1` (`hc` genuine, `hM` genuinely fails since `hfNz² = 0 ≠ hfNz`):
   the dropped statement reads `1 + hfNz = 1 + (e − 1) • hfNz`, i.e.
   `e = 2` entrywise — refuted by `9/4 ≤ e`.

### γ — decay-factor monotonicity and dissipation (K₂ fixtures, the
delivered `edgeLaplacian_evals_QA` pin `[0, 2]` read directly)

9. `heatKernel_decayFactor_antitone`'s `ht : 0 ≤ t`, at `t = -1`,
   `i = ⟨0⟩ ≤ j = ⟨1⟩`: the claim `e² ≤ e⁰ = 1` is false
   (`Real.one_lt_exp_iff`).
10. Same theorem's `hij : i ≤ j`, at `i = ⟨1⟩`, `j = ⟨0⟩`, `t = 1`:
    `e⁰ = 1 ≤ e⁻²` is false.
11. `heatKernel_decayFactor_le_one`'s `ht`, at `k = ⟨1⟩`, `t = -1`:
    `e² ≤ 1` is false.

### δ — the negative-edge fixture `hfNegAdj = !![0, -2; -2, 0]]`
(degrees `(-2, -2)`, Laplacian `!![-2, 2; 2, -2]]` with square
`(-4) • L`, trace `-4`, determinant `0` — pins the spectrum `[-4, 0]`
through the two-point pattern)

12. `heatKernel_decayFactor_le_one`'s `hnonneg`, at `k = ⟨0⟩`, `t = 1`:
    `e⁴ > 1` against the dropped claim — **dissipation fails on signed
    input**: the negative Laplacian eigenvalue `-4` makes the "decay"
    factor a growth factor. First negative witness for the clause.
13. `heatKernel_mulVec_tendsto_atTop`'s `hnonneg`, at
    `x = ![1, -1]` (a genuine eigenvector at `-4`): the flow is
    `e^{4t} • x`, coordinate `0` bounded below by `1` — it does not
    tend to the claimed mean `0`. **The DC limit fails on signed
    input** — modes grow instead of dissipating.
14. `heatKernel_variance_decay`'s `hnn`, at `t = 1`, `f = ![1, -1]`:
    the output variance is `2e⁸` against the rate-`e⁰ = 1` bound on
    input variance `2` — **the variance bound genuinely needs PSD**
    (at `λ₂ = 0` with a negative eigenvalue below it, the growth mode
    escapes the rate).
15. `secondEval_le_eigvalOf_of_ne_zero`'s `hnn`, at the index with
    `eigvalOf = -4` (from `evals_mem_eigvalOf` at the pinned `⟨0⟩`
    entry): the claim `λ₂ = 0 ≤ -4` is false — **below-gap eigenvalues
    are only kernel eigenvalues on PSD input**.
16. `sum_deg_mul_sq_eq`'s `hd`, at `g = ![1, 0]`: the left side is
    `-2`, the right side is junk-`√(-2) = 0` — the π-isometry genuinely
    needs positive degrees.
17. `sum_deg_mul_eq`'s `hd`, same fixture: `-2 ≠ 0`.

### ε — the disconnected fixture `disAdj` (delivered pins reused)

18. `heatKernel_mulVec_tendsto_atTop`'s `hconn`, at the isolated
    vertex's indicator `x`: the flow is *constantly* `x` (the delivered
    `heatKernel_isolated_fixed_QA`), so it converges to `x ≠ (1/3) • 1`
    — **the DC limit genuinely needs connectivity** (the limit is the
    component mean, not the global mean). Needs the new eigen pin
    `L_dis *ᵥ ![1, -1, 0] = 2 • ![1, -1, 0]`.
19. `heatKernel_variance_decay`'s `ht : 0 ≤ t`, at `t = -1`,
    `f = ![1, -1, 0]`: the backward flow grows the eigenvalue-`2` mode
    (`e² • f`), output variance `2e⁴` against the rate-`e⁰ = 1` bound —
    **negative time is the backward (growth) semigroup** and the
    variance bound genuinely excludes it.

### ζ — the asymmetric mass fixture `hfAsymAdj = !![0, 2; 1, 0]]`
(Laplacian `!![2, -2; -1, 1]]` with square `3 • L`)

20. `sum_heatKernel_mulVec`'s `hA`, at `t = 1`, `f = ![1, 0]`: the
    flow is `![1, 0] − α • ![2, -1]` with `α = (1 − e⁻³)/3 ≠ 0`, so its
    mass is `1 − α ≠ 1` — **mean preservation genuinely needs
    symmetry** (asymmetric column sums move the mass). The rank-one
    collapse at `c = -3` evaluates the flow exactly.

### η — K₂ misc

21. `eigvecOf_ker_eq_smul_onesVec_of_secondEval_pos`'s
    `hμ : eigvalOf i = 0`, at the index with `eigvalOf = 2` (delivered
    `edge_eigvalOf_exists_two`): the mode structure pin
    (`edge_eigvecOf_mode_two`: `eigvecOf i = c • ![1, -1]`,
    `2c² = 1`) contradicts `= d • onesVec` (would force `c = 0`) —
    **the kernel-characterization clause genuinely excludes nonzero
    modes**, with `hpos` genuine at the pinned gap `2`.
22. `heatKernel_firstOrder_remainder_apply_le`'s
    `ht : ∀ i, |t · λᵢ| ≤ 1`, at `t = -2`, `x = ![1, 3]`, `a = 0`:
    the closed form gives LHS `|5 − e⁴| = e⁴ − 5` and the eigen-sum
    constant (delivered `edge_remainder_sum_eq = 4`) gives RHS
    `4 · 4 = 16`; `e⁴ > 21` (from `9/4 ≤ e`: `(9/4)⁴ > 21`) — the
    dropped-window claim `e⁴ − 5 ≤ 16` is false. **The smallness window
    is genuinely load-bearing, not cosmetic** — the first negative
    witness for the remainder bound itself (the delivered window fence
    only showed the hypothesis fails at `t = 1`, not that the
    conclusion escapes).

### θ — the zero-degree signed fixture `hfZeroAdj = !![-2, 2; 2, 0]]`
(degrees `(0, 2)`; `degreeInvSqrt` junk on row `0` kills the
congruence to the zero matrix, so `normalizedLaplacian = 1` and
`walkLaplacian = !![1, 0; -1, 1]]`; both heat kernels evaluate in
closed form — `e⁻¹ • 1` and `e⁻¹ • !![1, 0; 1, 1]]`)

23. `normalizedHeatKernel_mulVec_degreeSqrt_onesVec`'s
    `hd : ∀ i, 0 < deg A i`: the normalized flow of `√D · 1` is
    `e⁻¹ (0, √2) ≠ (0, √2)` — **the normalized mass-conservation twin
    genuinely needs positive degrees** (at a zero-degree row the junk
    `D⁻¹ᐟ²` kills the congruence but the `√D · 1` vector survives).
24. `walkHeatKernel_mulVec_onesVec`'s `hd`: the walk flow of `1` is
    `e⁻¹ (1, 2) ≠ (1, 1)` — same mechanism on the walk side.
25. `degreeSqrt_mul_walkLaplacian`'s `hd`: entry `(1, 0)` reads
    `-√2 ≠ 0` — **the commutation genuinely needs positive degrees**.
26. `degreeSqrt_mul_pow_neg_smul_walkLaplacian`'s `hd` (at `n = 1`,
    `t = 1`): the per-power conjugation, same entry.
27. `degreeSqrt_mulVec_walkHeatKernel`'s `hd` (at `t = 1`,
    `f = ![1, 0]`): LHS `(0, √2 e⁻¹) ≠ 0` = RHS — **the semigroup
    conjugation genuinely needs positive degrees**.
28. `walkHeatKernel_variance_decay`'s `hd`, at `t = 1`, `f = ![0, 1]`:
    the input's π-variance is exactly `0` (mean `1`, both entries) so
    the bound claims output variance `≤ rate · 0 = 0`, but the flow
    `e⁻¹ ![0, 1]` has π-variance `2(e⁻¹ − 1)² > 0` — a clean
    zero-variance-input kill with no secondEval pin needed at all.

### ι — the signed 2-regular fixture `hfRegAdj = !![3, -1; -1, 3]]`
(degrees `(2, 2)`; `L_sym = L_walk = 1 − A/2 = !![-1/2, 3/2; 3/2, -1/2]]`,
trace `-1`, determinant `-2` — pins the spectrum `[-2, 1]`)

29. `secondEval_le_eigvalOf_normalizedLaplacian_of_ne_zero`'s `hnn`,
    at the index with `eigvalOf = -2`: the claim `λ₂(L_sym) = 1 ≤ -2`
    is false — the normalized twin of fence 15, with `hd` genuine
    (degrees `2 > 0`). The pin needs the `1/√2 · 1/√2 = 1/2` arithmetic
    and a two-point spectrum pin without the product-zero crutch
    (sum `-1`, product `-2`: the pair `{-2, 1}`).
30. `walkHeatKernel_variance_decay`'s `hnn`, at `t = 1`,
    `f = ![1, -1]` (a genuine `L_walk`-eigenvector at `-1`): the flow
    is `e • f`, output π-variance `4e²` against the rate-`e⁻²` bound on
    input `4` — `e⁴ ≤ 1` is false. The signed-regular walk twin of
    fence 14.

### Deferral (priced, recorded mechanism)

D1. `walkHeatKernel_variance_decay`'s `ht : 0 ≤ t` — the natural
    witness is `K₂ ⊕ K₂` on `Fin 4` (disconnected, regular, positive
    degrees), where the backward flow grows the per-block eigenvalue-`2`
    mode while `λ₂(L_sym) = 0` holds the rate at `1`. Needs a
    four-point `secondEval(L_sym) = 0` pin at a `4 × 4` fixture (route:
    `secondEval_le_rayleigh_of_ker` at a centered component indicator
    + `normalizedLaplacian_evals_zero`), the heaviest single item
    priced; deferred with the combinatorial twin (fence 19) closing the
    same mechanism class (`ht`, backward-time growth) for the family.

    **RESOLVED 2026-09-05** (run `20260905T144054Z-run-1`, session
    `ses_f8e134871ffeiWXCb84ykj7oaD`; see the D1 delivery record
    below): `hf_walk_var_t_fence` in `Heat_QA.lean`'s new
    `HeatFencesD1` section, at the priced witness and the priced
    route — the four-point pin landed as
    `hfDis4Adj_norm_secondEval_eq_zero` (upper bound via
    `secondEval_le_rayleigh` at the centered component indicator
    `![1,1,-1,-1]`, a genuine `L_sym`-kernel vector; lower bound via
    `normalizedLaplacian_evals_zero` + `evals_sorted`), the flow pin
    via `exp_mulVec_eq_smul_of_mulVec_eq_smul` at the eigenvalue-`2`
    mode. Output π-variance `2e⁴` against the rate-`e⁰ = 1` bound on
    input `2`, at `t = -1`; packaged isolation proving every kept
    clause (`hA`/`hnn`/`hd`/`hcard`) genuine and `ht` genuinely
    failing. The family's falsification surface is now complete with
    no open deferral.

### Non-fenceables with mechanisms (the P4/signature classes)

- **The `hA`-in-display class**: every eigenbasis-consuming statement
  (`heatKernel_mulVec_eigvecOf`, `heatKernel_mulVec_eq_sum`,
  `eigvecOf_dotProduct_heatKernel_mulVec`,
  `dotProduct_self_heatKernel_mulVec`, the remainder bound's `hA`,
  `eigvalOf_mem_evals`) mentions `laplacian_symmetric A hA` or
  `eigvecOf/eigvalOf` in its *conclusion*, so the dropped-hA statement
  does not elaborate — the dk audit's signature-entangled class. Same
  for the `hcard` clauses (`secondEval`'s display consumes the
  cardinality proof).
- **The HasDerivAt pair's `hA` (P4, truth-removable)**: the generator
  identity `d/dt e^{-tL} x|₀ = -Lx` holds for *every* real matrix
  (finite-dimensional differentiability of the exponential), so the
  dropped statement is provable — the hypothesis is an artifact of the
  eigenbasis proof route, not load-bearing in the statement. Recorded,
  not fenced.
- **The choice-entangled kernel-mode clauses** of
  `eigvecOf_ker_eq_smul_degreeSqrt_onesVec_of_secondEval_pos` (`hpos`,
  `hμ` at fixtures whose `eigvalOf` ordering is unknowable): the
  combinatorial twin (fence 21) closes the mechanism class at a pinned
  fixture.

## Delivery record (2026-09-05)

DELIVERED at the full priced scope: **30 fences** (items 1–30 above),
QA-only, a pure insertion in `Heat_QA.lean`'s new `HeatFences` section,
plus the four new fixtures with their pin blocks (spectrum pins at
`hfNegAdj` via the trace/determinant two-point pattern, at `hfRegAdj`
via the sum/product pair `{-2, 1}`, closed-form heat-kernel pins at
`hfZeroAdj` and `hfAsymAdj` through the delivered collapse engines,
and the eigen-equation pins the flow fences consume) and the isolation
companions (each kept hypothesis proved genuine at its fixture).
Zero axiom contact: `#print axioms` via `wip/heatfences_axcheck.lean`
on every new public declaration — each exactly `propext,
Classical.choice, Quot.sound`; no `-- @refutes` tags (theorem
instantiations, nothing admitted consumed). QA count and records
updated per the ladder; see the terminal activity entry.

Technique findings (recorded for future audits):

1. **The `9/4 ≤ e` lower-bound chain** — two applications of
   `add_one_le_exp` at `1/2` composed through `Real.exp_add` — is the
   cheapest sufficient pin for every `e ≠ 1`, `e ≠ 2`, `e⁴ > 21`-shaped
   fence constant in this file; no series or numeric-exp machinery
   needed.
2. **Tendsto refutations** (`hμ` of `tendsto_exp_neg_mul_atTop`,
   `hnonneg` of the DC limit) close through the
   eventually-atTop-membership route (`mem_atTop_sets`) with the
   constant/`exp ≥ 1` lower bound supplying the contradiction; the DC
   limit's `hconn` fence instead uses `tendsto_nhds_unique` against
   `tendsto_const_nhds` (the flow is *constant* at the isolated
   vertex).
3. **Junk-`√` and junk-`0⁻¹` corner pins** (`degreeSqrt`,
   `degreeInvSqrt`, `walkTransitionMatrix` at degrees `0` and `-2`)
   reduce entrywise through `Real.sqrt_zero`/`inv_zero` and the
   diagonal-matrix entry lemmas — the zero-degree row kills the
   congruence to zero while `√D · 1` survives, which is exactly what
   makes fences 23–28 kill rather than junk-trivialize (a P4 trap the
   pricing checked explicitly: at *symmetric zero-degree* input several
   of the dropped statements are junk-provable, per the normalized
   audit's finding; the negative-diagonal entry is what breaks the
   symmetry genuinely).
4. **The two-point spectrum pin generalizes**: the delivered
   `two_point_pin` (sum `2`, product `0`) has two siblings in this
   delivery — sum `-4`/product `0` (roots `{0, -4}`, the zero-root
   branch forced by sortedness) and sum `-1`/product `0` (roots
   `{-1, 0}`, same shape at the normalized Laplacian).
5. **`fin_cases` must precede the literal-entry `simp`** at `2×2`
   matrix-literal pins: `simp [deg, fixture, Fin.sum_univ_two]` with a
   *variable* index leaves `deg !![...] i` unreduced (the cons-entry
   lemmas cannot fire under an opaque index), while the same call
   after `fin_cases i` closes — probe-confirmed before landing.
6. **The pricing-stage scalar-vs-matrix-`1` correction**: the signed
   2-regular fixture's normalized Laplacian was initially priced at
   `!![-1/2, 3/2; 3/2, -1/2]]` — reading the identity in `1 − (1/2)•A`
   as *scalar*. The off-diagonal of the identity *matrix* is zero, so
   the correct value is `!![-1/2, 1/2; 1/2, -1/2]]` with spectrum
   `[-1, 0]` (not `[-2, 1]`). Caught by a genuinely-nontrivial fixture
   probe (`simp` reduced the mispriced identity to `False`) before any
   landing — the fences at this fixture were re-derived from the
   corrected spectrum (`0 ≤ -1` and `4e² > 4`), both killing as
   priced, only at the corrected constants.
7. **`rw` under binders only for closed subterms**: rewriting a
   hypothesis-side mean value (a closed term) inside a `∑`-body works,
   but the follow-up `sub_zero` does not (`rw` is syntactic under
   binders) — `simp only [sub_zero]` is the drop-in replacement; and
   scalar-literal smuls in *statement* position elaborate as `ℕ`-smuls
   unless annotated `(c : ℝ) •`, which silently mismatches
   `matrix_exp_smul_one`'s `ℝ`-smul instance.

## D1 delivery record (2026-09-05)

**Run:** `20260905T144054Z-run-1`, session
`ses_f8e134871ffeiWXCb84ykj7oaD`. DELIVERED at the full priced scope —
the walk-twin variance `ht` fence in `Heat_QA.lean`'s new
`HeatFencesD1` section (a pure insertion after `end HeatFences`):
twenty theorems plus two fixture `def`s at the priced witness
`hfDis4Adj` (two disjoint edges on `Fin 4`, the `if`-spelling per the
family's own technique finding — the `!![…]` cons-tower leaves
`vecHead/vecTail` residue at Fin 4), QA-only, zero axiom contact
(`#print axioms` via `wip/d1fence_axcheck.lean` on all twenty public
declarations — every one exactly `propext, Classical.choice,
Quot.sound`; the two `def`s audited transitively; no `-- @refutes`
tags — theorem instantiations of an all-proved shelf, nothing
admitted consumed; the 12-tag independence check unchanged and
clean). QA 6041 → 6061 (+20 by the generator metric).

The delivery's content:

- **The fixture's honest-clause design** — the deferral's whole reason
  for existing: the walk twin's kept clauses include `hnn` and `hd`,
  so neither pre-delivery fixture could carry an `ht`-only fence (the
  Fin 3 `disAdj` breaks `hd` at its isolated vertex; the Fin 2
  `hfRegAdj` breaks `hnn` at its negative weight). Two disjoint edges
  keep every clause genuine while disconnection holds the rate at
  `e⁰ = 1` — the packaged isolation `hfDis4Adj_isolation` proves
  `hA`/`hnn`/`hd`/`hcard` genuine and `(-1 : ℝ) < 0`.
- **The four-point pin** `hfDis4Adj_norm_secondEval_eq_zero` at the
  priced route: upper bound via `secondEval_le_rayleigh` at the
  centered component indicator `hfDis4KerVec = ![1,1,-1,-1]` (a
  genuine `L_sym`-kernel vector at the unit degrees where
  `degreeInvSqrt = 1`, so `L_sym = 1 − A` and the Rayleigh quotient is
  `0`), lower bound via `normalizedLaplacian_evals_zero` +
  `evals_sorted` — the exact shape of the delivered Fin 3
  combinatorial pin `disAdj_secondEval_eq_zero_QA`, lifted to the
  normalized Laplacian.
- **The flow pin** `hfDis4Adj_walkHeatKernel_minus_one_mode`:
  `walkHeatKernel hfDis4Adj (-1) *ᵥ ![1,-1,0,0] = e² • ![1,-1,0,0]`
  through `exp_mulVec_eq_smul_of_mulVec_eq_smul` at the per-block
  antisymmetric mode, a genuine `L_walk`-eigenvalue-`2` vector (the
  within-block swap negates it).
- **The fence** `hf_walk_var_t_fence` in the delivered
  `hf_walk_var_nn_fence` statement shape (the deg-weighted π-variance,
  the rate through `secondEval (normalizedLaplacian …)`): at
  `t = -1`, mean `0` (the deg-weighted cross sum vanishes), input
  variance `2`, output `2e⁴` — the dropped statement demands
  `2e⁴ ≤ 2`, killed by `hf_exp_two_gt_one`. Backward time is the
  backward (growth) semigroup, and the variance bound genuinely
  excludes it — now witnessed on both twins at independent fixtures.

Technique findings: (1) the `if`-spelling fixture is mandatory at
Fin 4 — the `!![…]` literal's entry proofs leave irreducible
`vecHead/vecTail` towers that neither `simp` nor `norm_num` closes
(the family's own finding 4, re-confirmed); (2) at unit degrees the
normalized Laplacian collapses through the `degreeInvSqrt = 1` pin
(`simp only` with `Matrix.diagonal_apply`/`Matrix.one_apply`, then
`one_mul`/`mul_one`), which is what makes the four-point pin a
Fin-3-shaped argument rather than a new engine; (3) literal-index
entry pins of the 4-vector `![1,-1,0,0]` close under plain `norm_num`
after the degree `rw` — no cons-entry lemma list needed in `have`
position (only in `funext`-position proofs, where full `simp [def]`
carries them).

**Verification:** spike first (`wip/d1fence_spike.lean` — the full
delivery, green after two fix rounds in the recorded trap classes:
the cons-tower residue forcing the `if`-spelling, and a
`degreeInvSqrt` `rw` that needed `simp only [degreeInvSqrt, …]`
rather than `rw [Matrix.diagonal_apply]` at the folded def); `lake
env lean` on the landed module (zero errors; the file's two
`Try this: ring_nf` traces pre-exist at HEAD, verified by elaborating
`git show HEAD`'s copy); explicit `lake build
Scaffold.QA.SpectralGraph.Heat_QA` ✔; full `lake build` ✔ +
`check_build_completeness.py` — 134/134/0/0, exit 0; `lint_axioms`
exit 0 (4 axioms unchanged); `check_refutation_independence`
(12-tag clean); `check_public_reachability` clean (63 modules);
`check_citations` ("All axioms have proper citations!");
`check_qa_name_uniqueness` clean (the new `hfDis4*` names add no
collision); `check_backlog_freshness` clean; scoreboard regenerated
(**6061/4/0**) with the verification row; map-freshness exit 0 after
the 6041 → 6061 stats sync in both map data tables and SVG
regeneration (49 stations, no status change — none owed: this
proposal is not a map station's cited source).
