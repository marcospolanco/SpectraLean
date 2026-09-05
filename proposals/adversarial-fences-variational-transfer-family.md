# The Variational-Transfer Family's Adversarial Fence Audit

**Status:** COMPLETE (delivered 2026-09-04 by run `20260904T225018Z-run-1`,
session `ses_f91628a09ffet5PEiih6q7y4mG`; see the delivery record).

## Scope

The prior terminal handoff's named top survey target: "`VariationalTransfer_QA`
(13 consumers, the smallest and only fully pre-discipline QA of the top three)
and `Resolvent_QA` (16 consumers) — a fresh consumption survey should
confirm." This run ran the survey independently (a reverse-import walk over
every `Scaffold.Mathlib` shelf, counting transitive non-QA consumers) and it
confirmed the ranking: Spectral 46, Cheeger 24, Normalized 20, Resolvent 16,
Matrix.Basic 14, **VariationalTransfer 13**, Electrical 10, PerronFrobenius 7 —
with the fence-section cross-check deciding the pick: Resolvent's 1153-line QA
already carries free-form negative witnesses, while
`Scaffold/QA/SpectralGraph/VariationalTransfer_QA.lean` (170 lines, delivered
2026-08-25 with the module) is the top tier's only *fully* pre-discipline QA
— positive instantiations only, zero negative witnesses.

This proposal audits `Scaffold/Mathlib/GraphTheory/VariationalTransfer.lean`'s
*unfenced* clause surface. The boundary against already-delivered fences:

- `IrregularCheeger_QA.lean`'s `IrregularFences` (2026-09-04) already fences
  the Cheeger statements' clauses (`cheeger_upper_bound_normalized`'s `hnn`,
  `cheeger_sweep_normalized`'s `hnn`/`horth`/`hf0`,
  `cheeger_sweep_cut_normalized`'s `hnn`/`hf0`,
  `cheeger_lower_bound_normalized`'s `hnn`,
  `cheegerConstant_pos_of_connected`'s `hconn`/`hnn`), the connectivity
  transfer's `secondEval_normalizedLaplacian_eq_zero_of_not_connected`
  (`hnn` at the two-disjoint-signed-blocks fixture, `hd` at the
  edge⊕isolated fixture), the mul-form sandwich
  (`mul_degMin_le_lambda2`'s `hdmin`, `lambda2_le_mul_degMax`'s `hdmax`) and
  both window-Cheeger constants' wrong-constant clauses, and the sweep
  extraction's `hy`/`hM`.
- `DegreeSandwich_QA.lean` already fences the secondEval-level upper engine's
  wrong-constant pairing (`dsP3_wrongConstant_refuted_QA`) and `0 < dmin`
  guard (`dsIsoAdj_upper_dmin_zero_refuted_QA`).
- `IrregularCheeger_QA.lean`'s `ifc_disc_hinge_fence_QA` fences the
  Fiedler orthogonality hinge's *mechanism* (a kernel eigenvector violating
  orthogonality at `λ₂ = 0`).

The audit target is therefore the remainder: the **transfer-engine layer**
(`quadForm_congr`, `degreeSqrt_mulVec_ne_zero`,
`quadForm_laplacian_eq_quadForm_normalizedLaplacian`,
`dotProduct_degreeSqrt_mulVec`/`_mixed`/`_onesVec`,
`rayleigh_normalizedLaplacian_degreeSqrt`,
`normalizedLaplacian_psd`, the cut-test-vector quartet's degree clauses,
`degreeSqrt_mul_normalizedLaplacian`, the kernel-cone lift), the
**connectivity-transfer layer**'s `hnn` clauses
(`secondEval_normalizedLaplacian_pos_of_connected`,
`secondEval_normalizedLaplacian_pos_iff_connected`,
`normalizedLaplacian_evals_zero`), and the **degree-sandwich layer's
pointwise engines** (`sum_deg_mul_sq_ge`/`_le`,
`rayleigh_normalizedLaplacian_le_div`,
`rayleigh_le_mul_rayleigh_normalizedLaplacian`,
`degreeSqrtEquiv`'s bijectivity, the div-form interface's wrong-constant
clause).

Consumer set (the leverage case): the shelf feeds `Cheeger.lean`'s volume
machinery consumers, `Fiedler.lean`, `EdgePerturbation.lean` (the derived
Cheeger-window capstone), `PolyFilter.lean`, and `SpectralCertificates.lean`
— 13 transitive non-QA consumers by the survey's count, every one riding the
congruence bridge this module wraps.

## Step-0 findings: the priced fence list

Fixtures: the negative-degree `nfNegEdge = !![-2, 1; 1, 0]]` (degrees
(−1, 1), `L_sym = 1`, `L = !![1,−1;−1,1]]` — pins delivered in
`Normalized_QA`'s `AdversarialFences` and imported), `Normalized_QA`'s
`nfIso` (zero-degree corner) and `nfAsymAdj = !![0,2;1,0]]` (asymmetric,
positive degrees), `KernelBridge_QA`'s `kbfSgnPath3Adj =
!![0,2,−1;2,0,2;−1,2,0]]` (symmetric, signed, *connected* support, kernel
pinning delivered), plus three local fixtures: `vtSigAdj = !![3,−1;−1,3]]`
(signed genuinely-`d = 2`-regular), `vtZeroAdj` (the all-zero adjacency on
`Fin 2`), `vtK2Adj` (K₂), and `vtNegCutAdj = !![3,1,−3;1,0,1;−3,1,3]]`
(the connected negative-cut shape, degrees (1,2,1)).

1. **`quadForm_congr`'s `hP`** at `P = !![1,1;0,1]]`, `M = 1`, `y = (0,1)`:
   `quadForm (P·1·P) y = 1 ≠ 2 = quadForm 1 (P *ᵥ y)`.
2. **`quadForm_laplacian_eq_quadForm_normalizedLaplacian`'s `hd`** at
   `nfNegEdge`, `y = e₀`: LHS `1`, RHS `quadForm 1 (0, 0) = 0` — the
   negative-degree row kills the stretch.
3. **`dotProduct_degreeSqrt_mulVec`'s `hdeg`** at `nfNegEdge`, `y = e₀`:
   LHS `0` (the junk `√(−1) = 0` kills the vector), RHS `−1`.
4. **`dotProduct_degreeSqrt_mulVec_mixed`'s `hdeg`** — same witness: `0 ≠ −1`.
5. **`dotProduct_degreeSqrt_mulVec_onesVec`'s `hdeg`** — same witness: `0 ≠ −1`.
6. **`degreeSqrt_mulVec_ne_zero`'s `hd`** at `nfNegEdge`, `y = e₀`: the
   conclusion itself fails — `√D *ᵥ e₀ = (0, 0) = 0`.
7. **`rayleigh_normalizedLaplacian_degreeSqrt`'s `hd`** at `nfNegEdge`,
   `y = e₀`: LHS `rayleigh 1 0 = 0` (the definitional junk branch), RHS
   `1 / (−1) = −1`.
8. **`degreeSqrt_mul_normalizedLaplacian`'s `hd`** at `nfNegEdge`: entry
   (0,1) reads `0` (junk `√(−1)·1`) against `−1` (genuine `L · 1`).
9. **The kernel-cone lift's `hd`** at `nfNegEdge`, `y = (1,1)` (genuinely
   `L *ᵥ y = 0`): conclusion `L_sym *ᵥ (√D y) = 1 *ᵥ (0,1) = (0,1) ≠ 0`.
10. **`dotProduct_degreeSqrt_mulVec_cutTestVector`'s `hdeg`** at
    `nfNegEdge`, `S = {0}`: the stretched cut vector and stretched constants
    are both `(0,1)`, dot `1` against the claimed `0`.
11. **`dotProduct_degreeSqrt_mulVec_cutTestVector_self`'s `hdeg`** — same
    witness: `1` against `vol S · vol Sᶜ · vol V = (−1)(1)(0) = 0`.
12. **`degreeSqrt_mulVec_cutTestVector_ne_zero`'s `hd`** at `vtZeroAdj`,
    `S = {0}`: every volume is junk-zero, the cut vector is `0`, and the
    stretch of `0` is `0` — the conclusion itself fails.
13. **`rayleigh_normalizedLaplacian_degreeSqrt_cutTestVector`'s `hd`** at
    `nfNegEdge`, `S = {0}`: LHS `rayleigh 1 (0,1) = 1`, RHS
    `boundary · vol V / (vol S · vol Sᶜ) = 1 · 0 / (−1) = 0`.
14. **`normalizedLaplacian_psd`'s `hA`** at `nfAsymAdj`, `x = (1,1)`: the
    form sees the symmetrized action, `2 − (3/2)√2 < 0` (`4 < 3√2` since
    `16 < 18`).
15. **`normalizedLaplacian_psd`'s `hnn`** at `vtSigAdj`, `x = (1,−1)`:
    `quadForm L_sym (1,−1) = −2 < 0` (an eigenpair at `−1`).
16. **`normalizedLaplacian_evals_zero`'s `hnn`** at `vtSigAdj`: the bottom
    eigenvalue is `≤ −1` (eigen-index existence at the `(1,−1)` mode +
    `evals_first_le_eigvalOf`), against the claimed `= 0` — the signed
    normalized Laplacian is not PSD and its spectrum dips below `0`.
17. **`normalizedLaplacian_evals_zero`'s `hd`** at `vtZeroAdj`: `L_sym = 1`
    entrywise, `evals ⟨0⟩ = 1 ≠ 0` through `evals_one`.
18. **`secondEval_normalizedLaplacian_pos_of_connected`'s `hnn`** at
    `kbfSgnPath3Adj`: both combinatorial kernel vectors (`1` and
    `![1,2,3]`, delivered pins) stretch into the `L_sym` kernel (the cone
    lift, `hd` genuine — degrees (1,4,1)), so a 2-dimensional subspace of
    the kernel forces `λ₂ ≤ R(x) = 0` through the subspace competitor
    engine (`exists_ne_mem_rayleigh_ge_of_finrank_eq`) — refuting
    `0 < λ₂` with `hconn` genuine (delivered pin).
19. **`secondEval_normalizedLaplacian_pos_iff_connected`'s `hnn`** — the
    same witness: the iff reads `false ↔ true`.
20. **`degreeSqrtEquiv`'s `hd`** (bijectivity) at `vtZeroAdj`: the stretch
    map is literally `0`, so injectivity fails (`f 1 = 0 = f 0`).
21. **`sum_deg_mul_sq_ge`'s `hdmin`** at `vtK2Adj`, `dmin = 5`, `x = e₀`:
    `5 · 1 ≤ 1` is false — an overstated floor cannot bound the weighted
    norm.
22. **`sum_deg_mul_sq_le`'s `hdmax`** at `vtK2Adj`, `dmax = 1/2`, `x = e₀`:
    `1 ≤ 1/2` is false.
23. **`rayleigh_normalizedLaplacian_le_div`'s `hnn`** (the headline) at
    `vtNegCutAdj`, `dmin = 1` (genuine), `x = (1,1,0)`: `quadForm L x = −2`
    is negative, so the degree-weighted denominator `3` divides it to
    `−2/3` while the plain-norm quotient lands at `−1 = −2/2` — the
    bracket *flips* exactly as the docstring warns
    ("on signed input the combinatorial form is not PSD and the division
    flips"): `−2/3 ≤ −1` is false with `hA`, `hd`, `hdmin`, `hpos`, `hx0`
    all genuine.
24. **`rayleigh_le_mul_rayleigh_normalizedLaplacian`'s `hnn`** — the same
    witness at `dmax = 2` (genuine): `−1 ≤ 2 · (−2/3) = −4/3` is false.
25. **`rayleigh_normalizedLaplacian_le_div`'s `hdmin`** (wrong constant) at
    `vtK2Adj`, `dmin = 5`, `x = (1,−1)`: `2 ≤ 2/5` is false.
26. **`rayleigh_le_mul_rayleigh_normalizedLaplacian`'s `hdmax`** at
    `vtK2Adj`, `dmax = 1/2`: `2 ≤ 1` is false.
27. **`rayleigh_normalizedLaplacian_le_div`'s `hpos`** at `nfIso`,
    `dmin = 0` (genuine against `0 ≤ deg`), `x = e₀`: the RHS is
    `rayleigh L e₀ / 0 = 1/0 = 0` while the LHS computes to `1`.
28. **`div_le_secondEval_normalizedLaplacian`'s `hdmax`** at `vtK2Adj`,
    `dmax = 1/2`: the div-form interface at `lambda2 / (1/2) = 4 ≤ 2` —
    false (the mul form is fenced by `icf_sandwich_hdmax`; this is the
    div form's own statement).

### Non-fenceables (with mechanisms)

- **`normalizedLaplacian_psd`'s `hd`** — P4 truth-removable: at nonnegative
  symmetric input a zero-degree row is identically zero (nonnegativity
  forces `A i j = 0` for all `j`), so `L_sym` is block-diagonal with an
  identity block on the zero-degree coordinates and the PSD normalized
  block elsewhere; PSD survives the dropped clause.
- **`secondEval_normalizedLaplacian_pos_of_connected`'s `hd`** — P4
  *conditional on `hnn`*: at nonnegative symmetric input, connectivity
  with `2 ≤ card` forces every degree positive (a zero-degree vertex is
  support-isolated); the clause is redundant given `hnn`, whose own fence
  (#18) carries the load.
- **The `hA` clauses of `secondEval_..._pos_of_connected`/`_pos_iff`** —
  display-entangled: `hconn` is `(supportGraph A hA).Connected`, so the
  dropped statement does not elaborate.
- **The `hcard` clauses** — proof-term-in-display: `secondEval`'s
  `⟨1, by omega⟩` index elaborates against `hcard`; the dropped statement
  is malformed.
- **The Fiedler layer's `hpos` clauses** (`fiedlerVectorNormalized_ortho`,
  `fiedlerSweepVector_sum_deg_eq_zero`) and the sweep-vector identity
  pair's `hd` clauses — choice-entangled: the objects are built from
  `Classical.choose`/`eigvecOf`, whose coordinate behavior at a degenerate
  eigenspace is not determined by the hypotheses; the *mechanism* is
  fenced by the delivered `ifc_disc_hinge_fence_QA` (a kernel eigenvector
  provably violating the hinge at `λ₂ = 0`).
- **The eigenvalue-level engines' `hnn` clauses**
  (`evals_normalizedLaplacian_le_div`/`div_le_evals_...`) — screened: the
  engine's proof routes every test vector through the pointwise bracket
  (#23/#24), so the mechanism is guarded there; at *regular* signed input
  the bracket is an identity (`∑ deg x² = d‖x‖²`), so the eigenvalue-level
  violation is genuinely fixture-dependent and not cheaply witnessable.
- **`fiedlerIndexNormalized`/`fiedlerVectorNormalized` interface theorems'
  `hA`/`hcard`** — display-consumed by the def's own type
  (`normalizedLaplacian_symmetric A hA`, the `⟨1, by omega⟩` position).

## Delivery record

**DELIVERED at the full priced scope** — 27 fences (the priced 26 plus
the mixed-pairing clause of `dotProduct_degreeSqrt_mulVec_mixed`, whose
`y = z` instance is statement-identical to the diagonal companion and
is carried by it), 12 explicit isolation-companion theorems, the
remaining fences' isolation evidence carried by the local fixture pins
named in each fence's documentation (`vtSigAdj_isSymm`,
`vtSigAdj_deg_pos`, `vtNegCutAdj_degMin/degMax`, `vtf_neg_vol_*`, the
imported `nfNegEdge_*`/`kbfSgn3_*` pins). Landed as
`VariationalTransfer_QA.lean`'s `TransferFences` section, a pure
1126-line insertion plus three QA imports (`Normalized_QA` for the
negative-degree/zero-degree/asymmetric fixture pins, `KernelBridge_QA`
for the signed-path pins, `DegreeSandwich_QA` transitively for K₂'s
delivered `lambda2`/`secondEval` pins). 127 new declarations (124
theorems + the 3 local fixture `def`s `vtSigAdj`, `vtZeroAdj`,
`vtNegCutAdj`); QA 5116 → 5240 (+124 by the generator metric).
QA-only, zero axiom contact: `#print axioms` via
`wip/vtfences_axcheck.lean` on all 127 declarations — every one exactly
`propext, Classical.choice, Quot.sound`; no `-- @refutes` tags
(theorem instantiations, nothing admitted consumed). QA proves
consequences relative to the substrate; it does not prove the substrate
(no axiom touched).

The headline finding is the quotient bracket's flip: the docstring of
`rayleigh_normalizedLaplacian_le_div` itself warns that "on signed
input the combinatorial form is not PSD and the division flips" — no
witness existed anywhere in the repository. The connected negative-cut
fixture `vtNegCutAdj = !![3,1,−3;1,0,1;−3,1,3]]` (degrees (1,2,1),
`dmin = 1`/`dmax = 2` both genuine) supplies it at `x = (1,1,0)`:
`quadForm L x = −2` is negative, so the degree-weighted denominator
`∑ deg x² = 3` divides it to `−2/3` while the plain-norm quotient lands
at `−1 = −2/2` — `−2/3 ≤ −1` is false for the upper side and
`−1 ≤ 2·(−2/3) = −4/3` is false for the lower side, both with `hA`,
`hd`, `hdmin`/`hdmax`, `hpos`, `hx0` all genuine. The second finding is
the connectivity transfer's `hnn`: at the signed path with *connected*
support (the delivered `kbfSgnPath3Adj`), both combinatorial kernel
vectors stretch into the normalized kernel (the cone lift at genuine
positive degrees), so a two-dimensional kernel subspace forces
`λ₂ (L_sym) ≤ R(x) = 0` through the subspace competitor engine
`exists_ne_mem_rayleigh_ge_of_finrank_eq` — refuting `0 < λ₂` with
`hconn` genuine: **connected support does not force a spectral gap once
signs enter**. Third: the signed `d = 2`-regular fixture's alternating
mode pins the bottom normalized eigenvalue at `≤ −1` (the
`normalizedLaplacian_evals_zero` `hnn` fence) — the signed normalized
Laplacian dips below zero, exactly the PSD failure the dropped
nonnegativity would have prevented.

Non-fenceables recorded with mechanisms (the proposal's Step-0 list,
delivered as priced): the PSD transfer's `hd` (P4 — at nonnegative
symmetric input zero-degree rows vanish identically, PSD survives);
`secondEval_..._pos_of_connected`'s `hd` (P4 conditional on `hnn`:
connectivity + nonnegativity + `2 ≤ card` forces positive degrees); the
`hA` clauses display-entangled through `supportGraph A hA`; the `hcard`
clauses proof-term-in-display (the `⟨1, by omega⟩` position); the
Fiedler layer's `hpos` clauses and the sweep-vector identity pair's
`hd` clauses choice-entangled through `Classical.choose`/`eigvecOf`
(the *mechanism* is fenced by the delivered `ifc_disc_hinge_fence_QA`);
and the eigenvalue-level sandwich engines' `hnn` clauses screened (the
engines route every test vector through the pointwise bracket, whose
`hnn` fence carries the guard; at regular signed input the bracket is
an identity, so the eigenvalue-level violation is fixture-dependent).

**Verification:** spike first (`wip/vtfences_spike.lean` — the full
127-declaration delivery, iterated to zero errors/zero warnings over
five fix rounds, all in recorded trap classes); `lake env lean` on the
landed module (zero errors, zero warnings); explicit `lake build
Scaffold.QA.SpectralGraph.VariationalTransfer_QA` ✔; the 127-declaration
axiom audit above; **full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh artifacts,
0 stale, 0 missing, exit 0**; `lint_axioms` exit 0 (4 current axioms,
unchanged); `check_refutation_independence` (9-tag clean — no tags
touched); `check_public_reachability` clean (63 repo modules);
`check_citations` ("All axioms have proper citations!");
`check_markdown_links` clean; `check_backlog_freshness` clean;
scoreboard regenerated (**5240/4/0**) with the verification row;
map-freshness after the 5116 → 5240 stats sync in both map data tables
and SVG regeneration (49 stations, no status change — none owed). The
landing verified as a pure insertion (1126/0 in numstat, plus the three
import lines).

**Technique findings** (all five fix rounds stayed inside recorded trap
classes; two sharpenings worth recording):

1. **`norm_num` does not fold numeric sums under `Real.sqrt`** (nor
   evaluate `√4` embedded in products). The robust route: pin the
   square root through `Real.sqrt_mul_self` with a numeral-identity
   preamble (`vtf_sqrt_four : √4 = 2` via rewriting `4 = 2 * 2`), and
   for irrational entries rewrite `1/√2 = √2/2` first
   (`vtf_inv_sqrt_two`), after which every entry is polynomial in `√2`
   and `linear_combination c * (√2·√2 = 2)` closes it with an explicit
   rational coefficient.
2. **The eta-literal trap is asymmetric.** ∀-quantified degree pins
   (`vtSigAdj_deg : ∀ i, deg vtSigAdj i = 2`) rewrite under *any* index
   form; literal-indexed entry lemmas (`vtNC_00`) only match goals whose
   indices come from the same literal source — `rcases nfFin3_cases`
   (whose `fin_cases <;> simp` proof normalizes to `OfNat` literals)
   works where bare `fin_cases i` (leaving `Fin.mk` displays) does not,
   and `show` at a concrete index is the escape hatch otherwise. This
   sharpens the kernel-bridge audit's record: the trap is not about
   `fin_cases` per se but about *which* literal the rewriter and the
   goal independently normalize to.
3. `rw` cannot use `Matrix.mulVec`/`Matrix.dotProduct` equation lemmas
   (no equation theorem for `rw`); they must go through `simp only`,
   and `congrArg` results need `simp only at e` for beta-reduction
   before further rewriting.
4. `reduceIte` + `Fin.isValue` is *not* reliable on `if (0 : Fin n) = 1`
   conditions inside these matrix entry unfolds; full `simp` at the end
   of an entry computation evaluates them, and the `add_zero` +
   `Real.sqrt_zero` pair must precede it when degenerate sums appear
   under the root.
5. `omega` cannot see `Fintype.card (Fin n)` (use `decide`/`norm_num`
   for index-admissibility side goals) and never applies to
   real-valued endpoint arithmetic (`linarith` for the reals).
