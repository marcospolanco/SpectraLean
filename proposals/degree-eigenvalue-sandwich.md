# The Degree Eigenvalue Sandwich

**Status: DELIVERED 2026-08-29 (run `20260829T025710Z-run-1`) — COMPLETE; the priced follow-on (the irregular Cheeger window assembly) DELIVERED the same day (run `20260829T043741Z-run-1`) — see the record in `proposals/matrix-hoeffding-spectral-gap-estimation.md`'s follow-on section; the program is fully closed.**

## The obligation this serves

The standing handoff after the sharpened-drift delivery (2026-08-29,
`docs/EXECUTION_PLAN.md`) named the irregular/volume-weighted analogue
of the Cheeger window as the top priced follow-on, and named its
missing engine exactly: *"needs the degree bridge to
`normalizedLaplacian`"*. The delivered Cheeger window family
(`edgePerturbation_lambda2_cheeger_floor`,
`edgePerturbation_connectivity_bracket`) combs the combinatoratorial
λ₂ tail with the *regular* Cheeger pair at the `lambda2` interface;
the irregular Cheeger pair
(`cheeger_lower_bound_normalized`/`cheeger_upper_bound_normalized`)
lives at `secondEval (normalizedLaplacian A)`, and before this
delivery the two worlds had **no eigenvalue-level connection at all**
— `GraphTheory.VariationalTransfer` moved quadratic forms and
Rayleigh quotients through the congruence `√D L_sym √D = L`, but no
spectrum statement.

## The statement (delivered, proved)

With `A` symmetric nonnegative, every degree positive, `dmin ≤ deg ≤
dmax`, and `0 < dmin`, at **every** sorted index `k`:

```
evals (normalizedLaplacian A) k ≤ evals (laplacian A) k / dmin
evals (laplacian A) k / dmax    ≤ evals (normalizedLaplacian A) k
```

(`evals_normalizedLaplacian_le_div`,
`div_le_evals_normalizedLaplacian` in `GraphTheory.VariationalTransfer`),
plus the interface pair the window consumer composes with
(`secondEval_normalizedLaplacian_le_div`,
`div_le_secondEval_normalizedLaplacian` at `lambda2`/`secondEval`) and
division-free mul forms (`mul_degMin_le_lambda2`,
`lambda2_le_mul_degMax`). No connectivity hypothesis — the sandwich
holds on every positive-degree graph, matching the irregular Cheeger
pair's own hypothesis shape.

## Why no cheaper route exists (the analysis finding)

The obvious approach — transport a test vector through the degree
stretch and compare Rayleigh quotients pointwise — **cannot prove
either side**: the combinatorial variational problem constrains
`x ⊥ onesVec` while the normalized one constrains `x ⊥ √D · onesVec`,
and the substitution `x ↦ √D x` maps the first constraint to a
*degree-weighted* orthogonality (`x ⊥ D·1`), not the second. Both
one-sided pointwise arguments die on exactly this mismatch (verified
in analysis before any Lean was written: every candidate chain needs
`R_L(x)` bounded at an `x` orthogonal to the wrong vector). This is
why the statement is genuinely min–max-shaped and why the proof below
is load-bearing on the subspace Courant–Fischer machinery rather than
on the pointwise transfers the module already had.

## Route (all proved; zero axioms)

- **Pointwise bracket** (the only pointwise content, which is true):
  `R_{L_sym}(√D x) = (xᵀLx)/(∑ᵢ degᵢ xᵢ²)` (the delivered
  `rayleigh_normalizedLaplacian_degreeSqrt`), the degree-weighted
  denominator bracketed by `dmin·‖x‖²` and `dmax·‖x‖²`
  (`sum_deg_mul_sq_ge`/`_le`), and `laplacian_psd` fixing the division
  direction — giving `R_{L_sym}(√D x) ∈ [R_L(x)/dmax, R_L(x)/dmin]`
  (`rayleigh_normalizedLaplacian_le_div`,
  `rayleigh_le_mul_rayleigh_normalizedLaplacian`).
- **Subspace transport**: the degree stretch is a linear equivalence
  at positive degrees (`degreeSqrtEquiv`, inverse `1/√D`), and
  `finrank_map_eq_of_injective` carries witness subspaces across it
  with their dimension.
- **Upper side**: the combinatorial existence form
  (`exists_submodule_forall_rayleigh_le`) exhibits a `(k+1)`-dimensional
  `W₁` dominated by `λₖ(L)`; its stretch-image is again `(k+1)`-
  dimensional with every Rayleigh quotient `≤ λₖ(L)/dmin` (the
  bracket), so that value is a member of `L_sym`'s min–max dominating
  set (`evals_min_max`) and `csInf_le` closes.
- **Lower side**: every dominating value `r` of the *normalized*
  min–max set (on some `(k+1)`-dimensional `W`) yields, on the
  un-stretched preimage of `W`, a competitor vector
  (`exists_ne_mem_rayleigh_ge_of_finrank_eq`) with `λₖ(L) ≤ R_L(x) ≤
  dmax · R_{L_sym}(√D x) ≤ dmax · r`; `le_csInf` closes. (The first
  draft of this proof ran the competitor form on the *combinatorial*
  dominating set — a genuine design slip caught by elaboration: the
  dominating operator must match the min–max side. Recorded here so
  the mistake is not remade.)
- **Supporting pin**: `normalizedLaplacian_evals_zero` — the
  normalized counterpart of `laplacian_evals_zero` (bottom eigenvalue
  exactly `0` at the stretched-constants kernel vector, no
  connectivity), which every exact normalized-spectrum fixture needs.

## QA (`Scaffold/QA/SpectralGraph/DegreeSandwich_QA.lean`, +37)

- **P₃** (degrees `1, 2, 1`): the exact pin `λ₂(L_sym) = 1` by two
  independent raw computations (the `≤` side at the eigenpair witness
  `![1, 0, -1]` through `secondEval_le_rayleigh_of_ker`; the `≥` side
  by the degree-weighted zero-sum constraint algebra
  `x₀ + √2·x₁ + x₂ = 0 ⟹ q = ‖x‖² + 2x₁²` through
  `secondEval_variational_of_ker`); the upper side **attained at
  equality** (`1 = λ₂/dmin` at `dmin = 1` — a wrong constant on the
  engine's `dmin` half breaks exactly this); the lower-side instance
  at `dmax = 2` (values `1/2 ≤ 1`, the bracket's honest slack); the
  engine at a **non-second index** (`k = 2`: `3/2 ≤ 2` through
  trace-route pins on both spectra — `evals L ⟨2⟩ = 3`,
  `evals L_sym ⟨2⟩ = 2`); and the **wrong-constant pairing fence**
  (`¬(λ₂(L_sym) ≤ λ₂/dmax)`: `1 ≤ 1/2` is false — the `dmin`/`dmax`
  pairing cannot be swapped).
- **K₂ regular squeeze**: at `dmin = dmax = 1` both sides collapse to
  `2 ≤ 2` — attained on both ends (combinatorial `λ₂ = 2` by the
  kernel-plus-trace route; normalized `λ₂ = 2` joined to the delivered
  `icEdge_normLap_secondEval`).
- **The `dmin = 0` fence**: on `K₂ ⊕` isolated vertex (degrees
  `(1, 1, 0)` — the degree-floor hypothesis `∀ i, dmin ≤ deg` *still
  holds* at `dmin = 0`; only the `0 < dmin` guard fails) the
  un-guarded upper-side statement reads `λ₂(L_sym) ≤ lambda2 / 0`,
  with `λ₂(L_sym) = 1` (pinned by two raw computations: the `≤` side
  at the isolated vertex's unit vector, the `≥` side by constraint
  algebra) against `lambda2 / 0 = 0`: **refuted**. The engine's own
  positive-degree hypothesis excludes the fixture; the fence exhibits
  the junk-instantization failure mode that guard fences.

`#print axioms` on the audited declarations (engine, interfaces, and
the six headline QA lemmas): exactly `propext, Classical.choice,
Quot.sound` — pure hard crust, no axiom contact.

## Verification

Spike first (`wip/ds_spike.lean`, `wip/ds_qa_spike.lean`, every piece
iterated to zero errors/warnings before any shelf edit); explicit
`lake build` targets ✔ on `Scaffold.Mathlib.GraphTheory.VariationalTransfer`
and `Scaffold.QA.SpectralGraph.DegreeSandwich_QA`; **full `lake build` ✔
(2405/2406) immediately followed by `check_build_completeness.py` —
128 source files, 128 fresh artifacts, 0 stale, 0 missing, exit 0**;
`lint_axioms` (10, both findings allowlisted-confirmed),
`check_citations`, `check_markdown_links` pass; scoreboard regenerated
(2865 → 2902, +37); map freshness after the stats-stamp sync.

### Technique findings (small)

- `∑ i, evals hM i` at `V = Fin 3` elaborates with binder type
  `Fin (Fintype.card (Fin 3))`, so `Fin.sum_univ_three` neither `rw`s
  nor `simp`s — the recorded `Fin`-spelling trap again; the fix is the
  recorded one (a type-ascribed `have h2 : ∑ i : Fin 3, … := hsum`
  accepted by defeq, then the simp fires). omega cannot close the
  decomposed goal (ℝ facts): `linarith`.
- A bare `refine le_csInf ?_ ?_` leaves the set a metavariable and the
  `ConditionallyCompleteLattice` instance unresolvable; name the set
  (`set S := …`) and pass explicit `hne`/`hmem` terms.
- 3×3 `!![…]`-literal entries do not evaluate under
  `fin_cases; simp [fixture]` (the `vecHead (vecTail …)` stall the
  records already note); the working idiom is the `Matrix.of`-with-ℕ-if
  definition plus `simp (config := {decide := true})`.
- `mul_le_mul_of_nonneg_left/right` are side-sensitive in exactly the
  way their names say; `mul_div_assoc` in the pin is
  `a * b / c = a * (b / c)` (the `←` direction is the useful one).
- `Real.inv_mul_cancel` does not exist in the pin;
  `inv_mul_cancel₀ (by positivity)` does.

## Residuals and priced follow-on

- ~~**The irregular Cheeger window assembly** (open, priced)~~
  **DELIVERED 2026-08-29** (run `20260829T043741Z-run-1`; the delivery
  record lives in
  `proposals/matrix-hoeffding-spectral-gap-estimation.md`'s follow-on
  section, the window family's home): the window-Cheeger engine pair
  `dmin·φ²/2 ≤ λ₂(L) ≤ 2·dmax·φ` shelved beside the sandwich
  (`cheeger_{lower,upper}_bound_laplacian_of_degree_window`), plus
  `edgePerturbation_normalized_cheeger_floor` and
  `edgePerturbation_normalized_connectivity_bracket` at
  `Derived/EdgePerturbationTail.lean` — both Step-0 design questions
  settled as predicted there: the per-outcome degree bound is
  event-internal (`perturbAdmissible`), and the floor consumes the
  sandwich's lower side at the perturbed degree ceiling / the ceiling
  the upper side at the degree floor. Zero new axioms; QA +16.
- The general-`k` hypothesis-free equality at the regular cone
  (`λₖ(L_sym) = λₖ(L)/d` exactly when `dmin = dmax`) is implied by the
  squeeze but not stated as a named lemma; add it when a consumer
  asks for the exact form rather than the bracket.
