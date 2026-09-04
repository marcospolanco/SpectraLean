# The Adversarial Fence Audit of the Irregular Cheeger Family

**Status:** COMPLETE (delivered 2026-09-04 by run
`20260904T052258Z-run-1`, session `ses_f9521383fffeC9LkyZav1cZJet`;
proposal and priced fence list by run `20260904T022027Z-run-1`,
session `ses_f95d213b4ffePQ6s5Fg99s0yJM`).

**Goal.** The audit-shaped adversarial pass applied to the irregular
(volume-weighted) Cheeger program — the most-consumed unaudited cluster
in the library — closing every unfenced load-bearing clause it finds
with the repository's hypothesis-form negative-witness fences.

## Why this and why now

- **No open gate.** The Active table is all-Low (human/technical/process
  decisions this run cannot make), and every frontier the prior
  handoff names is decision- or consumer-gated — the randomized-QA
  axis (a design decision the repo's own Step-0 rules have excluded),
  the undirected `walkTVPair` join (priced, consumer-gated), the sharp
  `|λ₂| = α` layer (consumer-gated, and its equality half genuinely
  needs complex spectral theory), the reverse TV → χ² calculus (no
  consumer). Forcing one would violate the gate discipline held since
  2026-08-28. Under the center-out policy the highest-leverage safe
  increment is the next application of the audit method.
- **The audit method** (`governance/ADVERSARIAL_REVIEW.md`: "for a
  theorem with several hypotheses, reviewers should also ask whether
  each one is actually necessary, not just used by the proof as
  written"): for every hypothesis of every shelf lemma in the family,
  either produce a fixture where exactly that hypothesis fails and the
  conclusion is refuted at pinned values (a *fence*), or record why no
  fence is possible. Cross-checked against every existing fence so
  nothing is duplicated. Five precedents over the mixing cascade
  (TV/Dobrushin, lazy, entropy, Poisson-bridge, primitivity-supplier),
  each finding 7–28 genuinely unfenced clauses.
- **The substrate's leverage.** The irregular Cheeger family is the
  strategy's ring-1 namesake cluster: `cheeger_upper_bound_normalized`
  / `cheeger_lower_bound_normalized` (both retired from axiom on
  2026-08-18/23 — the heart of the "retire the mushy center"
  program), the connectivity transfer
  (`secondEval_normalizedLaplacian_pos_iff_connected`,
  `normalizedLaplacian_mulVec_eq_zero_iff`,
  `cheegerConstant_pos_of_connected`), the sweep extraction
  (`sweep_level_extract_vol`, `cheeger_sweep_cut_normalized`), the
  Fiedler instantiation (`fiedler_sweep_cut_normalized`), the λ₂
  degree-sandwich interface (`mul_degMin_le_lambda2`,
  `lambda2_le_mul_degMax`), and the degree-window pair
  (`cheeger_{lower,upper}_bound_laplacian_of_degree_window`). Its
  consumers include the edge-perturbation capstones (the window pair +
  `fiedler_sweep_cut_normalized` via
  `edgePerturbation_fiedler_sweep_cut_tail`), the Ramanujan expansion
  ceiling, and the Poincaré family. Its QA (delivered 2026-08-25/26
  with the family) predates the adversarial-review discipline and
  carries only delivery-scoped fences.

## The family audited

`VariationalTransfer.lean`'s irregular-Cheeger sections plus the
volume-extraction/attainment layer of `Cheeger.lean` they consume:
the normalized pair, `cheeger_sweep_normalized`,
`cheeger_sweep_cut_normalized`, the connectivity transfer quartet and
its consumer corollary, the Fiedler instantiation, the λ₂ sandwich
interface pair, the degree-window Cheeger pair,
`sweep_level_extract_vol`, and `cheegerConstant_attained`.

## Existing fences (cross-check, no duplication)

`IrregularCheeger_QA.lean` already carries: the easy direction's `hd`
(`icZero_degree_fence`, all-zero fixture), the hard direction's `hnn`
(`ichv_signed_fence_QA`, signed 2×2: `φ = −1`, `λ₂ = 0`), the
positivity transfer's `hconn` (`icDisc_hconn_fence`) and `hnn`
(`icSigConn_fence`), the kernel iff's `hnn`
(`icSigConn_kernel_fence`), the cut extraction's `horth`
(`vsc_cut_orth_dropped_refuted_QA`), two minority fences on the
volume co-area/boundary engines, and the PSD engine's `hpsd`
(`icFence_psd_fence`). All are cited below, none duplicated.

## Audit findings: the fence list (priced)

Each entry: the clause, the fixture, and the refuting values.

1. **`cheeger_upper_bound_normalized.hnn`** — at the existing signed
   fixture `ichSigAdj` (every other clause genuine: symmetric, degrees
   `1 = 2 − 1 > 0`, two vertices): the dropped conclusion reads
   `λ₂ = 0 ≤ 2φ = −2` — false. Reuses the pinned
   `ichSigAdj_secondEval`, `ichSigAdj_cheegerConstant`.
2. **`cheeger_sweep_normalized.horth`** — at `edgeAdj` (K₂), `f = ![1,2]`
   (the existing cut-theorem fence's own function): `∑ deg·f = 3 ≠ 0`
   fails; the dropped conclusion reads `φ²/2 = 1/2 ≤ R = 1/5` — false.
   Reuses the existing `R = 1/5` pin route.
3. **`cheeger_sweep_normalized.hf0`** — at `edgeAdj`, `f = 0` (the
   orthogonality clause trivially genuine: `∑ deg·0 = 0`): `rayleigh`
   at the zero vector is the definitional junk `0`, so the dropped
   conclusion reads `1/2 ≤ 0` — false.
4. **`cheeger_sweep_normalized.hnn`** — at `ichSigAdj`, `f = ![1,−1]`
   (degree-orthogonal: `∑ deg·f = 0`): through the congruence
   `quadForm (laplacian) = quadForm (normalizedLaplacian)` at `√D f`,
   `R = −4/2 = −2`, so the dropped conclusion reads
   `φ²/2 = 1/2 ≤ −2` — false (the PSD-broken spectral side goes
   negative while the conductance side squares back positive).
5. **`cheeger_sweep_cut_normalized.hf0`** — at `edgeAdj`, `f = 0`: the
   swept superlevel/sublevel family of a constant function contains no
   nonempty proper member at all (superlevels are `∅` or `univ`), so
   the existential conclusion fails on the *shape* clauses before the
   bound clause — a genuinely distinct witness shape from the `horth`
   fence.
6. **`cheeger_sweep_cut_normalized.hnn`** — at `ichSigAdj`,
   `f = ![1,−1]`: the swept family is exactly the two singletons, each
   of conductance `φ = −1` (boundary `−1` at unit volumes), while
   `2R = −4`, so `φ² = 1 ≤ −4` fails for every candidate.
7. **`normalizedLaplacian_mulVec_eq_zero_iff.hconn`** — at the existing
   `icDiscAdj` (two disjoint edges on `Fin 4`, degrees all `1` so
   `D = 1`): the component indicator `![1,1,0,0]` is a kernel vector
   but not a multiple of `√D·1 = 1` — the forward direction fails.
8. **`secondEval_normalizedLaplacian_eq_zero_of_not_connected.hnn`** —
   new fixture `icSigDisc4Adj` (two disjoint copies of `ichSigAdj` on
   `Fin 4`: symmetric, degrees all `1`, disconnected, one negative
   entry per block): the spectrum is `{−2, −2, 0, 0}` by four
   eigenvector witnesses, so `λ₂ = −2 ≠ 0` — the dropped conclusion
   fails. (A 2×2 signed disconnected fixture cannot serve: `λ₂` is
   always `0` there — see the non-fenceable mechanisms.)
9. **`secondEval_normalizedLaplacian_eq_zero_of_not_connected.hd`** —
   new fixture `icIsoAdj` (edge ⊕ isolated vertex on `Fin 3`,
   nonnegative, degrees `(1, 1, 0)`): the spectrum is `{0, 1, 2}` by
   three witnesses (`(1,1,0)`, `(0,0,1)`, `(1,−1,0)`), so
   `λ₂ = 1 ≠ 0` — the isolated vertex's junk `D⁻¹ᐟ² = 0` row makes
   its `L_sym` eigenvalue `1`, not `0`.
10. **`cheegerConstant_pos_of_connected.hconn`** — at `icDiscAdj`: the
    first component `{0,1}` is a nonempty proper cut of boundary `0`
    and positive volumes, so `φ = 0` and the dropped conclusion
    `0 < 0` fails.
11. **`cheegerConstant_pos_of_connected.hnn`** — new fixture
    `icNegCutAdj = !![3,1,−3; 1,0,1; −3,1,3]` on `Fin 3` (symmetric;
    degrees `(1,2,1) > 0`; connected through the positive edges
    `(0,1)`, `(1,2)`; one negative off-diagonal `(0,2) = −3`): the cut
    `{0}` has boundary `1 − 3 = −2` at unit volume, so
    `φ ≤ −2 < 0` and the dropped conclusion fails.
12. **`fiedler_sweep_cut_normalized.hnn`** — at the same `icNegCutAdj`:
    the spectrum of `L_sym` is `{−5, 0, 2}` by three witnesses
    (`(1,0,−1)` at `−5`, `(1,√2,1)` at `0`, `(1,−√2,1)` at `2`), so
    `λ₂ = 0` and the dropped conclusion demands a swept nonempty
    proper cut with `φ(S)² ≤ 0`; every cut of the fixture has
    `|φ| ≥ 1` (`φ({0}) = φ({2}) = φ({0,1}) = φ({1,2}) = −2`,
    `φ({1}) = φ({0,2}) = 1`), so it fails for every candidate. The
    Fiedler sweep vector itself is pinned up to sign through the
    1-dimensional `λ₂ = 0` eigenspace (`span (1,√2,1)`, unit norm
    `2`), whose distinct values sweep exactly the singleton `{1}` and
    its complement.
13. **`mul_degMin_le_lambda2.hdmin`** — at `edgeAdj` with `dmin = 5`
    (every degree is `1`, so `5 ≤ deg` fails): `5·λ₂(L_sym) = 10 ≤
    λ₂(L) = 2` — false. The wrong-constant fence shape: an
    understating `dmin` cannot inflate the bound, an overstating one
    does.
14. **`lambda2_le_mul_degMax.hdmax`** — at `edgeAdj` with `dmax = 1/2`:
    `λ₂(L) = 2 ≤ (1/2)·λ₂(L_sym) = 1` — false.
15. **`cheeger_lower_bound_laplacian_of_degree_window.hdmin`** — at
    `edgeAdj` with `dmin = 5`: `5·φ²/2 = 5/2 ≤ λ₂(L) = 2` — false.
16. **`cheeger_upper_bound_laplacian_of_degree_window.hdmax`** — at
    `edgeAdj` with `dmax = 1/2`: `λ₂(L) = 2 ≤ 2·(1/2)·φ = 1` — false.
17. **`sweep_level_extract_vol.hy`** — at `edgeAdj`, `y = 1`: the
    minority clause fails at `t = 1` (the superlevel is everything:
    `2·2 ≤ 2`), and the dropped conclusion demands a nonempty proper
    `S` with `φ(S)² ≤ 0/2 = 0` while `φ = 1` — false.
18. **`sweep_level_extract_vol.hM`** — at `edgeAdj`, `y = 0` (the
    minority clause trivially genuine: positive superlevels are
    empty): the bound's right side is the junk `0/0 = 0` while
    `φ = 1`, and the swept-by-`y²` sets at `t > 0` are all empty, so
    the existential fails on both clauses at once — the junk-division
    hazard class exercised at the extraction's own display.
19. **`cheegerConstant_attained.hcard`** — new fixture `icOneAdj`
    (single vertex, `Fin 1`, nonnegative): no nonempty proper subset
    of a one-element type exists, so the dropped conclusion's
    existential fails outright — the `2 ≤ card V` guard is what keeps
    the attainment statement's search space nonempty.

## Recorded non-fenceables (with mechanisms)

- **`hA` (symmetry) of every `secondEval`-displaying statement** —
  structural: `secondEval`/`evals` consume the symmetry proof in the
  statement's own well-formedness; there is no dropped-hypothesis
  statement to refute. (The sweep statements, whose `rayleigh`
  display is symmetry-free, are different — see the unresolved item.)
- **`hcard` of the `secondEval` statements** — structural in the same
  way (the `Fin (card V)` index coercion carries the proof).
- **`cheeger_lower_bound_normalized.hd`** — at any nonnegative
  hd-violating fixture the degree-zero vertex is isolated, its cut has
  `boundary = 0` and `min vol = 0`, so the junk `0/0 = 0` pins
  `φ = 0`; PSD survives (the quadratic form is block-SOS plus the
  isolated coordinate's `x_i²`), so `λ₂ ≥ 0 = φ²/2` and the dropped
  conclusion stays true — the junk-conductance collapse hazard class.
- **`cheeger_sweep_normalized.hd` and
  `cheeger_sweep_cut_normalized.hd`** — same collapse (`φ = 0`) plus,
  on the natural edge⊕isolated fixture, every swept cut satisfies the
  bound (`φ² = 1 ≤ 4 = 2R` across the degree-orthogonal family); no
  refuting fixture found in the pass, mechanism recorded.
- **`rayleigh_normalizedLaplacian_le_div.hx0` /
  `rayleigh_le_mul_rayleigh_normalizedLaplacian.hx0`** — at `x = 0`
  both Rayleigh quotients are the definitional junk `0` and the
  inequalities read `0 ≤ 0` — benign.
- **The window pair's `hpos : 0 < dmin`** — a nonpositive `dmin` makes
  the lower bound's left side nonpositive against `λ₂(L) ≥ 0`
  (PSD at nonnegative weights) — benign, bound-inflating.
- **`lambda2_le_mul_degMax.hd` and the window ceiling's `hd`** — at
  every nonnegative hd-violating fixture the isolated vertex forces ≥ 2
  support components, hence `0` is a doubly-degenerate `L`-eigenvalue,
  hence `λ₂(L) = 0` against a nonnegative right side — benign. The
  window floor's `hd` collapses identically (`φ = 0` junk).
- **`cheegerConstant_attained.hnn`** — attainment over a finite cut
  set is sign-free (`Finset.exists_min_image`); the dropped statement
  is true — proof-shaped, not truth-shaped.
- **`fiedler_sweep_cut_normalized.hconn`** — proof-shaped: on
  disconnected input a whole component is a swept-able cut of
  boundary `0`, satisfying the dropped conclusion's bound at
  `λ₂ = 0` — the statement stays true where the proof's engine
  (connectivity → `0 < λ₂` → orthogonality) breaks.
- **`fiedler_sweep_cut_normalized.hd`** — screened: at nonnegative
  weights a degree-zero vertex is isolated, contradicting `hconn`;
  no fixture isolates `hd` alone.

## Unresolved this pass (priced follow-ons)

- **`hA` of the sweep lemma and the cut theorem** (`rayleigh` is
  symmetry-free, so a dropped-hypothesis statement *exists*): the
  2-dimensional analysis closes negatively — for every nonnegative
  asymmetric 2×2 with positive degrees, the constraint-subspace
  Rayleigh quotient satisfies `R = 1 + (A₀₁ + A₁₀)/(total degree) > 1
  ≥ φ²/2`, and the constraint (`√D f ⊥ √D·1`) excludes the top
  generalized direction at every 3-dimensional candidate tried (a
  saturated-bipartite design included: the constraint forces `μ < 0`
  on the whole feasible subspace). A refutation, if one exists, needs
  the sym-part's second generalized eigenvalue near `1` together with
  a one-sided boundary ratio above `√2` — recorded, not found.
- **`hnn` of the sandwich interface (`mul_degMin_le_lambda2`,
  `lambda2_le_mul_degMax`) and the window pair**: the 2×2 case always
  reads `λ₂(L_sym) = λ₂(L) = 0` (the `√D·1` kernel forces `1` into
  the transition spectrum at any positive degree, symmetric or not);
  the congruence `L_sym = D⁻¹ᐟ²LD⁻¹ᐟ²` preserves inertia, so a
  straddling fixture needs ≥ 2 negative eigenvalues with careful
  index bookkeeping; the one 3×3 candidate computed
  (`!![0,3,−1;3,0,3;−1,3,0]`, spectra `{0,1,9}` / `{0,1/2,5/2}`)
  satisfies both clauses at every legal `dmin`/`dmax`. Priced, not
  delivered.

## QA plan (this *is* the QA)

One new section (`IrregularFences`) appended to
`Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean`: the 19 fences
above in the corpus's packaged hypothesis-refutation form (each
carrying its isolation evidence — every other clause verified genuine
— in the same declaration), plus the fixture helper pins the new
fixtures need (`icSigDisc4Adj`'s four-witness spectrum pin,
`icIsoAdj`'s three-witness pin, `icNegCutAdj`'s three-witness pin,
degree/volume/conductance pins, and the Fiedler-vector eigenspace
pin). Expected +40–70 QA declarations. No `-- @refutes` tags: these
refute *theorem* instantiations and consume nothing admitted.

## Scope and non-goals

- QA-only: no shelf declaration changes; the family's statements stay
  exactly as delivered.
- The regular Cheeger pair (`cheeger_upper_bound`/`cheeger_lower_bound`
  and the regular sweep family), the multiway family, and the degree
  sandwich proper are *not* in this audit's scope (separate families,
  separate audits if pursued).
- Zero axiom contact: the family is all hard crust; nothing here
  touches the admitted surface.

## Delivery record (2026-09-04, run `20260904T052258Z-run-1`)

**Delivered as specified** — all 19 priced fences closed with
hypothesis-form negative witnesses plus isolation companions, as one
`IrregularFences` section appended to
`Scaffold/QA/SpectralGraph/IrregularCheeger_QA.lean` (a pure
insertion, 1560 lines, zero deletions). QA 4434 → 4535 (+101 by the
generator metric; 110 new declarations: 19 fences, 17 isolation
companions, the four new fixtures `icSigDisc4Adj`, `icIsoAdj`,
`icNegCutAdj`, `icOneAdj`, and the helper pins — the signed-fixture
Rayleigh pin, the K₂ `lambda2` transfer through `evals_congr` at the
`laplacian = normalizedLaplacian` coincidence, the two-block spectrum
pin, the `icIsoAdj` PSD/kernel/mulVec/variational pins, the
`icNegCutAdj` three-eigenvector witnesses with the `√2` atom algebra,
the six dot-product pins, the three subspace-linear-independence
lemmas, the trace pin, and the kernel characterization). The sweep
statements' `hA` clauses stay priced follow-ons exactly as the survey
recorded them (the 2-dimensional analysis closes negatively; a
refutation needs a >= 3-dimensional straddling fixture not found), as
does the sandwich/window `hnn` analysis.

**Zero axiom contact** (count stays 4): `#print axioms` via
`wip/icfences_axcheck.lean` on all 110 new declarations — 104 public
plus the 5 private helpers audited transitively — every one exactly
`propext, Classical.choice, Quot.sound`. No `-- @refutes` tags: these
refute *theorem* instantiations and consume nothing admitted.

**Verification:** spike first (`wip/icfences_spike.lean` — the full
110-declaration delivery, iterated to zero errors/zero warnings before
any shelf edit); `lake env lean` on the landed module (zero errors,
zero warnings); explicit `lake build
Scaffold.QA.SpectralGraph.IrregularCheeger_QA` ✔; the 110-declaration
axiom audit above; full `lake build` ✔ immediately followed by
`check_build_completeness.py` — 133 source files, 133 fresh
artifacts, 0 stale, 0 missing, exit 0; `lint_axioms` exit 0 (4 current
axioms, unchanged; only the allowlisted-confirmed PF finding);
`check_refutation_independence` (9-tag clean — no tags touched);
`check_public_reachability` clean (63 repo modules); `check_citations`
("All axioms have proper citations!"); `check_markdown_links` clean;
`check_backlog_freshness` clean; scoreboard regenerated (4535/4/0)
with the verification row; map-freshness exit 0 after the 4434 → 4535
stats sync in both map data tables and SVG regeneration (49 stations,
no status change — none owed).

**Technique findings** (six, for the next fixture-heavy audit):

1. **The fixture-form tradeoff**: `Matrix.of fun i j => if …`-form
   fixtures resist `simp`'s Fin-literal if-decisions inside sums
   (`deg` over a variable `j` collapses into filter-card junk), while
   `!![…]` literal matrices resist entry evaluation at trailing
   positions (`Matrix.vecHead (Matrix.vecTail …)` junk at indices
   `2`/`3`). The working split for every `normalizedLaplacian` entry
   computation on literal fixtures: apply the entry-form lemma
   (`normLap_entry`) FIRST (its LHS still names the fixture), rewrite
   `deg` pins SECOND, unfold the fixture def LAST (a two-pass
   finisher; a single `simp` set containing both the entry lemma and
   the def lets the def-unfold win and blocks the entry rewrite).
2. **`evals_sum_eq_trace`'s index type is `Fin (Fintype.card V)`, and
   `Fin.sum_univ_three` cannot match `Fin (Fintype.card (Fin 3))`**
   (instance mismatch at reducible transparency; `simp only
   [Fintype.card_fin]` cannot rewrite under the dependent binder — and
   `rw` there motive-fails). The working bridge:
   `Finset.sum_fin_eq_sum_range` (its `Fin ?n` pattern matches
   anything) then `Fintype.card_fin` on the now-nondependent `range`
   argument, then `Finset.sum_range_succ`/`sum_range_one` and
   `reduceDIte`.
3. **`rw [← h]` with `h : X = 0` rewrites every `0` in the goal** —
   including numerals inside other subterms (a `2·(√2)⁻¹ = √2` pin
   attempted by `rw [← sq_sqrt]` rewrote the `2` inside `√2` itself,
   producing `√(√2·√2)` junk). The escape is `field_simp` for the
   numeric identity and `show … ; linarith/exact` for zero-flavored
   equational goals.
4. **rcases/rintro `-` cannot absorb a remaining goal-level
   conjunction** — tail conjuncts must be destructured explicitly
   (`⟨-, -⟩`), and `Finset.Nonempty` slots destructure inline
   (`⟨i₀, hi₀⟩`) rather than being named and re-obtained.
5. **linarith treats un-beta-reduced eta-wrapped Fin literals as
   distinct atoms** (`c ((fun i => i) ⟨0, ⋯⟩)` vs `c 0` — from
   `Fintype.linearIndependent_iff`'s conclusion): `rw`/`linarith` both
   fail where `exact` (defef) succeeds. State LI conclusions per case
   with `exact`, not `linarith`.
6. **`√2`-atom arithmetic splits by shape**: products
   (`(√2)⁻¹·√2`) collapse only through an explicit pin in the simp
   set; sums (`2·(√2)⁻¹ = √2`) are a *linear* equation over the two
   atoms `(√2)⁻¹` and `√2` — pass the pin to `linarith` as a
   hypothesis; `norm_num` cannot bridge them (different atoms), and
   `ring`/`ring_nf` cannot either (nonlinear atom identity).
