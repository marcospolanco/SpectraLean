# SGT Backlog

**Status:** Canonical backlog for the broad spectral-graph-theory program  
**Last reviewed:** September 4, 2026

This is the bounded, center-first backlog required by the strategy's
center-out policy. Items are ranked by concrete reuse: each names the
existing declarations it composes with, the consumers it unlocks, and
its dependency path back to the SGT center. New bridge or application
work is accepted only against an item listed here (or a revision of this
document that argues the leverage case).

**Reconciliation obligation:** whenever a delivery closes or opens a
gate this document names, update the relevant item in the same
delivery — the same records-ladder obligation `proposals/README.md`'s
Active/Delivered tables already carry. Left unreconciled, this document
drifts exactly the way it did between August 17 and September 1, 2026:
dozens of completed deliveries landed (Poincaré, the heat-variance/
mixing/entropy cascade, the spectral mixing floor) while several items'
opening framing still read "conditional," "gated," or "entirely
absent" long after those gates were satisfied. `scripts/check_backlog_freshness.py`
mechanically enforces the reviewed-date half of this (wired into the
standard verification ladder); it cannot verify that the prose itself
is accurate, only that someone has looked recently — content
reconciliation still needs an actual read.

The center today: `GraphTheory.Spectral` (Laplacians, sorted spectra,
Rayleigh forms, projectors, projector algebra — all proved where stated),
`GraphTheory.Cheeger` (normalized Laplacian, admitted Cheeger bounds),
`GraphTheory.Dynamics` + `Derived.{EventStream,ProjectorDrift}`
(retained compatibility/example package), the perturbation and
concentration bridges.

## Ranked items

### 1. Random-walk / Markov interfaces (regular case) — **delivered**

*Status:* implemented 2026-08-17 in `GraphTheory.RandomWalk` (all proved,
no axioms): `transitionMatrix`, row-stochasticity for `d`-regular graphs,
`randomWalkLaplacian`, and the two interoperability theorems
(`randomWalkLaplacian_eq_regularNormalizedLaplacian`,
`randomWalkLaplacian_eq_smul_laplacian`), QA'd at a concrete two-vertex
graph.

*Unlocks:* Markov-chain consumers of the Cheeger bounds; transfer of
combinatorial-Laplacian statements to the walk view by homogeneity; the
grounding for item 2's irregular adapters.

### 2. Weighted/normalized Laplacian interoperability (irregular case) — **delivered (core)**

*Status:* the core delivered 2026-08-17 in `GraphTheory.Normalized` (all
proved, no axioms). The recorded obstruction — no matrix square root in
the pinned Mathlib — was bypassed by the observation that only a
*diagonal* square root is needed (`Real.sqrt` per vertex):
`degreeSqrt`/`degreeInvSqrt`, the general symmetric
`normalizedLaplacian A = 1 - (1/√D) A (1/√D)`, proved symmetry, the
congruence `√D L_sym √D = laplacian A` (square roots cancel), and
agreement with `regularNormalizedLaplacian` on the regular cone. QA at a
3-vertex path (degrees 1, 2, 1) and the regular edge.

*Remaining in this item:* ~~spectral similarity transfer to the walk form~~
delivered 2026-08-17 as the proved similarity identity
`√D · L_walk · (1/√D) = L_sym` plus irregular row-stochasticity
(`walkTransitionMatrix_row_sum`); ~~the *eigenvalue-list* transfer is the
precisely named residual gap~~ — **closed 2026-08-22** (proposal
`mixing-time-bound.md` Step 1): the eigenpair-transfer section of
`GraphTheory.Normalized` conjugates eigenpairs through the similarity in
both directions, reflects the transition matrix's eigenvalues as
`1 − λ`, reconstructs every vector from the transferred eigenbasis
(`walk_eigvec_expansion`), and certifies every `walkEvals` entry a
genuine eigenvalue of `P` with an explicit nonzero witness — no
characteristic-polynomial interface needed, which is why the pinned
Mathlib's lack of one (still true, re-surveyed 2026-08-22: no
similar-matrices-share-eigenvalues lemma anywhere under
`Mathlib/LinearAlgebra/`) stopped being the obstruction it appeared to
be. The remaining open piece on this axis is the mixing-time program's
Step 3 — the geometric decay bound. **Step 2 (the ℓ²-mixing proxy) was
delivered 2026-08-22** in the new `GraphTheory.Mixing` (zero new
axioms): the scoping gate decided and recorded first (ℓ² alone, with
the weighted χ² form `∑ (ν_t − π)²/π` primary — the form in which the
decay bound is Parseval-exact — and the plain Euclidean shape a
corollary bridge), then `stationaryVec`/`walkDistribution`/
`walkDensity`/`chiSquareDistance` with the evolution interface, the
density-coordinate evolution `walkDensity_succ` consuming the Phase A
detailed-balance interface (`h_{t+1} = P *ᵥ h_t` — the coordinates the
transferred eigenbasis diagonalizes), the vanishing characterization,
the `t = 0` normalization `(π x)⁻¹ − 1`, and mass conservation. Step 3
consumes exactly this interface plus the Step-1 transfer theorems; its
new work is the matrix-power layer (`Pᵗ` on eigencomponents, induction
on `t`). **Step 3, component 1 (the decay engine) was delivered
2026-08-22** under the proposal's authorized sub-decomposition, zero
new axioms: the conjugated-power transfer
`√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)` in `Normalized` (through
the new commutation form `√D · P = (1 − L_sym) · √D` — the
matrix-power layer done, never diagonalizing the non-symmetric
power), the generic eigenaction `eigvecOf_dotProduct_one_sub_mulVec`
in the center, and in `Mixing` the eigencoordinate evolution, the
Parseval-exact decay identity, and the ℓ²(π) contraction
`∑ π ((Pᵗ g))² ≤ r^{2t} ∑ π g²` under **value-based** mode exclusion
(`eigvalOf i = 0`, not index-0 — true unconditionally on degenerate
graphs) and a hypothesis-shaped rate. QA: exact decay on the
non-bipartite K₃ (`2 → 1/2 → 1/8` at rate `1/2`), the P₃ λ* = 1
oscillation cross-check against the pinned `χ²(2) = 1`, and the
mode-hypothesis negative witness. **Component 2 (the χ² assembly) was
delivered 2026-08-22 — the program is COMPLETE**, zero new axioms:
the centered evolution `h_t − 1 = Pᵗ(h₀ − 1)` (through the new
constant fix `P *ᵥ 1 = 1`), mass conservation in the conjugated
pairing, the **connectivity kernel characterization of `L_sym`**
(the kernel transferred through the proved congruence
`√D L_sym √D = L` to the shelf's combinatorial kernel theorem, then
collapsed by mass conservation — the mode hypothesis *derived*, not
assumed), and the closing mixing bound
`chiSquareDistance_le_of_connected`:
`χ²(t, x) ≤ (λ*)^{2t} · ((π x)⁻¹ − 1)`. QA pins the bound attained
*exactly* on K₃ at `t = 1, 2`, derives the P₃ rate basis-independently
from two sum-of-squares certificates (every eigenvalue in `[0, 2]`,
no exact-spectrum computation), and refutes the connectivity-dropped
form on a triangle⊕self-loop fixture where the rate hypothesis
provably holds yet the conclusion fails (`χ²(3) = 3/8 > 3/64`).
Radar axis 5 re-scored 3.0 → 3.5 (the mixing statement's own landing).

*Update (2026-09-01): the mixing program's second wave — TV, mixing-time
objects, continuous time, entropy, both a ceiling and a floor, and the
lazy time-change.* Far
beyond the original three-step scope above, `GraphTheory.Mixing` and
the new `GraphTheory.Oversmoothing` now carry: the ℓ²→TV conversion at
the sharp classical constant and its depth-form oversmoothing ceiling;
the per-pair `effectiveResistance` refinement — the first bridge
between the electrical and mixing axes; the continuous-time analogue
(intrinsic rate, no connectivity hypothesis) with its own TV/ceiling
package, the mixing-time object `contMixingTimeFrom` (the repo's first
defined `sInf` time object), and the Poisson bridge relating continuous
and discrete walk laws; the sup-over-starts uniform `t_mix` object
(`walkMixingTime`) with LPW's Dobrushin-contraction submultiplicativity
class; **the spectral mixing floor** — the program's first lower-bound
family, via the exact eigen-component-equality route, completing a
genuine two-sided depth bracket (provably-insufficient vs.
provably-enough layers); the entropy leg (Pinsker's inequality,
entropy decay, an entropy floor), which discharges log-Sobolev's
consumer gate — see item 6's update below; and **the lazy walk**
(`proposals/lazy-walk-mixing.md`: `P_L = (P + I)/2` with the
intrinsic-rate χ²/TV/entropy family and the signless-Laplacian SOS
`μ(L_sym) ≤ 2`) — LPW ch. 5's periodicity fix, making the discrete
certificate families satisfiable on every bipartite graph (the plain
families' `r < 1` rate hypotheses are provably unsatisfiable there;
the lazy rate `1 − λ₂/2` is intrinsic and the `K₂` QA attains the
bound exactly at every time, `χ²_lazy ≡ 0`), and **the lazy mixing
time** (`proposals/lazy-mixing-time-objects.md`: the `t_mix(ε)` object
at the lazy law with the certificate/attainment package and the
intrinsic-rate spectral ceiling, the depth-form TV lazy ceiling, and
the entrywise lazy ceiling at the intrinsic rate — the plain objects'
junk corner on bipartite graphs closed by genuine lazy mixing times,
with `λ₂(L_sym) ≤ 2` capping the whole normalized spectrum; the
follow-ons' consumer gate discharged by naming the
empirical-stationary agent's bipartite setting, whose lazy extension
**is now delivered** — `proposals/empirical-lazy-stationary-sampling.md`
(2026-09-02): `Derived/EmpiricalStationary.lean`'s `LazyStationaryLimit`
section clones the empirical-stationary capstone at the lazy law with
the bias computed at the intrinsic rate `(1 − λ₂/2)^t₀` under
connectivity alone — the sampling guarantee (`n` simulated lazy
trajectories estimate `π i` to `ε` past the lazy ceiling's own depth
threshold) instantiating on exactly the bipartite class where the
plain program's certificate is provably unsatisfiable, fenced in QA).
Zero new axioms across the
entire wave; QA now 3612. See `proposals/message-passing-depth-mixing-bound.md`,
`proposals/total-variation-mixing-conversion.md`,
`proposals/continuous-time-chi-square-mixing.md`,
`proposals/entropy-mixing-pinsker.md`,
`proposals/lazy-walk-mixing.md`, and
`proposals/lazy-mixing-time-objects.md` for the full delivery records.

### 3. Expansion and cut interfaces

*Have:* `vol`, `boundary`, `conductance`, `cheegerConstant`
(volume-based), the **proved** Cheeger upper bound (easy direction,
`cheeger_upper_bound`, retired from axiom 2026-08-18 with the
`cutTestVector` interface), the **proved** Cheeger lower bound (hard
direction `cheeger_lower_bound`, retired from axiom 2026-08-23 by the
median-split route) for regular graphs; cut duality delivered 2026-08-17
(`vol_compl`, `boundary_compl`, `conductance_compl`, degenerate-cut
guards — proved; cuts are partition-valued, the interface sweep cuts
and sparsest-cut shapes assume).

*Plan:* edge-boundary and uniform-weight variants of conductance;
sparsest-cut statement shapes; cut/measure duality interfaces used by
local algorithms. Each variant must name the algorithm consumer that
needs it before admission. **The Alon–Boppana bound for d-regular
graphs** (`proposals/alon-boppana-bound.md`) — adopted 2026-08-26,
operator decision recorded in that proposal's own Gate section per its
"closes the field's most conspicuous gap next to the existing
Cheeger/expander toolkit" case; the diameter-dependent single-graph
form via Route A (Nilli's variational/test-vector method, reusing
`secondEval_variational` as its entire linear-algebra engine).

*Update (2026-08-26, Steps 0+1 delivered):* **the program's Step 0
(tree-ball spike) priced and Step 1 (the d-regularity interface)
delivered** (`proposals/alon-boppana-bound.md`, run
`20260826T215003Z-run-1`; zero new axioms, QA +14 in the new
`AlonBoppana_QA.lean`, 2506 → 2520). The new
`GraphTheory/AlonBoppana.lean`: `IsDRegular` (the shelf's `d : ℝ`
hypothesis idiom), the constant-eigenvector fact
`adjacency_mulVec_onesVec`, the AM–GM row-sum domination
`quadForm_le_of_isDRegular` (`xᵀAx ≤ d ‖x‖²`; `hnn` load-bearing,
fenced), and **the top-eigenvalue identification
`evals_last_eq_of_isDRegular`** (`evals ⟨last⟩ = d` from both sides —
eigenvalue witness + unit-eigenvector domination; load-bearing on the
sorted-spectrum API at its extremes; instances on C₄/K₂ at raw pins).
Step 0's verdict: the tree-ball hypothesis discharges as **BFS
level-cardinality equations** `#{z | dist (z, e) = j} = 2 (d−1)^j`
against `SimpleGraph.dist` on `supportGraph` (the `levE`/`levClass`/
`ballE` idiom; `Mathlib.Combinatorics.SimpleGraph.Metric` needs an
explicit import at Steps 2–3) — unit cost one distance value per
vertex-level pair (adjacency/self one-liners; j-step values need a
pre-named-Adj walk witness inline in `dist_le` — a `have`-bound walk
is opaque to `rfl` — plus the 0/1 refutations), connectivity
amortizing every reachability refutation into one lemma; Q₃ and K₃,₃
identified as the honest not-full/not-far negative fixtures.

*Update (2026-08-26, Step 2 delivered):* **the tree-ball interface is
now module-level shelf fact** (run `20260826T232419Z-run-1`; zero new
axioms, QA +19, 2520 → 2539). `GraphTheory/AlonBoppana.lean`'s new
`TreeBall` section realizes the Step-0 verdict verbatim: `levE`/
`levClass`/`ballE`, the junk-zero-honest level-0 iff and its
connected amortization, the **`IsTreeBall` cardinality predicate**
(level `j` exactly `2 (d−1)^j` vertices for `j < k`), the ball algebra
with the **layer-cake bridge `ballE_card_eq_sum`** (ball card =
geometric level sum — the Step-3 test vector's normalization input),
and `distEdge` + **`ballE_disjoint_of_lt_distEdge`** (the far-apart
condition, four-pairing triangle inequality — the Step-4
orthogonalization's separation input). QA: the C₈ full-hypothesis
positive (tree-ball instance at the antipodal edge, disjoint antipodal
balls at four rfl-verified cross distances ≥ 3 proved by short-walk
exhaustion, layer-cake cardinality by two independent routes), the C₄
wrap-around negative (`IsTreeBall` fails at radius 3 — the
qualification trap's witness), and the threshold-tightness fence (at
exactly `r + s` the balls provably intersect).

*Update (2026-08-27, Step 5 delivered — the program COMPLETE):*
**Alon–Boppana is a shelf theorem** (run `20260827T105501Z-run-1`;
zero new axioms; QA +9, 2576 → 2585). The `Packaging` section of
`GraphTheory/AlonBoppana.lean`: the `√` plumbing
`mul_sqrt_inv_eq_sqrt` (`x·√(x⁻¹) = √x`, hypothesis-free), the
**far-apart-to-diameter bridge `distEdge_le_diam`** (the Step-2
priced `ediam ≠ ⊤` blocker dissolved: finiteness-attainment
`exists_edist_eq_ediam_of_finite` + connectivity's
`edist_ne_top_iff_reachable`), the honest diameter bookkeeping
**`alonBoppana_diam_ge`** (`2(k+1)+1 ≤ diam`, i.e. `k+1 ≤ ⌊diam/2⌋`,
hypothesis-side only — the tree-ball hypothesis is never derived from
the diameter), the capstone **`alonBoppana_nilli`** —
`secondEval (d•1 − A) ≤ d − (1 + 2k√(d−1))/(k+1)` at
`ρ = √((d−1)⁻¹)`, Alon–Boppana's `2√(d−1)` barrier with the error
explicit — and the classical error shape
**`alonBoppana_nilli_classical`** (`≤ d − 2√(d−1) + 2√(d−1)/(k+1)`).
Both priced QA residuals delivered: the loop-pair fence (a loop's
level-0 class has one element; `IsTreeBall` fails and the two-vector
orthogonality fails with it) and the independent engine route at the
integer witness (`secondEval (2•1 − C₈) ≤ 2/3`, strictly stronger
than the theorem routes' `≤ 1`, fully raw arithmetic). With Steps
0–5 all pure hard crust, this item's Alon–Boppana candidate is
**closed**; the natural follow-on (the asymptotic family corollary)
needs a named d-regular family with `diam → ∞` and stays a Plan
entry until one is named.

*Update (2026-09-02, records reconciliation by a later run):* the
closing sentence above is stale — **the follow-on named its family and
was delivered 2026-09-02** (`proposals/cycle-family-alon-boppana-asymptotic.md`,
run `20260902T021120Z-run-1`, zero new axioms): the cycles `C_n` as
`cycleAdj n := SimpleGraph.toWAdj (SimpleGraph.cycleGraph n)` (Mathlib's
own cycle graph through the adapter), the **exact cycle distance
formula** `cycleAdj_dist_eq` (`dist a b = min ((b−a).val) (n −
(b−a).val)`, walk route up + ℤ-potential route down), the tree-ball and
far-apart hypotheses discharged at arbitrary scale
(`isTreeBall_cycle`, `cycleAdj_distEdge_gt`, the `4k+8` sizing buying
exactly slack `1`), and the headlines `alonBoppana_cycle`
(`secondEval (2•1 − C_{4k+8}) ≤ 1/(k+1)`, the error term
`d − 2√(d−1) = 0` at `d = 2`),
`alonBoppana_cycle_laplacian` (`λ₂ (L (C_{4k+8})) ≤ 1/(k+1)`), and
`alonBoppana_cycle_asymptotic` (`∀ ε > 0, ∃ k, λ₂ (L (C_{4k+8})) ≤ ε`)
— the program's first parametric (arbitrary-`n`) instantiation. QA
pinned at `C₁₂` at delivery, then made parametric (all-scale, the
tree-ball truth boundary bracketed at every `n`) by
`proposals/parametric-cycle-qa.md` the same day. The delivery run
updated the scoreboard, map, and README but missed this item's closing
note — this update closes that records gap; item 3's Alon–Boppana
program, follow-on included, is now fully delivered hard crust.

*Update (2026-08-27, the expansion ceiling delivered):* **the
Alon–Boppana theorem has its first theorem consumer — the composition
with the Cheeger hard direction** (run `20260827T220230Z-run-1`,
`proposals/ramanujan-expansion-ceiling.md`; zero new axioms; QA +7,
2659 → 2666). `GraphTheory/AlonBoppana.lean`'s new `ExpansionCeiling`
section: `ramanujan_expansion_ceiling` —
`cheegerConstant A ≤ √(2 (1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))))` under
exactly `alonBoppana_nilli_classical`'s hypotheses, the textbook
ceiling on expansion quality — through the operator identity
`smul_one_sub_eq_smul_regularNormalizedLaplacian` (`d • 1 − A =
d • L_sym` under regularity) and two new engine pieces in
`Spectral.lean` (`secondEval_smul_of_pos`, the exact positive-scaling
lemma by the variational route; `secondEval_congr`, the
proof-irrelevance bridge across equal operator spellings). Obstruction
scope only — the ceiling says nothing about tightness or attainment
(the separate Ramanujan-graph construction program); the QA pins
non-vacuity as strict slack on C₈ (`φ ≤ 1/4` by the exhibited
half-set cut, against the `k = 0` ceiling `√2`). The engine's
hypothesis-free generalization (`secondEval_smul` for arbitrary
symmetric `M`) stays priced: the pin has no
`eigenvalues_smul`/`charpoly_smul`, and no consumer has named it.

*Update (2026-08-27, Steps 3b + 4 delivered):* **the energy half and
the two-vector orthogonalization are shelf facts — the program has its
first eigenvalue-level statement** (runs `20260827T052400Z-run-1` and
`20260827T072423Z-run-1`; zero new axioms; QA +11 then +16, 2549 →
2560 → 2576). Step 3b's `Energy` section: the level-Lipschitz lemma
`levE_le_levE_add_one_of_adj`, the parent lemma `exists_levE_parent`
(the from-below harvest dissolving the "level sizes, not edge counts"
obstruction without strengthening `IsTreeBall`), the interior
level-sum bridge, the numerator bound `radialVec_quadForm_ge`
(`2 + 4k(d−1)ρ ≤ xᵀAx`), and the Rayleigh corollary. Step 4's
`TwoEdge` section: the equal-mass lemma `radialVec_sum_eq` (both
balls' vector masses the same function of `(d, ρ, k)`, so
`twoEdgeVec := radialVec(x,y) − radialVec(u,v)` is orthogonal to
`onesVec`), the norm identity `4 (k+1)` on disjoint radius-`k` balls,
the cross-edge elimination through the level-Lipschitz lemma at the
exact far-apart threshold `(k+1)+(k+1) < distEdge`, and the headline
**`twoEdgeVec_secondEval_le`** — `secondEval (d•1 − A) ≤ d −
(2 + 4k(d−1)ρ)/(2(k+1))` through `secondEval_le_rayleigh` at
`M = d•1 − A`. Remaining: **Step 5 only** — the
far-apart-to-diameter bridge, the `d : ℝ`/`d : ℕ` join, the `√`
packaging, and the honest diameter-dependent single-graph statement
(plus two named QA residuals: the loop-pair orthogonality fence and an
independent engine route at the integer witness — both priced and
fixtures on file).

*Update (2026-08-27, Step 3's first sub-slice delivered):* **the
radial test vector exists on the shelf with its normalization computed
exactly** (run `20260827T012700Z-run-1`; zero new axioms, QA +10,
2539 → 2549). The `RadialVector` section of
`GraphTheory/AlonBoppana.lean`: `radialVec` (Nilli's `ρ^{lev}` on the
radius-`k` edge ball, `0` outside, the d-regular-tree normalization
`ρ² = ((d−1:ℕ):ℝ)⁻¹` carried as a hypothesis), the
entry/support/nonvanishing interface, the layer-cake sum bridge
`sum_ballE_eq_sum_levels`, and **the squared-norm identity
`radialVec_dotProduct_self`** — `⟨ρ^{lev}, ρ^{lev}⟩ = 2 (k+1)`
exactly under `IsTreeBall`, the geometric growth of full levels
cancelling the vector's decay per level: the Rayleigh quotient's
denominator, the first theorem consumer of the Step-2 level machinery.
`1 < d` load-bearing at the `mul_inv_cancel₀` cancellation (at `d = 1`
the hypothesis set is junk-satisfiable at `ρ = 0` through `0⁻¹ = 0`
and the identity fails — fenced at K₂, `2 ≠ 4`). QA: the C₈ pin `4`
by two independent routes (theorem vs raw per-vertex enumeration) and
the `k = 0` pair both routes (`isTreeBall_one_of_connected`'s first
consumer). **Next: Step 3b** (the energy half — the numerator
`⟨ρ^{lev}, A ρ^{lev}⟩` against the level equations, the
level-Lipschitz property of `levE` along edges its likely first
lemma) per the proposal's one-step-per-run instruction.

*Update (2026-08-27, Step 3's second sub-slice delivered):* **the
energy half is shelf fact — Nilli's Rayleigh quotient now has both
halves** (run `20260827T052400Z-run-1`; zero new axioms, QA +11,
2549 → 2560). The `Energy` section of `GraphTheory/AlonBoppana.lean`:
the level-Lipschitz lemma `levE_le_levE_add_one_of_adj` (junk-safe
adjacency triangle at both endpoints), **the parent lemma
`exists_levE_parent`** — every level-`≥ 1` vertex has a
support-adjacent neighbor exactly one level down, no connectivity
hypothesis — whose from-below harvest dissolves the recorded
"cardinality equations give level sizes, not edge counts" obstruction
*without* strengthening `IsTreeBall`; the interior `interiorE` with
its level-sum bridge; **the numerator bound `radialVec_quadForm_ge`**
`2 + 4 k (d−1) ρ ≤ xᵀAx` under the existing tree-ball predicate plus
a `0`-or-`≥ 1` weight discipline, distinct endpoints, and a genuine
edge (both orders of the endpoint edge plus both orders of every
interior vertex's parent edge, the per-level growth cancelling the
decay); and **the Rayleigh corollary `radialVec_rayleigh_ge`**
`(2 + 4 k (d−1) ρ) / (2 (k+1)) ≤ R` — Nilli's quotient before the
Step-5 `√` packaging, the exact interface Step 4 consumes. QA: the C₈
numerator pin **tight at equality** (raw `6` vs the theorem's `2 +
4·1·1·1 = 6`, no shared mechanism), the `k = 0` pair, the Rayleigh
instance, and three fences isolating the three new hypotheses (the P₃
pseudo-edge `hedge`, the half-weight edge `h01`, the one-vertex loop
`hxy` whose junk-zero partner keeps `IsTreeBall` honest).
**Next: Step 4** (the two-vector orthogonalization at two far-apart
edges through `ballE_disjoint_of_lt_distEdge` and
`radialVec_rayleigh_ge`, concluding via `secondEval_variational`).

*Update (2026-08-29, follow-on):* **the degree eigenvalue sandwich
delivered** (`proposals/degree-eigenvalue-sandwich.md`, zero new
axioms) — the eigenvalue-level bridge the irregular family lacked:
`λₖ(laplacian A)/dmax ≤ evals (normalizedLaplacian A) k ≤
λₖ(laplacian A)/dmin` at every sorted index on arbitrary symmetric
nonnegative positive-degree graphs (`evals_normalizedLaplacian_le_div`
/ `div_le_evals_normalizedLaplacian` in `VariationalTransfer.lean`,
plus the `lambda2`/`secondEval` interface pair and mul forms, and the
supporting `normalizedLaplacian_evals_zero` pin). Pre-delivery
analysis established that no pointwise test-vector route exists (the
`x ⊥ 1` vs `x ⊥ √D·1` constraint sets mismatch under the degree
substitution), so the proof rides the subspace Courant–Fischer
machinery (`evals_min_max` with both witness forms, the degree stretch
as a linear equivalence transporting witness subspaces) — load-bearing
on the congruence, `laplacian_psd`, and the CF engine. QA +37 (the new
`DegreeSandwich_QA.lean`: the P₃ exact pin by two independent routes,
the upper side attained at equality, the wrong-constant pairing fence,
the K₂ regular squeeze tight both ends, the `k = 2` engine instance,
and the `dmin = 0` isolated-vertex junk fence). The named consumer —
the irregular analogue of the Cheeger window (composing the λ₂ tails
with this bridge and the irregular pair) — **was delivered the same
day** (run `20260829T043741Z-run-1`, record in
`proposals/matrix-hoeffding-spectral-gap-estimation.md`'s follow-on
section): the window-Cheeger engine pair
`dmin·φ²/2 ≤ λ₂(L) ≤ 2·dmax·φ`
(`cheeger_{lower,upper}_bound_laplacian_of_degree_window`) plus
`edgePerturbation_normalized_cheeger_floor` and
`edgePerturbation_normalized_connectivity_bracket` at
`Derived/EdgePerturbationTail.lean`, with the admissibility window
event-internal (`perturbAdmissible` — the Step-0 verdict: no design
restriction preserves the centered tail and the norm tail carries zero
degree information since `L(E_ω)·1 = 0` identically) and the floor
consuming the sandwich's lower side at the perturbed degree ceiling,
the ceiling the upper side at the degree floor. Zero new axioms;
QA +16 (2902 → 2918). **The window family's algorithm-facing capstone
followed the same day** (run `20260829T060601Z-run-1`, the standing
handoff's named "volume-weighted sweep extraction joined to the
normalized window's floor" composition, record in the matrix-Hoeffding
proposal's sweep-cut follow-on section):
`edgePerturbation_fiedler_sweep_cut_tail` — outside the bracket's tail
set, every admissible outcome's resampled graph is *connected* (the
floor-positivity guard `0 < dmin·φ²/2 − t` feeding the connectivity
transfer `secondEval_normalizedLaplacian_pos_iff_connected`) and
carries an explicit swept level set of its own Fiedler sweep vector at
`conductance² ≤ 2·(2·dmax·φ + t)/dmin` (`fiedler_sweep_cut_normalized`
on the resampled graph, the ceiling capping its `2λ₂` bound) — the
chain concentration → eigenvalue window → connectivity → the
spectral-partitioning sweep's cut, closed under one statement;
conditional on `matrix_hoeffding` alone. Zero new axioms;
QA +4 (2918 → 2922).

*Update (2026-08-25/26):* **the irregular (volume-weighted) Cheeger *upper*
bound delivered** (`proposals/irregular-cheeger-variational-transfer.md`
Steps 0+1, found committed-but-unindexed and pursued per priority item
0; zero new axioms): `cheeger_upper_bound_normalized` —
`secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A` on
arbitrary symmetric nonnegative positive-degree graphs, no regularity
and no connectivity — through the degree-stretched cut indicator
`√D · cutTestVector` (orthogonality to the true kernel vector `√D · 1`
by a volume identity needing no regularity), the new general-kernel
`secondEval_le_rayleigh_of_ker`, and the `VariationalTransfer`
congruence engine's first theorem consumers; QA 2067 → 2152 on the
genuinely-irregular `P₃` fixture with an independent eigenpair spectral
route and both hypothesis fences. The Step-0 verdict: definitions were
already volume-general, only the inequality was new.

*Update (2026-08-25/26, the priced follow-on program delivered):* **the
irregular Cheeger *hard* direction delivered — the full volume-weighted
pair complete** (the same proposal's deferred half, opened by run
`20260825T221207Z-run-1`, verified and recorded by continuation
`20260826T010711Z-run-1`; zero new axioms):
`cheeger_lower_bound_normalized` —
`cheegerConstant A ^ 2 / 2 ≤ secondEval (normalizedLaplacian A)` on
exactly the easy direction's hypotheses — through the `VolumeHardDirection`
machinery in `Cheeger.lean` (the volume median, the degree-weighted
coarea core, the weighted norm split; the regular family's
Cauchy–Schwarz core and fused contraction already degree-weighted and
consumed verbatim), the new general-kernel sInf engine
`secondEval_variational_of_ker` in `Spectral.lean`, and the sweep
lemma + headline in `VariationalTransfer.lean`. QA 2249 → 2280 with the
P₃ headline joined to the easy delivery's independently pinned spectral
bracket, the K₂ regular recovery, and the minority/nonnegativity fences.
**Update (2026-08-26, follow-on):** the connectivity transfer
delivered (zero new axioms): the kernel characterization
`normalizedLaplacian_mulVec_eq_zero_iff` (`ker L_sym = span √D·1` on
connected input), the Fiedler mirror
`secondEval_normalizedLaplacian_pos_of_connected`, the disconnected
converse, the packaged equivalence
`secondEval_normalizedLaplacian_pos_iff_connected`
(`0 < λ₂(L_sym) ↔ connected`), and the consumer corollary
`cheegerConstant_pos_of_connected` (`0 < φ` on connected irregular
graphs, joined to the delivered easy direction) — all in
`GraphTheory.VariationalTransfer`'s new connectivity-transfer section;
QA +50 in `IrregularCheeger_QA` (the P₃/K₂ positive joins to existing
independent pins, the disconnected two-edge negative witness with
`λ₂ = 0` by two independent routes, and the `hconn`/`hnn` fences in
proved form — the signed fixture is *connected*, isolating `hnn`
exactly). **Update (2026-08-26, follow-on):** the volume-weighted
*sweep-cut extraction* delivered (zero new axioms):
`sweep_level_extract_vol` (the per-part attainment route at the
`boundary / vol` ratio in `Cheeger.lean`'s new `VolumeSweepExtraction`
section — the explicit witness level set with
`conductance S² ≤ E'(y)/∑ deg y²`, the degree-weighted layer-cake a
clone of `coarea_core_vol`'s proof) and `cheeger_sweep_cut_normalized`
(the median assembly in `VariationalTransfer.lean`: every nonzero
degree-weighted zero-sum `f` carries a swept nonempty proper cut at
`conductance² ≤ 2 · R_{L_sym}(√D f)` — the irregular pair now returns
*the cut the spectral-partitioning sweep returns*, with no regularity,
connectivity, or cardinality hypothesis); QA +10 (2330 → 2340) with the
witness forced on irregular input, the shared cut test vector consumed
by both directions *and* the sweep, and the zero-sum fence in proved
form. *Update (2026-08-26, follow-on):* the **irregular Fiedler instantiation** delivered (zero new
axioms): `fiedler_sweep_cut_normalized` in `VariationalTransfer.lean`'s
new Fiedler-instantiation section — the normalized Fiedler interface
(`fiedlerIndexNormalized`/`fiedlerVectorNormalized`) plus the
`D^{-1/2}` pullback `fiedlerSweepVector`, composed with the delivered
sweep extraction so that on every connected symmetric nonnegative
positive-degree graph an explicit closed superlevel/sublevel cut of the
sweep vector itself satisfies `conductance S² ≤ 2 λ₂ (L_sym)` — the
family's algorithm-facing capstone at exactly the regular family's
`2λ₂/d` cone constant; the degree-weighted zero-sum constraint obtained
from the eigen-orthogonality hinge (`0 < λ₂` by the connectivity
transfer — connectivity's exact entry point). QA +9 (2340 → 2349) with
the exact pin `λ₂ (L_sym P₃) = 1` (new `≥ 1` sum-of-squares side), both
fixture instances at independent pins, the pullback hinge raw at the
concrete eigenpair, and the connectivity mechanism fenced on the
disconnected fixture. *Update (2026-08-26, later):* **the multiway easy
direction delivered** (`proposals/multiway-expansion.md`, COMPLETE, zero
new axioms; QA 2349 → 2422, `MultiwayCheeger_QA` a new file at 73 by
the generator metric). The Step-0 verdict dissolved both previously
priced obstructions at the every-family statement form: no
partition-space attainment is needed (any disjoint family certifies),
and cross-part energy is *absorbed* pointwise by `(a−b)² ≤ 2a² + 2b²` at
constant exactly 2 — not eliminated (the centering concern was an
artifact of reusing the k = 2 kernel-based engine). Delivered: the
order-statistics↔counting bridge `evals_le_of_card_eigvalOf_le` and the
general-k subspace Rayleigh–Ritz engine `evals_le_of_linearIndependent`
(both k-general, in `Spectral.lean`, with the QA spin-offs
`evals_sum_eq_trace` and `exists_eigvalOf_eq_of_mulVec_eq_smul`), plus
the application layer in the new `Multiway.lean` — the indicator energy
identity `quadForm_laplacian_partIndicator`, the absorption lemma
`laplacian_quadForm_multiwayCombination_le`, and the headlines
`cheeger_upper_bound_multiway` / `cheeger_upper_bound_multiway_conductance`:
`evals (L_sym) ⟨k−1⟩ ≤ 2 · maxᵢ boundary(Sᵢ)/vol(Sᵢ)` (resp. at
conductance) for every disjoint nonempty k-family on every symmetric
nonnegative positive-degree graph. QA at all six obligations: the tight
equalities at `k = n` on K₂ (`2 = 2·1`, both forms) and the
all-rational C₄ (`λ₄ = 2 = 2·1`, the alternating-vector + trace-`4`
pin), the P₃ non-covering family at `k = 2` (certificates from a
family that provably does not cover), the P₃ `k = 3` singleton
partition with `λ₃ = 2` pinned by trace arithmetic + the raw
eigenvector `![1, −√2, 1]`, the `k = 1` zero-constraint edge, and the
C₄ cyclic-pair **overlap fence** — every other hypothesis verified,
disjointness refuted, the dropped conclusion refuted at `2 > 1`.
**The item's remaining residue:** the multiway *hard* direction (λ_k
from below, higher-order Cheeger from above) — multi-run, gated on a
named consumer. *Update (2026-08-26, latest):* **the ρ_k
partition-minimum packaging delivered** (the multiway delivery's own
top priced follow-on, pure hard crust, zero new axioms; QA 2422 →
2444): `IsMultiwayPartition` + `maxPartConductance` +
`multiwayExpansion A k := sInf` over the k-way partitions, attainment
over the finite partition space (`Set.Nonempty.csInf_mem` at the value
set's finiteness — the every-family form made this a pure attainment
task, no new engine), the `k ≤ card V` existence supplier, and the
headline `cheeger_upper_bound_multiway_rhoK` — the classical
`λ_k ≤ 2ρ_k` statement form, the every-family theorem consumed at the
attained minimizer. QA made attainment falsifiable: the star instance
`ρ₂(C₄) = 1/2` *exact* (the adjacent-pair witness above, the headline
joined to the independently pinned `λ₂ (L_sym C₄) = 1` below — the `≤`
side by the counting bridge at two raw eigenvectors, the `≥` side by
the `(x₀+x₂)²` sum-of-squares through `secondEval_variational_of_ker`),
the minimum provably beating the diagonal partition's `1`, and the
empty-set junk fence `ρ₃(K₂) = sInf ∅ = 0` (no 3-partition of two
vertices exists) proving partition-existence load-bearing. Radar axis 4
raised 4.5 → 5.0 at the pre-recorded trigger.

*Update (2026-08-25, later the same day):* **the Hoffman-type
independence bound delivered** (`proposals/expander-independence-number-bound.md`
Steps 0+1, found committed-but-unindexed and pursued per the standing
handoff's triage instruction; zero new axioms):
`hoffman_independence_bound` — `|S| ≤ μ·n/(d+μ)` for every independent
set of a symmetric nonnegative `d`-regular positive-degree network, at
exactly `expander_mixing_lemma`'s own `μ` hypothesis. The mixing lemma
(24 declarations of proved discrepancy machinery, zero theorem
consumers until now) now carries weight — the load-bearing-growth
principle executed on this item. The new `IsIndependentSet`
(diagonal-inclusive, the reading that collapses the internal cut
weight), the collapse lemma, and the deg-univ corner fence live in
`Expander.lean` §8; QA +21 in `Expander_QA.lean` Step 5 with both
classical tight cases attained with equality (`C₄`'s bipartite pair
`2 = 2·4/(2+2)`, `K₃`'s clique singleton `1 = 1·3/(2+1)`) at the exact
Ramanujan-pinned `μ`, the whole-graph and non-independent fences, and
the `d = 0` zero-adjacency isolation proving `0 < d` load-bearing. The
spectral-diameter EML corollary remains the item's gated follow-on
(needs a named consumer per its own proposal).

*Unlocks:* cut-based algorithm interfaces; localization results that
consume random-walk returns.

### 4. Spectral algorithms (application ring)

*Gate:* items 1–3 must make the inner interfaces credible first. No new
algorithm statement is admitted until its dependency path is explicit
and its inner ring is certified.

*Candidate shapes:* spectral partitioning through `lambda2`/Fiedler
vectors — **Phase A delivered 2026-08-18** (`GraphTheory.Fiedler`:
the Fiedler-vector interface `fiedlerVector`/`fiedlerVector_eigen`,
the algebraic-connectivity certificate `lambda2_pos_of_connected`, and
the sign partition `fiedlerPartition` proved nonempty and proper on
connected graphs, all hard crust; QA computes the partition on the
`P₄` barbell to be exactly the known good cut. See
`proposals/fiedler-partitioning.md`); **Fiedler-subspace stability
delivered 2026-08-28** (`proposals/fiedler-subspace-stability-davis-kahan.md`
Step 0 verdict + Step 1: `fiedlerSubspace_stability` — the bottom-2
invariant spectral subspace of the combinatorial Laplacian moves by at
most `‖laplacian E‖/δ` under a symmetric perturbation at two-cluster
separation `δ`, the proved `davis_kahan_sin_theta`'s first
graph-theoretic consumer, closing that theorem's zero-Mathlib-consumer
valley; with `laplacian_add`/`evals_congr`/`laplacian_evals_zero` as
reusable spectrum pins — and **the Fiedler-*line* rotation delivered
the same day** (the proposal's Step 2, its payoff slice:
`fiedlerLine_stability` — the residual Fiedler-mode projector
difference `‖(P₁' − P₀') − (P₁ − P₀)‖ ≤ ‖laplacian E‖/δ` on connected
base and perturbed graphs — through the common-kernel identification
`initialProjector_laplacian_zero_eq_of_connected` (every connected
Laplacian carries the same index-0 projector; uniqueness-by-fixed-space
plus the connectivity-free fixed-space iff), making the program
complete; and **the concentration → subspace-stability pipeline
delivered 2026-08-28** (run `20260828T132541Z-run-1`:
`Derived.EdgePerturbationDrift`'s
`edgePerturbation_fiedlerSubspace_drift`/
`edgePerturbation_fiedlerLine_drift` — high-probability Fiedler
rotation under the centered Bernoulli edge design, composing
`fiedlerLine_stability` with `edgePerturbation_norm_tail` through the
packaging identity `laplacian (perturbWeight A p ω) = ∑ₑ
perturbSummand` and the new Laplacian linearity package
`laplacian_smul`/`laplacian_sum`, with the separation discharged from
the base graph's deterministic gap by the proved Weyl on the tail
event's complement — conditional on `matrix_hoeffding` via the tail
alone; see the matrix-Hoeffding proposal's follow-on delivery record).
The pipeline's priced `t/δ`-sharpened interface **delivered
2026-08-29** (run `20260829T012051Z-run-1`, the same proposal's
sharpened-interface record): the matched-threshold `s/(γ−s)` pair
`edgePerturbation_fiedlerSubspace_drift'`/`edgePerturbation_fiedlerLine_drift'`
— `eventStreamProjectorDrift`'s exact statement shape with the gap
consumed inline, the envelope-optimal instance of the `t/δ` family at
every threshold (QA proves the envelope arithmetic and the strict
improvement over a valid non-envelope instance at the same threshold);
zero new axioms, QA +10 (2855 → 2865);
**Phase B delivered 2026-08-23**
— `cheeger_cut_existence`, the classical Cheeger cut-existence
certificate: on every connected `d`-regular graph a nonempty proper
`S` exists with `conductance S ^ 2 ≤ 2 · lambda2 / d` (the recorded
operator gate dissolved by the same day's `cheeger_lower_bound`
retirement; pure hard crust, assembled from the proved sweep lemma at
the Fiedler vector, attainment of the conductance minimum, and the
Rayleigh transfer — the certificate is existential over the minimizer,
with the *swept-level-set* extraction the named strengthening
follow-on); **Phase C delivered 2026-08-24**
(`proposals/sweep-cut-extraction.md`, zero new axioms) —
`fiedler_sweep_cut`, the swept-level-set extraction itself: the
certified cut is now an *explicit closed superlevel or sublevel set of
the Fiedler vector* (the object the spectral-partitioning sweep
returns) at the same `conductance S² ≤ 2 λ₂ / d` constant, proved
through the new Cheeger-module pair `sweep_level_extract` (per-part
attainment over the finitely many positive values of `y²`, the
covering fact that every closed superlevel set equals one at an
attained value, and a non-strict layer-cake integration cloned from
`coarea_core`'s own proof, closed by Component A) and
`cheeger_sweep_cut` (the median assembly; the same constant 2 as
`cheeger_sweep` with the witness explicit — a strengthening of the
sweep lemma itself, load-bearing on the whole Step-1a/1b/1c chain).
QA (+22): the family characterized at two orthogonal `C₄` vectors (one
sweep-optimal, one honestly not), the per-part extraction forced
through its level-membership iff, the orthogonality fence refuted in
proved form on the constant vector, and the `K₂` Fiedler-value family
characterization; walk mixing through the transition spectrum.

### 5. Graph-dynamical systems (conditional)

*Only when a named SGT consumer needs them* (per strategy): diffusion /
heat flow `e^{-tL}`, consensus maps, synchronization, graph semigroups.
The retained persistence package is a compatibility example, not a
roadmap driver.

*Gate opened 2026-08-19 for the heat semigroup specifically*
(`reversibility-and-heat-semigroup.md` Phase B): an established external
field — diffusion models, heat-kernel graph signatures — accepted as the
named consumer this item requires, an operator decision on record rather
than the proposal self-authorizing. Consensus maps, synchronization, and
general graph semigroups remain gated; this opens only the heat-semigroup
instance.

*Gate strengthened 2026-08-23:* `sgt-gaps.md`, from the independent
`spectral-proof` clean-sheet rewrite project, names
`reversibility-and-heat-semigroup.md` Phase B by file path as the one
remaining Scaffold dependency it needs, with the exact interface (heat
evolution on `laplacian A`; identity/semigroup; mass conservation;
eigenmode decay with the connected-graph DC-limit consequence) matching
Phase B's Steps 1–4 verbatim. This is a real external named consumer,
not the field-level acceptance the 2026-08-19 note recorded — promoted
to High in `proposals/README.md`.

*Delivery opened 2026-08-23:* Phase B Steps 0+1 delivered as pure hard
crust in the new `GraphTheory.Heat` — the Step-0 survey (the pin's
`MatrixExponential.lean` is purpose-built norm-free, so the semigroup
step needs no ball/radius hypothesis the proposal's sketch feared) plus
`heatKernel A t := NormedSpace.exp ℝ (-(t • laplacian A))` with
symmetry under `A.IsSymm`, the hypothesis-free time-zero identity, and
the square-zero exponential collapse; zero new axioms; QA with the exact
closed form `e^{-L} = !![0,1;-1,2]` on the square-zero-Laplacian
fixture, the symmetry hypothesis refuted-on-omission, and the sign
witness.

*COMPLETE 2026-08-23:* the heat-semigroup program finished in four
zero-axiom runs — Step 2 (the hypothesis-free semigroup law through
`Matrix.exp_add_of_commute`), Step 3 (mass conservation through the
entrywise-built exponential-series convergence `expSeries_hasSum_exp`
and the kernel-vector engine, with the per-component no-leakage
witness), and Step 4 (the payoff: the eigenmode engine
`exp_mulVec_eq_smul_of_mulVec_eq_smul` consuming Step 3's convergence
at an eigenvector, mode decay `heatKernel A t *ᵥ vᵢ = e^{−t·λᵢ} • vᵢ`,
the sorted-spectrum monotonicity, the eigenbasis expansion, and the
connected-graph **DC limit** `heatKernel_mulVec_tendsto_atTop` — free
diffusion leaves only the mean `((∑ x)/|V|) • onesVec`). The external
consumer's (`sgt-gaps.md`) four-item interface is fully discharged as
hard crust; QA 1503 declarations total. Consensus maps,
synchronization, and general graph semigroups remain gated as before.

*Gate narrowly opened 2026-08-23/24 for discrete affine control
specifically:* a second `sgt-gaps.md` request (item 2) names a
finite-dimensional discrete-time convergence wrapper (`r^n → 0` lifted
to finite vectors, plus a linear affine-iteration convergence theorem)
as a requirement of the `spectral-proof` rewrite — see
`proposals/discrete-affine-convergence.md`. This is narrower than
general "consensus maps, synchronization": no graph adjacency structure
appears in the request, and it is explicitly discrete-time, not the
continuous-time ODE-trajectory case `icebox/lyapunov-stability-
formalization-gap.md` already found unsupported. Graph-structured
consensus dynamics, synchronization proper, and general graph semigroups
remain gated; this opens only the discrete-affine-convergence instance.

*Discrete-affine slice DELIVERED 2026-08-23:* both steps in one run as
pure hard crust (`proposals/discrete-affine-convergence.md` COMPLETE)
— the new `Scaffold.Mathlib.Dynamics.DiscreteAffine` (a standalone
`Dynamics` area: no graph structure in the statements, per the
proposal's scope note): `tendsto_pow_smul_atTop_nhds_zero`
(`r ^ n • x → 0` for `|r| < 1` — the pin's scalar decay fact lifted
through `Filter.Tendsto.smul_const`), `affineIteration_eq` (the closed
form), and `affineIteration_tendsto_atTop` (`x_{n+1} = (1−α) • x_n +
α • e → e` under `0 < α < 2`). Zero new axioms; stated at a general
real normed space with the consumer's `V → ℝ` shape as the instance;
QA +25 in the new `Dynamics` domain with both endpoint hypotheses
refuted-on-omission as proved non-convergence (`α = 2` oscillation,
`α = 0` constancy — complementary fixtures, each isolating exactly one
dropped hypothesis). The gate's remaining scope (graph-structured
consensus dynamics, synchronization, general graph semigroups) is
unchanged and still gated.

*Update (2026-09-01):* the heat-semigroup instance extended into the
mixing axis. `GraphTheory.Heat` now carries the walk-heat kernels
(`normalizedHeatKernel`, `walkHeatKernel`) and their variance-decay
theorems — the heat semigroup's first `λ₂` consumers — plus the
continuous-time analogue of the discrete mixing bound and the
Poissonization identity bridging continuous and discrete walk laws
(`GraphTheory.Mixing`'s Poisson-bridge section); see item 2's
2026-09-01 update above for the full account. This is still the
heat-semigroup instance the 2026-08-19 gate opened, not a broadening of
it: consensus maps, synchronization, and general graph semigroups
remain gated as before.

### 6. Thermodynamics / statistical mechanics (conditional)

*Gated on item 1–2 stability:* entropy and reversibility interfaces,
Dirichlet/functional inequalities, dissipation. No admission before the
Markov prerequisites are stable.

*2026-08-22 note:* the reversibility half of this item's named
interface set is now delivered as proved hard crust —
`GraphTheory.Stationary`'s detailed-balance layer
(`walk_detailed_balance`, `walk_detailed_balance_measure`,
`diagonal_deg_mul_walkTransitionMatrix_isSymm`,
`transitionMatrix_detailed_balance_uniform`; proposal
`proposals/reversibility-and-heat-semigroup.md` Phase A, zero new
axioms). **The entropy half is delivered too** (2026-08-22,
`proposals/finite-relative-entropy.md` — both steps, zero new axioms,
in the new `Scaffold.Mathlib.InformationTheory.Entropy`: `klDiv` and
`shannonEntropy` with Gibbs' inequality in both directions and the
entropy maximum with its equality case; backlog item 6's named
interface set is complete).

**Update (2026-08-31/2026-09-01): the inequality layer is delivered
too — this item's "what remains gated" claim above is now stale.** The
Poincaré inequality family (`proposals/poincare-inequality.md`, zero
new axioms) closed the Dirichlet/functional-inequality gap directly:
the division-free spectral-gap bound `poincare_variance_mul_le`, its
connected form, the degree-weighted normalized form, and
`spectral_gap_edge_expansion` (linear in the gap; the family's first
consumer outside `Multiway`). Heat-variance decay
(`proposals/heat-variance-decay.md`) gave the heat semigroup its first
`λ₂` consumer. The entropy leg (`proposals/entropy-mixing-pinsker.md`)
added Pinsker's inequality, entropy decay, and an entropy floor, and
explicitly discharges the log-Sobolev consumer gate: an LSI now has an
on-shelf consumer it would improve, so **adopting one is an explicit
operator decision, not a missing-machinery or missing-consumer gap.**
What remains open on this item, if anything, is only the LSI statement
itself, gated on that operator decision — not a backlog residual
waiting on consumer demand.

### 7. Combinatorial and electrical structure (radar-driven candidate)

*Radar finding (2026-08-17, [SGT Radar](7_SGT_RADAR.md)):* this axis
scores 0.5 — entirely absent (effective resistance, spanning-tree
enumeration, Kirchhoff identities). Candidate first slice: the
transfer-impedance/Multiplicity-Tree statement shape, which consumes the
already-proved Laplacian adjugate-adjacent infrastructure. **Gated:**
admit or define nothing here until a named consumer states which
identity it needs (per the center-out policy, adjacency alone does not
justify admission).

**Step 1 delivered (2026-08-18, under the proposal's 2026-08-18
re-sequenced numbering): the `SimpleGraph → WAdj` interop adapter.**
`GraphTheory.SimpleGraphAdapter` (all proved, no axioms):
`SimpleGraph.toWAdj` (defined as Mathlib's `adjMatrix ℝ`), symmetry
and nonnegativity (unlocking every `hnonneg`-hypothesized center
theorem for Mathlib graphs), degree/volume agreement plus the handshake
corollary (`vol univ = 2 * #edgeFinset`), the headline
`laplacian G.toWAdj = G.lapMatrix ℝ`, the boundary as the
crossing-edge count, the neutral re-exports of Mathlib's unweighted
kernel/reachable and component-count results, and the adapter
roundtrip `supportGraph (toWAdj G) = G` with the connected-`G` kernel
corollary. QA `SpectralGraph/SimpleGraphAdapter_QA.lean` (38
declarations): numeric agreement at the 3-vertex path and a
disconnected `Fin 4` witness where the kernel is proved ≠
`span {onesVec}` (connectivity load-bearing through the adapter).

**Step 2 delivered (2026-08-18): connectivity/kernel characterization**
(the run recorded below as "step 1" used the proposal's original
numbering): the `supportGraph` adapter (`WAdj → SimpleGraph`) plus, for
connected symmetric nonnegative weights, `ker (laplacian A) = span ℝ
{onesVec}` (`exists_const_of_laplacian_mulVec_eq_zero`,
`laplacian_mulVec_eq_zero_iff_exists_const`,
`laplacian_kernel_eq_span_onesVec`; QA in
`SpectralGraph/Connectivity_QA.lean` with connected and disconnected
witnesses). No axioms. The named consumers this unlocks:
effective-resistance well-definedness (two potential-equation solutions
differ by a kernel element, constant — proposal step 5), positivity of
`λ₂` / Fiedler interfaces (item 4), and any mixing statement (item 5).
**Step 3 delivered (2026-08-18): the kernel-equality bridge** —
`ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)` for symmetric
nonnegative weights, through the new component-form center
characterization (`laplacian_mulVec_eq_zero_iff_forall_reachable`, no
connectivity hypothesis) on the weighted side and Mathlib's
`lapMatrix_toLin'_apply_eq_zero_iff_forall_reachable` on the other. In
the same step, Mathlib's component-indexed kernel facts are inherited
for the *weighted* Laplacian: kernel dimension = number of
support-graph components (`finrank_ker_laplacian_eq_card_
supportGraph_components`) and the component-indicator basis
(`laplacian_ker_basis` + value interface `laplacian_ker_basis_apply`).
QA `SpectralGraph/KernelBridge_QA.lean` (14 declarations, reusing the
`Connectivity_QA` fixtures): connected path — bridge + dimension `1` +
single basis vector constantly `1`, coherent with the connected span
theorem; disconnected two-edge fixture — component count computed to
`2` independently of the transferred theorem (block classification +
`Nat.card_eq_two_iff`), dimension `2`, basis vectors computed to
`![1,1,0,0]`/`![0,0,1,1]`, kernel strictly larger than the constants.
No axioms. **Step 4 delivered (2026-08-18): potential solvability, the
hinge** — for connected symmetric nonnegative weights, every zero-sum
demand is solvable (`exists_laplacian_mulVec_eq_of_sum_eq_zero`) and
the unit demand `e u − e v` in particular
(`exists_laplacian_mulVec_eq_single_sub_single`). Route decision
recorded before stating (constructive eigenbasis over orthogonality;
no ready-made `range = (ker)ᗮ` lemma in the pin, and the witness
consumes the proved eigenbasis algebra plus the step-2 kernel theorem,
making it load-bearing on both). Supporting crust:
`laplacian_dotProduct_mulVec` (reciprocity),
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (unsolvability
certificates), `exists_mulVec_eq_of_zero_comp` /
`mulVec_eigvecOf_sum_apply` (spectral inversion). QA
`SpectralGraph/PotentialSolvability_QA.lean` (12 declarations):
computed potentials on the edge and 3-path, plus *proved unsolvability*
witnesses for the zero-sum hypothesis (demand `e 0` on the connected
edge) and for connectivity (zero-sum cross-component demand on the
disconnected fixture, via the indicator kernel certificate). No
axioms. **Step 5 delivered (2026-08-18): effective resistance by the
potential equation** — new `GraphTheory.Electrical` (no axioms;
Mathlib surveyed first: no effective-resistance declaration and no
pseudoinverse in the pin). The relation `IsEffectiveResistance A u v r`
(`∃ f, L *ᵥ f = e u − e v ∧ f u − f v = r`); existence from step 4;
uniqueness of `r` stated at reachability-pair strength from the
component-form kernel characterization (valid within a component of a
disconnected graph); the total function `effectiveResistance A u v : ℝ`
by classical choice with an explicit junk fallback `0`, its firing
QA-witnessed (cross-component pair on the disconnected fixture: no
value exists, function reads `0`); agreement theorems at component and
connected strength; the energy identity at solution level
(`quadForm (laplacian A) f = f u − f v`, hypothesis-free) and function
level; nonnegativity from `laplacian_psd`; hypothesis-free relation
symmetry; `R u u = 0` unconditional. QA
`SpectralGraph/EffectiveResistance_QA.lean` (17 declarations): values
computed on the unit edge (`1`) and 3-path (`2`, series edges add),
energy identity cross-checked against an independently computed
energy, junk fallback pinned, and two-distinct-potentials/one-value
same-component witnesses. **Step 6 delivered (2026-08-18): the
one-sided Dirichlet bound, completing the program** —
`effectiveResistance_ge_sq_div_quadForm` (`(f u − f v)² / energy f ≤
R u v` for any test potential of positive energy; no axioms), proved by
polarization of the PSD energy through three reusable layers:
`sq_le_mul_of_forall_zero_le_sub` (nonnegative-everywhere quadratics
have nonpositive discriminant), `quadForm_laplacian_sub_smul`
(polarization; mixed terms agree by the proved reciprocity), and
`laplacian_cauchy_schwarz` (semidefinite Cauchy–Schwarz
`(f ⬝ᵥ L g)² ≤ quadForm L f * quadForm L g`, no connectivity
hypothesis — Mathlib surveyed: the pin's only C–S is the definite
inner-product one). QA: attainment at both harmonic potentials
(edge `1/1 = 1`, path `4/2 = 2`), strictness at a non-harmonic
potential, the reverse inequality numerically refuted, and the
`0 <` energy guard witnessed on the disconnected fixture. **Remaining
in this family:** the cheap definiteness residual `R u v = 0 ↔ u = v`
(reachable pair; natural completion of nonnegativity). **Update
(2026-08-19):** the conductance-form Rayleigh monotonicity below is no
longer deferred — `effectiveResistance_le_of_le` (proposal
`electrical-flow-routing.md` step 4, `GraphTheory.ElectricalFlow`)
delivers `A ≤ B ⇒ R_B ≤ R_A` through the *flow* route (Thomson's
principle at the transferred `A`-current), which never needed the
attained-supremum Dirichlet principle; what remains deferred at
proposal level is only the Dirichlet-principle *route* (the variational
upper bound the crust keeps out of scope). **Program complete
(2026-08-19):** the flow proposal's step 5 delivered the
capacity-reinforcement packaging (`increaseConductance`,
`supportGraph_connected_of_le`, the one-hypothesis
`effectiveResistance_le_increaseConductance`), closing
`electrical-flow-routing.md` in full at zero axiom cost. **Foster's
theorem delivered (2026-08-19):** `GraphTheory.Foster`
(`proposals/spectral-graph-sparsification.md` Phase A, the top High item
after the flow program closed) proves `(∑ i, ∑ j, A i j * R i j)/2 =
card V − 1` on every connected symmetric-nonnegative network — zero
new axioms, via the pseudoinverse-free eigenbasis route (the per-pair
spectral sum, the double-sum swap, per-eigenvector Dirichlet
evaluation, and the one-kernel-index count against
`laplacian_kernel_eq_span_onesVec`), with the leverage-score
corollaries (`leverageScore`, `sum_leverageScore_eq_two`) defining the
sparsification-facing importance-sampling object; QA on `K₃`/`K₄`/`P₃`/
star witnesses the ordered-pair double-counting factor (`4 ≠ 2`,
`6 ≠ 3`) exactly as the proposal's calibration demands. **The
resistance-metric residuals delivered (2026-08-24):** the family's two
named non-gated residuals are proved in `GraphTheory.Electrical`
(`proposals/resistance-metric.md`, zero new axioms) — the **maximum
principle** for unit-demand potentials (`min (f u) (f v) ≤ f x ≤
max (f u) (f v)` by diffusion-form propagation + walk induction),
`effectiveResistance_pos_of_ne` / `effectiveResistance_eq_zero_iff`
(the definiteness residual `R u v = 0 ↔ u = v`, via the Dirichlet bound
at the indicator `e u`), and `effectiveResistance_le_add` (the
**triangle inequality** — the polarization cross term closed by the
maximum principle; the eigenbasis route provably yields only the
root-triangle, recorded in the proposal's Step 0). With nonnegativity,
symmetry, and self-distance, `effectiveResistance` is now a genuine
metric on every connected network (the classical resistance distance);
QA carries the equality case on the 3-path (`2 = 1 + 1`), the strict
case on `K₃`, and one signed fixture fencing the nonnegativity
hypothesis across all three theorems. The family's remaining items are:
Matrix–Tree, and Kirchhoff network theorems beyond the conservation
bridge — both still gated on a named consumer.

**Sparsification Step 1, Slice 1 delivered (2026-08-27,
`proposals/spectral-sparsification-via-leverage-scores.md` — the
superseding document for Phase B; pure hard crust, zero new axioms,
QA 2585 → 2609):** `Probability/BernoulliProduct.lean` — the shelf's
first concrete probability space (the independent-Bernoulli product on
`ι → Bool`), with the marginals, pairwise `IndepFun` of coordinates,
the cylinder measures, `∫ δ_e ∂μ = p e`, and the matrix-codomain
transfer layer — the clause machinery the eventual `matrix_bernstein`
consumer (the leverage-score sparsifier, Slices 2–3) and the
empirical-stationary-distribution proposal both need.

**Matrix-Hoeffding consumer delivered + all three matrix concentration
axioms repaired (2026-08-28,
`proposals/matrix-hoeffding-spectral-gap-estimation.md`; QA
2749 → 2765, zero new axioms):** the delivery's Step-0 defect check
found `matrix_hoeffding`, `matrix_bernstein`, and
`matrix_azuma_hoeffding` all inconsistent at the degenerate dimension
(`card V = 0`, `t = 0` gives the provable `1 ≤ 0`); all three repaired
in place with the `[Nonempty V]` guard, refutation records in
`Matrix_QA.lean`. `matrix_hoeffding` — the concentration family's last
zero-consumer dimension-prefactored axiom — now has its first theorem
consumer: `Derived.EdgePerturbationTail`'s
`edgePerturbation_norm_tail`/`edgePerturbation_quadForm_tail` on the
new sign-free centered Bernoulli edge-Laplacian design of
`GraphTheory.EdgePerturbation` (single-edge algebra joined to the
`rankOne` family, the PosSemidef helpers the pin lacks, every axiom
clause proved), conditional on that axiom alone. ~~The sampled-graph
packaging identity is the priced follow-on.~~ Delivered 2026-08-28 by
the pipeline run (see the Fiedler item above), and joined the same day
by **the eigenvalue-level packaging** (run `20260828T214358Z-run-1`;
QA 2830 → 2843, zero new axioms): `edgePerturbation_eval_tail` —
`μ{|λᵢ(L(A+E_ω)) − λᵢ(L A)| ≥ t} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))` at
every sorted index, the norm tail transferred to the sorted spectrum
through the *proved* Weyl inequality (the proposal's filename
namesake), with the one-sided gap-survival, the λ₂-spelled corollary,
and the uniform/existential-x quadratic-form packaging whose `x ≠ 0`
guard the QA fence proves load-bearing — the Weyl transfer pinned
*tight* at a genuine design outcome (`|4 − 2| = ‖L(E_ω)‖ = 2` on K₂,
independent routes). The proposal's priced residual list is now empty.
**The Cheeger-window consumer followed the same day** (run
`20260828T230752Z-run-1`; QA 2843 → 2855, zero new axioms): the proved
Cheeger pair transported to the combinatorial `lambda2` spelling as
public API (`cheeger_lower_bound_laplacian`/`cheeger_upper_bound_laplacian`
via `L = d • L_sym` and `secondEval_smul_of_pos`), then composed with
the λ₂ tail into the high-probability connectivity window —
`μ{λ₂(G_ω) ≤ d·φ²/2 − t} ≤ 2 d exp(…)` and the two-sided bracket at the
same constant, both Cheeger directions load-bearing on the inclusion
(the window contains the eigenvalue ball `[λ₂ − t, λ₂ + t]`); see the
proposal's Cheeger-window follow-on delivery record.

**Empirical-stationary-distribution Steps 0+1 delivered (2026-08-27,
`proposals/empirical-stationary-distribution-concentration.md`; QA
2666 → 2695, zero new axioms):** the V-valued i.i.d. product sampling
space `Probability.IIDProduct` (the BernoulliProduct construction at
an arbitrary normalized factor), the walk-law nonnegativity layer
(`walkTransitionMatrix_nonneg`/`walkDistribution_nonneg` in
`Mixing.lean`), and `Derived.EmpiricalStationary` —
**`hoeffding_empirical`'s first theorem consumer**: the fixed-time
empirical visit-frequency concentration
`P{|p̂_i(n) − ν_{t₀} i| ≥ t} ≤ 2 exp(−2nt²)`, conditional on that axiom
alone with every hypothesis clause proved hard crust, no
symmetry/connectivity/mixing hypothesis. The stationarity-limit form
(folding the mixing decay in as a bias term) is the proposal's priced
deferred Step 2.

**Sparsification Step 1, Slice 2 delivered (2026-08-27, the same
proposal; pure hard crust, zero new axioms, QA 2609 → 2632):**
`GraphTheory/Sparsification.lean` — the deterministic SS algebra, every
input the `matrix_bernstein` assembly (Slice 3) consumes: the rank-one
norm bound `‖v vᵀ‖ ≤ v ⬝ᵥ v`, the bilinear Dirichlet identity, the
eigen-coordinate edge vectors with `‖v_e‖² = w_e R_eff/2` and
`∑ v_e v_eᵀ = Π_{im L}` exactly, the Bernoulli second moment, and the
Finding-A-guarded sampling family with `∫ X_e = 0` (no connectivity
hypothesis), `‖X_e ω‖ ≤ 1/q` uniformly, `∑_e ∫ X_e X_e = Σ`, and
`‖Σ‖ ≤ 1/q` — the classical constants now proved rather than asserted.

**Sparsification Step 1, Slice 3 delivered (2026-08-27, the same
proposal — Step 1 COMPLETE, the program's payoff: `matrix_bernstein`'s
first real theorem consumer; zero new axioms consumed beyond that one,
QA 2632 → 2659):** `GraphTheory/Sparsification.lean`'s Slice-3
sections (the sampled operator `ssSampled` with the *exact pointwise*
deviation identity `ssSampled ω − Π_{im L} = ∑_e X_e ω` — the
deterministic saturation guard, no null-event caveats; the
symmetry-free norm→form transfer `‖M‖ ≤ t → |xᵀMx| ≤ t (x ⬝ᵥ x)`; the
Bool-valued summand shape closing `h_meas`/`h_indep` through the
Slice-1 transfer layer) and the new `Derived/SparsificationTail.lean`
— **`sparsification_norm_tail`**: `μ {‖S(ω) − Π_{im L}‖ ≥ t} ≤
2 d exp(−t²/(2/q + 2t/(3q)))` at the *proved* constants `R = 1/q`,
`‖Σ‖ ≤ 1/q`, Finding B's `Fin n` transport via `Fintype.equivFin` +
`Equiv.sum_comp`, no connectivity hypothesis — plus
`sparsification_quadForm_tail` (the additive eigen-coordinate
pullback). Conditional on `matrix_bernstein`, reported honestly in
`#print axioms` (the two tails and their two QA interface pins the
only bernstein-bearing declarations of the 43 audited); the
multiplicative `(1±ε)` refinement on `im Π`-coordinate vectors and
the `q ~ log n/ε²` budget corollary **were delivered 2026-08-28**
(run `20260828T183001Z-run-1`: `sparsification_multiplicative_tail` —
the field-standard "S is a (1±ε)-sparsifier" shape on the cone, via
the engine lemma `quadForm_imageProjector_eq_of_mulVec_eq` — and
`sparsification_multiplicative_budget`, the
`q ≥ (8/3)·log(2d/δ)/ε²` sample-complexity corollary at the exact
Tropp constant; zero new axioms, QA 2800 → 2808 with the cone fence
proving the `im Π` restriction load-bearing — the un-guarded pointwise
claim refuted at the all-false outcome; see the proposal's follow-on
delivery record). **The graph-vector form was delivered 2026-08-28**
(run `20260828T200603Z-run-1`): `sparsification_graph_tail` /
`sparsification_graph_budget` — `(1±ε)xᵀLx ≤ xᵀL̃(ω)x ≤ (1+ε)xᵀLx`
for every graph vector with *no* `im Π` restriction, through the
transport (on-cone by construction, `L`-isometric), claim A, and the
sampled-Laplacian form correspondence — the SS program's textbook
sentence; zero new axioms, QA 2808 → 2830 with the raw `4`/`8` pins, a
two-route correspondence join, and signed-fixture fences proving
nonnegativity load-bearing on both new engines. The proposal now has
no open follow-ons.
The assembly (Finding B's `Fin n` transport, the quadratic-form
transfer) and the proposal's three QA obligations remain Slice 3.

### 8. Directed and asymmetric graph operators (2026-08-19, axis newly opened)

*Scope decision resolved (2026-08-19):* `docs/1_STRATEGY.md`'s center-out
prioritization now covers directed graphs — see that document's
2026-08-19 note and `admit-perron-frobenius.md`'s resolved gate. Every
item 1–7 above is scoped to undirected, weighted graphs; this item is the
first to open the other side.

*Named external consumers* (`sgt-gaps.md` item 6, spot-checked
2026-08-19): PageRank-style directed Markov chains, citation/web-graph
analysis, directed community detection via the magnetic Laplacian — an
active area with no route into this backlog before today.

*Candidate first slice:* the foundational directed objects — random-walk
and asymmetric Laplacians, directed normalized Laplacians, the relation
of each back to the symmetric case — which `admit-perron-frobenius.md`'s
algebraic tool (Perron–Frobenius for irreducible nonnegative matrices)
consumes once they exist. Scope both together, per that proposal's own
note: they are two pieces of the same decision, not independent ones.
Magnetic Laplacians and Hermitian embeddings of directed graphs are a
further, separate slice — real, but do not fold into the first proposal
under this item by default.

*Update (2026-08-22):* **Step 0 + Step 1 of
`proposals/directed-graph-operators.md` delivered** (zero new axioms):
the Step-0 record made the three mandated decisions — carrier reuse (no
new type), the out-degree-symmetrized normalized-Laplacian convention
(deliberately *not* Chung's Perron-vector one, which would make the
admitted axiom a prerequisite of a definition; the two proposals are
thereby **decoupled**, PF proceeding on its own leverage case), and the
Mathlib re-survey (no directed Laplacian anywhere in the pin) — and
found that items 1 and 3 of the recommendation already exist
hypothesis-free on the undirected shelf (`deg` is the row sum =
out-degree; `walkTransitionMatrix = D⁻¹ A` and
`walkLaplacian = I − D⁻¹ A` are defined with no symmetry hypothesis).
Step 1 delivered the genuinely new layer (`GraphTheory.Directed`:
`inDeg`, the `rfl` identifications, the symmetric-cone degree
agreements, directed handshaking) plus the asymmetric-input QA
certification of the pre-existing walk operators. *Second update
(2026-08-22, same day):* **Step 2 + the Step-3 agreement brick
delivered — the proposal's Lean content is complete** (zero new
axioms): `directedNormalizedLaplacian I − ½(SAS + SAᵀS)` with
hypothesis-free symmetry, the acceptance-bar agreement with
`normalizedLaplacian` under `A.IsSymm`, and the square-root-free
conjugate `√D L_dir √D = D_out − ½(A + Aᵀ)`; QA adds the calibration
refutation (symmetric but not PSD on directed input — `quadForm` at
`!![0,4;1,0]` is `−1/2 < 0`), witnessing the boundary the item's
follow-on work (directed spectral theory via
`admit-perron-frobenius.md`) must cross. *Third update (2026-08-22,
same day):* **that follow-on's first half crossed —
`proposals/admit-perron-frobenius.md` delivered** (the scoped
admission, explicit axioms 9 → 10): `Matrix.IsIrreducible` (directed
reachability) and the admitted Horn–Johnson 8.4.4 theorem at the
irreducible-case qualification level — positive simple Perron root,
strictly positive eigenvector, positive-multiple uniqueness among
nonnegative eigenvectors, complex-spectrum domination, deliberately no
strict-dominance clause (QA's `strict_dominance_refuted_QA` exhibits
the directed 2-cycle where the strengthening dies at `|−2| = 2 = r`).
The item's named consumers — irreducible stationary distributions and
PageRank — are now unblocked as separate follow-on proposals.
*Fourth update (2026-08-24):* **the first named consumer delivered —
`proposals/irreducible-stationary-distributions.md` complete (Steps
0+1 in one run, zero new axioms): the new
`GraphTheory.IrreducibleStationary` proves existence, uniqueness up
to positive scale, the `∃!` packaging, and full support of the
stationary distribution on every irreducible nonnegative walk —
**conditional on `perron_frobenius`** through exactly two axiom
applications (the eigenvalue-identification clause pinning the walk's
Perron root to `1` at `onesVec`; the uniqueness clause), with the
transposed root pinned by a bilinear pairing and the irreducibility
transfer lemmas (`isIrreducible_transpose`,
`walkTransitionMatrix_isIrreducible`) unconditional. QA (+94) carries
the asymmetric-fixture identification, the symmetric-cone agreement
with `stationaryVec`, and the reducibility fence (both hypothesis-free
conclusions refuted in proved form). PageRank remains the second
named consumer, needing its own document.
*Fifth update (2026-08-24, same day):* **the second named consumer
delivered — `proposals/pagerank-distributions.md` complete (Steps 0+1
in one run, zero new axioms): the new `GraphTheory.PageRank` proves
existence, the `∃!`, and full support of the PageRank distribution on
reducible input — no irreducibility hypothesis anywhere — the Google
matrix's teleportation floor `(1−α)·n⁻¹` making every entry positive
so irreducibility is *derived* (`ReflTransGen.single` per pair), the
delivered consumer layer composed at `G` through the general
row-stochasticity bridge `walkTransitionMatrix M = M`, all three
theorems conditional on `perron_frobenius` with zero new axiom
contact.** QA (+89 by the generator metric, 1715 → 1804): the
reducible two-edge fixture's uniform PageRank verified completely raw
with the `∃!` join (on the fixture whose raw walk has two stationary
distributions), the asymmetric star's `(4/9, 5/18, 5/18)` verified
raw and provably distinct from the raw stationary, and both endpoint
fences refuted in proved form (`α = 1` teleportation-removed, `α = -1`
identity degeneration — row stochasticity surviving both, being
α-free). The item's named-consumer program (irreducible stationary
distributions, PageRank) is now fully delivered; what remains on the
directed axis is rate work (see the next update) and the
magnetic-Laplacian slice (separate, per this item's own scope note).
*Sixth update (2026-08-24, same day):* **the primitivity gate opened
by admission and the mixing first slice delivered —
`proposals/primitive-power-convergence.md` complete (Steps 0+1 in one
run, one new axiom, count 9 → 10):** the admitted
`LinearAlgebra.PrimitiveConvergence.primitive_power_tendsto` (Horn &
Johnson §8.5 at the row-stochastic specialization — powers of a
primitive row-stochastic matrix converge entrywise to the rank-one
stationary projector `(Pᵗ) *ᵥ x → (π ⬝ᵥ x) • 1`, given-π form, no
rate), with the unconditional transfer layer (`Matrix.IsPrimitive` as
H&J's positive-power definition, primitivity from positivity,
primitivity → irreducibility by the entry-of-power walk decomposition)
and its first consumer — the new `GraphTheory.DirectedMixing`:
`googleMatrix_isPrimitive` (the teleportation floor makes the Google
matrix primitive at `k = 1`, aperiodicity *derived* — strictly
stronger than the delivered irreducibility) and
**`pageRank_powerIteration`**, the classical PageRank algorithm as a
theorem, closing the loop with the same day's existence/`∃!` layer
(the distribution is unique *and* computable), plus the entrywise
column and walk-evolution forms. All conditional on the new axiom
**alone** — `#print axioms` verifies zero `perron_frobenius` contact.
QA (+30, 2021 → 2051, `DirectedMixing_QA` a new file): the reducible
fixture's limit pinned to the raw-verified uniform value with the
second iterate computed raw at `3/16 < 1/4`; the **2-cycle
periodicity refutation** — nonnegative, row-stochastic, *irreducible*,
stationary verified, powers provably without any limit, exactly
`hprim` isolated (the convergence-form mirror of
`strict_dominance_refuted_QA`); and the `onesVec` coherence join.
What remains on the directed mixing axis is the *rate* layer
(geometric rates need the complex spectral theory of non-symmetric
matrices — a separate future admission gated on a named consumer) and
the magnetic-Laplacian slice. *Seventh update (2026-08-25):* **that
slice delivered — `proposals/magnetic-laplacian.md` complete (Steps
0+1, zero new axioms): the new `GraphTheory.Magnetic` is the shelf's
first complex-valued object and the directed axis' third spectral
toolkit** — `magneticLaplacian A Θ := D_sym − ½(W + Wᴴ)` with
`W := A ∘ e^{iΘ}` entrywise, **Hermitian by construction
hypothesis-free** for any real possibly-asymmetric weights and any
phases (the Crucoli–Pérez–Bungert–Van Mieghem directed convention;
the single-`W` classical form derived on the symmetric/antisymmetric
cone), with the **magnetic energy identity** (hypothesis-free),
PSD on nonnegative weights, the **balanced-potential gauge
characterization** `x*Mx = 0 ↔ x_u = e^{iΘ_uv} x_v` on positive edges
(a frustrated cycle forces the kernel trivial — flux localization at
form level, no complex spectral theorem anywhere), and the zero-phase
agreement with the complexified classical Laplacian (the join with
the real shelf). QA (+16, 2051 → 2067, `Magnetic_QA` a new file): the
asymmetric-flux conjugate-pair entries and energy pin, the
frustrated-vs-consistent kernel pair (the triangle vs `K₂` at the
same `π` flux — the characterization exhibited discriminating), the
classical bridge, and the nonnegativity fence (symmetric signed input
refutes PSD, exactly `hA` isolated). The named external consumer
("directed community detection via the magnetic Laplacian") now has
its mathematical core on the shelf; the complex spectral layer
(eigenvalues of `M`, magnetic Cheeger, synchronization functionals)
is the priced follow-on when a consumer names a bound. What remains
on the directed axis is the *rate* layer and that spectral layer.
*Eighth update (2026-09-02):* **the convergence layer is no longer
admitted — `primitive_power_tendsto` retired to a proved theorem**
(`proposals/retire-primitive-power-convergence.md`, zero new axioms,
count 5 → 4): the admission's own "Replacement path" note had left
the local route unpriced, and the elementary Doeblin/Dobrushin
entrywise-range contraction (no Perron–Frobenius machinery) proves
the statement unchanged — the contraction landing as a reusable
public engine (`entryRange_mulVec_le_of_pos_entries`:
`range (Q *ᵥ y) ≤ (1 - |V|δ)·range y` for row-stochastic `Q` with
entries `≥ δ`), with the PageRank power iteration and both generic
corollaries now hard crust at `#print axioms` standard-three. The
proof's byproduct rate is the Doeblin bound — explicit but
typically loose; the *sharp* `|λ₂|`-type rate layer stays exactly
as gated above (complex spectral theory of non-symmetric matrices,
a named consumer required), and the magnetic spectral layer is
unchanged. *Ninth update (2026-09-02):* **the coarse rate layer is
now delivered at the TV level** — `proposals/doeblintv-tv-contraction-
pagerank-rate.md`: the Doeblin engine's second consumer
(`tvDistance_vecMul_le_of_pos_entries`, `TV(μ ᵥ* Q, ν ᵥ* Q) ≤
(1 − |V|δ)·TV(μ, ν)` at equal masses, hypothesis-minimal) with the
block assembly `tvDistance_vecMul_pow_le_of_pos_power` and the named
consumer **`pageRank_tvDistance_le`** — `TV(ν ᵥ* G^t, π) ≤ α^t·TV(ν,
π)`, the field-standard PageRank power-method rate, attained exactly
at every time on the periodic 2-cycle QA where the plain walk
provably never mixes. The gated remainder is unchanged and now
precisely the *sharp* layer: a sharpness theorem for general
primitive chains (`|λ₂| = α` on the Google matrix is
Haveliwala–Kamvar), the ⌈log⌉-threshold depth form, and a directed
`t_mix` object — each still gated on a named consumer. *Tenth update
(2026-09-02):* **two of those three gated items delivered — the
directed `t_mix` object and the ⌈log⌉-threshold depth form, as one
package with the consumer gate discharged by naming the empirical
PageRank capstone** (`proposals/directed-mixing-time-object.md`, zero
new axioms): `DirectedMixing.lean`'s per-start Google-walk law
`pageRankDistribution` (probability-certified), the depth form
`pageRank_tvDistance_le_of_depth`, and the object
`pageRankMixingTimeFrom` with its α-ceiling `t_mix(ε) ≤
⌈log(TV(δ_x,π)/ε)/log(1/α)⌉` (attained exactly in QA) and attainment
package; the named consumer is `Derived/EmpiricalStationary.lean`'s
**`empiricalPageRank_stationary_tail_of_depth`** — `n` simulated
random-surfer trajectories estimate `π i` to `ε` at
`2 exp(−nε²/2)` past the object's own threshold, on directed input the
only mixing route (the symmetric `evals`/`eigvecOf` toolkit being
unavailable there); plus `Mixing.lean`'s equal-mass entrywise TV
extraction `|μ i − ν i| ≤ TV(μ, ν)` (constant sharp), the directed
bias term's engine. The gated remainder narrows to precisely the
*sharp* layer: a sharpness theorem for general primitive chains
(`|λ₂| = α`, Haveliwala–Kamvar) and the directed uniform
(worst-start) twin — each still gated on a named consumer. *Eleventh
update (2026-09-02):* **the directed uniform twin delivered — the
`t_mix` object family is complete**
(`proposals/directed-uniform-mixing-time.md`, zero new axioms):
`DirectedMixing.lean`'s uniform-mixing-time section carries LPW's two
distances `d`/`d̄` at the Google law, the submultiplicativity class and
ε-escalation corollaries through `Mixing.lean`'s new **matrix-level
Dobrushin-coefficient engine** (`tvDobrushinCoeff` + the sharp
contraction `TV(μ ᵥ* Q, ν ᵥ* Q) ≤ TV(μ,ν)·δ(Q)` at equal masses +
generic power submultiplicativity — the undirected uniform delivery's
mechanism promoted from bespoke-at-the-walk-matrix to any row action,
with the pairing core promoted public from Oversmoothing-private),
the refined α-ceiling `t_mix(ε) ≤ ⌈log(d̄(0)/ε)/log(1/α)⌉` (attained
exactly in QA on the fixture where the per-start one is), and the
worst-start sampling capstone `empiricalPageRank_uniform_tail_of_depth`
— one start-independent threshold certifying `n` simulated trajectories
for every start. The gated remainder is now the *sharp* layer alone
(`|λ₂| = α`, still gated on a named consumer).
*Twelfth update (2026-09-02):* **the stationary layer left the axiom —
`perron_frobenius` now has zero non-QA consumers**
(`proposals/cesaro-stationary-existence.md`, zero new axioms): the
fourth update's conditional layer — `IrreducibleStationary`'s engine
plus its four stationary theorems, `PageRank`'s three, and every
`DirectedMixing`/empirical instantiation producing `π` through them —
was **re-proved at unchanged statements** by the elementary route the
admission's own "Replacement path" note had left unpriced: power
positivity from strong connectivity (`exists_pow_pos_of_isIrreducible`),
existence by Krylov–Bogoliubov Cesàro averaging of the orbit of `1`
over the compact simplex (`exists_cluster_stationary_of_orbit` +
`exists_nonneg_stationary_of_row_stochastic` — the latter with *no*
irreducibility, the honest scope statement), strict positivity, and
min-ratio uniqueness-up-to-scale — `#print axioms` exactly the
standard three across 37 audited declarations. The axiom itself stays
admitted at its own full statement (rootMultiplicity +
complex-domination clauses untouched, its QA still exercising it);
whether to open the §9 deprecation window is an operator decision,
flagged in `index/load_bearing_axioms.md`.
*Thirteenth update (2026-09-02):* **the directed sampling program is
now self-contained** (`proposals/selfcontained-empirical-pagerank.md`,
zero new axioms): `empiricalPageRank_tail_selfcontained_of_depth`
produces the program's target itself — `∃ π` strictly positive, mass
one, stationary at the Google walk (through the re-proved
`exists_pageRankVec`) — such that past the single
`(α, ε)`-computable display threshold `⌈log(2/ε)/log(1/α)⌉`, `n`
simulated trajectories estimate `π i` to `ε` for *every* start
simultaneously. The sibling capstones' caller-supplied `π` hypotheses
(a design forced by the PF-conditional era) are gone: the agent that
can only simulate the walk needs to know nothing about the target in
advance, closing the directed family's asymmetry against the plain
and lazy families (whose targets are definitional via `stationaryVec`).
*Fourteenth update (2026-09-02):* **the undirected plain-walk sampling
family is self-contained too, and the retired
`primitive_power_tendsto` has its first undirected consumer**
(`proposals/primitivity-supplier-plain-walk.md`, zero new axioms): the
primitivity supplier `isPrimitive_of_pow_pos_of_odd_loop` (strong
connectivity + every index on a positive 2-cycle and an odd closed
walk ⟹ `IsPrimitive`, the two-parity covering) with the walk-level
wrapper `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk`
(connected + a single odd closed walk; reversal at the `Walk` level,
`Odd p.length` the honest interface since the pinned Mathlib has no
`SimpleGraph.Bipartite`), the plain walk's first mixing rate with no
spectral certificate and no caller-supplied `r`
(`walkDistribution_tvDistance_le_of_pos_power`, the intrinsic-rate
family's non-bipartite member — complementary to the lazy family's
bipartite class), `walkDistribution_tendsto_stationaryVec`, and the
plain family's self-contained twin
`empiricalWalkDistribution_tail_selfcontained_of_depth` (`∃ t₀` past
which `n` simulated trajectories estimate `π i` to `ε` for every
start; the produced `(m, δ)` honestly existential). The sharp
`|λ₂| = α` layer and the spectral-certificate route
(non-bipartite ⟹ `λ_max(L_sym) < 2`) both remain consumer-gated
exactly as before.

*Fifteenth update (2026-09-02):* **the directed TV/Dobrushin engine
family's fence discipline is complete** — the audit-shaped pass two
consecutive handoffs named as the top unstarted frontier, executed
(`proposals/adversarial-fences-tv-dobrushin-engines.md`, QA-only, zero
axioms): `DirectedMixing_QA.lean`'s Section I supplies negative
witnesses for the seven load-bearing hypotheses the 2026-09-02
directed-rate deliveries left unfenced — the equal-mass clauses of
both TV contractions, the row-sum and nonnegativity clauses of
non-expansiveness, the row-sum clause of Dobrushin submultiplicativity,
and the zero-mass clauses of both pairing cores — each with an
isolation companion proving the refuted clause is exactly what fails
at the fixture. No gate named here opened or closed; the sharp
`|λ₂| = α` layer and the spectral-certificate route stay
consumer-gated exactly as before.

*Sixteenth update (2026-09-02):* **the lazy family's fence discipline
is complete** — the audit-shaped pass's second family
(`proposals/adversarial-fences-lazy-family.md`, QA-only, zero
axioms): `Mixing_QA.lean`'s `LazyFences` section supplies negative
witnesses for the ten load-bearing hypotheses the 2026-09-01 lazy
deliveries left unfenced — the `hd` clauses of lazy
row-stochasticity, mass conservation, and the `t = 0` χ²
normalization (zero-degree fixture), the `hnn` clauses of operator-
and law-nonnegativity (negative off-diagonal fixture), the `hA`
clauses of detailed balance, stationarity, and attainment
persistence (asymmetric fixture whose lazy law hits `π` exactly at
`t = 1` and leaves it at `t = 2`), and both certificate clauses of
the public lazy ℓ²(π) contraction engine — each with an isolation
companion; recorded non-fenceable with reasons (the headline's
connectivity clause is proof-shaped, not truth-shaped). No gate
named here opened or closed; the audit-shaped pass over the
*remaining* mixing-cascade families (entropy, Poisson bridge,
primitivity supplier) stays open with the method now twice
exercised.

*Seventeenth update (2026-09-03):* **the entropy family's fence
discipline is complete** — the audit-shaped pass's third family
(`proposals/adversarial-fences-entropy-family.md`, QA-only, zero
axioms; 28 fences, +130 QA declarations): `Entropy_QA.lean`'s Section
F and `Mixing_QA.lean`'s `EntropyFences` section supply negative
witnesses for the entropy family's 28 load-bearing clauses the
2026-09-01 entropy delivery left unfenced (the only family of the
cascade whose QA predates the adversarial-review discipline) — every
mass clause of the generic KL/entropy layer (including the
transcendental `H(1/3,…) = (4/3)·log 3 > log 4` fence at mass `4/3`
via `3⁴ > 4³`), both mass clauses of Pinsker, the decay form's rate
certificate, `hnn`/`ht` of the continuous nonnegativity plumbing
(closed-form heat kernels at a negative off-diagonal fixture and the
`K₂` backward semigroup at `t = −1`), `hA`/`hd` of continuous mass
conservation (a new asymmetric-swap fixture with an idempotent walk
Laplacian; the `zdAdj` junk-zero law), and all four analytic clauses
of the entropy floor — each with isolation companions; recorded
non-fenceable with reasons (junk log-of-negative contamination,
vacuous empty-type corners, the proof-shaped `hconn`) and three
removable-hypothesis findings (notably: the continuous nonneg `hA`
clauses — the heat kernel `e^{−t}·e^{tP}` is entrywise nonnegative
for any nonnegative `P`, symmetric or not). No gate named here opened
or closed; the Poisson-bridge and primitivity-supplier audit families
stay open with the method now thrice exercised.

*Eighteenth update (2026-09-03):* **the Poisson-bridge family's fence
discipline is complete** — the audit-shaped pass's fourth family
(`proposals/adversarial-fences-poisson-bridge-family.md`, QA-only,
zero axioms; 28 fences, +82 QA declarations): `Mixing_QA.lean`'s new
`PoissonFences` section supplies negative witnesses for the
continuous↔discrete hinge's 28 load-bearing clauses the 2026-09-01
Poisson-bridge delivery left unfenced — the simplex-diameter lemma's
four mass clauses, the head–tail split's summability clause (junk
`0 = 1`), the TV convexity bound's `hc`/`hc1` and `hν`/`hν1` (the
corpus's first **divergent-tsum junk** fences: summable weights
against growing laws junk both sides to `0`), the Poisson weight's
negative time, the `hnn` clauses of the TV ≤ 1 bound / the
adjoint-walk contraction and power twin / discrete TV monotonicity
(`3/2 → 9/2`), the `hA` clauses of the whole Poissonization identity
triple (reversibility, at the asymmetric swap), of the stationary
power, and of monotonicity at a new `asymFlowAdj` fixture
(`1/10 → 7/20`), the rate theorems' `hA` at `t = 2`
(`1 − e⁻² > 2/3`), the `ht` clauses at `t = −1` on the edge, and the
transfer corollary's `htail` on the triangle (refuted from a new
series bound `e < 3`) — each with isolation companions; sixteen
non-fenceables recorded with mechanisms (ten `hd` clauses survive on
truth as substochastic algebra; the convexity bound needs no target
structure; the factorial beats spectral growth; the transfer's `hnn`
is screened by spectral escape `> 1`), and two removable-hypothesis
findings. No gate named here opened or closed; the
primitivity-supplier audit family stays open as the cascade's last
unaudited member, with the method now four times exercised.


*Nineteenth update (2026-09-03):* **the primitivity-supplier family's
fence audit closes the adversarial re-read of the entire mixing
cascade** (`proposals/adversarial-fences-primitivity-supplier-family.md`,
`EmpiricalStationary_QA.lean`'s `PrimitivityFences` section, +197 by
the generator metric, QA-only, zero axiom contact): negative witnesses
for the supplier family's 21 unfenced load-bearing clauses — the
concatenation/bounce engines' `hnn`/seed/step clauses, the matrix-level
supplier's four hypotheses (`hreach` at the identity, `htwo` at the
directed 3-cycle permutation, `hodd` at the swap, `hnn` at the
exact-cube rotation `!![1,−3;1,1]` with `M³ = −8·1`), the walk-to-power
bridge's `hnn` (a negative-diagonal chord making `(P²) 0 2 = −5`), the
walk-level supplier's and convergence corollary's `hnn`/`hconn`/`hp`
(the negative-diagonal triangle with the `−11/4` eigenvalue closed
forms; the triangle⊕isolated-vertex fixture with identically-zero
cross-block powers and the absorbed law `δ₃ ≠ π`; `K₂`'s alternating
law), and the Doeblin rate's `hle` and `hA` — every fence with an
isolation companion, the non-fenceables recorded with mechanisms
(structural `hA`s, the certificate-screened rate `hnn`, the benign-junk
capstone corners, the plain-twin removable `hd`). The step-0 finding
that reshaped two fixtures: the support graph's adjacency demands
*positive* weights, so negative edges are not graph edges — the
negative weight must sit off the positive odd cycle (a diagonal),
which is exactly why the delivered negative-diagonal fixtures keep
every other hypothesis genuine.

*Twentieth update (2026-09-03):* **the same proposal's priced follow-on
closes the capstone's own falsification surface** — negative witnesses
for `empiricalWalkDistribution_tail_selfcontained_of_depth`'s two
deferred graph clauses (`EmpiricalStationary_QA.lean`'s
`PrimitivityFences` capstone subsection, +6, QA-only, zero axiom
contact): `hp` at `K₂` (connectivity genuine, every closed walk even —
past any threshold the even-time law from `0` is `δ₀`, the sampling
measure concentrates on the all-zero trajectory, deviation `1/2` at
full mass `1 > 2 exp(−4)`) and `hconn` at `triIso4` started at the
absorbing vertex `x = 3` (a genuine odd closed walk and every
walk-level clause genuine, but the law is `δ₃` at every time —
convergent to the wrong vector while deviation `6/7` carries full
mass), both through the point-mass cylinder helper
`toMeasure_cyl_singleton_one` — after this, every hypothesis of the
self-contained sampling theorem is fenced or recorded non-fenceable.

*Twenty-first update (2026-09-03):* **the lazy family's priced
follow-ons close the last priced QA items anywhere in the mixing
cascade** (`proposals/adversarial-fences-lazy-family.md`'s follow-on
delivery record, `Mixing_QA.lean`'s `LazyFollowOnFences` section,
+39 by the generator metric, QA-only, zero axiom contact): the
conjugated-norm contraction twin's two certificate clauses (the
√D-weighted mirrors of the delivered ℓ²(π) pair — `hrate` at the
triangle's `3/2`-mode direction with the below-mode `r = 1/8`
(`1/4 > 1/16`), `hmode` at the edge's constant zero mode with the
genuine `r = 0` (`2 > 0`), the companions reused verbatim through
`conj_twin_isolation_QA` since the two engines share the clauses
statement-identically) and the lazy `t_mix` object's `_spec`
witness-clause junk corner at the disconnected bipartite fixture
`K₂ ⊕ K₂` on `Fin 4` (the lazy-law closed form: `δ₀` at zero, the
component-stationary `(1/2,1/2,0,0)` at every positive time —
`TV = 3/4`/`1/2`, never below `1/8`, so no witness exists,
`t_mix = sInf ∅ = 0`, and the dropped-`hne` conclusion fails at
`s = 0`; every structural hypothesis genuine with connectivity
exactly the failure — laziness repairs periodicity, not
disconnection). The plain twin's junk corner was already fenced
(`k2_mix_junk_corner_QA`); the pair is complete.
The stated `(ε, n) = (1/2, 32)` adjusts the priced `(1/4, 32)`: the
latter's numeric side needs a strict `2 < exp 1` the non-strict
`Real.add_one_le_exp` engine cannot deliver, and `(1/2, 32)` closes
(`2 exp(−4) ≤ 2/5 < 1`) at the same honest deviations.

*Twenty-second update (2026-09-03):* **the spectral-certificate route
for the plain family — the frontier this item's fourteenth update
recorded as consumer-gated "exactly as before" — is delivered**
(`proposals/spectral-certificate-plain-walk.md`, zero new axioms): the
strict signless engine `eigvalOf_normalizedLaplacian_lt_two_of_odd_walk`
(connected + an odd closed walk ⟹ every `L_sym` eigenvalue `< 2`,
through the signless SOS: the `μ = 2` eigenvector unstretches to an
edge-flipping potential, zeroed by the odd walk and propagated to zero
by connectivity), the computed certificates `∃ r < 1` / `∃ r ∈ (0,1)` at
`max (1 − λ₂) (λ_max − 1)`, and the χ²/TV/entrywise max-rate joins —
the consumer gate discharged by naming the plain family's entrywise
oversmoothing ceiling (the message-passing depth setting's non-lazy
walk), the same consumer class the lazy intrinsic rate's delivery named
on the bipartite side. QA +75 (`Mixing_QA.lean`'s `SpectralCertificate`
section): the triangle's certificate `1/2` exact with the bound attained
at `χ²(1) = 1/2`; the honest `r = 0` corner at the looped triangle
(spectrum `{0,1,1}`, one-step exact mixing); the C₄ unsatisfiability
fence (alternating-mode `eigvalOf = 2` forbids every `r < 1`); and the
engine's `hnn`/`hconn` fences. The gated remainder on this item is
unchanged: the sharp `|λ₂| = α` layer alone.

*Twenty-third update (2026-09-03):* **the spectral-certificate
delivery's recorded depth-form composition is landed**
(`proposals/spectral-certificate-plain-walk.md`'s follow-on, zero new
axioms): `Oversmoothing.lean`'s
`walkDistribution_sub_stationaryVec_le_of_depth_of_odd_walk` — the
plain family's first certificate-free depth ceiling, stated at the
inflated computed rate `(max (max (1 − λ₂) (λ_max − 1)) 0 + 1)/2`
(the inflation honest: the computed rate is `0` at exactly-mixing
fixtures and depth thresholds divide by `log (1/r)`). The rate facts
proved directly from the constituents (connectivity's `0 < λ₂`, the
strict signless `λ_max < 2`, the below-gap workhorse), so nothing
depends on rcases witness unfolding. QA +17: the inflated display
pinned exact at both certificate fixtures, the ceiling instantiated
with genuinely verified thresholds at both, and the odd-walk clause
fenced load-bearing at `C₄` by the junk-threshold route — dropped,
the display saturates at `1` and the threshold hypothesis degenerates
to junk while the conclusion fails. The gated remainder is unchanged:
the sharp `|λ₂| = α` layer alone.

*Twenty-fourth update (2026-09-04):* **the depth-form delivery's
recorded two-start composition is landed too**
(`proposals/spectral-certificate-plain-walk.md`'s second follow-on,
zero new axioms): `Oversmoothing.lean`'s
`walkDistribution_sub_walkDistribution_le_of_depth_of_odd_walk` —
past *both* starts' own computed-rate thresholds, any two `t`-step
views are within `2ε` at every target vertex: the "representations
become indistinguishable" statement, certificate-free, the same
consumer the caller-certificate twin has served since 2026-08-31. QA
+6 (4428 → 4434): the true two-start values pinned at both
certificate fixtures (triangle `t = 3`, starts `0`/`1`: `1/8` inside
the certified `1`, the one-start deviations `1/12`/`1/24` in opposite
directions summing to it; looped triangle `t = 1`, every pair:
exactly `0` by one-step mixing) and the odd-walk clause fenced at
`C₄` with a **genuinely two-start witness** — opposite-parity starts
(`|0 − 1/2| = 1/2 > 2ε` at `(t, ε) = (2, 1/8)`, both thresholds
junk-satisfiable), a shape the one-start fence cannot exhibit since
same-parity starts coincide at even times. The gated remainder is
unchanged: the sharp `|λ₂| = α` layer alone.

### 9. Bounded-window ("band") Davis–Kahan (2026-08-21, opened by the Davis–Kahan Step-0/1 survey)

*Scope:* `proposals/discharge-perturbation-axioms.md`'s Davis–Kahan
survey found a purely algebraic commutator/shift proof technique
(Vershynin, *High-Dimensional Probability*, 2018, Thm 4.1.15–4.1.16;
`index/sources/vershynin_hdp.md`) that proves a Davis–Kahan-shaped bound
`‖QP‖ ≤ ‖A−B‖/δ` with no integral calculus at all — but only when both
`P` and `Q` select a *bounded* spectral window, not the half-line
threshold form `davis_kahan_sin_theta` actually states. It is explicitly
**not** a substitute for that axiom's retirement (see the proposal's
survey record for the worked-through reason: the technique needs a
containment radius `r` the half-line hypothesis does not bound). It is,
however, a different, new, axiom-free theorem in its own right.

*Named consumer / leverage:* the object model this technique needs —
two finite, `δ`-separated spectral windows — is exactly what
`GraphTheory.Band` already provides (Steps 1–4 delivered 2026-08-20/21:
two-sided bands, disjoint-band orthogonality, completeness under a
partition, the Hilbert-projection specialization). A band-form
Davis–Kahan theorem would be the first perturbation-stability result for
band projectors, and — being provable by pure finite-dimensional algebra
(operator-norm submultiplicativity, projection contractivity, spectral-
subspace invariance under a shifted operator) — is plausibly cheap
relative to the half-line case's Duhamel route.

*Candidate first slice:* state the exact theorem first (bounded interval
`I` for `A`, bounded-away set `J` for `B`, `δ`-separation) against
`GraphTheory.Band`'s existing projector definitions before writing any
proof — a Step-0 survey confirming the shelf (commutation of a
self-adjoint operator with its own spectral/band projector; contractivity;
invariance of a band under the shifted operator) is a prerequisite, per
this backlog's own admission rule. Not authorized to start inside a
Davis–Kahan Step-1/2 run — it needs its own proposal entry.

**DELIVERED 2026-08-24** (`proposals/band-davis-kahan.md` complete,
Steps 0+1 in one run; zero new axioms, count stays 9): the new
`Analysis.OperatorTheory.Perturbation.BandDavisKahan` proves
`l2OpNorm_bandProjector_mul_bandProjector_le_of_lt` / `_of_gt` —
`‖Q * P‖ ≤ ‖A − B‖ / δ` for the band projectors of two symmetric
matrices on δ-separated windows, constant 1, by the survey's algebraic
commutator/shift route (no integral, no sorting, no rank counting). The
Step-0 survey verified the shelf (PolyFilter's band component action,
Spectral's Parseval/eigenaction, Duhamel's pairing engine, Band's
idempotence/action all present) and priced two gaps, both landed: the
vector action bound `l2OpNorm_mulVec_le` (absent from the pinned
Mathlib) and the operator↔band-projector vector commutation (the
2026-08-21 survey's spike-verified fact, previously unlanded). The
proof's mathematical content, worked through in the proposal before any
Lean: the *r-cancellation* — the naive single-shift assembly strands
the window spread `+ r` (exactly the recorded catch that kills the
technique at the half-line form), and the rescue is range invariance of
`A`'s band under the shifted operator, bounding the compressed term by
`r · ‖Q * P‖ · ‖y‖` so the `r` cancels. Load-bearing on four delivered
layers at once (Band, Spectral, PolyFilter, Duhamel). QA (+20,
`Perturbation/BandDavisKahan_QA.lean`): the rotated 2×2 witness with
`‖Q * P‖` pinned from below by `1/√10` completely independently of the
theorem (eigenbasis resolution, eigen-equation direction constraints,
no `eigvecOf` value assumed) against the delivered `3/4` upper bound;
the ε = 0 commuting case attained exactly; the overlapping-window fence
refuted in proved form with every `hsep`-shaped hypothesis exhibited
impossible; the mirror orientation at δ = 1/2. *The recorded follow-on
— the difference form — was delivered later the same day (see the
update below), closing this item's named program.*

**Difference form DELIVERED 2026-08-24** (`proposals/
band-davis-kahan-difference.md` complete, Steps 0+1 in one run; zero
new axioms, count stays 9; QA +21, `BandDavisKahanDiff_QA` a new file,
total 1873): the *sin-Θ* (subspace-distance) form
`l2OpNorm_bandProjector_sub_bandProjector_le` / `_le_of_mem` —
`‖P_A(a₁,b₁] − P_B(a₂,b₂]‖ ≤ ‖A − B‖ / δ` at constant 1 for equal-rank
band projectors under one-sided eigenvalue separation (B's
out-of-window eigenvalues δ-away from A's window closure), the
interval-margin corollary covering contained windows. **The
equal-rank identity `ProjectionGap.l2OpNorm_sub_eq_of_rank_eq` —
delivered 2026-08-21 as "the Davis–Kahan Step-1 component" but never
until now consumed — carries its first weight** (the falsifiability
principle's exact use case), the engine re-runs at the complement
projector `1 − Q` (F1 and range invariance reused verbatim; the new
fact is the complement expansion), and a public rank supplier
`rank_bandProjector_eq_card` (rank = in-band eigenvalue count, via
trace and the exact `{0,1}` spectrum of a symmetric idempotent) makes
the rank hypothesis checkable. What remains on this axis: the
eigenvalue-cluster-separated generalization (closer to YWS Theorem 1's
literal shape) and the two-sided symmetric-gap form — recorded
follow-ons, not gaps in what is claimed.

## Standing decisions

- Coverage is assessed on the [SGT Radar](7_SGT_RADAR.md); scores move
  only with usable, verified coverage and are recorded with the causing
  milestone. Downstream reuse reached 3.5 on 2026-08-17
  (`GraphTheory.Stationary` consumes both `Normalized` and `RandomWalk`);
  the constraint is now breadth of reuse. Named future consumer
  candidate: spectral transfer `evals (c • M) = c • evals M` (requires
  excavation through Mathlib's `irreducible_def` eigenspace
  decomposition).
- The per-step `spectral_persistence` axiom was **deprecated
  2026-08-17** (decision closed): zero non-QA consumers, motivating use
  covered by the derived two-endpoint chain. Retained through the
  compatibility window with a migration note; removal is a later release
  decision. Do not extend its theorem family.
  **Update (2026-08-20, operator-directed): removed.** Not well-established
  math per the operator's own retirement criterion — the compatibility
  window is closed. Deleted from `Scaffold/Mathlib/GraphTheory/Dynamics.lean`
  along with its sole QA consumer
  (`persistence_zero_perturbation_QA` in `Dynamics_QA.lean`); the
  `TimeVaryingGraph`/`laplacianSequence`/`IsEventDriven` building blocks
  it shared with the derived layer are untouched and still load-bearing
  for `Derived.EventStream`/`Derived.ProjectorDrift`. Explicit axiom
  count 12 → 11. `research/archive/` mentions of the axiom under its
  original name (`spectral_persistence_under_events`) are historical
  record and were deliberately left unedited, per this repository's
  archive-immutability policy (`AGENTS.md`).
- Removed subgaussian statements (moment growth, linear combinations,
  centering, sums) are re-admitted only when a consumer names them.
- Horn–Johnson/Chung locator confirmation awaits a physical or publisher
  copy; numbers are not invented.

## Source provenance

Backlog ranking follows [Strategy](1_STRATEGY.md) (center-out, leverage
test) and the operator's 2026-08-17 broad-SGT reorientation recorded in
[AGENT_ACTIVITY.md](AGENT_ACTIVITY.md).
