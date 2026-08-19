# Spectral Graph Theory

This index maps the SGT center: Laplacians, sorted spectra, cuts and
conductance, Cheeger theory, interlacing, and event-driven dynamics.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.GraphTheory.{Spectral,SimpleGraphAdapter,Electrical,Cheeger,Dynamics}`.

## Modules and Declarations

### `Scaffold.Mathlib.GraphTheory.Spectral` (SGT center)

Real definitions: `WAdj`, `deg`, `degreeMatrix`, `laplacian`,
`quadForm`, `rayleigh`, `onesVec`, `evals` (sorted spectrum),
`lambda2`, `secondEval` (matrix-facing λ₂, without the combinatorial
`laplacian` wrap; added in the 2026-08-18 Cheeger shape repair),
`spectralGap`, `spectralProjector`, `initialProjector`,
`eigvecOf`, `eigvalOf`, `vol`, `boundary`, `conductance`,
`cheegerConstant`, `eventUpdate`, `supportGraph` (2026-08-18: the
`WAdj → SimpleGraph` adapter, `Adj i j ↔ i ≠ j ∧ 0 < A i j` — the first
bridge from the matrix-first representation to Mathlib's connectivity
API), and `padVec`/`padVecLinear` (2026-08-18: the extend-by-zero
embedding `↥S → ℝ → V → ℝ` preserving dot products, quadratic forms,
and Rayleigh quotients — the bridge through which principal-submatrix
test subspaces share the Courant–Fischer engine).

Proved theorems (no admission): `degreeMatrix_*`, `laplacian_symmetric`,
`laplacian_ones_in_kernel`, `evals_sorted`, `laplacian_quadForm`
(Dirichlet form), `laplacian_psd`, `eventUpdate_preserves_symmetry`,
`principalSubmatrix_symmetric`, `spectralProjector_symmetric`,
`conductance_nonneg`, `cheegerConstant_nonneg`,
`conductance_ge_cheegerConstant`; cut duality (2026-08-17):
`vol_compl` (volume complementarity), `boundary_compl` / `conductance_compl`
(invariance of cuts under complementation — the sweep-cut consumer
interface), `boundary_empty` / `boundary_univ` (degenerate-cut guards);
projector algebra from the Mathlib
spectral theorem (2026-08-17): `initialProjector_congr`,
`eigvecOf_inner` (eigenbasis orthonormality), `eigvecOf_complete`
(eigenbasis completeness), `spectralProjector_idempotent`,
`spectralProjector_eq_zero`, `spectralProjector_eq_one`,
`initialProjector_idempotent`; spectrum pinning tools (2026-08-18):
`lambda2_eq_secondEval` (bridge between the adjacency-facing and
matrix-facing λ₂ APIs), `evals_mem_eigvalOf` (sorted-spectrum ↔
eigenbasis connection), `eigvalOf_sum_eq_trace` (trace from the unitary
diagonalization), `eigvalOf_le_of_quadForm_nonpos` (one-sided Rayleigh
eigenvalue bound — the refutation engine of `Cheeger_QA`);
connectivity and the kernel characterization (2026-08-18):
`supportGraph_adj` (adapter interface lemma),
`eq_of_laplacian_mulVec_eq_zero_of_pos_weight` (zero Dirichlet energy
forces constancy across positive-weight edges),
`eq_of_supportGraph_walk` (walk propagation),
`exists_const_of_laplacian_mulVec_eq_zero` and
`laplacian_mulVec_eq_zero_iff_exists_const` (on a connected graph the
Laplacian kernel is exactly the constants — the converse of
`laplacian_ones_in_kernel`; proposal
`electrical-structure-crust.md` step 2 after the 2026-08-18
re-sequencing), `laplacian_mulVec_const`, and
`laplacian_kernel_eq_span_onesVec`
(`ker (mulVecLin (laplacian A)) = span ℝ {onesVec}`); the component
form (2026-08-18, proposal step 3's weighted dependency):
`laplacian_mulVec_apply` (diffusion-form entrywise action
`(L *ᵥ f) i = ∑ j, A i j * (f i - f j)` — self-loops cancel),
`laplacian_mulVec_eq_zero_of_forall_reachable`
(component-constant ⇒ kernel, entrywise; needs no connectivity), and
`laplacian_mulVec_eq_zero_iff_forall_reachable` (`L *ᵥ f = 0` iff `f`
constant on each support-graph component — the weighted counterpart
of Mathlib's unweighted iff, and the load-bearing statement behind
the kernel-equality bridge); potential solvability, the electrical
hinge (2026-08-18, proposal step 4, constructive eigenbasis route —
decision recorded in the proposal): `laplacian_dotProduct_mulVec`
(reciprocity `w ⬝ᵥ (L *ᵥ f) = (L *ᵥ w) ⬝ᵥ f`),
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (kernel vectors
certify unsolvability), `mulVec_eigvecOf_sum_apply` (entrywise action
on eigenbasis combinations) and `exists_mulVec_eq_of_zero_comp`
(constructive spectral inversion — the load-bearing consumer of the
eigenbasis algebra), `exists_laplacian_mulVec_eq_of_sum_eq_zero`
(zero-sum demands are solvable on connected graphs — existence hinge
gating effective resistance), and
`exists_laplacian_mulVec_eq_single_sub_single` (the unit demand
`e u − e v` is solvable; step 5's defining equation); the general
Courant–Fischer min–max (2026-08-18, proposal
`prove-courant-fischer.md`, proved — never admitted, no axioms):
`card_filter_eigvalOf_lt_evals_le` / `succ_le_card_filter_eigvalOf_le`
(general-`k` multiplicity pins — count-form generalizations of the
`k = 1` pins behind `lambda2_variational`), `eigvecOf_dotProduct`
(orthonormality in dot-product form), `linearIndependent_eigvecOf_finset`,
`finrank_span_eigvecOf_finset` (dimension of an eigenbasis subfamily
span = index count), `rayleigh_le_evals_of_forall_dotProduct_eq_zero` /
`evals_le_rayleigh_of_forall_dotProduct_eq_zero` (component-form
Rayleigh bounds through the proved spectral resolution),
`dotProduct_eigvecOf_eq_zero_of_mem_span` (members of an eigenbasis
span have vanishing components outside it),
`exists_submodule_forall_rayleigh_le` (existence direction: a
`(k+1)`-dimensional subspace all of whose Rayleigh quotients are at
most `evals k`), `exists_ne_mem_rayleigh_ge_of_finrank_eq` (competitor
direction: every `(k+1)`-dimensional subspace contains a nonzero test
vector with quotient at least `evals k`), and `evals_min_max` (the
packaged infimum equation — `evals k` as the min over subspaces of the
dominating Rayleigh value), all at every index with *only symmetry*
assumed.

### `Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter` (Mathlib interop adapter)

The `SimpleGraph → WAdj` direction of the bridge (2026-08-18; the
complement of `Spectral.supportGraph`), all proved, no axioms. Real
definition: `SimpleGraph.toWAdj` (a `SimpleGraph` enters the center as
its 0/1 adjacency matrix — defined as Mathlib's `adjMatrix ℝ`, so no
parallel construction can drift out of agreement).

| Declaration | Content |
|-------------|---------|
| `SimpleGraph.toWAdj_apply` | interface lemma: `G.toWAdj i j = if G.Adj i j then 1 else 0` |
| `SimpleGraph.toWAdj_symm`, `SimpleGraph.toWAdj_nonneg` | symmetry; 0/1 weights are nonnegative (unlocks every `hnonneg`-hypothesized center theorem for Mathlib graphs) |
| `deg_toWAdj` | degree agreement with Mathlib: `deg G.toWAdj i = ↑(G.degree i)` |
| `vol_toWAdj_eq_sum_degrees`, `vol_toWAdj_univ_eq_two_mul_card_edges` | volume agreement; handshake `vol univ = 2 * #edgeFinset` (Mathlib's degree-sum formula transferred) |
| `laplacian_toWAdj_eq_lapMatrix` | **headline agreement** `laplacian G.toWAdj = G.lapMatrix ℝ` — transfers every Mathlib `lapMatrix` theorem to the Scaffold side and back |
| `boundary_toWAdj_eq_sum_neighbors`, `boundary_toWAdj_eq_sum_card_neighbors` | boundary as the crossing-edge count (each crossing edge counted once, from its endpoint in `S`) |
| `laplacian_toWAdj_mulVec_eq_zero_iff_reachable` | kernel ↔ constant along Mathlib reachability (Mathlib's unweighted kernel result transferred) |
| `finrank_ker_laplacian_toWAdj` | kernel dimension = number of connected components (Mathlib's component-count result transferred) |
| `supportGraph_toWAdj_eq_self` | **adapter roundtrip** `supportGraph (toWAdj G) = G` — the two adapter directions are mutually consistent |
| `laplacian_toWAdj_kernel_eq_span_ones` | for connected `G`, the kernel is the constants line — the weighted span theorem applies to Mathlib graphs through the roundtrip |
| `supportGraphAdjDecidable` | `DecidableRel (supportGraph A hA).Adj` via `Real.decidableLT` — discharges Mathlib's `DecidableRel G.Adj` hypotheses for weighted support graphs |
| `ker_laplacian_eq_ker_supportGraph_lapMatrix` | **kernel-equality bridge (2026-08-18, proposal step 3):** `ker (laplacian A) = ker ((supportGraph A).lapMatrix ℝ)` — weights do not change the kernel; both sides are the component-constant vectors |
| `finrank_ker_laplacian_eq_card_supportGraph_components` | kernel dimension = number of support-graph components, for *weighted* graphs (Mathlib's component-count result transferred through the bridge; generalizes the connected case) |
| `laplacian_ker_basis`, `laplacian_ker_basis_apply` | component-indicator basis of the weighted kernel (Mathlib's `lapMatrix_ker_basis` transported); apply lemma: the `c`-th vector is the indicator of `c` |


Admitted axioms:

| Axiom | Description | Source |
|-------|-------------|--------|
| `lambda2_variational` | Courant–Fischer characterization of λ₂ (proved theorem since 2026-08-18; axiom retired — pre-repair symmetry-only shape refuted in QA) | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md), [Chung](../sources/chung_spectral_graph.md) |
| `eigen_interlacing_principal_submatrix` | Cauchy interlacing for principal submatrices (proved theorem since 2026-08-18; axiom retired — a pure proof task from the proved Courant–Fischer engine, whose first named consumer it is) | [Horn & Johnson](../sources/horn_johnson_matrix_analysis.md) |

### `Scaffold.Mathlib.GraphTheory.Electrical` (effective resistance)

Effective resistance defined by the potential equation (2026-08-18,
proposal `electrical-structure-crust.md` step 5; Mathlib surveyed
first — no resistance declaration, no pseudoinverse in the pin). All
proved, no axioms. Real definitions: `IsEffectiveResistance A u v r`
(the relation: a potential `f` solves `laplacian A *ᵥ f = e u − e v`
with `f u − f v = r`) and the total function `effectiveResistance A u
v : ℝ` (classical choice over the relation, junk value `0` when no
value exists — the fallback's firing is QA-witnessed, not hidden).

| Declaration | Content |
|-------------|---------|
| `isEffectiveResistance_self_iff` | diagonal fully characterized, no hypotheses: `IsEffectiveResistance A u u r ↔ r = 0` |
| `isEffectiveResistance_symm` | relation symmetry with **no hypotheses** (negate the potential) |
| `exists_isEffectiveResistance` | existence on connected graphs — consumes the step-4 solvability theorem |
| `isEffectiveResistance_unique_of_reachable` | uniqueness of `r` at reachability-pair strength (two solutions differ by a component-constant kernel vector) — consumes the component-form kernel characterization |
| `isEffectiveResistance_unique` | the connected corollary |
| `effectiveResistance_eq_zero_of_not_exists` | the junk branch, stated: value `0` when the relation is unsatisfiable |
| `effectiveResistance_eq_of_reachable`, `effectiveResistance_eq` | agreement: the total function equals every witness value (component strength / connected strength) |
| `quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single` | **energy identity, solution level, no hypotheses:** every solution has `quadForm (laplacian A) f = f u − f v` |
| `effectiveResistance_eq_quadForm` | **energy identity, function level:** `R u v = quadForm (laplacian A) f` for an actual potential |
| `effectiveResistance_nonneg` | nonnegativity, from `laplacian_psd` through the energy identity |
| `effectiveResistance_symm` | `R u v = R v u` on connected graphs |
| `effectiveResistance_self` | `R u u = 0` unconditionally |
| `sq_le_mul_of_forall_zero_le_sub` | algebra core: a real quadratic nonnegative everywhere has nonpositive discriminant (`c² ≤ Q·E`) |
| `quadForm_laplacian_sub_smul` | polarization: `quadForm L (f − t • g)` expands with cross term `f ⬝ᵥ L *ᵥ g` (reciprocity collapses the mixed terms) |
| `laplacian_cauchy_schwarz` | **semidefinite Cauchy–Schwarz:** `(f ⬝ᵥ L g)² ≤ quadForm L f * quadForm L g`, no connectivity hypothesis (proposal step 6, 2026-08-18) |
| `effectiveResistance_ge_sq_div_quadForm` | **one-sided Dirichlet bound:** `(f u − f v)² / quadForm L f ≤ R u v` for any test potential of positive energy (proposal step 6, 2026-08-18) |

### `Scaffold.Mathlib.GraphTheory.ElectricalFlow` (electrical flows, Kirchhoff conservation, flow energy, Thomson's principle)

The routing object of proposal `electrical-flow-routing.md` (High,
2026-08-18), steps 0–3 delivered 2026-08-19. Step 0 decision recorded
in the proposal before any Lean: matrix representation on ordered
pairs (`EdgeFlow V = Matrix V V ℝ`; Mathlib re-surveyed — no
flow/circulation/graph-divergence API in the pin, `SimpleGraph.Dart`
carries none), weights are **conductances**, zero-conductance support
is a named `IsFlowOn` conjunct, and the ordered-pair `1/2` factor
lives in `flowEnergy` (delivered, step 2). All proved, no axioms.
Consumer to come: Rayleigh monotonicity (step 4) builds on Thomson's
principle and the flow interface.

| Declaration | Content |
|-------------|---------|
| `EdgeFlow` | flows on ordered vertex pairs (`abbrev` of `Matrix V V ℝ`) |
| `electricalCurrent` | Ohm's law: `A i j * (f i − f j)` — conductance times voltage drop |
| `flowDivergence` | net outflow: `∑ j, θ i j` |
| `IsFlowOn` | valid flow: antisymmetric **and** supported (`A i j = 0 → θ i j = 0` — the zero-conductance trap guard; QA-witnessed load-bearing at the energy level) |
| `IsUnitFlow` | `IsFlowOn` + divergence exactly the unit demand `e u − e v` |
| `electricalCurrent_antisymm` | current negates under pair reversal (symmetric weights; QA-witnessed load-bearing) |
| `electricalCurrent_eq_zero_of_weight_eq_zero` | no conductance, no current (support, unconditional) |
| `flowDivergence_electricalCurrent` | **Kirchhoff bridge**: `flowDivergence (electricalCurrent A f) = laplacian A *ᵥ f` (consumes the center's `laplacian_mulVec_apply` sign convention) |
| `isFlowOn_electricalCurrent` | any potential's current is a flow on the network |
| `isUnitFlow_electricalCurrent` | **headline (step 1)**: a unit-demand potential induces a unit flow — the resistance API becomes a routing object |
| `flowEnergy` | dissipated energy: ordered-pair sum of squared current over conductance with an explicit zero branch, halved for double counting (the `1/2` factor QA-witnessed mandatory, step 2) |
| `flowEnergy_electricalCurrent` | **energy agreement (step 2)**: `flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f`, symmetry-only |
| `flowEnergy_nonneg` | `0 ≤ flowEnergy A θ` for nonnegative conductances (nonnegativity load-bearing, QA-witnessed) |
| `flowEnergy_electricalCurrent_eq_effectiveResistance` | **step-2 headline**: a unit-demand current dissipates exactly the resistance it routes (connected graph) |
| `flowDivergence_sub` | divergence is linear: divergence of a difference is the difference of divergences (step 3) |
| `isFlowOn_sub` | the flow space is linear: difference of two flows on `A` is a flow on `A` (step 3) |
| `flowEnergy_add_of_flowDivergence_eq_zero` | **discrete integration by parts / superposition** (step 3): a divergence-free flow perturbation of a current adds exactly its own energy — **no hypotheses on `A`**, only the perturbation's flow properties (QA-decomposed on the triangle: `2 = 2/3 + 4/3`) |
| `effectiveResistance_le_flowEnergy` | **Thomson's principle (step-3 headline)**: `R u v ≤ flowEnergy A θ` for every valid unit flow — the electrical current is the energy minimizer; QA witnesses attainment (split current `2/3` on the triangle) and a strict competitor (detour `2`, `2/3 < 2`) |


### `Scaffold.Mathlib.GraphTheory.Cheeger`

Real definitions: `regularNormalizedLaplacian`, `cutTestVector`.

| Declaration | Kind | Description | Source |
|-------|------|-------------|--------|
| `cheeger_lower_bound` | axiom | `φ(G)²/2 ≤ λ₂(L_sym)` for `d`-regular graphs (the hard direction) | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_upper_bound` | **theorem (proved 2026-08-18; axiom before, retired)** | `λ₂(L_sym) ≤ 2 φ(G)` for `d`-regular graphs — proved from `secondEval_variational` at the volume-centered cut indicator | [Chung](../sources/chung_spectral_graph.md) |

Statement-shape correction (2026-08-18): through 2026-08-17 both axioms
stated the spectral side as `lambda2 (regularNormalizedLaplacian A d)`,
which reads `λ₂(L(L_sym)) = λ₂(-L_sym)` — materially false on the
two-vertex edge (`1/2 ≤ 0`; refuted by
`QA.old_cheeger_lower_bound_refuted_QA`). Both are restated at
`secondEval (regularNormalizedLaplacian A d) …` — the source-faithful
`λ₂(L_sym)`, pinned to its classical value `2` on `K₂` by
`QA.edge_normLap_secondEval_eq_two_QA`.

### `Scaffold.Mathlib.GraphTheory.Fiedler` (Fiedler vector, Phase A)

The Fiedler-vector interface — proposal `fiedler-partitioning.md`
Phase A (2026-08-18), all proved, no axioms. Real definitions:
`fiedlerIndex` (an eigenbasis index carrying `lambda2`, fixed by
classical choice through `evals_mem_eigvalOf` — the proposal's sketch
indexed `eigvecOf` by a sorted-spectrum position, which is not that
function's type; deviation recorded in the module docstring) and
`fiedlerVector` (the unit eigenvector there), plus the sign-pattern
partition `fiedlerPartition`.

| Declaration | Content |
|-------------|---------|
| `fiedlerIndex_eigvalOf` | the chosen index's eigenvalue is `lambda2` |
| `fiedlerVector_eigen` | the eigenvector equation `L *ᵥ f = lambda2 • f` |
| `fiedlerVector_norm`, `fiedlerVector_ne_zero` | unit norm (orthonormal eigenbasis), nonvanishing |
| `fiedlerVector_quadForm` | the Fiedler energy is exactly `lambda2` |
| `fiedlerVector_ortho_onesVec`, `fiedlerVector_sum_eq_zero` | orthogonality to the constants under `0 < lambda2` |
| `lambda2_pos_of_connected` | **algebraic-connectivity certificate:** connected + symmetric nonnegative weights ⇒ `0 < lambda2` (consumes `laplacian_kernel_eq_span_onesVec`, PSD, and both multiplicity pins) |
| `fiedlerPartition_mem` | membership interface (`0 ≤ f i`) |
| `fiedlerPartition_nonempty_of_pos`, `fiedlerPartition_ne_univ_of_pos` | interface-form sanity under `0 < lambda2` |
| `fiedlerPartition_nonempty`, `fiedlerPartition_ne_univ` | connectivity corollaries: a genuine bipartition |

QA: `SpectralGraph/Fiedler_QA.lean` — `K₂` (partition pinned to a
singleton half, boundary `1`), the `P₄` barbell (two `K₂` near-cliques
joined by a bridge: `lambda2 ≤ 1` via the proved Rayleigh engine,
`lambda2 ≠ 1` via the eigen equations, partition computed to be exactly
the known good cut `{0,1}` or its complement — boundary `1`, volume
`3`, conductance `1/3`), and the disconnected negative witness
(`lambda2 = 0`; `onesVec` is a nonzero eigenvector there whose sign
filter is all of `univ`).

### `Scaffold.Mathlib.GraphTheory.RandomWalk` (random-walk interfaces)

Real definitions: `transitionMatrix` (`d⁻¹ • A`), `randomWalkLaplacian`
(`1 - P`). All statements proved (2026-08-17), no axioms:

| Declaration | Content |
|-------------|---------|
| `transitionMatrix_symmetric` | symmetry transport |
| `transitionMatrix_row_sum` | row-stochasticity for `d`-regular graphs |
| `randomWalkLaplacian_symmetric` | symmetry transport |
| `randomWalkLaplacian_eq_regularNormalizedLaplacian` | interop with the Cheeger bridge |
| `randomWalkLaplacian_eq_smul_laplacian` | `L_rw = d⁻¹ • L` for `d`-regular graphs |

See the [SGT backlog](../../docs/6_SGT_BACKLOG.md) for the irregular-graph
adapter plan.

### `Scaffold.Mathlib.GraphTheory.Normalized` (general normalized Laplacian)

Real definitions: `degreeSqrt`, `degreeInvSqrt` (diagonal `√D`, `1/√D`
via `Real.sqrt` — no matrix square root needed), `normalizedLaplacian`
(`1 - (1/√D) A (1/√D)`, the irregular symmetric normalized Laplacian).
All statements proved (2026-08-17), no axioms:

| Declaration | Content |
|-------------|---------|
| `degreeSqrt_mul_degreeSqrt` | `√D √D = degreeMatrix` |
| `degreeSqrt_mul_degreeInvSqrt`, `degreeInvSqrt_mul_degreeSqrt` | the diagonal factors are inverse (positive degrees) |
| `normalizedLaplacian_symmetric` | symmetry for symmetric `A` |
| `degreeSqrt_mul_normalizedLaplacian_mul_degreeSqrt` | congruence `√D L_sym √D = laplacian A` |
| `normalizedLaplacian_eq_regularNormalizedLaplacian` | agreement with the regular cone |
| `walkTransitionMatrix`, `walkLaplacian` | definitions: general walk form `D⁻¹A`, `I − D⁻¹A` |
| `walkTransitionMatrix_row_sum` | row-stochasticity on irregular graphs (positive degrees) |
| `degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt` | similarity `√D · L_walk · (1/√D) = L_sym` |

### `Scaffold.Mathlib.GraphTheory.Stationary` (first walk/normalized consumer)

All statements proved (2026-08-17), no axioms; consumes the `RandomWalk`
and `Normalized` interfaces — demonstrated downstream reuse:

| Declaration | Content |
|-------------|---------|
| `mulVec_one_eq_deg` | `A *ᵥ 1 = deg A` (row sums in vector form) |
| `normalizedLaplacian_mulVec_sqrtDeg_eq_zero` | kernel of `L_sym` is `√deg` — normalized counterpart of `laplacian_ones_in_kernel` |
| `walkTransitionMatrix_transpose_mulVec_deg` | degree measure stationary for the adjoint walk (`π ∝ deg`; Markov-mixing consumer interface) |
| `randomWalkLaplacian_mulVec_one_eq_zero` | conservation of mass, regular case (consumes `RandomWalk.transitionMatrix_row_sum`) |
| `walkLaplacian_mulVec_one_eq_zero` | conservation of mass, irregular case (consumes `Normalized.walkTransitionMatrix_row_sum`) |

### `Scaffold.Mathlib.GraphTheory.VariationalTransfer` (variational consumer of the congruence bridge)

All statements proved (2026-08-17), no axioms; the second consuming
module of the `Normalized`/`Spectral` interfaces (after `Stationary`):

| Declaration | Content |
|-------------|---------|
| `quadForm_congr` | generic congruence lemma: `quadForm (P M P) y = quadForm M (P *ᵥ y)` for symmetric `P` |
| `degreeSqrt_isSymm`, `degreeSqrt_mulVec` | symmetry of `√D`; entrywise action `√D *ᵥ y = √deg ∘ y` |
| `quadForm_laplacian_eq_quadForm_normalizedLaplacian` | Dirichlet-form transfer `yᵀ L y = (√D y)ᵀ L_sym (√D y)` through the proved congruence |
| `dotProduct_degreeSqrt_mulVec` | degree-weighted denominator `⬝(√D y, √D y) = ∑ deg i · y i²` |
| `degreeSqrt_mulVec_ne_zero` | the stretch preserves nonzero vectors (positive degrees) |
| `rayleigh_normalizedLaplacian_degreeSqrt` | normalized Rayleigh quotient `rayleigh L_sym (√D y) = (yᵀ L y) / ∑ deg i · y i²` — the irregular-graph variational interface |
| `normalizedLaplacian_psd` | PSD transfers from `laplacian_psd` by un-stretching through `1/√D` |

### `Scaffold.Mathlib.GraphTheory.Dynamics` (dynamic frontier)

Real definitions: `TimeVaryingGraph`, `laplacianSequence`,
`IsEventDriven`, `laplacianSequence_symmetric`.

| Axiom | Description | Source |
|-------|-------------|--------|
| `spectral_persistence` (**deprecated** 2026-08-17; zero non-QA consumers, covered by the derived two-endpoint chain — see migration note) | Per-step projector stability `≤ ε/γ` under gap-separated event streams | [Davis & Kahan 1970](../sources/davis_kahan_1970.md) |

## Applications

These declarations feed the perturbation bridge
([Perturbation map](perturbation.md)) and a retained spectral-persistence
example described in [docs/3_SPECTRAL_THEORY.md](../../docs/3_SPECTRAL_THEORY.md).
That example is compatibility surface, not the SGT roadmap.
