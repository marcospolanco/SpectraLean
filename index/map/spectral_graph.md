# Spectral Graph Theory

This index maps the SGT center: Laplacians, sorted spectra, cuts and
conductance, Cheeger theory, interlacing, and event-driven dynamics.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.GraphTheory.{Spectral,SimpleGraphAdapter,Electrical,ElectricalFlow,Foster,Expander,SpectralCertificates,Tikhonov,Band,ClusterProjector,Cheeger,Mixing,Dynamics,Krylov,PolyFilter,Multiway}`.

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
`initialProjector_idempotent`; the projector product-and-action layer
(2026-08-20, enabling `GraphTheory.Band`):
`spectralProjector_mul_spectralProjector` (the nestedness cross-law
`P_{c₁} * P_{c₂} = P_{min c₁ c₂}`, with the ordered forms `_of_le` /
`_of_le'`; `spectralProjector_idempotent` re-derived from it at
unchanged statement) and `spectralProjector_mulVec_eigvecOf` (the
complete action description `P_c *ᵥ vᵢ = if λᵢ ≤ c then vᵢ else 0`,
with the `_self` / `_of_lt` specializations); spectrum pinning tools (2026-08-18):
`lambda2_eq_secondEval` (bridge between the adjacency-facing and
matrix-facing λ₂ APIs), `evals_mem_eigvalOf` (sorted-spectrum ↔
eigenbasis connection), `eigvalOf_sum_eq_trace` (trace from the unitary
diagonalization), `eigvalOf_le_of_quadForm_nonpos` (one-sided Rayleigh
eigenvalue bound — the refutation engine of `Cheeger_QA`); the
identity-spectrum pin (2026-08-29, the degenerate-degree corner audit):
`eigvalOf_one` (every eigenbasis value of the identity matrix is `1`,
from the eigenaction `1 *ᵥ v = v` against `eigvecOf_inner`'s unit
norm) and `evals_one` (**the sorted spectrum of the identity is `1` at
every index** — the junk value `normalizedLaplacian` degenerates to at
nonpositive-degree corners, not the zero matrix's `0`); top-of-
spectrum tools (2026-08-19, the decidable-certificates Step-2 slice):
`eigvalOf_le_evals_last` (the sorted spectrum's last entry dominates
every eigenbasis eigenvalue), `quadForm_le_evals_last` (**top
eigenvalue Rayleigh domination in multiplication form**:
`xᵀ M x ≤ λ_max • (x ⬝ᵥ x)` for every symmetric matrix,
unconditionally in `x`, no positivity — the upper half of the
Rayleigh sandwich), and `dotProduct_self_pos` made public (the
positivity idiom for division-form variational consumers);
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
| `laplacian_mulVec_eq_single_sub_single_le_max` | **maximum principle, top half:** every unit-demand potential satisfies `f x ≤ max (f u) (f v)` — diffusion-form propagation + walk induction (proposal `resistance-metric.md`, 2026-08-24) |
| `laplacian_mulVec_eq_single_sub_single_min_le` | **maximum principle, min half:** `min (f u) (f v) ≤ f x` — the max half at the negated demand |
| `effectiveResistance_pos_of_ne` | **positivity off the diagonal:** `u ≠ v → 0 < R u v` — the Dirichlet bound at the indicator `e u` (energy `∑_{j≠u} A u j > 0` by connectivity) |
| `effectiveResistance_eq_zero_iff` | **definiteness residual:** `R u v = 0 ↔ u = v` on connected networks — the law distinguishing a metric from a pseudometric |
| `effectiveResistance_le_add` | **triangle inequality:** `R u w ≤ R u v + R v w` — with nonnegativity/symmetry/self-distance, the fourth metric law; the polarization cross term `f v − f w ≤ 0` closed by the maximum principle |

### `Scaffold.Mathlib.GraphTheory.ElectricalFlow` (electrical flows, Kirchhoff conservation, flow energy, Thomson's principle, Rayleigh monotonicity, capacity reinforcement)

The routing object of proposal `electrical-flow-routing.md` (High,
2026-08-18), all six steps (0–5) delivered 2026-08-19 — the program is
complete. Step 0 decision recorded in the proposal before any Lean:
matrix representation on ordered pairs (`EdgeFlow V = Matrix V V ℝ`;
Mathlib re-surveyed — no flow/circulation/graph-divergence API in the
pin, `SimpleGraph.Dart` carries none), weights are **conductances**,
zero-conductance support is a named `IsFlowOn` conjunct, and the
ordered-pair `1/2` factor lives in `flowEnergy` (delivered, step 2).
All proved, no axioms.

| Declaration | Content |
|-------------|---------|
| `EdgeFlow` | flows on ordered vertex pairs (`abbrev` of `Matrix V V ℝ`) |
| `electricalCurrent` | Ohm's law: `A i j * (f i − f j)` — conductance times voltage drop |
| `flowDivergence` | net outflow: `∑ j, θ i j` |
| `IsFlowOn` | valid flow: antisymmetric **and** supported (`A i j = 0 → θ i j = 0` — the zero-conductance trap guard; QA-witnessed load-bearing at the energy level) |
| `IsUnitFlow` | `IsFlowOn` + divergence exactly the unit demand `e u − eᵥ` |
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
| `isFlowOn_of_le` | **flow-space growth (step 4)**: a flow supported on `A` is a flow on every entrywise larger `B ≥ A ≥ 0` (support load-bearing: a `B`-zero entry squeezes the nonnegative `A` entry to zero) — the competitor-transfer interface |
| `flowEnergy_le_of_le` | **raising conductances lowers dissipated energy (step 4)**: `flowEnergy B θ ≤ flowEnergy A θ` for `0 ≤ A ≤ B` entrywise, termwise (`θ²/B ≤ θ²/A` on nonzero branches); support again load-bearing on the `A i j = 0 < B i j` branch |
| `effectiveResistance_le_of_le` | **Rayleigh monotonicity in conductance form (step-4 headline)**: `A ≤ B` entrywise ⇒ `effectiveResistance B u v ≤ effectiveResistance A u v` on connected symmetric nonnegative networks — the `A`-current as competitor on `B`, Thomson on `B`, the energy comparison, and the step-2 identity; QA certifies `1 → 1/2` (capacity increase) and `2/3 → 2/5` (partial increase), strict, with the orientation guard refuting the reverse direction |
| `increaseConductance` | capacity reinforcement (step 5): raise one undirected pair's conductance by `δ`, both ordered entries together (symmetry-preserving; entry interface lemmas `increaseConductance_apply_of_reinforced` / `_of_not_reinforced`, plus `le_increaseConductance` for `0 ≤ δ`, `increaseConductance_isSymm`, `increaseConductance_nonneg`) |
| `supportGraph_le_of_le` | support graphs grow with the network: entrywise `A ≤ B` ⇒ `supportGraph A ≤ supportGraph B` (no nonnegativity hypothesis — `0 < A i j ≤ B i j`) |
| `supportGraph_connected_of_le` | capacity growth preserves connectivity: `A ≤ B` entrywise and `supportGraph A` connected ⇒ `supportGraph B` connected (Mathlib's `SimpleGraph.Connected.mono` along the containment) — the step-4-recorded optional adapter, delivered as step 5's packaging companion |
| `effectiveResistance_le_increaseConductance` | **capacity reinforcement cannot worsen certified routing cost (step-5 headline, the ICP example)**: `effectiveResistance (increaseConductance A i j δ) u v ≤ effectiveResistance A u v` for `δ ≥ 0`, with only the *original* network's connectivity hypothesized (the reinforced network's derived by the adapter); QA is the release example — the Mathlib `Fin 3` path graph through `toWAdj`, reinforcement computed to the doubled-path matrix, `2 → 3/2` strict |


### `Scaffold.Mathlib.GraphTheory.Foster` (Foster's theorem, leverage scores)

Foster's theorem for weighted graphs (proposal
`spectral-graph-sparsification.md` **Phase A only**, High, delivered
2026-08-19): the conductance-weighted effective resistances sum to the
spanning-tree edge count. All proved, zero axioms, via the proposal's
**pseudoinverse-free eigenbasis route** — no `L⁺` and no matrix square
root anywhere; the unit-demand potential is used only through its
energy, resolved spectrally (`quadForm_eigvalOf`). Phase B (the
sparsification guarantee) is blocked in that proposal on an unresolved
matrix-Chernoff scope decision and is not developed.

| Declaration | Content |
|-------------|---------|
| `card_filter_eigvalOf_laplacian_eq_zero` | the kernel of a connected Laplacian occupies exactly one eigenbasis index — at most one by orthonormality against the one-dimensional kernel (`laplacian_kernel_eq_span_onesVec`), at least one because `onesVec` is a nonzero kernel vector; the counting fact that turns "each nonzero eigenvalue contributes `1`" into `card V − 1` |
| `effectiveResistance_eq_sum_eigbasis` | **resistance as a spectral sum:** `R u v = ∑_k (v_k u − v_k v)² / λ_k` over the nonzero-eigenvalue eigenvectors (zero-eigenvalue terms omitted; their voltage differences vanish) — the per-pair Foster kernel |
| `foster_theorem` | **Foster's theorem (1949):** `(∑ i, ∑ j, A i j * R i j) / 2 = card V − 1` on every connected symmetric-nonnegative network — in unordered-pair form `∑_{u<v} w_e R_e = n − 1`; the `/ 2` is the ordered-pair double count (QA-witnessed load-bearing: the ordered sums compute to `4 ≠ 2` on `K₃` and `6 ≠ 3` on `K₄`) |
| `leverageScore` | the pair's share `A u v * R u v / (card V − 1)` of the Foster budget — the importance-sampling object of Spielman–Srivastava sparsification (Phase B, blocked); junk values below `2 ≤ card V` documented in the docstring |
| `sum_leverageScore_eq_two` | **Foster in leverage form:** the ordered-pair leverage scores sum to exactly `2` (unordered: `1`), making them a probability distribution over edges; `2 ≤ card V` is the division guard |


### `Scaffold.Mathlib.GraphTheory.Expander` (edge weights, the centered-indicator decomposition, the Expander Mixing Lemma)

Steps 1 and 2 of the decidable-spectral-certificates program (proposal
`decidable-spectral-certificates.md`, High; its Step 0 gate — the
Laplacian-convention decision and the ℚ-`decide` spike with the integer
cross-multiplied fallback — was completed and recorded in the proposal
on 2026-08-19 immediately before this module): the combinatorial
edge-weight and discrepancy core, and the Expander Mixing Lemma itself
delivered the same day through the Rayleigh-sandwich route. Section 8
(2026-08-25, `proposals/expander-independence-number-bound.md`) adds
the lemma's first theorem consumer: the Hoffman-type independence
bound. All proved, zero axioms.

| Declaration | Content |
|-------------|---------|
| `edgeWeight` | the ordered `(S, T)` cut weight `∑ i ∈ S, ∑ j ∈ T, A i j`, with degenerate-cut guards (`edgeWeight_empty_left/right`), the degree-sum form against `univ` (`edgeWeight_univ_right`), the hypothesis-free matrix form `edgeWeight_eq_dotProduct` (`indicatorVec S ⬝ᵥ (A *ᵥ indicatorVec T)`, the bilinear identity every spectral mixing-lemma proof starts from), and `edgeWeight_symm` (cut-weight symmetry under entrywise symmetry, by sum swap) |
| `indicatorVec` / `centeredIndicator` | the 0/1 characteristic vector of a subset and its centered (mean-removed) version — the decomposition `indicatorVec_eq_smul_onesVec_add_centeredIndicator` splits the characteristic vector into its `onesVec` component plus the centered remainder |
| `sum_centeredIndicator_eq_zero` / `centeredIndicator_dotProduct_onesVec` | the centered indicator is **exactly** orthogonal to `onesVec` — unconditionally (the empty-type case is handled; no `Nonempty`/cardinality hypothesis is carried) — the fact that kills the `d`-regular cross terms in the headline |
| `mulVec_onesVec_eq_const` | on a `d`-regular network, `A *ᵥ onesVec` is the constant `d` (`deg` is exactly the row sum) |
| `edgeWeight_eq_regular_add_centered` | **the `d`-regular decomposition (headline):** `edgeWeight A S T = d·\|S\|·\|T\|/\|V\| + centeredIndicator S ⬝ᵥ (A *ᵥ centeredIndicator T)` on symmetric `d`-regular networks — the population main term plus the centered cross term the Expander Mixing Lemma bounds by `μ`; symmetry load-bearing (the `1 ⬝ᵥ (A *ᵥ v)` cross term dies through `Matrix.dotProduct_mulVec`'s transpose) and regularity load-bearing (the `A *ᵥ onesVec = d` evaluation); no cardinality hypothesis (empty type degenerates to `0 = 0 + 0`) |
| `quadForm_add` / `quadForm_add_sub_eq` / `quadForm_degreeMatrix` | generic matrix algebra consumed by the sandwich: quadratic forms are additive in the matrix; **polarization** — the difference of the quadratic form at `x + y` and `x − y` isolates `4 • (x ⬝ᵥ (M *ᵥ y))` for symmetric `M` (symmetry load-bearing: it folds the `y ⬝ᵥ (M *ᵥ x)` half onto the `x ⬝ᵥ (M *ᵥ y)` half); and the degree matrix's form is the degree-weighted sum of squares |
| `quadForm_add_quadForm_laplacian` | **the `d`-regular identity:** `xᵀAx + xᵀLx = d • ‖x‖²` — the quadratic form of `A + L = D`; regularity only, no looplessness (the Step 0 sketch's `hloop` found unnecessary and dropped — a recorded statement-shape strengthening) |
| `lambda2_mul_dotProduct_le_quadForm` | the variational lower bound in multiplication form: `λ₂ • ‖x‖² ≤ xᵀLx` on `x ⊥ onesVec` (the center's `secondEval_le_rayleigh` multiplied out; zero vector handled so consumers never case-split) |
| `eigvecOf_ortho_of_mulVec_eq_zero` | general-kernel orthogonality: eigenvectors at nonzero eigenvalues are ⊥ any kernel vector `w` (2026-08-25; the onesVec form's general-`w` parent) |
| `secondEval_le_rayleigh_of_ker` | **general-kernel Rayleigh domination** (2026-08-25): `secondEval ≤ R(x)` for every nonzero `x ⊥ w` at a nonzero kernel vector `w` of a PSD symmetric matrix — the delivered `secondEval_le_rayleigh` is the `w = onesVec` instance; first consumer the irregular Cheeger upper bound |
| `secondEval_variational_of_ker` | **general-kernel Courant–Fischer, sInf form** (2026-08-25/26): `secondEval = sInf {R(x) : x ≠ 0, x ⊥ w}` at a nonzero kernel vector `w` of a PSD symmetric matrix — the hard half is `secondEval_le_rayleigh_of_ker` reused verbatim; the new witness half produces an orthogonal candidate at both `0 < λ₂` and the `λ₂ = 0` double bottom; first consumer the irregular Cheeger hard direction `cheeger_lower_bound_normalized` (whose operator is killed by `√D·1`, not `1`) |
| `vol_pos_of_pos_deg` | a nonempty set has positive volume under positive degrees (2026-08-25; the regularity-free replacement for `vol_pos_of_regular`) |
| `evals_le_of_card_eigvalOf_le` | **the order-statistics↔counting bridge** (2026-08-26, the multiway engine): if at least `k+1` eigenbasis eigenvalues are ≤ `t`, then the `k`-th sorted entry is ≤ `t` — the shelf previously had only the two endpoint instances (`evals_first_le_eigvalOf`, `eigvalOf_le_evals_last`); proved by induction on the sorted list; first consumer the general-k subspace engine below |
| `evals_le_of_linearIndependent` | **the general-k subspace Rayleigh–Ritz engine** (2026-08-26, the multiway engine): a `k`-dimensional linearly independent family whose every combination satisfies `quadForm ≤ t · ‖·‖²` certifies `evals ⟨k−1⟩ ≤ t` — no PSD, no kernel hypothesis; the `k−1` smallest-eigenvalue eigenvectors impose at most `k−1` constraints on the combination space, so a nonzero survivor exists (`LinearMap.ker_ne_bot_of_finrank_lt`), and its eigen-expansion contradicts the bound strictly; the delivered `k = 2` engines are its constraint-form specializations; first consumer `cheeger_upper_bound_multiway` |
| `evals_sum_eq_trace` | the sorted spectrum sums to the trace (2026-08-26, the multiway QA spin-off — the trace-pinning technique at the sorted API) |
| `exists_eigvalOf_eq_of_mulVec_eq_smul` | an exhibited eigenvector at `μ` lands some eigenbasis eigenvalue at `μ` (2026-08-26, the multiway QA spin-off — the eigenvalue-witness bridge QA uses to pin spectra without computing them) |
| `abs_quadForm_le_of_ortho_onesVec` | **the operator bound on `1⊥` (Step 2 bridge):** `\|xᵀAx\| ≤ μ ‖x‖²` under the Laplacian-spectrum hypothesis `μ ≥ max \|d − λ₂(L)\| \|d − λ_max(L)\|` — the Rayleigh sandwich (lower bound + the generic top domination + the `d`-regular identity; load-bearing on all three) |
| `quadForm_bilinear_sq_le_of_ortho_onesVec` | **the sharp bilinear bound:** `(x ⬝ᵥ (A *ᵥ y))² ≤ μ² ‖x‖² ‖y‖²` on `1⊥ × 1⊥`, by the scaling trick (`√Y•x ± √X•y` through polarization; `a² = Y, b² = X` attains the AM–GM equality, so the product form carries no slack) |
| `dotProduct_centeredIndicator_self` | the variance identity `‖centeredIndicator S‖² = \|S\|(|V|−\|S\|)/\|V\|` — the geometric factor of the mixing bound |
| `expander_mixing_lemma` | **the Expander Mixing Lemma (headline):** `\|e(S,T) − d•\|S\|•\|T\|/\|V\|\| ≤ μ • √(\|S\|\|T\|(|V|−\|S\|)(|V|−\|T\|))/\|V\|` on symmetric, nonnegative, `d`-regular networks with the Laplacian-spectrum hypothesis — the classical discrepancy bridge between algebraic spectral gaps and combinatorial pseudorandomness (Alon–Chung 1988; Hoory–Linial–Wigderson 2006 §2; Vadhan 2012 §4), at the Step 0 restated `√` signature with squaring only inside the proof |
| `IsIndependentSet` | **independent set** of a weighted adjacency (2026-08-25, the Hoffman proposal's Step 0 verdict 1): `∀ i ∈ S, ∀ j ∈ S, A i j = 0` — no weight within the set, self-loops included (the looped-graph reading; exactly what collapses `edgeWeight A S S`); defined natively over `WAdj`/`Finset` since the pinned Mathlib has no independence-number machinery |
| `edgeWeight_self_eq_zero_of_isIndependentSet` | the collapse: an independent set's internal cut weight is `0` (one `Finset.sum_eq_zero`) — the single mixing-lemma fact the Hoffman bound consumes |
| `deg_eq_zero_of_isIndependentSet_univ` | **the whole-graph corner fence:** independence of the entire vertex set forces every degree to `0` — under regularity the network is `d = 0`; a positive-degree graph provably cannot cover itself with an independent set |
| `hoffman_independence_bound` | **the Hoffman ratio bound (headline, the mixing lemma's first theorem consumer; 2026-08-25):** `\|S\| ≤ μ • \|V\| / (d + μ)` for every independent set of a symmetric nonnegative `d`-regular network with positive degree, at exactly the mixing lemma's `μ` hypothesis — the classical bound (Hoffman; Brouwer–Haemers, *Spectra of Graphs*, in the mixing-lemma corollary form of the module's [AC]/[HLW]/[V] citations); `0 < d` is an explicit load-bearing hypothesis (the zero-adjacency fence in QA), consumed only through `0 < d + μ`; per-set form since no independence-number API exists at the pin — bounding every independent set bounds the independence number |


### `Scaffold.Mathlib.GraphTheory.SpectralCertificates` (proof-carrying λ₂ upper-bound certificates)

Step 3 of the decidable-spectral-certificates program (proposal
`decidable-spectral-certificates.md`, High): the computable certificate
layer over the proved spectral center. An outside solver proposes an
inexact rational/integer test vector and a bound; Lean kernel-checks
elementary arithmetic and a proved soundness theorem lifts the check to
`lambda2 ≤ bound` in the real center — closing, inside Lean, the
noncomputable-extraction gap `docs/traction-plan.md` records. All
proved, zero axioms.

| Declaration | Content |
|-------------|---------|
| `algebraMap_apply` | the ordered-field embedding `algebraMap ℚ ℝ` is the rational coercion *definitionally* — the hinge every transport goes through (the proposal's Calibration 1) |
| `toReal` / `toRat` | entrywise embedding of a rational (resp. integer) test vector |
| `isSymm_map_algebraMap` / `isSymm_map_intCast` / `isSymm_map_intCastReal` | symmetry transports along the ℚ→ℝ, ℤ→ℚ, and ℤ→ℝ embeddings |
| `dotProduct_toReal` / `dotProduct_toReal_self` / `quadForm_laplacian_map_algebraMap` | dot products and the Dirichlet energy of an embedded test vector are the casts of the raw rational sums — the certificate's `rawNumer` is exactly `quadForm (laplacian A ℝ) (toReal v)`, halved (`laplacian_quadForm`; load-bearing on the center's exact Laplacian convention) |
| `lambda2_le_rayleigh` | **the one-sided Rayleigh consumer form:** every nonzero test vector orthogonal to `onesVec` certifies `lambda2 ≤ R_L(x)` — the division-form twin of `Expander.lambda2_mul_dotProduct_le_quadForm`, proved straight from the characterization `lambda2_variational` (constraint-set membership + PSD boundedness) |
| `isSpectralUpperBoundCertificate` | the ℚ-facing specification checker: orthogonality to `onesVec`, positive norm, and the raw Dirichlet sum bounded by `2 • bound • denom` — the cross-multiplied form of `R_L(v) ≤ bound`; not kernel-decidable (the Step 0 reducibility wall), reached through the proved bridges |
| `lambda2_le_of_certificate` | **certificate soundness (ℚ-facing, headline):** an accepted certificate proves `lambda2 (A ℝ) ≤ bound` — the proposal's flagship load-bearing consumer of the proved `lambda2_variational` (`rawNumer/2` is the Laplacian energy, `dotOne = 0` is the constraint, `sInf ≤ rayleigh ≤ bound`) |
| `isSpectralUpperBoundCertificateInt` / `isSpectralUpperBoundCertificateIntFrac` | the kernel-verifiable **integer cross-multiplied twin** (integer bound) and its fractional-bound variant (`den • rawNumer ≤ 2 • num • denom`, `0 < den`) — the checkers plain kernel `decide` evaluates on concrete `Fin n` graphs |
| `isSpectralUpperBoundCertificateInt_iff` | the integer twin is *sound and complete* against the specification at the same integer bound — pure ordered-field algebra, no `decide` |
| `isSpectralUpperBoundCertificateIntFrac_iff` | **the proved cross-multiplication bridge (fractional form):** with `0 < den`, the fractional twin accepts exactly when the specification accepts at the rational bound `num / den` — cross-multiplication in an ordered field plus integer-cast transport of the finite sums; the lemma that makes the ℚ specification reachable from kernel-verifiable arithmetic |
| `lambda2_le_of_certificateInt` / `lambda2_le_of_certificateIntFrac` | **kernel-facing soundness:** a `decide`d integer (resp. fractional) certificate yields a verified `lambda2 ≤ bound` on the real network — the executable end-to-end chain (integer arithmetic → kernel `decide` → proved bridge → real spectral bound) |


### `Scaffold.Mathlib.GraphTheory.Tikhonov` (graph-signal smoothing in the Laplacian eigenbasis)

Tikhonov regularization on a network (proposal
`tikhonov-shrinkage-filter.md`, High): the smoothing operator
minimizing `‖x − y‖² + (1/π) · xᵀLx` — the standard denoising /
label-propagation filter of graph signal processing, delivered as pure
hard crust on the eigenbasis machinery. Zero axioms. A recorded
statement-shape deviation from the proposal: the attenuation factor is
`1` *exactly* at a zero eigenvalue (kernel modes pass through
untouched — that is mean preservation), so the delivered endpoint
facts are `factor = 1 ↔ λ = 0` and `factor < 1 ↔ 0 < λ`, not the
proposal's "never exactly 1". **Phase 2 (the hard-filter limit,
2026-08-23) delivered in full — the proposal COMPLETE:** the
positive-eigenvalue limit of `tikhonovShrinkage` plus the finite
tail-suppression corollary (suppression-stated per the external
consumer's explicit non-overclaim instruction), still zero axioms.

| Declaration | Content |
|-------------|---------|
| `tikhonovShrinkage` | the attenuation factor `π / (λ + π)` a mode of eigenvalue `λ` is multiplied by |
| `tikhonovShrinkage_pos` / `_ne_zero` / `_le_one` / `_lt_one` | the factor is in `(0, 1]` on nonnegative eigenvalues — no mode is ever annihilated (the true half of the proposal's Step-3 claim) |
| `tikhonovShrinkage_eq_one_iff` | the factor is exactly `1` iff `λ = 0` — the kernel mode is fixed, the engine of mean preservation |
| `tikhonovShrinkage_lt_tikhonovShrinkage` | strict antitonicity in `λ` on `λ ≥ 0` — larger eigenvalues attenuated more (the low-pass property) |
| `dotProduct_eigvecOf_filter` | **generic spectral-filter coefficient identity:** the eigenbasis coefficient of `∑_i g(λ_i) (v_i ⬝ᵥ y) • v_i` along `v_k` is `g(λ_k) (v_k ⬝ᵥ y)` — orthonormality collapse, any filter `g`, reusable by any GSP filter consumer |
| `ext_of_dotProduct_eigvecOf_eq` | eigenbasis expansion is injective — the uniqueness engine |
| `eigvalOf_laplacian_nonneg` | every Laplacian eigenvalue of a symmetric nonnegative network is nonnegative (`quadForm_eigvecOf_self` + `laplacian_psd`) |
| `tikhonovMinimizer` | **the minimizer, defined by the eigenbasis formula** `x* = ∑_k (π/(λ_k+π)) (v_k ⬝ᵥ y) • v_k` (the recorded route: explicit formula over `Classical.choice` strict convexity) |
| `tikhonovMinimizer_dotProduct_eigvecOf` | **the closed-form eigencoefficient identity** (proposal Step 2): the minimizer's coefficient along any eigenvector is the signal's coefficient shrunk by `π/(λ_k+π)`; hypothesis-free |
| `tikhonovMinimizer_add_smul_one_mulVec` | **the normal equation:** `(L + π•1) *ᵥ x* = π • y` |
| `eq_tikhonovMinimizer_of_add_smul_one_mulVec` | **the converse characterization:** any solution of the normal equation *is* the minimizer — the interface that lets QA pin the spectral construction against a hand-solved linear system |
| `tikhonovObjective` | the objective `‖x − y‖² + (1/π) · xᵀLx` (junk-degenerate at `π = 0`, excluded by the theorems) |
| `tikhonovObjective_sub_minimizer` | **the strict-convexity decomposition:** the objective's excess over its minimum is `∑_k (1 + λ_k/π) (d_k − d*_k)²` with positive weights — one identity delivering minimality and uniqueness |
| `tikhonovObjective_minimizer_le` | **minimality** (proposal Step 1) |
| `eq_of_tikhonovObjective_eq_minimizer` | **uniqueness:** a tie in the objective forces vector equality |
| `sum_tikhonovMinimizer_eq_sum` | **mean preservation:** `∑ x* = ∑ y` — needs symmetry and `π ≠ 0` only (each component's mean is preserved on disconnected graphs) |
| `tikhonovMinimizer_eigvecOf` | an eigenvector input comes out as `factor • v` — pure orthonormality |
| `tikhonovMinimizer_ne_apply_self_of_eigvalOf_pos` | **not a projection:** the filter is not idempotent — `T(T v) = s² • v ≠ s • v` at any positive-eigenvalue eigenvector; the precise sense in which Tikhonov smoothing differs from `spectralProjector` (which fixes its image exactly) |
| `tikhonovShrinkage_tendsto_zero` | **the hard-filter limit (Phase 2, 2026-08-23):** `π/(lam+π) → 0` as `π → 0` at every fixed `0 < lam` — two-sided (the full `𝓝 0`), via continuity of division at the nonzero denominator; the `0 < lam` hypothesis load-bearing (QA: at `lam = 0` the factor has no limit at all) |
| `tikhonovShrinkage_tail_energy_tendsto_zero` | **tail suppression, general symmetric form (Phase 2):** for a finite set of modes each with `lam ≤ λᵢ` (`lam > 0`), the filtered coefficient energy `∑_{i∈t} (g(π,λᵢ) cᵢ)² → 0` as `π → 0` — stated as suppression of the selected positive-eigenvalue tail (the requester's non-overclaim instruction), on a general symmetric matrix since nothing in the proof uses PSD |
| `tikhonovMinimizer_tail_energy_tendsto_zero` | **tail suppression, minimizer form (Phase 2):** the filtered signal's coefficient energy on any selected positive-enough mode set vanishes in the hard-filter limit — the consumer-facing `sgt-gaps.md` item-1 statement, no band-projector convergence claimed |

### `Scaffold.Mathlib.GraphTheory.Band` (two-sided spectral band projectors)

The `(a, b]` band projector (proposal `spectral-band-projectors.md`,
High, the four-step program complete — Steps 1–3 delivered
2026-08-20, Step 4 delivered 2026-08-21): the orthogonal projector
onto the eigenspaces with
eigenvalues strictly above `a` and at most `b` — the bandpass-filtering
object of frequency-selective graph signal processing — delivered as
the difference of two `spectralProjector` calls, pure hard crust on
the proved projector algebra. Zero axioms. Parameterized by spectral
interval, not index (the proposal's design note); the definition is
total, with the `a > b` negated-band junk documented. The enabling
lemmas live one module in, in `Spectral`: the nestedness cross-law
`spectralProjector_mul_spectralProjector` (`P_{c₁} * P_{c₂} = P_{min c₁ c₂}`,
with ordered forms; `spectralProjector_idempotent` re-derived from it
at unchanged statement) and the complete projector-eigenvector action
`spectralProjector_mulVec_eigvecOf` (`P_c *ᵥ vᵢ = if λᵢ ≤ c then vᵢ else 0`).
Step 2 (delivered 2026-08-20): disjoint bands are orthogonal — the
pairwise half of the partition completeness Step 3 generalizes.
Step 3 (delivered 2026-08-20): **completeness under a partition** — the
unconditional telescoping law, the covering-family resolution of the
identity, monotone-family orthogonality (where monotonicity is exactly
what makes the family a partition), and the consumer's vector
decomposition `x = ∑ B_k x`.
Step 4 (delivered 2026-08-21): **the Hilbert-projection
specialization** — the band projector's output *is* Mathlib's
`orthogonalProjection` onto its transported range and the closest
point of that range to the input (statements at `EuclideanSpace ℝ V`;
the bare `V → ℝ` default norm is the sup norm and is not used).

| Declaration | Content |
|-------------|---------|
| `bandProjector` | **the two-sided band projector** `spectralProjector M hM b − spectralProjector M hM a` — projects onto `∑_{a < λᵢ ≤ b} span vᵢ` |
| `bandProjector_symmetric` | self-adjointness (difference of symmetric matrices) |
| `bandProjector_idempotent` | **idempotence for `a ≤ b`**, through the nestedness cross-law — the difference of two idempotents is idempotent precisely because `P_a P_b = P_b P_a = P_a` |
| `bandProjector_mulVec_eigvecOf_self` | **in-band modes are fixed** (`a < λᵢ ≤ b`): the bandpass-selection interface |
| `bandProjector_mulVec_eigvecOf_eq_zero_left` / `_right` | **out-of-band modes are annihilated** (`λᵢ ≤ a`, or `b < λᵢ`): below-band and above-band guards |
| `bandProjector_eq_spectralProjector_of_lt` | below the whole spectrum, the band *is* the below-threshold projector — the design note's named special case (`spectralProjector` kept, not re-derived) |
| `bandProjector_eq_one` | a covering band is the identity — the two-band instance of the Step-3 completeness statement |
| `bandProjector_mul_bandProjector_eq_zero` / `_eq_zero'` | **disjoint bands compose to zero in both orders** (`b ≤ c` = interval disjointness, load-bearing): the four-term cross-law expansion collapses under the ordering |
| `bandProjector_inner_eq_zero` | **orthogonality of the images:** `(B_{a,b} *ᵥ x) ⬝ᵥ (B_{c,d} *ᵥ y) = 0` for disjoint bands — the frequency-selective consumer's form |
| `eq_zero_of_bandProjector_mulVec_eq_self` | **disjoint bands share no mode:** a vector fixed by both band projectors is zero — the subspace-level reading of "they share no eigenvector" |
| `sum_range_bandProjector_eq_sub` | **the unconditional telescoping law:** `∑_{k<n} B(t_k, t_{k+1}) = P_{t_n} − P_{t_0}` for *any* threshold sequence, ordered or not — the algebraic engine of completeness, load-bearing on the band definition's exact difference shape |
| `sum_range_bandProjector_eq_one` | **completeness under a partition:** a family whose start is strictly below every eigenvalue and whose end covers them all resolves the identity — both covering hypotheses load-bearing (the QA endpoint guards refute the hypothesis-free form) |
| `bandProjector_mul_bandProjector_eq_zero_of_monotone` | **distinct members of a monotone family are orthogonal** — monotonicity supplies exactly the disjointness Step 2 consumes; together with completeness, the identity resolves into mutually orthogonal band projectors |
| `sum_range_bandProjector_mulVec_eq_self` | **the consumer's form:** `∑ B_k *ᵥ x = x` under the same covering hypotheses — the frequency-band decomposition a graph-signal-processing consumer filters with |
| `bandProjector_residual_dotProduct_eq_zero` | **the residual-orthogonality engine** `(x − B *ᵥ x) ⬝ᵥ (B *ᵥ z) = 0` — load-bearing on exactly the two Step-1 facts (symmetry moves the band across the dot product; idempotence collapses the band of the residual to zero) |
| `bandProjector_toEuclidean_apply_eq_orthogonalProjection` | **the Hilbert-projection identification:** Mathlib's `orthogonalProjection` at `LinearMap.range (toEuclideanLin B)` maps the packaged signal to the packaged band-filtered signal — the SGT center's first consumption of `Analysis/InnerProductSpace/Projection.lean` (transport per the resolvent Step-0 precedent) |
| `norm_sub_bandProjector_apply_le` | **the closest-point property:** `‖e x − e (B *ᵥ x)‖ ≤ ‖e x − e y‖` for every fixed point `y` of the band (equivalently every range member) — from `orthogonalProjection_minimal` + `ciInf_le`; the fixed-point hypothesis is load-bearing (the QA guard refutes the hypothesis-free form) |

### `Scaffold.Mathlib.GraphTheory.ClusterProjector` (the set-valued spectral projector)

The cluster projector (proposal `cluster-projector.md`, delivered
2026-08-24 — the recorded follow-on of the band Davis–Kahan
cluster/symmetric deliveries): the orthogonal projector onto the span
of the eigenvectors whose eigenvalues lie in an **arbitrary set**
`S ⊆ ℝ` — `clusterProjector M hM S = ∑_{λᵢ ∈ S} vᵢ vᵢᵀ` over the
proved orthonormal eigenbasis. Pure hard crust, zero axioms. The object
the interval-only shelf lacked: `spectralProjector` selects at `≤ c`,
`bandProjector` at `(a, b]`, while the classical Davis–Kahan/YWS
statements are set-based (a consumer wanting `P_{{|λ| ≥ 3}}` — two
half-lines — had no object to name). The definition is total and
**junk-free** (a set has no orientation, so none of the band family's
`a ≤ b` guards reappear).

Interface highlights, all proved from the Spectral eigenbasis algebra:
the component action (the mirror of PolyFilter's band form, and the
only projector input the set-form Davis–Kahan engine consumes); the
**intersection product law** `P_S * P_T = P_{S ∩ T}` (the nestedness
law's set twin; idempotence is its diagonal, disjoint-set orthogonality
its empty-intersection case); the **complement law**
`1 − P_S = P_{Sᶜ}` (a partition of the eigenbasis filter — the
structural fact the window family lacks, where `1 − bandProjector` is
not a band projector); mode selection (in-`S` fixed, out-of-`S`
annihilated, guard-free); commutation with the carrier matrix; capture
equality at sets; the **band agreement**
`clusterProjector M hM (Set.Ioc a b) = bandProjector M hM a b` (the
entire delivered band family is the interval-set special case); and the
trace/rank supplier (rank = cardinality of the in-`S` eigenbasis
filter, the exact `{0,1}`-spectrum route). The set-form Davis–Kahan
pair consuming this interface lives in
`Analysis.OperatorTheory.Perturbation.BandDavisKahan` (see the
[Perturbation map](perturbation.md)).

QA: `Scaffold/QA/Perturbation/ClusterProjector_QA.lean` — the
non-interval pin `P_{{0,11}} = diag(1,0,1)` on the `diag(0,5,11)`
fixture (a subspace no window expresses, reached through a four-lemma
composition: capture, complement, band agreement, imported threshold
pin), the interface witnesses, the non-interval difference instance at
exact-fit data, the ε = 0 attainment, and the `hfar` fence on the
interior-gap configuration.

### `Scaffold.Mathlib.GraphTheory.Cheeger`

Real definitions: `regularNormalizedLaplacian`, `cutTestVector`.

| Declaration | Kind | Description | Source |
|-------|------|-------------|--------|
| `cheeger_lower_bound` | **theorem (proved 2026-08-23; axiom before, retired)** | `φ(G)²/2 ≤ λ₂(L_sym)` for `d`-regular graphs (the hard direction) — proved by the median-split route: `exists_median`, the median-part level-set inclusions, `hardDirection_perPart`, the norm split, the sweep lemma `cheeger_sweep`, and the `secondEval_variational` + `le_csInf` assembly (Steps 1a/1b/1c of `proposals/discharge-perturbation-axioms.md`) | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_upper_bound` | **theorem (proved 2026-08-18; axiom before, retired)** | `λ₂(L_sym) ≤ 2 φ(G)` for `d`-regular graphs — proved from `secondEval_variational` at the volume-centered cut indicator | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_lower_bound_laplacian` | theorem (2026-08-28, combinatorial spelling) | `d · φ(G)²/2 ≤ λ₂(L)` on `d`-regular graphs — the hard direction transported to the combinatorial Laplacian (`L = d • L_sym` by `smul_regularNormalizedLaplacian`, scaled by `secondEval_smul_of_pos`); first consumer the connectivity floor `edgePerturbation_lambda2_cheeger_floor` | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_upper_bound_laplacian` | theorem (2026-08-28, combinatorial spelling) | `λ₂(L) ≤ 2 d φ(G)` on `d`-regular graphs — the easy-direction ceiling by the same bridge-and-scaling route; attained with equality on `K₂` (`λ₂ = 2 = 2·(1·φ)`); first consumer the connectivity bracket `edgePerturbation_connectivity_bracket` | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_lower_bound_laplacian_of_degree_window` | theorem (2026-08-29, degree-window spelling) | `dmin · φ(G)²/2 ≤ λ₂(L)` on any symmetric nonnegative positive-degree graph with degrees in `[dmin, dmax]` (`0 < dmin`) — the irregular hard direction scaled through the degree sandwich's `mul_degMin_le_lambda2`; reduces to `cheeger_lower_bound_laplacian` at `dmin = d`; first consumer `edgePerturbation_normalized_cheeger_floor` | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_upper_bound_laplacian_of_degree_window` | theorem (2026-08-29, degree-window spelling) | `λ₂(L) ≤ 2 · dmax · φ(G)` — the irregular easy direction scaled through `lambda2_le_mul_degMax`; attained with equality on `K₂` (`λ₂ = 2 = 2·(1·φ)`); first consumer `edgePerturbation_normalized_connectivity_bracket` | [Chung](../sources/chung_spectral_graph.md) |
| `core_sum_abs_sq_sub_sq` | theorem (2026-08-23, hard-direction Step 1a) | **Component A**, the Cauchy–Schwarz core: `(∑ i j, A i j \|f i² − f j²\|)² ≤ E'(f) · 4 ∑ i deg A i f i²` (no sign hypothesis on `f`; `IsSymm` load-bearing on the degree collapse — refuted in QA on asymmetric nonnegative input) | [Chung](../sources/chung_spectral_graph.md) |
| `sq_posPart_sub_add_sq_negPart_sub_le`, `sum_edgeWeight_sq_posPart_add_sq_negPart_le` | theorem (2026-08-23, hard-direction Step 1a) | the *fused* median-part contraction: `(max (a−m) 0 − max (b−m) 0)² + (max (m−a) 0 − max (m−b) 0)² ≤ (a−b)²` pointwise (translation invariance absorbed into the RHS), summed to `E'((x−m)⁺) + E'((x−m)⁻) ≤ E'(x)` under nonneg weights only — the tight form whose cross-edge slack pays for carrying both parts | [Chung](../sources/chung_spectral_graph.md) |
| `sum_deg_mul_eq_of_regular` | theorem (2026-08-23, hard-direction Step 1a) | regularity bridge `∑ i, deg A i · f i² = d · ∑ i, f i²` | [Chung](../sources/chung_spectral_graph.md) |
| `rayleigh_regularNormalizedLaplacian_eq` | theorem (2026-08-23, hard-direction Step 1a) | the normalization `R_{L_sym}(x) = E'(x) / (2·d·‖x‖²)` for `x ≠ 0` — the explicit `2` is the constant budget of the hard-direction chain (`E'` is the ordered double sum, twice `quadForm (laplacian A)`); cross-checked in QA against the independently pinned `λ₂(L_sym) = 2` on `K₂` | [Chung](../sources/chung_spectral_graph.md) |
| `indicatorLE`, `indicatorLE_of_le`, `indicatorLE_of_lt`, `indicatorLE_mono` | def + lemmas (2026-08-23, hard-direction Step 1b) | the closed cumulative level step `1_{t ≤ c}` — the layer-cake primitive of the co-area encoding, stated through `Set.indicator` on `{x \| x ≤ c}` to match `intervalIntegral.integral_indicator`'s truncation shape exactly | [Chung](../sources/chung_spectral_graph.md) |
| `intervalIntegrable_indicatorLE`, `intervalIntegrable_const_mul` | theorem (2026-08-23, hard-direction Step 1b) | integrability of the level step on every interval (indicator of a measurable set on a finite-measure interval) and the constant-multiple helper for the pin's missing `IntervalIntegrable.const_mul` | [Chung](../sources/chung_spectral_graph.md) |
| `integral_indicatorLE`, `integral_abs_indicatorLE_sub` | theorem (2026-08-23, hard-direction Step 1b) | the two layer-cake primitives: `∫₀^R 1_{t ≤ c} dt = c` and `∫₀^R \|1_{t ≤ c} − 1_{t ≤ d}\| dt = \|c − d\|` for `0 ≤ c, d` and `max c d ≤ R` | [Chung](../sources/chung_spectral_graph.md) |
| `sum_pairAbs_eq_two_boundary` | theorem (2026-08-23, hard-direction Step 1b) | the closed-superlevel cut identity `∑ i j, A i j \|1_{t ≤ c_i} − 1_{t ≤ c_j}\| = 2 · boundary S_t` (symmetry load-bearing through `boundary_compl`) | [Chung](../sources/chung_spectral_graph.md) |
| `boundary_ge_of_minority` | theorem (2026-08-23, hard-direction Step 1b) | minority conductance: `cheegerConstant A · d · \|S\| ≤ boundary A S` for nonempty `S` with `2\|S\| ≤ card V` on a `d`-regular network (`0 < d`) | [Chung](../sources/chung_spectral_graph.md) |
| `sum_indicatorLE_eq_card_filter`, `sum_pairAbs_ge` | theorem (2026-08-23, hard-direction Step 1b) | the indicator↔cardinality dictionary (`∑ i, 1_{t ≤ g i} = \|{i : t ≤ g i}\|`, closed-set form) and the per-level co-area bound `2·φ·d·\|S_t\| ≤ ∑ i j, A i j \|1_{t ≤ c_i} − 1_{t ≤ c_j}\|` at every `t > 0` | [Chung](../sources/chung_spectral_graph.md) |
| `coarea_core` | theorem (2026-08-23, hard-direction Step 1b) | **the co-area core, the crux of the hard direction**: `2·(φ·d·∑ y i²) ≤ ∑ i j, A i j · \|y i² − y j²\|` for *any* `y : V → ℝ` whose nonempty closed superlevel sets `{i : t ≤ y i²}` at positive levels are minority-side (`2\|S_t\| ≤ card V`) — no sign or cardinality hypothesis needed; composed with Component A this is the per-part bound `φ²·d·‖y‖² ≤ E'(y)` that Step 1c's assembly consumes. QA: attained *with equality* on `K₂` at `![1,0]` (both sides `2`), strict on the multi-level `C₄` witness (`20φ ≤ 10 < 16`), and the minority hypothesis refuted-on-omission (`4 ≤ 0` at `![1,1]`) | [Chung](../sources/chung_spectral_graph.md) |
| `exists_median` | theorem (2026-08-23, hard-direction Step 1c) | a median exists on every finite value multiset: some `m` with `2·\|{m < x i}\| ≤ n` and `2·\|{x i < m}\| ≤ n` — by pure Finset arithmetic (the at-most-half `T`-set is nonempty at a maximizing vertex; a `T`-minimal value works), no sorting; QA pins the returned median of `![1,1,−1,−1]` into the forced interval `[−1, 1]` | [Chung](../sources/chung_spectral_graph.md) |
| `posPart_superlevel_subset`, `negPart_superlevel_subset`, `minority_posPart`, `minority_negPart` | theorem (2026-08-23, hard-direction Step 1c) | the median-part level-set inclusions: at every `t > 0`, `{t ≤ (x−m)⁺²} ⊆ {x > m}` and `{t ≤ (m−x)⁺²} ⊆ {x < m}` — supplying `coarea_core`'s minority hypothesis for both median parts from the median's two counts | [Chung](../sources/chung_spectral_graph.md) |
| `hardDirection_perPart` | theorem (2026-08-23, hard-direction Step 1c) | the per-part bound `φ²·d·∑ y i² ≤ E'(y)` — `coarea_core` (below) composed with Component A (above) through the regularity bridge, the zero-norm case discharged by nonnegativity; QA pins `1 ≤ 2` on `K₂` at the Step-1b equality fixture | [Chung](../sources/chung_spectral_graph.md) |
| `posPart_add_negPart_sq`, `median_parts_norm` | theorem (2026-08-23, hard-direction Step 1c) | the norm split: pointwise `(x−m)⁺² + (m−x)⁺² = (x−m)²`, summed with `∑ x = 0` to `∑(x−m)⁺² + ∑(m−x)⁺² = ∑x² + n·m² ≥ ∑x²`; QA pins the exact `+4m²` remainder at `m = 0, 1` on `![1,−1,3,−3]` | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_sweep` | theorem (2026-08-23, hard-direction Step 1c) | **the sweep lemma**: `φ²/2 ≤ R_{L_sym}(x)` for every nonzero `x ⊥ 1` — median split, per-part bounds summed through the Step-1a fused contraction, the norm split, and the `E'/(2d‖x‖²)` normalization (exact constant budget); QA on `K₂` (`1/2 ≤ 2`, against the pinned `λ₂`) and on `C₄` at `d = 2` (`φ²/2 ≤ 1/8 < 1 = R`) | [Chung](../sources/chung_spectral_graph.md) |
| `sweep_level_extract` | theorem (2026-08-24, `proposals/sweep-cut-extraction.md`) | **the per-part sweep extraction**: for `y` with minority closed superlevel sets (exactly `coarea_core`'s hypothesis), some level set `S = {i : t ≤ y i²}` at a positive `t` attains `conductance S² ≤ E'(y)/(d·M)` — attainment over the finitely many positive values of `y²` (`Finset.exists_min_image`), the covering fact (every closed superlevel set equals one at an attained value, `Finset.min'`), a non-strict layer-cake integration cloned from `coarea_core`, and Component A; QA forces the extracted set to `{0}` on `C₄` through the level-membership iff, conductance `1` against bound `4/2 = 2` | [Chung](../sources/chung_spectral_graph.md) |
| `cheeger_sweep_cut` | theorem (2026-08-24, `proposals/sweep-cut-extraction.md`) | **the sweep-cut theorem (median assembly)**: for any `x ⊥ 1`, `x ≠ 0`, a closed superlevel or sublevel set of `x` itself satisfies `conductance S² ≤ 2·R_{L_sym}(x)` — the same constant as `cheeger_sweep` with the witness an explicit member of the sweep family (the median parts supply `sweep_level_extract`'s hypothesis verbatim; the product test picks the part, degenerate single-part cases included; the fused contraction, norm split, and Step-1a normalization close). QA characterizes the family at `cycSweepX` (best swept cut `1` within bound `2`, not optimal) and `cycX2` (swept cut ties the global optimum `1/2`), and refutes the orthogonality-dropped form on the constant vector (empty family) | [Chung](../sources/chung_spectral_graph.md) |
| `vol_le_vol_of_subset`, `vol_empty` | theorem (2026-08-25/26, `VolumeHardDirection`) | volume arithmetic: monotonicity along subset and the empty-set collapse — the volume replacements for the cardinality steps of the regular chain | [Chung](../sources/chung_spectral_graph.md) |
| `exists_median_vol` | theorem (2026-08-25/26, `VolumeHardDirection`) | **the volume median**: a level `t` with `vol {y² > t} ≤ vol V/2` and `vol V/2 ≤ vol {y² ≥ t}` — the same maximizing-vertex/minimal-member Finset argument as `exists_median` with `vol` replacing `card`; pure Finset arithmetic, no sorting; QA pins and forces the returned volume median of P₃'s cut vector into its computed interval | [Chung](../sources/chung_spectral_graph.md) |
| `boundary_ge_of_minority_vol` | theorem (2026-08-25/26, `VolumeHardDirection`) | minority conductance at volume strength: `cheegerConstant A · vol S ≤ boundary A S` for nonempty minority `S` (`vol S ≤ vol V/2`) — where the regular proof needed `vol_eq_of_regular` to collapse into cardinality, here `min (vol S) (vol Sᶜ) = vol S` is pure `vol_compl` arithmetic; QA fences the minority-dropped form at the full vertex set of `K₂` | [Chung](../sources/chung_spectral_graph.md) |
| `sum_deg_mul_indicatorLE_eq_vol`, `sum_pairAbs_ge_vol` | theorem (2026-08-25/26, `VolumeHardDirection`) | the degree-weighted mass side of the layer cake: the level-set volume dictionary (`∑ deg · 1_{t ≤ g i} = vol {t ≤ g i}`) and the per-level co-area bound at volume strength | [Chung](../sources/chung_spectral_graph.md) |
| `coarea_core_vol` | theorem (2026-08-25/26, `VolumeHardDirection`) | **the degree-weighted layer-cake core**: `φ · ∑ deg i · y i² ≤ ∑ i j, A i j \|y i² − y j²\|` for any `y` whose nonempty closed superlevel sets at positive levels are volume-minority — the `indicatorLE` integrability layer reused with the threshold integral, the boundary inequality at volume strength, the `t = 0` failure point absorbed measure-theoretically; QA pins the equality on `K₂` (both sides `2` at `![1,0]`) and fences the minority hypothesis | [Chung](../sources/chung_spectral_graph.md) |
| `hardDirection_perPart_vol` | theorem (2026-08-25/26, `VolumeHardDirection`) | the per-part bound at volume strength `φ² · ∑ deg i · y i² ≤ E'(y)` — the regular family's Cauchy–Schwarz core (`core_sum_abs_sq_sub_sq`, *already stated degree-weighted*) and fused contraction (nonnegative weights only) consumed **verbatim**, no regularity bridge anywhere; QA pins the instance on `K₂` raw | [Chung](../sources/chung_spectral_graph.md) |
| `minority_posPart_vol`, `minority_negPart_vol`, `median_parts_norm_vol` | theorem (2026-08-25/26, `VolumeHardDirection`) | the median-part level-set inclusions at volume strength (supplying `coarea_core_vol`'s minority hypothesis from the volume median's two counts) and the weighted norm split carrying the full degree-weighted norm | [Chung](../sources/chung_spectral_graph.md) |

Statement-shape correction (2026-08-18): through 2026-08-17 both axioms
stated the spectral side as `lambda2 (regularNormalizedLaplacian A d)`,
which reads `λ₂(L(L_sym)) = λ₂(-L_sym)` — materially false on the
two-vertex edge (`1/2 ≤ 0`; refuted by
`QA.old_cheeger_lower_bound_refuted_QA`). Both are restated at
`secondEval (regularNormalizedLaplacian A d) …` — the source-faithful
`λ₂(L_sym)`, pinned to its classical value `2` on `K₂` by
`QA.edge_normLap_secondEval_eq_two_QA`.

Hard-direction program (2026-08-22 survey, 2026-08-23 Steps 1a, 1b,
and 1c delivered — **the axiom retired, program complete**): the
pure-algebra layer above is Step 1a, the co-area layer Step 1b, and the
median/assembly layer Step 1c of the
`discharge-perturbation-axioms.md` Cheeger track. `cheeger_lower_bound`
is proved at the unchanged statement as of 2026-08-23 (explicit axioms
10 → 9): the sweep lemma plus the `secondEval_variational` + `le_csInf`
assembly at the `Pi.single` witness. The Step-1a delivery recorded a
constant-budget correction to the survey's summation route (the fused
contraction and the explicit-`2` normalization are the tight shapes
1b/1c consume); the Step-1b delivery recorded a second survey
correction (the priced hand Fubini exists in the pin as
`intervalIntegral.integral_finset_sum`) and two verified hypothesis
drops (`hynonneg`, `hcard`). With both directions proved, the Chung
source's rows are all proved theorems.

### `Scaffold.Mathlib.GraphTheory.Fiedler` (Fiedler vector, Phases A–C)

The Fiedler-vector interface — proposal `fiedler-partitioning.md`
Phase A (2026-08-18), all proved, no axioms. Real definitions:
`fiedlerIndex` (an eigenbasis index carrying `lambda2`, fixed by
classical choice through `evals_mem_eigvalOf` — the proposal's sketch
indexed `eigvecOf` by a sorted-spectrum position, which is not that
function's type; deviation recorded in the module docstring) and
`fiedlerVector` (the unit eigenvector there), plus the sign-pattern
partition `fiedlerPartition`. Phase B (2026-08-23, the module now
importing `Cheeger`): the certified conductance cut, pure hard crust.

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
| `fiedlerVector_rayleigh_regularNormalizedLaplacian` | **Phase B bridge:** `R_{L_sym}(f) = lambda2 / d` (unit norm × the quadratic-form transfer × the energy identity) |
| `cheeger_cut_existence` | **Phase B, the certified conductance cut:** on every connected `d`-regular graph, `∃ S` nonempty proper with `conductance S ^ 2 ≤ 2 · lambda2 / d` — the classical Cheeger cut-existence corollary, composed from the proved sweep lemma at the Fiedler vector + `cheegerConstant_attained` (the sign cut itself is not certifiable from `lambda2` alone; the swept-level-set extraction is the named follow-on) |
| `fiedler_sweep_cut` | **Phase C (2026-08-24, `proposals/sweep-cut-extraction.md`), the swept Fiedler cut:** on every connected `d`-regular graph, a *closed superlevel or sublevel set of the Fiedler vector* (the object the spectral-partitioning sweep returns, not the non-constructive minimizer) satisfies `conductance S ^ 2 ≤ 2 · lambda2 / d` — `cheeger_sweep_cut` at the Fiedler vector through the Phase B Rayleigh bridge; QA identifies the cut on `K₂` (singleton, conductance `1` = the pinned `cheegerConstant` — the sweep is exact there) and characterizes the swept family through the antisymmetry pins |
| `fiedlerSubspace_stability` | **(2026-08-28, `proposals/fiedler-subspace-stability-davis-kahan.md` Step 1) the Fiedler-subspace Davis–Kahan wrapper:** on every symmetric base `A` and perturbation `E` with `3 ≤ card V` and separation `δ ≤ λ₃(L(A+E)) − λ₂(L A)`, `‖initialProjector (L(A+E)) 1 − initialProjector (L A) 1‖ ≤ ‖laplacian E‖/δ` — the bottom-2 invariant spectral subspace (on a connected base, the Fiedler cluster `span {onesVec, fiedlerVector}`) moves by at most the Laplacian perturbation's norm over the gap; the proved `davis_kahan_sin_theta`'s first graph-theoretic consumer, through the new `laplacian_add` transport (module: `Spectral`); no connectivity hypothesis, tie-awareness inherited (QA: at the K₃ `λ₂ = λ₃` tie the hypothesis set is provably empty) |

The Step-2 headline — the proposal's payoff — sits in the same module:

| Declaration | Statement |
| --- | --- |
| `fiedlerLine_stability` | **(2026-08-28, the same proposal's Step 2) the Fiedler-line rotation:** on connected base `A` and perturbed `A + E` (symmetric, nonnegative, `3 ≤ card V`) at Step 1's separation `δ ≤ λ₃(L(A+E)) − λ₂(L A)`, the residual Fiedler-mode projector difference `‖(initialProjector (L(A+E)) 1 − initialProjector (L(A+E)) 0) − (initialProjector (L A) 1 − initialProjector (L A) 0)‖ ≤ ‖laplacian E‖/δ` — the rank-2 rotation attributed to the Fiedler component itself, because connected graphs never move their kernel direction; the common-kernel identification telescopes the residual to the Step-1 projector difference (QA: the P₃ → K₃ edge-addition instance with the bound exactly `≤ 1` on Davis–Kahan's own tie branch, the perturbation norm pinned `= 2` both sides, and the disconnected fence proving connectivity load-bearing) |

The identification layer behind it lives in `GraphTheory.Spectral`:
`dotProduct_mulVec_comm_of_isSymm` (the self-adjoint coordinate form),
`eq_of_isSymm_idempotent_of_forall_mulVec_eq` (symmetric idempotents
determined by fixed space — `ker P = Fix(P)ᗮ` algebraically),
`spectralProjector_mulVec_eq_sum` (the projector's action in its own
eigenbasis), `eigvecOf_expansion` (every vector is its eigenbasis
expansion), `initialProjector_laplacian_zero_fix_iff` (the index-0
projector's fixed space is exactly the kernel, connectivity-free), and
`initialProjector_laplacian_zero_eq_of_connected` (every connected
Laplacian carries the same index-0 projector — the uniqueness lemma
joined to `laplacian_mulVec_eq_zero_iff_exists_const`). The Step-1
engine lemmas also live in `GraphTheory.Spectral`:
`laplacian_zero` and `laplacian_add` (the perturbed-adjacency Laplacian
identity), `evals_congr` (general-index proof-irrelevance for the
sorted spectrum), and `laplacian_evals_zero` (the bottom Laplacian
eigenvalue is exactly `0` on symmetric nonnegative weights, no
connectivity hypothesis — the pin every exact Laplacian-spectrum
fixture starts from).

`GraphTheory.Cheeger` additionally carries Phase B's enabling lemma:
`cheegerConstant_attained` (the conductance `sInf` realized as a
minimum by `Finset.exists_min_image` over the filtered powerset — no
regularity hypothesis; the step converting Cheeger's inequality about
an infimum into a statement about an actual cut).

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
| `normalizedLaplacian_mul_degreeSqrt` | the left-multiplied congruence `L_sym √D = (1/√D) L` (2026-08-25) |
| `normalizedLaplacian_mulVec_degreeSqrt_onesVec` | **the kernel vector is `√D · onesVec`, not `onesVec`** (2026-08-25) — the structural fact separating the irregular variational picture; consumed by `cheeger_upper_bound_normalized` |
| `degreeInvSqrt_apply_eq_zero_iff` | **the degenerate-degree corners pinned** (2026-08-29): the reciprocal factor vanishes exactly at nonpositive degrees — both the zero corner and the *negative* corner (`Real.sqrt` of a negative is `0`), the `p ≠ ½` outcomes route |
| `normalizedLaplacian_eq_one_of_forall_deg_nonpos` | the identity degeneration: at all-nonpositive degrees `L_sym = 1`, whose sorted spectrum is `1` (`evals_one`) — the junk corner refutation-fixture design must predict |
| `normalizedLaplacian_eq_regularNormalizedLaplacian` | agreement with the regular cone |
| `walkTransitionMatrix`, `walkLaplacian` | definitions: general walk form `D⁻¹A`, `I − D⁻¹A` |
| `walkTransitionMatrix_row_sum` | row-stochasticity on irregular graphs (positive degrees) |
| `degreeSqrt_mul_walkLaplacian_mul_degreeInvSqrt` | similarity `√D · L_walk · (1/√D) = L_sym` |

The degree eigenvalue sandwich (2026-08-29,
`proposals/degree-eigenvalue-sandwich.md`, delivered in
`VariationalTransfer.lean`; all proved, no axioms) — the
eigenvalue-level bridge between the combinatorial and normalized
worlds, at the irregular family's own hypothesis shape (symmetric
nonnegative positive degrees, no connectivity):

| Declaration | Content |
|-------------|---------|
| `degreeSqrtEquiv` | the degree stretch `x ↦ √D x` as a linear equivalence (inverse `1/√D`; positive degrees) |
| `sum_deg_mul_sq_ge`, `sum_deg_mul_sq_le` | the degree-weighted squared norm bracketed by `dmin·‖x‖²` and `dmax·‖x‖²` |
| `rayleigh_normalizedLaplacian_le_div` | pointwise bracket upper side: `R_{L_sym}(√D x) ≤ R_L(x)/dmin` (PSD load-bearing) |
| `rayleigh_le_mul_rayleigh_normalizedLaplacian` | pointwise bracket lower side: `R_L(x) ≤ dmax · R_{L_sym}(√D x)` |
| `normalizedLaplacian_evals_zero` | the bottom eigenvalue of `L_sym` is exactly `0` (no connectivity) — the normalized counterpart of `laplacian_evals_zero` |
| `evals_normalizedLaplacian_le_div` | **sandwich upper side**: `evals (L_sym) k ≤ evals (laplacian) k / dmin` at every sorted index, via the subspace min–max with the existence-form witness subspace stretched by `√D` |
| `div_le_evals_normalizedLaplacian` | **sandwich lower side**: `evals (laplacian) k / dmax ≤ evals (L_sym) k`, via the competitor form on the un-stretched preimage |
| `secondEval_normalizedLaplacian_le_div`, `div_le_secondEval_normalizedLaplacian` | the interface pair at `lambda2`/`secondEval` (the shape the irregular Cheeger-window consumer composes) |
| `mul_degMin_le_lambda2`, `lambda2_le_mul_degMax` | division-free mul forms of both sides |

Eigenpair transfer through the similarity (2026-08-22, proposal
`mixing-time-bound.md` Step 1, no axioms; the section closing this
module's named residual gap — the walk form is not symmetric, so `evals`
does not apply to it, and the pin has no charpoly-similarity interface):

| Declaration | Content |
|-------------|---------|
| `eigvecOf_ne_zero` | eigenbasis vectors are nonzero (unit self-inner-product) |
| `walkLaplacian_mulVec_degreeInvSqrt` | **forward transfer**: a `μ`-eigenpair of `L_sym` conjugates to a `μ`-eigenpair of `L_walk` at eigenvector `(1/√D) *ᵥ v` |
| `normalizedLaplacian_mulVec_degreeSqrt` | **backward transfer**: a `μ`-eigenpair of `L_walk` conjugates back to `L_sym` at eigenvector `√D *ᵥ w` |
| `walkTransitionMatrix_mulVec_degreeInvSqrt` | transition form: `μ`-eigenpair of `L_sym` gives a `(1 − μ)`-eigenpair of `P = D⁻¹A` |
| `walkLaplacian_mulVec_eigvecOf`, `walkTransitionMatrix_mulVec_eigvecOf` | the transfer instantiated at the spectral-theorem eigenbasis of `L_sym` |
| `degreeInvSqrt_mulVec_ne_zero` | conjugation by the invertible `1/√D` preserves nonvanishing |
| `walk_eigvec_expansion` | completeness of the transferred family: every vector reconstructed from the conjugated walk eigenvectors (the diagonalizability interface) |
| `walkEvals` | definition: the walk spectrum `1 − evals (L_sym)`, transferred through the similarity |
| `exists_eigenvector_walkTransitionMatrix_eq_walkEvals` | every `walkEvals` entry is a genuine eigenvalue of `P` with an explicit nonzero conjugated-eigenvector witness |

### `Scaffold.Mathlib.GraphTheory.Stationary` (first walk/normalized consumer)

All statements proved (stationarity/kernel layer 2026-08-17;
reversibility/detailed-balance layer 2026-08-22,
`proposals/reversibility-and-heat-semigroup.md` Phase A), no axioms;
consumes the `RandomWalk` and `Normalized` interfaces — demonstrated
downstream reuse:

| Declaration | Content |
|-------------|---------|
| `mulVec_one_eq_deg` | `A *ᵥ 1 = deg A` (row sums in vector form) |
| `normalizedLaplacian_mulVec_sqrtDeg_eq_zero` | kernel of `L_sym` is `√deg` — normalized counterpart of `laplacian_ones_in_kernel` |
| `walkTransitionMatrix_transpose_mulVec_deg` | degree measure stationary for the adjoint walk (`π ∝ deg`; Markov-mixing consumer interface) |
| `walk_detailed_balance` | **reversibility**, degree-measure form: `deg i * P i j = deg j * P j i` (both sides `A i j`); the property that makes spectral methods apply to the walk |
| `walk_detailed_balance_measure` | **reversibility**, stationary-measure form: `π i * P i j = π j * P j i` with `π i = deg i / vol univ`; no volume hypothesis carried |
| `diagonal_deg_mul_walkTransitionMatrix_isSymm` | the matrix packaging: `D * P` is symmetric — reversibility *is* symmetrizability (the self-adjointness interface spectral arguments consume) |
| `transitionMatrix_detailed_balance_uniform` | regular-case uniform-measure balance, composed from `RandomWalk.transitionMatrix_symmetric` |
| `randomWalkLaplacian_mulVec_one_eq_zero` | conservation of mass, regular case (consumes `RandomWalk.transitionMatrix_row_sum`) |
| `walkLaplacian_mulVec_one_eq_zero` | conservation of mass, irregular case (consumes `Normalized.walkTransitionMatrix_row_sum`) |

(The entry form `Normalized.walkTransitionMatrix_apply`
(`P i j = (deg A i)⁻¹ * A i j`) was added alongside, next to the
`walkTransitionMatrix` definition.)

### `Scaffold.Mathlib.GraphTheory.Mixing` (the ℓ²-mixing proxy, decay engine, and closing mixing bound)

All statements proved (2026-08-22, `proposals/mixing-time-bound.md`,
the program complete: Steps 1–2 plus both Step-3 components), no
axioms; the third consuming module of the walk interfaces (after
`Stationary` and `VariationalTransfer`) and the first consumer of the
Phase A detailed-balance layer. The scoping record: the weighted χ²
form is primary (the form in which Step 3's decay bound is
Parseval-exact); the plain Euclidean distance is a corollary bridge.

| Declaration | Content |
|-------------|---------|
| `stationaryVec` | the stationary distribution as a vector: `π i = deg A i / vol A univ` (definition) |
| `vol_univ_pos` | positive degrees + nonempty ⟹ `0 < vol A univ` |
| `stationaryVec_pos` | `π` strictly positive entrywise — what makes every χ² division meaningful |
| `sum_stationaryVec` | `∑ π = 1`: the stationary vector is a probability vector |
| `stationaryVec_eq_inv_smul_deg` | `π = vol⁻¹ • deg` (unpacking) |
| `walk_isStationary` | the adjoint walk fixes `π` — the probability-measure form of the proved degree-form stationarity |
| `walkDistribution` | the walk law started at `x` after `t` steps: `(Pᵀ)ᵗ *ᵥ δₓ` (definition) |
| `walkDistribution_zero` / `walkDistribution_succ` | `ν₀ = δₓ`; `ν_{t+1} = Pᵀ *ᵥ ν_t` (evolution equations) |
| `sum_walkDistribution` | mass conservation: `∑ ν_t = 1` at every `t` (load-bearing on row-stochasticity) |
| `walkTransitionMatrix_nonneg` / `walkDistribution_nonneg` | entrywise nonnegativity of the walk kernel and the walk law at every time — with `sum_walkDistribution`, what makes `ν_{t₀}` a legal factor distribution for `Probability.IIDProduct.iidPMF` (the empirical-concentration consumer `Derived.EmpiricalStationary`) |
| `walkDensity` | the density `h_t = ν_t/π` (definition) — the coordinate the transferred eigenbasis diagonalizes |
| `walkDensity_succ` | **the density evolution** `h_{t+1} = P *ᵥ h_t` — detailed balance in action (the Phase A interface's first consumer); the interface Step 3 consumes |
| `chiSquareDistance` | the χ² mixing distance `∑ (ν_t − π)²/π` (definition; junk `0` at `π i = 0`) |
| `chiSquareDistance_nonneg` | nonnegativity (squares over a positive measure) |
| `chiSquareDistance_eq_zero_iff` | `χ²(t, x) = 0 ↔ ν_t = π` (vanishing characterization; positivity load-bearing) |
| `chiSquareDistance_zero` | `χ²(0, x) = (π x)⁻¹ − 1` — Step 3's normalization constant |
| `chiSquareDistance_eq_sum_smul` | density form `∑ π (h_t − 1)²` — the π-weighted norm Step 3 computes by Parseval |
| `sum_sub_sq_walkDistribution_le` | the plain-ℓ² corollary bridge: `∑ (ν−π)² ≤ c · χ²` whenever every `π i ≤ c` |
| `eigvecOf_dotProduct_degreeSqrt_mulVec_pow_walkTransitionMatrix` | **eigencoordinate evolution (Step 3 engine):** the `i`-th eigencoefficient of the conjugated `t`-step walk evolution is the initial coefficient times `(1 − μ i)ᵗ` |
| `dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix` | **the Parseval-exact decay identity:** the squared conjugated norm is the eigenvalue-weighted sum of squared initial eigencoordinates — no inequality lost |
| `dotProduct_self_degreeSqrt_mulVec_pow_walkTransitionMatrix_le` | **the ℓ²(π) contraction, norm form:** under the value-based mode hypothesis (no kernel component) and rate hypothesis (`\|1 − μ i\| ≤ r`), `‖√D (Pᵗ g)‖² ≤ r^{2t} ‖√D g‖²` — term-wise, no case split on `r < 1` |
| `sum_stationaryVec_smul_sq_eq` | **the π-norm bridge** `∑ π f² = vol⁻¹ · ‖√D f‖²` (degree nonnegativity only) |
| `sum_stationaryVec_smul_sq_pow_walkTransitionMatrix_le` | **the ℓ²(π) contraction (headline):** `∑ π ((Pᵗ g))² ≤ r^{2t} ∑ π g²` — the exact interface the Step-3 χ² assembly instantiates at `g = h₀ − 1` |
| `walkDensity_sub_one` | **centered evolution (χ² assembly):** `h_t − 1 = Pᵗ *ᵥ (h₀ − 1)` — one induction from `walkDensity_succ` plus the constant fix `P *ᵥ 1 = 1` |
| `sum_deg_mul_walkDensity_sub_one_eq_zero` | **mass conservation in the conjugated pairing:** `∑ deg (h₀ − 1) = 0` (termwise `deg · h₀ = vol · ν₀`, both sums `vol`) |
| `eigvecOf_dotProduct_degreeSqrt_walkDensity_sub_one_of_eigvalOf_eq_zero` | **the connectivity mode derivation:** on a connected graph every `μ = 0` eigenvector of `L_sym` is orthogonal to `√D *ᵥ (h₀ − 1)` — the kernel transferred through the congruence `√D L_sym √D = L`, pinned constant by the shelf's kernel theorem, collapsed by mass conservation |
| `chiSquareDistance_le_of_connected` | **the closing mixing bound:** `χ²(t, x) ≤ r ^ (2t) · ((π x)⁻¹ − 1)` on connected symmetric-nonnegative positive-degree networks under the rate hypothesis — the mixing-time program's target statement, mode hypothesis *derived* from connectivity rather than assumed |

Supporting additions elsewhere: `Spectral.eigvecOf_dotProduct_one_sub_mulVec`
(the generic eigenaction at `1 − M`, composed from
`dotProduct_eigvecOf_mulVec`) and in `Normalized`
`degreeSqrt_mul_walkTransitionMatrix_eq` (`√D · P = (1 − L_sym) · √D`)
with `degreeSqrt_mulVec_pow_walkTransitionMatrix` (the conjugated-power
transfer — `√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)`), plus the
χ²-assembly entry lemmas `walkTransitionMatrix_mulVec_one`
(the constant fix `P *ᵥ 1 = 1`), `degreeSqrt_mulVec_apply`, and
`degreeInvSqrt_mulVec_apply` (the conjugating actions' entry forms).

### `Scaffold.Mathlib.GraphTheory.Directed` (the directed degree layer and the directed normalized Laplacian)

All statements proved (2026-08-22, `proposals/directed-graph-operators.md`
— Steps 0+1, then Step 2 + the Step-3 agreement brick; the program
complete), no axioms, no symmetry assumed anywhere it is not named. The
Step-0 record's discovery shapes the module: the undirected shelf's
`deg` (the row sum) *is* the out-degree and `walkTransitionMatrix =
D⁻¹ A` / `walkLaplacian = I − D⁻¹ A` are defined symmetry-free — so
this module adds the genuinely new directed quantity (the in-degree),
the degree-level agreement theorems, and the directed normalized
Laplacian at the out-degree-symmetrized convention, while QA
certifies the pre-existing walk operators on asymmetric input and
refutes PSD-ness of the new operator (the calibration boundary).

| Declaration | Content |
|-------------|---------|
| `outDeg` | the out-degree `∑ j, A i j` — definitionally the shelf's `deg` (definition) |
| `inDeg` | the in-degree `∑ j, A j i`, the column sum — the genuinely new directed quantity (definition) |
| `outDeg_eq_deg` | the out-degree *is* `deg` (`rfl`) — every `deg`-indexed theorem applies to directed out-degrees verbatim |
| `inDeg_eq_deg_transpose` | the in-degree is `deg` of the transposed network (`rfl`) |
| `inDeg_eq_outDeg_of_isSymm` | agreement on the symmetric cone: `A.IsSymm → inDeg A i = outDeg A i` — the degree brick of the proposal's Step-3 acceptance bar |
| `inDeg_eq_deg_of_isSymm` | agreement with the shelf: `A.IsSymm → inDeg A i = deg A i` |
| `sum_outDeg_eq_sum_inDeg` | **directed handshaking:** `∑ i, outDeg A i = ∑ i, inDeg A i` with no nonnegativity or symmetry hypothesis (`Finset.sum_comm`) |
| `directedNormalizedLaplacian` | the directed normalized Laplacian `I − ½(SAS + SAᵀS)`, `S = degreeInvSqrt` (the out-degree normalization, Step-0 decision (b); definition — total, noncomputable through `Real.sqrt`) |
| `directedNormalizedLaplacian_apply` | the entry form `δ_ij − ½·(√d_i)⁻¹(A_ij + A_ji)(√d_j)⁻¹` — the same second term in both arc directions *is* the symmetrization |
| `directedNormalizedLaplacian_isSymm` | **symmetry, hypothesis-free, for every matrix** — the two defining halves are transposes of each other; the directed axis' one symmetric operator (contrast the provably asymmetric walk operators) |
| `directedNormalizedLaplacian_eq_normalizedLaplacian` | **the Step-3 acceptance bar:** `A.IsSymm → L_dir = normalizedLaplacian` — both halves coincide on the symmetric cone; every directed construction reduces to its undirected counterpart there |
| `degreeSqrt_mul_directedNormalizedLaplacian_mul_degreeSqrt` | the square-root-free conjugate `√D L_dir √D = degreeMatrix A − ½(A + Aᵀ)` — the symmetrized adjacency at out-degree normalization; every quadratic-form statement transfers to this pair |

### `Scaffold.Mathlib.GraphTheory.IrreducibleStationary` (irreducible stationary distributions — the first Perron–Frobenius consumer)

The first *theorem* consumer of the admitted `perron_frobenius` axiom
(delivered 2026-08-24, `proposals/irreducible-stationary-distributions.md`,
Steps 0+1 in one run). The five stationary-distribution theorems are
**conditional on that axiom** — Lean-checked deductions whose trust
cost is the axiom's, never to be described as foundationally proved;
the two transfer lemmas are unconditional. The derivation consumes the
axiom's eigenvalue-identification clause (any nonnegative eigenvector's
eigenvalue is the Perron root — pinning the walk's root to `1` through
the shelf's row-stochasticity at `onesVec`) and its uniqueness clause
structurally, with the transposed application's root pinned by the
bilinear pairing through the pin's `Matrix.dotProduct_mulVec`/
`Matrix.mulVec_transpose` — no charpoly, rootMultiplicity, or complex
domination anywhere. QA at
`Scaffold/QA/SpectralGraph/IrreducibleStationary_QA.lean` (94
declarations: the asymmetric directed star with the hand value
identified through the `∃!`, the symmetric-cone `K₂` agreement with
`stationaryVec` through the shelf's detailed-balance chain, and the
reducibility fence refuting the hypothesis-free `∃!` and
scale-uniqueness conclusions).

| Declaration | Content |
|-------------|---------|
| `isIrreducible_transpose` | strong connectivity is arc-reversal invariant: `M.IsIrreducible → Mᵀ.IsIrreducible` (unconditional; the private `ReflTransGen` flip induction behind it) |
| `walkTransitionMatrix_isIrreducible` | positive row scaling preserves the support digraph: `A.IsIrreducible` + positive out-degrees → the walk matrix irreducible (unconditional; the private `ReflTransGen` congruence — the pin has `mono` for `ReflGen` only) |
| `exists_walkPerronVector` | **the transposed Perron engine** (conditional): a strictly positive vector fixed by `Pᵀ *ᵥ ·`, unique up to positive scalars among nonzero nonnegative fixed vectors — the Perron vector of `Pᵀ` with the root computed to be `1` |
| `exists_stationaryVec_of_irreducible` | **existence with full support** (conditional): a strictly positive, mass-one stationary distribution `π ᵥ* P = π` for every irreducible nonnegative walk — the directed-axis statement the undirected shelf cannot reach |
| `stationaryVec_smul_of_irreducible` | **uniqueness up to positive scale** (conditional) among all nonzero nonnegative stationary vectors, the scale-free form |
| `existsUnique_stationaryVec_of_irreducible` | **the textbook `∃!`** (conditional): exactly one nonnegative mass-one vector fixed by the walk, positivity derived rather than hypothesized |
| `stationaryVec_pos_of_irreducible` | **full support** (conditional): every nonzero nonnegative stationary vector is strictly positive — no stationary distribution of an irreducible chain can vanish anywhere |

### `Scaffold.Mathlib.GraphTheory.PageRank` (the teleportation-regularized walk — the second Perron–Frobenius consumer)

The Google matrix `G i j = α * P i j + (1 - α) * (card V)⁻¹` (delivered
2026-08-24, `proposals/pagerank-distributions.md`, Steps 0+1 in one
run). The construction's content is the **teleportation floor**: every
entry positive on the damping window `[0, 1)`, so irreducibility is
*derived* rather than assumed and the delivered
`IrreducibleStationary` layer composes at `G` through the general
row-stochasticity bridge — extending the stationary theory to
**reducible** input with no irreducibility hypothesis in any
statement. The three PageRank theorems are **conditional on the
`perron_frobenius` axiom** (no new axiom contact — the composition
consumes the delivered layer); the nine structural declarations are
unconditional. QA at
`Scaffold/QA/SpectralGraph/PageRank_QA.lean` (89 declarations by the
generator metric: the reducible two-edge fixture's uniform PageRank
verified completely raw with the `∃!` join, the asymmetric star's
`(4/9, 5/18, 5/18)` verified raw and provably distinct from the raw
stationary, and both endpoint fences refuted in proved form —
`α = 1` teleportation-removed, `α = -1` identity degeneration — with
row stochasticity pinned intact at both).

| Declaration | Content |
|-------------|---------|
| `googleMatrix` | the teleportation-regularized walk matrix, entry form `α * P i j + (1 - α) * (card V)⁻¹` (the Page–Brin damping construction; entry form for literal-index pinning) |
| `googleMatrix_apply` | the entry-level interface every entry computation consumes |
| `walkTransitionMatrix_nonneg` | the walk of a nonnegative positive-degree network is nonnegative (unconditional; the sign-pattern reading the floor consumes) |
| `googleMatrix_nonneg` | nonnegativity on the damping window `[0, 1]` (unconditional; the consumer layer's `hnn` discharge) |
| `googleMatrix_pos` | **the teleportation floor**: `0 < G i j` at every pair on `[0, 1)` with nonempty `V` — regardless of the input walk's support, reducibility, or asymmetry (unconditional; the `googleMatrix_isIrreducible` engine) |
| `googleMatrix_row_sum` | row stochasticity, for **every** real `α` (affine — survives both fence endpoints where uniqueness dies; unconditional) |
| `googleMatrix_deg_eq_one` | all degrees one — the consumer layer's positive-degree hypothesis discharged unconditionally |
| `googleMatrix_isIrreducible` | **irreducibility derived, not assumed**: every pair one positive arc apart through the floor, `ReflTransGen.single` per pair — reducible input included (unconditional) |
| `walkTransitionMatrix_eq_of_row_sum_one` | **the general bridge**: any row-stochastic matrix is its own walk transition matrix — the composition point for any row-stochastic consumer, the Google matrix the first (unconditional) |
| `exists_pageRankVec` | **existence** (conditional on `perron_frobenius`): a strictly positive, mass-one `π ᵥ* G = π` for every nonnegative positive-degree network — reducible or not |
| `existsUnique_pageRankVec` | **the `∃!`** (conditional): exactly one nonnegative stationary distribution of the Google walk, **no irreducibility hypothesis on the input** — the statement the raw walk cannot support on reducible input |
| `pageRankVec_pos` | **full support** (conditional): every nonzero nonnegative vector fixed by `G` is strictly positive — even a vertex with no inbound walk arcs receives teleportation mass |

### `Scaffold.Mathlib.GraphTheory.DirectedMixing` (the PageRank power iteration — the first primitive-power-convergence consumer)

The directed axis' first convergence theorem (delivered 2026-08-24,
`proposals/primitive-power-convergence.md`, Steps 0+1 in one run). The
delivered PageRank layer proved the stationary theory (existence,
`∃!`, full support, all conditional on `perron_frobenius`) while its
own statement-shapes section recorded that power iteration "needs
strict spectral dominance, which the axiom deliberately does not
claim" — this module discharges that recorded obligation at the
convergence level: the teleportation floor makes the Google matrix
strictly positive hence **primitive at `k = 1`** (aperiodicity
derived, never assumed), so the power iteration converges and the
PageRank distribution is *computable*. The three convergence theorems
are **conditional on `primitive_power_tendsto` alone** — no
`perron_frobenius` contact (`#print axioms`-verified): producing `π`
needs PF, concluding convergence does not, the two trust costs
independent. QA at `Scaffold/QA/SpectralGraph/DirectedMixing_QA.lean`
(30 declarations by the generator metric: the reducible-fixture
positive witness with the limit pinned to the raw-verified uniform
value and the second iterate computed raw at `3/16 < 1/4`; the
periodicity refutation — the directed 2-cycle nonnegative,
row-stochastic, irreducible, with verified stationary distribution,
its power action provably having no limit at all, exactly `hprim`
isolated; and the `onesVec` coherence join deriving `π ⬝ᵥ 1 = 1` from
the axiom against the raw sum).

| Declaration | Content |
|-------------|---------|
| `googleMatrix_isPrimitive` | the Google matrix is primitive on `[0, 1)` — `isPrimitive_of_pos` at the teleportation floor; strictly stronger than the delivered irreducibility (unconditional) |
| `pageRank_powerIteration` | **the classical PageRank algorithm as a theorem** (conditional on `primitive_power_tendsto` alone): `(G ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` at any nonnegative mass-one stationary `π` — of which the delivered `∃!` says there is exactly one |
| `pageRank_entrywise_tendsto` | the `t`-step transition probability `(G ^ t) i j → π j`, independent of the start (conditional, same axiom alone) |
| `pageRank_walk_tendsto` | the Markov-chain mixing first slice: `ν ᵥ* (G ^ t) → π` for every start summing to one, entrywise topology (conditional, same axiom alone; rates out of scope) |
| `googleMatrix_pow_mulVec_onesVec` | powers of the Google matrix fix `onesVec` — the mass bookkeeping translation (unconditional; the QA coherence join's other half) |

The admission's own module is
`Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence` (the axiom,
`Matrix.IsPrimitive`, and the unconditional transfer layer — see the
[Linear Algebra map](linear_algebra.md)).

### `Scaffold.Mathlib.GraphTheory.Magnetic` (the magnetic Laplacian — the directed-native Hermitian operator)

The directed axis' third spectral toolkit (delivered 2026-08-25,
`proposals/magnetic-laplacian.md`, backlog item 8's reserved "further,
separate slice" per that item's own scope note) and the shelf's first
complex-valued object: the **magnetic Laplacian**
`magneticLaplacian A Θ := D_sym − ½(W + Wᴴ)` with `W := A ∘ e^{iΘ}`
entrywise (the Crucoli–Pérez–Bungert–Van Mieghem directed convention;
route provenance in the module docstring — the statements are proved,
not admitted). Real possibly-asymmetric weights `A` and arbitrary real
phases `Θ`; **Hermitian by construction, hypothesis-free** (the
Hermitian-part convention, the `directedNormalizedLaplacian` precedent
— the single-`W` classical form is *derived* on the
`A.IsSymm ∧ Θᵀ = −Θ` cone). All statements below are proved, zero
axioms. QA at `Scaffold/QA/SpectralGraph/Magnetic_QA.lean` (16
declarations by the generator metric, 30 total: the asymmetric-flux
fixture pinning the hypothesis-free content on genuinely directed
input with genuinely complex phases; the frustrated-vs-consistent
kernel pair — one `π`-flux edge forces the triangle's kernel trivial
while leaving `K₂`'s antipodal phase potential in the kernel; the
classical bridge at zero phase; the nonnegativity fence refuting PSD
on symmetric signed input with exactly `hA` isolated).

| Declaration | Content |
|-------------|---------|
| `symDeg` | the symmetrized degree `½(outDeg + inDeg)` — the fan-in/fan-out split the energy identity's diagonal demands |
| `magneticMatrix` | `W := A ∘ e^{iΘ}` entrywise — the phase-weighted complex adjacency, defined for any real `A` and any real `Θ` |
| `magneticLaplacian` | `M := D_sym − ½(W + Wᴴ)` — the magnetic Laplacian at the Hermitian-part convention |
| `hermQuadForm` | the sesquilinear quadratic form `∑ i, conj (x i) * (M *ᵥ x) i` — the complex analogue of the shelf's `quadForm` |
| `magneticMatrix_isHermitian` | `Wᴴ = W` on the symmetric/antisymmetric cone (the cone lemma behind `magneticLaplacian_eq_single`) |
| `magneticLaplacian_isHermitian` | **Hermitian, hypothesis-free** — any real weights, any phases; the convention's structural payoff |
| `magneticLaplacian_mulVec_apply` | the entry action: symmetrized degree minus the conjugate-paired phase couplings (interface lemma; the energy identity's engine) |
| `magnetic_energy` | **the magnetic energy identity, hypothesis-free**: `x*Mx = ½ ∑ A_uv \|x_u − e^{iΘ_uv} x_v\|²` — the finite-algebra Dirichlet principle of the magnetic program |
| `magnetic_energy_real` | the real-coerced form: the quadratic form *is* the real energy sum |
| `magneticQuadForm_im_eq_zero` | the form is real-valued (the identity at the imaginary coordinate) |
| `magneticQuadForm_re_nonneg` | **PSD** on nonnegative weights (every edge energy nonnegative; the nonnegativity hypothesis load-bearing — the QA signed fence) |
| `magneticQuadForm_eq_zero_iff` | **the balanced-potential gauge characterization**: `x*Mx = 0 ↔ x_u = e^{iΘ_uv} x_v` on every positive edge — a frustrated cycle forces the kernel trivial (flux localization at form level, no eigenvalue machinery) |
| `magneticLaplacian_zero_phase_apply` | at `Θ = 0`: the complexified classical Laplacian of the symmetrized weights, entrywise (loops included, no case analysis) |
| `magneticLaplacian_zero_phase_apply_of_isSymm` | on symmetric `A`: the complexified `laplacian A` itself — the join with the real shelf |
| `magneticLaplacian_eq_single` | on the `A.IsSymm ∧ Θᵀ = −Θ` cone: `M = D_sym,ℂ − W` — the classical single-`W` magnetic Laplacian, derived not assumed |

Eigenvalue, magnetic-Cheeger, and synchronization statements are priced
follow-ons in the proposal (the pin has Hermitian spectral theory), not
gaps in what is claimed. With the signed-graph delivery
(2026-08-26, `proposals/signed-graphs-balance.md`) the module also
carries the gauge characterization at **kernel action level**:
`magneticLaplacian_mulVec_eq_zero_iff` — `M *ᵥ x = 0 ↔ x_u = e^{iΘ_uv} x_v`
on every positive edge of connected nonnegative input (the delivered
form-level `magneticQuadForm_eq_zero_iff` promoted to the kernel by
pure row algebra at unit modulus), the join the signed Harary theorem
consumes.

### `Scaffold.Mathlib.GraphTheory.Signed` (signed graphs — balance via the magnetic π-flux)

The signed-graph slice of the graph-model axis (delivered 2026-08-26,
`proposals/signed-graphs-balance.md`; section added retrospectively by
run `20260827T012700Z-run-1` — the delivery's own commit `7ca544b`
had covered only the irregular/multiway index rows, a records gap
flagged at the time and closed here): a `{±1}` signing `s` of a
symmetric network's edges, the **signed Laplacian** `D − A_σ`, and the
classical Harary balance theory joined to the delivered magnetic
program at the π-flux. All statements proved, zero new axioms — the
load-bearing join is the energy identity being *derived from* the
delivered `magnetic_energy`, so a defect in the magnetic shelf breaks
the signed theorems. QA at
`Scaffold/QA/SpectralGraph/Signed_QA.lean` (62 declarations by the
generator metric: the balanced path's iff both directions with the
kernel pinned raw to the switching, the frustrated triangle with
`¬IsBalanced` proved from the switching equations, the disconnected
conclusion-level fence, the negative-loop and `hnn` mechanism fences,
and the switching/eigen-transfer pins at an independently verified
eigenpair).

| Declaration | Content |
| --- | --- |
| `signedAdj` / `signedLaplacian` | the signed adjacency `A_σ = s ∘ A` and the signed Laplacian `D − A_σ` at a `{±1}` signing — loop-unsigned by balance itself (no separate loop-sign convention; a negative self-loop auto-frustrates, QA-witnessed) |
| `IsBalanced` | Harary balance as switching existence: `∃ g : V → {±1}, g_u · s_uv · g_v = 1` on every positive edge |
| `signFlux` / `complex_exp_I_mul_signFlux` / `magneticLaplacian_signFlux_apply` | the π-flux potential of a signing and the entrywise magnetic join `magneticLaplacian A (signFlux s) = (signedLaplacian A s : ℂ)` — the bridge the whole slice crosses |
| `signedLaplacian_quadForm` / `hermQuadForm_signedLaplacian` | the **signed Dirichlet energy identity** `xᵀL_σx = ½ ∑ A_uv \|x_u − s_uv x_v\|²` (real and complex forms), *derived from* the delivered `magnetic_energy` — the load-bearing join |
| `signedLaplacian_mulVec_apply` / `signedLaplacian_mulVec_eq_zero_iff_aligned` | the row-sum identity and the kernel↔edge-alignment characterization (`L_σ *ᵥ x = 0 ↔ x_v = s_uv x_u` on every positive edge) |
| `walk_sign` / `exists_switching_of_aligned` | the walk collapse: a walk's signed product telescopes, so an aligned vector *is* a `{±1}` switching on each component |
| `isBalanced_iff_exists_ne_zero_mulVec_eq_zero` | **the Harary balance theorem in kernel form**: on connected symmetric nonnegative input, `IsBalanced A s ↔ ∃ x ≠ 0, L_σ *ᵥ x = 0` — balance is exactly solvability of the signed Laplacian |
| `quadForm_pos_of_ne_zero_of_not_isBalanced` | positive definiteness under frustration: on a connected unbalanced signed network the signed Laplacian is strictly positive definite |
| `diagonal_mul_signedLaplacian_mul_diagonal` / `switchVec` family / `signedLaplacian_eq_diagonal_mul_laplacian_mul_diagonal` | **the switching similarity**: `diag(g) · L_σ · diag(g) = laplacian A` when `g` switches `s` to all-positive, with `switchVec` the conjugating action and the two-way eigenpair transfer (`signedLaplacian_mulVec_switchVec` / `laplacian_mulVec_switchVec`) — the balanced signed spectrum is the unsigned spectrum |

The multiset-level spectrum equality, signed Cheeger, and
frustration-index theory are priced follow-ons in the proposal, gated
on named consumers.

### `Scaffold.Mathlib.GraphTheory.VariationalTransfer` (variational consumer of the congruence bridge)

All statements proved (2026-08-17), no axioms; the second consuming
module of the `Normalized`/`Spectral` interfaces (after `Stationary`).
**Since 2026-08-25 the module also hosts its own docstring-named
irregular-Cheeger consumer (proposal
`irregular-cheeger-variational-transfer.md`, the module's first theorem
consumers anywhere): the volume-weighted easy direction and its
degree-stretched cut-test-vector layer** — see the second table.

| Declaration | Content |
|-------------|---------|
| `quadForm_congr` | generic congruence lemma: `quadForm (P M P) y = quadForm M (P *ᵥ y)` for symmetric `P` |
| `degreeSqrt_isSymm`, `degreeSqrt_mulVec` | symmetry of `√D`; entrywise action `√D *ᵥ y = √deg ∘ y` |
| `quadForm_laplacian_eq_quadForm_normalizedLaplacian` | Dirichlet-form transfer `yᵀ L y = (√D y)ᵀ L_sym (√D y)` through the proved congruence |
| `dotProduct_degreeSqrt_mulVec` | degree-weighted denominator `⬝(√D y, √D y) = ∑ deg i · y i²` |
| `degreeSqrt_mulVec_ne_zero` | the stretch preserves nonzero vectors (positive degrees) |
| `rayleigh_normalizedLaplacian_degreeSqrt` | normalized Rayleigh quotient `rayleigh L_sym (√D y) = (yᵀ L y) / ∑ deg i · y i²` — the irregular-graph variational interface |
| `normalizedLaplacian_psd` | PSD transfers from `laplacian_psd` by un-stretching through `1/√D` |

The irregular Cheeger upper bound (2026-08-25, proved, zero axioms;
supports: `secondEval_le_rayleigh_of_ker` in `Spectral.lean` — the
general-kernel Rayleigh domination — and
`normalizedLaplacian_mulVec_degreeSqrt_onesVec` in `Normalized.lean`,
the kernel vector):

| Declaration | Content |
|-------------|---------|
| `dotProduct_degreeSqrt_mulVec_cutTestVector` | **the volume identity, hypothesis-free**: `⬝(√D x, √D 1) = 0` for the cut indicator `x` — `vol S · vol Sᶜ − vol Sᶜ · vol S = 0`, the orthogonality the regular proof obtained from `vol_eq_of_regular`, exact in the weighted measure |
| `dotProduct_degreeSqrt_mulVec_cutTestVector_self` | the weighted norm `⬝(√D x, √D x) = vol S · vol Sᶜ · vol V` |
| `degreeSqrt_mulVec_cutTestVector_ne_zero` | the stretched cut indicator of a nonempty proper cut is nonzero (positive degrees) |
| `rayleigh_normalizedLaplacian_degreeSqrt_cutTestVector` | the Rayleigh quotient `boundary · vol V / (vol S · vol Sᶜ)` — the *same* value the regular family computes |
| `cheeger_upper_bound_normalized` | **the irregular easy direction**: `secondEval (normalizedLaplacian A) ≤ 2 * cheegerConstant A` for symmetric nonnegative positive-degree `A` with `2 ≤ card V` — no regularity, no connectivity; the regular `cheeger_upper_bound` recovered on the cone through `normalizedLaplacian_eq_regularNormalizedLaplacian` |

The irregular Cheeger **lower** bound (2026-08-25/26, proved, zero
axioms — the proposal's deferred hard half delivered, completing the
volume-weighted pair; supports: the `VolumeHardDirection` section of
`Cheeger.lean` — the volume median, the degree-weighted coarea core,
the weighted norm split — and `secondEval_variational_of_ker` in
`Spectral.lean`, the general-kernel sInf engine):

| Declaration | Content |
|-------------|---------|
| `dotProduct_degreeSqrt_mulVec_mixed` | the general weighted inner product: `⬝(√D x, √D y) = ∑ deg i · x i · y i` (hypothesis-free at `0 ≤ deg`) |
| `dotProduct_degreeSqrt_mulVec_onesVec` | the irregular variational constraint: `√D x ⊥ √D·1` iff `x` has degree-weighted zero sum — the constraint the irregular `sInf` set imposes on the un-stretched vector |
| `cheeger_sweep_normalized` | **the irregular sweep lemma (hard direction at test-vector level)**: every nonzero degree-weighted zero-sum `f` has `φ²/2 ≤ R_{L_sym}(√D f)` — the volume median routes both median parts to their volume-minority sides, the per-part bounds sum through the regular family's already-degree-weighted fused contraction, the weighted norm split carries the full norm, and `rayleigh_normalizedLaplacian_degreeSqrt` normalizes |
| `cheeger_lower_bound_normalized` | **the irregular hard direction (headline)**: `cheegerConstant A ^ 2 / 2 ≤ secondEval (normalizedLaplacian A)` on exactly the easy direction's hypotheses — `secondEval_variational_of_ker` at the true kernel vector `√D·1` reduces the spectral claim to the sweep lemma; the sInf set's nonemptiness witnessed by the easy direction's own cut test vector (one test object, both directions of the pair) |
| `cheeger_sweep_cut_normalized` | **the irregular sweep-cut theorem (median assembly, 2026-08-26)**: every nonzero degree-weighted zero-sum `f` has a nonempty proper *closed superlevel or sublevel cut of `f` itself* with `conductance A S ^ 2 ≤ 2 · R_{L_sym}(√D f)` — `sweep_level_extract_vol` per part (the volume median feeding its minority hypothesis verbatim), the product test with degenerate single-part cases, the fused contraction verbatim, the weighted norm split, and the `2 · R = E'/∑ deg f²` normalization; exactly the hard direction's constraint shape (no regularity, no connectivity, no cardinality); QA forces the family on the pair's shared `P₃` cut test vector (`1 ≤ 8/3` at the pinned `R = 4/3`), the `K₂` recovery (`1 ≤ 4` at `R = 2`), and the zero-sum fence (`f = ![1,2]`: `1 ≤ 2/5` refuted for every swept candidate) |

The connectivity transfer (2026-08-26, proved, zero axioms — the
irregular family's own priced follow-on; supports: the electrical
program's `laplacian_mulVec_eq_zero_iff_exists_const` in `Spectral.lean`
and the general-kernel engine `secondEval_le_rayleigh_of_ker`):

| Declaration | Content |
| --- | --- |
| `degreeSqrt_mul_normalizedLaplacian` | the left-multiplied congruence `√D · L_sym = L · D^{-1/2}` — the identity through which the normalized kernel is located |
| `normalizedLaplacian_mulVec_degreeSqrt_of_laplacian_mulVec_eq_zero` | the kernel-cone lift: a combinatorial kernel vector stretches into the normalized kernel |
| `normalizedLaplacian_mulVec_eq_zero_iff` | **the kernel characterization**: on connected input, `L_sym *ᵥ x = 0 ↔ x ∈ span(√D · onesVec)` — the stretched-constant line |
| `secondEval_normalizedLaplacian_pos_of_connected` | **Fiedler's certificate, normalized form**: connected ⇒ `0 < λ₂ (L_sym)` (PSD + sorted + multiplicity pin + orthonormality, the mirror of `lambda2_pos_of_connected`) |
| `secondEval_normalizedLaplacian_eq_zero_of_not_connected` | the disconnected converse: `λ₂ = 0` exactly, via the component indicator and Gram–Schmidt against `√D·1` through `secondEval_le_rayleigh_of_ker` |
| `secondEval_normalizedLaplacian_pos_iff_connected` | **the packaged equivalence**: `0 < λ₂ (L_sym) ↔ connected` — algebraic connectivity *is* connectivity in the volume-weighted world |
| `cheegerConstant_pos_of_connected` | **the Cheeger consumer corollary**: `0 < cheegerConstant A` on connected irregular graphs — `0 < λ₂ ≤ 2φ` through the delivered easy direction |

The volume-weighted sweep extraction (2026-08-26, proved, zero axioms —
the irregular family's own port of the regular 2026-08-24
`sweep-cut-extraction` delivery; supports: the `VolumeHardDirection`
layer consumed a second time and the fused contraction verbatim):

| Declaration | Content |
| --- | --- |
| `sweep_level_extract_vol` | **the per-part sweep extraction, volume form** (`Cheeger.lean`'s `VolumeSweepExtraction` section): for `y` with volume-minority closed superlevel sets and `0 < ∑ deg y²`, a positive level `t` with `S = {i : t ≤ y²}` nonempty, proper, and `conductance S² ≤ E'(y)/∑ deg y²` — the attainment route at the `boundary / vol` ratio (the card denominator replaced by the level set's volume), the degree-weighted layer-cake cloned from `coarea_core_vol`'s proof, Component A already degree-weighted, and the minority-volume conversion by pure `vol_compl` arithmetic; QA forces the extracted set to `{0}` on `P₃` through the level-membership iff, conductance `1` against bound `2/1` |

The irregular Fiedler instantiation (2026-08-26, proved, zero axioms — the
family's algorithm-facing capstone, the standing handoff's named bounded
candidate; supports: the delivered connectivity transfer `0 < λ₂`
supplying the orthogonality hinge, the sweep family's constraint shape,
the `degreeSqrt/degreeInvSqrt` cancellation, and
`quadForm_eigvecOf_self`):

| Declaration | Content |
| --- | --- |
| `fiedlerIndexNormalized`, `fiedlerIndexNormalized_eigvalOf` | the eigenbasis index of `L_sym` carrying `secondEval`, and the interface fact that the chosen index's eigenvalue *is* `λ₂ (L_sym)` (the `Fiedler.lean` pattern at the operator the irregular world uses) |
| `fiedlerVectorNormalized`, `fiedlerVectorNormalized_eigen` | the normalized Fiedler vector (the unit eigenvector at `λ₂`) with the eigenvector equation `L_sym *ᵥ u = λ₂ • u` |
| `fiedlerVectorNormalized_dot_self`, `fiedlerVectorNormalized_ne_zero`, `fiedlerVectorNormalized_quadForm` | unit norm (orthonormal eigenbasis), nonvanishing, and the energy identity `quadForm L_sym u = λ₂` |
| `fiedlerVectorNormalized_rayleigh` | `R_{L_sym}(u) = λ₂` — the spectral side of the sweep bound, where `2 * R_{L_sym}(√D f)` closes to `2 * λ₂` |
| `fiedlerVectorNormalized_ortho_degreeSqrt_onesVec` | **the orthogonality hinge**: under `0 < λ₂` (connectivity's exact entry point), `u ⊥ √D·1` by `eigvecOf_ortho_of_mulVec_eq_zero` at the true kernel vector |
| `fiedlerSweepVector` | **the sweep vector**: the `D^{-1/2}` pullback of the Fiedler vector — the vector the spectral-partitioning algorithm actually sorts, the generalized eigenfunction of `(L, D)` at `λ₂` |
| `fiedlerSweepVector_degreeSqrt_mulVec`, `fiedlerSweepVector_ne_zero` | the stretch cancellation `√D f = u` and nonvanishing (conjugation by invertible `1/√D`) |
| `fiedlerSweepVector_sum_deg_eq_zero` | **the constraint conversion**: the sweep vector is degree-weighted zero-sum — the sweep family's own hypothesis, obtained from the eigen-hinge through the degree-weighted pairing identity rather than assumed |
| `fiedler_sweep_cut_normalized` | **the headline**: on every connected symmetric nonnegative positive-degree graph with `2 ≤ card V`, an explicit nonempty proper closed superlevel/sublevel cut of the sweep vector itself with `conductance S² ≤ 2 λ₂ (L_sym)` — the regular family's own `fiedler_sweep_cut` constant `2λ₂/d` on the cone; QA pins `λ₂ (L_sym P₃) = 1` *exactly* (the new `≥ 1` side a `2 x₁²` sum-of-squares through the sInf engine), instantiates on both fixtures at independent pins, and fences the connectivity mechanism on the disconnected fixture (a kernel eigenvector provably violates the hinge at the pinned `λ₂ = 0`) |

### `Scaffold.Mathlib.GraphTheory.Multiway` (the higher-order Cheeger easy direction)

Delivered 2026-08-26 (`proposals/multiway-expansion.md`, COMPLETE —
the every-family form plus its ρ_k partition-minimum packaging follow-on
delivered the same day; proved, zero axioms — radar axis 4 raised to
5.0 at the pre-recorded trigger when the packaging closed the easy
half's classical statement form; supports: `laplacian_quadForm`,
the eigenbasis expansion/Parseval layer, the irregular family's
congruence bridge `quadForm_laplacian_eq_quadForm_normalizedLaplacian`
+ `dotProduct_degreeSqrt_mulVec`, `vol_pos_of_pos_deg`, and the two
new k-general engine pieces in `Spectral.lean` above):

| Declaration | Content |
| --- | --- |
| `partIndicator`, `partIndicator_of_mem`, `partIndicator_of_not_mem` | the plain `{0,1}`-valued indicator of a vertex set and its entry lemmas — the *uncentered* part indicators are the multiway test family (the Step-0 verdict: no centering anywhere; the k = 2 family's constraint is replaced by the subspace engine's dimension count) |
| `quadForm_laplacian_partIndicator` | **the per-part energy identity**: `quadForm (laplacian A) (partIndicator S) = boundary A S` — the k = 2 family's `cutTestVector` energy identity at the indicator level, for arbitrary part counts; load-bearing on `laplacian_quadForm` |
| `multiwayCombination`, `multiwayCombination_of_mem`, `multiwayCombination_eq_zero` | the part combination `∑ᵢ cᵢ · 1_{Sᵢ}` — the multiway test family's general member — with the disjoint-family reading lemmas (a member of part `i₀` reads exactly `c i₀`; off all parts, `0`) |
| `dotProduct_degreeSqrt_mulVec_multiwayCombination` | the weighted-norm identity `‖√D · ∑ cᵢ1_{Sᵢ}‖² = ∑ cᵢ² · vol(Sᵢ)` — disjointness makes the weighted sum read each part's volume exactly once |
| `laplacian_quadForm_multiwayCombination_le` | **the cross-part absorption lemma (the theorem's engine)**: `xᵀLx ≤ 2 · ∑ cᵢ² · boundary(Sᵢ)` for every combination — a linear combination's re-introduced cross-part energy is *absorbed*, not eliminated, each crossing pair bounded pointwise by `(a−b)² ≤ 2a² + 2b²`; the headline's constant 2 is exactly this absorption constant; QA pins it at *equality* on the K₂ and C₄ fixtures |
| `cheeger_upper_bound_multiway` | **the multiway Cheeger easy direction (headline)**: `evals (L_sym) ⟨k−1⟩ ≤ 2 · maxᵢ boundary(Sᵢ)/vol(Sᵢ)` for every family of nonempty pairwise-disjoint vertex sets on every symmetric nonnegative positive-degree graph (`1 ≤ k ≤ card V`) — the *every-family form*: any concrete disjoint family certifies, no partition-space minimum is taken (the ρ_k packaging is a priced follow-on); the delivered irregular pair is the `k = 2` instance; route provenance Lee–Gharan–Trevisan (STOC 2012 / JAMS 2014, the λ_k ≤ 2ρ_k half) — provenance only, the statement is proved |
| `cheeger_upper_bound_multiway_conductance` | the conductance form at `2 ≤ k` (every complement nonempty, `boundary/vol ≤ boundary/min vol volᶜ = conductance` termwise) — the k-way generalization of `cheeger_upper_bound_normalized`'s conductance shape |
| `IsMultiwayPartition` | the k-way partition predicate (nonempty, pairwise disjoint, covering) — the structure the every-family form deliberately did not need; the ρ_k minimum ranges over it (2026-08-26, the packaging follow-on) |
| `maxPartConductance`, `maxPartConductance_const`, `finset_univ_sup'_eq_sSup_range` | the maximum part conductance as `sSup` of range (the `k = 0` junk documented), the constant-family evaluation, and the join to the delivered theorems' `sup'` statement shapes |
| `multiwayExpansion`, `multiwayExpansion_le` | **ρ_k, the multiway expansion constant**: the `sInf` over k-way partitions of the maximum part conductance (the `k > card V` `sInf ∅ = 0` junk documented, hypothesis-gated), with the `csInf` bound at finiteness-supplied `BddBelow` — the classical object of the higher-order Cheeger easy direction |
| `exists_isMultiwayPartition_eq_multiwayExpansion` | **attainment over the finite partition space**: the ρ_k infimum is realized by an actual k-way partition (`Set.Nonempty.csInf_mem` at the value set's finiteness — a subset of the range over the Fintype of families); the packaging's only new content |
| `cheeger_upper_bound_multiway_rhoK` | **the ρ_k form of the easy direction**: `evals (L_sym) ⟨k−1⟩ ≤ 2 · multiwayExpansion A k` at `2 ≤ k ≤ card V` with a partition — the classical Lee–Gharan–Trevisan statement form, the every-family theorem consumed at the attained minimizer, no new engine; QA pins `ρ₂(C₄) = 1/2` exact (forced by the theorem joined to the independently pinned `λ₂ = 1`, the minimum beating the diagonal partition's `1`) and the empty-set junk fence at `k > card V` |
| `exists_isMultiwayPartition_of_le_card` | the existence supplier: k-way partitions exist whenever `1 ≤ k ≤ card V` (an injection's singletons with the complement absorbed into the last part) — discharges the `hex` hypothesis in the common case |

### `Scaffold.Mathlib.GraphTheory.AlonBoppana` (the Alon–Boppana program, Steps 1–4)

Opened 2026-08-26 (`proposals/alon-boppana-bound.md`, ADOPTED by
operator decision that day — the program delivering the lower
companion to the Cheeger/expander toolkit via Nilli's two-edge
variational method; both delivered steps are proved, zero axioms, and
Step 1 supports the shelf's sorted-spectrum API at its extremes —
`exists_eigvalOf_eq_of_mulVec_eq_smul`, `eigvalOf_le_evals_last`,
`evals_mem_eigvalOf`, `quadForm_eigvecOf_self`; the Step-0 spike
`wip/ab_spike.lean` priced the level-cardinality idiom and the Step-2
delivery realized it at module level —
`Mathlib.Combinatorics.SimpleGraph.Metric` imported explicitly per the
spike's verdict — and Step 3's first sub-slice (2026-08-27) delivered
the radial test vector with its normalization, the denominator of
Nilli's Rayleigh quotient):

| Declaration | Content |
| --- | --- |
| `IsDRegular` | d-regularity as a per-graph hypothesis in the shelf's `d : ℝ` idiom (every row sum equals `d`) — the `Cheeger.lean` `regularNormalizedLaplacian A d` pattern, no new regularity machinery |
| `adjacency_mulVec_onesVec` | the constant-eigenvector fact: `A *ᵥ onesVec = d • onesVec` under `IsDRegular A d` — a row-sum computation, hypothesis-free beyond regularity; the interface's own witness, fenced by QA at P₃ (provably not an eigenvector there) |
| `quadForm_le_of_isDRegular` | **AM–GM row-sum domination**: `xᵀAx ≤ d · (x ⬝ᵥ x)` on symmetric nonnegative d-regular input — entrywise AM–GM multiplied through nonnegative weights, the symmetric double sum's halves both `d ‖x‖²` (row-sum and column-sum degree identities); `hnn` load-bearing (QA refutes at the signed 0-regular `!![1,-1;-1,1]]`) |
| `evals_last_eq_of_isDRegular` | **the top adjacency eigenvalue of a d-regular graph is `d`** — `evals hA ⟨card−1⟩ = d`, from both sides: the eigenvalue witness at `onesVec` (`exists_eigvalOf_eq_of_mulVec_eq_smul` + `eigvalOf_le_evals_last`) and domination at the unit eigenvector (`quadForm_eigvecOf_self` + `evals_mem_eigvalOf`); QA instances on C₄ (`= 2`) and K₂ (`= 1`) joined to raw entrywise eigen-equation pins |
| `levE` / `levClass` / `ballE` | **the Step-0 verdict's BFS-level machinery at module level** (Step 2, 2026-08-26): the level of `z` from the edge `(x, y)` (min of the two endpoint distances on `supportGraph`), the level classes, and the closed radius filter — the test vector's support and the far-apart condition's operands |
| `levE_eq_zero_iff` / `levE_eq_zero_iff_of_connected` | the junk-zero-honest level-0 form (the `dist` trap stated, not hidden: level 0 collects the endpoints *and* every unreachable vertex) and its connected amortization (level 0 is exactly the two distinct endpoints — one connectivity hypothesis discharges every reachability refutation, the spike's promised unit-cost amortization) |
| `levClass_zero_eq` / `levClass_zero_card` / `isTreeBall_one_of_connected` | level 0 is exactly the endpoint pair on connected input at distinct endpoints — the `j = 0` cardinality equation free of regularity; the one-level tree-ball predicate holds at every `d` |
| `IsTreeBall` | **the tree-ball predicate**, exactly as the Step-0 verdict priced it: level `j` carries exactly `2 (d−1)^j` vertices for every `j < k` — the count of the infinite d-regular tree around an edge; the cardinality-equation form Nilli's Rayleigh computation consumes, never a structural tree-ness predicate; QA: the C₈ instance at `d = 2, k = 2` (levels 0/1 full) and the C₄ wrap-around refutation at `k = 3` (level 2 demanded nonempty, provably empty) |
| `ballE_mem_iff` / `ballE_zero` / `ballE_mono` / `levClass_pairwise_disjoint` / `ballE_succ_union` | the ball algebra: membership as a two-sided endpoint bound, the radius-0 identification with the level-0 class, radius monotonicity, pairwise-disjoint level classes (a vertex has one level), and the layer-cake decomposition of radius `r+1` |
| `ballE_card_eq_sum` | **the layer-cake cardinality bridge**: under `IsTreeBall` at radius `k+1`, the ball of radius `k` has exactly the geometric level sum `∑_{j ≤ k} 2 (d−1)^j` — the Step-3 test vector's normalization input; QA pins it two independent routes on C₈ (set enumeration vs the theorem, one number) |
| `distEdge` / `ballE_disjoint_of_lt_distEdge` | **the far-apart condition**: the least cross-endpoint graph distance, and the theorem that every cross distance exceeding `r + s` makes the two edge-balls disjoint (the connected triangle inequality at all four endpoint pairings) — the Step-4 orthogonalization's load-bearing separation input; QA: the antipodal C₈ instance (four rfl-verified cross distances ≥ 3) and the threshold-tightness fence (at exactly `r + s` the balls provably intersect) |
| `radialVec` | **Nilli's radial test vector** (Step 3's first sub-slice, 2026-08-27): on the radius-`k` ball of the edge, the value `ρ ^ levE z` — constant per BFS level, `0` outside — with the d-regular-tree normalization carried by consumers as the hypothesis `ρ ^ 2 = ((d−1 : ℕ) : ℝ)⁻¹` (the `√` plumbing deliberately left to the Step-5 packaging, where the `IsDRegular` `d : ℝ` join also lives) |
| `radialVec_apply` / `radialVec_of_mem_ballE` / `radialVec_eq_zero_of_not_mem_ballE` / `radialVec_left` / `radialVec_ne_zero` | the radial vector's interface: the entry form, the pure level power on the ball, vanishing outside (support = `ballE`), the always-`1` left-endpoint seed, and nonvanishing at every radius and every `ρ` |
| `sum_ballE_eq_sum_levels` | **the layer-cake sum bridge**: any function summed over the radius-`k` edge ball equals its level-by-level sum — `ballE_card_eq_sum`'s summation form at a function rather than a count (the squared norm is level-constant but not constant) |
| `radialVec_dotProduct_self` | **the squared-norm identity**: `⟨ρ^{lev}, ρ^{lev}⟩ = 2 (k + 1)` exactly, under `IsTreeBall` at radius `k+1` and `ρ ^ 2 = ((d−1 : ℕ) : ℝ)⁻¹` — per level, the geometric growth `2 (d−1)^j` cancels the vector's decay `ρ^{2j}` to exactly `2` (`pow_mul`/`mul_pow`/`mul_inv_cancel₀`); the denominator of Nilli's Rayleigh quotient and the first theorem consumer of the Step-2 level machinery; `1 < d` load-bearing at the cancellation (at `d = 1`, `ρ = 0` is junk-admissible through `0⁻¹ = 0` while the truncated counts die — QA fences it at K₂ with the squared norm `2 ≠ 4`); QA pins the C₈ value `4` by two independent routes (theorem vs raw per-vertex enumeration) and the `k = 0` pair both routes (`isTreeBall_one_of_connected`'s first consumer) |
| `levE_le_levE_add_one_of_adj` | **the level-Lipschitz lemma** (Step 3's second sub-slice, 2026-08-27): the BFS level function moves by at most `1` along any support-graph edge (`levE u ≤ levE v + 1`), from a junk-safe adjacency triangle (`dist_le_dist_add_one_of_adj`, private — shortest-walk prefix in the reachable regime, contraposed reachability in the junk regime) applied at both endpoints and collapsed by `omega` at the min |
| `exists_levE_parent` | **the parent lemma**: every vertex at level `≥ 1` has a support-adjacent neighbor exactly one level down (`∃ p, 0 < A z p ∧ levE p + 1 = levE z`), no connectivity hypothesis — the min-attaining endpoint's shortest-walk predecessor (`exists_pred_of_one_le_dist`, private) with the level equality closed by Lipschitz from both sides; the from-below harvest edge of the energy bound, dissolving the "level sizes, not edge counts" obstruction without strengthening `IsTreeBall` |
| `interiorE` / `interiorE_zero` / `interiorE_succ_union` / `sum_interiorE_eq_sum_levels` | the interior of the radius-`k` edge ball (levels `1..k`, level 0 excluded — the parent-carrying vertices) with its algebra and the interior level-sum bridge (`sum_ballE_eq_sum_levels`'s pattern at `Finset.Ico 1 (k+1)`) |
| `radialVec_quadForm_ge` | **the energy half of Nilli's Rayleigh quotient — the numerator bounded from below** (the Step-3b headline): `2 + 4 k (d−1) ρ ≤ quadForm A (radialVec …)` under the existing `IsTreeBall` at radius `k+1` plus the `0`-or-`≥ 1` weight discipline (`∀ i j, A i j = 0 ∨ 1 ≤ A i j` — every parent edge weighs at least `1`), distinct endpoints, a genuine edge `A x y ≠ 0`, `1 < d`, the normalization, and `0 ≤ ρ`; the proof harvests a pairwise-disjoint selection of nonnegative terms of the double sum (both orders of the endpoint edge, both orders of every interior vertex's parent edge) and collapses each level's `2 (d−1)^j ρ^{2j−1}` to exactly `2 (d−1) ρ`; QA pins it **tight at equality** on C₈ (raw `6` = the theorem's `2 + 4·1·1·1`) with three fences isolating `hedge` (the P₃ pseudo-edge), `h01` (the half-weight edge), and `hxy` (the loop whose junk-zero partner keeps `IsTreeBall` honest) |
| `radialVec_rayleigh_ge` | **the Rayleigh-quotient corollary**: `(2 + 4 k (d−1) ρ) / (2 (k+1)) ≤ rayleigh A (radialVec …)` — the numerator bound joined to the delivered denominator identity through `div_le_div_iff_of_pos_right`; Nilli's `(1 + 2 k √(d−1)) / (k+1)` before the Step-5 `√` packaging, the exact interface Step 4's orthogonalization consumes |

| `radialVec_sum_eq` | Alon–Boppana Step 4 | The equal-mass lemma: the radial vector's total mass is a function of `(d, ρ, k)` only under `IsTreeBall` |
| `twoEdgeVec` / `twoEdgeVec_dotProduct_onesVec` | Alon–Boppana Step 4 | Nilli's two-edge difference vector, orthogonal to `onesVec` by the equal-mass lemma |
| `twoEdgeVec_dotProduct_self` / `twoEdgeVec_ne_zero` | Alon–Boppana Step 4 | The squared norm `4 (k+1)` on disjoint radius-`k` balls (the two 3a denominators add) |
| `radialVec_dotProduct_eq_zero_of_disjoint` / `radialVec_cross_dotProduct_eq_zero` / `levE_cross_adj_eq_zero` | Alon–Boppana Step 4 | Cross-support and cross-edge dot products vanish; the cross-edge elimination runs 3b's level-Lipschitz lemma at the far-apart threshold |
| `dotProduct_mulVec_symm` / `quadForm_sub` | Alon–Boppana Step 4 | Symmetric-matrix swap and difference-vector quadratic-form expansion (general algebra) |
| `twoEdgeVec_quadForm_ge` / `twoEdgeVec_rayleigh_ge` | Alon–Boppana Step 4 | The doubled numerator bound `2·(2 + 4k(d−1)ρ)` and its Rayleigh-quotient form |
| `smul_one_sub_isSymm` / `smul_one_sub_mulVec_onesVec` / `quadForm_smul_one_sub` | Alon–Boppana Step 4 | The engine layer at `M = d•1 − A`: symmetry, kernel (Step-1 eigen-equation), and the shifted quadratic form |
| `twoEdgeVec_secondEval_le` | Alon–Boppana Step 4 | **The headline**: `secondEval (d•1 − A) ≤ d − (2 + 4k(d−1)ρ)/(2(k+1))` through `secondEval_le_rayleigh` — the program's first eigenvalue-level statement |

### `Scaffold.Mathlib.GraphTheory.AlonBoppana` (the Alon–Boppana program, Step 5 — the diameter-dependent packaging)

The program's capstone step (2026-08-27, `proposals/alon-boppana-bound.md`
COMPLETE): the `√` packaging, the far-apart-to-diameter bridge, and
the honest classical statement forms.

| Declaration | Area | Description |
| --- | --- | --- |
| `mul_sqrt_inv_eq_sqrt` | Alon–Boppana Step 5 | The `√` plumbing: `x·√(x⁻¹) = √x` hypothesis-free (`Real.sqrt_inv`/`Real.div_sqrt`, junk-safe) |
| `distEdge_le_diam` | Alon–Boppana Step 5 | **The far-apart-to-diameter bridge**: `distEdge ≤ diam` on finite connected input (finiteness-attainment + `edist_ne_top_iff_reachable` supplying the `ediam ≠ ⊤` that Mathlib's `dist_le_diam` demands) |
| `alonBoppana_diam_ge` | Alon–Boppana Step 5 | The honest diameter bookkeeping: the far-apart hypothesis forces `2(k+1)+1 ≤ diam`, i.e. `k+1 ≤ ⌊diam/2⌋` — hypothesis-side only, the tree-ball constraint never derived from the diameter |
| `alonBoppana_nilli` | Alon–Boppana Step 5 | **The capstone**: `secondEval (d•1 − A) ≤ d − (1 + 2k√(d−1))/(k+1)` at `ρ = √((d−1)⁻¹)` — Alon–Boppana's `2√(d−1)` barrier with the error explicit |
| `alonBoppana_nilli_classical` | Alon–Boppana Step 5 | The classical error shape `≤ d − 2√(d−1) + 2√(d−1)/(k+1)` — the single-graph form of `λ₂ ≥ 2√(d−1) − O(1/⌊diam/2⌋)` |

### `Scaffold.Mathlib.GraphTheory.AlonBoppana` (the expansion ceiling)

The program's first theorem consumer (2026-08-27,
`proposals/ramanujan-expansion-ceiling.md` COMPLETE): the capstone
composed with the proved Cheeger hard direction into the textbook
ceiling on expansion quality — obstruction scope only, no tightness
claim.

| Declaration | Area | Description |
| --- | --- | --- |
| `smul_one_sub_eq_smul_regularNormalizedLaplacian` | Expansion ceiling | The operator identity joining the two families' spellings: `d • 1 − A = d • regularNormalizedLaplacian A d` under regularity and `d ≠ 0` (Cheeger's `smul_regularNormalizedLaplacian` plus the `degreeMatrix = d • 1` half) |
| `ramanujan_expansion_ceiling` | Expansion ceiling | **The headline**: `cheegerConstant A ≤ √(2 (1 − 2√(d−1)/d + 2√(d−1)/(d (k+1))))` under exactly `alonBoppana_nilli_classical`'s hypotheses — the Alon–Boppana upper bound chained below the Cheeger hard direction through the scaling engine; consumed `cheeger_lower_bound` (its first cross-module AlonBoppana-side consumer) |

### `Scaffold.Mathlib.GraphTheory.Spectral` (positive scaling — the expansion ceiling's engine)

Two interface lemmas delivered with the expansion ceiling (2026-08-27)
for composing spectral statements across linearly related operators.

| Declaration | Area | Description |
| --- | --- | --- |
| `smul_isSymm` | Spectral engine | A scalar multiple of a symmetric matrix is symmetric |
| `secondEval_smul_of_pos` | Spectral engine | **Exact positive scaling** (the variational route): `secondEval (c • M) = c * secondEval M` for `0 < c` on a PSD symmetric operator with `onesVec` in the kernel — the constraint set of `c • M` is the positive-scaled image and `sInf` commutes; first consumer the expansion ceiling |
| `secondEval_congr` | Spectral engine | Matrix equality respected at possibly-different symmetry proofs (proof irrelevance) — the robust bridge around the motive-not-type-correct trap of rewriting matrix equalities under proof-carrying applications |

### `Scaffold.Mathlib.GraphTheory.Heat` (the heat semigroup)

Opened 2026-08-23 as Phase B of
`proposals/reversibility-and-heat-semigroup.md` — the Active priority
table's single High row, its operator gate resolved by a real external
named consumer (`sgt-gaps.md`, the independent `spectral-proof`
rewrite project, which asks for heat evolution on `laplacian A`,
identity/semigroup, mass conservation, and eigenmode decay — Steps 1–4
of the proposal verbatim). **Steps 0–4 delivered — the proposal
COMPLETE 2026-08-23** (survey; definition, symmetry, identity; the
semigroup law; mass conservation; eigenmode decay + the connected-graph
DC limit — the payoff statement). **Phase C (the heat-flow derivative +
remainder bound, the second `sgt-gaps.md` request) opened 2026-08-23,
priority High: COMPLETE** — Step 1 the derivative at zero (entrywise +
vector form), Step 2 the first-order remainder bound
`heatKernel_firstOrder_remainder_apply_le` (the coordinate form
`|(e^{-tL} x) a − x a + t (L x) a| ≤ t² · ∑ᵢ λᵢ² |vᵢ ⬝ᵥ x| |vᵢ a|` on
the window `|t · λᵢ| ≤ 1`, termwise through the pin's
`Real.abs_exp_sub_one_sub_id_le`) plus its `[0, T]` interval packaging
`heatKernel_firstOrder_remainder_interval`. Pure hard crust, zero
axioms; QA at `Scaffold/QA/SpectralGraph/Heat_QA.lean`.

| Declaration | Content |
|-------------|---------|
| `heatKernel` | the matrix-level diffusion operator `heatKernel A t := NormedSpace.exp ℝ (-(t • laplacian A))`; total in `A` and `t` (negative `t` = the growing backward semigroup, documented) |
| `heatKernel_isSymm` | `(heatKernel A t).IsSymm` under `A.IsSymm`, every `t` — `laplacian_symmetric` through `Matrix.IsSymm.smul`/`.neg` and the pin's `Matrix.IsSymm.exp` |
| `heatKernel_zero` | `heatKernel A 0 = 1`, hypothesis-free (`zero_smul`/`neg_zero`/`NormedSpace.exp_zero`) |
| `heatKernel_mul_heatKernel` | **the semigroup law** `heatKernel A s * heatKernel A t = heatKernel A (s + t)`, hypothesis-free (Step 2) — `Matrix.exp_add_of_commute` at the commuting negated scalar multiples, no ball/radius hypothesis (the survey's norm-free finding); the joined exponent reduced by `neg_add` + `add_smul` |
| `hasSum_pi` | pin-gap Pi-HasSum assembler (entrywise `HasSum` → global `HasSum` for Pi codomains), from `Filter.tendsto_pi_nhds` + `Finset.sum_apply` — the pin has no such lemmas; consumed by the Step-3 series work |
| `abs_pow_apply_le` | entrywise power bound `\|(M ^ n) i j\| ≤ (∑ p q, \|M p q\|) ^ n`, by `Matrix.mul_apply`-induction — the entire matrix-analysis input to the series summability, norm-free |
| `summable_exp_term` | every entry of the exponential series is summable, by comparison with `B ^ n / n!` (`Real.summable_pow_div_factorial` + `Summable.of_norm_bounded`) |
| `expSeries_hasSum_exp` | the exponential series converges to `NormedSpace.exp ℝ M` in the entrywise (Pi) topology — the matrix-level summability the pin's normed section does not provide at matrix type (Step 3's survey finding) |
| `pow_mulVec_smul` | powers of a matrix act on an eigenvector by powers of the eigenvalue: `(M ^ n) *ᵥ v = (μ ^ n) • v` at `M *ᵥ v = μ • v` (Step 4) |
| `exp_mulVec_eq_smul_of_mulVec_eq_smul` | **the eigenmode engine** (Step 4): `M *ᵥ v = μ • v → exp ℝ M *ᵥ v = Real.exp μ • v` — Step 3's `expSeries_hasSum_exp` pushed through the continuous action at an eigenvector, the scalar series summed by `NormedSpace.exp_series_hasSum_exp'` at ℝ (via `Real.exp_eq_exp_ℝ`) |
| `exp_mulVec_eq_of_mulVec_eq_zero` | **mass conservation for kernel vectors**: `M *ᵥ v = 0 → exp ℝ M *ᵥ v = v` — the `μ = 0` case of the eigenmode engine (at unchanged statement) |
| `heatKernel_mulVec_onesVec` | **mass conservation** (Step 3): `heatKernel A t *ᵥ onesVec = onesVec` at every time, hypothesis-free, through the shelf's `laplacian_ones_in_kernel` |
| `exp_eq_one_add_of_mul_self_eq_zero` | general square-zero collapse `M * M = 0 → NormedSpace.exp ℝ M = 1 + M` (by `exp_eq_tsum` + `tsum_eq_sum` over `range 2`) — the closed-form evaluation handle |
| `exp_neg_smul_eq_one_add_of_mul_self_eq_zero` | the every-time collapse `exp ℝ (-(t • M)) = 1 + -(t • M)` for `M * M = 0` (the exponent squares to `(t·t) • (M·M) = 0`) — makes QA fixtures exactly evaluable at symbolic times |
| `exp_eq_one_add_of_mul_self_eq_smul` | **rank-one-idempotent collapse** (Step 4): `M * M = c • M → exp ℝ M = 1 + ((exp c − 1)/c) • M` (`c ≠ 0`) — the square-zero collapse's sibling; its scalar tail shifted by the pin's `hasSum_nat_add_iff'` (no plain tail-shift `HasSum` lemma at this pin), reassembled on `tsum_eq_zero_add` + `tsum_smul_const`; makes the symmetric K₂ fixture (L² = 2 • L) exactly evaluable at symbolic times |
| `tendsto_exp_neg_mul_atTop` | the scalar decay-factor asymptotics: for `0 < μ`, `Real.exp (-(t * μ)) → 0` as `t → ∞` (`Real.tendsto_exp_atBot` at the linear escape) |
| `heatKernel_mulVec_eigvecOf` | **eigenmode decay** (Step 4): every eigenbasis vector of `laplacian A` is an eigenvector of `heatKernel A t` at every time, with eigenvalue the mode's decay factor `e^{−t·λᵢ}` — the eigenmode engine at the eigenvector equation |
| `heatKernel_decayFactor_antitone` | the proposal's named monotonicity: sorted `λᵢ ≤ λⱼ` and `t ≥ 0` ⇒ the mode-`j` factor ≤ the mode-`i` factor (higher frequencies dissipate at least as fast; `evals_sorted` + `Real.exp_le_exp`) |
| `heatKernel_decayFactor_le_one` | PSD dissipation: on symmetric-nonnegative input every sorted eigenvalue is ≥ 0 (`evals_mem_eigvalOf` + `laplacian_psd`), so every mode factor is ≤ 1 at `t ≥ 0` |
| `heatKernel_mulVec_eq_sum` | **the eigenbasis expansion** — the spectral-calculus identity in action form: `heatKernel A t *ᵥ x = ∑ᵢ e^{−t·λᵢ} (vᵢ ⬝ᵥ x) • vᵢ` over the proved orthonormal basis (`eigvecOf_expansion_apply` + `mulVecLin` linearity + the mode theorem) |
| `heatKernel_mulVec_tendsto_atTop` | **the connected-graph DC limit — the payoff** (Step 4): the heat flow of any vector converges to its mean `((∑ j, x j)/\|V\|) • onesVec` — PSD, kernel-mode existence (`det L = 0` + `det_eq_prod_eigenvalues`), the kernel characterization (a second kernel mode would put two orthogonal unit vectors in one line), and finite-sum limit passage |
| `heatKernel_mulVec_apply_hasDerivAt_zero` | **the heat-flow derivative at zero, entrywise** (Phase C Step 1, the `spectral-proof` rewrite's dissolution-theorem input): each coordinate of `t ↦ heatKernel A t *ᵥ x` differentiates at `t = 0` to `-(L *ᵥ x)`'s coordinate — `heatKernel_mulVec_eq_sum` differentiated termwise (Duhamel's `heatApply_hasDerivAt` technique), the derivative sum re-expanded through `eigvecOf_expansion_apply` + the self-adjoint pairing transfer `dotProduct_eigvecOf_mulVec` |
| `heatKernel_mulVec_hasDerivAt_zero` | **the heat-flow derivative at zero, vector form** (Phase C Step 1): `HasDerivAt (fun t => heatKernel A t *ᵥ x) (-(laplacian A *ᵥ x)) 0` — the infinitesimal generator `d/dt e^{-tL} x\|₀ = -L x`, assembled from the entrywise engine by the pin's `hasDerivAt_pi` (the direct vector-form proof times out at `whnf` on a variable vertex type; recorded trap) |
| `heatKernel_firstOrder_remainder_apply_le` | **the first-order remainder bound, entrywise form** (Phase C Step 2): on the window `\|t · λᵢ\| ≤ 1`, `\|(e^{-tL} x) a − x a + t (L x) a\| ≤ t² · ∑ᵢ λᵢ² \|vᵢ ⬝ᵥ x\| \|vᵢ a\|` at every coordinate `a` — the boundary-observable Taylor bound the dissolution theorem consumes; coordinate + generator coordinate expanded over the proved eigenbasis, the three sums combined termwise, each mode's scalar remainder by the pin's `Real.abs_exp_sub_one_sub_id_le`; no nonnegativity hypothesis |
| `heatKernel_firstOrder_remainder_interval` | **the `[0, T]` interval packaging** (Phase C Step 2): the same bound uniformly on `[0, T]` whenever `T` meets the window (`\|T · λᵢ\| ≤ 1`), the hypothesis transfer `\|t · λ\| = t\|λ\| ≤ T\|λ\| = \|T · λ\| ≤ 1` by monotonicity |

### `Scaffold.Mathlib.Dynamics.DiscreteAffine` (discrete-affine dynamics)

Delivered 2026-08-23, complete, per
`proposals/discrete-affine-convergence.md` — the `sgt-gaps.md` item-2
consumer interface (the external `spectral-proof` rewrite project's
named request), opening the discrete-affine slice of backlog item 5
(consensus maps, synchronization, and general graph semigroups remain
gated). Pure hard crust, zero axioms — everything composes the pin's
`tendsto_pow_atTop_nhds_zero_of_abs_lt_one` and
`Filter.Tendsto.smul_const`; the statements carry no graph structure
(the proposal's own scope note), hence the standalone `Dynamics` area
rather than the event-driven `GraphTheory.Dynamics`. Stated at a
general real normed space; the consumer's `V → ℝ`/`Fintype V` shape is
the instance. QA at `Scaffold/QA/Dynamics/DiscreteAffine_QA.lean`.

| Declaration | Content |
|-------------|---------|
| `tendsto_pow_smul_atTop_nhds_zero` | geometric decay on vectors: `\|r\| < 1 → r ^ n • x → 0` (Step 1 — the pin's scalar fact lifted through `smul_const`) |
| `affineIteration_eq` | the affine-iteration closed form `x n = (1−α)^n • (x 0 − e) + e` by pure module induction (no topology) |
| `affineIteration_tendsto_atTop` | convergence of `x_{n+1} = (1−α) • x_n + α • e` to `e` under `0 < α < 2` (Step 2 — the closed form plus Step 1 at `r = 1−α`) |

### `Scaffold.Mathlib.GraphTheory.Dynamics` (dynamic frontier)

Real definitions: `TimeVaryingGraph`, `laplacianSequence`,
`IsEventDriven`, `laplacianSequence_symmetric`.

No axioms remain in this module. It previously admitted a per-step
subspace-persistence axiom (`spectral_persistence`, deprecated
2026-08-17), retired 2026-08-20 with zero non-QA consumers — the
motivating use is covered by the derived layer's proved two-endpoint
chain (`Derived.ProjectorDrift.davisKahanTwoPoint`,
`Derived.ProjectorDrift.eventStreamProjectorDrift`, which sums to a
per-step bound if one is needed). See `docs/6_SGT_BACKLOG.md` for the
retirement record.

### `Scaffold.Mathlib.GraphTheory.Krylov` (Krylov methods, the Chebyshev layer, and the Kaniel–Paige spectral discharge)

Steps 0–1c of the Lanczos/Kaniel–Paige program
(`proposals/approximate-spectral-projection.md`, Steps 0, 1a, and 1b
delivered 2026-08-23; Step 1c — the final statement — delivered
2026-08-24, **the proposal COMPLETE**). The reusable pieces the
cleared Kaniel–Paige shape is assembled from, the Step-1b spectral
discharge that closes the skeleton's five named sites on the shelf's
eigenbasis machinery, and the Step-1c final statement `kanielPaige`
(the `tan²φ`/`γ` form, decomposition internal). All proved, zero
axioms; the Saad §6 locator is carried by `kanielPaige`'s own
docstring with the proposal's verify-against-the-physical-copy caveat
(the proposal owns the statement). QA at
`Scaffold/QA/SpectralGraph/Krylov_QA.lean` (two-route polynomial
action and membership, the degree-guard refutation, the composed
`natDegree_T` use, the full skeleton instantiation on a diagonal
fixture, the band-map pins and transfer engines two-route, the
composite `kanielPaigeChebyshev` instantiated on `diag(3,1,0)` with
the band hypothesis derived from the eigen-equation and an independent
raw route proving the true Krylov-witness gap strictly inside the
delivered bound; and the Step-1c witnesses — the final form's bound
proved expression-equal to the composite's `16/75`, the `k = 1`
degenerate case at the plain Rayleigh-gap value, the `b = u`
tightness with the bound attained at exactly `Ltop`, and the
simple-top guard refuted on the top-multiplicity `diag(3,3,0)`
fixture).

| Declaration | Content |
|-------------|---------|
| `abs_T_eval_le_one` | the Chebyshev band bound `\|T_n(x)\| ≤ 1` on `[−1, 1]`, from the pin's `T_real_cos` |
| `natDegree_T` | `(T ℝ (n : ℤ)).natDegree = n` — the Step-0-priced pin gap (two-step induction at `T_add_two`) |
| `one_le_eval_T_of_one_le` | `1 ≤ T_m(x)` at `x ≥ 1` — the second priced gap, through the private index-monotonicity conjunction engine |
| `sum_mulVec` | the `*ᵥ`-action distributes over Finset sums in the matrix argument (pin-gap helper) |
| `krylovSpan` | the `k`-th Krylov space `span {b, Mb, …, Mᵏ⁻¹b}` — the variational object Rayleigh–Ritz optimizes over |
| `scalar_mul_eq_smul` | `algebraMap ℝ (Matrix V V ℝ) a * M = a • M` (the action helper) |
| `aeval_mulVec_eq_eval_smul` | polynomial-eigenaction transfer `p(M) *ᵥ v = p(μ) • v` at `M *ᵥ v = μ • v`, through `Heat.pow_mulVec_smul` |
| `aeval_mulVec_mem_krylovSpan` | degree-`< k` polynomial images of `b` lie in `krylovSpan M b k` |
| `kanielPaigeSkeleton` | the Kaniel–Paige bound in hypothesis form: from `b = c • u + s • g` and the five named spectral sites (`hp₁`, `horth`, `horthM`, `hbottom`, `hband`), the Krylov space contains nonzero `x` with `Ltop − R_M(x) ≤ (Ltop − Lbot) · s² / (c² Tv²)` |
| `eigvec_dotProduct_mulVec` | self-adjointness transfer at any eigenvector: `u ⬝ᵥ (M *ᵥ y) = μ (u ⬝ᵥ y)` at `M *ᵥ u = μ • u` (not tied to `eigvecOf`) |
| `eigvec_dotProduct_pow_mulVec` | the power transfer `u ⬝ᵥ (M ^ j *ᵥ g) = μ ^ j (u ⬝ᵥ g)` (transpose-power commutation at `IsSymm`) |
| `eigvec_dotProduct_aeval_mulVec` | the polynomial transfer `u ⬝ᵥ (p(M) *ᵥ g) = (u ⬝ᵥ g) · p(μ)` — the `horth` engine at `u ⊥ g` |
| `eigvecOf_dotProduct_aeval_mulVec` | the eigenbasis component form: the `i`-th eigencomponent of `p(M) y` is `p(μ i)` times that of `y` |
| `dotProduct_aeval_mulVec_self` | Parseval for polynomial images: `‖p(M) y‖² = ∑ (p(μ i))² (v i ⬝ᵥ y)²` |
| `quadForm_aeval_mulVec` | the quadratic-form resolution `xᵀ M x` of a polynomial image: `∑ μ i (p(μ i))² (v i ⬝ᵥ y)²` |
| `bandMap` | the affine band map `w(λ) = (2λ − Ltwo − Lbot)/(Ltwo − Lbot)`, sending the spectral band onto `[−1, 1]` |
| `bandMap_eval` / `bandMap_eval_bot` / `bandMap_eval_two` | the closed form and the endpoint pins `w(Lbot) = −1`, `w(Ltwo) = 1` |
| `abs_bandMap_eval_le_one` | the band range: `\|w(μ)\| ≤ 1` on `[Lbot, Ltwo]` |
| `one_le_bandMap_eval` | the growth pin `1 ≤ w(Ltop)` at `Ltwo ≤ Ltop` (the `hTv` route) |
| `natDegree_bandMap` | `(bandMap Ltwo Lbot).natDegree = 1` (the affine side of `hdeg`) |
| `exists_unit_decomposition` | unit `b` along unit `u`: `b = c • u + s • g` with `g ⊥ u`, `‖g‖² ≤ 1`, `c² + s² = 1` |
| `kanielPaigeChebyshev` | **the spectral discharge complete**: at the Chebyshev-composed band polynomial `T_{k−1} ∘ w`, the full Kaniel–Paige bound with every spectral site discharged from the eigenbasis-level band hypothesis (out-of-band eigenvectors parallel to `u`) |
| `kanielPaige` | **the final statement (Step 1c)**: the classical Kaniel–Paige bound at the Step-0 recorded shape — unit `b` with `u ⬝ᵥ b ≠ 0`, the decomposition internal, the bound phrased `(Ltop − Lbot) · tan²φ / T_{k−1}(1 + 2γ)²` at `γ = (Ltop − Ltwo)/(Ltwo − Lbot)`; composed from `kanielPaigeChebyshev` via `c = u ⬝ᵥ b`, `s² = 1 − c²`, `w(Ltop) = 1 + 2γ` |

### `Scaffold.Mathlib.GraphTheory.PolyFilter` (polynomial filters and band projection — the Chebyshev layer's second consumer)

`proposals/polyfilter-band-projection.md`, Steps 0+1 delivered 2026-08-24
(zero new axioms). The matrix-level functional calculus behind the
Krylov Step-0 survey's recorded filter shape
`‖p_d(M) − bandProjector M hM a b‖₂ ≤ ε(d, gaps)`: a filter-agnostic
transfer engine (per-eigenvalue filter quality in, operator-norm bound
out — no eigenvalues of the difference computed anywhere) plus the two
classical top-eigenspace instantiations, the second of which makes the
Krylov Chebyshev scalar layer a *two-consumer* layer. QA at
`Scaffold/QA/SpectralGraph/PolyFilter_QA.lean` (on the `diag13`
fixture reused from `Band_QA`: exact-projector recovery through an
affine filter at ε = 0 by theorem and raw routes, the power and
Chebyshev ε constants *attained* at the out-mode, the power-vs-
Chebyshev rate comparison `1/17 < 4/9`, and the out-of-band
filter-quality hypothesis refuted in proved form with the norm
lower-bounded at `1 > 1/2` through the vector the difference fixes).

| Declaration | Content |
|-------------|---------|
| `eigvecOf_dotProduct_spectralProjector_mulVec` | the threshold projector's component action `v i ⬝ᵥ (P_c *ᵥ y) = χ_{λ i ≤ c} (v i ⬝ᵥ y)` (the `dotProduct_eigvecOf_mulVec` mirror at the projector, through symmetry + the delivered eigenbasis action) |
| `eigvecOf_dotProduct_bandProjector_mulVec` | the band projector's component action — in-band modes pass, out-of-band modes annihilate; the `a ≤ b` guard load-bearing for the indicator form (at `a > b` the total definition is the negated band) |
| `aeval_sub_bandProjector_l2OpNorm_le` | **the transfer theorem**: within `ε` of `1` at every in-band eigenvalue and of `0` at every out-of-band one ⇒ `‖p(M) − B_{a,b}‖ ≤ ε` — Krylov's polynomial transfer, the band component action, Parseval, and the Resolvent `opNorm_le_bound`/`cstar_norm_def` spine held in one statement (load-bearing on all four) |
| `powFilter_l2OpNorm_le` | the power filter: spectrum in `[0, c]`, band `(t, c]` top-only ⇒ `‖(M/c)^d − B_{t,c}‖ ≤ (t/c)^d` — the power-method rate, attained at out-modes |
| `chebyshevFilter` | the damped Chebyshev filter `T_d ∘ w / T_d(w(Ltop))` at the Krylov layer's affine band map `w = bandMap t Lbot` |
| `chebyshevFilter_eval` | the filter's closed form: `p(μ) = T_d(w(μ)) / T_d(w(Ltop))` |
| `chebyshevFilter_l2OpNorm_le` | **the Chebyshev-damped instantiation** (the Chebyshev layer's second consumer: `abs_T_eval_le_one`, `one_le_eval_T_of_one_le`, `bandMap` and its pins): spectrum in `[Lbot, Ltop]`, top-only band ⇒ `‖T_d(w(M))/T_d(w(Ltop)) − B_{t,Ltop}‖ ≤ 1/T_d(w(Ltop))` — the damped-iteration rate, strictly better than power in the small-gap regime |

### `Scaffold.Mathlib.GraphTheory.FunctionalCalculus` (the Hermitian functional-calculus bridge)

The Scaffold–Mathlib bridge proposal's Steps 1–3 (2026-08-25,
`proposals/hermitian-functional-calculus-bridge.md`): Mathlib's proved
continuous functional calculus
(`Matrix.IsHermitian.cfc`, `Mathlib/LinearAlgebra/Matrix/
HermitianFunctionalCalculus.lean`) exposed at the shelf's
real-symmetric convention and tied to the shelf's own hand-built
spectral-filter machinery. Not a re-proof of the spectral theorem, not
a path to retiring any axiom, not a Krylov/Chebyshev replacement — the
consolidation layer the four hand-built "function of a symmetric
matrix" notions (`spectralProjector`/`bandProjector`, PolyFilter,
`heatKernel`, `tikhonovShrinkage`) can now be stated against.

| Declaration | Content |
|-------------|---------|
| `spectralCalc` | the thin wrapper `spectralCalc M hM f := (isHermitian_of_isSymm hM).cfc f` — Mathlib's calculus consumed, not rebuilt; bare `ℝ → ℝ` functions admissible (finite spectrum), no continuity hypothesis |
| `spectralCalc_apply` | the entry form / falsifiability anchor: `f(M) a b = ∑ i, f (eigvalOf M hM i) * eigvecOf M hM i a * eigvecOf M hM i b` — the calculus and the eigenbasis filter sum are the same operator entrywise |
| `spectralCalc_mulVec_apply` | the action form: `f(M) *ᵥ y` is exactly the filtered signal `∑ i, f (λᵢ) (vᵢ ⬝ᵥ y) • vᵢ` of the graph-signal-processing expansion |
| `spectralCalc_mulVec_eigvecOf` | the eigenvector action, hypothesis-free: `f(M) *ᵥ vₖ = f (eigvalOf M hM k) • vₖ` — the load-bearing bridge every calculus consumer needs |
| `dotProduct_eigvecOf_spectralCalc_mulVec` | the coefficient bridge consuming `GraphTheory.Tikhonov.dotProduct_eigvecOf_filter` verbatim: the shelf's arbitrary-filter expansion and the calculus agree coefficient-by-coefficient |
| `spectralCalc_indicator_eq_spectralProjector` | the recovery: at the indicator of `(· ≤ c)` the calculus returns exactly the shelf's hand-built `spectralProjector M hM c` — the proof the bridge is real rather than decorative |
| `spectralCalc_id` | the calculus identity `spectralCalc M hM id = M` |
| `continuousOn_of_finite_real_spectrum` | every function is continuous on a matrix's (finite) real spectrum, via `Finite.instDiscreteTopology` — the `ContinuousOn` supplier Mathlib's generic CFC lemmas need (`cfc_cont_tac`'s `fun_prop` cannot discharge spectrum-restricted continuity of spectral-data functions) |
| `tikhonovMinimizer_eq_spectralCalc_mulVec` | **the first consumer recovered** (2026-08-25, `proposals/hermitian-calculus-consumer-tikhonov-heat.md`): `x* = f(L) *ᵥ y` at `f = tikhonovShrinkage π`, hypothesis-free — the eigenbasis-defined minimizer IS the calculus at `π ↦ π/(λ+π)` |
| `add_smul_one_mul_spectralCalc_tikhonovShrinkage` | the normal equation through the calculus algebra: `(L + π•1) * f(L) = π • 1` under PSD + `0 < π`, proved via Mathlib's generic CFC (`cfc_add_const`/`cfc_id'`/`cfc_mul`/`cfc_congr`/`cfc_const`) — an eigenbasis-free route to a statement the shelf had only through the eigenbasis expansion |
| `matrix_eq_of_forall_mulVec_eq` | the action-equality helper: two real matrices are equal when their `mulVec` actions agree on every vector (entries recovered at the coordinate units `Pi.single j 1`) — the reconciliation tool for action-level equality theorems |
| `heatKernel_eq_spectralCalc_exp` | **the second consumer recovered** (2026-08-25, the Heat half, completing the consumer stub): `heatKernel A t = spectralCalc (laplacian A) hL (fun x => Real.exp (-(t * x)))` — a genuine reconciliation of two independent proof stacks (`Heat.lean`'s entrywise exponential-series engine vs Mathlib's `cfc`), in effect the spectral mapping theorem for `exp` at real-symmetric matrices |
| `spectralCalc_exp_mul` | the calculus semigroup at the exponential family: `f_s(M) * f_t(M) = f_{s+t}(M)` via `cfc_mul` + `cfc_congr` promoting pointwise `Real.exp_add` from the spectrum — the calculus-algebra mirror of `Matrix.exp_add_of_commute`, eigenbasis-free |
| `heatKernel_mul_heatKernel_of_spectralCalc` | the semigroup law through the calculus: composing the equality theorem with `spectralCalc_exp_mul`, a second proof technology for `Heat.lean`'s hypothesis-free `heatKernel_mul_heatKernel` (this route needs `A.IsSymm`; the original remains primary) |
| `add_smul_one_mul_spectralCalc_tikhonovShrinkage_of_forall_add_ne_zero` | **the general-symmetric normal equation** (2026-08-25, the resolvent-identity delivery's priced follow-on): merely symmetric `M` under spectrum-avoidance `x + π ≠ 0` gives `(M + π•1) * f(M) = π • 1` — no PSD, no `0 < π`; the delivered PSD statement is derived from this parent, shape unchanged |
| `spectralCalc_tikhonovShrinkage_eq_smul_inv_of_forall_add_ne_zero` | the general-symmetric **resolvent identity, calculus route**: `f(M) = π • (M + π•1)⁻¹` under avoidance alone, through Mathlib's `cfc_inv` + `Matrix.nonsing_inv_eq_ring_inverse` at the additive layer `cfc (x+π) = M + π•1` — no matrix inverse, determinant, or cancellation lemma anywhere |
| `spectralCalc_tikhonovShrinkage_eq_smul_inv` | **the headline, matrix-algebra route**: under PSD + `0 < π`, `f(L) = π • (L + π•1)⁻¹` — a three-layer load-bearing join (the normal equation + the shelf resolvent program's spectral-gap-free `isUnit_det_add_smul_one_of_quadForm_nonneg`, its first calculus consumer, + `laplacian_psd`, closed by `nonsing_inv_mul_cancel_left`) |
| `spectralCalc_tikhonovShrinkage_eq_smul_inv'` | the same statement by the calculus route (the general identity instantiated): two proof technologies, one statement — the divergence-falsifier pattern |
| `tikhonovMinimizer_eq_smul_inv_mulVec` | the consumer corollary: `x* = π • ((L + π•1)⁻¹ *ᵥ y)` — the textbook Tikhonov shifted-inverse solve as a shelf theorem |

The complex half needs no second wrapper (Mathlib's `cfc` is stated
for any `RCLike 𝕜`; complex-Hermitian consumers — the magnetic
Laplacian's `magneticLaplacian_isHermitian` — use it at `𝕜 = ℂ`
directly, confirmed elaborating by the QA file's `fcM2c_cfc_id`
witness).

The first consumer reconciliation (the "Recovered instances" section,
2026-08-25, the Tikhonov half of the consumer stub): `Tikhonov.lean`
stays exactly as delivered; the rows above are additive. QA Section E
pins the reconciliation numerically on the `Tikhonov_QA` K₂ fixture
(two constructions, one number: the calculus routes `![1,0]` to the
hand-solved `![2/3, 1/3]`), exhibits the normal equation by two
independent routes, and fences the `0 < π` hypothesis with the
`π = -2` junk-division refutation.

The resolvent-identity delivery (2026-08-25, the consumer stub's two
priced follow-ons — the family closed): the Tikhonov filter IS `π`
times the shifted inverse, and the shelf's Aug-19 resolvent program
(`Analysis/OperatorTheory/Resolvent.lean`) gains its first
functional-calculus consumer — its spectral-gap-free invertibility
supplier `isUnit_det_add_smul_one_of_quadForm_nonneg` carries the
headline's determinant hypothesis. QA Section G pins both routes to
one concrete matrix (joined to Section E's calculus instance and the
hand-solved Gaussian), and fences the `π = -2` degeneration with the
avoidance failure proved spectral — both junk surfaces (shrinkage
division, singular inverse) colliding in one refuted entry.

The second consumer reconciliation (later the same day, the Heat
half — the stub complete): `Heat.lean` likewise stays exactly as
delivered. QA Section F pins this reconciliation doubly-routed on the
same K₂ fixture (the closed form `!![(1±e^{-2t})/2]` by Mathlib's
`cfc` through the equality theorem vs by the series engine with the
sign-free outer-product pins — two independent proof stacks, one
matrix; the semigroup at times `1, 2` by the calculus route vs the
commute route plus a raw closed-form product check) and fences
nontriviality (`heatKernel K₂ 1 ≠ 1`: diffusion provably moves mass,
refuting any constant-collapse reading).

### `Scaffold.Mathlib.GraphTheory.Sparsification` (leverage-score sparsification, Steps 1 Slices 2–3 — the deterministic core)

The deterministic Spielman–Srivastava algebra
(`proposals/spectral-sparsification-via-leverage-scores.md`, the
program completed through Slice 3 on 2026-08-27 and the follow-ons on
2026-08-28): every input the `matrix_bernstein` assembly consumes, at
the classical constants `R = 1/q` and `‖Σ‖ ≤ 1/q` proved rather than
asserted — plus the sampled operator with its exact pointwise deviation
identity, and (the graph-vector follow-on) the transport, claim A, and
the sampled Laplacian with its form-level correspondence.

| Declaration | Area | Description |
| --- | --- | --- |
| `rankOne` / `rankOne_mulVec` / `rankOne_quadForm` / `rankOne_mul_self` / `rankOne_isSymm` / `rankOne_neg` | Sparsification Slice 2 | The rank-one outer product and its algebra (action, quadratic form, idempotence `(v⊗v)² = ‖v‖²(v⊗v)`, symmetry, evenness) |
| `dotProduct_sq_le` / `dotProduct_self_nonneg` / `dotProduct_self_pos_of_ne_zero` | Sparsification Slice 2 | Squared Cauchy–Schwarz in plain dot-product form (through the Euclidean inner product) and the definiteness facts |
| `l2OpNorm_rankOne_le` | Sparsification Slice 2 | **The rank-one operator-norm bound** `‖v vᵀ‖ ≤ v ⬝ᵥ v` (per-eigenvalue Rayleigh quotients at unit eigenvectors) |
| `laplacian_dirichlet_bilinear` | Sparsification Slice 2 | Polarized Dirichlet form: `∑∑ A ΔxΔy = 2 x ⬝ᵥ (L *ᵥ y)` |
| `eigvalOf_laplacian_nonneg` | Sparsification Slice 2 | Laplacian eigenvalues nonnegative on nonnegative symmetric input (PSD at the eigenvector) |
| `ssEdgeVec` / `ssEdgeVec_self` / `ssEdgeVec_swap` / `ssEdgeVec_dotProduct_self` / `sum_ssEdgeVec_dotProduct_self` | Sparsification Slice 2 | **The SS edge vectors in eigen-coordinates** (`√(w/2)·(v_k u − v_k v)/√λ_k`, zero-eigenvalue entries dropped; no pseudoinverse or matrix square root), with `‖v_e‖² = w_e R_eff/2` and the Foster budget corollary `∑_{u,v} ‖v_e‖² = card V − 1` |
| `imageProjector` / `imageProjector_mul_self` / `l2OpNorm_imageProjector_le` / `trace_imageProjector_eq` / `quadForm_imageProjector_le` / `quadForm_imageProjector_eq` | Sparsification Slice 2 | The eigen-coordinate projector onto `im L`: idempotent, `‖Π‖ ≤ 1`, `trace = card V − 1` (connected), Rayleigh domination, and `qF(Π) x = ∑_e (x ⬝ᵥ v_e)²` |
| `quadForm_imageProjector_eq_of_mulVec_eq` | Sparsification follow-on (2026-08-28) | **The cone identity**: at every `im Π`-coordinate vector (`Π *ᵥ x = x`), `qF(Π) x = x ⬝ᵥ x` — the piece that converts the additive quadratic-form tail into the multiplicative `(1±ε)` sparsifier reading; equality fails off the cone (the zero-eigenvalue mass is dropped), fenced at `K₂` in QA |
| `ssTransport` / `imageProjector_mulVec_ssTransport` / `quadForm_laplacian_eq_ssTransport` | Sparsification follow-on (2026-08-28) | **The eigen-coordinate transport** `c(x)_k = √λ_k (x ⬝ᵥ q_k)` — on the `im Π` cone *by construction* and `L`-isometric (`xᵀLx = ‖c(x)‖²` via the spectral resolution); the mechanism that removes the cone restriction from the graph-vector sparsifier statement (nonnegativity load-bearing — junk-zero `√` at nonpositive spectra, fenced in QA) |
| `ssTransport_dot_ssEdgeVec` | Sparsification follow-on (2026-08-28) | **Claim A**: `c(x) ⬝ᵥ v_e = √(w_e/2)(x u − x v)` at positive pairs — the kernel-eigenvector constancy (`eq_of_laplacian_mulVec_eq_zero_of_pos_weight`) doing the load-bearing work |
| `ssEdgeDiff` / `dotProduct_ssEdgeDiff` | Sparsification follow-on (2026-08-28) | The vertex-space edge-difference vector and its pairing identity `x ⬝ᵥ (e_u − e_v) = x u − x v` |
| `ssWeight_nonneg` / `ssLaplacian` / `ssLaplacian_isSymm` / `quadForm_ssLaplacian_nonneg` | Sparsification follow-on (2026-08-28) | **The sampled Laplacian** `∑_e (g_e/2 · w_e) • rankOne (e_u − e_v)` — the SS object in graph coordinates: symmetric, PSD, expected to be `laplacian A` |
| `quadForm_ssLaplacian_eq` | Sparsification follow-on (2026-08-28) | **The form-level correspondence**: `xᵀL̃(ω)x = c(x)ᵀ S(ω) c(x)` for every vector and every outcome (claim A squared at positive pairs; junk-zero corners at nonpositive weights) — the deterministic heart of the graph-vector tail |
| `sum_rankOne_ssEdgeVec` | Sparsification Slice 2 | **The projector identity**: `∑_e v_e v_eᵀ = Π_{im L}` *exactly* (the ordered-pair `1/√2` halving absorbing the double count) |
| `integral_bern_center_sq` | Sparsification Slice 2 | The Bernoulli second moment `E[(δ/p − 1)²] = (1−p)/p`, linearized through the first moment |
| `ssProb` / `ssDelta` / `ssSummand` / `ssMeasure` / `ssVariance` | Sparsification Slice 2 | The Finding-A-guarded sampling design on the Slice-1 `bernPMF` at `ι = V × V`: probabilities `min 1 (q‖v_e‖²)`, indicators, guarded summands, the measure, and the variance statistic |
| `integral_ssSummand_eq_zero` | Sparsification Slice 2 | **Centering** `∫ X_e = 0` with *no connectivity hypothesis* (zero-leverage pairs absorbed by the zero rank-one factor; saturated by the guard) |
| `ssSummand_l2OpNorm_le` | Sparsification Slice 2 | **Boundedness** `‖X_e ω‖ ≤ 1/q` for every outcome (the classical `R = 1/q`, uniformity via the guard) |
| `integral_ssSummand_mul_self` / `sum_integral_ssSummand_mul_self` / `l2OpNorm_ssVariance_le` | Sparsification Slice 2 | **The variance statistic**: `∑_e ∫ X_e X_e = Σ` and the headline `‖Σ‖ ≤ 1/q` (eigenvalue route) |
| `quadForm_add` / `quadForm_sub_matrix` / `quadForm_smul` | Sparsification Slice 3 | Quadratic-form linearity in the matrix argument |
| `l2OpNorm_mulVec_dotProduct_le` | Sparsification Slice 3 | The operator-norm action bound in dot-product form: `(M x) ⬝ᵥ (M x) ≤ ‖M‖² (x ⬝ᵥ x)` (local route to the C*-norm spine) |
| `abs_quadForm_le_of_l2OpNorm_le` | Sparsification Slice 3 | **The norm→form transfer** `‖M‖ ≤ t → |xᵀMx| ≤ t (x ⬝ᵥ x)` — symmetry-free (C–S on the action form) |
| `ssWeight` / `ssSampled` | Sparsification Slice 3 | The deterministic sampled weight (the saturation guard as weight `1`) and **the sampled operator** `∑_e g_e(ω) • (v_e v_eᵀ)` |
| `ssSampled_sub_imageProjector` | Sparsification Slice 3 | **The exact deviation identity**: `ssSampled ω − Π_{im L} = ∑_e X_e ω` *pointwise in ω* (no null-event caveats) |
| `ssSummandBool` / `ssSummand_eq_ssSummandBool` / `ssSummand_fun_eq` | Sparsification Slice 3 | The Bool-valued summand shape (a finite-range function of one coordinate) |
| `stronglyMeasurable_ssSummand` / `indepFun_ssSummand` | Sparsification Slice 3 | The `h_meas` and `h_indep` clauses of `matrix_bernstein` at this design, through the Slice-1 transfer layer |

### `Scaffold.Mathlib.GraphTheory.EdgePerturbation` (the matrix-Hoeffding engine — 2026-08-28)

The deterministic engine for `matrix_hoeffding`'s first theorem consumer:
single-edge Laplacian algebra joined to the `rankOne` family, the
`Matrix.PosSemidef` helpers the pin lacks, and the centered Bernoulli
edge-perturbation design with every repaired-axiom clause proved
(sign-free — no hypothesis on the weight matrix).

| Declaration | Area | Description |
| --- | --- | --- |
| `edgeAdj` / `edgeAdj_isSymm` / `deg_edgeAdj` | Edge perturbation | The single-edge adjacency `w` on `{i, j}`, its symmetry and row sums |
| `laplacian_edgeAdj` | Edge perturbation | `L(edge i j w) = w • (e_i − e_j)(e_i − e_j)ᵀ` — the join to the `rankOne` algebra, valid also at `i = j` |
| `posSemidef_smul_nonneg` / `rankOne_posSemidef` | PSD helpers | Nonnegative scaling and rank-one matrices are PSD (pin gaps) |
| `posSemidef_mul_self_of_isSymm` | PSD helpers | **Squares of symmetric matrices are PSD** — no PSD hypothesis on `M`; through `dotProduct_mulVec_comm_of_isSymm`, its first consumer outside the projector-uniqueness layer |
| `perturbEdgeLap` / `perturbEdgeLap_posSemidef` / `laplacian_edgeAdj_eq_perturbEdgeLap` | Edge perturbation | The single-edge Laplacian block and its PSD at nonnegative weights |
| `perturbSummand` / `perturbSummand_mul_self` / `perturbSummand_sq_le` | Edge perturbation | The centered Bernoulli summand `(δ_e − p_e) • L_e` and the **semidefinite bound `X_e² ⪯ L_e²`** — the axiom's `h_bound` clause, sign-free, load-bearing only on `p ∈ [0, 1]` |
| `stronglyMeasurable_perturbSummand` / `indepFun_perturbSummand` | Edge perturbation | The `h_meas`/`h_indep` clauses through BernoulliProduct's matrix transfer layer |
| `perturbAdj` / `perturbWeight` / `perturbWeight_isSymm` | Edge perturbation | **(2026-08-28, the pipeline delivery) the random weight-space perturbation** — the summed centered single-edge adjacencies, symmetric for every outcome |
| `perturbWeight_apply_of_ne` / `perturbWeight_apply_diag` | Edge perturbation | The entry formulas: off the diagonal the two ordered pairs on `{i, j}` contribute; on the diagonal one (no double count) |
| `perturbWeight_entry_nonneg` | Edge perturbation | **The nonnegativity design condition** (2026-08-29, the admissibility dissolution): at `p e + p (e.2, e.1) ≤ 1` every resampled entry is nonnegative at *every* outcome — off-diagonal `A i j · (1 + δ_{ij} + δ_{ji} − p_{ij} − p_{ji})`, diagonal `A i i · (1 + δ_{ii} − p_{ii})`; tight at the uniform `p ≡ ½` boundary, refuted-when-dropped at `p ≡ 9/10` (QA) |
| `laplacian_perturbWeight` | Edge perturbation | **The packaging identity** `laplacian (perturbWeight A p ω) = ∑ₑ perturbSummand A p e ω` — the concentration → stability pipeline's deterministic hinge, through `laplacian_sum`/`laplacian_smul` (delivered the same day in `Spectral.lean`, retiring the sparsification program's recorded engine prerequisite) |
| `degPerturbWeight` / `degPerturbSummand` / `deg_perturbAdj` / `deg_perturbWeight` | Edge perturbation | (2026-08-29, the degree-concentration delivery) the scalar-companion design: the ordered pair's weight in vertex `v`'s degree and its centered Bernoulli summand, with the row-sum transport |
| `deg_resampled` | Edge perturbation | **The degree-deviation identity** `deg (A + perturbWeight A p ω) v = deg A v + ∑ₑ degPerturbSummand A p v e ω` — the deterministic hinge of the degree tail, through `deg_add`/`deg_sum` (the degree-linearity package delivered beside `deg_smul` in `Spectral.lean`) |
| `measurable_degPerturbSummand` / `indepFun_degPerturbSummand` / `degPerturbSummand_abs_le` / `integral_degPerturbSummand_eq_zero` | Edge perturbation | The four `hoeffding_inequality` clauses at the design (2026-08-29): measurability and pairwise independence through BernoulliProduct's scalar layer, the bound `\|X_e\| ≤ \|w_v(e)\|` (sign-free), and the centering `∫ X_e = 0` through `integral_delta` + the audit's integrability safety — no `p ≠ 0` guard needed |
| `integral_sq_degPerturbSummand` | Edge perturbation | The `bernstein_inequality` variance clause at the design (2026-08-29, the Bernstein twin): `∫ X_e² ∂μ = w_v(e)² p e (1 − p e)` through BernoulliProduct's second-moment companion `integral_sq_delta_sub` (`∫ (δ_e − p_e)² = p_e (1 − p_e)`, beside `integral_delta`) — identifies the axiom's variance statistic exactly, making the twin variance-adaptive |

### `Scaffold.Derived.EdgePerturbationDrift` (the concentration → subspace-stability pipeline — 2026-08-28)

The first join of the two most recent center deliveries:
high-probability Fiedler rotation under the centered Bernoulli edge
design, in the `eventStreamProjectorDrift` inclusion idiom. All four
declarations are **conditional on the `matrix_hoeffding` axiom via the
tail alone**; the Davis–Kahan side, the kernel identification, the
packaging identity, and the Weyl separation discharge are proved. The
separation is stated against the *base* graph's deterministic gap —
no per-outcome spectral hypothesis. The primed pair (2026-08-29) is
the sharpened, matched-threshold interface: the `s/(γ−s)` shape of
`eventStreamProjectorDrift` with the gap consumed inline and the
threshold matched to the tail — the envelope-optimal instance of the
`t/δ` family at every threshold (at threshold `u` the exponent is
maximized at `s = γu/(1+u)`; QA proves the domination and
same-threshold identities).

| Declaration | Area | Description |
| --- | --- | --- |
| `edgePerturbation_fiedlerSubspace_drift` | Fiedler stability | At `t + δ ≤ λ₃(A) − λ₂(A)`: `μ{‖P(A+E_ω) − P(A)‖ ≥ t/δ} ≤ 2 d exp(−t²/(2‖∑ₑ L_e²‖))` — the bottom-2 subspace (the Fiedler cluster on a connected base) under random edge resampling |
| `edgePerturbation_fiedlerLine_drift` | Fiedler stability | The payoff: the same tail for the Fiedler *line* itself, under the per-outcome nonnegativity/connectivity design constraints the kernel identification needs (both hold universally at `p_{ij} + p_{ji} ≤ 1` on positive-weight pairs); QA pins the closed-form instance `6 exp(−1/24)` on the three-path at `p ≡ ¼` |
| `edgePerturbation_fiedlerSubspace_drift'` | Fiedler stability | The sharpened (matched-threshold) form mirroring `eventStreamProjectorDrift` exactly: at `0 < s < γ ≤ λ₃(A) − λ₂(A)`, `μ{‖P(A+E_ω) − P(A)‖ ≥ s/(γ−s)} ≤ 2 d exp(−s²/(2‖∑ₑ L_e²‖))` — the gap consumed inline, and the envelope-optimal instance of the `t/δ` family at every threshold (QA proves the envelope arithmetic) |
| `edgePerturbation_fiedlerLine_drift'` | Fiedler stability | The sharpened payoff: the same `s/(γ−s)` statement for the Fiedler *line* itself, at the same design constraints; QA pins the closed-form instances `6 exp(−1/24)` (join point, γ = 2, s = 1) and `6 exp(−2/27)` (threshold 2, s = 4/3) plus the strict improvement over a valid non-envelope instance at the same threshold |

### `Scaffold.Derived.SparsificationTail` (leverage-score sparsification, Slice 3 — the axiom-backed assembly)

The program's payoff: `matrix_bernstein`'s first real theorem consumer
(2026-08-27). The declarations are **conditional on the
`matrix_bernstein` axiom** (Tropp 2012, Theorem 1.1) — every
hypothesis clause is proved hard crust, the tail inequality itself is
axiom-backed, and `#print axioms` reports the dependency. The
2026-08-28 follow-ons add the multiplicative `(1±ε)` sparsifier shape
and its `q ~ log n/ε²` budget corollary on the same conditional
structure.

| Declaration | Area | Description |
| --- | --- | --- |
| `sparsification_norm_tail` | Sparsification Slice 3 (axiom-conditional) | **The SS deviation tail**: `μ {‖S(ω) − Π_{im L}‖ ≥ t} ≤ 2 d exp(−t²/(2/q + 2t/(3q)))` at the proved constants `R = 1/q`, `‖Σ‖ ≤ 1/q`; Finding B's `Fin n` transport via `Fintype.equivFin` + `Equiv.sum_comp`; no connectivity hypothesis |
| `sparsification_quadForm_tail` | Sparsification Slice 3 (axiom-conditional) | **The quadratic-form tail**: the same bound for the failure of `|xᵀ S x − xᵀ Π x| ≤ t (x ⬝ᵥ x)` for every vector — the additive eigen-coordinate pullback of the norm event |
| `sparsification_multiplicative_tail` | Sparsification follow-on (axiom-conditional, 2026-08-28) | **The `(1±ε)` sparsifier tail** — the field-standard statement shape: the failure of the two-sided bound `(1−ε)(x ⬝ᵥ x) ≤ xᵀ S(ω) x ≤ (1+ε)(x ⬝ᵥ x)` over `im Π`-coordinate vectors obeys the same exponential tail (the additive tail at `t = ε`, legitimate on the cone by the engine identity) |
| `sparsification_multiplicative_budget` | Sparsification follow-on (axiom-conditional, 2026-08-28) | **The sample-complexity corollary**: at `0 < ε ≤ 1`, `0 < δ`, budget `q ≥ (8/3)·log(2 card V/δ)/ε²` drives the multiplicative failure measure below `δ` — the classical `q ~ log n/ε²` sentence at the exact Tropp exponent constant |
| `sparsification_graph_tail` | Sparsification follow-on (axiom-conditional, 2026-08-28) | **The graph-vector `(1±ε)` tail** — the textbook sentence: `(1−ε)xᵀLx ≤ xᵀL̃(ω)x ≤ (1+ε)xᵀLx` failing only on a set of the bound's measure, for *every* graph vector with no `im Π` restriction (the transport is on-cone by construction; the isometry and form correspondence transfer the delivered additive tail verbatim) |
| `sparsification_graph_budget` | Sparsification follow-on (axiom-conditional, 2026-08-28) | **The graph-vector budget corollary**: the same `q ≥ (8/3)·log(2d/δ)/ε²` sentence driving the graph-form failure measure below `δ` (numeric core factored as `sparsification_budget_core`) |

## Applications

These declarations feed the perturbation bridge
([Perturbation map](perturbation.md)) and a retained spectral-persistence
example described in [docs/3_SPECTRAL_THEORY.md](../../docs/3_SPECTRAL_THEORY.md).
That example is compatibility surface, not the SGT roadmap.
