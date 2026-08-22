# Spectral Graph Theory

This index maps the SGT center: Laplacians, sorted spectra, cuts and
conductance, Cheeger theory, interlacing, and event-driven dynamics.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.GraphTheory.{Spectral,SimpleGraphAdapter,Electrical,ElectricalFlow,Foster,Expander,SpectralCertificates,Tikhonov,Band,Cheeger,Mixing,Dynamics}`.

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
eigenvalue bound — the refutation engine of `Cheeger_QA`); top-of-
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
delivered the same day through the Rayleigh-sandwich route. All
proved, zero axioms.

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
| `abs_quadForm_le_of_ortho_onesVec` | **the operator bound on `1⊥` (Step 2 bridge):** `\|xᵀAx\| ≤ μ ‖x‖²` under the Laplacian-spectrum hypothesis `μ ≥ max \|d − λ₂(L)\| \|d − λ_max(L)\|` — the Rayleigh sandwich (lower bound + the generic top domination + the `d`-regular identity; load-bearing on all three) |
| `quadForm_bilinear_sq_le_of_ortho_onesVec` | **the sharp bilinear bound:** `(x ⬝ᵥ (A *ᵥ y))² ≤ μ² ‖x‖² ‖y‖²` on `1⊥ × 1⊥`, by the scaling trick (`√Y•x ± √X•y` through polarization; `a² = Y, b² = X` attains the AM–GM equality, so the product form carries no slack) |
| `dotProduct_centeredIndicator_self` | the variance identity `‖centeredIndicator S‖² = \|S\|(|V|−\|S\|)/\|V\|` — the geometric factor of the mixing bound |
| `expander_mixing_lemma` | **the Expander Mixing Lemma (headline):** `\|e(S,T) − d•\|S\|•\|T\|/\|V\|\| ≤ μ • √(\|S\|\|T\|(|V|−\|S\|)(|V|−\|T\|))/\|V\|` on symmetric, nonnegative, `d`-regular networks with the Laplacian-spectrum hypothesis — the classical discrepancy bridge between algebraic spectral gaps and combinatorial pseudorandomness (Alon–Chung 1988; Hoory–Linial–Wigderson 2006 §2; Vadhan 2012 §4), at the Step 0 restated `√` signature with squaring only inside the proof |


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
proposal's "never exactly 1".

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

### `Scaffold.Mathlib.GraphTheory.Directed` (the directed degree layer)

All statements proved (2026-08-22, `proposals/directed-graph-operators.md`
Steps 0+1), no axioms, no symmetry anywhere. The Step-0 record's discovery
shapes the module: the undirected shelf's `deg` (the row sum) *is* the
out-degree and `walkTransitionMatrix = D⁻¹ A` / `walkLaplacian = I − D⁻¹ A`
are defined symmetry-free — so this module adds the genuinely new directed
quantity (the in-degree) and the degree-level agreement theorems, while
QA certifies the pre-existing walk operators on asymmetric input.

| Declaration | Content |
|-------------|---------|
| `outDeg` | the out-degree `∑ j, A i j` — definitionally the shelf's `deg` (definition) |
| `inDeg` | the in-degree `∑ j, A j i`, the column sum — the genuinely new directed quantity (definition) |
| `outDeg_eq_deg` | the out-degree *is* `deg` (`rfl`) — every `deg`-indexed theorem applies to directed out-degrees verbatim |
| `inDeg_eq_deg_transpose` | the in-degree is `deg` of the transposed network (`rfl`) |
| `inDeg_eq_outDeg_of_isSymm` | agreement on the symmetric cone: `A.IsSymm → inDeg A i = outDeg A i` — the degree brick of the proposal's Step-3 acceptance bar |
| `inDeg_eq_deg_of_isSymm` | agreement with the shelf: `A.IsSymm → inDeg A i = deg A i` |
| `sum_outDeg_eq_sum_inDeg` | **directed handshaking:** `∑ i, outDeg A i = ∑ i, inDeg A i` with no nonnegativity or symmetry hypothesis (`Finset.sum_comm`) |

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

No axioms remain in this module. It previously admitted a per-step
subspace-persistence axiom (`spectral_persistence`, deprecated
2026-08-17), retired 2026-08-20 with zero non-QA consumers — the
motivating use is covered by the derived layer's proved two-endpoint
chain (`Derived.ProjectorDrift.davisKahanTwoPoint`,
`Derived.ProjectorDrift.eventStreamProjectorDrift`, which sums to a
per-step bound if one is needed). See `docs/6_SGT_BACKLOG.md` for the
retirement record.

## Applications

These declarations feed the perturbation bridge
([Perturbation map](perturbation.md)) and a retained spectral-persistence
example described in [docs/3_SPECTRAL_THEORY.md](../../docs/3_SPECTRAL_THEORY.md).
That example is compatibility surface, not the SGT roadmap.
