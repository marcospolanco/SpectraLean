# Spectral Graph Theory

This index maps the SGT center: Laplacians, sorted spectra, cuts and
conductance, Cheeger theory, interlacing, and event-driven dynamics.

## Status

**Implemented and build-certified** (see the QA scoreboard):
`Scaffold.Mathlib.GraphTheory.{Spectral,SimpleGraphAdapter,Electrical,ElectricalFlow,Foster,Expander,SpectralCertificates,Tikhonov,Band,ClusterProjector,Cheeger,Mixing,Oversmoothing,Poincare,Dynamics,Krylov,PolyFilter,Multiway}`.

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

**Adversarial fence audit, Step 1 delivered (2026-09-05,
`proposals/adversarial-fences-spectral-core-family.md`):** the root
shelf — 46 transitive non-QA consumers, the library's most-consumed
surface, invisible to every prior survey because its QA was scattered
across ~10 per-topic files — now has its own QA home
(`Spectral_QA.lean`) and a fenced first cluster. The census (105
hypothesis-bearing theorems, 214 named clauses; multi-run program)
and the Step-1 fences: the `hA : A.IsSymm` cone on
`laplacian_symmetric`, `laplacian_quadForm`, `laplacian_psd`,
`laplacian_dotProduct_mulVec`,
`dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (killed at the new
asymmetric star whose two-dimensional harmonic kernel makes the
hypothesis `L *ᵥ w = 0` genuine while the conclusion fails),
`boundary_compl`, and `conductance_compl`; the `hnonneg` clause of
`laplacian_psd` at the new signed edge; both clauses of
`vol_pos_of_pos_deg`; and the signed-input kills of
`degreeMatrix_diagonal_nonneg` and `boundary_nonneg`. Steps 2-4
(connectivity/kernel, spectral-theorem interface, variational) are
priced in the proposal's census table.

**Adversarial fence audit, Step 2 delivered (2026-09-05, the same
proposal):** the connectivity/kernel cluster — the root shelf's most
load-bearing API — fenced in `Spectral_QA.lean`'s
`AdversarialFencesStep2` section (18 fences + the P4 companion, 79
declarations, all at the standard three axioms, zero axiom contact).
The `hconn` clauses reconcile `Connectivity_QA`'s and
`PotentialSolvability_QA`'s delivered disconnected witnesses into the
per-clause discipline; the `hnonneg` clauses are killed at the new
signed path `sfSignedPath` with connectivity kept genuine — the
kernel is genuinely two-dimensional there, and the solvability hinge
dies through the shelf's own kernel certificate (the zero-sum unit
demand pairs `2 ≠ 0` against the kernel vector). The census's P4
candidate `laplacian_mulVec_eq_zero_of_forall_reachable`'s `hnonneg`
is settled **by refutation** (genuinely load-bearing; the earlier
"row-sum closes without signs" pricing was wrong); the Step-1 cut
residuals close at the negative-min division-rescue fixture
`sfSignedCut` with a hypothesis-free P4 companion for
`conductance_ge_cheegerConstant`; and the `supportGraph`-entanglement
classification is recorded (every `hA` clause of a
`supportGraph`-carrying statement is non-fenceable — the dropped
statement cannot even be formed at an asymmetric fixture).

**Adversarial fence audit, Step 4 delivered (2026-09-05, the same
proposal):** the variational / Courant-Fischer cluster — nineteen
hypothesis-form fences plus the `rayleigh_padVec` hypothesis-free P4
companion in `Spectral_QA.lean`'s `AdversarialFencesStep4` section
(41 public declarations, all at the standard three axioms, zero axiom
contact). `secondEval_variational`'s and `secondEval_le_rayleigh`'s
`hpsd`/`hker`/`hx0`/`hxorth` (the negative Laplacian's `λ₂ = 0` against
every admissible quotient `-2`; `sfProjE0`'s `λ₂ = 1` against the
alternating quotient `1/2`; the junk-zero quotient kills at `x = 0`);
the congruence pair's `h` clauses, resolving Step 3's recorded deferral
for both members (`2 ≠ 0` through two `lambda2_eq_secondEval`-derived
pins; the identity's uniform spectrum against `sfProjE0`'s bottom
entry `0`); `evals_le_of_linearIndependent`'s `hk1`/`hgi`/`hbnd`;
`lambda2_variational`'s `hnonneg` reconciled from the 2026-08-18
pre-discipline refutation; the `_of_ker` twins' seven clauses.
Classifications: `secondEval_smul_of_pos`'s `hpsd`/`hker`
truth-removable-not-fenceable (positive scaling commutes with
sorting). Adjacent coverage cited; one public-docstring repair
(`icFence_psd_fence`); and a QA-lattice defect recorded — the
`Cheeger_QA`/`PotentialSolvability_QA` `edgeAdj` collision blocks
co-import.

**Adversarial fence audit, Step 3 delivered (2026-09-05, the same
proposal):** the spectral-theorem interface layer's priced residue —
seventeen hypothesis-form fences in `Spectral_QA.lean`'s
`AdversarialFencesStep3` section (60 declarations, all at the
standard three axioms, zero axiom contact). The
symmetry-free-conclusion minority: the raw-matrix self-adjointness
identity (`4 ≠ 1` at `dirB`), `smul_isSymm`, and all five clauses of
the projector-uniqueness lemma at an idempotent family sharing the
fixed line `{x | x 1 = 0}`. The side clauses at the identity/zero
matrices through the shelf's own pins: `eigvalOf_le_of_quadForm_nonpos`'s
`hq`, the projector-threshold quartet (killed by the sibling
theorems' satisfiable hypotheses), and the kernel-orthogonality
quintet (the onesVec trio through a Parseval exclusion engine
load-bearing on `dotProduct_eigvecOf`). The entangled majority
(spectral-object-consuming `hM` clauses, index-consuming `hcard`
clauses) classified; three concrete-pin-gated deferrals recorded.
Step 4 (the variational cluster) remains priced in the proposal's
census table.

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

**Adversarial fences (2026-09-04, proposal
`adversarial-fences-kernel-bridge-family.md`, `KernelBridge_QA.lean`'s
`BridgeFences` section):** the bridge family and its weighted center
characterization chain carry 12 hypothesis-form negative witnesses at
three fixtures the nonnegative QA fixtures could not serve — the Fin 2
negative edge (edgeless support) kills the center iff's ← direction
(reachability constancy junk-trivial while `L *ᵥ ![1,0] ≠ 0`), the
bridge's first orientation, and the dimension statement (`finrank 1 ≠
2`); the Fin 3 signed path with *connected* support (the negative edge
`(0,2)` is not a support edge) kills the iff's → direction at the
kernel vector `![1,2,3]`, the span and exists-const forms (with the
connectivity co-hypothesis genuine), the bridge's second orientation,
the dimension statement's second witness (`2 ≤ finrank ≠ 1`), and the
pos-weight engine's `hnonneg` at the mechanism level (`0 < A 0 1`
genuine, kernel equation genuine, `f 0 ≠ f 1`); and the Fin 3
asymmetric *nonnegative* sink star kills the pos-weight engine's `hA`
— the family's only `supportGraph`-free statement, whose `hA` is
proof-internal — with every other hypothesis genuine (`hnonneg`
entrywise): symmetry is load-bearing at the quadratic-form step. The
`hA` clauses of every `supportGraph`-carrying statement are recorded
non-fenceable (statement-entangled); the `hconn` clauses were already
fenced by `Connectivity_QA`'s disconnected witnesses.


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


The family's **adversarial fence audit** (2026-09-04, proposal
`adversarial-fences-electrical-flow-family.md`, QA-only): 22 fences +
19 isolation companions in `ElectricalFlow_QA.lean`'s
`AdversarialFences` section — the energy agreement's and the
routed-energy identity's `hA` at the asymmetric 4-path `asymPath4Adj`
(demand genuinely solvable, `flowEnergy = 1 ≠ 3/2 = quadForm`, the
resistance pinned by fixture-local voltage pinning); the
superposition lemma's `hd` (the cyclic phantom `cycleFlow`,
divergence-free on the cheat network's zero-conductance pairs) and
`hdiv` (the doubled current `doubleCurrent`); Thomson's `hnneg` (the
unit flow `negRouteFlow` riding both negative edges of the signed
4-cycle: energy `−1` against the junk resistance `0`); the flow-space
transfer and energy-comparison clauses (the phantom's negative
energies `1 ≤ −1`, `1 ≤ 0`); Rayleigh's `hnnegA` (the signed edge's
genuine negative resistance `−1`) and `hconnA` (the cheat network's
junk `0` under the dominating path); the support-graph and
connectivity-adapter clauses; and the reinforcement family's
`hδ`/`hA`/`hnneg`/`hconn` corners (the conductance-`1/2` edge
`halfEdgeAdj`; the reinforced cheat network computing to exactly the
path). Three P4 removable findings recorded in the proposal.

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

Adversarial fence audit (`proposals/adversarial-fences-foster-family.md`,
2026-09-04, `Foster_QA.lean`'s `FosterFences` section): negative
witnesses for the family's nine unfenced load-bearing clauses at the
prior day's delivered fixtures plus a one-vertex fixture. The
zero-eigenvalue count's `hnn`/`hconn` (two non-parallel kernel vectors —
`1` with `![1,1,-1,-1]` at the signed rank-1 4-cycle, `1` with the
component indicator at the disconnected fixture — force the count
`≥ 2 ≠ 1`, inverting the theorem's own at-most-one orthogonality
argument through the new generic kernel-onto-a-line engine); the
spectral kernel's `hnn`/`hconn` (the junk-fallback LHS `0` against a
*strictly positive* RHS — a genuine eigenvector with differing
coordinates confines its expansion to the nonzero modes, all terms
nonnegative; PSD at the signed fixture through the fixture-local rank-1
SOS identity `quadForm L f = (s ⬝ f)²`, which does not need
`laplacian_psd`'s nonnegativity hypothesis); `foster_theorem`'s `hnn`
(every off-diagonal demand unsolvable — the kernel-generator coordinate
map `x ↦ (w₁ x, w₂ x)` is injective on `Fin 4` — so the ordered sum is
`0 ≠ 3`) and `hconn` (the ordered sum `4 ≠ 2·3`, within-block
resistances genuinely pinned, no junk value entering); and the leverage
layer's `hcard` junk corner (the `0/0` division guard at `card V = 1`:
the score reads `0`, the sum `0 ≠ 2`) with its `hnn`/`hconn` mirrors.
The four `hA` clauses recorded non-fenceable (consumed by the displays'
`laplacian_symmetric A hA` or by `hconn`'s own `supportGraph A hA`).


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
**Adversarial fence audit + first positive pins (2026-09-07,
`proposals/adversarial-fences-tikhonov-family.md`):** the
compiler-derived consumption census's top named target — every theorem
above now has a genuine QA consumer (`tkp_*` pins in
`Tikhonov_QA.lean`'s `AdversarialFences` section; the pre-audit QA
re-derived minimality/uniqueness numerically beside the theorems), and
every load-bearing hypothesis clause is fenced (`tkf_*`: the
shrinkage-arithmetic five's `hπ`/`hlam`, the `π = 0` matrix guards,
the kernel-mode non-idempotence kill through the eigen theorem, the
signed-network PSD clause), with the pole-class deferrals priced in
the proposal.

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

**Adversarial fences** (2026-09-04,
`proposals/adversarial-fences-band-projector-family.md`,
`Band_QA.lean`'s `BandFences` section): 22 hypothesis-form negative
witnesses closing every load-bearing clause the pre-discipline QA left
unfenced — the negated junk band `B(4,0] = −1` kills idempotence
(`(−1)² ≠ −1`), both annihilation statements (`−v ≠ 0`), the
disjointness trio's `hab`/`hcd` plus the flipped twin's `hbc`, both
inner-orthogonality clauses, the residual-orthogonality engine
(`−2 ≠ 0`), the Hilbert identification (surjective `v ↦ −v` range:
projection `x ≠ −x`), and the closest-point bound (`‖2x‖ ≤ ‖x‖`
collapse); the mode-selection `h₂`, the covering `h`/`ha`/`hb`, the
monotone-family `ht`/`hkm`, and the vector-completeness `hb`/`hc` close
the rest. The shared-mode theorem's `hab`/`hcd` are recorded
non-fenceable: a negated band's fixed space is trivially zero, so the
dropped-guard statement is provable (the P4 truth-removable class).

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

**Adversarial fences** (2026-09-04,
`proposals/adversarial-fences-band-projector-family.md`,
`ClusterProjector_QA.lean`'s `ClusterFences` section): 7
hypothesis-form negative witnesses at `clusterA = diag(0,5,11)` —
mode-selection in both directions at `{0,11}`, the zero/one corners
via the delivered projector pins, identical-cluster disjointness
(`P² = P ≠ 0`), capture-iff against a covering `Ioc` selection, and
the band agreement's own docstring corner (`Ioc 6 (−1) = ∅` gives the
zero projector against the negated band `−diag(1,1,0) ≠ 0`).

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


The general-rank family (2026-08-31, proved, zero axioms — the operator-chosen
new-capability direction `proposals/spectral-positional-encoding-stability.md`;
both `k = 1` theorems above re-proved as one-line corollaries at unchanged
public statements, machine-checking that nothing in their proofs used `k = 1`
specifically):

| Declaration | Statement |
| --- | --- |
| `spectralEncodingSubspace_stability` | **(2026-08-31) general-rank Davis–Kahan subspace bound:** on every symmetric base `A` and perturbation `E` with cutoff index `k` (`k + 1 < card V`) and separation `δ ≤ λ_{k+2}(L(A+E)) − λ_{k+1}(L A)`, `‖initialProjector (L(A+E)) k − initialProjector (L A) k‖ ≤ ‖laplacian E‖/δ` — the bottom-`k+1` invariant subspace (the object a Laplacian positional encoding spans) moves by at most the Laplacian perturbation's norm over the gap; the proved `davis_kahan_sin_theta` is rank-general, so this is the re-parameterization of the `k = 1` wrapper (QA: the star `K₁,₃` → `K₄` instance at `k = ⟨2⟩` with the separation pinned independently and **the bound exactly attained**) |
| `spectralEncoding_stability` | **(2026-08-31) the kernel-isolated general-rank form:** on two *connected* graphs at the same separation, the residual `‖(P'_{k} − P'_{0}) − (P_{k} − P_{0})‖ ≤ ‖laplacian E‖/δ` — the informative (non-constant) `k`-dimensional component of the encoding, the common kernel projector cancelling exactly as at `k = 1`; the first machine-checked instance of the LapPE/SAN subspace-stability class (Dwivedi & Bresson; Kreuzer et al. as motivation; von Luxburg / Gama–Ribeiro / Levie et al. as the informal precedent), with the honest scope limits — subspace distance, not entrywise; both graphs connected; `δ` the caller's obligation — stated in the module docstring itself |

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

**Adversarial fence audit (2026-09-05,
`proposals/adversarial-fences-random-walk-family.md`):** the shelf is
the walk-mixing chain's root interface (5 transitive non-QA consumers
via `Stationary`); the `AdversarialFences` section of
`RandomWalk_QA.lean` carries six hypothesis-form fences covering every
hypothesis clause of the theorem surface — both `hA` symmetry clauses
at the asymmetric `!![0,2;1,0]]` (with the `d = 0` junk-rescue corner
pinned: `0⁻¹ = 0` symmetrizes every matrix), both `hd` regularity
clauses at the delivered `edgeAdj` at the wrong claimed degree `d = 2`
(no junk anywhere), and both `hdpos` clauses at the genuinely
`0`-regular zero matrix (the junk `0⁻¹ = 0` corner where the
transition matrix collapses to zero). The recorded structural finding:
`hdpos` is load-bearing *only* through that corner — the proved
strengthening companions `_of_ne_zero` show `d ≠ 0` (negative degrees
included) suffices, so fence+strengthening is an exact characterization.
The hypothesis-free `rfl` bridge is non-fenceable by inspection. QA-only,
zero axioms.

See the [SGT backlog](../../docs/6_SGT_BACKLOG.md) for the irregular-graph
adapter plan.

### `Scaffold.Mathlib.GraphTheory.Normalized` (general normalized Laplacian)

Real definitions: `degreeSqrt`, `degreeInvSqrt` (diagonal `√D`, `1/√D`
via `Real.sqrt` — no matrix square root needed), `normalizedLaplacian`
(`1 - (1/√D) A (1/√D)`, the irregular symmetric normalized Laplacian).
**Adversarial fence audit (2026-09-04,
`proposals/adversarial-fences-normalized-family.md`):** the shelf is the
library's most-consumed unaudited surface (20 transitive non-QA
consumers); the `AdversarialFences` section of `Normalized_QA.lean`
carries 27 hypothesis-form fences with packaged isolation companions
covering every load-bearing clause of the theorem surface. The recorded
headline: at *symmetric zero-degree* fixtures the dropped-`hd`
statements of the congruence bridge, left-multiplied congruence,
commutation form, and conjugated-power transfer are *provable* (the
junk kills both sides identically) — the genuine breaker is the
negative-degree row, where `(deg)⁻¹` stays genuine while the
square-root factors vanish; the single Fin 2 fixture `!![-2,1;1,0]]`
(`L_sym` degenerates to the identity, `P = !![2,−1;1,0]]`, all
rational) kills fifteen clauses including the transfer trio at genuine
eigen-hypotheses, the eigenbasis instantiations (orthonormality-witness
index — no eigenvalue pin), and the transferred-spectrum existential
(dead by the pinned `P` row equations through `evals_congr` +
`evals_one`). QA-only, zero axioms.
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

**Adversarial fence audit (2026-09-05,
`proposals/adversarial-fences-stationary-family.md`):** the shelf is
the stationarity/reversibility root every walk-mixing consumer starts
from (4 transitive non-QA consumers); the `AdversarialFences` section
of `Stationary_QA.lean` carries thirteen hypothesis-form fences
covering every priceable clause of the theorem surface — the six `hA`
clauses at the delivered asymmetric `asymAdj2` (kill mechanism:
`Pᵀ *ᵥ deg` computes column sums against the row-sum degree vector;
the degree-measure fence consumes the delivered free-form witness,
reconciling it into the discipline), the degree-measure `hd` clauses
at the new signed canceling-zero-degree triangle (junk-√ collapse for
the kernel; junk-`0⁻¹` column-zeroing for stationarity and balance —
nonnegative zero-degree rows are inert, signs make them load-bearing),
the stationary-measure/symmetrized `hd` twins at a volume-nonzero
variant (vol `0` would junk-collapse both sides of the division), and
the mass-conservation `hd`/`hdpos` pair at the wrong claimed degree
and the `d = 0` corner. Five proved strengthening companions record
the structural findings: the kernel statement's `hA` is P4
truth-removable (the shelf proof never consumes symmetry), and the
positivity clauses are secretly nonzeroness clauses (`deg ≠ 0`/`d ≠ 0`
suffice by the shelf proofs' own routes). QA-only, zero axioms.

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
| `tvDistance` | **the total-variation distance** in its finite-state vector form `(1/2) ∑ i, \|μ i − ν i\|` — the mixing program's deferred Step 4 (2026-08-31, `proposals/total-variation-mixing-conversion.md`), scoped vector-valued: no `MeasureTheory` anywhere, and for probability vectors this `L¹` form *is* the classical finite-state TV |
| `tvDistance_triangle` | the triangle inequality — the only structural fact the two-start TV twin needs |
| `tvDistance_le_half_sqrt` | **the ℓ² → TV conversion:** for a positive weight `w` of total mass one and *any* vector `ν` (sign-free), `TV ≤ (1/2)·√(∑ (ν − w)²/w)` — the classical Cauchy–Schwarz step at its sharp constant (attained exactly on `K₂`), mass-one hypothesis load-bearing (fenced in QA) |
| `walkDistribution_tvDistance_le` | the unconditional walk-level shadow: `TV(ν_t x, π) ≤ (1/2)·√χ²(t, x)` for every walk — no connectivity, no rate |
| `walkDistribution_tvDistance_le_of_connected` | **the rate form:** `TV(ν_t x, π) ≤ (1/2)·√(r^{2t} · ((π x)⁻¹ − 1))` at exactly the χ² theorem's hypothesis set — the closing mixing bound restated in the field-standard distance |
| `sum_vecMul_eq_of_row_sum` | **mass preservation** under a row-stochastic row action (the Doeblin TV section, 2026-09-02, `proposals/doeblintv-tv-contraction-pagerank-rate.md`) |
| `abs_dotProduct_le_half_entryRange_mul_sum_abs` | **zero-sum interval pinning:** a zero-mass functional pairs with any function to at most half its entrywise range times the `ℓ¹` mass — the dual step behind the Doeblin TV contraction |
| `tvDistance_vecMul_le` | **row-action TV non-expansiveness** at the generic-matrix level — the adjoint-walk `mulVec` contraction's row-action twin |
| `tvDistance_vecMul_le_of_pos_entries` | **the Doeblin TV contraction:** `TV(μ ᵥ* Q, ν ᵥ* Q) ≤ (1 − \|V\|δ)·TV(μ, ν)` for row-stochastic `Q` with entries `≥ δ` at equal masses — hypothesis-minimal (sign-free on both vectors), the entrywise-range engine's second consumer through the dual/test-function pairing `z ⬝ᵥ s = w ⬝ᵥ (Q *ᵥ s)`; the directed axis' first TV statement |
| `tvDistance_vecMul_pow_le_of_pos_entries` | the block-iterated contraction at `(1 − \|V\|δ)^q` |
| `tvDistance_vecMul_pow_le_of_pos_power` | **the Doeblin mixing bound:** with `P^m` entrywise `≥ δ`, `TV(ν ᵥ* P^t, π) ≤ (1 − \|V\|δ)^(t/m)·TV(ν, π)` for any mass-one start against any mass-one stationary `π` — the rate clause the retired convergence theorem did not carry, at its proof's own byproduct rate |
| `abs_sub_le_tvDistance` | **the equal-mass entrywise TV extraction** (2026-09-02, `proposals/directed-mixing-time-object.md`): `\|μ i − ν i\| ≤ TV(μ, ν)` at equal masses, by the zero-mass triangle route (the complement's deviation mass is exactly `−d i`); the constant sharp — the directed bias term's engine, since the directed program bounds TV, not χ² |
| `tvDistance_le_sqrt_half_klDiv` | **Pinsker's inequality (2026-09-01, `proposals/entropy-mixing-pinsker.md`):** `tvDistance p q ≤ √(klDiv p q / 2)` for a probability vector against a strictly positive one — TV-as-positive-part at `S = {q < p}` (`TV = a − b`), the two-block decomposition of `klDiv` through the two-block log-sum, and the binary two-point bound; the strict q-positivity load-bearing (refuted at the q-zero junk corner in QA) |
| `walkDensity_nonneg` / `contWalkDensity_nonneg` / `contWalkDistribution_nonneg` / `sum_contWalkDistribution` | the entropy leg's nonnegativity plumbing: the discrete density's entrywise nonnegativity; the continuous density's by the Poissonization identity + `tsum_nonneg` (the identity's first nonnegativity consumer); the continuous law's; and the continuous law's mass conservation packaged |
| `klDiv_walkDistribution_le` | **entropy decay, discrete:** `D(ν_t ‖ π) ≤ r^{2t}·((πx)⁻¹ − 1)` at exactly `chiSquareDistance_le_of_connected`'s hypothesis set — the entropy–χ² bridge composed with the delivered χ² theorem |
| `klDiv_contWalkDistribution_le` | **entropy decay, continuous-time twin:** `D ≤ e^{−2tλ₂(L_sym)}·((πx)⁻¹ − 1)` at `contChiSquareDistance_le`'s hypothesis set — the intrinsic-rate entropy bound, no caller certificate |


### `Scaffold.Mathlib.GraphTheory.Oversmoothing` (the certified oversmoothing ceiling, the `t_mix` objects, and the submultiplicativity class)

All statements proved (2026-08-31,
`proposals/message-passing-depth-mixing-bound.md`), no axioms — the
depth-form consumers of `chiSquareDistance_le_of_connected`: the bound
decreases in `t`, so it certifies convergence, and the depth statement
it supports is an **oversmoothing ceiling** (guaranteed representation
collapse past a computable depth), the corrected direction of the
proposal's original (retracted) over-squashing floor. Honest scope in
the module docstring: the linearized mean-aggregation propagation
operator (a linear GCN-style layer up to weights/nonlinearity), a
single global rate, and no reach at all on graphs admitting no
`r < 1` certificate (bipartite graphs). The discrete mixing-time
section (2026-09-01, `proposals/total-variation-mixing-conversion.md`'s
deferred `t_mix` object, consumer gate discharged by the Poisson
bridge) is also proved, zero axioms — see the table's last rows. The
spectral-floor section (2026-09-01, the message-passing proposal's
deferred over-squashing item delivered on its own named route — the
program's first lower-bound family) is proved as well, zero axioms.

| Declaration | Content |
|-------------|---------|
| `stationaryVec_le_one` | `π x ≤ 1` entrywise (positive masses summing to one) — what makes the ceiling constant real |
| `walkDistribution_sub_stationaryVec_abs_le` | **the entrywise extraction:** `|ν_t x y − π y| ≤ r^t · √(π y · ((π x)⁻¹ − 1))` — one χ² summand bounded by the whole sum (`Finset.single_le_sum`), root-flipped; the mixing bound's normalization enters the constant unchanged |
| `pow_mul_le_of_log_threshold` | **the log-threshold calculus bridge:** `log (C/ε)/log (1/r) ≤ t` with `0 < r < 1` ⟹ `r^t · C ≤ ε` (the sign of `log` is the proposal's corrected step; `C = 0` trivial) |
| `walkDistribution_sub_stationaryVec_le_of_depth` | **the oversmoothing ceiling:** past the computed depth, the `t`-step walk law from any start is within `ε` of stationarity at every target vertex — the architecture-design ceiling |
| `walkDistribution_sub_walkDistribution_le_of_depth` | **two-start indistinguishability:** past the depth, any two starts' `t`-step views are within `2ε` at every vertex — the informal oversmoothing statement made formal |
| `walkDistribution_eq_sum_eigbasis` | **the entrywise eigenbasis expansion of the walk law** on any `d`-regular graph: `ν_t x y = ∑_k (1 − λ_k/d)^t u_k x u_k y` over the combinatorial Laplacian's orthonormal basis — the per-pair refinement's engine |
| `walkDistribution_pair_contrast_abs_le` | **the per-pair resistance contrast bound:** on a connected `d`-regular graph, the four-point contrast of the walk law is bounded by the certified mode-rate `ρ` times `√R(x₁,x₂)·√R(y,y')` — Foster's spectral resistance formula joined through Cauchy–Schwarz; the first bridge between the electrical and mixing axes |
| `walkDistribution_pair_contrast_abs_le'` | the packaged corollary at the walk family's `\|1 − λ_k/d\| ≤ r` certificate shape — the explicit mode-rate `2 d r^t` (via the `λ ≤ 2d` engine `laplacian_quadForm_le_two_mul`/`eigvalOf_laplacian_le_two_mul`) |
| `oversmoothing_log_threshold_mono` | **rate monotonicity:** a looser certified rate buys a provably larger threshold — the ceiling tracks the certified spectral gap (the QA sanity-contrast engine) |
| `walkDistribution_tvDistance_le_of_rate` | **the TV twin, split-constant rate form:** `TV(ν_t x, π) ≤ (1/2)·r^t·√C` with `C = (π x)⁻¹ − 1 ≥ 0` (`stationaryVec_le_one` supplying the nonnegativity) — the shape the depth threshold consumes |
| `walkDistribution_tvDistance_le_of_depth` | **the TV ceiling:** past the threshold `log (√C/(2ε))/log (1/r)` (the entrywise ceiling's own at `2ε`), the walk law is within `ε` of stationarity *in total variation* — the field-standard `t_mix(ε)` statement form, now expressible on the shelf |
| `walkDistribution_tvDistance_sub_le_of_depth` | **two-start indistinguishability in TV:** past both starts' thresholds, the two `t`-step laws are within `2ε` of each other in total variation (triangle + symmetry) |
| `walkMixingTimeFrom` | **the discrete mixing time** `t_mix(ε)` — the least number of steps from which the walk law stays within `ε` of stationarity in TV (LPW ch. 20's per-start reading, the discrete twin of `contMixingTimeFrom`; delivered 2026-09-01, `proposals/total-variation-mixing-conversion.md`'s deferred object, consumer gate discharged by the Poisson bridge) |
| `walkMixingTimeFrom_bddBelow` / `walkMixingTimeFrom_le_of_cert` | the witness-set boundedness and the certificate interface: any witness time certifies the mixing time (`t_mix(ε) ≤ T`) |
| `walkMixingTimeFrom_spec` | **the attainment specification** — the discrete object's own advantage: `ℕ` is well-ordered, so the witness infimum is a *member* (`csInf_mem`) and membership is the uniform bound — this discharges the Poisson-bridge transfer corollary's `hmix` clause, closing the recorded consumer loop |
| `walkMixingTimeFrom_le_of_connected` | **the spectral ceiling** `t_mix(ε) ≤ ⌈log(√C/(2ε))/log(1/r)⌉` at the depth-form TV certificate's own hypothesis set (`0 < r < 1` — honest: periodic chains admit no such certificate; big-`ε` absorbed by `⌈·⌉ = 0`) |
| `walkMixingTimeFrom_anti` | ε-antitonicity (`ε ≤ δ → t_mix(δ) ≤ t_mix(ε)` under a witness), the continuous twin's `csInf_le_csInf` mirror |
| `contWalkDistribution_tvDistance_le_of_walkMixingTime` | **the bridge composition** — the named consumer: a Poisson lower-tail bound below `t_mix(ε₁)` gives `TV_cont(t) ≤ ε₁ + ε₂`, the discrete certificate supplied by the object itself |
| `tvDistance_ge_half_abs_sum` (Mixing) | **the distinguishing-function bound** `|(μ−ν)(f)| ≤ 2·TV(μ,ν)` for `‖f‖∞ ≤ 1`, hypothesis-minimal — no sign or mass assumptions; the standard route around the Cauchy–Schwarz conversion's missing reverse, and the engine of every total-variation *floor* |
| `degreeSqrt_onesVec_dotProduct_of_eigenpair` / `stationaryVec_dotProduct_degreeInvSqrt_of_eigenpair` | **kernel orthogonality of nonzero modes, derived** (not assumed): `μ ≠ 0` forces `⟨√D·1, v⟩ = 0` through symmetry and `L_sym(√D·1) = 0` — no connectivity; the conjugated eigenvector is π-mean-zero |
| `walkDistribution_dotProduct_degreeInvSqrt_of_eigenpair` | **the exact law-level test-function evolution** (the deferred over-squashing item's own engine): pairing the walk law against `(1/√D)•v` at *any* genuine `L_sym` eigenpair evolves exactly geometrically at `1 − μ` — an equality, not a bound, no `eigvecOf` indexing |
| `walkDistribution_tvDistance_ge_of_eigenpair` | **the TV spectral floor** `(1/2)·\|1−μ\|^t·\|v x\|/(√D x·c) ≤ TV(ν_t, π)` at a caller-certified sup bound `c` — no connectivity, no aperiodicity: periodic `\|1−μ\| = 1` modes never decay, exactly the chains no `r < 1` ceiling reaches (QA: attained exactly on `K₂` at every time) |
| `chiSquareDistance_ge_of_eigenpair` | **the χ² spectral floor** `(1−μ)^{2t}·(v x)²/(π x·‖v‖²) ≤ χ²(t,x)` — the √D-conjugated initial centered density pairs with `v` in coordinate exactly `vol/√D x·v x`, and Cauchy–Schwarz extracts that mode's slice of the Parseval identity (QA: attained exactly at every time on both `K₂` and the triangle) |
| `walkMixingTimeFrom_gt_of_tv_gt` | **the `t_mix` floor gate**: a witness at `ε` plus `ε < TV_t` gives `t < t_mix(ε,x)` — the witness-existence hypothesis load-bearing exactly at the periodic junk corner (fenced in QA) |
| `pow_lt_of_lt_log_div` | **the strict log-threshold calculus bridge, floor direction** — the downward twin of `pow_mul_le_of_log_threshold`: `t < log b/log r` (negative denominator — the sign of `log` is the trap here too) gives `b < r^t` |
| `walkMixingTimeFrom_ge_of_eigenpair` | **the log-form spectral floor** `⌈log(\|v x\|/(√D x·2εc))/log(1/\|1−μ\|)⌉ ≤ t_mix(ε,x)` under `0 < \|1−μ\| < 1` and a witness at `ε` (certified from above, e.g. by the ceiling) — the classical eigenvalue lower bound on mixing time, the delivered ceiling's textbook companion; QA hits all three pinned triangle `t_mix` closed forms exactly, completing the two-sided depth bracket |
| `walkTVPair` / `walkTVUniform` | **LPW's two distances** — the two-start distance `d(t) = max_{x,y} TV(ν_t^x, ν_t^y)` and the worst-start distance `d̄(t) = max_x TV(ν_t^x, π)` (Montenegro–Tetali's, the one whose threshold curve *is* the mixing time), `Finset.sup'` maxima on a finite type, with nonnegativity (delivered 2026-09-01, `proposals/total-variation-mixing-conversion.md`'s deferred uniform-`t_mix` family) |
| `tvDistance_pow_walkTransitionMatrixTranspose_mulVec_le` | **the sharp Dobrushin contraction** `TV(μ(Pᵀ)ᵗ, ν(Pᵀ)ᵗ) ≤ TV(μ,ν)·d(t)` at equal masses — hypothesis-minimal (no stochasticity, no signs): the sign statistic of the evolved difference paired through the recentering-pairing core against the delivered distinguishing-function bound, avoiding the factor-`2`-losing naive triangle route (QA: the submultiplicativity equalities it powers are attained with *equality* on the triangle) |
| `walkTVPair_submul` | **submultiplicativity of the two-start distance** — LPW's classical `d(s+t) ≤ d(s)·d(t)`: the Dobrushin contraction at the pair of `s`-step laws, equal masses by walk conservation; pure Markovity, no connectivity, no rates |
| `stationaryVec_eq_sum_smul_walkDistribution` / `walkTVUniform_le_walkTVPair` | the stationary mixture identity (`π` as the π-weighted mixture of the `t`-step laws) and **`d̄(t) ≤ d(t)`** — the TV-convexity-in-mixtures route, `d̄` vs `d` needing no reversibility |
| `walkTVUniform_mul_walkTVPair_le` / `walkTVUniform_succ_mul_le` | **the mixed submultiplicativity** `d̄(s+t) ≤ d̄(s)·d(t)` and its iteration **the escalation engine** `d̄((k+1)t₀) ≤ d̄(t₀)·d(t₀)^k` — the certificate-free geometric decay powering the ε-escalation corollary |
| `walkMixingTime` | **the uniform mixing time** — LPW ch. 20's field-standard worst-case-start `t_mix(ε)`: the least time from which *every* start's law stays within `ε` of stationarity in TV; on a finite type it is the worst start's per-start object (`walkMixingTime_eq_sup_walkMixingTimeFrom`, the sup-inf interchange), with the `bddBelow`/`_le_of_cert`/`_spec` certificate-and-attainment interface mirroring the per-start object's |
| `walkMixingTimeFrom_le_walkMixingTime` | per-start times are dominated by the uniform time *given a uniform witness* — the witness hypothesis load-bearing (at the junk corner the un-witnessed statement is false; fenced in QA) |
| `walkMixingTime_le_mul_of_escalation` / `walkMixingTime_le_of_escalation` | **the ε-escalation corollary** — the class's consumer capstone: one evaluation time `t₀` with `d̄(t₀) ≤ ε₀` and `d(t₀) ≤ ρ < 1` yields *every* ε-level mixing time (`t_mix(ε) ≤ (k+1)t₀` at `ε₀·ρᵏ ≤ ε`), LPW's canonical `t_mix := t_mix(1/4)` bridge, in both the `k`-form and the ⌈log⌉ display form |
| `walkMixingTime_le_of_connected` | **the uniform spectral ceiling** — the per-start ceiling's uniform form: under the depth-form TV certificate's own hypothesis set with start constants uniformly bounded by `C`, every start mixes within `⌈log(√C/(2ε))/log(1/r)⌉` steps |

Supporting additions elsewhere: `Spectral.eigvecOf_dotProduct_one_sub_mulVec`
(the generic eigenaction at `1 − M`, composed from
`dotProduct_eigvecOf_mulVec`) and in `Normalized`
`degreeSqrt_mul_walkTransitionMatrix_eq` (`√D · P = (1 − L_sym) · √D`)
with `degreeSqrt_mulVec_pow_walkTransitionMatrix` (the conjugated-power
transfer — `√D *ᵥ (Pᵗ *ᵥ g) = (1 − L_sym)ᵗ *ᵥ (√D *ᵥ g)`), plus the
χ²-assembly entry lemmas `walkTransitionMatrix_mulVec_one`
(the constant fix `P *ᵥ 1 = 1`), `degreeSqrt_mulVec_apply`, and
`degreeInvSqrt_mulVec_apply` (the conjugating actions' entry forms).
| `klDiv_walkDistribution_ge_of_eigenpair` | **the entropy floor (2026-09-01, `proposals/entropy-mixing-pinsker.md`):** `2·((1/2)·\|1−μ\|^t·\|(√D⁻¹ v) x\|/c)² ≤ D(ν_t ‖ π)` at the spectral TV floor's exact hypothesis set — Pinsker composed with `walkDistribution_tvDistance_ge_of_eigenpair`, the floor family's first non-TV member (periodic modes pin entropy bounded away from zero forever; `D = log 2` on `K₂` exactly, pinned in QA) |


### `Scaffold.Mathlib.GraphTheory.Poincare` (the Poincaré inequality family)

All statements proved (2026-08-31,
`proposals/poincare-inequality.md`), no axioms — the functional
inequality the variational axis's charter names beside Courant–Fischer:
variance controlled by Dirichlet energy at the spectral gap, in both
the combinatorial and the degree-weighted (π-measure) forms, plus the
cut-level consumer. Consumers: the mixing program's ℓ²(π) contraction
(Poincaré in walk form), the heat family's priced variance-decay
follow-on, and `Multiway.lean`'s indicator energy identity (its first
consumer outside its own module).

| Declaration | Content |
|-------------|---------|
| `quadForm_laplacian_sub_const` | centering invariance of the energy: `quadForm L (f − c • 1) = quadForm L f` (the ones kernel) |
| `poincare_variance_mul_le` | **the division-free engine form:** `λ₂(L) · ∑ (f i − mean f)² ≤ fᵀLf` with *no* λ₂ positivity hypothesis (vacuous at `λ₂ = 0`; the QA no-constant fence proves the division form's guard is exactly the true region's boundary) |
| `poincare_inequality` | **the combinatorial Poincaré inequality** `∑ (f i − mean f)² ≤ fᵀLf / λ₂(L)` at `0 < λ₂`, from `secondEval_le_rayleigh` at the centered vector |
| `poincare_inequality_of_connected` | the connected twin (gap from `lambda2_pos_of_connected`) |
| `poincare_inequality_normalized` | **the π-form:** `∑ deg i · (f i − E_π f)² ≤ fᵀLf / λ₂(L_sym)` — from `secondEval_le_rayleigh_of_ker` at `√D (f − E_π f · 1)` (orthogonal to `√D · 1` by mass conservation), energy through the congruence `√D L_sym √D = L`; the denominator is `L_sym`'s own eigenvalue (not scalar-related to the combinatorial one on irregular graphs) |
| `poincare_inequality_normalized_of_connected` | the connected twin (gap from the delivered connectivity transfer) |
| `spectral_gap_edge_expansion` | **spectral edge expansion:** `λ₂(L) · \|S\| · (\|V\| − \|S\|)/\|V\| ≤ boundary A S` for every vertex set — linear in the gap, set-by-set, no sweep/median/regularity; the indicator's variance collapse joined to `quadForm_laplacian_partIndicator` |

Supporting QA: `Scaffold/QA/SpectralGraph/Poincare_QA.lean` (the
exact-attainment pins on K₂/P₃/K₃ Fiedler vectors, the wrong-constant
refutation, the no-constant connectivity fence on the disconnected
two-edge fixture, and both edge-expansion instances attained with
equality).

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

**Adversarial fence audit complete (2026-09-05,
`proposals/adversarial-fences-directed-family.md`):** the shelf's
entire clause surface — four one-clause theorems — carries per-clause
hypothesis-form fences in `Directed_QA.lean`'s `AdversarialFences`
section. The three `hA : A.IsSymm` cone clauses fall at the delivered
`dirA` (the first two reconciling the pre-existing free-form
witnesses into fence form); the conjugate's
`hd : ∀ i, 0 < deg A i` falls at the new zero-out-degree fixture
`dzA = !![0, 1; 0, 0]]`, where the junk `√0 * (√0)⁻¹ = 0` collapse
erases the symmetrized arc from the conjugate's left side while the
right side's `D − ½(A + Aᵀ)` keeps it (`0 ≠ −(1/2)`). The audit's
headline finding: **`hd` is genuinely a positivity clause, not
nonzeroness in disguise** — unlike the random-walk family's `hdpos`
(where `d⁻¹ * d = 1` holds for every `d ≠ 0`), the `Real.sqrt` route
collapses the whole non-positive half-line, so the
nonzeroness-*strengthened* statement is itself refuted at the new
negative-degree fixture `dzNeg = !![-1, 0; 1, 0]]` (out-degrees
`(−1, 1)`, every kept clause of the strengthening genuine).

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
Steps 0+1 in one run). **Hard crust since 2026-09-02**
(`proposals/cesaro-stationary-existence.md`): the five
stationary-distribution theorems were re-proved without the axiom by
the elementary Cesàro route — power positivity from strong
connectivity, existence by Krylov–Bogoliubov averaging of the orbit of
`1` over the compact simplex (Tychonoff + subsequential cluster point,
the telescoping action-defect `t⁻¹(1 − 1 ᵥ* P^t)` vanishing
entrywise), strict positivity, and min-ratio uniqueness-up-to-scale —
`#print axioms` exactly the standard three across the whole layer.
The two transfer lemmas were always unconditional. QA at
`Scaffold/QA/SpectralGraph/IrreducibleStationary_QA.lean` (the
asymmetric directed star with the hand value identified through the
`∃!`, the symmetric-cone `K₂` agreement with `stationaryVec` through
the shelf's detailed-balance chain, the reducibility fence refuting
the hypothesis-free `∃!` and
scale-uniqueness conclusions, and the Section E engine-mechanism pins —
orbit/oscillation values, the one-period Cesàro mean exactly
stationary, power-positivity instances, the engine output identified,
the min-ratio scalar, reducible-input existence). The shelf's
**adversarial fence audit** (2026-09-05,
`proposals/adversarial-fences-irreducible-stationary-family.md`, the
audit method's twenty-first application — its 706-line QA had carried
only the two hypothesis-free refutations above, never reconciled into
the per-clause discipline): thirty-two hypothesis-form fences plus
three strengthening declarations in the QA file's `AdversarialFences`
section, all 256 declarations at the standard three axioms — headline
mechanisms: the Krylov–Bogoliubov `hgnn` killed by the Jordan-block
orbit-escape fixture `!![0,1;-1,2]]` (the mass-constant orbit
`![2-s, s-1]` escapes exactly where the telescoping defect bound
needed nonnegativity), the `hnn` clauses by three complementary signed
Fin 3 fixtures (mixed-sign fixed space / two-dimensional wedge /
signed-cancellation vanishing support), `exists_pow_pos`'s `hnn` by
the rank-one `M² = 8•M` power-sign fixture, and the `hdeg`/`hex`
clauses proved truth-removable (`deg_pos_of_nonneg_irreducible`:
`hnn + hirr + hex ⟹ hdeg`; `exists_pos_entry_of_deg_pos`: one
positive row sum suffices) with `exists_walkPerronVector_of_hex`
restating existence at the strictly weaker hypothesis set.

| Declaration | Content |
|-------------|---------|
| `isIrreducible_transpose` | strong connectivity is arc-reversal invariant: `M.IsIrreducible → Mᵀ.IsIrreducible` (unconditional; the private `ReflTransGen` flip induction behind it) |
| `walkTransitionMatrix_isIrreducible` | positive row scaling preserves the support digraph: `A.IsIrreducible` + positive out-degrees → the walk matrix irreducible (unconditional; the private `ReflTransGen` congruence — the pin has `mono` for `ReflGen` only) |
| `vecMul_mul` | vector-matrix-matrix associativity in `vecMul` form — the `ᵥ*`-shaped associate of `Matrix.mulVec_mulVec`, absent from the pinned Mathlib (new 2026-09-02) |
| `vecMul_entry` | the entry form of the row action (new 2026-09-02) |
| `sum_vecMul_eq_of_row_sum` | mass preservation under a row-stochastic action (new 2026-09-02) |
| `vecMul_sum` | the row action commutes with finite sums of vectors (new 2026-09-02) |
| `pow_row_sum` / `pow_entry_nonneg` / `pow_entry_le_one` | powers of a nonnegative row-stochastic matrix keep row sums `1` and entries in `[0, 1]` (new 2026-09-02) |
| `exists_pow_pos_of_isIrreducible` | **power positivity**: for a nonnegative irreducible matrix every index pair is joined by a power with a strictly positive entry — the `ReflTransGen` induction along the arcs (new 2026-09-02) |
| `exists_cluster_stationary_of_orbit` | **the Krylov–Bogoliubov cluster lemma** (finite form): for any action and any nonnegative fixed-mass orbit, some cluster point of the Cesàro means is stationary of the same mass — compactness + the telescoping defect `t⁻¹(g 0 − g t) → 0` (new 2026-09-02) |
| `exists_nonneg_stationary_of_row_stochastic` | **existence for any nonnegative row-stochastic matrix** — no irreducibility: the Cesàro means of the orbit of `1` supply the stationary vector (mass `\|V\|`) (new 2026-09-02) |
| `exists_walkPerronVector` | **the transposed stationary engine** (hard crust since 2026-09-02): a strictly positive vector fixed by `Pᵀ *ᵥ ·`, unique up to positive scalars among nonzero nonnegative fixed vectors |
| `exists_stationaryVec_of_irreducible` | **existence with full support** (hard crust since 2026-09-02): a strictly positive, mass-one stationary distribution `π ᵥ* P = π` for every irreducible nonnegative walk — the directed-axis statement the undirected shelf cannot reach |
| `stationaryVec_smul_of_irreducible` | **uniqueness up to positive scale** (hard crust since 2026-09-02) among all nonzero nonnegative stationary vectors, the scale-free form |
| `existsUnique_stationaryVec_of_irreducible` | **the textbook `∃!`** (hard crust since 2026-09-02): exactly one nonnegative mass-one vector fixed by the walk, positivity derived rather than hypothesized |
| `stationaryVec_pos_of_irreducible` | **full support** (hard crust since 2026-09-02): every nonzero nonnegative stationary vector is strictly positive — no stationary distribution of an irreducible chain can vanish anywhere |

### `Scaffold.Mathlib.GraphTheory.PageRank` (the teleportation-regularized walk — the second Perron–Frobenius consumer)

The Google matrix `G i j = α * P i j + (1 - α) * (card V)⁻¹` (delivered
2026-08-24, `proposals/pagerank-distributions.md`, Steps 0+1 in one
run). The construction's content is the **teleportation floor**: every
entry positive on the damping window `[0, 1)`, so irreducibility is
*derived* rather than assumed and the delivered
`IrreducibleStationary` layer composes at `G` through the general
row-stochasticity bridge — extending the stationary theory to
**reducible** input with no irreducibility hypothesis in any
statement. The three PageRank theorems are **hard crust since
2026-09-02** (the `IrreducibleStationary` layer they compose was
re-proved that day, `proposals/cesaro-stationary-existence.md`); the
nine structural declarations are unconditional. QA at
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
| `exists_pageRankVec` | **existence** (hard crust since 2026-09-02): a strictly positive, mass-one `π ᵥ* G = π` for every nonnegative positive-degree network — reducible or not |
| `existsUnique_pageRankVec` | **the `∃!`** (hard crust since 2026-09-02): exactly one nonnegative stationary distribution of the Google walk, **no irreducibility hypothesis on the input** — the statement the raw walk cannot support on reducible input |
| `pageRankVec_pos` | **full support** (hard crust since 2026-09-02): every nonzero nonnegative vector fixed by `G` is strictly positive — even a vertex with no inbound walk arcs receives teleportation mass |
**The spectral ceiling (2026-09-06, `proposals/sharp-second-eigenvalue-layer.md`,
Slice 1):** `PageRank.lean`'s `SpectralCeiling` section — the mass
lemma, the shadow lemma (G's off-one left-eigenvectors ARE P's
mass-zero left-eigenvectors), the ℓ¹ peripheral bound,
Haveliwala–Kamvar's inequality half `|c| ≤ α`, and the attainment
twin; QA pins the `-α`-eigenpair attained at the two-cycle fixture
and the end-mix `0`-pair. Slice 2 (a) (same day): the Dobrushin
shadow in `DirectedMixing.lean`'s `DobrushinShadow` section — the
exact pointwise TV scaling, the shadow and walk Dobrushin ceilings,
and the pair rate at the sharper constant `(α·δ(P))^t`. Slice 3 (a): the exact shadow
equality `δ(G) = α·δ(P)` and the exact `t = 1` identity, via the
sup'-induction attainment route. Slice 4: the eigenvalue-level forms —
the ceilings, shadow, and twin in `Module.End.HasEigenvector`/
`HasEigenvalue` through the definitional `vecMulLinear` bridge.
Slice 5 (same day, the proposal COMPLETE): the strictness layer in
`PageRank.lean`'s `Strictness` section — `vecMul_pow_smul_eq` (the
power-eigenpair engine), `vecMul_sign_coherent_of_abs_eq_pow_pos`
(the peripheral sign-rigidity engine: equality in the ℓ¹ contraction
at a strictly positive power forces a common sign — no
Perron–Frobenius), `googleMatrix_abs_eigen_lt_of_primitive` (on an
aperiodic chain every off-one Google left-eigenvalue is STRICTLY
inside the α-disk, `|c| < α`), its `_of_pow_pos` form, and the
eigen-level twin `googleMatrix_hasEigenvalue_abs_lt_of_primitive`;
QA pins strictness at the primitive two-vertex fixture (self-loop +
arc, `P² > 0`, the `-α/2` eigenpair) and fences the necessity — the
periodic two-cycle where the ceiling is attained provably fails
primitivity. The follow-on right-eigenvector forms (same day,
`proposals/right-eigenvector-sharp-layer.md`): the general
left/right spectrum bridge
`hasEigenvalue_mulVecLin_iff_vecMulLinear` (a square matrix's left
and right eigenvalue sets coincide, any field — kernel-level
`det Mᵀ = det M`, no charpoly) with its two raw-pair↔determinant
factoring lemmas, and on it the ceiling and strictness at the
right (`mulVecLin`) convention, eigen-level and raw — QA's two
boundary witnesses recording why (the right eigenvector's nonzero
mass; the no-right-shadow witness). The doubly-stochastic follow-on
(same day, same proposal): on column-stochastic walks the right mass
lemma, right shadow, and right twin all hold — transported at
`A := Pᵀ` through `googleMatrix Pᵀ α = Gᵀ` — with QA at the
non-symmetric doubly-stochastic `Fin 3` cyclic chain. The
characterization iff (the layer's item 3) closes the family's open
statement: `googleMatrix_abs_eigen_eq_alpha_iff` — the ceiling
attained ⟺ a mass-zero peripheral walk eigenpair — plus its
doubly-stochastic right twin. The family's adversarial fence audit
(same day, `proposals/adversarial-fences-sharp-layer-family.md`):
22 hypothesis-form fences — every unfenced load-bearing clause
closed, with the two-cycle `G(−1) = I` vacuity finding. The
literal-`λ₂` sorted-spectrum forms (same day, another follow-on in
`proposals/sharp-second-eigenvalue-layer.md`): on regular input the
top eval exactly `1` (the `1`-eigenspace simplicity — teleportation
strict positivity + sign-rigidity + min-ratio), `evals ⟨n−2⟩ ≤ α`,
`-α ≤ evals ⟨0⟩`; QA the two-cycle's bottom `−α` attained. Its own
priced follow-up (the fourth) pinned the separating 4-cycle fixture:
`G(4/5)` spectrum ascending `{−4/5, 0, 0, 1}`, the exact middle pins
`evals ⟨1⟩ = evals ⟨2⟩ = 0` through the subspace Rayleigh–Ritz
engine at `k = 2, 3` (its first exercise on the PageRank family),
and the separation stated (`|λ₂| = 0 < α` strictly inside, the
bottom `−α` attained).


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
are **hard crust since the 2026-09-02 retirement of the
`primitive_power_tendsto` admission**
(`proposals/retire-primitive-power-convergence.md`: the
Doeblin/Dobrushin contraction route proved the axiom at its unchanged
statement; `#print axioms` on all of them exactly the standard three)
— and they make no `perron_frobenius` contact: producing `π` needs
that axiom, concluding convergence needs none. QA at
`Scaffold/QA/SpectralGraph/DirectedMixing_QA.lean`
(180 declarations by the generator metric: the reducible-fixture
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
| `pageRank_powerIteration` | **the classical PageRank algorithm as a theorem** (hard crust since the 2026-09-02 retirement): `(G ^ t) *ᵥ x → (π ⬝ᵥ x) • 1` at any nonnegative mass-one stationary `π` — of which the delivered `∃!` says there is exactly one |
| `pageRank_entrywise_tendsto` | the `t`-step transition probability `(G ^ t) i j → π j`, independent of the start (hard crust since the retirement) |
| `pageRank_walk_tendsto` | the Markov-chain mixing first slice: `ν ᵥ* (G ^ t) → π` for every start summing to one, entrywise topology (hard crust since the retirement; rates out of scope) |
| `googleMatrix_pow_mulVec_onesVec` | powers of the Google matrix fix `onesVec` — the mass bookkeeping translation (unconditional; the QA coherence join's other half) |
| `pageRank_tvDistance_le` | **the rate form** (2026-09-02, `proposals/doeblintv-tv-contraction-pagerank-rate.md`): `TV(ν ᵥ* (G ^ t), π) ≤ α^t · TV(ν, π)` — the field-standard PageRank power-method rate, the teleportation floor read as a Doeblin floor of coefficient exactly `α` through the mixing layer's new directed TV contraction; sign-free on `ν`, `π` through stationarity and mass alone (hard crust) |
| `pageRankDistribution` (+ `_apply`, `_nonneg`, `sum_`, `_zero`, `piSingle_vecMul_apply`) | **the per-start Google-walk law** (2026-09-02, `proposals/directed-mixing-time-object.md`): the random surfer's position distribution after `t` steps from `x` — the directed twin of `walkDistribution`, probability-certified through the power plumbing (`0 ≤` entries and row-sums preserved under powers) |
| `pageRank_tvDistance_le_of_depth` | **the ⌈log⌉-threshold depth form of the rate**: past `log(TV(ν,π)/ε)/log(1/α)` the evolved law is within `ε` of stationarity — the depth packaging of `pageRank_tvDistance_le`, at a private twin of the Oversmoothing calculus bridge (import-minimal) |
| `pageRankMixingTimeFrom` (+ `_bddBelow`, `_le_of_cert`, `_spec`, `_le_of_rate`, `_anti`) | **the directed mixing time** — the `t_mix` object family's missing sibling (plain/lazy/discrete/continuous/uniform all existed undirected): LPW ch. 20's per-start `t_mix` at the Google law against the caller-held stationary `π`; `_spec` the well-ordered attainment, `_le_of_rate` the α-ceiling `t_mix(ε) ≤ ⌈log(TV(δ_x,π)/ε)/log(1/α)⌉` (attained exactly in QA); the named consumer is the empirical PageRank capstone in `Derived/EmpiricalStationary.lean` |
| `pageRankTVPair` / `pageRankTVUniform` (+ `_nonneg`, `_eq_tvDobrushinCoeff`, `pageRankDistribution_add`/`_eq_row`, `piSingle_nonneg`) | **LPW's two distances at the Google law** (2026-09-02, `proposals/directed-uniform-mixing-time.md`): `d(t) = max_{x,y} TV(ν_t^x, ν_t^y)` (the two-start distance) and `d̄(t) = max_x TV(ν_t^x, π)` (Montenegro–Tetali's worst-start distance) against the caller-held `π`; the engine join identifies `d(t)` with the matrix-level Dobrushin coefficient of `G^t` |
| `tvDistance_vecMul_pow_googleMatrix_le`, `pageRankTVPair_submul` | **the Google-walk Dobrushin contraction and `d`-submultiplicativity**: `TV(μ ᵥ* G^t, ν ᵥ* G^t) ≤ TV(μ,ν)·d(t)` at equal masses, and `d(s+t) ≤ d(s)·d(t)` — pure Markovity (row stochasticity of `G` the only graph input) |
| `pageRankTVUniform_le_pageRankTVPair`, `pageRankDistribution_tvDistance_anti`, `pageRankTVUniform_mul_pageRankTVPair_le`, `pageRankTVUniform_succ_mul_le` | **the domination and the escalation engine**: `d̄ ≤ d` by the contraction at `(δ_x, π)` plus the simplex diameter (no mixture identity, no reversibility), discrete TV monotonicity in time, the mixed form `d̄(s+t) ≤ d̄(s)·d(t)`, and the iterated engine `d̄((k+1)t₀) ≤ d̄(t₀)·d(t₀)^k` |
| `pageRankMixingTime` (+ `_bddBelow`, `_le_of_cert`, `_spec`, `pageRankMixingTimeFrom_le_pageRankMixingTime`, `_eq_sup_pageRankMixingTimeFrom`, `exists_pageRankMixingTime_witness`, `_le_of_rate`, `_le_of_rate'`, `_le_mul_of_escalation`, `_le_of_escalation`) | **the directed uniform (worst-start) mixing time** — the `t_mix` object family's last missing member: LPW's `∀ s ≥ t, ∀ x` reading at the Google law; `_spec` the well-ordered attainment, the witness-load-bearing per-start domination, the sup interchange, the well-posedness supplier (every `ε` reachable from every start simultaneously), **the refined α-ceiling `t_mix(ε) ≤ ⌈log(d̄(0)/ε)/log(1/α)⌉`** (attained exactly in QA) and its display form, and LPW's ε-escalation corollaries (one certified evaluation yields every ε-level); the named consumer is the worst-start sampling capstone `empiricalPageRank_uniform_tail_of_depth` in `Derived/EmpiricalStationary.lean` (one start-independent threshold for every start) |

The retired admission's own module is
`Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence` (the
Doeblin-contraction engine and the proved convergence theorem,
`Matrix.IsPrimitive`, and the transfer layer — see the
[Linear Algebra map](linear_algebra.md)). The retirement's mechanism
QA (Section E of the QA module) pins the contraction attained
exactly on the strictly positive `2×2` fixture and refutes the
wrong-`δ` form; the rate layer's QA (Section F, 2026-09-02) pins the
TV contraction attained exactly at the basis pair and the Google
`α^t` rate attained exactly at *every* time on the periodic 2-cycle —
with the plain walk's never-decay `TV ≡ 1/2` pin beside it (the
periodicity fix in one picture). The uniform object's QA (Section H,
2026-09-02) pins the two-start closed form `d(t) = (1/2)^t` with
submultiplicativity attained with equality at every time, the
matrix-level Dobrushin contraction attained exactly, `d̄ = d/2`, the
uniform object in both directions, the refined α-ceiling attained
exactly with the display form's slack witnessed, and the escalation
corollary attained exactly. The engines' adversarial fence QA (Section
I, 2026-09-02,
`proposals/adversarial-fences-tv-dobrushin-engines.md`) supplies
negative witnesses for the seven load-bearing hypotheses the
directed-rate deliveries had left unfenced — the equal-mass clauses of
both TV contractions (the all-half matrix makes the Dobrushin
coefficient exactly `0`, so the mass-dropped contraction reads
`1/2 ≤ 0`), the row-sum and nonnegativity clauses of non-expansiveness
(the doubled identity doubles the basis pair's TV; the signed
stochastic fixture triples it), the row-sum clause of Dobrushin
submultiplicativity, and the zero-mass clauses of both pairing cores —
each with an isolation companion proving the refuted clause is exactly
what fails at the fixture. The TV-contraction shelf lives in
`Mixing.lean`'s Doeblin TV-contraction section — now also the home of
the matrix-level Dobrushin-coefficient engine
(`tvDobrushinCoeff`, `tvDistance_vecMul_le_tvDobrushinCoeff`,
`tvDobrushinCoeff_pow_add_le`, and the promoted public pairing core
`abs_sum_mul_le_of_pairwise`) — the `Mixing` rows above. The undirected walk layer joined this engine 2026-09-06
(`proposals/walktvpair-dobrushin-join.md`): the identity
`walkTVPair A t = tvDobrushinCoeff ((walkTransitionMatrix A) ^ t)`
(no symmetry needed) re-routes `Oversmoothing.lean`'s submul and
sharp-contraction proofs onto it at unchanged statements.

### Mixing — the primitivity supplier and the plain walk's Doeblin rate (`GraphTheory.Mixing` + `LinearAlgebra.PrimitiveConvergence`, 2026-09-02, `proposals/primitivity-supplier-plain-walk.md`)

The standing handoff's named blocker — an irreducibility+primitivity
supplier for the undirected plain walk — delivered with its consumer
chain. The engine lives at matrix level (`PrimitiveConvergence.lean`),
the wrapper and consumers at the walk level (`Mixing.lean`). All hard
crust (`#print axioms`-verified at the standard three).

| Declaration | Content |
|-------------|---------|
| `pow_entry_pos_of_pos` | **concatenation positivity** (matrix level): a positive `M^a` entry through `k` followed by a positive `M^b` entry gives a positive `M^(a+b)` entry — one term of the defining sum |
| `pow_entry_pos_bounce` | the `+2` bounce chain: a positive `e`-step entry `u → v` extends by any even length, bouncing `v → z → v` along a positive 2-cycle |
| `isPrimitive_of_pow_pos_of_odd_loop` | **the supplier** (matrix level): strong connectivity + every index on a positive 2-cycle (`htwo`) and an odd closed walk (`hodd`) ⟹ `IsPrimitive`, by the two-parity covering (reach, bounce for one parity, run the odd closed walk first for the other; witness `m := 1 + ∑ (d + L₀)` — the `1 +` keeps the empty index type case split-free). Support-level hypotheses, deliberately not `IsSymm`: `walkTransitionMatrix = D⁻¹A` is not symmetric on irregular graphs |
| `pow_walkTransitionMatrix_pos_of_walk` | **the walk→power bridge**: every support-graph walk of length `t` gives a positive `(i, j)` entry of `P^t` — `SimpleGraph.Walk` induction, each adjacency step one positive product term |
| `walkTransitionMatrix_isPrimitive_of_connected_of_odd_walk` | **the wrapper**: connected support graph + a single odd closed walk ⟹ the walk matrix is primitive; the odd walk transports to every vertex by concatenating a walk there, the odd walk, and the *reversed* walk back (`2\|q\| + \|p\|`, odd). `Odd p.length` is the honest interface — the pinned Mathlib has no `SimpleGraph.Bipartite` |
| `walkDistribution_tvDistance_le_of_pos_power` | **the plain walk's first mixing rate with no spectral certificate**: at a positive-power certificate `δ ≤ (P^m) i j`, `TV(ν_t x, π) ≤ (1 − \|V\|δ)^{t/m}` — the intrinsic-rate family's non-bipartite member (the entrywise lazy ceiling being its bipartite member), consuming the same Doeblin engine as the directed PageRank rate with `TV(δ_x, π) ≤ 1` folded in through the simplex diameter |
| `walkDistribution_tendsto_stationaryVec` | **the retired `primitive_power_tendsto`'s first undirected consumer**: the plain walk law converges to stationarity on the supplier's hypothesis set, composed from the proved `primitive_vecMul_tendsto` through the law/power bridge |

#### The primitivity-supplier family's adversarial fences (2026-09-03)

`proposals/adversarial-fences-primitivity-supplier-family.md`,
`EmpiricalStationary_QA.lean`'s `PrimitivityFences` section (QA-only,
zero axiom contact, +197 by the generator metric): negative witnesses
for the family's 21 unfenced load-bearing clauses, each with an
isolation companion — the engine trio's `hnn`/seed/step clauses
(`concatNeg`, `bounceNeg`, `bounceNoUp`/`bounceNoDown`, `swap2`), the
supplier's four hypotheses (`ident2`, `cycle3` the directed 3-cycle
permutation with `cycle3 ^ 3 = 1`, `swap2`, `rot2` the exact-cube
rotation with `rot2 ^ 3 = −8·1` — `rot2_pow_three_mul` signs every
power), the walk-to-power bridge's `hnn` (`negWalkAdj`: the
negative-diagonal chord makes `(P²) 0 2 = −5` on the genuine walk
`0 → 1 → 2`), the walk-level supplier's and corollary's `hnn`
(`negDiagTri` with the eigenvalue-`−11/4` closed forms
`negDiagTri_pow_mulVec_w` / `negDiagTri_row1_col0` — no power
entrywise positive, the law divergent), their `hconn` (`triIso4`:
`triIso4_pow_off` pins the identically-zero cross-block entry,
`triIso4_pow_row3` the absorbed law, `π 3 = 1/7 ≠ 1`), their `hp`
(`k2WalkEven` + `k2P_not_isPrimitive` + the alternating-law
`k2_tendsto_hp_fence_QA`), and the Doeblin rate's `hle` (negative
base at `δ = 1` on `K₂`) and `hA` (`asymLoopAdj`: the certificate
genuine at equality on `P = (1/2)·J` but `π` not stationary). The
generic `walkDistribution_apply_pow` (the law reads the power's row)
and `dist_ge_entry` support lemmas are public.

The proposal's priced follow-on (same file, the capstone subsection,
2026-09-03, +6): negative witnesses for the self-contained capstone
`empiricalWalkDistribution_tail_selfcontained_of_depth`'s two deferred
graph clauses — `hp` at `K₂` (`k2_capstone_hp_fence_QA`: connectivity
genuine, every closed walk even; past any threshold the even-time law
from `0` is `δ₀`, the sampling measure concentrates on the all-zero
trajectory, deviation `1/2` at full mass `1 > 2 exp(−4)`) and `hconn`
at `triIso4` (`triIso4_capstone_hconn_fence_QA`: a genuine odd closed
walk, but the absorbing vertex `3`'s law is `δ₃` at every time —
deviation `6/7` at full mass) — both through the point-mass cylinder
helper `toMeasure_cyl_singleton_one` (`toMeasure_cyl_inter` at a
factor with `q v = 1`, collapsing to `1 ^ n`), with
`two_mul_exp_neg_four_lt_one` the shared numeric and
`_isolation_QA` companions attributing each failure to its clause
alone. The capstone's falsification surface is complete: every
hypothesis fenced or recorded non-fenceable.

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

**Adversarial fences** (2026-09-04,
`proposals/adversarial-fences-variational-transfer-family.md`, the
fresh consumption survey's pick at 13 transitive non-QA consumers):
`VariationalTransfer_QA.lean`'s `TransferFences` section carries 27
hypothesis-form fences over the shelf's unfenced clause surface — the
transfer-engine layer's degree clauses at the negative-degree fixture
(junk `√(−1) = 0` collapsing the stretch across the Dirichlet transfer,
the degree-weighted pairings, the Rayleigh transfer, the
left-multiplied congruence, and the kernel-cone lift), PSD transfer's
`hA`/`hnn`, the congruence lemma's `hP`, the bottom-eigenvalue pin's
`hnn`/`hd`, the algebraic-connectivity transfer's `hnn` at the signed
path with connected support (two stretched kernel vectors force
`λ₂ ≤ 0`), and the degree sandwich's pointwise engines — headline: the
quotient bracket's sign-flip on signed input, the docstring's own
warning, witnessed at the connected negative cut. The Cheeger-statement
clauses and the mul-form sandwich/window clauses were already fenced by
`IrregularCheeger_QA`'s `IrregularFences` and `DegreeSandwich_QA` and
are out of scope.

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
| `laplacian_mulVec_partIndicator_of_mem`, `laplacian_mulVec_partIndicator_of_not_mem`, `laplacian_mulVec_partIndicator_apply` | **the boundary outflow lemma** (2026-09-07, `proposals/boundary-outflow-lemma.md` Step 1, hypothesis-free): `L · 1_S` is the outflow vector — on `S` the crossing outflow `∑_{j ∈ Sᶜ} A i j`, off it the negative inflow `-(∑_{j ∈ S} A i j)` — `laplacian_mulVec_apply` at the indicator plus the energy identity's own `sum_add_sum_compl` split one level down; the combined `if i ∈ S` packaging |
| `sum_laplacian_mulVec_partIndicator` | the region row-sum total is `boundary A S` definitionally (hypothesis-free) |
| `quadForm_laplacian_partIndicator_unsymm` | **the energy identity without symmetry**: the same `quadForm (laplacian A) (partIndicator S) = boundary A S` for ANY weights (asymmetric included) — the vector-level outflow route never flips the region, so `boundary_compl` never enters and the delivered symmetric version's `hA` is removable |
| `abs_partIndicator_dotProduct_heatFlow_le` | **the regional dissipation bound** (2026-09-07, `proposals/boundary-outflow-lemma.md` Part 2 / the Medium row's ask): `|1_S ⬝ᵥ (x₀ − e^{−tL}x₀)| ≤ t · ‖L·1_S‖ · ‖x₀‖` — the cut↔heat bridge, the norm factor being the outflow vector's own norm; general-probe engine `abs_dotProduct_heatFlow_le` in `Heat.lean` (symmetric swap + Cauchy–Schwarz + the global order-0 contraction at the probe) |
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

### `Scaffold.Mathlib.GraphTheory.AlonBoppana` (the cycle family — the asymptotic corollary)

The program's first *parametric* (arbitrary-`n`) instantiation, delivered
2026-09-02 (`proposals/cycle-family-alon-boppana-asymptotic.md`, zero new
axioms): the canonical 2-regular family — the cycles `C_n`, carried by
Mathlib's own `SimpleGraph.cycleGraph` through the `toWAdj` adapter —
names the d-regular family with `diam → ∞` that the program's completion
note required, and Nilli's two-edge method discharges on it at every
scale `k`. The new mathematical content is the **exact cycle distance
formula** (the walk route up, the integer-potential route down), from
which the tree-ball hypothesis and the far-apart condition follow at
arbitrary scale. QA pinned at `C₁₂` at delivery, then made parametric
(every lemma `∀`-quantified over the scale, the tree-ball truth boundary
bracketed at every `n`) by the follow-on
`proposals/parametric-cycle-qa.md` (`AlonBoppana_QA.lean` Steps 7–8).

| Declaration | Content |
| --- | --- |
| `cycleAdj` | **the family's weighted adjacency**: `cycleAdj n := SimpleGraph.toWAdj (SimpleGraph.cycleGraph n)` — Mathlib's own cycle graph entering the SGT center through the adapter, the `Matrix (Fin n) (Fin n) ℝ` representation every center theorem consumes |
| `cycleAdj_isSymm` / `cycleAdj_nonneg` / `cycleAdj_apply` / `cycleAdj_h01` | the adapter interface re-expressed on the family: symmetry, nonnegativity, the `0`/`1` entry form (`if (cycleGraph n).Adj i j then 1 else 0`), and the `0`-or-`≥ 1` weight discipline — exactly the `h01` hypothesis idiom `radialVec_quadForm_ge` and the headline consume |
| `supportGraph_cycleAdj` | the adapter roundtrip on the family: `supportGraph (cycleAdj n) = SimpleGraph.cycleGraph n` — every `supportGraph`-stated theorem on the family reduces to Mathlib's own cycle graph |
| `cycleAdj_connected` / `cycleAdj_isDRegular` | the structural hypotheses supplied at the family level: connectivity at `1 ≤ n`, and `IsDRegular (cycleAdj n) 2` at `3 ≤ n` — the degree the Alon–Boppana error term `d − 2√(d−1)` vanishes at |
| `cycleAdj_dist_eq` | **the exact cycle distance formula**: `dist a b = min ((b−a).val) (n − (b−a).val)` at `2 ≤ n` — the short orientation bound by an explicit walk (`cycleGraph_dist_le_up`, private), the long orientation by the ℤ-potential route (`cycle_walk_potential`, private: every walk realizes a residue representative of `b − start` of absolute value ≤ its length, in `Int.ModEq` form); the engine from which both structural hypotheses of the two-edge method discharge at arbitrary scale, and the program's first parametric distance fact (before this, `dist` on the shelf was pinned only at fixed literal fixtures) |
| `cycle_levE_eq` | **the BFS level formula at a cycle edge**: `levE a (a+1) z = 0` at the endpoints, `min ((z−a).val − 1) (n − (z−a).val)` otherwise — the level machinery of Step 2 computed in closed form on the family |
| `cycle_levClass_eq` | **the level class in closed form**: at `1 ≤ j` and the strict `2(j+1) < n`, the level-`j` class of the edge `(a, a+1)` is exactly the two vertices at cyclic offsets `j+1` forward and `n−j` backward — `{a+(j+1), a+(n−j)}`; the strictness is proof-forced, not truth-forced (the parametric QA computed the boundary classes raw from `cycle_levE_eq` exactly where this hypothesis refuses: the even tie `2(j+1) = n` still carries the adjacent antipodal *pair*, card `2` — the cardinality equation holds there — while the odd boundary `n = 2j+1` merges the two branches into one vertex, card `1 < 2`, the genuine strictness bite) |
| `isTreeBall_cycle` | **the tree-ball hypothesis at arbitrary scale**: `IsTreeBall (cycleAdj n) … 2 (k+1)` at `2(k+1) < n` — the cardinality equations `2·(d−1)^j = 2` reading off the level-class closed form; the strict threshold is proof-forced (QA pins `IsTreeBall` *holding* one radius past the certified one at the antipodal tie, and failing one past the truth with the empty class — the bracket at every scale) |
| `cycleAdj_distEdge_gt` | **the far-apart condition at the antipodal edge**: on `C_{4k+8}`, `(k+1)+(k+1) < distEdge (0,1) (2k+4, 2k+5)` — the two-edge method's separation hypothesis, with the family's `4k+8` sizing buying exactly slack `1` (QA pins the exact value `distEdge = 2k+3` against the required `2(k+1) = 2k+2`, slack exactly `1` at every scale) |
| `alonBoppana_cycle` | **the headline**: `secondEval (2•1 − cycleAdj (4k+8)) ≤ 1/(k+1)` — Nilli's theorem instantiated at `d = 2` where the barrier `d − 2√(d−1) = 0`, every hypothesis (regularity, the genuine edges, connectivity, far-apart, both tree balls) discharged at every scale `k` |
| `laplacian_cycleAdj` | the spelling bridge: `laplacian (cycleAdj n) = 2•1 − cycleAdj n` at `3 ≤ n` (2-regularity: `degreeMatrix = 2•1`), joining the adjacency-facing statement to the Laplacian |
| `alonBoppana_cycle_laplacian` | **the Laplacian form**: `λ₂ (L (C_{4k+8})) ≤ 1/(k+1)` — the headline transported through `laplacian_cycleAdj` and `secondEval_congr` at an unchanged bound; the statement form the asymptotic corollary consumes |
| `alonBoppana_cycle_asymptotic` | **the asymptotic corollary**: `∀ ε > 0, ∃ k, λ₂ (L (C_{4k+8})) ≤ ε` — the Alon–Boppana error term tending to zero along the named family with `diam → ∞` (witness `k := ⌈1/ε⌉`, pinned explicitly in QA); the d-regular family the program's completion note asked to be named |

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
`heatKernel_firstOrder_remainder_interval`. **The variance-decay
section added 2026-08-31** (`proposals/heat-variance-decay.md`, the
Poincaré delivery's named deferred follow-on): eigenvalue plumbing
(`eigvalOf_mem_evals`, `secondEval_le_eigvalOf_of_ne_zero`), the
positive-gap kernel lemma, mean preservation, the coordinate-damping
and Parseval-exact heat identities, and **`heatKernel_variance_decay`**
(`Var(e^{-tL}f) ≤ e^{−2tλ₂}Var(f)`, hypothesis-minimal — no
connectivity, no gap positivity — by the eigenbasis contraction, no
derivative machinery). **The global (window-free) contraction section
added 2026-09-07** (`proposals/global-semigroup-contraction.md`
Steps 0(m=0)/1/2 under its named-consumer scope — the operator-added
Medium row `proposals/boundary-outflow-lemma.md`, whose Part 2 is the
consumer): the scalar engine `sq_one_sub_exp_neg_le`
(`(1 − e^{−y})² ≤ y²` on the half-line, from `Real.add_one_le_exp` +
`Real.exp_le_exp` — the window-free stand-in for the pin's windowed
`Real.abs_exp_sub_one_sub_id_le`),
`heatKernel_globalContraction_dotProduct_le` /
`heatKernel_globalContraction_le` (`‖x − e^{−tL}x‖ ≤ t·‖Lx‖` at every
`t ≥ 0` on nonnegative-weight networks, no eigenvalue window —
Parseval + PSD + the scalar engine), and the general-probe dissipation
engine `abs_dotProduct_heatFlow_le` (`|v ⬝ᵥ (x₀ − e^{−tL}x₀)| ≤ t ·
√(Lv ⬝ᵥ Lv) · √(x₀ ⬝ᵥ x₀)`, symmetric swap + Cauchy–Schwarz + the
contraction at the probe; the `partIndicator` specialization lives in
`Multiway.lean` as the Part-2 theorem). Pure hard crust, zero axioms;
QA at `Scaffold/QA/SpectralGraph/Heat_QA.lean` — including the payoff
pin (the global bound holds at `t = 1` on K₂ where the windowed
bound's hypothesis provably fails) and the `hnonneg` fence (the
conclusion provably fails on the signed negative-eigenvalue fixture,
`e² > 3` by `Real.add_one_lt_exp`). The shelf's
falsification surface was completed 2026-09-05
(`proposals/adversarial-fences-heat-family.md`, the audit method's
eighteenth application, this run's fresh consumption survey confirming
Heat as the library's most-consumed unaudited shelf at 8 transitive
non-QA consumers): 30 hypothesis-form fences in the QA file's
`HeatFences` section, headline findings the dissipation failure on
signed input (the negative edge's eigenvalue `-4` makes every "decay"
factor a growth factor, `e⁴ > 1`), the DC-limit and variance-decay
`hnn` failures at the same fixture (`2e⁸ > 2` at rate `1`), the
mean-preservation `hA` kill on asymmetric input (`1 − α ≠ 1` with
`α = (1−e⁻³)/3`), the six normalized/walk `hd` kills at the
zero-degree signed fixture (the junk `D⁻¹ᐟ²` congruence-collapse with
`√D·1` surviving), and the remainder-window kill at `t = -2`
(`e⁴ − 5 > 16` through the `9/4 ≤ e` pin).

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
| `eigvalOf_mem_evals` | **eigenvalue plumbing, converse half** (2026-08-31, the variance-decay section, `proposals/heat-variance-decay.md`): every eigenbasis eigenvalue appears in the sorted spectrum (`∃ k, evals hM k = eigvalOf M hM i`) — the converse of `evals_mem_eigvalOf`, by `List.mem_iff_get` at the sorted list |
| `secondEval_le_eigvalOf_of_ne_zero` | **every nonzero Laplacian eigenvalue dominates the gap**: an eigenvalue below `evals ⟨1⟩` sits at sorted index `0` (sortedness), which is exactly `0` (`laplacian_evals_zero`) — below-gap eigenvalues *are* kernel eigenvalues; the rate comparison the heat variance decay consumes |
| `eigvecOf_ker_eq_smul_onesVec_of_secondEval_pos` | **kernel modes at a positive gap are constant**: a nonzero centered kernel residual would have Rayleigh quotient `0`, forcing `λ₂ ≤ 0` through `secondEval_le_rayleigh`; stated at `0 < λ₂` (the exact boundary), not connectivity |
| `sum_heatKernel_mulVec` | **mean preservation**: `∑ (e^{-tL} f) = ∑ f` at every time on symmetric input — the sum is the `onesVec` pairing moved across by kernel symmetry (`heatKernel_isSymm` + `heatKernel_mulVec_onesVec`); what makes both variances in the headline decay center at the same mean |
| `eigvecOf_dotProduct_heatKernel_mulVec` | **coordinate damping**: `vᵢ ⬝ᵥ (e^{-tL} *ᵥ x) = e^{−tλᵢ} (vᵢ ⬝ᵥ x)` — the heat analogue of the mixing program's walk-factor identity, through self-adjointness of the (symmetric) kernel plus `heatKernel_mulVec_eigvecOf` |
| `dotProduct_self_heatKernel_mulVec` | **Parseval-exact heat identity**: `‖e^{-tL}x‖² = ∑ᵢ (e^{−tλᵢ} (vᵢ ⬝ᵥ x))²` — no inequality lost; the exact quantity the variance becomes in eigenbasis coordinates |
| `heatKernel_variance_decay` | **heat-variance decay — the Poincaré delivery's named deferred follow-on, the heat family's consumer of λ₂**: `∑ ((e^{-tL}f) i − mean f)² ≤ e^{−2tλ₂} · ∑ (f i − mean f)²` for every `f` on every symmetric nonnegative network at every `t ≥ 0`, hypothesis-minimal (no connectivity, no gap positivity — at `λ₂ = 0` the true rate-1 statement, QA-pinned *exact* there); proved by the eigenbasis contraction (the mixing program's proved ℓ²(π) technique transferred from `P^t` to `e^{-tL}`, no derivative machinery), the two branches sharing one Parseval identity: at `0 < λ₂` zero modes carry no coordinate + the eigenvalue comparison; at `λ₂ ≤ 0` every factor `≤ 1 ≤ e^{−2tλ₂}` |

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

#### Adversarial fences (`CoreFences`, 2026-09-04)

`Sparsification_QA.lean`'s `CoreFences` section (`proposals/adversarial-fences-sparsification-core-family.md`): hypothesis-form negative witnesses for the deterministic core's 15 unfenced load-bearing clauses — the eigenvalue-nonnegativity engine's `hnn` (whole-family form at the signed fixture: the pinned `quadForm = −2` plus the spectral resolution), the leverage-share identity's `hnn` (the signed fixture's negative pair: junk-`√` zero edge vector against `(−1)·R 2 1/2 = 1`), the ordered-pair budget identity's `hnn` (the rank-1 signed 4-cycle: `L = s⊗s` pinned entrywise, the single genuine eigenvalue `4`, per-pair `1/8`, total `1 ≠ card − 1`), the projector trio and exact-deviation identity's `hnn` (the nonpositive-spectrum fixture: every eigenvalue `≤ 0` zeroes every edge vector), the trace identity's `hconn` (the disconnected fixture through the Foster kernel-count engine), the bilinear Dirichlet identity's `hA` (asymmetric `Fin 2`: `3 ≠ 4`), the sampling layer's `hq` clauses and the second moment's `hpne` at `K₂`, and the strict dot-positivity `hv`. Recorded non-fenceables with mechanisms: the junk-`√` zero edge vector as an automatic sign guard on the sampled Laplacian's PSD theorem; two `hq` bound clauses algebraically true at every corner; the two transport clauses already fenced by the tail QA's `sg` fixture.

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
| `edgePerturbation_spectralEncodingSubspace_drift` | Spectral-encoding stability | **(2026-08-31)** The pipeline at arbitrary encoding rank `k` (`k + 1 < card V`), consuming `spectralEncodingSubspace_stability` with the separation discharged *inline* from the base graph's rank-`k` gap by the proved Weyl at index `k+1` — automatic `δ` certification, the LapPE delivery's priced deferred follow-on (`proposals/spectral-encoding-drift-pipeline.md`) |
| `edgePerturbation_spectralEncoding_drift` | Spectral-encoding stability | **(2026-08-31)** The kernel-isolated rank-`k` form: the informative encoding component `P_k − P₀` under the per-outcome design constraints (the `k = 1` instance is the Fiedler-line theorem); conditional on `matrix_hoeffding` via the tail alone |
| `edgePerturbation_spectralEncodingSubspace_drift'` | Spectral-encoding stability | **(2026-08-31)** The sharpened matched-threshold rank-`k` form: at `0 < s < γ ≤ evals ⟨k+1⟩ (L A) − evals k (L A)`, `μ{‖P_k(A+E_ω) − P_k(A)‖ ≥ s/(γ−s)} ≤ 2 d exp(−s²/(2‖∑ₑ L_e²‖))` |
| `edgePerturbation_spectralEncoding_drift'` | Spectral-encoding stability | **(2026-08-31)** The ML-facing payoff at general rank: the same `s/(γ−s)` statement for the encoding component `P_k − P₀` itself; QA pins the star `K₁,₃` closed-form instances `8 exp(−1/32)` at `k = ⟨2⟩` (a rank the `k = 1` family cannot express — the trace-route vacuity pin proves `evals ⟨2⟩ − evals ⟨1⟩ = 0` there, so `k = ⟨2⟩` is exactly the tie structure's demand) |

### `Scaffold.Derived.SparsificationTail` (leverage-score sparsification, Slice 3 — the axiom-backed assembly)

The program's payoff: `matrix_bernstein`'s first real theorem consumer
(2026-08-27). The declarations are **conditional on the
`matrix_bernstein` axiom** (Tropp 2012, Theorem 1.1) — every
hypothesis clause is proved hard crust, the tail inequality itself is
axiom-backed, and `#print axioms` reports the dependency. The
2026-08-28 follow-ons add the multiplicative `(1±ε)` sparsifier shape
and its `q ~ log n/ε²` budget corollary on the same conditional
structure. The 2026-08-31 Track A additions (`sparsificationBudget`
and the plug-in form,
`proposals/spectral-graph-sparsification-gnn-training.md`) are the
GNN-facing packaging: the closed-form minimal budget is **proved hard
crust** — only the plug-in guarantee inherits the axiom.

| Declaration | Area | Description |
| --- | --- | --- |
| `sparsification_norm_tail` | Sparsification Slice 3 (axiom-conditional) | **The SS deviation tail**: `μ {‖S(ω) − Π_{im L}‖ ≥ t} ≤ 2 d exp(−t²/(2/q + 2t/(3q)))` at the proved constants `R = 1/q`, `‖Σ‖ ≤ 1/q`; Finding B's `Fin n` transport via `Fintype.equivFin` + `Equiv.sum_comp`; no connectivity hypothesis |
| `sparsification_quadForm_tail` | Sparsification Slice 3 (axiom-conditional) | **The quadratic-form tail**: the same bound for the failure of `|xᵀ S x − xᵀ Π x| ≤ t (x ⬝ᵥ x)` for every vector — the additive eigen-coordinate pullback of the norm event |
| `sparsification_multiplicative_tail` | Sparsification follow-on (axiom-conditional, 2026-08-28) | **The `(1±ε)` sparsifier tail** — the field-standard statement shape: the failure of the two-sided bound `(1−ε)(x ⬝ᵥ x) ≤ xᵀ S(ω) x ≤ (1+ε)(x ⬝ᵥ x)` over `im Π`-coordinate vectors obeys the same exponential tail (the additive tail at `t = ε`, legitimate on the cone by the engine identity) |
| `sparsification_multiplicative_budget` | Sparsification follow-on (axiom-conditional, 2026-08-28) | **The sample-complexity corollary**: at `0 < ε ≤ 1`, `0 < δ`, budget `q ≥ (8/3)·log(2 card V/δ)/ε²` drives the multiplicative failure measure below `δ` — the classical `q ~ log n/ε²` sentence at the exact Tropp exponent constant |
| `sparsification_graph_tail` | Sparsification follow-on (axiom-conditional, 2026-08-28) | **The graph-vector `(1±ε)` tail** — the textbook sentence: `(1−ε)xᵀLx ≤ xᵀL̃(ω)x ≤ (1+ε)xᵀLx` failing only on a set of the bound's measure, for *every* graph vector with no `im Π` restriction (the transport is on-cone by construction; the isometry and form correspondence transfer the delivered additive tail verbatim) |
| `sparsification_graph_budget` | Sparsification follow-on (axiom-conditional, 2026-08-28) | **The graph-vector budget corollary**: the same `q ≥ (8/3)·log(2d/δ)/ε²` sentence driving the graph-form failure measure below `δ` (numeric core factored as `sparsification_budget_core`) |
| `sparsificationBudget` / `_pos` / `_le` / `_min` | GNN packaging Track A (proved, 2026-08-31) | **The closed-form sampling budget** — `max 1 ⌈(8/3)·log(2n/δ)/ε²⌉` as pure arithmetic (zero axioms): positive, meeting the budget inequality, and *minimal* among naturals, so a caller supplies only `(n, ε, δ)`; the GNN-facing statement with the trust caveat first is `docs/gnn-sparsification-budget.md` |
| `sparsification_graph_budget_closedForm` | GNN packaging Track A (axiom-conditional, 2026-08-31) | **The plug-in budget guarantee**: `sparsification_graph_budget` at the computed budget — pass only the graph hypotheses and `(ε, δ)`; conditional on `matrix_bernstein` exactly like the corollary it applies, while the budget arithmetic itself is axiom-free |

## Applications

These declarations feed the perturbation bridge
([Perturbation map](perturbation.md)) and a retained spectral-persistence
example described in [docs/3_SPECTRAL_THEORY.md](../../docs/3_SPECTRAL_THEORY.md).
That example is compatibility surface, not the SGT roadmap.

### Continuous-time mixing (`GraphTheory.Heat` walk-heat sections + `GraphTheory.Mixing` `ContinuousTime`, 2026-08-31)

The π-weighted `L_sym` twin of heat-variance decay with the
continuous-time χ² mixing consumer
(`proposals/continuous-time-chi-square-mixing.md`): the walk heat
kernel conjugated to the normalized one, degree-weighted variance
decay at rate `λ₂(L_sym)`, and the intrinsic-rate mixing bound. All
proved hard crust; no axiom disposition changed.

| Declaration | Area | Description |
| --- | --- | --- |
| `normalizedHeatKernel` | Heat (continuous-time mixing) | the normalized heat semigroup `e^{-tL_sym} := exp(−(t • normalizedLaplacian A))` — the π-weighted world's diffusion operator |
| `normalizedHeatKernel_mulVec_eigvecOf` | Heat (continuous-time mixing) | mode decay at `L_sym`: every eigenbasis vector is an eigenvector of `e^{-tL_sym}` at factor `e^{−t·λᵢ}` |
| `dotProduct_self_normalizedHeatKernel_mulVec` | Heat (continuous-time mixing) | the Parseval-exact norm identity at `L_sym` — the squared norm as the eigenvalue-weighted sum of squared eigencoordinates |
| `secondEval_le_eigvalOf_normalizedLaplacian_of_ne_zero` | Heat (continuous-time mixing) | every nonzero `L_sym` eigenvalue dominates the normalized spectral gap (below-gap = kernel, via `normalizedLaplacian_evals_zero`) |
| `eigvecOf_ker_eq_smul_degreeSqrt_onesVec_of_secondEval_pos` | Heat (continuous-time mixing) | at a positive gap every kernel eigenbasis vector is a `√D·1` multiple (the general-kernel Rayleigh bound at the normalized kernel vector) |
| `walkHeatKernel` | Heat (continuous-time mixing) | the walk heat semigroup `e^{-tL_walk} := exp(−(t • walkLaplacian A))` — the continuous-time random walk's density evolution operator |
| `degreeSqrt_mulVec_walkHeatKernel` | Heat (continuous-time mixing) | **the exp conjugation**: `√D *ᵥ (e^{-tL_walk} *ᵥ f) = e^{-tL_sym} *ᵥ (√D *ᵥ f)` — the continuous analogue of the conjugated-power transfer, by per-power conjugation of the exponential series |
| `walkHeatKernel_variance_decay` | Heat (continuous-time mixing) | **the π-weighted twin**: `∑ deg·(e^{-tL_walk}f − mean_π f)² ≤ e^{−2tλ₂(L_sym)}·∑ deg·(f − mean_π f)²` — hypothesis-minimal (at `λ₂(L_sym) = 0` the true rate-1 statement) |
| `contWalkDensity` | Mixing (continuous time) | the continuous-time walk's π-density started at `x`: the walk density evolved by `e^{-tL_walk}` |
| `degreeSqrt_mulVec_contWalkDensity_sub_one` | Mixing (continuous time) | the centered-density conjugation shift `√D(h_t − 1) = e^{-tL_sym}(√D(h₀ − 1))` — the identity every exact computation runs through |
| `contChiSquareDistance` | Mixing (continuous time) | the continuous-time χ² distance `∑ π (h_t − 1)²`, with the `t = 0` join `= ((πx)⁻¹ − 1)` to the discrete object |
| `contChiSquareDistance_le` | Mixing (continuous time) | **the continuous-time mixing bound**: `χ²_cont(t,x) ≤ e^{−2tλ₂(L_sym)}·((πx)⁻¹ − 1)` — no connectivity, no caller-certified rate (the continuous rate is intrinsic; strictly stronger shape than the discrete sibling) |
| `contWalkDistribution` | Mixing (continuous time) | the continuous walk **law** `ν_t(i) = π i · h_t(i)` — the actual probability vector of the walk run in continuous time, with the `t = 0` join `contWalkDistribution_zero` to `walkDistribution` |
| `contWalkDistribution_tvDistance_le` | Mixing (continuous time) | **the continuous-time ℓ²→TV conversion**: `TV(ν_t x, π) ≤ (1/2)·√χ²_cont` — unconditional (the delivered conversion composed with the delivered continuous χ² through the sum-div bridge) |
| `contWalkDistribution_tvDistance_le_of_decay` | Mixing (continuous time) | **the decay form**: `TV ≤ (1/2)·e^{−t·λ₂(L_sym)}·√((πx)⁻¹ − 1)` at exactly `contChiSquareDistance_le`'s hypothesis set — no caller-certified rate |
| `contMixingTimeFrom` | Mixing (continuous time) | **the continuous-time mixing time**: the per-start `sInf{t | 0 ≤ t ∧ ∀ s ≥ t, TV(ν_s x, π) ≤ ε}` — exactly LPW ch. 20's `t_mix` reading (the honest form for a distance not assumed monotone in time); junk corner at unreachable `ε` documented |
| `contMixingTimeFrom_le_of_cert` | Mixing (continuous time) | the certificate interface: any witness time `T` (`0 ≤ T`, `∀ s ≥ T, TV ≤ ε`) certifies `t_mix(ε) ≤ T` — the discrete `pow_mul_le_of_log_threshold` analogue |
| `contMixingTimeFrom_le_of_connected` | Mixing (continuous time) | **the spectral ceiling**: `t_mix(ε) ≤ max 0 (ln(√((πx)⁻¹ − 1)/(2ε))/λ₂(L_sym))` — the field-standard continuous-time mixing bound (Montenegro–Tetali; LPW ch. 20), the `max 0` floor the honest two-case shape |
| `contMixingTimeFrom_anti` | Mixing (continuous time) | ε-antitonicity: `ε ≤ δ` and a witness for `ε` give `t_mix(δ) ≤ t_mix(ε)` — the field-standard monotonicity in the threshold |

### The Poisson bridge (`GraphTheory.Mixing` Poisson-bridge section + `GraphTheory.Heat` generic helpers, 2026-09-01)

The continuous↔discrete mixing-time comparability
(`proposals/continuous-time-chi-square-mixing.md`'s named follow-on):
LPW ch. 20's Poissonization — the continuous-time walk law is the
Poisson mixture of the discrete walk laws — with the TV contraction
toolkit it yields. All proved hard crust; no axiom disposition
changed.

| Declaration | Area | Description |
| --- | --- | --- |
| `pow_smul_matrix` | Heat (matrix algebra) | scalar-matrix powers: `(c • M) ^ n = c ^ n • M ^ n` — generic algebra consumed by the Poissonization identity |
| `matrix_exp_smul_one` | Heat (matrix algebra) | **the scalar-matrix exponential**: `e^{cI} = e^c • I` — the scalar half of the Poissonization exponential split `−t(I − P) = tP − tI` |
| `poissonWeight` | Mixing (Poisson bridge) | the Poisson weight `e^{−t}·tᵏ/k!` — the probability a rate-one clock rings `k` times by `t` (definition) |
| `poissonWeight_nonneg` / `poissonWeight_hasSum_one` / `poissonWeight_summable` / `poissonWeight_tsum_eq_one` | Mixing (Poisson bridge) | the probability-sequence package: `∑' poissonWeight t = 1` at every time (`e^{−t}·e^{t} = 1`) |
| `walkDensity_eq_pow_walkTransitionMatrix_mulVec` | Mixing (Poisson bridge) | the discrete density at `k` is `Pᵏ *ᵥ h₀` — the uncentered power identity the mixture consumes |
| `hasSum_poisson_walkDensity` | Mixing (Poisson bridge) | **the Poissonization identity** (`HasSum` form): `e^{−tL_walk} *ᵥ h₀ = ∑'ₖ poissonWeight t k • h_k` — through `Matrix.exp_add_of_commute` at `−t(I−P) = tP − tI` plus the scalar-matrix exp, the mixing layer's first tsum construction |
| `contWalkDensity_eq_tsum` / `contWalkDistribution_eq_tsum` | Mixing (Poisson bridge) | the identity at density and law level: `ν^cont_t = ∑'ₖ e^{−t}tᵏ/k! · ν_k` — LPW ch. 20's `H_t = e^{−t}∑ tᵏ/k!·Pᵏ` read at the law |
| `tvDistance_le_one_of_nonneg_of_sum_eq_one` / `walkDistribution_tvDistance_le_one` | Mixing (Poisson bridge) | the TV diameter of the probability simplex; the walk law's TV distance to stationarity `≤ 1` at every time |
| `tvDistance_walkTransitionMatrixTranspose_mulVec_le` | Mixing (Poisson bridge) | **the adjoint walk is an ℓ¹-contraction**: `TV(Pᵀμ, Pᵀν) ≤ TV(μ, ν)` — every row of `P` a probability vector, the triangle inequality averaged against them |
| `tvDistance_walkTransitionMatrixTranspose_pow_mulVec_le` / `walkTransitionMatrixTranspose_pow_mulVec_stationaryVec` / `walkDistribution_add` | Mixing (Poisson bridge) | the iterated contraction, the stationary fixpoint, and the power evolution `ν_{t+s} = (Pᵀ)ˢ *ᵥ ν_t` |
| `walkDistribution_tvDistance_anti` | Mixing (Poisson bridge) | **discrete TV monotonicity in time**: `TV_{t+s} ≤ TV_t` — the field-standard `d(k)` non-increasing, new to the shelf |
| `tsum_eq_range_add` | Mixing (Poisson bridge) | splitting a summable series at a threshold `m`: the head–tail decomposition |
| `tvDistance_tsum_le` | Mixing (Poisson bridge) | **TV convexity in countable mixtures**: the mixture's TV distance ≤ the weight-averaged TV distances — the Poissonization consumer |
| `contWalkDistribution_tvDistance_le_tsum` | Mixing (Poisson bridge) | the Poisson-averaged bound: `TV_cont(t) ≤ ∑'ₖ e^{−t}tᵏ/k! · TV_disc(k)` |
| `contWalkDistribution_tvDistance_add_le` | Mixing (Poisson bridge) | **the continuous↔discrete comparability**: `TV_cont(t) ≤ ∑_{k<m} e^{−t}tᵏ/k! + TV_disc(m)` at every threshold `m` — LPW ch. 20's Poissonization comparison, tail term exact (no Chernoff rounding) |
| `contWalkDistribution_tvDistance_le_of_discreteMixing` | Mixing (Poisson bridge) | **the discrete-certificate transfer**: a discrete mixing certificate (`∀ k ≥ m, TV_disc(k) ≤ ε₁`) plus a Poisson lower-tail bound (`∑_{k<m} e^{−t}tᵏ/k! ≤ ε₂`) give `TV_cont(t) ≤ ε₁ + ε₂` — was the would-be consumer of the still-deferred discrete `t_mix` object (`hmix` is exactly its witness condition); that object is now delivered (`walkMixingTimeFrom`, the Oversmoothing table), and its attainment specification discharges this `hmix` clause |

### Mixing — the lazy walk (`GraphTheory.Mixing`, 2026-09-01, `proposals/lazy-walk-mixing.md`)

The discrete mixing program's periodicity fix: LPW ch. 5's lazy chain
`P_L = (P + I)/2`, whose mode factors `1 − λ/2` lie in `[0, 1]` — the
intrinsic-rate mixing family on the side of the program where every
caller-certified family is provably unsatisfiable (bipartite graphs).

| Declaration | Area | Description |
| --- | --- | --- |
| `lazyWalkTransitionMatrix` | Mixing (lazy walk) | the lazy operator `2⁻¹ • (P + 1)` — stay or move, probability `1/2` each (definition) |
| `lazyWalkTransitionMatrix_apply` / `_mulVec_one` / `_nonneg` | Mixing (lazy walk) | the entry interface, the constant fix `P_L *ᵥ 1 = 1`, and entrywise nonnegativity |
| `lazyWalkDistribution` / `_zero` / `_succ` / `sum_` / `_nonneg` | Mixing (lazy walk) | the lazy walk law `(P_Lᵀ)ᵗ *ᵥ δₓ` with its evolution, mass conservation, and nonnegativity — the plain object's exact definition at the lazy operator |
| `stationaryVec_mul_lazyWalkTransitionMatrix` | Mixing (lazy walk) | **detailed balance, lazy form**: `π` is reversible for `P_L` (the average of two π-reversible operators) |
| `lazyWalkTransitionMatrixTranspose_mulVec_stationaryVec` / `lazyWalkDistribution_add_stationary` | Mixing (lazy walk) | `π` stationary for the lazy walk; **attainment persists** — once at stationarity, forever |
| `lazyWalkDensity` / `_zero` / `_succ` / `_sub_one` | Mixing (lazy walk) | the π-density objects: the join to the plain initial density (the connectivity mode derivation applies verbatim), the density evolution `h_{t+1} = P_L *ᵥ h_t`, and the centered evolution |
| `lazyChiSquareDistance` / `_eq_sum_smul` / `_zero` | Mixing (lazy walk) | the lazy χ² distance in sum-div shape (composable with the entropy bridge), density form, and `t = 0` normalization |
| `quadForm_sub_eq` / `quadForm_add_eq` / `quadForm_degreeMatrix_eq` | Mixing (lazy walk) | generic quadratic-form splitting + the degree-matrix entry identity |
| `quadForm_degreeMatrix_add_eq_half_sum` | Mixing (lazy walk) | **the signless sum-of-squares**: `uᵀ(D+A)u = (1/2) ∑ i j, A i j (u i + u j)²` — the positivity certificate bounding the normalized spectrum above by `2` |
| `quadForm_two_sub_normalizedLaplacian_eq` / `_nonneg` | Mixing (lazy walk) | the conjugation identity `xᵀ(2·1 − L_sym)x = uᵀ(D+A)u` at `u = (1/√D) *ᵥ x`, and its nonnegativity at nonnegative weights (`hnn` load-bearing, fenced) |
| `eigvalOf_normalizedLaplacian_nonneg` / `eigvalOf_normalizedLaplacian_le_two` | Mixing (lazy walk) | **the two-sided normalized-spectrum bound** `0 ≤ μ ≤ 2` — PSD at the unit eigenvector, the signless certificate at the unit eigenvector (bipartite top mode = the boundary) |
| `degreeSqrt_mul_lazyWalkTransitionMatrix_eq` / `degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix` | Mixing (lazy walk) | the lazy commutation `√D P_L = (1 − (1/2)L_sym) √D` and the conjugated-power transfer |
| `eigvecOf_dotProduct_one_sub_half_normalizedLaplacian_mulVec` | Mixing (lazy walk) | the eigenaction of the symmetric lazy operator on the `L_sym` eigenbasis — mode factor `1 − μ/2` |
| `eigvecOf_dotProduct_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix` / `dotProduct_self_...` / `..._contraction` / `sum_stationaryVec_smul_sq_pow_lazyWalkTransitionMatrix_le` | Mixing (lazy walk) | the lazy decay engine: eigencoordinate evolution at `(1 − μ/2)^t`, the Parseval-exact identity, the conjugated-norm and ℓ²(π) contractions (mode/rate shape inherited from the plain engine) |
| `abs_one_sub_half_eigvalOf_le_one_sub_half_secondEval` | Mixing (lazy walk) | **the intrinsic rate assembled**: `|1 − μ/2| ≤ 1 − λ₂/2` for every nonzero mode — PSD + signless + the below-gap plumbing, no sign hypothesis anywhere |
| `lazyChiSquareDistance_le_of_connected` | Mixing (lazy walk) | **the headline**: `χ²_lazy(t,x) ≤ (1 − λ₂(L_sym)/2)^{2t}·((πx)⁻¹ − 1)` with connectivity the only graph hypothesis — the continuous family's intrinsic-rate advantage on the discrete side; satisfiable on every bipartite graph where the plain families are not |
| `lazyWalkDistribution_tvDistance_le_of_connected` | Mixing (lazy walk) | the TV corollary: `TV ≤ (1/2)·(1 − λ₂/2)^t·√((πx)⁻¹ − 1)` |
| `klDiv_lazyWalkDistribution_le` | Mixing (lazy walk) | the entropy corollary: `D(ν^L_t ‖ π) ≤ (1 − λ₂/2)^{2t}·((πx)⁻¹ − 1)` — the delivered bridge composed with the lazy bound |

### Mixing — the lazy mixing time (`GraphTheory.Oversmoothing`, 2026-09-01, `proposals/lazy-mixing-time-objects.md`)

The periodicity fix completed at the object level: the `t_mix(ε)` object
and the depth/entrywise ceilings at the lazy law, at the intrinsic rate
`1 − λ₂/2` — with the consumer gate discharged by naming the
bipartite-input instance (the empirical-stationary capstone's "agent
that can only simulate the walk" on paths/trees/grids, where the plain
family's certificate is provably unsatisfiable; the entrywise ceiling
is that extension's hypothesis supplier, the named follow-on).

| Declaration | Area | Description |
| --- | --- | --- |
| `secondEval_normalizedLaplacian_le_two` | Mixing (lazy walk) | **the spectrum cap**: `λ₂(L_sym) ≤ 2` — sortedness + membership + the pointwise signless bound; with the pointwise twin the whole normalized spectrum lives in `[0, 2]`, and the lazy rate is nonnegative by theorem |
| `lazyWalkDistribution_sub_stationaryVec_abs_le` | Mixing (lazy walk) | **the entrywise lazy ceiling at the intrinsic rate**: `|ν_lazy(t) x y − π y| ≤ (1−λ₂/2)^t·√(π y ((πx)⁻¹−1))`, connectivity the only graph hypothesis — the plain twin's certificate hypothesis replaced by the computed rate |
| `lazyWalkDistribution_tvDistance_le_of_depth` | Mixing (lazy walk) | the depth-form TV lazy ceiling past `log(√((πx)⁻¹−1)/(2ε))/log(1/(1−λ₂/2))` at the honest visible `λ₂ < 2` (K₂'s rate-0 corner excluded and documented) |
| `lazyWalkMixingTimeFrom` | Mixing (lazy walk) | **the lazy `t_mix(ε)` object**: the `sInf` over witness times of the lazy TV (the plain object at the lazy law — genuine and finite on the bipartite class where the plain object is junk) |
| `lazyWalkMixingTimeFrom_bddBelow` / `_le_of_cert` / `_spec` / `_anti` | Mixing (lazy walk) | the object's package: the certificate interface, the `csInf_mem` attainment (membership itself the uniform bound), ε-antitonicity |
| `lazyWalkMixingTimeFrom_le_of_connected` | Mixing (lazy walk) | **the intrinsic-rate spectral ceiling**: `t_mix_lazy(ε) ≤ ⌈log(√((πx)⁻¹−1)/(2ε))/log(1/(1−λ₂/2))⌉` under the depth ceiling's hypothesis set |

The lazy family's adversarial fences (`Mixing_QA.lean`'s `LazyFences`
section, 2026-09-02, `proposals/adversarial-fences-lazy-family.md`):
the audit-shaped pass over the whole family above, closing its ten
unfenced load-bearing hypotheses with hypothesis-form negative
witnesses plus isolation companions — the `hd` clauses of
row-stochasticity, mass conservation, and the `t = 0` χ²
normalization at the zero-degree fixture `zdAdj` (the `D⁻¹A` row
junk-zero); the `hnn` clauses of operator- and law-nonnegativity at
the negative off-diagonal fixture `negOffAdj` (`P_L 0 1 = −1/2` —
the existing negative-*diagonal* fixture cannot kill them); the `hA`
clauses of detailed balance, stationarity, and attainment persistence
at the asymmetric loop fixture `asymLoopAdj` (whose lazy law hits `π`
exactly at `t = 1` and leaves it at `t = 2`, making the persistence
hypothesis genuine while the conclusion fails); and both certificate
clauses of the public lazy ℓ²(π) contraction engine (`hrate` on the
triangle at the genuine `3/2`-mode direction with `r = 1/8` below the
factor `1/4`; `hmode` on the edge at the constant mode with the
genuine `r = 0` certificate — the edge spectrum pinned by the
companion `k2_eigvalOf_cases_QA` with no basis control). Recorded
non-fenceable with reasons: the headline's connectivity clause (the
dropped statement stays *true* on disconnected input — proof-shaped,
not truth-shaped) and the depth ceiling's `λ₂ < 2` (junk prevention);
a removable-hypothesis finding recorded for the two nonnegativity
`hd` clauses.

The lazy audit's two priced follow-on fences (`Mixing_QA.lean`'s
`LazyFollowOnFences` section, 2026-09-03, the same proposal's
follow-on delivery record): the conjugated-norm contraction twin
`dotProduct_self_degreeSqrt_mulVec_pow_lazyWalkTransitionMatrix_contraction`'s
`hrate` and `hmode` certificate clauses (the √D-weighted mirrors of
the delivered ℓ²(π) pair — `hrate` on the triangle at the `3/2`-mode
direction with the below-mode `r = 1/8`: `LHS = (1/4)²·4 = 1/4 >
1/16 = (1/8)²·4 = RHS`; `hmode` on the edge at the constant zero mode
with the genuine `r = 0`: `LHS = 2 > 0 = RHS`; the companions reused
verbatim — `conj_twin_isolation_QA` packages the delivered
genuine/fails pairs, the two engines sharing `hmode`/`hrate`
statement-identically) and the lazy `t_mix` object's `_spec`
witness-clause junk corner at the disconnected bipartite fixture
`dK2Adj = K₂ ⊕ K₂` on `Fin 4` (`dK2_lazy_law_succ_QA`: the lazy law
is `δ₀` at time zero and the component-stationary `(1/2,1/2,0,0)` at
every positive time — convergent to the wrong vector;
`dK2_lazy_no_mixing_QA`: no witness exists at `ε = 1/8` since
`TV(ν₀) = 3/4` and `TV(ν_t) = 1/2` at every `t ≥ 1`;
`dK2_lazy_mix_junk_corner_QA`: `t_mix = sInf ∅ = 0`;
`dK2_lazy_mix_spec_fence_QA`: the dropped-`hne` conclusion fails at
`s = 0` — while `dK2_fence_isolation_QA` pins every structural
hypothesis genuine and connectivity exactly the failure: laziness
repairs periodicity, not disconnection). After this, no priced QA
item remains anywhere in the mixing cascade.

### The spectral certificate for the plain walk (the computed rate on non-bipartite input)

*Delivered 2026-09-03 (`proposals/spectral-certificate-plain-walk.md`):
the strict signless engine, the computed `∃ r < 1` certificates, and
the plain family's max-rate joins — the caller-supplied rate hypothesis
of the plain χ²/TV/entrywise ceilings becomes computed on exactly the
class (connected, non-bipartite) where the plain walk mixes. Zero
axioms; QA in `Mixing_QA.lean`'s `SpectralCertificate` section
(certificate pins at the triangle and the looped `r = 0` corner,
unsatisfiability at `C₄`, and the engine's `hnn`/`hconn` fences).*

| Name | Content |
| --- | --- |
| `walk_eq_neg_one_pow_length_mul_of_forall_adj` | edge-sign-flipping potentials flip along walks (`u b = (−1)^|p|·u a`) |
| `eigvalOf_normalizedLaplacian_lt_two_of_odd_walk` | connected + odd closed walk ⟹ every `L_sym` eigenvalue `< 2` (the bipartite dichotomy's strict half) |
| `evals_normalizedLaplacian_lt_two_of_odd_walk` | the sorted-spectrum form of the strict bound |
| `abs_one_sub_eigvalOf_le_max` | `|1 − μ| ≤ max (1 − λ₂) (λ_max − 1)` for every nonzero mode |
| `exists_lt_one_rate_of_odd_walk` / `exists_pos_lt_one_rate_of_odd_walk` | the computed `∃ r < 1` certificate and its `(0,1)` display inflation |
| `chiSquareDistance_le_max_rate` / `walkDistribution_tvDistance_le_max_rate` | the plain χ²/TV bounds at the computed rate (unconditional displays; contractive on the odd-walk class) |
| `walkDistribution_sub_stationaryVec_abs_le_max_rate` | the entrywise plain ceiling at the computed rate (the named consumer, `Oversmoothing.lean`) |
| `walkDistribution_sub_stationaryVec_le_of_depth_of_odd_walk` | the depth-form oversmoothing join at the computed rate (`Oversmoothing.lean`): the plain family's first certificate-free depth ceiling, at the inflated display rate `(max (max (1 − λ₂) (λ_max − 1)) 0 + 1)/2` — the recorded composition landed 2026-09-03; unlike the abs twins the odd-walk clause is load-bearing (on bipartite input the display saturates at `1` and the log threshold degenerates to junk — fenced at `C₄`) |
| `walkDistribution_sub_walkDistribution_le_of_depth_of_odd_walk` | the two-start indistinguishability twin at the computed rate (`Oversmoothing.lean`, landed 2026-09-04): past *both* starts' own computed-rate thresholds any two `t`-step views are within `2ε` at every target vertex — the "representations become indistinguishable" statement certificate-free; the odd-walk clause load-bearing with a genuinely two-start `C₄` witness (opposite-parity starts — same-parity starts coincide at even times) |

### The entropy family's adversarial fences (2026-09-03)

`proposals/adversarial-fences-entropy-family.md` (the third
mixing-cascade audit; `Mixing_QA.lean`'s `EntropyFences` section holds
the walk-level half, `Entropy_QA.lean`'s Section F the generic-layer
half): negative witnesses for the entropy family's 28 unfenced
load-bearing clauses — both mass clauses of Pinsker's inequality (a
junk-negative divergence collapses `√(D/2)` to `0` against `TV = 1/4`
and `1/2`), the `hnn` of `walkDensity_nonneg` (`−2` at `negOffAdj`),
the `hnn`/`ht` of `contWalkDensity_nonneg` and
`contWalkDistribution_nonneg` (closed-form heat kernels: the negative
off-diagonal fixture at `t = 1`, and the `K₂` *backward* semigroup at
`t = −1`, both giving `h(1) = 1 − e² < 0`), the `hA`/`hd` of
`sum_contWalkDistribution` (a new asymmetric-swap fixture
`asymSwapAdj = !![2,0;4,0]` whose walk Laplacian is idempotent — mass
`3 − 2e^{−1} ≠ 1` — and the `zdAdj` junk-zero law against the
`0⁻¹ − 1 = −1` bound), the `hd` of `klDiv_contWalkDistribution_le`
(`0 ≤ −e^{−2λ₂}` by `exp_pos` alone), the `hrate` of
`klDiv_walkDistribution_le` (the triangle at the failing `r = 1/8`:
`log(3/2) ≥ 1/3 > 1/32`), and all four analytic clauses of the entropy
floor `klDiv_walkDistribution_ge_of_eigenpair` (`hμ` at the genuine
kernel eigenpair, `hv` at a fake `μ = 3` mode amplifying the floor to
`2`, `hc` at an undershooting sup bound inflating it to `8`, `hA` at
the swap's genuine `(1, ![0,1])` eigenpair with the strict
`1/2 > log(3/2)`). Recorded non-fenceable: the junk log-of-negative
corners of every `p`-side clause, the vacuous empty-type corners, the
proof-shaped `hconn`, and three removable-hypothesis findings —
notably the continuous nonneg `hA` clauses: the heat kernel
`e^{−t}·e^{tP}` is entrywise nonnegative for any nonnegative `P`,
symmetric or not.

### The Poisson-bridge family's adversarial fences (2026-09-03)

`proposals/adversarial-fences-poisson-bridge-family.md` (the fourth
mixing-cascade audit; `Mixing_QA.lean`'s `PoissonFences` section,
placed after `EntropyFences` and reusing its fixtures): negative
witnesses for the Poisson-bridge family's 28 unfenced load-bearing
clauses — the continuous↔discrete hinge (the Poissonization identity,
the TV convexity toolkit, the comparability/transfer pair) whose QA
(2026-09-01) had never been independently re-read. The fences: the
simplex-diameter lemma's four mass clauses; the head–tail split's
summability clause (junk `0 = 1` at the constant-one sequence); the
convexity bound's `hc` (the alternating geometric weights
`(3/2)(−1/2)ᵏ` against a geometric law family: the signed mixture's
TV `1/4` against the weighted average `3/20`) and `hc1` (a mass-`2`
single-point weight: `1/2 > 1/5`); `hν`/`hν1` by the corpus's first
**divergent-tsum junk** route (the summable weights `1/2·2⁻ᵏ` against
the growing laws `(2ᵏ⁺¹, 1 − 2ᵏ⁺¹)` and `(2ᵏ⁺¹, 2ᵏ⁺¹ − 1)` make every
series in the statement non-summable — both sides junk to `0` against
the honest left TV `1/2`); the Poisson weight's negative time (`−e`);
the `hnn` clauses of the TV ≤ 1 bound, the adjoint-walk contraction
and its power twin (the basis pair's TV triples), and discrete TV
monotonicity (`3/2 → 9/2` at the negative off-diagonal fixture, the
two-step law `(5, −4)` pinned); the `hA` clauses of the whole
Poissonization identity triple — at the asymmetric swap the
constant-density mixture sums to `(3, 0)` against the heat kernel's
genuine drift `(3, 3(1 − e⁻¹))`: the identity is reversibility — of
the stationary power (`Pᵀπ = (1, 0) ≠ π`), and of monotonicity at a
**new fixture** `asymFlowAdj = !![1,1;3,0]]` (`P = [[1/2,1/2],[1,0]]`,
`π = (2/5, 3/5)`): TV rises `1/10 → 7/20`; the rate theorems' `hA` at
the swap's `t = 2` (`1 − e⁻² > 2/3` from `e² > 4`, the mass-drift law
`(1, 2(1 − e⁻²))` pinned through the idempotent-Laplacian kernel);
the `ht` clauses at `t = −1` on the edge (the signed weights
`e·(−1)ᵏ/k!` leave the continuous TV at `e²/2` against the average
`1/2`); and the transfer corollary's `htail` on the triangle at
`t = 1/2` (certificate `ε₁ = 1/6` genuine, tail budget `1/20`
understating the honest head `(3/2)e^{−1/2}`, refuted from a new
series bound `e < 3` — the range-5 partial sum plus the
factorial-vs-geometric tail). `hmix` was already fenced
(`k2_no_discrete_mixing_QA`). Sixteen non-fenceables recorded with
mechanisms (the ten `hd` clauses survive on truth — with `hnn`
retained the junk-collapsed chain is honestly substochastic; the
convexity bound needs no target structure; the factorial beats
matrix-power growth; the transfer's `hnn` is screened by spectral
escape `> 1`), and two removable-hypothesis findings. Helper shelf
additions of note: `not_summable_of_abs_ge`, `exp_one_lt_three`, and
the `pf_tv_lit` two-point TV closed form.

### The regular Cheeger family's adversarial fences (2026-09-04)

`proposals/adversarial-fences-regular-cheeger-family.md` (the audit
method applied to the SGT center namesake — `Cheeger.lean`'s regular
layer: the proved inequality pair at both spellings, the sweep lemma,
the PSD engine, the cut-test-vector junk corners; `Cheeger_QA.lean`'s
`RegularFences` section): negative witnesses for the 17 core + 4
junk-corner load-bearing clauses the pre-discipline QA left unfenced,
each with an isolation companion — the `hnn` clauses at the signed
genuinely-`d = 2`-regular fixture `rcSAdj = !![3,-1;-1,3]]` (`λ₂ = 0`
against `2φ = -1`, `φ²/2 = 1/8`, `d·φ²/2 = 1/4`, `2dφ = -2`, and the
sweep mode's `R = -1`, all four statements refuted at one fixture);
the `hd` clauses at the nonnegative genuinely-`d = 3`-regular
`rcPosAdj = !![2,1;1,2]]` instantiated at claimed wrong degrees
(`d' = 4`: the mode eigenvalue `3/4 > 2φ = 2/3`; `d' = 1`: the
operator collapses to all-`-1`s with `λ₂ = 0 < φ²/2 = 1/18` and the
mode's `R = 0`; `d' = 40`/`d' = 1/8` against the degree-independent
combinatorial `λ₂(L) = 2`); the upper bound's `hdpos` at the zero
matrix with genuine `d = 0` regularity (the identity operator,
`λ₂ = 1 > 2φ = 0` — the junk-conductance `0/0 = 0` corner); the
sweep's `hx0` (the definitional junk Rayleigh `0 < φ²/2 = 1/2`) and
`horth` (the constant vector: in the kernel, `R = 0`, not
self-orthogonal) at `edgeAdj`; the PSD engine's `hA` at the asymmetric
row-regular `rcAsymPsdAdj = !![4,1;3,2]]` (the quadratic form sees the
symmetric part `[[4,2],[2,2]]`, whose `![2,1]`-Rayleigh `26/5`
exceeds the claimed degree `5`: `quadForm = -1/5 < 0`), plus its `hnn`
and `hd`; and the four `cutTestVector_ne_zero` junk corners (the cut
test vector identically `0` at the zero matrix's `hd`/`hdpos`
instantiations, the empty cut, and the full cut). The pinning runs
through two new private Fin 2 engines — the eigenvalue-witness route
(`exists_eigvalOf_eq_of_mulVec_eq_smul` + `eigvalOf_le_evals_last`,
where `secondEval` is the top sorted entry) for lower bounds, and the
whole-space instance of `evals_le_of_linearIndependent` (no PSD, no
kernel) for upper bounds. Recorded non-fenceables: the structural
`hA`s of the five spectrum-carrying statements (consumed by the
conclusions' own symmetry proofs) and `hcard`; and — the survey's
decisive companion-audit finding — four `hdpos` clauses (sweep, lower
bound, both `_laplacian` twins, PSD) whose signed-fixture pricing
failed the isolation companion (`hnn` is a co-hypothesis) and whose
satisfiable nonnegative corner collapses to the zero matrix with the
dropped conclusions surviving. The sweep's genuinely-mathematical `hA`
(`rayleigh`'s symmetry-free display) stays a priced follow-on with the
2-vertex negative analysis recorded.

### The irregular Cheeger family's adversarial fences (2026-09-04)

`proposals/adversarial-fences-irregular-cheeger-family.md` (the audit
method's first application beyond the mixing cascade — the irregular
volume-weighted Cheeger program, the strategy's ring-1 namesake
cluster; `IrregularCheeger_QA.lean`'s `IrregularFences` section):
negative witnesses for the 19 load-bearing clauses the 2026-08-25/26
delivery left unfenced, each with an isolation companion — the easy
direction's `hnn` (`ichSigAdj`: `λ₂ = 0 ≤ 2φ = −2`); the sweep
lemma's `horth` (`K₂`, `f = ![1,2]`: `1/2 ≤ R = 1/5`), `hf0` (`f = 0`:
the definitional junk Rayleigh `0`, `1/2 ≤ 0`), and `hnn` (`f =
![1,−1]`: `R = −2` through the entry-pinned `L_sym`); the cut
theorem's `hf0` and `hnn` (no nonempty proper swept set of a constant
exists; the bound clause `1 ≤ 2R = −4`); the kernel iff's `hconn` (the
component indicator `![1,1,0,0]` at the two-edge fixture — a kernel
vector not a multiple of the stretched constants); the
disconnected-λ₂ theorem's `hnn` at `icSigDisc4Adj` (two disjoint
signed blocks: both block-antisymmetric modes eigenvectors at exactly
`−2` by the subspace Rayleigh–Ritz engine, `λ₂ ≤ −2 ≠ 0`) and `hd` at
`icIsoAdj` (edge ⊕ isolated vertex: `λ₂ = 1 ≠ 0` by the variational
engine with PSD and kernel supplied by hand — the isolated vertex's
junk `D⁻¹ᐟ² = 0` row makes its `L_sym` eigenvalue `1`); the positivity
corollary's `hconn` (`φ ≤ 0`) and `hnn` at the new connected
negative-cut fixture `icNegCutAdj = !![3,1,−3;1,0,1;−3,1,3]` (degrees
`(1,2,1)`, the cut `{0}` of boundary `−2` at unit volume, `φ ≤ −2`);
the Fiedler capstone's `hnn` at the same fixture — λ₂ pinned exactly
`0` (engine bounds `e₀ ≤ −5`, `e₁ ≤ 0`, `e₂ ≤ 2` plus trace `−3`),
the 1-dimensional eigenspace characterized (`span (1, √2, 1)` with the
three witness eigenvectors `(1,0,−1)`/`(1,√2,1)`/`(1,−√2,1)`), so the
sweep vector is provably a nonzero constant and the dropped
conclusion fails on the shape clauses; the sandwich interface's and
the degree-window pair's wrong-constant clauses (`dmin = 5`:
`5·λ₂(L_sym) = 10 ≤ λ₂(L) = 2`; `dmax = 1/2`: `2 ≤ 1` twice); the
volume extraction's `hy` (`y = 1`: `y²` constant, shape) and `hM`
(`y = 0`: every positive superlevel empty — the junk-division corner
at the extraction's own display); and the attainment theorem's
`hcard` at `icOneAdj` (no nonempty proper subset of `Fin 1` exists).

### The effective-resistance core family's adversarial fences
(`EffectiveResistance_QA.lean` and `ResistanceMetric_QA.lean`,
`AdversarialFences` sections, 2026-09-04,
`proposals/adversarial-fences-effective-resistance-family.md`)

Negative witnesses for the electrical cluster's root family's 16
unfenced load-bearing clauses — `Electrical.lean`'s definition,
Dirichlet-bound, confinement, and metric layers — each with an
isolation companion: the existence-flavored statements' `hnn` at the
rank-1 signed 4-cycle `sgnK4Adj` (positive support the connected
4-cycle `1—0—2—3—1`, negative diagonals, every degree `1`, kernel
dimension 3 — the demand `e 0 − e 2` unsolvable through the
kernel-vector pairing `2 ≠ 0`: connected support does not imply
solvability once signs enter; the junk fallback pinned); the
confinement max half's `hnn` at the signed overshoot fixture
`sgnOverAdj` (support the path `0—1—3—2`, one negative edge `(0,2)`,
kernel exactly constants so every demand solvable — the `e 0 − e 1`
solution `![1/2, 0, 1, 1/2]` takes vertex `2` to `1 > max(1/2, 0)`;
no three-vertex signed fixture can kill the max half, the interior
value always solving to a weighted average of the boundary pair);
both confinement halves' `hconn` at the disconnected fixture's
free-constant mechanism (the same-component demand solutions
`![1, 0, 7, 7]` / `![1, 0, -7, -7]` escaping above/below the boundary
values); the Cauchy–Schwarz engine's `hA` (cross term `4² = 16 ≤
(-4)·2 = -8` refuted) and the polarization engine's `hA` (`-4 = 2`
refuted) at the asymmetric nonnegative `ecAsymAdj = !![0,2;1,0]]` —
the family's only two `supportGraph`-free statements, so its only
freely-fenceable symmetry clauses; the Cauchy–Schwarz engine's `hnn`
(cross `1 ≤ 0`) and the Dirichlet bound's `hnn` (ratio `1/2 ≤
R 0 1 = 0`) at the delivered signed fixture; the Dirichlet bound's
`hconn` at the cross-component pair with the genuine-energy indicator
`e 0` (`1 ≤ R 0 2 = 0`); and the metric residuals' junk corners
(triangle `1 ≤ 0 + 0` through a foreign-component middle vertex with
the mirrored demand `e 2 − e 1` unsolvability pinned; `0 < R 0 2 = 0`;
the definiteness iff identifying distinct vertices on both the signed
and disconnected fixtures; explicit `0 ≤ R 2 1 = -2`). Screened
clauses cited rather than duplicated; non-fenceables recorded with
mechanisms in the proposal (the structural `hA`s; the
uniqueness/agreement `hnn` — solvability forces kernel-invariant
voltage differences on symmetric input; `effectiveResistance_symm`'s
`hnn`/`hconn`; `effectiveResistance_nonneg`'s `hconn`; the generic
quadratic's `hE`).
