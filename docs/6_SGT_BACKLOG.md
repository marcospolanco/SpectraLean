# SGT Backlog

**Status:** Canonical backlog for the broad spectral-graph-theory program  
**Last reviewed:** August 17, 2026

This is the bounded, center-first backlog required by the strategy's
center-out policy. Items are ranked by concrete reuse: each names the
existing declarations it composes with, the consumers it unlocks, and
its dependency path back to the SGT center. New bridge or application
work is accepted only against an item listed here (or a revision of this
document that argues the leverage case).

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

### 3. Expansion and cut interfaces

*Have:* `vol`, `boundary`, `conductance`, `cheegerConstant`
(volume-based), the **proved** Cheeger upper bound (easy direction,
`cheeger_upper_bound`, retired from axiom 2026-08-18 with the
`cutTestVector` interface), the admitted Cheeger lower bound (hard
direction) for regular graphs; cut duality delivered 2026-08-17
(`vol_compl`, `boundary_compl`, `conductance_compl`, degenerate-cut
guards — proved; cuts are partition-valued, the interface sweep cuts
and sparsest-cut shapes assume).

*Plan:* edge-boundary and uniform-weight variants of conductance;
sparsest-cut statement shapes; cut/measure duality interfaces used by
local algorithms. Each variant must name the algorithm consumer that
needs it before admission.

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
`proposals/fiedler-partitioning.md`); **Phase B delivered 2026-08-23**
— `cheeger_cut_existence`, the classical Cheeger cut-existence
certificate: on every connected `d`-regular graph a nonempty proper
`S` exists with `conductance S ^ 2 ≤ 2 · lambda2 / d` (the recorded
operator gate dissolved by the same day's `cheeger_lower_bound`
retirement; pure hard crust, assembled from the proved sweep lemma at
the Fiedler vector, attainment of the conductance minimum, and the
Rayleigh transfer — the certificate is existential over the minimizer,
with the *swept-level-set* extraction the named strengthening
follow-on); walk mixing through the transition spectrum.

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
interface set is complete). What remains gated on this item is the
*inequality* layer — Dirichlet/functional inequalities, dissipation,
log-Sobolev — which stays conditional on consumer demand per the
icebox note.

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
`6 ≠ 3`) exactly as the proposal's calibration demands. The family's
remaining items are unchanged: the definiteness residual
`R u v = 0 ↔ u = v`, the resistance metric (triangle inequality),
Matrix–Tree, and Kirchhoff network theorems beyond the conservation
bridge — the last two still gated on a named consumer.

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
