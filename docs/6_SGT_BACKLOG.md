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
(`walkTransitionMatrix_row_sum`); the *eigenvalue-list* transfer is the
precisely named residual gap — `L_walk` is not symmetric for irregular
graphs, so `evals` does not apply to it, and a
characteristic-polynomial-roots interface for non-symmetric matrices is
absent from the pinned Mathlib.

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
`proposals/fiedler-partitioning.md`); the open remainder is **Phase B**
— a certified conductance bound on `fiedlerPartition`, whose trust
level is exactly the Cheeger hard direction's (admitted until proved);
walk mixing through the transition spectrum.

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

### 6. Thermodynamics / statistical mechanics (conditional)

*Gated on item 1–2 stability:* entropy and reversibility interfaces,
Dirichlet/functional inequalities, dissipation. No admission before the
Markov prerequisites are stable.

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
- Removed subgaussian statements (moment growth, linear combinations,
  centering, sums) are re-admitted only when a consumer names them.
- Horn–Johnson/Chung locator confirmation awaits a physical or publisher
  copy; numbers are not invented.

## Source provenance

Backlog ranking follows [Strategy](1_STRATEGY.md) (center-out, leverage
test) and the operator's 2026-08-17 broad-SGT reorientation recorded in
[AGENT_ACTIVITY.md](AGENT_ACTIVITY.md).
