# Clean-Room SGT Lemma-to-Science Map

**Status:** Provisional review inventory. This document does not approve an
export, copying, publication, or use of quarantined material. The approval gate
in [Clean-Room SGT Export](clean-room-sgt-export.md) still controls every such
action.

## Scope and method

The proposed minimal SGT core is provisionally identified with
`Scaffold/Mathlib/GraphTheory/Spectral.lean`. That file has no local
`Scaffold.*` imports: its Lean dependency closure is Mathlib-only. At the
working-tree state reviewed on 2026-08-18 it contains **84 lemma-like
declarations**: 74 public proved theorems, one public explicit axiom, and nine
private proved helper theorems. The tables below account for all 84.

This is a conceptual and provenance map, not a claim that every helper is a
named scientific law. Rows marked **proof infrastructure** formalize ordinary
finite-set, ordering, dimension, or linear-algebra steps needed to reach a
classical result. Their scientific connection is inherited from the public
theorem they support.

`Export fit` is a technical recommendation only:

- **Core** — a neutral SGT or spectral-linear-algebra interface with clear
  independent use.
- **Support** — proof infrastructure needed by a Core theorem; review and
  reimplement with that theorem.
- **Hold** — mathematically valid, but outside the proposal's deliberately
  narrow first export or requiring separate citation/provenance review.

Line numbers identify the reviewed working-tree version and will drift as the
source changes. The `spectral-proof` column is a historical audit result: at
review time it reported only whether the candidate declaration or its source
file pointed to the (then-present, gitignored, untracked) `spectral-proof/`
directory; the scan did not inspect or reproduce that area's contents. That
directory has since been permanently removed from the working tree
(2026-08-18); the column is retained as evidence that zero pointers existed
before removal, not as a live check.

## Reference key

- **[C]** Fan R. K. Chung, *Spectral Graph Theory*, CBMS 92, AMS, 1997:
  [author-hosted text](https://www.math.ucsd.edu/~fan/cbms.pdf) and
  [AMS catalog record](https://bookstore.ams.org/view?ProductCode=CBMS%2F92).
  Chapters 1–2 cover graph Laplacians, spectra, Rayleigh quotients,
  isoperimetry, and Cheeger-type quantities.
- **[HJ]** Roger A. Horn and Charles R. Johnson, *Matrix Analysis*, 2nd ed.,
  Cambridge University Press, 2012/2013,
  [publisher record and DOI](https://www.cambridge.org/highereducation/books/matrix-analysis/FDA3627DC2B9F5C3DF2FD8C3CC136B48).
  The spectral theorem, Rayleigh quotients, Courant–Fischer, trace/eigenvalue
  identities, projectors, and interlacing are classical matrix analysis.
- **[F]** Miroslav Fiedler, “Algebraic connectivity of graphs,”
  *Czechoslovak Mathematical Journal* 23 (1973), 298–305,
  [DML-CZ record and open PDF](https://dml.cz/handle/10338.dmlcz/101168).
- **[VL]** Ulrike von Luxburg, “A Tutorial on Spectral Clustering,”
  *Statistics and Computing* 17 (2007), 395–416,
  [Max Planck record](https://is.mpg.de/publications/4488),
  DOI 10.1007/s11222-007-9033-z. This connects Laplacians, cuts, Rayleigh
  relaxations, and low-frequency eigenvectors to data clustering.
- **[SM]** Jianbo Shi and Jitendra Malik, “Normalized Cuts and Image
  Segmentation,” *IEEE TPAMI* 22 (2000), 888–905,
  [DOI record](https://doi.org/10.1109/34.868688). This is a canonical
  scientific use of graph cuts and spectral relaxations in computer vision.
- **[GSP]** David I. Shuman et al., “The Emerging Field of Signal Processing
  on Graphs,” *IEEE Signal Processing Magazine* 30 (2013), 83–98,
  [EPFL record](https://infoscience.epfl.ch/entities/publication/da34f8f8-5b02-4602-b635-c8a31ca1bd53),
  DOI 10.1109/MSP.2012.2235192. This supplies the graph-Fourier and modal-filter
  interpretation of eigenbases and spectral projectors.
- **[DS]** Peter G. Doyle and J. Laurie Snell, *Random Walks and Electric
  Networks*, MAA, 1984,
  [author-hosted open edition](https://math.dartmouth.edu/~doyle/docs/walkspdf/walks.pdf).
  This supplies the electrical-network interpretation of Laplacian equations,
  potentials, currents, and energy.
- **[T]** Petter Holme and Jari Saramäki, “Temporal Networks,”
  *Physics Reports* 519 (2012), 97–125,
  [Aalto publication record](https://research.aalto.fi/en/publications/temporal-networks/),
  DOI 10.1016/j.physrep.2012.03.001.

## 1. Degree matrices, Laplacians, and conservation

| Declaration | Kind | Classical anchor | Well-known science connection | Export fit | `spectral-proof` |
| --- | --- | --- | --- | --- | --- |
| `degreeMatrix_off_diagonal` (`Spectral.lean:100`) | Proved | A degree matrix is diagonal [C] | Node strength is a local scalar in network diffusion and clustering | Core | No pointer |
| `degreeMatrix_diagonal` (`:105`) | Proved | `Dᵢᵢ = deg(i)` [C] | Encodes total interaction rate or weighted connectivity at a node | Core | No pointer |
| `degreeMatrix_diagonal_nonneg` (`:111`) | Proved | Nonnegative weights give nonnegative degrees [C] | Physical conductances, transition rates, and similarities are nonnegative | Core | No pointer |
| `degreeMatrix_symmetric` (`:118`) | Proved | Every real diagonal matrix is symmetric [HJ] | Makes the degree operator self-adjoint, enabling real modal analysis | Core | No pointer |
| `laplacian_symmetric` (`:127`) | Proved | `L = D-A` is symmetric when `A` is symmetric [C] | Undirected diffusion, spring, and resistor operators have real orthogonal modes | Core | No pointer |
| `laplacian_ones_in_kernel` (`:134`) | Proved | Laplacian row sums vanish [C] | Conservation law: a spatially constant state is stationary under diffusion or consensus | Core | No pointer |

## 2. Spectrum, eigenmodes, and spectral projectors

| Declaration | Kind | Classical anchor | Well-known science connection | Export fit | `spectral-proof` |
| --- | --- | --- | --- | --- | --- |
| `isHermitian_of_isSymm` (`:161`) | Proved | Real symmetric matrices are Hermitian [HJ] | Bridges real network/covariance operators to the self-adjoint spectral theorem | Core | No pointer |
| `length_sortedEvals` (`:167`) | Private proved helper | Sorting preserves multiset cardinality | Proof infrastructure for enumerating all physical or graph modes | Support | No pointer |
| `evals_sorted` (`:188`) | Proved | Eigenvalues may be ordered nondecreasingly [HJ] | Orders modes from low to high energy/frequency | Core | No pointer |
| `lambda2_eq_secondEval` (`:220`) | Proved | Algebraic connectivity is the Laplacian's second eigenvalue [F] | Identifies the graph connectivity scale used in clustering, diffusion, and synchronization | Core | No pointer |
| `evals_mem_eigvalOf` (`:245`) | Proved | Sorting permutes the eigenvalue multiset [HJ] | Ensures every reported spectral mode corresponds to an actual eigenpair | Core | No pointer |
| `spectralProjector_symmetric` (`:277`) | Proved | Orthogonal spectral projectors are self-adjoint [HJ] | A graph-frequency filter preserves real symmetric modal geometry [GSP] | Core | No pointer |
| `initialProjector_symmetric` (`:293`) | Proved | Low-mode projector is self-adjoint [HJ] | Low-frequency graph subspaces used for smoothing, compression, and clustering [GSP] | Core | No pointer |
| `initialProjector_congr` (`:302`) | Proved | Functional calculus respects equality [HJ] | Stable API bookkeeping when the same scientific operator is rewritten | Support | No pointer |
| `eigvecOf_inner` (`:321`) | Proved | Eigenvectors of a real symmetric matrix form an orthonormal basis [HJ] | Independent normal modes in vibration, covariance analysis, and graph Fourier analysis [GSP] | Core | No pointer |
| `eigvecOf_complete` (`:333`) | Proved | Resolution of the identity by an orthonormal eigenbasis [HJ] | Any signal or physical state decomposes completely into modes [GSP] | Core | No pointer |
| `eigvalOf_le_of_quadForm_nonpos` (`:364`) | Proved | Rayleigh-quotient sign bounds eigenvalues [HJ] | Certifies dissipative or negative-semidefinite operators from energy measurements | Core | No pointer |
| `eigvalOf_sum_eq_trace` (`:386`) | Proved | Trace equals the sum of eigenvalues [HJ] | In covariance analysis, total variance equals summed modal variance; in mechanics it aggregates modal stiffness | Core | No pointer |
| `spectralProjector_idempotent` (`:411`) | Proved | Orthogonal projection satisfies `P²=P` [HJ] | Reapplying an ideal modal/graph-frequency filter changes nothing [GSP] | Core | No pointer |
| `spectralProjector_eq_zero` (`:468`) | Proved | A spectral cutoff below all eigenvalues selects no modes [HJ] | An ideal filter with an empty passband outputs zero [GSP] | Core | No pointer |
| `spectralProjector_eq_one` (`:480`) | Proved | A cutoff above all eigenvalues selects every mode [HJ] | An all-pass graph spectral filter is the identity [GSP] | Core | No pointer |
| `initialProjector_idempotent` (`:493`) | Proved | Low-eigenspace projector is idempotent [HJ] | Repeated low-frequency projection in denoising or clustering is stable [GSP] | Core | No pointer |

## 3. Cuts, volume, conductance, and isoperimetry

| Declaration | Kind | Classical anchor | Well-known science connection | Export fit | `spectral-proof` |
| --- | --- | --- | --- | --- | --- |
| `vol_nonneg` (`:525`) | Proved | Weighted set volume is nonnegative [C] | Cluster mass or stationary mass cannot be negative | Core | No pointer |
| `boundary_nonneg` (`:529`) | Proved | Cut capacity is nonnegative [C] | Interface cost, flow capacity, or cross-cluster similarity is nonnegative | Core | No pointer |
| `conductance_nonneg` (`:534`) | Proved | Conductance is a nonnegative bottleneck ratio [C] | Quantifies leakage/mixing between communities [VL] | Core | No pointer |
| `cheegerConstant_nonneg` (`:541`) | Proved | Isoperimetric minimum is nonnegative [C] | A network's best normalized bottleneck has nonnegative cost | Core | No pointer |
| `conductance_ge_cheegerConstant` (`:549`) | Proved | An infimum is below every admissible cut [C] | Any proposed segmentation is no better than the optimum bottleneck value [VL, SM] | Core | No pointer |
| `vol_compl` (`:576`) | Proved | Volume partitions over a set and its complement [C] | Conservation of total network mass across a binary partition | Core | No pointer |
| `boundary_compl` (`:585`) | Proved | Undirected cut capacity is complement-invariant [C] | An interface has the same weight viewed from either side [SM] | Core | No pointer |
| `conductance_compl` (`:598`) | Proved | Conductance is complement-invariant [C] | Binary clustering score does not depend on which region is named foreground [SM] | Core | No pointer |
| `boundary_empty` (`:604`) | Proved | Empty set has zero boundary [C] | Empty segmentation carries no interface | Core | No pointer |
| `boundary_univ` (`:609`) | Proved | Whole vertex set has zero external boundary [C] | A closed network has no cut against an exterior vertex set | Core | No pointer |

## 4. Dirichlet energy, positivity, connectivity, and Laplacian equations

| Declaration | Kind | Classical anchor | Well-known science connection | Export fit | `spectral-proof` |
| --- | --- | --- | --- | --- | --- |
| `laplacian_quadForm` (`:623`) | Proved | Dirichlet identity `xᵀLx = ½∑wᵢⱼ(xᵢ-xⱼ)²` [C] | Dissipated resistor power, spring energy, graph smoothness, and diffusion energy [DS, GSP] | Core | No pointer |
| `laplacian_psd` (`:692`) | Proved | Nonnegative weighted Laplacians are positive semidefinite [C] | Energy is nonnegative; diffusion/consensus modes are stable | Core | No pointer |
| `supportGraph_adj` (`:732`) | Proved | Positive weights define the underlying unweighted support graph | Separates topology (“an interaction exists”) from interaction strength | Core | No pointer |
| `eq_of_laplacian_mulVec_eq_zero_of_pos_weight` (`:740`) | Proved | Harmonic zero-energy states agree across a positive edge [C] | Equipotential endpoints carry no current; consensus equalizes neighboring states [DS] | Core | No pointer |
| `eq_of_supportGraph_walk` (`:764`) | Proved | Equality propagates along a connected path [C] | Equipotential or consensus state propagates through a connected component [DS] | Core | No pointer |
| `exists_const_of_laplacian_mulVec_eq_zero` (`:780`) | Proved | Kernel of a connected Laplacian consists of constants [C, F] | Connected resistor networks have potentials unique up to gauge; consensus equilibria are uniform [DS] | Core | No pointer |
| `laplacian_mulVec_const` (`:792`) | Proved | Every constant vector lies in the Laplacian kernel [C] | Uniform temperature/opinion/potential is stationary | Core | No pointer |
| `laplacian_mulVec_eq_zero_iff_exists_const` (`:804`) | Proved | Connected Laplacian kernel characterization [C, F] | Exactly characterizes steady states of connected diffusion or consensus | Core | No pointer |
| `laplacian_kernel_eq_span_onesVec` (`:817`) | Proved | `ker L = span{1}` for a connected graph [C, F] | One zero mode expresses conservation; all other modes restore variation | Core | No pointer |
| `laplacian_mulVec_apply` (`:855`) | Proved | Pointwise Laplacian is a weighted difference sum [C] | Discrete diffusion/flux balance at a node | Core | No pointer |
| `laplacian_mulVec_eq_zero_of_forall_reachable` (`:877`) | Proved | Componentwise-constant functions are harmonic [C] | Each disconnected component may settle at its own equilibrium | Core | No pointer |
| `laplacian_mulVec_eq_zero_iff_forall_reachable` (`:898`) | Proved | Kernel vectors are exactly componentwise constants [C] | Counts independent equilibria or conserved component offsets | Core | No pointer |
| `laplacian_dotProduct_mulVec` (`:933`) | Proved | Symmetric-Laplacian Green/Dirichlet pairing identity [C] | Reciprocity of discrete diffusion and resistor networks [DS] | Core | No pointer |
| `dotProduct_eq_zero_of_laplacian_mulVec_eq_zero` (`:944`) | Proved | Solvability compatibility: loads are orthogonal to the kernel [HJ] | Kirchhoff current balance requires total injected current zero [DS] | Core | No pointer |

## 5. Eigenbasis expansion and Poisson solvability

| Declaration | Kind | Classical anchor | Well-known science connection | Export fit | `spectral-proof` |
| --- | --- | --- | --- | --- | --- |
| `mulVec_eigvecOf_sum_apply` (`:955`) | Proved | Spectral synthesis commutes with a diagonalizable operator [HJ] | Applying a linear physical/network operator scales each normal mode independently [GSP] | Core | No pointer |
| `eigvecOf_expansion_apply` (`:1001`) | Proved | Fourier expansion in an orthonormal eigenbasis [HJ] | Reconstructs a graph signal or physical state from modal coefficients [GSP] | Core | No pointer |
| `dotProduct_eigvecOf` (`:1022`) | Proved | Parseval/resolution identity in eigen-coordinates [HJ] | Inner products and signal energy are preserved in the graph Fourier domain [GSP] | Core | No pointer |
| `dotProduct_eigvecOf_mulVec` (`:1055`) | Proved | Spectral coefficients of `Mx` are eigenvalue-scaled [HJ] | Frequency response of a graph or physical linear operator [GSP] | Core | No pointer |
| `quadForm_eigvalOf` (`:1068`) | Proved | Quadratic form is an eigenvalue-weighted modal energy [HJ] | Decomposes stiffness, variance, or graph smoothness across modes [GSP] | Core | No pointer |
| `quadForm_eigvecOf_self` (`:1079`) | Proved | An eigenvector's quadratic energy is its eigenvalue times norm squared [HJ] | Each normal mode has its characteristic energy/frequency scale | Core | No pointer |
| `eigvecOf_ortho_onesVec_of_mulVec_eq_zero` (`:1099`) | Proved | Nonzero modes are orthogonal to a zero mode [HJ] | Nonconstant diffusion/vibration modes have zero mean when constants span equilibrium | Core | No pointer |
| `eigvecOf_ortho_onesVec` (`:1135`) | Proved | Positive Laplacian eigenmodes are orthogonal to constants [C, F] | Fiedler and higher modes represent balanced deviations from a uniform state | Core | No pointer |
| `exists_mulVec_eq_of_zero_comp` (`:1151`) | Proved | Symmetric linear equation solvability on the kernel's orthogonal complement [HJ] | Finite-dimensional Fredholm alternative; solves compatible force/current/load equations | Core | No pointer |
| `exists_laplacian_mulVec_eq_of_sum_eq_zero` (`:1200`) | Proved | Connected graph Poisson equation is solvable for zero-sum load [C, DS] | Voltages exist for balanced current injection; analogous heat/source balance | Core | No pointer |
| `exists_laplacian_mulVec_eq_single_sub_single` (`:1231`) | Proved | Unit source–sink Laplacian equation [DS] | Voltage potentials exist for one unit of current sent between two vertices | Core | No pointer |

## 6. Second eigenvalue and algebraic connectivity

| Declaration | Kind | Classical anchor | Well-known science connection | Export fit | `spectral-proof` |
| --- | --- | --- | --- | --- | --- |
| `filter_length_eq_card_filter` (`:1271`) | Private proved helper | List/multiset filtering preserves counted multiplicity | Proof infrastructure for selecting eigenvalues below a threshold | Support | No pointer |
| `sorted_filter_le_length` (`:1286`) | Private proved helper | Order statistic count bound | Proof infrastructure for identifying the second spectral order statistic | Support | No pointer |
| `filter_eq_two_of_head` (`:1333`) | Private proved helper | Multiplicity count at the first two sorted entries | Proof infrastructure for the second-eigenvalue variational theorem | Support | No pointer |
| `evals_one_le_max_of_ne` (`:1363`) | Proved | Second order statistic is bounded by any eigenvalue except a chosen minimum representative [HJ] | Handles repeated modes when isolating algebraic connectivity | Core | No pointer |
| `exists_ne_eigvalOf_of_evals_head_eq` (`:1414`) | Proved | A second eigenvalue has a distinct eigenbasis index when dimension is at least two [HJ] | Produces a nonconstant candidate mode even with eigenvalue multiplicity | Core | No pointer |
| `secondEval_variational` (`:1489`) | Proved | Courant–Fischer/Rayleigh characterization of the second eigenvalue [HJ] | Basis of spectral relaxation, connectivity estimates, and low-frequency mode extraction [VL, F] | Core | No pointer |
| `secondEval_le_rayleigh` (`:1793`) | Proved | Second eigenvalue is below every admissible orthogonal Rayleigh quotient [HJ] | Turns a constructed test signal or cut vector into a certified spectral bound [VL] | Core | No pointer |
| `lambda2_variational` (`:1840`) | Proved | Fiedler value as minimum Laplacian Rayleigh quotient orthogonal to constants [F, C] | Core relaxation behind graph partitioning, connectivity, and image segmentation [VL, SM] | Core | No pointer |

## 7. General Courant–Fischer min–max

| Declaration | Kind | Classical anchor | Well-known science connection | Export fit | `spectral-proof` |
| --- | --- | --- | --- | --- | --- |
| `filter_nil_of_forall_lt` (`:1872`) | Private proved helper | Empty threshold-filter lemma | Proof infrastructure for spectral order statistics | Support | No pointer |
| `sorted_filter_ge_length_of_le_get` (`:1885`) | Private proved helper | At least `k+1` sorted entries lie below the `k`-th threshold | Proof infrastructure for min–max multiplicity counting | Support | No pointer |
| `sorted_filter_lt_length_of_eq_get` (`:1915`) | Private proved helper | At most `k` sorted entries lie strictly below the `k`-th threshold | Proof infrastructure for min–max multiplicity counting | Support | No pointer |
| `card_filter_eigvalOf_eq` (`:1951`) | Private proved helper | Transfers eigenvalue multiset counts to eigenbasis-index counts | Proof infrastructure joining sorted spectra to concrete modes | Support | No pointer |
| `card_filter_eigvalOf_lt_evals_le` (`:1966`) | Proved | Multiplicity bound below the `k`-th eigenvalue [HJ] | Counts how many modes can lie below a chosen energy/frequency threshold | Core | No pointer |
| `succ_le_card_filter_eigvalOf_le` (`:1977`) | Proved | Multiplicity bound at or below the `k`-th eigenvalue [HJ] | Guarantees a sufficiently large low-frequency/modal subspace | Core | No pointer |
| `eigvecOf_dotProduct` (`:1990`) | Proved | Eigenbasis orthonormality in dot-product notation [HJ] | Decoupled normal modes and graph Fourier coordinates [GSP] | Core | No pointer |
| `linearIndependent_eigvecOf_finset` (`:1997`) | Proved | Every subfamily of an orthonormal basis is independent [HJ] | Selected modes retain distinct physical/signal degrees of freedom | Core | No pointer |
| `finrank_span_eigvecOf_finset` (`:2033`) | Proved | Span dimension equals the size of an independent modal family [HJ] | Counts retained degrees of freedom in modal reduction | Core | No pointer |
| `dotProduct_self_pos` (`:2043`) | Private proved helper | A nonzero real vector has positive squared norm | Proof infrastructure ensuring a Rayleigh quotient denominator is positive | Support | No pointer |
| `rayleigh_le_evals_of_forall_dotProduct_eq_zero` (`:2058`) | Proved | Rayleigh quotient of a low-mode vector is at most the spectral threshold [HJ] | Certifies energy/frequency bounds for band-limited states [GSP] | Core | No pointer |
| `evals_le_rayleigh_of_forall_dotProduct_eq_zero` (`:2085`) | Proved | Rayleigh quotient of a high-mode vector is at least the spectral threshold [HJ] | Certifies lower energy/frequency bounds after removing low modes [GSP] | Core | No pointer |
| `dotProduct_eigvecOf_eq_zero_of_mem_span` (`:2113`) | Proved | A vector in a modal span is orthogonal to basis modes outside it [HJ] | Exact band-limiting in modal or graph-Fourier analysis [GSP] | Core | No pointer |
| `exists_submodule_forall_rayleigh_le` (`:2143`) | Proved | Courant–Fischer optimal low-dimensional subspace, existence direction [HJ] | Ritz/modal reduction finds a subspace whose maximum energy is controlled | Core | No pointer |
| `exists_ne_mem_rayleigh_ge_of_finrank_eq` (`:2170`) | Proved | Courant–Fischer competitor direction [HJ] | No competing subspace of the same dimension can avoid a mode at the threshold energy | Core | No pointer |
| `evals_min_max` (`:2251`) | Proved | General Courant–Fischer min–max theorem [HJ] | Variational foundation for vibration modes, PCA/covariance modes, spectral clustering, and eigenvalue approximation | Core | No pointer |

## 8. Temporal update and principal-submatrix interlacing

| Declaration | Kind | Classical anchor | Well-known science connection | Export fit | `spectral-proof` |
| --- | --- | --- | --- | --- | --- |
| `eventUpdate_preserves_symmetry` (`:2289`) | Proved | Symmetric rank-two edge updates preserve symmetry | Timestamped edge addition/removal in temporal interaction networks [T] | Hold | No pointer |
| `principalSubmatrix_symmetric` (`:2309`) | Proved | Principal submatrices of symmetric matrices are symmetric [HJ] | Restricting a covariance, stiffness, or network operator to observed/retained coordinates preserves self-adjointness | Core | No pointer |
| `eigen_interlacing_principal_submatrix` (`:2337`) | **Explicit axiom** | Cauchy interlacing theorem [HJ] | Bounds how modal frequencies/eigenvalues change under coordinate or vertex deletion | Hold pending axiom/citation review | No pointer |

## `spectral-proof/` pointer audit (historical — directory removed 2026-08-18)

At review time, the candidate source file had **no direct pointer** to
`spectral-proof/`: no import, path literal, URL, comment reference, or
symlink was found anywhere under the live `Scaffold/`, `proposals/`, `docs/`,
`index/`, or `scripts/` trees. A follow-on comparison (recorded in
`cdx-clean-assess.md`) went further, diffing all 215 declaration names and
searching all distinctive vocabulary across `spectral-proof/`'s 22 Lean files
against the entire tracked repository, and found the same result: no
meaningful overlap. `spectral-proof/` was untracked and gitignored throughout
its presence in this working tree, and has since been permanently removed
(`rm -rf`, 2026-08-18); the `.gitignore` entry that referenced it has been
removed as well.

The repository-wide path scan, at review time, found these references:

| Location | What it points to | Export significance |
| --- | --- | --- |
| `research/archive/oil-strategy.md:23,33` | Names a proprietary-theory layer and an assumptions file under `spectral-proof/` | Historical/archive-only pointer, left unedited per the repository instruction not to edit archive content. Excluded from export regardless. |
| `research/archive/status/STATUS.md:25,28` | Records an old Mathlib symlink/build arrangement involving `spectral-proof/` | Historical provenance hazard, left unedited for the same reason. Do not reuse its dependency path or copy this generated status record. |
| `research/archive/status/QA_SCOREBOARD.md:120,121,126` | Records the same old dependency provenance and contrasts QA files with `spectral-proof/` | Historical provenance hazard, left unedited for the same reason. Excluded from export and from evidentiary claims about independent origin. |

These three archive files are the only remaining textual references to
`spectral-proof` anywhere in this repository, and are deliberately untouched:
`AGENTS.md` prohibits editing `research/archive/` except archive metadata,
and rewriting historical record to remove a past connection would itself be
the wrong kind of provenance cleanup.

This negative result was, and remains, deliberately narrow: absence of a
textual pointer never established independent provenance by itself — the
follow-on comparison in `cdx-clean-assess.md` is what actually tested that,
and manual provenance review and counsel approval remain mandatory
regardless of either result.

## Completeness ledger

- Basic structural facts: 6 declarations.
- Spectrum and projectors: 16 declarations.
- Cuts and conductance: 10 declarations.
- Dirichlet/connectivity/Laplacian equations: 14 declarations.
- Eigenbasis expansion and Poisson solvability: 11 declarations.
- Second eigenvalue: 8 declarations.
- General Courant–Fischer: 16 declarations.
- Temporal update and interlacing: 3 declarations.
- **Total: 84 of 84 declarations mapped.**

The count should be regenerated before any review or export because the source
is actively changing. Definitions such as `WAdj`, `laplacian`, `rayleigh`,
`evals`, `spectralProjector`, `conductance`, and `eventUpdate` are discussed by
the rows that consume them, but are not counted as lemmas. QA declarations are
also outside this inventory; the export proposal permits only the minimal QA
selected in a later file-level approval review.

## OPS Critique (2026-08-18)

Independent review of this map and its `clean-room-sgt-export.md` update,
verified against the working tree rather than taken on the author's own
summary.

**Declaration coverage: exact.** Every `theorem`/`lemma`/`axiom` name in
`Spectral.lean` was extracted and diffed against every declaration name in
this map — zero missing, zero stale or hallucinated entries. The 84 count
(74 public theorems, 1 axiom, 9 private helpers) is exactly right, and the
20 excluded raw `def`s match this document's own stated scope precisely.

**Classification discipline: correct where it matters most.** The single
axiom, `eigen_interlacing_principal_submatrix`, is held at "Hold pending
axiom/citation review" rather than promoted to Core despite carrying a
legitimate Horn & Johnson citation — the right call under the clean-room
policy's caution, since an admitted-not-proved statement shouldn't carry
proved-theorem export confidence. `eventUpdate_preserves_symmetry` is
similarly held rather than defaulted to Core.

**Citations are real, not decorative.** Chung, Horn–Johnson, Fiedler, von
Luxburg, Shi–Malik, Shuman et al., Doyle–Snell, and Holme–Saramäki each
carry an actual DOI, publisher record, or author-hosted PDF — spot-checked,
not name-dropped.

**The `spectral-proof/` audit is genuine due diligence.** Confirmed
independently that the directory is real, substantial, and gitignored; the
claim that only `.gitignore` and archived status records reference it holds.

**Scope boundary respected throughout.** Both this document's own header
and the pointer paragraph added to `clean-room-sgt-export.md` repeat,
explicitly, that this is an inventory and does not authorize export — no
overreach past that boundary was found.

**One gap, since resolved.** The originating status note (`cdx-cleanroom.md`,
an untracked scratch file, since deleted) claimed markdown-link verification
had passed; re-running `scripts/check_markdown_links.py` at review time
found broken links, but they traced entirely to that scratch file's own use
of absolute local filesystem paths to reference this map and the export
proposal — not to anything in either real deliverable. Both are confirmed
clean now that the scratch file is gone.

**Verdict: A-.** Rigorous, accurate, and appropriately cautious about what
it does and doesn't authorize. Docked only for the overstated verification
claim in the (now-removed) originating summary, not for the substance of
the map itself.
