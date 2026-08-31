import Scaffold.Mathlib.Core.RandomVariable
import Scaffold.Mathlib.Core.Norms
import Scaffold.Mathlib.Core.MatrixUpdates
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter
import Scaffold.Mathlib.GraphTheory.Electrical
import Scaffold.Mathlib.GraphTheory.ElectricalFlow
import Scaffold.Mathlib.GraphTheory.Foster
import Scaffold.Mathlib.GraphTheory.Expander
import Scaffold.Mathlib.GraphTheory.SpectralCertificates
import Scaffold.Mathlib.GraphTheory.Tikhonov
import Scaffold.Mathlib.GraphTheory.Band
import Scaffold.Mathlib.GraphTheory.Cheeger
import Scaffold.Mathlib.GraphTheory.Fiedler
import Scaffold.Mathlib.GraphTheory.RandomWalk
import Scaffold.Mathlib.GraphTheory.Normalized
import Scaffold.Mathlib.GraphTheory.IrreducibleStationary
import Scaffold.Mathlib.GraphTheory.PageRank
import Scaffold.Mathlib.GraphTheory.DirectedMixing
import Scaffold.Mathlib.GraphTheory.Stationary
import Scaffold.Mathlib.GraphTheory.Mixing
import Scaffold.Mathlib.GraphTheory.Oversmoothing
import Scaffold.Mathlib.GraphTheory.Heat
import Scaffold.Mathlib.GraphTheory.Directed
import Scaffold.Mathlib.GraphTheory.Magnetic
import Scaffold.Mathlib.GraphTheory.Krylov
import Scaffold.Mathlib.GraphTheory.PolyFilter
import Scaffold.Mathlib.GraphTheory.ClusterProjector
import Scaffold.Mathlib.GraphTheory.FunctionalCalculus
import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.Mathlib.GraphTheory.Multiway
import Scaffold.Mathlib.GraphTheory.Poincare
import Scaffold.Mathlib.GraphTheory.Signed
import Scaffold.Mathlib.GraphTheory.AlonBoppana
import Scaffold.Mathlib.GraphTheory.Dynamics
import Scaffold.Mathlib.Dynamics.DiscreteAffine
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.BandDavisKahan
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.ProjectionGap
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Duhamel
import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent
import Scaffold.Mathlib.LinearAlgebra.PerronFrobenius
import Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence
import Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein
import Scaffold.Mathlib.Probability.Concentration.Matrix.Basic
import Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Matrix.Bernstein
import Scaffold.Mathlib.Probability.Concentration.Matrix.Azuma
import Scaffold.Mathlib.Probability.BernoulliProduct
import Scaffold.Mathlib.Probability.IIDProduct
import Scaffold.Mathlib.GraphTheory.Sparsification
import Scaffold.Mathlib.GraphTheory.EdgePerturbation
import Scaffold.Mathlib.InformationTheory.Entropy
import Scaffold.Derived.EventStream
import Scaffold.Derived.ProjectorDrift
import Scaffold.Derived.SparsificationTail
import Scaffold.Derived.EdgePerturbationTail
import Scaffold.Derived.EdgePerturbationDrift
import Scaffold.Derived.EmpiricalStationary

/-!
# Scaffold library root

The default `lake build` target. The umbrella imports every public
module that the current milestone certifies: the SGT center
(`GraphTheory.Spectral`), the `SimpleGraph` interop adapter
(`GraphTheory.SimpleGraphAdapter`, completing the two-directional
bridge with `supportGraph`), the electrical crust
(`GraphTheory.Electrical`, defining effective resistance by the
potential equation), its flow-routing extension
(`GraphTheory.ElectricalFlow`, Thomson's principle and Rayleigh
monotonicity), Foster's theorem
(`GraphTheory.Foster`, the conductance-weighted resistance identity
`∑_{u<v} w_e R_e = n - 1`), the expander discrepancy core and the
Expander Mixing Lemma itself (`GraphTheory.Expander`, steps 1–2 of the
decidable-certificates program: subset edge weights, the
centered-indicator decomposition, the Rayleigh sandwich on `1⊥`, and
the mixing-lemma discrepancy bound with its spectral hypothesis in
Laplacian terms), the computable certificate layer
(`GraphTheory.SpectralCertificates`, Step 3 of the
decidable-certificates program: the ℚ specification checker with its
soundness theorem `lambda2_le_of_certificate` consuming the proved
`lambda2_variational`, and the kernel-verifiable ℤ cross-multiplied
twin bridged by proved cross-multiplication lemmas), Tikhonov
regularization in the Laplacian eigenbasis
(`GraphTheory.Tikhonov`, the graph-signal smoothing operator: the
eigenbasis-defined minimizer of `‖x−y‖² + (1/π)·xᵀLx`, its
eigencoefficient shrinkage identity, the normal equation with its
converse characterization, minimality and uniqueness through the
strict-convexity decomposition, mean preservation, and the
not-a-projection (idempotence-failure) theorem), the two-sided
spectral band projectors (`GraphTheory.Band`, the four-step
band-projector program complete: the `(a, b]` band as the difference
of two `spectralProjector` calls, idempotence through the nestedness
cross-law `spectralProjector_mul_spectralProjector`, the
mode-selection action interface — in-band modes fixed, out-of-band
modes annihilated — and orthogonality of disjoint bands: both
composition orders, image orthogonality, and shared-mode-freeness —
and completeness under a partition: the unconditional telescoping
law, the covering-family resolution of the identity, monotone-family
orthogonality, and the consumer's vector decomposition `x = ∑ B_k x`;
Step 4 caps the program with the Hilbert-projection specialization:
the band projector's output *is* Mathlib's `orthogonalProjection`
onto its transported range and the closest point of that range to
the input — the residual-orthogonality engine, the identification
`bandProjector_toEuclidean_apply_eq_orthogonalProjection`, and the
closest-point minimality `norm_sub_bandProjector_apply_le`),
its Cheeger
bridge (`GraphTheory.Cheeger`), the Fiedler-vector interface (`GraphTheory.Fiedler`, Phase A: the vector,
the sign partition, and the algebraic-connectivity certificate),
the random-walk interfaces (`GraphTheory.RandomWalk`), the general
normalized Laplacian (`GraphTheory.Normalized`), the directed axis'
stationary theory (`GraphTheory.IrreducibleStationary` — the first
Perron–Frobenius consumer: existence, uniqueness, and full support of
the stationary distribution on irreducible nonnegative walks,
conditional on the axiom — and `GraphTheory.PageRank` — the second:
the teleportation-regularized Google matrix whose positive floor makes
irreducibility *derived* rather than assumed, extending the same
stationary theory to reducible input, likewise conditional), the stationary
structure consuming both (`GraphTheory.Stationary`), the magnetic
Laplacian (`GraphTheory.Magnetic`: the shelf's first complex Hermitian
object — the directed-native `D_sym − ½(W + Wᴴ)` operator, Hermitian by
construction hypothesis-free, with the magnetic energy identity, PSD on
nonnegative weights, the balanced-potential gauge characterization of
the kernel now promoted to the kernel-at-action-level
(`magneticLaplacian_mulVec_eq_zero_iff`), and the
zero-phase/symmetric-cone agreements with the classical Laplacian, all
proved), the signed-graph slice (`GraphTheory.Signed`: the signed
Laplacian `D − A_σ` at a `{±1}` signing, the magnetic π-flux join, the
signed Dirichlet energy identity derived from the delivered
`magnetic_energy`, the kernel characterization, the **Harary balance
theorem in kernel form** `IsBalanced A s ↔ ∃ x ≠ 0, L_σ *ᵥ x = 0` on
connected input, positive definiteness under frustration, and the
switching similarity `diag(g) · L_σ · diag(g) = laplacian A` with
two-way eigenpair transfer, all proved), the Alon–Boppana program's
d-regularity interface (`GraphTheory.AlonBoppana`, Step 1 of the
adopted proposal: `IsDRegular`, the constant-eigenvector fact
`A *ᵥ onesVec = d • onesVec`, the AM–GM row-sum domination
`xᵀAx ≤ d · ‖x‖²`, and the top-eigenvalue identification
`evals ⟨last⟩ = d` from both sides — the lower companion to the
Cheeger/expander toolkit, with the tree-ball test-vector steps 2–5
gated on the proposal's one-step-per-run instruction), the heat
semigroup
(`GraphTheory.Heat`: Phase B, Step 1 of the reversibility/heat program —
the matrix-level diffusion operator `heatKernel A t = e^{-tL}` with its
hypothesis-graded symmetry and time-zero identity, plus the square-zero
exponential collapse), the variational
transfer consuming the congruence bridge
(`GraphTheory.VariationalTransfer`), the event-driven
frontier (`GraphTheory.Dynamics`), the discrete-affine dynamics slice
(`Dynamics.DiscreteAffine`, the `sgt-gaps.md` item-2 consumer
interface: the finite-vector geometric-decay wrapper and the
        affine-iteration convergence theorem, all proved hard crust), the
        perturbation bridge
        (`Analysis.OperatorTheory.Perturbation.*`, including the
        bounded-window Davis–Kahan theorem
        `Perturbation.BandDavisKahan`: the product bound
        `‖Q * P‖ ≤ ‖A − B‖ / δ` for δ-separated band projectors of two
        symmetric matrices, proved by the algebraic commutator/shift
        route — the band-projector sibling of the half-line
        `davis_kahan_sin_theta`), the resolvent calculus
(`Analysis.OperatorTheory.Resolvent`, proposal steps 0–1: the
operator-norm bridge `‖M‖ ↔ max-abs eigenvalue` proved from the
eigenbasis machinery after the C*-algebra thread was found
structurally inapplicable to real matrices, invertibility of the
shifted PSD matrix, and the resolvent identity), the nonnegative-matrix
spectral theory for the directed axis (`LinearAlgebra.PerronFrobenius`:
the combinatorial irreducibility predicate
`Matrix.IsIrreducible` — strong connectivity through positive-weight
arcs — and the admitted Perron–Frobenius theorem for irreducible
nonnegative matrices at the Horn–Johnson 8.4.4 qualification level:
positive simple Perron root with a strictly positive eigenvector, the
positive-multiple uniqueness among nonnegative eigenvectors, and
complex-spectrum domination, deliberately with **no** strict-dominance
clause since imprimitive directed cycles have peripheral eigenvalues of
equal modulus), the probability
concentration bridge (`Probability.Concentration.*`), the
finite-distribution entropy layer (`InformationTheory.Entropy`:
relative entropy and Shannon entropy with Gibbs' inequality and the
entropy maximum, all proved hard crust), the derived
layer (`Derived.EventStream` and `Derived.ProjectorDrift`, whose tail
and projector-drift theorems are conditional on the Matrix Azuma
axiom; Weyl and Davis–Kahan are proved since 2026-08-20/21), and the
core utilities.

Downstream consumers should prefer narrow imports (for example
`import Scaffold.Mathlib.GraphTheory.Spectral`) over this umbrella.
-/
