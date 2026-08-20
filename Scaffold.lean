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
import Scaffold.Mathlib.GraphTheory.Stationary
import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.Mathlib.GraphTheory.Dynamics
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan
import Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent
import Scaffold.Mathlib.Probability.Concentration.Scalar.Subgaussian
import Scaffold.Mathlib.Probability.Concentration.Scalar.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Scalar.Bernstein
import Scaffold.Mathlib.Probability.Concentration.Matrix.Basic
import Scaffold.Mathlib.Probability.Concentration.Matrix.Hoeffding
import Scaffold.Mathlib.Probability.Concentration.Matrix.Bernstein
import Scaffold.Mathlib.Probability.Concentration.Matrix.Azuma
import Scaffold.Derived.EventStream
import Scaffold.Derived.ProjectorDrift

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
spectral band projectors (`GraphTheory.Band`, Step 1 of the
band-projector program: the `(a, b]` band as the difference of two
`spectralProjector` calls, idempotence through the nestedness
cross-law `spectralProjector_mul_spectralProjector`, and the
mode-selection action interface — in-band modes fixed, out-of-band
modes annihilated), its Cheeger
bridge (`GraphTheory.Cheeger`), the Fiedler-vector interface (`GraphTheory.Fiedler`, Phase A: the vector,
the sign partition, and the algebraic-connectivity certificate),
the random-walk interfaces (`GraphTheory.RandomWalk`), the general
normalized Laplacian (`GraphTheory.Normalized`), the stationary
structure consuming both (`GraphTheory.Stationary`), the variational
transfer consuming the congruence bridge
(`GraphTheory.VariationalTransfer`), the event-driven
frontier (`GraphTheory.Dynamics`), the perturbation bridge
(`Analysis.OperatorTheory.Perturbation.*`), the resolvent calculus
(`Analysis.OperatorTheory.Resolvent`, proposal steps 0–1: the
operator-norm bridge `‖M‖ ↔ max-abs eigenvalue` proved from the
eigenbasis machinery after the C*-algebra thread was found
structurally inapplicable to real matrices, invertibility of the
shifted PSD matrix, and the resolvent identity), the probability
concentration bridge (`Probability.Concentration.*`), the derived
layer (`Derived.EventStream` and `Derived.ProjectorDrift`, whose tail
and projector-drift theorems are conditional on the Matrix Azuma,
Weyl, and Davis–Kahan axioms), and the core utilities.

Downstream consumers should prefer narrow imports (for example
`import Scaffold.Mathlib.GraphTheory.Spectral`) over this umbrella.
-/
