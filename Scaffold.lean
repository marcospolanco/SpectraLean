import Scaffold.Mathlib.Core.RandomVariable
import Scaffold.Mathlib.Core.Norms
import Scaffold.Mathlib.Core.MatrixUpdates
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.SimpleGraphAdapter
import Scaffold.Mathlib.GraphTheory.Electrical
import Scaffold.Mathlib.GraphTheory.ElectricalFlow
import Scaffold.Mathlib.GraphTheory.Foster
import Scaffold.Mathlib.GraphTheory.Expander
import Scaffold.Mathlib.GraphTheory.Cheeger
import Scaffold.Mathlib.GraphTheory.Fiedler
import Scaffold.Mathlib.GraphTheory.RandomWalk
import Scaffold.Mathlib.GraphTheory.Normalized
import Scaffold.Mathlib.GraphTheory.Stationary
import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.Mathlib.GraphTheory.Dynamics
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan
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
`∑_{u<v} w_e R_e = n - 1`), the expander discrepancy core
(`GraphTheory.Expander`, step 1 of the decidable-certificates
program: subset edge weights, the centered-indicator decomposition,
and the `d`-regular main-term split the Expander Mixing Lemma
measures), its Cheeger bridge (`GraphTheory.Cheeger`), the
Fiedler-vector interface (`GraphTheory.Fiedler`, Phase A: the vector,
the sign partition, and the algebraic-connectivity certificate),
the random-walk interfaces (`GraphTheory.RandomWalk`), the general
normalized Laplacian (`GraphTheory.Normalized`), the stationary
structure consuming both (`GraphTheory.Stationary`), the variational
transfer consuming the congruence bridge
(`GraphTheory.VariationalTransfer`), the event-driven
frontier (`GraphTheory.Dynamics`), the perturbation bridge
(`Analysis.OperatorTheory.Perturbation.*`), the probability concentration
bridge (`Probability.Concentration.*`), the derived layer
(`Derived.EventStream` and `Derived.ProjectorDrift`, whose tail and
projector-drift theorems are conditional on the Matrix Azuma, Weyl, and
Davis–Kahan axioms), and the core utilities.

Downstream consumers should prefer narrow imports (for example
`import Scaffold.Mathlib.GraphTheory.Spectral`) over this umbrella.
-/
