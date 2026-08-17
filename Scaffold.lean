import Scaffold.Mathlib.Core.RandomVariable
import Scaffold.Mathlib.Core.Norms
import Scaffold.Mathlib.Core.MatrixUpdates
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.Cheeger
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
(`GraphTheory.Spectral`), its Cheeger bridge (`GraphTheory.Cheeger`), the
event-driven frontier (`GraphTheory.Dynamics`), the perturbation bridge
(`Analysis.OperatorTheory.Perturbation.*`), the probability concentration
bridge (`Probability.Concentration.*`), the derived layer
(`Derived.EventStream` and `Derived.ProjectorDrift`, whose tail and
projector-drift theorems are conditional on the Matrix Azuma, Weyl, and
Davis–Kahan axioms), and the core utilities.

Downstream consumers should prefer narrow imports (for example
`import Scaffold.Mathlib.GraphTheory.Spectral`) over this umbrella.
-/
