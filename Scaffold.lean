import Scaffold.Mathlib.Core.RandomVariable
import Scaffold.Mathlib.Core.Norms
import Scaffold.Mathlib.Core.MatrixUpdates
import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.Cheeger
import Scaffold.Mathlib.GraphTheory.Dynamics
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.Weyl
import Scaffold.Mathlib.Analysis.OperatorTheory.Perturbation.DavisKahan

/-!
# Scaffold library root

The default `lake build` target. The umbrella imports every public
module that the current milestone certifies: the SGT center
(`GraphTheory.Spectral`), its Cheeger bridge (`GraphTheory.Cheeger`), the
event-driven frontier (`GraphTheory.Dynamics`), the perturbation bridge
(`Analysis.OperatorTheory.Perturbation.*`), and the core utilities.

Downstream consumers should prefer narrow imports (for example
`import Scaffold.Mathlib.GraphTheory.Spectral`) over this umbrella.

Known exclusions (see `docs/5_QA_SCOREBOARD.md`): the probability
concentration subtree `Scaffold.Mathlib.Probability.Concentration.*` is
not yet elaborable and is excluded until repaired.
-/
