/-
  ElectricalFlow.lean

  Purpose
  -------
  Edge flows for weighted graphs — the routing object of proposal
  `proposals/electrical-flow-routing.md` (High, 2026-08-18). This
  module delivers step 1: the electrical current induced by a
  potential, its divergence, the flow predicates, and the Kirchhoff
  bridge turning the delivered potential-based resistance API into a
  conserved unit flow. No variational machinery yet — flow energy,
  Thomson's principle, and Rayleigh monotonicity are steps 2–4 of the
  proposal and are deliberately not attempted here.

  Representation decision (proposal step 0, recorded in the proposal
  on 2026-08-19 before this module was written): flows live on ordered
  vertex pairs as `EdgeFlow V = Matrix V V ℝ`, composing directly with
  `WAdj`, `Matrix.mulVec`, and finite sums. Survey of the pinned
  Mathlib (v4.14.0): no network-flow/circulation/max-flow API, no
  graph-native divergence (only the box/measure-integral divergence
  theorems on continua), no flow or energy API on the one oriented-edge
  type (`SimpleGraph.Dart` is counting machinery), and no
  `Matrix.IsAntiSymm` — antisymmetry is stated as a plain quantifier
  in `IsFlowOn`.

  Sign conventions (proposal calibration, binding for later steps):
  weights `A i j` are **conductances**, not resistances; an entry
  `θ i j` is current flowing `i → j`; `flowDivergence θ i` is net
  outflow at `i`. The zero-conductance trap is closed by the `IsFlowOn`
  support conjunct — without it, current on a zero-weight pair would
  dissipate no energy in step 2 and Thomson's principle would fail, so
  the conjunct is load-bearing, not hygiene. Flows are summed over
  ordered pairs, so every undirected edge is counted twice; that
  factor lives in `flowEnergy` (step 2, not yet defined), where the
  proposal requires a QA fixture that fails without it.

  Everything here is proved hard crust; this module adds no axioms.
  The Kirchhoff bridge is load-bearing on the exact Laplacian sign
  convention (`laplacian_mulVec_apply`, `Spectral.lean`) and on the
  unit-demand equation shape `Pi.single u 1 − Pi.single v 1`
  (`exists_laplacian_mulVec_eq_single_sub_single`, the step-4
  solvability hinge of the electrical crust): an error in either would
  break `flowDivergence_electricalCurrent` or
  `isUnitFlow_electricalCurrent` rather than pass beside them.
-/

import Scaffold.Mathlib.GraphTheory.Electrical

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Edge flows (proposal `electrical-flow-routing.md`, step 1)
-/

/-- An edge flow on `V`: a real assignment to ordered vertex pairs.
`θ i j` is the flow from `i` to `j`. A *valid* flow (`IsFlowOn`) is
antisymmetric, so each undirected edge is carried by its two opposite
entries. Abbreviation of `Matrix V V ℝ` so flows compose with `WAdj`
and `Matrix.mulVec` directly. -/
abbrev EdgeFlow (V : Type) := Matrix V V ℝ

/-- The electrical current induced by a potential `f` on the network
`A`: Ohm's law across each ordered pair — conductance times voltage
drop, `A i j * (f i − f j)`. Weights are conductances, not
resistances. -/
def electricalCurrent (A : WAdj (V := V)) (f : V → ℝ) : EdgeFlow V :=
  fun i j => A i j * (f i - f j)

/-- Divergence of an edge flow at a vertex: the row sum, i.e. the net
outflow. Kirchhoff's current law away from the source and sink is the
statement that this vanishes; the source/sink demand is carried by
`IsUnitFlow`. -/
def flowDivergence (θ : EdgeFlow (V := V)) (i : V) : ℝ :=
  ∑ j, θ i j

/-- A flow on the network `A`: antisymmetric, and supported on the
network — no current may ride a zero-conductance ordered pair. The
support conjunct is load-bearing for the variational theory (proposal
step 2): current on a zero-weight pair would dissipate no energy,
making Thomson's principle false rather than merely inelegant. -/
def IsFlowOn (A : WAdj (V := V)) (θ : EdgeFlow V) : Prop :=
  (∀ i j, θ i j = -θ j i) ∧ (∀ i j, A i j = 0 → θ i j = 0)

/-- A unit flow from `u` to `v`: a flow on `A` whose divergence is the
unit demand `e u − e v` — one unit injected at `u`, one extracted at
`v`, conserved at every other vertex (`e u = Pi.single u 1`). This is
the routing object the proposal builds its minimum-energy theory on. -/
def IsUnitFlow (A : WAdj (V := V)) (u v : V) (θ : EdgeFlow V) : Prop :=
  IsFlowOn A θ
    ∧ flowDivergence θ = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ)

omit [Fintype V] [DecidableEq V] in
/-- **Ohm's law is antisymmetric** under symmetric weights: reversing
the ordered pair negates the voltage drop while the conductance agrees
by symmetry, so the current entries negate. This is the first conjunct
of `IsFlowOn` for the electrical current. -/
theorem electricalCurrent_antisymm (A : WAdj (V := V)) (hA : A.IsSymm)
    (f : V → ℝ) (i j : V) :
    electricalCurrent A f i j = -electricalCurrent A f j i := by
  simp only [electricalCurrent, hA.apply i j]
  ring

omit [Fintype V] [DecidableEq V] in
/-- **Support:** no conductance, no current. The electrical current
never rides a zero-weight ordered pair — the second `IsFlowOn`
conjunct, available unconditionally. -/
theorem electricalCurrent_eq_zero_of_weight_eq_zero (A : WAdj (V := V))
    (f : V → ℝ) {i j : V} (h : A i j = 0) :
    electricalCurrent A f i j = 0 := by
  simp [electricalCurrent, h]

/-- **The Kirchhoff bridge:** the divergence of the electrical current
is the Laplacian action on the potential. Entrywise this is the
diffusion form `laplacian_mulVec_apply` — the load-bearing consumer of
the center's exact sign convention `(L *ᵥ f) i = ∑ j, A i j (f i − f
j)`. A potential solving a demand equation therefore has current whose
divergence is exactly that demand. -/
theorem flowDivergence_electricalCurrent (A : WAdj (V := V)) (f : V → ℝ) :
    flowDivergence (electricalCurrent A f) = (laplacian A).mulVec f := by
  funext i
  exact (laplacian_mulVec_apply A f i).symm

omit [Fintype V] [DecidableEq V] in
/-- The electrical current of any potential is a flow on the network:
antisymmetric under symmetric weights, supported unconditionally. -/
theorem isFlowOn_electricalCurrent (A : WAdj (V := V)) (hA : A.IsSymm)
    (f : V → ℝ) : IsFlowOn A (electricalCurrent A f) :=
  ⟨electricalCurrent_antisymm A hA f,
    fun _i _j h => electricalCurrent_eq_zero_of_weight_eq_zero A f h⟩

/-- **Kirchhoff conservation (proposal step 1, headline):** a
unit-demand potential induces a unit flow. If `f` solves the potential
equation `laplacian A *ᵥ f = e u − e v` — the defining equation of
effective resistance (`exists_laplacian_mulVec_eq_single_sub_single`
supplies such `f` on every connected graph with symmetric nonnegative
weights) — then the electrical current `A i j * (f i − f j)` is a
valid unit flow from `u` to `v`: antisymmetric, supported, and with
divergence exactly the unit demand. This turns the delivered
potential-based resistance API into a routing object. -/
theorem isUnitFlow_electricalCurrent (A : WAdj (V := V)) (hA : A.IsSymm)
    {u v : V} {f : V → ℝ}
    (hf : (laplacian A).mulVec f = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ)) :
    IsUnitFlow A u v (electricalCurrent A f) :=
  ⟨isFlowOn_electricalCurrent A hA f, by
    rw [← hf]
    exact flowDivergence_electricalCurrent A f⟩

end SpectralGraphTheory
