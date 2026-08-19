/-
  ElectricalFlow.lean

  Purpose
  -------
  Edge flows for weighted graphs — the routing object of proposal
  `proposals/electrical-flow-routing.md` (High, 2026-08-18). Step 1:
  the electrical current induced by a potential, its divergence, the
  flow predicates, and the Kirchhoff bridge turning the delivered
  potential-based resistance API into a conserved unit flow. Step 2:
  the dissipated `flowEnergy` and its agreement with the Dirichlet
  energy and the effective resistance it routes. Step 3: Thomson's
  principle — the electrical current minimizes energy among valid unit
  flows, `effectiveResistance A u v ≤ flowEnergy A θ`, via the
  divergence-free superposition lemma (discrete integration by parts).
  Rayleigh monotonicity is step 4 of the proposal and is deliberately
  not attempted here.

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
  dissipate no energy in `flowEnergy` and Thomson's principle would
  fail, so the conjunct is load-bearing, not hygiene. Flows are summed
  over ordered pairs, so every undirected edge is counted twice; the
  `1/2` factor lives in `flowEnergy` (step 2), with a QA fixture that
  fails without it.

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

/-!
## Flow energy (proposal `electrical-flow-routing.md`, step 2)
-/

/-- Energy dissipated by a flow `θ` on the network `A`: squared
current over conductance, summed over ordered pairs and halved. The
`1/2` corrects the ordered-pair double count — every undirected edge is
carried by its two opposite entries — and is load-bearing: QA pins the
raw ordered-pair sum at exactly twice the energy on the unit edge, so
omitting the factor would break the agreement with the Dirichlet
energy below (proposal QA item 4). The zero branch is explicit: a
zero-conductance ordered pair contributes *no* energy, which is
precisely why `IsFlowOn`'s support conjunct is load-bearing for the
variational theory (steps 3–4) — without it, a phantom flow could
route current through a zero-weight pair for free and Thomson's
principle would be false (proposal QA item 5; QA exhibits exactly such
a zero-energy unit-divergence phantom). -/
noncomputable def flowEnergy (A : WAdj (V := V)) (θ : EdgeFlow V) : ℝ :=
  (∑ i, ∑ j, if A i j = 0 then 0 else (θ i j) ^ 2 / A i j) / 2

/-- **Energy agreement (proposal step 2, headline):** the energy
dissipated by the electrical current equals the Dirichlet energy of its
potential. Termwise, Ohm's law gives
`(A i j * (f i − f j))² / A i j = A i j * (f i − f j)²` whenever
`A i j ≠ 0` — pure field algebra, no nonnegativity needed — and the
zero branch matches the vanishing weight, so the ordered-pair sum is
termwise the Dirichlet summand of `laplacian_quadForm`. The identity is
load-bearing on the `1/2` convention in *both* sums: either factor
without its half breaks the equality (QA `edge_double_counting_guard_QA`
pins the unhalved ordered-pair sum at `2 ≠ 1` on the unit edge). Only
symmetry is hypothesized — that is what `laplacian_quadForm` needs; the
entrywise algebra is unconditional. -/
theorem flowEnergy_electricalCurrent (A : WAdj (V := V)) (hA : A.IsSymm)
    (f : V → ℝ) :
    flowEnergy A (electricalCurrent A f) = quadForm (laplacian A) f := by
  have hterm : ∀ i j : V,
      (if A i j = 0 then 0 else electricalCurrent A f i j ^ 2 / A i j)
        = A i j * (f i - f j) ^ 2 := by
    intro i j
    by_cases h : A i j = 0
    · simp [h]
    · simp only [electricalCurrent, if_neg h]
      field_simp
      ring
  simp only [flowEnergy, hterm]
  exact (laplacian_quadForm A hA f).symm

omit [DecidableEq V] in
/-- **Energy is nonnegative** for nonnegative conductances: every
summand is a square over a positive conductance, or the zero branch.
This is the base order fact the variational theory (steps 3–4)
compares flows by — Thomson's principle and Rayleigh monotonicity both
reduce to it on the difference flow. -/
theorem flowEnergy_nonneg (A : WAdj (V := V)) (hnonneg : ∀ i j, 0 ≤ A i j)
    (θ : EdgeFlow V) : 0 ≤ flowEnergy A θ := by
  refine div_nonneg ?_ zero_le_two
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  by_cases h : A i j = 0
  · simp [h]
  · rw [if_neg h]
    exact div_nonneg (sq_nonneg _) (lt_of_le_of_ne (hnonneg i j) (Ne.symm h)).le

/-- **Energy identity, flow level (proposal step 2):** on a connected
graph with symmetric nonnegative weights, the energy dissipated by the
current of a unit-demand potential is exactly the effective resistance
it routes. Composes the agreement theorem with the electrical-crust
solution-level identity
(`quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single`) and the
agreement of the total resistance function (`effectiveResistance_eq`).
Step 3 (Thomson) consumes this as the value the minimum attains. -/
theorem flowEnergy_electricalCurrent_eq_effectiveResistance
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) {u v : V} {f : V → ℝ}
    (hf : (laplacian A).mulVec f = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ)) :
    flowEnergy A (electricalCurrent A f) = effectiveResistance A u v := by
  rw [flowEnergy_electricalCurrent A hA f,
    effectiveResistance_eq A hA hnonneg hconn ⟨f, hf, rfl⟩,
    quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single A hf]

/-!
## Thomson's principle (proposal `electrical-flow-routing.md`, step 3)
-/

omit [DecidableEq V] in
/-- Divergence is linear: the divergence of a difference of flows is
the difference of the divergences, entrywise over the row sums. -/
theorem flowDivergence_sub (θ ψ : EdgeFlow (V := V)) :
    flowDivergence (θ - ψ) = flowDivergence θ - flowDivergence ψ := by
  funext i
  simp only [flowDivergence, Matrix.sub_apply, Pi.sub_apply,
    Finset.sum_sub_distrib]

omit [Fintype V] [DecidableEq V] in
/-- The flow space is linear: the difference of two flows on `A`
(antisymmetric, supported) is again a flow on `A`. Consumed by Thomson's
principle on the difference between a competitor flow and the electrical
current. -/
theorem isFlowOn_sub (A : WAdj (V := V)) {θ ψ : EdgeFlow V}
    (hθ : IsFlowOn A θ) (hψ : IsFlowOn A ψ) : IsFlowOn A (θ - ψ) := by
  refine ⟨fun i j => ?_, fun i j h => ?_⟩
  · rw [Matrix.sub_apply, Matrix.sub_apply, hθ.1 i j, hψ.1 j i]
    ring
  · rw [Matrix.sub_apply, hθ.2 i j h, hψ.2 i j h, sub_self]

omit [DecidableEq V] in
/-- **Divergence-free perturbations of a current add energy** — the
discrete integration-by-parts step of Thomson's principle (proposal step
3, split out as its own interface per the proposal's suggestion: this is
the superposition fact any flow-space argument consumes). If `d` is a
flow on `A` with zero divergence, then perturbing the electrical
current of a potential `f` by `d` adds exactly `d`'s energy.

The proof expands the squared-current summand termwise; the cross term
is, after Ohm's law cancels the conductance on every nonzero branch
(and `d`'s support makes the identity total over ordered pairs), the
sum `∑ i j, (f i − f j) * d i j`. Discrete integration by parts
evaluates it: the row sums are `flowDivergence d` (zero by hypothesis)
and the column sums are the negated row sums by antisymmetry, so both
halves vanish.

Statement shape (stronger than the proposal's sketch): **no hypotheses
on `A` at all** — not even symmetry. Only `d`'s flow properties are
used; Ohm's law needs no symmetry to cancel one conductance. -/
theorem flowEnergy_add_of_flowDivergence_eq_zero (A : WAdj (V := V))
    (f : V → ℝ) {d : EdgeFlow V} (hd : IsFlowOn A d)
    (hdiv : flowDivergence d = 0) :
    flowEnergy A (electricalCurrent A f + d)
      = flowEnergy A (electricalCurrent A f) + flowEnergy A d := by
  -- Termwise square expansion, respecting the zero branches.
  have hptd : ∀ i j : V,
      (if A i j = 0 then (0 : ℝ)
        else (electricalCurrent A f i j + d i j) ^ 2 / A i j)
      = (if A i j = 0 then (0 : ℝ)
          else electricalCurrent A f i j ^ 2 / A i j)
        + (if A i j = 0 then (0 : ℝ) else d i j ^ 2 / A i j)
        + (if A i j = 0 then (0 : ℝ)
            else 2 * electricalCurrent A f i j * d i j / A i j) := by
    intro i j
    by_cases h : A i j = 0
    · simp [h]
    · simp only [if_neg h]
      field_simp
      ring
  -- Ohm's law turns the (undoubled) cross summand into a voltage drop
  -- times the difference flow, on every branch.
  have hterm : ∀ i j : V,
      (if A i j = 0 then (0 : ℝ)
        else electricalCurrent A f i j * d i j / A i j)
      = (f i - f j) * d i j := by
    intro i j
    by_cases h : A i j = 0
    · rw [if_pos h, hd.2 i j h, mul_zero]
    · simp only [electricalCurrent, if_neg h]
      field_simp
      ring
  -- Discrete integration by parts: the cross sum vanishes.
  have hsplit : ∀ i : V,
      ∑ j, (f i - f j) * d i j
        = f i * flowDivergence d i - ∑ j, f j * d i j := by
    intro i
    calc ∑ j, (f i - f j) * d i j
        = ∑ j, (f i * d i j - f j * d i j) :=
          Finset.sum_congr rfl fun j _ => sub_mul (f i) (f j) (d i j)
      _ = f i * ∑ j, d i j - ∑ j, f j * d i j := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = f i * flowDivergence d i - ∑ j, f j * d i j := rfl
  have hcol : ∀ j : V, ∑ i, d i j = 0 := by
    intro j
    have h1 : ∑ i, d i j = ∑ i, -(d j i) :=
      Finset.sum_congr rfl fun i _ => hd.1 i j
    rw [h1, Finset.sum_neg_distrib]
    have h2 : ∑ i, d j i = flowDivergence d j := rfl
    rw [h2, hdiv]
    simp
  have hmain : ∑ i, ∑ j, (f i - f j) * d i j = 0 := by
    have hz1 : ∑ i, f i * flowDivergence d i = 0 := by
      rw [hdiv]
      simp
    have hz2 : ∑ i, ∑ j, f j * d i j = 0 := by
      have hinner : ∀ j : V, ∑ i, f j * d i j = 0 := by
        intro j
        have hpull : f j * ∑ i, d i j = ∑ i, f j * d i j :=
          Finset.mul_sum _ _ _
        rw [← hpull, hcol j, mul_zero]
      calc ∑ i, ∑ j, f j * d i j
          = ∑ j, ∑ i, f j * d i j := Finset.sum_comm
        _ = 0 := Finset.sum_eq_zero fun j _ => hinner j
    calc ∑ i, ∑ j, (f i - f j) * d i j
        = ∑ i, (f i * flowDivergence d i - ∑ j, f j * d i j) :=
          Finset.sum_congr rfl fun i _ => hsplit i
      _ = (∑ i, f i * flowDivergence d i) - ∑ i, ∑ j, f j * d i j :=
          Finset.sum_sub_distrib
      _ = 0 - 0 := by rw [hz1, hz2]
      _ = 0 := sub_self _
  have hcross : ∑ i, ∑ j, (if A i j = 0 then (0 : ℝ)
      else electricalCurrent A f i j * d i j / A i j) = 0 := by
    rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => hterm i j]
    exact hmain
  -- Assemble: the doubled cross sum is twice the undoubled one.
  have hdoubled : ∑ i, ∑ j, (if A i j = 0 then (0 : ℝ)
      else 2 * electricalCurrent A f i j * d i j / A i j)
      = 2 * ∑ i, ∑ j, (if A i j = 0 then (0 : ℝ)
      else electricalCurrent A f i j * d i j / A i j) := by
    have hpair : ∀ i j : V,
        (if A i j = 0 then (0 : ℝ)
          else 2 * electricalCurrent A f i j * d i j / A i j)
        = 2 * (if A i j = 0 then (0 : ℝ)
          else electricalCurrent A f i j * d i j / A i j) := by
      intro i j
      by_cases h : A i j = 0
      · simp [h]
      · simp only [if_neg h]
        ring
    have hstep : ∀ i : V,
        ∑ j, (if A i j = 0 then (0 : ℝ)
          else 2 * electricalCurrent A f i j * d i j / A i j)
        = 2 * ∑ j, (if A i j = 0 then (0 : ℝ)
          else electricalCurrent A f i j * d i j / A i j) := by
      intro i
      rw [Finset.sum_congr rfl fun j _ => hpair i j]
      exact (Finset.mul_sum _ _ _).symm
    rw [Finset.sum_congr rfl fun i _ => hstep i]
    exact (Finset.mul_sum _ _ _).symm
  simp only [flowEnergy, Matrix.add_apply, hptd, Finset.sum_add_distrib]
  rw [hdoubled, hcross, mul_zero]
  ring

/-- **Thomson's principle (proposal step 3, headline):** on a connected
graph with symmetric nonnegative conductances, every valid unit flow
from `u` to `v` dissipates at least the effective resistance — the
electrical current is the energy minimizer,
`effectiveResistance A u v ≤ flowEnergy A θ`.

Proof as proposed: the unit-demand potential's current `ι` is a unit
flow (step 1), so the difference `d = θ − ι` is a flow with zero
divergence; the superposition lemma adds `d`'s energy to `ι`'s, and
`flowEnergy_nonneg` discards it. `ι`'s energy is exactly the resistance
(step 2). Load-bearing chain: Kirchhoff conservation (the difference of
two unit divergences vanishes), the solvability of the unit demand, the
energy agreement, and nonnegativity — an error in any breaks this
proof. The statement is the universal inequality the proposal pins; no
`sInf` packaging (attainment is already witnessed by the constructed
electrical flow through the step-2 identity). -/
theorem effectiveResistance_le_flowEnergy (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected)
    {u v : V} {θ : EdgeFlow V} (hθ : IsUnitFlow A u v θ) :
    effectiveResistance A u v ≤ flowEnergy A θ := by
  obtain ⟨f, hf⟩ :=
    exists_laplacian_mulVec_eq_single_sub_single A hA hnonneg hconn u v
  have hd : IsFlowOn A (θ - electricalCurrent A f) :=
    isFlowOn_sub A hθ.1 (isFlowOn_electricalCurrent A hA f)
  have hdivd : flowDivergence (θ - electricalCurrent A f) = 0 := by
    rw [flowDivergence_sub, hθ.2,
      flowDivergence_electricalCurrent A f, hf, sub_self]
  have hkey :=
    flowEnergy_add_of_flowDivergence_eq_zero A f hd hdivd
  have hsum : electricalCurrent A f + (θ - electricalCurrent A f) = θ := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply]
    ring
  have hnn := flowEnergy_nonneg A hnonneg (θ - electricalCurrent A f)
  rw [← hsum, hkey,
    flowEnergy_electricalCurrent_eq_effectiveResistance A hA hnonneg hconn hf]
  linarith

end SpectralGraphTheory
