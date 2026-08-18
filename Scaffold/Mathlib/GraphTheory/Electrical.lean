/-
  Electrical.lean

  Purpose
  -------
  Effective resistance for weighted graphs, defined by the potential
  equation it solves rather than by a pseudoinverse, per
  `proposals/electrical-structure-crust.md` step 5 (delivered
  2026-08-18, after the step-4 solvability hinge landed).

  The definition is the classical electrical one: `r` is the effective
  resistance between `u` and `v` when one unit of current injected at
  `u` and extracted at `v` admits a potential `f` — that is,
  `laplacian A *ᵥ f = e u − e v` — whose voltage difference `f u − f v`
  is exactly `r`.

  Mathlib survey (recorded 2026-08-18, before proving): the pinned
  Mathlib has no effective-resistance (or any "resistance") declaration
  anywhere, and no Moore–Penrose pseudoinverse (the
  `NonsingularInverse.lean` header comment states pseudoinverses are
  not considered there) — the potential-equation route is the only one
  available, and also the one that consumes the center.

  Everything here is proved hard crust; this module adds no axioms.
  Existence consumes `exists_laplacian_mulVec_eq_single_sub_single`
  (step 4, `Spectral.lean`); uniqueness of `r` consumes the component
  form of the kernel characterization
  (`laplacian_mulVec_eq_zero_iff_forall_reachable`, steps 2–3); the
  energy identity consumes `laplacian_psd`. An error in any of those
  statements would break proofs here rather than pass beside them.

  Honesty note on the total function: `effectiveResistance` is total by
  a classical choice fallback with junk value `0` when the unit demand
  is unsolvable (e.g. across components of a disconnected graph). That
  fallback is not a resistance; it is QA-witnessed as such in
  `Scaffold/QA/SpectralGraph/EffectiveResistance_QA.lean`
  (`disc_fallback_zero_QA`), and `effectiveResistance_eq_of_reachable`
  states exactly what is needed for the value to be meaningful.
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## Effective resistance (proposal `electrical-structure-crust.md`, step 5)
-/

/-- `IsEffectiveResistance A u v r`: `r` is the effective resistance
between `u` and `v` in the weighted graph `A`, defined by the potential
equation — there is a potential `f` solving the unit-demand equation
`laplacian A *ᵥ f = e u − e v` (one unit injected at `u`, one extracted
at `v`; `e u = Pi.single u 1`) whose voltage difference `f u − f v` is
`r`. No hypotheses: existence holds on connected graphs with symmetric
nonnegative weights (`exists_isEffectiveResistance`), and `r` is unique
whenever `u` and `v` lie in one connected component
(`isEffectiveResistance_unique_of_reachable`). -/
def IsEffectiveResistance (A : WAdj (V := V)) (u v : V) (r : ℝ) : Prop :=
  ∃ f : V → ℝ, (laplacian A).mulVec f
    = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ) ∧ f u - f v = r

/-- The diagonal case is hypothesis-free and fully characterized:
`IsEffectiveResistance A u u r` holds exactly for `r = 0`. Any solution
`f` of the trivial demand has `f u − f u = 0` by the second conjunct,
and `f = 0` exhibits the value. -/
theorem isEffectiveResistance_self_iff (A : WAdj (V := V)) (u : V)
    (r : ℝ) : IsEffectiveResistance A u u r ↔ r = 0 := by
  constructor
  · rintro ⟨f, hf, hfr⟩
    rw [sub_self] at hfr
    exact hfr.symm
  · intro hr
    subst hr
    exact ⟨0, by rw [Matrix.mulVec_zero, sub_self], by simp⟩

/-- **Symmetry of the relation, no hypotheses.** If `r` is an effective
resistance from `u` to `v`, it is one from `v` to `u`: negating the
potential negates the demand and swaps the voltage difference back. -/
theorem isEffectiveResistance_symm {A : WAdj (V := V)} {u v : V} {r : ℝ}
    (h : IsEffectiveResistance A u v r) : IsEffectiveResistance A v u r := by
  obtain ⟨f, hf, hfr⟩ := h
  refine ⟨-f, ?_, ?_⟩
  · have hneg : (laplacian A).mulVec (-f) = -((laplacian A).mulVec f) := by
      rw [← Matrix.mulVecLin_apply, map_neg, Matrix.mulVecLin_apply]
    rw [hneg, hf, neg_sub]
  · simpa only [Pi.neg_apply, neg_sub_neg] using hfr

/-- **Existence** of a resistance value on a connected graph with
symmetric nonnegative weights: the step-4 unit-demand solvability
theorem produces a potential, and its voltage difference is the value. -/
theorem exists_isEffectiveResistance (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    (u v : V) : ∃ r : ℝ, IsEffectiveResistance A u v r := by
  obtain ⟨f, hf⟩ :=
    exists_laplacian_mulVec_eq_single_sub_single A hA hnonneg hconn u v
  exact ⟨f u - f v, f, hf, rfl⟩

/-- **Uniqueness of the resistance value along a reachability pair.**
Two potentials solving the same unit demand differ by a Laplacian-kernel
vector, which is constant on components
(`laplacian_mulVec_eq_zero_iff_forall_reachable`, steps 2–3); if `u` and
`v` are reachable from each other, the kernel difference cancels in
`f u − f v`. Global connectivity is not needed — a same-component pair
on a disconnected graph still has a unique resistance. -/
theorem isEffectiveResistance_unique_of_reachable (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    {u v : V} (hr : (supportGraph A hA).Reachable u v) {r s : ℝ}
    (h1 : IsEffectiveResistance A u v r) (h2 : IsEffectiveResistance A u v s) :
    r = s := by
  obtain ⟨f, hf, hfr⟩ := h1
  obtain ⟨g, hg, hgs⟩ := h2
  have hd : (laplacian A).mulVec (f - g) = 0 := by
    rw [← Matrix.mulVecLin_apply, map_sub, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, hf, hg, sub_self]
  have hfg : f u - g u = f v - g v :=
    (laplacian_mulVec_eq_zero_iff_forall_reachable A hA hnonneg (f - g)).1 hd u v hr
  linarith

/-- **Uniqueness on a connected graph**: the connected corollary of
`isEffectiveResistance_unique_of_reachable` (reachability of every pair
through the `CoeFun` instance on `SimpleGraph.Connected`). -/
theorem isEffectiveResistance_unique (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    {u v : V} {r s : ℝ} (h1 : IsEffectiveResistance A u v r)
    (h2 : IsEffectiveResistance A u v s) : r = s :=
  isEffectiveResistance_unique_of_reachable A hA hnonneg (hconn u v) h1 h2

/-- **The energy identity, at the solution level.** Every potential `f`
solving the unit-demand equation has energy exactly equal to its
voltage difference: `quadForm (laplacian A) f = f u − f v`. This is the
definitional unfolding of `quadForm` plus `Matrix.dotProduct_single` on
the demand; no symmetry hypothesis is needed. The proposal's `R u v =
quadForm (laplacian A) f` (energy identity) is the function-level form
`effectiveResistance_eq_quadForm` below. -/
theorem quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single
    (A : WAdj (V := V)) {u v : V} {f : V → ℝ}
    (hf : (laplacian A).mulVec f = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ)) :
    quadForm (laplacian A) f = f u - f v := by
  rw [quadForm, hf, Matrix.dotProduct_sub, Matrix.dotProduct_single,
    Matrix.dotProduct_single, mul_one, mul_one]

open Classical in
/-- **Total effective-resistance function.** When the unit demand
`e u − e v` is solvable in the strong sense that `u`, `v` lie in one
connected component (in particular on any connected graph with
symmetric nonnegative weights), the value agrees with every
`IsEffectiveResistance A u v r` witness
(`effectiveResistance_eq_of_reachable`); otherwise it takes the junk
value `0`, which is *not* a resistance — see
`effectiveResistance_eq_zero_of_not_exists` and the QA witness
`disc_fallback_zero_QA`. Totality is by classical choice over the
existence proposition; well-definedness is
`isEffectiveResistance_unique_of_reachable`. -/
noncomputable def effectiveResistance (A : WAdj (V := V)) (u v : V) : ℝ :=
  if h : ∃ r : ℝ, IsEffectiveResistance A u v r then Classical.choose h else 0

/-- The junk case of `effectiveResistance`: when no resistance value
exists at all (the unit demand is unsolvable), the total function
evaluates to `0`. This is the fallback branch, not a measurement. -/
theorem effectiveResistance_eq_zero_of_not_exists (A : WAdj (V := V))
    (u v : V) (h : ¬ ∃ r : ℝ, IsEffectiveResistance A u v r) :
    effectiveResistance A u v = 0 := by
  simp only [effectiveResistance, dif_neg h]

/-- **Agreement, component form.** If `u` and `v` are reachable in the
support graph and `r` is any effective-resistance witness value, then
`effectiveResistance A u v = r`. This is the well-definedness of the
total function on every component of every graph; connectivity of the
whole graph is only needed for the *existence* of a witness, not for
the value to be meaningful. -/
theorem effectiveResistance_eq_of_reachable (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j) {u v : V}
    (hr : (supportGraph A hA).Reachable u v) {r : ℝ}
    (h : IsEffectiveResistance A u v r) :
    effectiveResistance A u v = r := by
  have hex : ∃ s : ℝ, IsEffectiveResistance A u v s := ⟨r, h⟩
  simp only [effectiveResistance, dif_pos hex]
  exact isEffectiveResistance_unique_of_reachable A hA hnonneg hr
    (Classical.choose_spec hex) h

/-- **Agreement on a connected graph:** every witness value pins the
total function. -/
theorem effectiveResistance_eq (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    {u v : V} {r : ℝ} (h : IsEffectiveResistance A u v r) :
    effectiveResistance A u v = r :=
  effectiveResistance_eq_of_reachable A hA hnonneg (hconn u v) h

/-- **Energy identity, function level:** on a connected graph there is a
potential solving the unit demand, and the effective resistance equals
that potential's energy `quadForm (laplacian A) f`. Composes the
step-4 existence theorem with the solution-level identity
`quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single`. -/
theorem effectiveResistance_eq_quadForm (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    (u v : V) :
    ∃ f : V → ℝ, (laplacian A).mulVec f
      = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ)
      ∧ effectiveResistance A u v = quadForm (laplacian A) f := by
  obtain ⟨f, hf⟩ :=
    exists_laplacian_mulVec_eq_single_sub_single A hA hnonneg hconn u v
  refine ⟨f, hf, ?_⟩
  rw [effectiveResistance_eq A hA hnonneg hconn ⟨f, hf, rfl⟩,
    quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single A hf]

/-- **Nonnegativity:** resistance is an energy, and the Laplacian is
positive semidefinite (`laplacian_psd`) — the energy identity transfers
PSD to the resistance value. -/
theorem effectiveResistance_nonneg (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    (u v : V) : 0 ≤ effectiveResistance A u v := by
  obtain ⟨f, hf, heq⟩ := effectiveResistance_eq_quadForm A hA hnonneg hconn u v
  rw [heq]
  exact laplacian_psd A hA hnonneg f

/-- **Symmetry:** effective resistance does not depend on orientation.
Transport the witness through `isEffectiveResistance_symm` and pin both
orientations to the same value by agreement. -/
theorem effectiveResistance_symm (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    (u v : V) :
    effectiveResistance A u v = effectiveResistance A v u := by
  obtain ⟨r, hr⟩ := exists_isEffectiveResistance A hA hnonneg hconn u v
  rw [effectiveResistance_eq A hA hnonneg hconn hr,
    effectiveResistance_eq A hA hnonneg hconn (isEffectiveResistance_symm hr)]

/-- **Vanishing on the diagonal, unconditionally:** the resistance from
a vertex to itself is `0`, on every graph — the diagonal case is fully
characterized by `isEffectiveResistance_self_iff`, with no symmetry,
nonnegativity, or connectivity hypothesis. -/
theorem effectiveResistance_self (A : WAdj (V := V)) (u : V) :
    effectiveResistance A u u = 0 := by
  have hex : ∃ r : ℝ, IsEffectiveResistance A u u r :=
    ⟨0, (isEffectiveResistance_self_iff A u 0).2 rfl⟩
  simp only [effectiveResistance, dif_pos hex]
  exact (isEffectiveResistance_self_iff A u _).1 (Classical.choose_spec hex)

end SpectralGraphTheory
