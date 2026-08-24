/-
  Electrical.lean

  Purpose
  -------
  Effective resistance for weighted graphs, defined by the potential
  equation it solves rather than by a pseudoinverse, per
  `proposals/electrical-structure-crust.md` step 5 (delivered
  2026-08-18, after the step-4 solvability hinge landed), the
  one-sided Dirichlet bound of step 6 (delivered 2026-08-18): every
  test potential of positive energy lower-bounds the resistance,
  `(f u − f v)² / quadForm (laplacian A) f ≤ effectiveResistance A u v`,
  and the resistance-metric residuals of backlog item 7 (delivered
  2026-08-24, `proposals/resistance-metric.md`): the maximum principle
  for unit-demand potentials, the definiteness residual
  `R u v = 0 ↔ u = v`, and the triangle inequality `R u w ≤ R u v +
  R v w` — the last two laws, with nonnegativity, symmetry, and
  self-distance, making the resistance a metric on every connected
  network.

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

/-!
## The one-sided Dirichlet bound (proposal `electrical-structure-crust.md`, step 6)

Mathlib survey (recorded 2026-08-18, before proving): the pin's only
Cauchy–Schwarz is the inner-product-space one
(`Analysis/InnerProductSpace/Basic.lean`), which requires a *definite*
inner product; the Laplacian energy is merely semidefinite (constants
have zero energy), so using it would first require quotienting out the
kernel. No `QuadraticForm` Cauchy–Schwarz exists at these function
types. The polarization route below is self-contained and is
load-bearing on `laplacian_psd` (every perturbed energy is nonnegative)
and on the reciprocity identity `laplacian_dotProduct_mulVec` (the
cross term collapses) — errors in either would break these proofs.
-/

/-- **Algebraic core: a real quadratic that is nonnegative everywhere
has a nonpositive discriminant.** If `Q - 2 * t * c + t * t * E ≥ 0`
for every `t` and `E ≥ 0`, then `c * c ≤ Q * E`. At `t = c / E` the
quadratic sits at its minimum `Q - c ^ 2 / E` (cleared by multiplying
through by `E > 0`); when `E = 0` the hypothesis at
`t = (Q + 1) / (2 * c)` forces `c = 0`, making the bound trivial. -/
theorem sq_le_mul_of_forall_zero_le_sub {Q c E : ℝ} (hE : 0 ≤ E)
    (h : ∀ t : ℝ, 0 ≤ Q - 2 * t * c + t * t * E) :
    c * c ≤ Q * E := by
  rcases hE.eq_or_lt with rfl | hE
  · have hc : c = 0 := by
      by_contra h0
      have hne : c ≠ 0 := h0
      have h1 := h ((Q + 1) / (2 * c))
      have h2 : 2 * ((Q + 1) / (2 * c)) * c = Q + 1 := by
        field_simp
        ring
      rw [h2, mul_zero, add_zero] at h1
      linarith
    rw [hc]
    simp
  · have hEne : E ≠ 0 := ne_of_gt hE
    have h1 := h (c / E)
    have key : 0 ≤ (Q - 2 * (c / E) * c + (c / E) * (c / E) * E) * E :=
      mul_nonneg h1 hE.le
    have key' : (Q - 2 * (c / E) * c + (c / E) * (c / E) * E) * E
        = Q * E - c * c := by
      field_simp
      ring
    rw [key'] at key
    linarith

/-- **Polarization of the energy.** For symmetric weights, the energy of
a perturbed potential `f - t • g` expands as a quadratic in `t` whose
cross term is `f ⬝ᵥ (L *ᵥ g)` — by the reciprocity identity
`laplacian_dotProduct_mulVec`, the two mixed terms agree. This is the
algebraic substrate of the one-sided Dirichlet bound: positive
semidefiniteness makes this quadratic nonnegative for every `t`, and
`sq_le_mul_of_forall_zero_le_sub` then forces the discriminant bound. -/
theorem quadForm_laplacian_sub_smul (A : WAdj (V := V)) (hA : A.IsSymm)
    (f g : V → ℝ) (t : ℝ) :
    quadForm (laplacian A) (f - t • g)
      = quadForm (laplacian A) f
        - 2 * t * Matrix.dotProduct f (laplacian A *ᵥ g)
        + t * t * quadForm (laplacian A) g := by
  have hrec : Matrix.dotProduct g (laplacian A *ᵥ f)
      = Matrix.dotProduct f (laplacian A *ᵥ g) := by
    rw [laplacian_dotProduct_mulVec A hA g f, Matrix.dotProduct_comm]
  simp only [quadForm, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.sub_dotProduct, Matrix.dotProduct_sub,
    Matrix.smul_dotProduct, Matrix.dotProduct_smul,
    smul_smul, smul_eq_mul]
  rw [hrec]
  ring

/-- **Cauchy–Schwarz for the (semidefinite) Laplacian energy.** For
symmetric nonnegative weights,
`(f ⬝ᵥ L *ᵥ g) ^ 2 ≤ quadForm L f * quadForm L g`. The Laplacian's
bilinear form is only semidefinite — constants have zero energy — so
Mathlib's inner-product Cauchy–Schwarz does not apply directly (see the
survey note above); this is proved instead by polarizing the PSD energy
along `f - t • g` and extracting the discriminant bound. No
connectivity hypothesis is needed. -/
theorem laplacian_cauchy_schwarz (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (f g : V → ℝ) :
    Matrix.dotProduct f (laplacian A *ᵥ g) ^ 2
      ≤ quadForm (laplacian A) f * quadForm (laplacian A) g := by
  have key := sq_le_mul_of_forall_zero_le_sub
    (laplacian_psd A hA hnonneg g)
    (fun t => by
      have h := laplacian_psd A hA hnonneg (f - t • g)
      rwa [quadForm_laplacian_sub_smul A hA f g t] at h)
  rwa [pow_two]

/-- **The one-sided Dirichlet bound** (proposal
`electrical-structure-crust.md`, step 6): every test potential `f` with
positive energy lower-bounds the effective resistance,
`(f u − f v) ^ 2 / quadForm (laplacian A) f ≤ effectiveResistance A u v`.
This is the direction applications use to bound resistance from below.
The proof evaluates the Cauchy–Schwarz cross term through the step-4
unit-demand potential `g`: its cross term `f ⬝ᵥ (L *ᵥ g)` is exactly
the voltage difference `f u − f v`, and its energy is exactly the
resistance (the step-5 energy identity). Equality is attained at
multiples of `g` (up to constants), but the statement needs no attained
supremum — the reverse (upper-bound) direction is the deferred Dirichlet
principle. The `0 <` hypothesis guards the division: on a connected
graph, zero energy forces `f u = f v` (PSD and the kernel
characterization), so the bound would degenerate to `0 / 0` junk
without it. -/
theorem effectiveResistance_ge_sq_div_quadForm (A : WAdj (V := V))
    (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected)
    (u v : V) (f : V → ℝ) (hpos : 0 < quadForm (laplacian A) f) :
    (f u - f v) ^ 2 / quadForm (laplacian A) f
      ≤ effectiveResistance A u v := by
  obtain ⟨g, hg⟩ :=
    exists_laplacian_mulVec_eq_single_sub_single A hA hnonneg hconn u v
  have hc : Matrix.dotProduct f (laplacian A *ᵥ g) = f u - f v := by
    rw [hg, Matrix.dotProduct_sub, Matrix.dotProduct_single,
      Matrix.dotProduct_single, mul_one, mul_one]
  have hE : quadForm (laplacian A) g = effectiveResistance A u v := by
    rw [quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single A hg,
      effectiveResistance_eq A hA hnonneg hconn ⟨g, hg, rfl⟩]
  have hcs := laplacian_cauchy_schwarz A hA hnonneg f g
  rw [hc, hE] at hcs
  rwa [div_le_iff₀' hpos]

/-!
## The resistance metric (backlog item 7's named residuals)

`effectiveResistance_pos_of_ne` / `effectiveResistance_eq_zero_iff`
(the definiteness residual `R u v = 0 ↔ u = v`) and
`effectiveResistance_le_add` (the triangle inequality) — together with
the proved nonnegativity, symmetry, and self-distance laws above, these
complete the four metric laws, making `effectiveResistance` a genuine
metric on every connected network with symmetric nonnegative weights
(the classical "resistance distance": Doyle–Snell 1984 §3.5 for the
potential route, Gutman–Xiao 2004 for the metric statement — route
provenance only; locators carry the standing
verify-against-physical-copy caveat).

The mathematical crux is the **maximum principle** for unit-demand
potentials (`laplacian_mulVec_eq_single_sub_single_le_max` and its min
sibling): a potential solving `L *ᵥ f = e u − e v` takes every value
between its boundary values `f v` and `f u`. The eigenbasis route
cannot replace it: there `R(u,v) = ‖z_u − z_v‖²` in the `1/√λ`-weighted
eigenbasis, and the Euclidean triangle on the `z`-vectors yields only
the *root*-triangle `√R(u,w) ≤ √R(u,v) + √R(v,w)` — the cross term is
exactly what the sharp triangle must cancel, and the cancellation *is*
the maximum principle (`proposals/resistance-metric.md` Step 0 records
this route comparison). Proof: at a max-point outside `{u, v}` the
diffusion form `∑ j, A x j * (f x − f j) = 0` (`laplacian_mulVec_apply`)
is a sum of nonnegative terms, so each vanishes and the max value
propagates across every positive-weight edge; a walk induction then
floods the connected graph, contradicting `f u ≠ f v`. This is the
kernel-characterization argument (`eq_of_supportGraph_walk`) run at an
inequality — an error in the diffusion form, the support-graph walk
machinery, or the existence theorem breaks these proofs rather than
passing beside them.
-/

/-- **The maximum principle, top half.** Every potential `f` solving the
unit-demand equation `L *ᵥ f = e u − e v` on a connected network with
symmetric nonnegative weights takes no value above its boundary
maximum: `f x ≤ max (f u) (f v)` for every vertex `x`. The proof is the
diffusion-form propagation: at a global max-point `x₀` outside the
boundary `{u, v}`, `∑ j, A x₀ j * (f x₀ − f j) = 0` is a sum of
nonnegative terms, so every positive-weight neighbor carries the same
max value; walk induction floods the graph, so a max strictly above
both boundary values would force `f` constant and contradict the
nonzero demand. Load-bearing on `laplacian_mulVec_apply` (the diffusion
form) and on the `supportGraph` walk machinery. -/
theorem laplacian_mulVec_eq_single_sub_single_le_max
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) {u v : V}
    {f : V → ℝ} (hf : (laplacian A).mulVec f
      = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ)) (x : V) :
    f x ≤ max (f u) (f v) := by
  haveI : Nonempty V := ⟨u⟩
  obtain ⟨x₀, hx₀⟩ := Finite.exists_max f
  by_contra hcon
  have hmax : max (f u) (f v) < f x₀ :=
    (lt_of_not_le hcon).trans_le (hx₀ x)
  have hclaim : ∀ (s y : V) (w : (supportGraph A hA).Walk s y),
      f s = f x₀ → (f y = f x₀ ∨ f u = f x₀ ∨ f v = f x₀) := by
    intro s y w
    induction w with
    | nil => exact fun h => Or.inl h
    | @cons a b c hadj wrest ih =>
      intro hs
      rcases eq_or_ne a u with rfl | hau
      · exact Or.inr (Or.inl hs)
      rcases eq_or_ne a v with rfl | hav
      · exact Or.inr (Or.inr hs)
      have hLa : (laplacian A).mulVec f a = 0 := by
        rw [hf]
        simp [Pi.single_apply, hau, hav]
      rw [laplacian_mulVec_apply A f a] at hLa
      have hterms := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => mul_nonneg (hnonneg a j)
          (sub_nonneg.2 (by rw [hs]; exact hx₀ j)))).1 hLa
      rcases mul_eq_zero.1 (hterms b (Finset.mem_univ b)) with h0 | h1
      · exact absurd h0 (ne_of_gt (supportGraph_adj.1 hadj).2)
      · exact ih (by rw [← sub_eq_zero.1 h1, hs])
  obtain ⟨w⟩ := hconn x₀ u
  rcases hclaim x₀ u w rfl with h | h | h
  · exact absurd h ((lt_of_le_of_lt (le_max_left (f u) (f v)) hmax).ne)
  · exact absurd h ((lt_of_le_of_lt (le_max_left (f u) (f v)) hmax).ne)
  · exact absurd h ((lt_of_le_of_lt (le_max_right (f u) (f v)) hmax).ne)

/-- **The maximum principle, min half.** Every potential solving the
unit-demand equation takes no value below its boundary minimum:
`min (f u) (f v) ≤ f x`. This is the max half applied to `−f`, whose
demand negates and swaps the boundary pair — no second propagation
argument is needed. -/
theorem laplacian_mulVec_eq_single_sub_single_min_le
    (A : WAdj (V := V)) (hA : A.IsSymm) (hnonneg : ∀ i j, 0 ≤ A i j)
    (hconn : (supportGraph A hA).Connected) {u v : V}
    {f : V → ℝ} (hf : (laplacian A).mulVec f
      = Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ)) (x : V) :
    min (f u) (f v) ≤ f x := by
  have hfn : (laplacian A).mulVec (-f)
      = Pi.single v (1 : ℝ) - Pi.single u (1 : ℝ) := by
    rw [← Matrix.mulVecLin_apply, map_neg, Matrix.mulVecLin_apply, hf,
      neg_sub]
  have key := laplacian_mulVec_eq_single_sub_single_le_max
    A hA hnonneg hconn (u := v) (v := u) hfn x
  rcases le_max_iff.1 key with h | h
  · exact min_le_iff.2 (Or.inr (by simp only [Pi.neg_apply] at h; linarith))
  · exact min_le_iff.2 (Or.inl (by simp only [Pi.neg_apply] at h; linarith))

/-- **Positivity off the diagonal:** on a connected network with
symmetric nonnegative weights, distinct vertices have strictly positive
resistance. The witness test potential is the indicator `e u` itself:
its energy is `quadForm L e u = deg A u − A u u = ∑_{j ≠ u} A u j`,
positive because connectivity gives `u` a positive-weight off-diagonal
neighbor (the first edge of any walk to `v ≠ u`), and its voltage
difference is `1`; the one-sided Dirichlet bound then gives
`1 / (∑_{j ≠ u} A u j) ≤ R u v`. Load-bearing on
`effectiveResistance_ge_sq_div_quadForm` — a misstated bound or energy
computation breaks this immediately. -/
theorem effectiveResistance_pos_of_ne (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    {u v : V} (huv : u ≠ v) : 0 < effectiveResistance A u v := by
  have hnb : ∃ j : V, j ≠ u ∧ 0 < A u j := by
    obtain ⟨w⟩ := hconn u v
    induction w with
    | nil => exact absurd rfl huv
    | @cons a b c hadj wrest ih =>
      exact ⟨b, (supportGraph_adj.1 hadj).1.symm, (supportGraph_adj.1 hadj).2⟩
  obtain ⟨j, hju, hjpos⟩ := hnb
  have hE : quadForm (laplacian A) (Pi.single u (1 : ℝ)) = deg A u - A u u := by
    rw [quadForm, Matrix.dotProduct_comm, Matrix.dotProduct_single, mul_one]
    simp [laplacian, degreeMatrix, deg]
  have hsum : ∑ k ∈ Finset.univ.erase u, A u k + A u u = ∑ k, A u k :=
    Finset.sum_erase_add _ _ (Finset.mem_univ u)
  have hle : A u j ≤ ∑ k ∈ Finset.univ.erase u, A u k :=
    Finset.single_le_sum (fun k _ => hnonneg u k)
      (Finset.mem_erase.2 ⟨hju, Finset.mem_univ j⟩)
  have hEpos : 0 < deg A u - A u u := by rw [deg]; linarith
  have hu1 : (Pi.single u (1 : ℝ) : V → ℝ) u = 1 := by
    rw [Pi.single_apply, if_pos rfl]
  have hv0 : (Pi.single u (1 : ℝ) : V → ℝ) v = 0 := by
    rw [Pi.single_apply, if_neg (Ne.symm huv)]
  have hD := effectiveResistance_ge_sq_div_quadForm A hA hnonneg hconn u v
    (Pi.single u (1 : ℝ)) (by rw [hE]; exact hEpos)
  rw [hu1, hv0, sub_zero, one_pow, hE] at hD
  exact lt_of_lt_of_le (one_div_pos.2 hEpos) hD

/-- **The definiteness residual:** on a connected network with symmetric
nonnegative weights, `effectiveResistance A u v = 0` exactly on the
diagonal — the last law distinguishing a metric from a pseudometric.
Forward: `u ≠ v` forces positivity
(`effectiveResistance_pos_of_ne`). Backward: `effectiveResistance_self`.
Together with `_nonneg`, `_symm`, and `_le_add` this completes the four
metric laws. (A `MetricSpace` instance is deliberately not registered:
the vertex type is global and the laws hold only under the connectedness
hypothesis — packaging it is a recorded follow-on, not a gap in what is
claimed.) -/
theorem effectiveResistance_eq_zero_iff (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    {u v : V} :
    effectiveResistance A u v = 0 ↔ u = v := by
  constructor
  · intro h
    by_contra huv
    have := effectiveResistance_pos_of_ne A hA hnonneg hconn huv
    linarith
  · intro he
    subst he
    exact effectiveResistance_self A u

/-- **The triangle inequality:** on a connected network with symmetric
nonnegative weights, `R u w ≤ R u v + R v w` — the sharp form that makes
`effectiveResistance` a metric (the resistance distance). The assembly:
`h := f + g` solves the `e u − e w` demand when `f` solves `e u − e v`
and `g` solves `e v − e w`, so by the energy identities
`R(u,w) = quadForm L h = R(u,v) + R(v,w) + 2 * (f ⬝ᵥ L *ᵥ g)` (the
polarization `quadForm_laplacian_sub_smul` at `t = −1`), and the cross
term is `f v − f w ≤ 0` by the maximum principle — the new mathematical
content, which the eigenbasis route provably cannot supply (only the
root-triangle). The degenerate cases `u = v` close through
`effectiveResistance_self`. Load-bearing on the existence theorem, the
solution-level energy identity, the reciprocity-based polarization, the
agreement theorem, positivity, and both confinement halves at once. -/
theorem effectiveResistance_le_add (A : WAdj (V := V)) (hA : A.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ A i j) (hconn : (supportGraph A hA).Connected)
    (u v w : V) :
    effectiveResistance A u w
      ≤ effectiveResistance A u v + effectiveResistance A v w := by
  obtain ⟨f, hf⟩ :=
    exists_laplacian_mulVec_eq_single_sub_single A hA hnonneg hconn u v
  obtain ⟨g, hg⟩ :=
    exists_laplacian_mulVec_eq_single_sub_single A hA hnonneg hconn v w
  have hRuv : effectiveResistance A u v = f u - f v :=
    effectiveResistance_eq A hA hnonneg hconn ⟨f, hf, rfl⟩
  have hRvw : effectiveResistance A v w = g v - g w :=
    effectiveResistance_eq A hA hnonneg hconn ⟨g, hg, rfl⟩
  have hh : (laplacian A).mulVec (f + g)
      = Pi.single u (1 : ℝ) - Pi.single w (1 : ℝ) := by
    rw [← Matrix.mulVecLin_apply, map_add, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, hf, hg, sub_add_sub_cancel]
  have hRuw : effectiveResistance A u w = (f + g) u - (f + g) w :=
    effectiveResistance_eq A hA hnonneg hconn ⟨f + g, hh, rfl⟩
  have hvec : f + g = f - (-1 : ℝ) • g := by funext i; simp
  have hcross : Matrix.dotProduct f (laplacian A *ᵥ g) = f v - f w := by
    rw [hg, Matrix.dotProduct_sub, Matrix.dotProduct_single,
      Matrix.dotProduct_single, mul_one, mul_one]
  have hexp := quadForm_laplacian_sub_smul A hA f g (-1 : ℝ)
  have e1 : quadForm (laplacian A) f = f u - f v :=
    quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single A hf
  have e2 : quadForm (laplacian A) g = g v - g w :=
    quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single A hg
  have e3 : quadForm (laplacian A) (f + g) = (f + g) u - (f + g) w :=
    quadForm_laplacian_eq_sub_of_mulVec_eq_single_sub_single A hh
  have key : quadForm (laplacian A) (f - (-1 : ℝ) • g)
      = (f u - f v) + (g v - g w) + 2 * (f v - f w) := by
    rw [hexp, hcross, e1, e2]; ring
  rw [← hvec] at key
  simp only [Pi.add_apply] at e3
  rw [← hRuv, ← hRvw] at key
  rcases eq_or_ne u v with rfl | huv
  · rw [effectiveResistance_self]; linarith
  · have hmin : min (f u) (f v) ≤ f w :=
      laplacian_mulVec_eq_single_sub_single_min_le A hA hnonneg hconn hf w
    have hpos : 0 < f u - f v := by
      rw [← hRuv]; exact effectiveResistance_pos_of_ne A hA hnonneg hconn huv
    have hvw : f v ≤ f w := by
      rcases min_le_iff.1 hmin with h | h
      · linarith
      · exact h
    rw [hRuw]
    simp only [Pi.add_apply]
    linarith

end SpectralGraphTheory
