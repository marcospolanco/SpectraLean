/-
  FunctionalCalculus.lean

  Purpose
  -------
  The Scaffold–Mathlib Hermitian functional-calculus bridge: a thin
  wrapper exposing Mathlib's proved continuous functional calculus
  (`Matrix.IsHermitian.cfc`, `Mathlib/LinearAlgebra/Matrix/
  HermitianFunctionalCalculus.lean`) at this shelf's real-symmetric
  convention (`Matrix V V ℝ` with an explicit `IsSymm` proof), together
  with the load-bearing bridge theorems tying it to the shelf's own
  hand-built spectral-filter machinery.

  What this module is, precisely:
  - an adapter: `spectralCalc M hM f` is *definitionally* Mathlib's
    `(isHermitian_of_isSymm hM).cfc f` — the continuous functional
    calculus consumed, not rebuilt;
  - the eigenvector action `spectralCalc_mulVec_eigvecOf` (every
    eigenbasis vector is an eigenvector of `f(M)` at eigenvalue
    `f (eigvalOf M hM i)` — hypothesis-free);
  - the equality with the shelf's existing arbitrary-filter expansion:
    `spectralCalc_mulVec_apply` exhibits `f(M) *ᵥ y` as exactly the
    filter-sum vector of `dotProduct_eigvecOf_filter`
    (GraphTheory/Tikhonov.lean), and
    `dotProduct_eigvecOf_spectralCalc_mulVec` consumes that workhorse
    verbatim — the calculus and the hand-built filter sum are the same
    operator, not merely analogous;
  - one existing definition recovered as a calculus instance:
    `spectralCalc_indicator_eq_spectralProjector` — the shelf's
    `spectralProjector` is the calculus at the indicator of `(· ≤ c)`;
  - the calculus identity `spectralCalc_id`;
  - the first *consumer* reconciliation (2026-08-25): the Tikhonov
    minimizer of `GraphTheory.Tikhonov` is the calculus at the
    shrinkage function (`tikhonovMinimizer_eq_spectralCalc_mulVec`),
    with the normal equation re-derived through the generic calculus
    algebra (`add_smul_one_mul_spectralCalc_tikhonovShrinkage`) —
    a second, eigenbasis-free route to a delivered statement;
  - the second consumer reconciliation (2026-08-25, later the same
    day): the heat semigroup of `GraphTheory.Heat` is the calculus at
    the exponential family (`heatKernel_eq_spectralCalc_exp`) — a
    genuine reconciliation of two independently built proof stacks
    (the entrywise exponential-series machinery behind
    `heatKernel_mulVec_eq_sum` against Mathlib's `cfc`), with the
    semigroup law re-derived through the calculus algebra
    (`heatKernel_mul_heatKernel_of_spectralCalc`) as the second,
    eigenbasis-free route to `Heat.lean`'s `heatKernel_mul_heatKernel`.
  - the first complex consumer (2026-08-25,
    `proposals/hermitian-calculus-consumer-magnetic.md`): the magnetic
    heat propagator `magneticHeat A Θ t` — the calculus of the
    delivered `magneticLaplacian` at `x ↦ e^{-t·x}`, through Mathlib's
    `RCLike`-generic `cfc` at 𝕜 = ℂ directly (no second wrapper, per
    the bridge's Step-0 verdict) — with the general eigen-action
    engine `cfc_mulVec_eq_smul_of_mulVec_eq_smul` (the calculus acts
    at eigenvalues on EVERY eigenvector, proved by pure matrix
    algebra through unitary diagonalization; Mathlib's calculus file
    has no such lemma), the entry form, the action interfaces, time
    zero, and the semigroup law through the generic calculus algebra.

  What this module is NOT (and must never be described as):
  - NOT a re-proof of the finite-dimensional spectral theorem —
    Mathlib's `cfc` is consumed, not rebuilt;
  - NOT a path to retiring any of Scaffold's explicit axioms: the two
    Perron–Frobenius-family axioms concern nonnegative, generally
    non-Hermitian matrices, and the eight concentration axioms are a
    different mathematical domain entirely;
  - NOT a replacement for Krylov/Chebyshev approximation
    (`GraphTheory.Krylov`, `GraphTheory.PolyFilter`) — the calculus
    gives exact semantics for `f(A)`, not its iterative computation.

  The complex half: Mathlib's `cfc` is stated for any `[RCLike 𝕜]`, so
  complex-Hermitian consumers (e.g. the magnetic Laplacian, whose
  `magneticLaplacian_isHermitian` is hypothesis-free) use
  `Matrix.IsHermitian.cfc` at `𝕜 = ℂ` directly; no second wrapper is
  added (the Step-0 API-split verdict of
  `proposals/hermitian-functional-calculus-bridge.md`). The complex
  half is confirmed elaborating by a QA witness.

  This module carries no `axiom` declarations.

  Source (the consumed calculus):
  - Mathlib, `Mathlib/LinearAlgebra/Matrix/HermitianFunctionalCalculus.lean`
    (Bannon–Loreaux, 2024): `Matrix.IsHermitian.cfc`, `cfc_eq`,
    the `ContinuousFunctionalCalculus` instance and its uniqueness.
-/

import Scaffold.Mathlib.GraphTheory.Spectral
import Scaffold.Mathlib.GraphTheory.Tikhonov
import Scaffold.Mathlib.GraphTheory.Heat
import Scaffold.Mathlib.GraphTheory.Magnetic
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus

open scoped BigOperators Matrix ComplexConjugate

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## The calculus wrapper
-/

/-- **The Hermitian functional calculus at the shelf's convention.**
`spectralCalc M hM f` is Mathlib's continuous functional calculus
`Matrix.IsHermitian.cfc` of the real-symmetric matrix `M` at the bare
function `f : ℝ → ℝ` — no continuity hypothesis, since a finite
spectrum makes every function continuous there. By Mathlib's
spectral-theorem realization, `f(M) = U * diagonal (f ∘ eigenvalues)
* U*` with `U` the eigenbasis unitary, i.e. the operator acting as
`f(λᵢ)` on each eigenvector and linearly elsewhere. -/
noncomputable def spectralCalc (M : Matrix V V ℝ) (hM : M.IsSymm)
    (f : ℝ → ℝ) : Matrix V V ℝ :=
  (isHermitian_of_isSymm hM).cfc f

/-!
## The bridge theorems
-/

/-- **Entry form of the calculus** — the falsifiability anchor: the
calculus's `f(M)` is entrywise the eigenbasis filter sum
`∑ i, f (eigvalOf M hM i) * eigvecOf M hM i a * eigvecOf M hM i b`,
the exact shape of the shelf's `spectralProjector` with the indicator
weight generalized to `f`. A wrong calculus specialization or a
mismatched eigenbasis convention breaks this equality loudly. -/
theorem spectralCalc_apply (M : Matrix V V ℝ) (hM : M.IsSymm)
    (f : ℝ → ℝ) (a b : V) :
    spectralCalc M hM f a b
      = ∑ i, f (eigvalOf M hM i) * eigvecOf M hM i a * eigvecOf M hM i b := by
  have ha : ∀ x : V, eigvecOf M hM x a
      = ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ) a x :=
    fun x => rfl
  have hb : ∀ x : V, eigvecOf M hM x b
      = ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ) b x :=
    fun x => rfl
  have hm : ∀ x : V, f (eigvalOf M hM x)
      = RCLike.ofReal (f ((isHermitian_of_isSymm hM).eigenvalues x)) :=
    fun x => rfl
  show ((isHermitian_of_isSymm hM).cfc f) a b = _
  rw [Matrix.IsHermitian.cfc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply, star_trivial,
    Function.comp_apply, Function.comp_apply, ha x, hb x, hm x]
  ring

/-- **The calculus is the shelf's filter-sum operator.** `f(M) *ᵥ y`
is exactly the filtered signal `∑ i, f (λᵢ) (vᵢ ⬝ᵥ y) • vᵢ` of the
graph-signal-processing expansion behind
`GraphTheory.Tikhonov.dotProduct_eigvecOf_filter` — the calculus and
the hand-built machinery compute the same vector, so every existing
filter consumer can be read as a calculus instance. -/
theorem spectralCalc_mulVec_apply (M : Matrix V V ℝ) (hM : M.IsSymm)
    (f : ℝ → ℝ) (y : V → ℝ) (a : V) :
    (spectralCalc M hM f *ᵥ y) a
      = ∑ i, f (eigvalOf M hM i)
          * Matrix.dotProduct (eigvecOf M hM i) y * eigvecOf M hM i a := by
  have h1 : (spectralCalc M hM f *ᵥ y) a
      = ∑ b, spectralCalc M hM f a b * y b := by
    simp only [Matrix.mulVec, Matrix.dotProduct]
  rw [h1]
  simp only [spectralCalc_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show Matrix.dotProduct (eigvecOf M hM i) y
        = ∑ x, eigvecOf M hM i x * y x from rfl,
    Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **Eigenvector action of the calculus** (hypothesis-free): every
eigenbasis vector of `M` is an eigenvector of `f(M)` with eigenvalue
`f (eigvalOf M hM k)` — the load-bearing bridge every downstream
calculus consumer needs. -/
theorem spectralCalc_mulVec_eigvecOf (M : Matrix V V ℝ) (hM : M.IsSymm)
    (f : ℝ → ℝ) (k : V) :
    spectralCalc M hM f *ᵥ eigvecOf M hM k
      = f (eigvalOf M hM k) • eigvecOf M hM k := by
  funext a
  rw [spectralCalc_mulVec_apply M hM f (eigvecOf M hM k) a]
  have hco : ∀ i : V, Matrix.dotProduct (eigvecOf M hM i) (eigvecOf M hM k)
      = if i = k then 1 else 0 := fun i => eigvecOf_inner M hM i k
  simp only [hco]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ k (fun i => f (eigvalOf M hM i) * eigvecOf M hM i a)]
  simp only [Finset.mem_univ, if_true, Pi.smul_apply, smul_eq_mul]

/-- **The coefficient bridge to the shelf's workhorse.** The
eigenbasis coefficient of the calculus output is the filtered
coefficient — this is `GraphTheory.Tikhonov.dotProduct_eigvecOf_filter`
consumed verbatim at the calculus output, the literal equality of
Step 3 of the bridge proposal: the shelf's arbitrary-filter expansion
and the calculus agree coefficient-by-coefficient. -/
theorem dotProduct_eigvecOf_spectralCalc_mulVec (M : Matrix V V ℝ)
    (hM : M.IsSymm) (f : ℝ → ℝ) (y : V → ℝ) (k : V) :
    Matrix.dotProduct (eigvecOf M hM k) (spectralCalc M hM f *ᵥ y)
      = f (eigvalOf M hM k) * Matrix.dotProduct (eigvecOf M hM k) y := by
  have hv : spectralCalc M hM f *ᵥ y
      = fun a => ∑ i, f (eigvalOf M hM i)
          * Matrix.dotProduct (eigvecOf M hM i) y * eigvecOf M hM i a :=
    funext fun a => spectralCalc_mulVec_apply M hM f y a
  rw [hv]
  exact dotProduct_eigvecOf_filter hM f y k

/-- **The shelf's `spectralProjector` is a calculus instance**: at the
indicator of `(· ≤ c)` the calculus returns exactly the hand-built
`spectralProjector M hM c`. This recovers an existing delivered
definition from the new interface — the proof the bridge is real
rather than decorative. -/
theorem spectralCalc_indicator_eq_spectralProjector (M : Matrix V V ℝ)
    (hM : M.IsSymm) (c : ℝ) :
    spectralCalc M hM (fun x => if x ≤ c then 1 else 0)
      = spectralProjector M hM c := by
  ext a b
  rw [spectralCalc_apply M hM (fun x => if x ≤ c then 1 else 0) a b]
  simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter]
  rfl

/-- **The calculus fixes `M` at the identity function** — the
fundamental property of any functional calculus, here at the shelf's
wrapper. -/
theorem spectralCalc_id (M : Matrix V V ℝ) (hM : M.IsSymm) :
    spectralCalc M hM (fun x => x) = M := by
  ext a b
  rw [spectralCalc_apply M hM (fun x => x) a b]
  have hMab : M a b
      = ∑ i, eigvalOf M hM i * eigvecOf M hM i a * eigvecOf M hM i b := by
    conv_lhs => rw [(isHermitian_of_isSymm hM).spectral_theorem]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hm : ∀ x : V, eigvalOf M hM x
        = RCLike.ofReal ((isHermitian_of_isSymm hM).eigenvalues x) :=
      fun x => rfl
    have ha : ∀ x : V, eigvecOf M hM x a
        = ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ) a x :=
      fun x => rfl
    have hb : ∀ x : V, eigvecOf M hM x b
        = ((isHermitian_of_isSymm hM).eigenvectorUnitary : Matrix V V ℝ) b x :=
      fun x => rfl
    rw [Matrix.mul_diagonal, Matrix.star_apply, star_trivial,
      Function.comp_apply, ha x, hb x, hm x]
    ring
  rw [hMab]

/-!
## Recovered instances: the Tikhonov filter

The first consumer reconciliation
(`proposals/hermitian-calculus-consumer-tikhonov-heat.md`, 2026-08-25):
the Tikhonov smoothing filter — delivered 2026-08-20 as an
*eigenbasis* construction in `GraphTheory.Tikhonov` — is the
functional calculus at the shrinkage function `π ↦ π/(λ+π)`. The
equality is an identity of definitions (the bridge's action form was
stated in exactly the minimizer's filter-sum shape), and the
substantive layer is the normal equation *re-derived through the
generic calculus algebra* (`cfc_mul`, `cfc_add_const`, `cfc_congr`
through `Matrix.IsHermitian.cfc_eq`) — a proof route that never
touches the shelf's eigenbasis machinery, giving two independent
routes to the same nontrivial statement. Per the proposal's
non-goals, `Tikhonov.lean` stays exactly as delivered; these theorems
are additive.
-/

/-- **Every function is continuous on a matrix's real spectrum** —
the finite-spectrum fact that supplies the `ContinuousOn` hypotheses
of Mathlib's generic functional-calculus lemmas. The auto-param
`cfc_cont_tac` runs `fun_prop`, which cannot discharge these for
spectral-data functions (e.g. `tikhonovShrinkage π`, continuous only
off `λ = -π`), so calculus consumers pass this supplier explicitly. -/
theorem continuousOn_of_finite_real_spectrum {M : Matrix V V ℝ}
    (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ M) := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_of_discreteTopology

/-- `algebraMap ℝ (Matrix V V ℝ) π` is the scalar matrix `π • 1`
(entrywise; the two forms differ only in the `diagonal` packaging). -/
private theorem algebraMap_matrix_eq_smul_one {π : ℝ} :
    algebraMap ℝ (Matrix V V ℝ) π = π • (1 : Matrix V V ℝ) := by
  ext i j
  rw [Matrix.algebraMap_matrix_apply]
  by_cases h : i = j
  · subst h
    simp [Matrix.smul_apply, Matrix.one_apply]
  · simp [h, Matrix.smul_apply, Matrix.one_apply]

/-- **The Tikhonov minimizer is the functional calculus at the
shrinkage function** — the bridge's falsifiability test at a real
consumer: `x* = f(L) *ᵥ y` with `f = tikhonovShrinkage π`, i.e. the
eigenbasis-defined minimizer of `Tikhonov.lean` and the calculus
wrapper at `fun λ => π / (λ + π)` are the same vector.
Hypothesis-free: symmetry only enters through the eigenbasis both
sides share, and the identity holds at every `π` (at degenerate `π`
hitting `-λ_k` both sides carry the same junk values — the calculus
evaluates `f` exactly at the eigenvalues). A wrong calculus
specialization, a mismatched eigenbasis convention, or a wrong
minimizer formula breaks this equality loudly. -/
theorem tikhonovMinimizer_eq_spectralCalc_mulVec (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (π : ℝ) (y : V → ℝ) :
    tikhonovMinimizer A hA π y
      = spectralCalc (laplacian A) (laplacian_symmetric A hA)
          (tikhonovShrinkage π) *ᵥ y := by
  funext a
  rw [spectralCalc_mulVec_apply]
  rfl

/-- **The normal equation through the calculus algebra** (the
substantive reconciliation layer): `(L + π•1) * f(L) = π • 1` at
`f = tikhonovShrinkage π`, i.e. the Tikhonov filter is `π` times the
resolvent of `L + π•1` — *re-derived here through Mathlib's generic
continuous-functional-calculus algebra* (`cfc_mul`, `cfc_add_const`,
`cfc_congr`, `cfc_const` after `Matrix.IsHermitian.cfc_eq`), a route
independent of the shelf's eigenbasis expansion that carries the
delivered `tikhonovMinimizer_add_smul_one_mulVec`. The mathematical
content is that `tikhonovShrinkage π · (λ + π) = π` *on the
spectrum*: PSD makes every spectral point nonnegative, so `0 < π`
keeps the division non-junk there, and `cfc_congr` promotes the
pointwise identity to the operator identity. The `0 < π` hypothesis
is load-bearing: at `π = -λ` for a spectral `λ` the shrinkage is the
junk `0` at that point and the identity fails (the QA fence exhibits
this on `K₂` at `π = -2`). -/
theorem add_smul_one_mul_spectralCalc_tikhonovShrinkage
    (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) {π : ℝ} (hπ : 0 < π) :
    (laplacian A + π • (1 : Matrix V V ℝ))
      * spectralCalc (laplacian A) (laplacian_symmetric A hA)
          (tikhonovShrinkage π)
      = π • (1 : Matrix V V ℝ) := by
  have hL : (laplacian A).IsSymm := laplacian_symmetric A hA
  have hherm : Matrix.IsHermitian (laplacian A) := isHermitian_of_isSymm hL
  have hsa : IsSelfAdjoint (laplacian A) := hherm
  -- PSD: every real spectral point of the Laplacian is nonnegative
  have hspec : ∀ x ∈ spectrum ℝ (laplacian A), 0 ≤ x := by
    intro x hx
    rw [Matrix.IsHermitian.eigenvalues_eq_spectrum_real] at hx
    obtain ⟨i, hi⟩ := hx
    rw [← hi]
    exact eigvalOf_laplacian_nonneg A hA hnonneg i
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ (laplacian A)) :=
    fun f => continuousOn_of_finite_real_spectrum f
  -- the additive layer: the calculus at `λ ↦ λ + π` is `L + π • 1`
  have h1 : cfc (fun x => x + π) (laplacian A)
      = laplacian A + π • (1 : Matrix V V ℝ) := by
    rw [cfc_add_const π (fun x => x) (laplacian A) (hcont _),
      cfc_id' ℝ (laplacian A) hsa, algebraMap_matrix_eq_smul_one]
  -- the multiplicative layer, assembled at the wrapper
  rw [show spectralCalc (laplacian A) hL (tikhonovShrinkage π)
      = cfc (tikhonovShrinkage π) (laplacian A) from by
      show (isHermitian_of_isSymm hL).cfc _ = _
      rw [← Matrix.IsHermitian.cfc_eq]]
  conv_lhs => rw [← h1]
  rw [← cfc_mul (fun x => x + π) (tikhonovShrinkage π) (laplacian A)
    (hcont _) (hcont _),
    cfc_congr (f := fun x => (fun x => x + π) x * tikhonovShrinkage π x)
      (g := fun _ => π) (by
        intro x hx
        have hxnn := hspec x hx
        have hnz : x + π ≠ 0 := by linarith
        show (x + π) * tikhonovShrinkage π x = π
        rw [tikhonovShrinkage, mul_div_cancel₀ _ hnz]),
    cfc_const π (laplacian A) hsa, algebraMap_matrix_eq_smul_one]

/-!
## Recovered instances: the heat semigroup

The second consumer reconciliation
(`proposals/hermitian-calculus-consumer-tikhonov-heat.md`, the Heat
half, 2026-08-25): the heat semigroup — delivered 2026-08-23 through
`NormedSpace.exp` and a from-scratch entrywise exponential-series
machinery in `GraphTheory.Heat` — is the functional calculus at the
exponential family `x ↦ e^{-t·x}`. Unlike the Tikhonov half (whose
equality was an identity of definitions), this reconciliation carries
genuine mathematical content: the two sides were built by independent
proof stacks — the series engine of `Heat.lean` (entrywise summability,
eigenvector action, eigenbasis expansion) against Mathlib's continuous
functional calculus — and their agreement is, in effect, the spectral
mapping theorem for `exp` at real-symmetric matrices. The substantive
second layer mirrors the Tikhonov delivery: the semigroup law
re-derived through the generic calculus algebra (`cfc_mul`/`cfc_congr`
at `Real.exp_add`), a second route to `Heat.lean`'s
`heatKernel_mul_heatKernel` (which used `Matrix.exp_add_of_commute`).
Per the proposal's non-goals, `Heat.lean` stays exactly as delivered;
these theorems are additive.
-/

/-- **Matrices are their actions** (on finite index types): two real
matrices are equal whenever their `mulVec` actions agree on every
vector. The reconciliation tool for action-level equality theorems:
entries are recovered by acting on the coordinate units
`Pi.single j 1`. -/
theorem matrix_eq_of_forall_mulVec_eq (M N : Matrix V V ℝ)
    (h : ∀ x : V → ℝ, M *ᵥ x = N *ᵥ x) : M = N := by
  ext i j
  have hj := h (Pi.single j (1 : ℝ))
  have hM : (M *ᵥ Pi.single j (1 : ℝ)) i = M i j := by
    simp [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply]
  have hN : (N *ᵥ Pi.single j (1 : ℝ)) i = N i j := by
    simp [Matrix.mulVec, Matrix.dotProduct, Pi.single_apply]
  rw [← hM, ← hN]
  exact congrFun hj i

/-- **The heat kernel is the functional calculus at the exponential
family** — the bridge's falsifiability test at its second real
consumer: `heatKernel A t = f(L)` with `f = (x ↦ e^{-t·x})`, i.e. the
matrix-exponential definition (`NormedSpace.exp ℝ (-(t • laplacian
A))`, built through `Heat.lean`'s from-scratch entrywise series
machinery) and the calculus wrapper at the scalar exponential are the
same operator. A genuine reconciliation, not an identity of
definitions: the two sides carry independent proofs
(`heatKernel_mulVec_eq_sum` — the series engine — against
`spectralCalc_mulVec_apply` — Mathlib's `cfc`), joined at exactly the
same filter-sum shape. Symmetry enters only through the eigenbasis
both sides share; a wrong calculus specialization, a mismatched
eigenbasis convention, or a wrong series engine breaks this equality
loudly. -/
theorem heatKernel_eq_spectralCalc_exp (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (t : ℝ) :
    heatKernel A t = spectralCalc (laplacian A) (laplacian_symmetric A hA)
      (fun x => Real.exp (-(t * x))) := by
  refine matrix_eq_of_forall_mulVec_eq _ _ fun x => ?_
  funext a
  rw [heatKernel_mulVec_eq_sum A hA t x,
    spectralCalc_mulVec_apply (laplacian A) (laplacian_symmetric A hA)
      (fun x => Real.exp (-(t * x))) x a]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- **The calculus semigroup at the exponential family**: the calculus
at `x ↦ e^{-s·x}` times the calculus at `x ↦ e^{-t·x}` is the calculus
at `x ↦ e^{-(s+t)·x}` — proved through Mathlib's generic
continuous-functional-calculus algebra (`cfc_mul`, then `cfc_congr`
promoting the pointwise `Real.exp_add` identity from the spectrum), a
route that never touches an eigenbasis. This is the calculus-algebra
mirror of `Matrix.exp_add_of_commute`. -/
theorem spectralCalc_exp_mul (M : Matrix V V ℝ) (hM : M.IsSymm)
    (s t : ℝ) :
    spectralCalc M hM (fun x => Real.exp (-(s * x)))
        * spectralCalc M hM (fun x => Real.exp (-(t * x)))
      = spectralCalc M hM (fun x => Real.exp (-((s + t) * x))) := by
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ M) :=
    fun f => continuousOn_of_finite_real_spectrum f
  have hf : ∀ c : ℝ, spectralCalc M hM (fun x => Real.exp (-(c * x)))
      = cfc (fun x => Real.exp (-(c * x))) M := by
    intro c
    show (isHermitian_of_isSymm hM).cfc _ = _
    rw [Matrix.IsHermitian.cfc_eq]
  rw [hf s, hf t, hf (s + t),
    ← cfc_mul (fun x => Real.exp (-(s * x))) (fun x => Real.exp (-(t * x))) M
      (hc _) (hc _),
    cfc_congr (f := fun x => Real.exp (-(s * x)) * Real.exp (-(t * x)))
      (g := fun x => Real.exp (-((s + t) * x))) (by
        intro x _
        show Real.exp (-(s * x)) * Real.exp (-(t * x))
          = Real.exp (-((s + t) * x))
        rw [← Real.exp_add]
        congr 1
        ring)]

/-- **The semigroup law through the calculus** (the substantive
reconciliation layer): flowing for time `s` then `t` equals flowing for
`s + t`, re-derived by composing the equality theorem with the
calculus-algebra semigroup — a second, eigenbasis-free route to
`Heat.lean`'s `heatKernel_mul_heatKernel` (the `Matrix.exp_add_of_
commute` route). Unlike that theorem this route requires `A.IsSymm`
(the calculus side needs the Hermitian structure); the hypothesis-free
original remains the primary statement, and this corollary witnesses
that the two proof technologies agree. -/
theorem heatKernel_mul_heatKernel_of_spectralCalc (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (s t : ℝ) :
    heatKernel A s * heatKernel A t = heatKernel A (s + t) := by
  rw [heatKernel_eq_spectralCalc_exp A hA s,
    heatKernel_eq_spectralCalc_exp A hA t, spectralCalc_exp_mul,
    ← heatKernel_eq_spectralCalc_exp A hA (s + t)]

/-!
## The magnetic heat propagator: the first complex consumer

The bridge's first genuinely complex consumer
(`proposals/hermitian-calculus-consumer-magnetic.md`, 2026-08-25, its
gate satisfied by the bridge delivery and the QA witness
`fcM2c_cfc_id`): the magnetic heat propagator of the delivered
`GraphTheory.Magnetic.magneticLaplacian` — the calculus at the
exponential family `x ↦ e^{-t·x}`, through Mathlib's `RCLike`-generic
`cfc` at 𝕜 = ℂ directly (per the bridge's Step-0 verdict, no second
wrapper is added; `magneticLaplacian_isHermitian` is hypothesis-free,
so the propagator is defined for ANY real weights — asymmetric
included — and ANY phases).

The load-bearing general engine is `cfc_mulVec_eq_smul_of_mulVec_eq_
smul`: the calculus acts at eigenvalues on EVERY eigenvector — not
just the chosen basis — proved by pure matrix algebra through the
unitary diagonalization (the shifted eigenvector equation transfers
to the diagonal side, where support at the eigenvalue is read off
entrywise), with no eigenspace-completeness machinery anywhere.
Mathlib's calculus file has no such lemma; every complex consumer of
the calculus needs it. Per the proposal's non-goals,
`Magnetic.lean` stays exactly as delivered, there is no magnetic
Cheeger/synchronization content here, and all statements are proved.
-/

variable {𝕜 : Type} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

/-- **The calculus acts at eigenvalues on every eigenvector.** If the
Hermitian matrix `M` has `M *ᵥ x = (μ : 𝕜) • x` at a real eigenvalue
`μ`, then the continuous functional calculus acts on `x` as the
scalar `f μ` — for ANY eigenvector, not just the eigenbasis the
calculus was built from. The proof is pure matrix algebra through the
unitary diagonalization `Uᴴ * M * U = diagonal λ`: the shifted
equation `(M − μ) *ᵥ x = 0` transfers to `(λ − μ) *ᵥ (Uᴴ x) = 0`, so
`Uᴴ x` is supported at the indices with `λ i = μ`, where the
calculus's diagonal acts as `f μ`; no eigenspace-completeness
machinery is needed. This is the interface every downstream consumer
of the complex calculus needs (Mathlib's
`HermitianFunctionalCalculus.lean` does not provide it). -/
theorem cfc_mulVec_eq_smul_of_mulVec_eq_smul {M : Matrix n n 𝕜}
    (hM : M.IsHermitian) {x : n → 𝕜} {μ : ℝ}
    (hx : M *ᵥ x = ((μ : ℝ) : 𝕜) • x) (f : ℝ → ℝ) :
    hM.cfc f *ᵥ x = ((f μ : ℝ) : 𝕜) • x := by
  classical
  have hdiag := hM.star_mul_self_mul_eq_diagonal
  have hUst : (hM.eigenvectorUnitary : Matrix n n 𝕜)
      * star (hM.eigenvectorUnitary : Matrix n n 𝕜) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp (hM.eigenvectorUnitary).2
  have hstU : star (hM.eigenvectorUnitary : Matrix n n 𝕜)
      * (hM.eigenvectorUnitary : Matrix n n 𝕜) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (hM.eigenvectorUnitary).2
  have hshift : (M - ((μ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) *ᵥ x = 0 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec, hx,
      sub_self]
  have hsmul : star (hM.eigenvectorUnitary : Matrix n n 𝕜)
      * (((μ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜))
      * (hM.eigenvectorUnitary : Matrix n n 𝕜)
      = ((μ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) := by
    rw [Matrix.mul_smul, mul_one, Matrix.smul_mul, hstU]
  have hkey : Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
      - ((μ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)
      = star (hM.eigenvectorUnitary : Matrix n n 𝕜)
        * (M - ((μ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜))
        * (hM.eigenvectorUnitary : Matrix n n 𝕜) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hsmul, hdiag]
  have hxy : (hM.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ
      ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hUst, Matrix.one_mulVec]
  have hy0 : (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues)
      - ((μ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜))
      *ᵥ ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) = 0 := by
    have hreg : (star (hM.eigenvectorUnitary : Matrix n n 𝕜)
        * (M - ((μ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜))
        * (hM.eigenvectorUnitary : Matrix n n 𝕜))
        *ᵥ ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x)
        = (star (hM.eigenvectorUnitary : Matrix n n 𝕜))
          *ᵥ ((M - ((μ : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) *ᵥ x) := by
      rw [← Matrix.mulVec_mulVec, hxy, ← Matrix.mulVec_mulVec]
    rw [hkey, hreg, hshift, Matrix.mulVec_zero]
  have hentry : ∀ i, (((hM.eigenvalues i : ℝ) : 𝕜)
      * ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i
      - ((μ : ℝ) : 𝕜) * ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i)
      = 0 := by
    intro i
    have h := congrFun hy0 i
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal,
      Matrix.smul_mulVec_assoc, Matrix.one_mulVec, Function.comp_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    exact h
  have hsupp : ∀ i, ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i ≠ 0
      → hM.eigenvalues i = μ := fun i hne => by
    have h1 := hentry i
    rw [sub_eq_zero] at h1
    exact RCLike.ofReal_injective (mul_right_cancel₀ hne h1)
  show ((hM.eigenvectorUnitary : Matrix n n 𝕜)
      * Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues)
      * star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hdiagF : Matrix.diagonal (RCLike.ofReal ∘ f ∘ hM.eigenvalues) *ᵥ
      ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x)
      = ((f μ : ℝ) : 𝕜) • ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) := by
    funext i
    rw [Matrix.mulVec_diagonal]
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hz : ((star (hM.eigenvectorUnitary : Matrix n n 𝕜)) *ᵥ x) i = 0
    · rw [hz]; ring
    · rw [hsupp i hz]
  rw [hdiagF, Matrix.mulVec_smul, hxy]

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **The magnetic heat propagator** — the bridge's first complex
consumer: the functional calculus of the magnetic Laplacian at the
exponential family `x ↦ e^{-t·x}`,
`e^{-t·M(A,Θ)} := (magneticLaplacian_isHermitian A Θ).cfc …` — the
complex analogue of `Heat.lean`'s `heatKernel`, built by consuming
Mathlib's `RCLike`-generic calculus at 𝕜 = ℂ directly (no second
wrapper, per the bridge's Step-0 verdict). Hypothesis-free by the
magnetic Laplacian's structural Hermiticity: defined for ANY real
weights (asymmetric included) and ANY phases. The semigroup of the
phase-frustrated diffusion; see `magneticHeat_mulVec_of_eigen` for the
action and `magneticHeat_mul_magneticHeat` for the semigroup law. -/
noncomputable def magneticHeat (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) (t : ℝ) :
    Matrix V V ℂ :=
  (magneticLaplacian_isHermitian A Θ).cfc (fun x => Real.exp (-(t * x)))

/-- **Entry form of the magnetic heat propagator** — the complex
mirror of `spectralCalc_apply` and the falsifiability anchor: the
propagator is entrywise the complex-eigenbasis filter sum with
exponentially damped weights. A wrong calculus specialization or a
mismatched complex-eigenbasis convention breaks this equality loudly. -/
theorem magneticHeat_apply (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) (t : ℝ)
    (a b : V) :
    magneticHeat A Θ t a b
      = ∑ i, ((Real.exp (-(t * (magneticLaplacian_isHermitian A Θ).eigenvalues i)) : ℂ)
          * (magneticLaplacian_isHermitian A Θ).eigenvectorUnitary a i
          * conj ((magneticLaplacian_isHermitian A Θ).eigenvectorUnitary b i)) := by
  show (((magneticLaplacian_isHermitian A Θ).cfc
      fun x => Real.exp (-(t * x))) a b) = _
  rw [Matrix.IsHermitian.cfc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_diagonal, Matrix.star_apply, Complex.star_def]
  simp only [Function.comp_apply]
  ac_rfl

/-- **The propagator acts at eigenvalues on every eigenvector of the
magnetic Laplacian** — the consumer action interface: any eigenvector
of `M(A, Θ)` at a real eigenvalue `μ` is an eigenvector of the
propagator at the decay factor `e^{-t·μ}`. The balanced-potential
kernel modes are invariant (`e⁰ = 1`); every other mode decays. This
is `cfc_mulVec_eq_smul_of_mulVec_eq_smul` at the exponential family,
and it holds for arbitrary directed weights and phases (Hermiticity
is structural). -/
theorem magneticHeat_mulVec_of_eigen (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    {x : V → ℂ} {μ : ℝ}
    (hx : magneticLaplacian A Θ *ᵥ x = ((μ : ℝ) : ℂ) • x) (t : ℝ) :
    magneticHeat A Θ t *ᵥ x
      = ((Real.exp (-(t * μ)) : ℝ) : ℂ) • x :=
  cfc_mulVec_eq_smul_of_mulVec_eq_smul _ hx _

/-- **The basis action**: the propagator acts on Mathlib's complex
eigenbasis vectors of the magnetic Laplacian with the decay factors
`e^{-t·μᵢ}` — the proposal's literal ask, as a corollary of the
arbitrary-eigenvector action at `mulVec_eigenvectorBasis`. -/
theorem magneticHeat_mulVec_eigenvectorBasis (A : Matrix V V ℝ)
    (Θ : Matrix V V ℝ) (t : ℝ) (j : V) :
    magneticHeat A Θ t *ᵥ
      ⇑((magneticLaplacian_isHermitian A Θ).eigenvectorBasis j)
      = ((Real.exp (-(t * (magneticLaplacian_isHermitian A Θ).eigenvalues j)) : ℝ) : ℂ)
        • ⇑((magneticLaplacian_isHermitian A Θ).eigenvectorBasis j) := by
  refine magneticHeat_mulVec_of_eigen A Θ ?_ t
  have h := (magneticLaplacian_isHermitian A Θ).mulVec_eigenvectorBasis j
  rw [h]
  funext i
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]

/-- **Every function is continuous on any matrix's real spectrum** —
the `𝕜`-generic supplier behind the calculus-algebra layer (the
complex-spectrum sibling of
`continuousOn_of_finite_real_spectrum`; the spectrum of ANY square
matrix over an `RCLike` field is finite, so every real function is
continuous on it). -/
theorem continuousOn_of_finite_spectrum {M : Matrix n n 𝕜} (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ M) := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_of_discreteTopology

/-- **Time zero**: flowing for zero time is the identity — the
calculus at the constant-one function, through the generic
calculus algebra. -/
theorem magneticHeat_zero (A : Matrix V V ℝ) (Θ : Matrix V V ℝ) :
    magneticHeat A Θ 0 = 1 := by
  have hf : (fun x => Real.exp (-((0 : ℝ) * x))) = fun _ => 1 :=
    funext fun x => by simp [Real.exp_zero]
  unfold magneticHeat
  rw [hf]
  have hsa : IsSelfAdjoint (magneticLaplacian A Θ) :=
    magneticLaplacian_isHermitian A Θ
  have hcfc := Matrix.IsHermitian.cfc_eq (f := fun _ => (1 : ℝ))
    (A := magneticLaplacian A Θ) (magneticLaplacian_isHermitian A Θ)
  rw [← hcfc, cfc_const (1 : ℝ) (magneticLaplacian A Θ) hsa, map_one]

/-- **The semigroup law through the complex calculus algebra**:
flowing for time `s` then `t` equals flowing for `s + t` — proved
through Mathlib's generic continuous-functional-calculus algebra
(`cfc_mul`, then `cfc_congr` promoting the pointwise `Real.exp_add`
identity from the spectrum), the complex instantiation of the
delivered `spectralCalc_exp_mul` technology; no eigenbasis anywhere. -/
theorem magneticHeat_mul_magneticHeat (A : Matrix V V ℝ) (Θ : Matrix V V ℝ)
    (s t : ℝ) :
    magneticHeat A Θ s * magneticHeat A Θ t = magneticHeat A Θ (s + t) := by
  have hsa : IsSelfAdjoint (magneticLaplacian A Θ) :=
    magneticLaplacian_isHermitian A Θ
  have hc : ∀ f : ℝ → ℝ,
      ContinuousOn f (spectrum ℝ (magneticLaplacian A Θ)) :=
    fun f => continuousOn_of_finite_spectrum f
  have hf : ∀ c : ℝ, magneticHeat A Θ c
      = cfc (fun x => Real.exp (-(c * x))) (magneticLaplacian A Θ) := by
    intro c
    unfold magneticHeat
    rw [Matrix.IsHermitian.cfc_eq]
  rw [hf s, hf t, hf (s + t),
    ← cfc_mul (fun x => Real.exp (-(s * x))) (fun x => Real.exp (-(t * x)))
      (magneticLaplacian A Θ) (hc _) (hc _),
    cfc_congr (f := fun x => Real.exp (-(s * x)) * Real.exp (-(t * x)))
      (g := fun x => Real.exp (-((s + t) * x))) (by
      intro x _
      show Real.exp (-(s * x)) * Real.exp (-(t * x))
        = Real.exp (-((s + t) * x))
      rw [← Real.exp_add]
      congr 1
      ring)]

end SpectralGraphTheory
