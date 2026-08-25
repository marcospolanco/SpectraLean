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
  - the calculus identity `spectralCalc_id`.

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
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus

open scoped BigOperators Matrix

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

end SpectralGraphTheory
