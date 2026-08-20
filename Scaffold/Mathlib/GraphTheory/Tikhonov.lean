/-
  Tikhonov.lean

  Purpose
  -------
  Tikhonov regularization in the Laplacian eigenbasis: the graph-signal
  smoothing operator minimizing `‖x − y‖² + (1/π) · xᵀLx`, its
  closed-form eigencoefficient shrinkage identity, minimality and
  uniqueness, and the shrinkage-factor arithmetic layer. Proposal
  `proposals/tikhonov-shrinkage-filter.md` (the Active priority table's
  top High row at delivery time), delivered as pure hard crust: no
  `axiom` declarations, every theorem proved from the eigenbasis
  machinery of `Scaffold.Mathlib.GraphTheory.Spectral` — orthonormality
  (`eigvecOf_inner`), completeness (`eigvecOf_expansion_apply`),
  Parseval (`dotProduct_eigvecOf`), the spectral resolution
  (`quadForm_eigvalOf`), and the eigenaction
  (`mulVec_eigvecOf_sum_apply`).

  Definition route (recorded per the proposal's standing rule): the
  minimizer is *defined directly* by the eigenbasis formula
  `x* = ∑_k (π/(λ_k + π)) (v_k ⬝ᵥ y) • v_k`, not extracted by
  `Classical.choice` from a strict-convexity argument. The formula makes
  every interface theorem (coefficient identity, normal equation,
  minimality) a computation, and uniqueness a corollary of the
  strict-convexity decomposition
  `obj(x) − obj(x*) = ∑_k (1 + λ_k/π)(d_k − d*_k)²`.

  Statement-shape deviation from the proposal's Step 3, recorded here:
  the proposal claims the attenuation factor is "never exactly 0 or 1".
  That is half right — it is never `0` — but at a zero eigenvalue the
  factor is *exactly* `1` (`π/(0+π) = 1`), and this is a feature, not a
  defect: the kernel modes (constants, on a connected graph) pass
  through the filter untouched, which is precisely mean preservation
  (`sum_tikhonovMinimizer_eq_sum`). The delivered statements are the
  true ones: `0 < factor`, `factor ≤ 1`, `factor < 1 ↔ 0 < λ`,
  `factor = 1 ↔ λ = 0`, and strict antitonicity on `λ ≥ 0`.

  The not-a-projection distinction the proposal asks to state
  explicitly: unlike `spectralProjector` (which zeroes every mode
  outside a band exactly and fixes every mode inside it), the Tikhonov
  filter attenuates every nonzero mode by a factor strictly in `(0, 1)`
  — nothing is exactly zeroed, and no nonzero mode is exactly fixed.
  The precise theorem is the failure of idempotence
  (`tikhonovMinimizer_ne_apply_self_of_eigvalOf_pos`): the filter of an
  eigenvector input is a *strictly* shrunk copy, so filtering twice
  differs from filtering once.

  External consumer (context, not citation): this is the standard
  smoothing operator of graph signal processing — semi-supervised label
  propagation and graph-signal denoising. The literature citation in
  the proposal is explicitly unverified and is therefore *not* repeated
  here; see the proposal for provenance status.

  Related modules: the eigenbasis machinery and Laplacian PSD facts
  live in `Scaffold.Mathlib.GraphTheory.Spectral`; the shifted-matrix
  invertibility tooling this module's normal equation complements lives
  in `Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent`.
-/

import Scaffold.Mathlib.GraphTheory.Spectral

open scoped BigOperators Matrix

namespace SpectralGraphTheory

variable {V : Type} [Fintype V] [DecidableEq V]

/-!
## 0. The shrinkage factor (generic arithmetic layer)

Pure ordered-field facts about `π / (λ + π)`, stated for real `π`, `λ`
with no matrix attached, so any spectral-filter consumer can reuse
them.
-/

/-- The Tikhonov shrinkage (attenuation) factor: the multiplier
`π / (λ + π)` that the minimizer applies to the eigencomponent of the
signal along an eigenvector of eigenvalue `λ`. -/
noncomputable def tikhonovShrinkage (π lam : ℝ) : ℝ := π / (lam + π)

/-- The shrinkage factor is positive whenever `π > 0` and `λ ≥ 0`. -/
theorem tikhonovShrinkage_pos {π lam : ℝ} (hπ : 0 < π) (hlam : 0 ≤ lam) :
    0 < tikhonovShrinkage π lam := by
  rw [tikhonovShrinkage]
  exact div_pos hπ (by linarith)

/-- The shrinkage factor never annihilates a mode: with `π > 0` and
`λ ≥ 0` the factor is nonzero. (No mode is exactly zeroed — half of
the proposal's Step-3 claim, the true half.) -/
theorem tikhonovShrinkage_ne_zero {π lam : ℝ} (hπ : 0 < π)
    (hlam : 0 ≤ lam) :
    tikhonovShrinkage π lam ≠ 0 :=
  ne_of_gt (tikhonovShrinkage_pos hπ hlam)

/-- The shrinkage factor is at most one on nonnegative eigenvalues. -/
theorem tikhonovShrinkage_le_one {π lam : ℝ} (hπ : 0 < π)
    (hlam : 0 ≤ lam) :
    tikhonovShrinkage π lam ≤ 1 := by
  have hpos : (0:ℝ) < lam + π := by linarith
  have h1 : 1 - tikhonovShrinkage π lam
      = lam / (lam + π) := by
    rw [tikhonovShrinkage]
    field_simp
  have h2 : 0 ≤ 1 - tikhonovShrinkage π lam := by
    rw [h1]; exact div_nonneg hlam (le_of_lt hpos)
  linarith

/-- A *positive* eigenvalue's mode is strictly attenuated. -/
theorem tikhonovShrinkage_lt_one {π lam : ℝ} (hπ : 0 < π)
    (hlam : 0 < lam) :
    tikhonovShrinkage π lam < 1 := by
  have hpos : (0:ℝ) < lam + π := by linarith
  have h1 : 1 - tikhonovShrinkage π lam
      = lam / (lam + π) := by
    rw [tikhonovShrinkage]
    field_simp
  have h2 : 0 < 1 - tikhonovShrinkage π lam := by
    rw [h1]; exact div_pos hlam hpos
  linarith

/-- A zero eigenvalue's mode passes through *exactly* unchanged — the
kernel mode is fixed, which is the engine of mean preservation. This
corrects the proposal's Step-3 sketch ("never exactly 1"): at `λ = 0`
the factor is exactly `1`, and that is the correct behavior. -/
theorem tikhonovShrinkage_eq_one_iff {π lam : ℝ} (hπ : π ≠ 0) :
    tikhonovShrinkage π lam = 1 ↔ lam = 0 := by
  constructor
  · intro h
    rcases eq_or_ne (lam + π) 0 with h₀ | h₀
    · rw [tikhonovShrinkage, h₀, div_zero] at h
      norm_num at h
    · rw [tikhonovShrinkage] at h
      field_simp [h₀] at h
      linarith
  · intro h
    rw [h, tikhonovShrinkage, zero_add, div_self hπ]

/-- The shrinkage factor is strictly decreasing in the eigenvalue on
`λ ≥ 0` (with `π > 0`): larger eigenvalues are attenuated more. -/
theorem tikhonovShrinkage_lt_tikhonovShrinkage {π lam₁ lam₂ : ℝ}
    (hπ : 0 < π) (h₁ : 0 ≤ lam₁) (h : lam₁ < lam₂) :
    tikhonovShrinkage π lam₂ < tikhonovShrinkage π lam₁ := by
  have hpos1 : (0:ℝ) < lam₁ + π := by linarith
  have hpos2 : (0:ℝ) < lam₂ + π := by linarith
  have hkey : tikhonovShrinkage π lam₁ - tikhonovShrinkage π lam₂
      = π * (lam₂ - lam₁) / ((lam₁ + π) * (lam₂ + π)) := by
    rw [tikhonovShrinkage, tikhonovShrinkage]
    field_simp
    linarith
  have h2 : 0 < tikhonovShrinkage π lam₁ - tikhonovShrinkage π lam₂ := by
    rw [hkey]
    exact div_pos (mul_pos hπ (by linarith)) (mul_pos hpos1 hpos2)
  linarith

/-!
## 1. The minimizer and its eigencoefficient identity

The minimizer is defined by the eigenbasis formula; its coefficient
along any eigenvector is the shrunk coefficient of the signal. The
identity needs no hypothesis at all — it is pure orthonormality, and
holds for every `π` (at `π` hitting `−λ_k` both sides carry the same
junk division).
-/

/-- Eigenbasis expansion is injective: two vectors with equal
coefficients along every eigenvector are equal. (The uniqueness engine
behind the minimizer's characterization theorems.) -/
theorem ext_of_dotProduct_eigvecOf_eq {M : Matrix V V ℝ} (hM : M.IsSymm)
    {x z : V → ℝ}
    (h : ∀ i, Matrix.dotProduct (eigvecOf M hM i) x
      = Matrix.dotProduct (eigvecOf M hM i) z) :
    x = z := by
  funext a
  rw [← eigvecOf_expansion_apply hM x a, ← eigvecOf_expansion_apply hM z a]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

/-- **Spectral-filter coefficient identity (the workhorse).** The
coefficient along `v_k` of the filtered signal `∑_i g(λ_i) (v_i ⬝ᵥ y) •
v_i` is `g(λ_k) (v_k ⬝ᵥ y)`: orthonormality collapses the double sum to
the diagonal term. Stated for an arbitrary filter function `g` on the
eigenvalues, since nothing in the computation is specific to the
Tikhonov factor — any graph-signal-processing filter consumer can reuse
it. -/
theorem dotProduct_eigvecOf_filter {M : Matrix V V ℝ} (hM : M.IsSymm)
    (g : ℝ → ℝ) (y : V → ℝ) (k : V) :
    Matrix.dotProduct (eigvecOf M hM k)
        (fun a => ∑ i, g (eigvalOf M hM i)
          * Matrix.dotProduct (eigvecOf M hM i) y * eigvecOf M hM i a)
      = g (eigvalOf M hM k) * Matrix.dotProduct (eigvecOf M hM k) y := by
  have h1 : Matrix.dotProduct (eigvecOf M hM k)
        (fun a => ∑ i, g (eigvalOf M hM i)
          * Matrix.dotProduct (eigvecOf M hM i) y * eigvecOf M hM i a)
      = ∑ a, eigvecOf M hM k a * ∑ i, g (eigvalOf M hM i)
          * Matrix.dotProduct (eigvecOf M hM i) y * eigvecOf M hM i a := rfl
  rw [h1]
  have h2 : ∀ a : V, eigvecOf M hM k a * ∑ i, g (eigvalOf M hM i)
      * Matrix.dotProduct (eigvecOf M hM i) y * eigvecOf M hM i a
      = ∑ i, g (eigvalOf M hM i) * Matrix.dotProduct (eigvecOf M hM i) y
        * (eigvecOf M hM k a * eigvecOf M hM i a) := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h2]
  rw [Finset.sum_comm]
  have h3 : ∀ i : V, ∑ a, g (eigvalOf M hM i)
      * Matrix.dotProduct (eigvecOf M hM i) y
      * (eigvecOf M hM k a * eigvecOf M hM i a)
      = g (eigvalOf M hM i) * Matrix.dotProduct (eigvecOf M hM i) y
        * ∑ a, eigvecOf M hM k a * eigvecOf M hM i a := by
    intro i
    rw [← Finset.mul_sum]
  have horthon : ∀ i : V, ∑ a, eigvecOf M hM k a * eigvecOf M hM i a
      = if k = i then 1 else 0 := fun i =>
    eigvecOf_inner M hM k i
  simp only [h3, horthon]
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hi
    rw [if_neg (Ne.symm hi), mul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ k) hcon

/-- Every Laplacian eigenvalue of a symmetric nonnegative network is
nonnegative: the quadratic form at a unit eigenvector is the eigenvalue
(`quadForm_eigvecOf_self`) and the form is nonnegative
(`laplacian_psd`). -/
theorem eigvalOf_laplacian_nonneg (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (hnonneg : ∀ i j, 0 ≤ A i j) (i : V) :
    0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) i := by
  have hpsd := laplacian_psd A hA hnonneg
    (eigvecOf (laplacian A) (laplacian_symmetric A hA) i)
  rw [quadForm_eigvecOf_self (laplacian_symmetric A hA) i] at hpsd
  exact hpsd

/-- **The Tikhonov minimizer**, defined by the eigenbasis formula:
`x* = ∑_k (π/(λ_k + π)) (v_k ⬝ᵥ y) • v_k` over the orthonormal
Laplacian eigenbasis. This is the closed-form solution of the
regularized least-squares problem — every mode of the signal shrunk by
the factor `π/(λ_k + π)`; see `tikhonovObjective_minimizer_le` for
minimality and `eq_of_tikhonovObjective_eq_minimizer` for uniqueness.
The definition is total; at degenerate `π` (e.g. `π = 0`, where every
factor is the junk `0`) the junk behavior is honest and guarded by the
hypotheses of the theorems. -/
noncomputable def tikhonovMinimizer (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (π : ℝ) (y : V → ℝ) : V → ℝ :=
  fun a => ∑ i, tikhonovShrinkage π
      (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
    * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
    * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a

/-- **The closed-form eigencoefficient identity** (the proposal's
Step 2): the minimizer's coefficient along any Laplacian eigenvector is
the signal's coefficient shrunk by `π/(λ_k + π)`. Hypothesis-free —
pure orthonormality of the eigenbasis. -/
theorem tikhonovMinimizer_dotProduct_eigvecOf (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (π : ℝ) (y : V → ℝ) (k : V) :
    Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
        (tikhonovMinimizer A hA π y)
      = tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) y :=
  dotProduct_eigvecOf_filter (laplacian_symmetric A hA) (tikhonovShrinkage π) y k

/-!
## 2. The normal equation: forward and converse

The minimizer solves the regularized normal equation
`(L + π•1) *ᵥ x* = π • y`, and it is the *only* solution — so the
minimizer can be pinned by any hand-solved linear system, which is how
the QA fixture cross-checks the spectral construction against plain
Gaussian elimination.
-/

/-- **The normal equation.** The eigenbasis minimizer solves
`(L + π•1) *ᵥ x* = π • y`: per eigencomponent, the factor
`π/(λ+π)` remultiplied by `λ + π` returns `π` (the denominator is
positive by PSD + `π > 0`), and the eigenbasis expansion resolves
`π • ∑_k (v_k ⬝ᵥ y) v_k = π • y`. -/
theorem tikhonovMinimizer_add_smul_one_mulVec (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    {π : ℝ} (hπ : 0 < π) (y : V → ℝ) :
    (laplacian A + π • (1 : Matrix V V ℝ)) *ᵥ tikhonovMinimizer A hA π y
      = π • y := by
  have hpos : ∀ i : V, eigvalOf (laplacian A) (laplacian_symmetric A hA) i + π ≠ 0 := by
    intro i
    have hμ := eigvalOf_laplacian_nonneg A hA hnonneg i
    linarith
  have hc : ∀ i : V, tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
      * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
      * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i + π)
      = π * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y := by
    intro i
    have hc0 : tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
        * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i + π) = π := by
      rw [tikhonovShrinkage, div_mul_cancel₀ _ (hpos i)]
    calc tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
          * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
          * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i + π)
        = (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
            * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i + π))
          * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y := by
            ring
      _ = π * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y := by
            rw [hc0]
  funext a
  have hsplit : ((laplacian A + π • (1 : Matrix V V ℝ))
      *ᵥ tikhonovMinimizer A hA π y) a
      = (laplacian A *ᵥ tikhonovMinimizer A hA π y) a
        + π * tikhonovMinimizer A hA π y a := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]
    simp [Pi.add_apply, Pi.smul_apply]
  rw [hsplit]
  have hLmul : (laplacian A *ᵥ tikhonovMinimizer A hA π y) a
      = ∑ i, tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
        * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a) :=
    mulVec_eigvecOf_sum_apply (laplacian_symmetric A hA)
      (fun i => tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y) a
  have hπmul : π * tikhonovMinimizer A hA π y a
      = ∑ i, π * (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
        * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a) := by
    simp only [tikhonovMinimizer]
    rw [Finset.mul_sum]
  rw [hLmul, hπmul, ← Finset.sum_add_distrib]
  have hterm : ∀ i : V,
      (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
        * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a))
      + π * (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
        * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a)
      = π * (Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
        * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a) := by
    intro i
    have hci := hc i
    calc tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
          * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
          * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a)
        + π * (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
          * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
          * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a)
        = (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
            * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y)
          * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i + π)
          * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a := by ring
      _ = (π * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y)
          * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a := by rw [hci]
      _ = π * (Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y
          * eigvecOf (laplacian A) (laplacian_symmetric A hA) i a) := by ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.mul_sum,
    eigvecOf_expansion_apply (laplacian_symmetric A hA) y a]
  simp [Pi.smul_apply]

/-- **The normal equation characterizes the minimizer.** Any solution
`z` of `(L + π•1) *ᵥ z = π • y` *is* the eigenbasis minimizer: taking
the inner product with each eigenvector `v_k` gives
`(λ_k + π) (v_k ⬝ᵥ z) = π (v_k ⬝ᵥ y)` (the Laplacian is self-adjoint
in coordinates), so `z` has exactly the minimizer's coefficients. This
is the interface QA uses to pin the minimizer by a hand-solved linear
system, independently of the spectral-theorem construction. -/
theorem eq_tikhonovMinimizer_of_add_smul_one_mulVec (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    {π : ℝ} (hπ : 0 < π) {y z : V → ℝ}
    (hz : (laplacian A + π • (1 : Matrix V V ℝ)) *ᵥ z = π • y) :
    z = tikhonovMinimizer A hA π y := by
  have hpos : ∀ i : V, eigvalOf (laplacian A) (laplacian_symmetric A hA) i + π ≠ 0 := by
    intro i
    have hμ := eigvalOf_laplacian_nonneg A hA hnonneg i
    linarith
  refine ext_of_dotProduct_eigvecOf_eq (laplacian_symmetric A hA) fun k => ?_
  rw [tikhonovMinimizer_dotProduct_eigvecOf]
  have hz' : Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
        ((laplacian A + π • (1 : Matrix V V ℝ)) *ᵥ z)
      = Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) (π • y) :=
    congrArg (Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)) hz
  rw [Matrix.add_mulVec, Matrix.smul_mulVec_assoc, Matrix.one_mulVec,
    Matrix.dotProduct_add, Matrix.dotProduct_smul,
    dotProduct_eigvecOf_mulVec (laplacian_symmetric A hA) k z, smul_eq_mul,
    Matrix.dotProduct_smul, smul_eq_mul] at hz'
  refine (mul_right_cancel₀ (hpos k) ?_).symm
  have hcanc : tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
      * (eigvalOf (laplacian A) (laplacian_symmetric A hA) k + π)
      = π := by
    rw [tikhonovShrinkage, div_mul_cancel₀ _ (hpos k)]
  rw [show tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) y
        * (eigvalOf (laplacian A) (laplacian_symmetric A hA) k + π)
      = (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) k)
          * (eigvalOf (laplacian A) (laplacian_symmetric A hA) k + π))
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) y from by
      ring, hcanc]
  linear_combination -hz'

/-!
## 3. The objective: minimality and uniqueness

The Tikhonov objective `‖x − y‖² + (1/π) xᵀLx`, its eigenbasis
decoupling (both terms resolve through Parseval and the spectral
resolution, so the objective is a sum of independent one-variable
quadratics), the strict-convexity decomposition, and the resulting
minimality and equality-uniqueness theorems.
-/

/-- The Tikhonov objective `‖x − y‖² + (1/π) · xᵀ L x` to be minimized
over `x`. Total: at `π = 0` the coefficient `1/π` is the junk value `0`
and the objective degenerates to `‖x − y‖²`; the theorems below carry
`0 < π` to exclude this. -/
noncomputable def tikhonovObjective (A : WAdj (V := V)) (π : ℝ) (y x : V → ℝ) : ℝ :=
  Matrix.dotProduct (x - y) (x - y) + (1 / π) * quadForm (laplacian A) x

/-- The one-variable quadratic behind the strict-convexity
decomposition (private): with `s = π/(μ+π)`,
`(d−c)² + (1/π) μ d² − ((sc−c)² + (1/π) μ (sc)²) = (1 + μ/π) (d − sc)²`
— completing the square at the shrunk value. -/
private theorem quad_identity {π μ d c : ℝ} (hπ : π ≠ 0) (hμ : μ + π ≠ 0) :
    ((d - c) ^ 2 + (1 / π) * (μ * d ^ 2))
        - ((π / (μ + π) * c - c) ^ 2 + (1 / π) * (μ * (π / (μ + π) * c) ^ 2))
      = (1 + μ / π) * (d - π / (μ + π) * c) ^ 2 := by
  field_simp
  ring

/-- **The strict-convexity decomposition.** The objective's excess over
its value at the minimizer is the eigencomponent-wise weighted sum of
squares `∑_k (1 + λ_k/π) (d_k − d*_k)²` with *positive* weights
(`1 + λ_k/π = (π + λ_k)/π > 0` on a PSD Laplacian with `π > 0`). This
one identity delivers both minimality (the excess is a sum of squares)
and uniqueness (a zero excess forces every eigencomponent to match).
Load-bearing on the whole eigenbasis stack: Parseval resolves the
fidelity term, `quadForm_eigvalOf` the energy term, and the minimizer
enters through its coefficient identity. -/
theorem tikhonovObjective_sub_minimizer (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    {π : ℝ} (hπ : 0 < π) (y x : V → ℝ) :
    tikhonovObjective A π y x
        - tikhonovObjective A π y (tikhonovMinimizer A hA π y)
      = ∑ i, (1 + eigvalOf (laplacian A) (laplacian_symmetric A hA) i / π)
          * (Matrix.dotProduct (eigvecOf (laplacian A)
              (laplacian_symmetric A hA) i) x
              - tikhonovShrinkage π (eigvalOf (laplacian A)
                  (laplacian_symmetric A hA) i)
              * Matrix.dotProduct (eigvecOf (laplacian A)
                  (laplacian_symmetric A hA) i) y) ^ 2 := by
  have hpos : ∀ i : V, eigvalOf (laplacian A) (laplacian_symmetric A hA) i + π ≠ 0 := by
    intro i
    have hμ := eigvalOf_laplacian_nonneg A hA hnonneg i
    linarith
  have hdec : ∀ w : V → ℝ, tikhonovObjective A π y w
      = ∑ i, ((Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) w
            - Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y) ^ 2
          + (1 / π) * (eigvalOf (laplacian A) (laplacian_symmetric A hA) i
            * (Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) w) ^ 2)) := by
    intro w
    have hp : Matrix.dotProduct (w - y) (w - y)
        = ∑ i, (Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) w
            - Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) y) ^ 2 := by
      rw [dotProduct_eigvecOf (laplacian_symmetric A hA) (w - y) (w - y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.dotProduct_sub, pow_two]
    simp only [tikhonovObjective, hp, quadForm_eigvalOf (laplacian_symmetric A hA) w,
      Finset.sum_add_distrib, Finset.mul_sum]
  rw [hdec x, hdec (tikhonovMinimizer A hA π y), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tikhonovMinimizer_dotProduct_eigvecOf A hA π y i]
  exact quad_identity hπ.ne' (hpos i)

/-- **Minimality.** The eigenbasis minimizer minimizes the Tikhonov
objective on every symmetric nonnegative network: the excess is a sum
of squares (`tikhonovObjective_sub_minimizer`). -/
theorem tikhonovObjective_minimizer_le (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    {π : ℝ} (hπ : 0 < π) (y x : V → ℝ) :
    tikhonovObjective A π y (tikhonovMinimizer A hA π y)
      ≤ tikhonovObjective A π y x := by
  rw [← sub_nonneg,
    tikhonovObjective_sub_minimizer A hA hnonneg hπ y x]
  refine Finset.sum_nonneg fun i _ => ?_
  refine mul_nonneg ?_ (sq_nonneg _)
  have hμ := eigvalOf_laplacian_nonneg A hA hnonneg i
  have hμπ : 0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) i / π :=
    div_nonneg hμ (le_of_lt hπ)
  linarith

/-- **Uniqueness.** The minimizer is the *unique* minimizer in the
strong sense that any tie forces equality of the vectors themselves:
a zero excess makes every squared eigencomponent difference vanish, and
eigenbasis expansion reconstructs vectors from those components. -/
theorem eq_of_tikhonovObjective_eq_minimizer (A : WAdj (V := V))
    (hA : Matrix.IsSymm A) (hnonneg : ∀ i j, 0 ≤ A i j)
    {π : ℝ} (hπ : 0 < π) {y x : V → ℝ}
    (h : tikhonovObjective A π y x
      = tikhonovObjective A π y (tikhonovMinimizer A hA π y)) :
    x = tikhonovMinimizer A hA π y := by
  have hsub : ∑ i, (1 + eigvalOf (laplacian A) (laplacian_symmetric A hA) i
        / π)
          * (Matrix.dotProduct (eigvecOf (laplacian A)
              (laplacian_symmetric A hA) i) x
              - tikhonovShrinkage π (eigvalOf (laplacian A)
                  (laplacian_symmetric A hA) i)
              * Matrix.dotProduct (eigvecOf (laplacian A)
                  (laplacian_symmetric A hA) i) y) ^ 2
      = 0 := by
    rw [← tikhonovObjective_sub_minimizer A hA hnonneg hπ y x, h, sub_self]
  have hnn : ∀ i : V, 0 ≤ (1 + eigvalOf (laplacian A)
      (laplacian_symmetric A hA) i / π) := by
    intro i
    have hμ := eigvalOf_laplacian_nonneg A hA hnonneg i
    have hμπ : 0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) i / π :=
      div_nonneg hμ (le_of_lt hπ)
    linarith
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => mul_nonneg (hnn i) (sq_nonneg _))).1 hsub
  refine ext_of_dotProduct_eigvecOf_eq (laplacian_symmetric A hA) fun i => ?_
  have hi := hterm i (Finset.mem_univ i)
  have hne : (1 + eigvalOf (laplacian A) (laplacian_symmetric A hA) i / π)
      ≠ 0 := by
    have hμ := eigvalOf_laplacian_nonneg A hA hnonneg i
    have hμπ : 0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) i / π :=
      div_nonneg hμ (le_of_lt hπ)
    linarith
  have hdiff : (Matrix.dotProduct (eigvecOf (laplacian A)
        (laplacian_symmetric A hA) i) x
        - tikhonovShrinkage π (eigvalOf (laplacian A)
          (laplacian_symmetric A hA) i)
        * Matrix.dotProduct (eigvecOf (laplacian A)
          (laplacian_symmetric A hA) i) y) = 0 := by
    rcases mul_eq_zero.1 hi with h' | h'
    · exact absurd h' hne
    · exact sq_eq_zero_iff.1 h'
  rw [sub_eq_zero.1 hdiff]
  exact (tikhonovMinimizer_dotProduct_eigvecOf A hA π y i).symm

/-!
## 4. What the filter does: fixed kernel modes, shrunk nonzero modes

The structure theorems that make this a *shrinkage* filter rather than
a projection: kernel modes pass through exactly (mean preservation),
every positive mode comes out strictly shrunk, and the filter is not
idempotent.
-/

/-- **Mean preservation.** The minimizer has the same coordinate sum as
the signal: every kernel mode's factor is exactly `1` (its eigenvalue
is `0`), and every nonzero mode's eigenvector is orthogonal to
`onesVec` (`eigvecOf_ortho_onesVec`) — so through Parseval the sums
agree. Needs symmetry and `π ≠ 0` only: no nonnegativity, no
connectivity (on a disconnected graph each component's mean is
preserved, which is the correct behavior). -/
theorem sum_tikhonovMinimizer_eq_sum (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    {π : ℝ} (hπ : π ≠ 0) (y : V → ℝ) :
    ∑ a, tikhonovMinimizer A hA π y a = ∑ a, y a := by
  have hkey : ∀ k : V,
      Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) onesVec
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
            (tikhonovMinimizer A hA π y)
      = Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) onesVec
        * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) y := by
    intro k
    by_cases hμ : eigvalOf (laplacian A) (laplacian_symmetric A hA) k = 0
    · rw [tikhonovMinimizer_dotProduct_eigvecOf, hμ, tikhonovShrinkage,
        zero_add, div_self hπ, one_mul]
    · simp [eigvecOf_ortho_onesVec A hA hμ]
  calc ∑ a, tikhonovMinimizer A hA π y a
      = Matrix.dotProduct onesVec (tikhonovMinimizer A hA π y) := by
        simp [Matrix.dotProduct, onesVec]
    _ = ∑ k, Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) onesVec
          * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
              (tikhonovMinimizer A hA π y) :=
        dotProduct_eigvecOf (laplacian_symmetric A hA) onesVec _
    _ = ∑ k, Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) onesVec
          * Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k) y :=
        Finset.sum_congr rfl fun k _ => hkey k
    _ = Matrix.dotProduct onesVec y :=
        (dotProduct_eigvecOf (laplacian_symmetric A hA) onesVec y).symm
    _ = ∑ a, y a := by simp [Matrix.dotProduct, onesVec]

/-- **Eigenvector inputs come out strictly shrunk.** The filter of an
eigenvector is its shrinkage factor times itself: pure
orthonormality, no hypothesis on `π`. -/
theorem tikhonovMinimizer_eigvecOf (A : WAdj (V := V)) (hA : Matrix.IsSymm A)
    (π : ℝ) (i : V) :
    tikhonovMinimizer A hA π (eigvecOf (laplacian A)
        (laplacian_symmetric A hA) i)
      = tikhonovShrinkage π (eigvalOf (laplacian A)
          (laplacian_symmetric A hA) i)
        • eigvecOf (laplacian A) (laplacian_symmetric A hA) i := by
  have hii : ∀ k : V, Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
      (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) = if k = i then 1 else 0 := by
    intro k
    simpa [Matrix.dotProduct] using eigvecOf_inner (laplacian A) (laplacian_symmetric A hA) k i
  refine ext_of_dotProduct_eigvecOf_eq (laplacian_symmetric A hA) fun k => ?_
  rw [tikhonovMinimizer_dotProduct_eigvecOf, Matrix.dotProduct_smul,
    smul_eq_mul, hii k]
  by_cases h : k = i
  · subst h
    simp
  · rw [if_neg h, mul_zero, mul_zero]

/-- **Not a projection** (the proposal's explicit-distinction
requirement): the Tikhonov filter is not idempotent. Filtering the
eigenvector of a positive eigenvalue yields a copy shrunk by a factor
strictly in `(0, 1)`, and filtering *that* again yields a doubly-shrunk
copy `s² • v ≠ s • v`. A projection (`spectralProjector` included)
fixes its image exactly; the Tikhonov filter never does, on any network
with a positive Laplacian eigenvalue (any graph with an edge). No
nonnegativity hypothesis: positivity of the single eigenvalue carries
everything. -/
theorem tikhonovMinimizer_ne_apply_self_of_eigvalOf_pos (A : WAdj (V := V))
    (hA : Matrix.IsSymm A)
    {π : ℝ} (hπ : 0 < π) {i : V}
    (hμ : 0 < eigvalOf (laplacian A) (laplacian_symmetric A hA) i) :
    tikhonovMinimizer A hA π
        (tikhonovMinimizer A hA π
          (eigvecOf (laplacian A) (laplacian_symmetric A hA) i))
      ≠ tikhonovMinimizer A hA π
          (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) := by
  have hnn : 0 ≤ eigvalOf (laplacian A) (laplacian_symmetric A hA) i := le_of_lt hμ
  have hs01 : tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
      ∈ Set.Ioo 0 1 :=
    ⟨tikhonovShrinkage_pos hπ hnn, tikhonovShrinkage_lt_one hπ hμ⟩
  have hvne : eigvecOf (laplacian A) (laplacian_symmetric A hA) i ≠ 0 := by
    intro h₀
    have h₁ : Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i)
        (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) = 0 := by
      rw [h₀, Matrix.zero_dotProduct]
    have h₂ : Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) i)
        (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) = 1 := by
      simpa [Matrix.dotProduct] using eigvecOf_inner (laplacian A) (laplacian_symmetric A hA) i i
    rw [h₁] at h₂
    norm_num at h₂
  have hstep2 : tikhonovMinimizer A hA π
      (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)
        • eigvecOf (laplacian A) (laplacian_symmetric A hA) i)
      = (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)) ^ 2
        • eigvecOf (laplacian A) (laplacian_symmetric A hA) i := by
    refine ext_of_dotProduct_eigvecOf_eq (laplacian_symmetric A hA) fun k => ?_
    have hii : Matrix.dotProduct (eigvecOf (laplacian A) (laplacian_symmetric A hA) k)
        (eigvecOf (laplacian A) (laplacian_symmetric A hA) i) = if k = i then 1 else 0 := by
      simpa [Matrix.dotProduct] using eigvecOf_inner (laplacian A) (laplacian_symmetric A hA) k i
    rw [tikhonovMinimizer_dotProduct_eigvecOf, Matrix.dotProduct_smul,
      smul_eq_mul, Matrix.dotProduct_smul, smul_eq_mul, hii]
    by_cases h : k = i
    · subst h
      simp
      ring
    · rw [if_neg h]
      ring
  intro hcon
  rw [tikhonovMinimizer_eigvecOf A hA π i, hstep2] at hcon
  have hz : ((tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)) ^ 2
      - tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i))
      • eigvecOf (laplacian A) (laplacian_symmetric A hA) i = 0 := by
    rw [sub_smul, ← hcon, sub_self]
  rcases smul_eq_zero.1 hz with h₀ | hv₀
  · have hfactor : (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i))
        * ((tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)) - 1) = 0 := by
      have hring : (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i))
          * ((tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)) - 1)
          = (tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)) ^ 2
            - tikhonovShrinkage π (eigvalOf (laplacian A) (laplacian_symmetric A hA) i) := by
        ring
      linarith
    rcases mul_eq_zero.1 hfactor with h | h
    · exact absurd h (ne_of_gt hs01.1)
    · exact absurd (by linarith : (tikhonovShrinkage π
        (eigvalOf (laplacian A) (laplacian_symmetric A hA) i)) = 1) (ne_of_lt hs01.2)
  · exact absurd hv₀ hvne
