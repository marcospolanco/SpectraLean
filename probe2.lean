import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

open Matrix InnerProductSpace

variable {V : Type} [Fintype V] [DecidableEq V]

section Probe

theorem toHerm (M : Matrix V V ℝ) (hM : M.IsSymm) : M.IsHermitian := by
  show Mᴴ = M
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hM.eq

noncomputable def evb (M : Matrix V V ℝ) (hM : M.IsSymm) :
    OrthonormalBasis V ℝ (EuclideanSpace ℝ V) :=
  (toHerm M hM).eigenvectorBasis

noncomputable def ev (M : Matrix V V ℝ) (hM : M.IsSymm) (i : V) : V → ℝ :=
  (evb M hM i : V → ℝ)

theorem probe_inner (M : Matrix V V ℝ) (hM : M.IsSymm) (i j : V) :
    ∑ k, ev M hM i k * ev M hM j k = if i = j then 1 else 0 := by
  have h := (evb M hM).orthonormal
  rw [orthonormal_iff_ite] at h
  have hij := h i j
  rw [PiLp.inner_apply] at hij
  simpa [RCLike.inner_apply] using hij

theorem probe_complete (M : Matrix V V ℝ) (hM : M.IsSymm) (a b : V) :
    ∑ i, ev M hM i a * ev M hM i b = if a = b then 1 else 0 := by
  have h := (evb M hM).sum_repr' (EuclideanSpace.single a (1 : ℝ))
  have hcoeff : ∀ i : V,
      ⟪evb M hM i, EuclideanSpace.single a (1 : ℝ)⟫_ℝ = ev M hM i a := by
    intro i
    rw [EuclideanSpace.inner_single_right]
    simp
  have happl := congrFun h b
  simp only [Finset.sum_apply, PiLp.smul_apply, hcoeff] at happl
  rw [EuclideanSpace.single_apply] at happl
  exact happl

end Probe
