/-
  FunctionalCalculus_QA.lean

  Purpose
  -------
  QA for the Scaffold–Mathlib Hermitian functional-calculus bridge
  delivered in `Scaffold.Mathlib.GraphTheory.FunctionalCalculus`
  (proposal `proposals/hermitian-functional-calculus-bridge.md`,
  2026-08-25): the thin wrapper `spectralCalc`, its eigenvector action,
  its equality with the shelf's filter-sum expansion, the
  `spectralProjector` recovery, and `spectralCalc_id`.

  The proposal's three mandated QA obligations, all as proved lemmas:

  1. **Two API paths to one value** (Section A): on the `diag13`
     fixture (`!![1, 0; 0, 3]`, reused from `Band_QA` with its
     eigenbasis pins), the calculus output is computed entrywise via
     the eigenbasis expansion (`spectralCalc_apply` — the
     filter-sum/calculus route, `fc_diag13_calc`, for arbitrary `f`)
     and independently via the shelf's hand-built `spectralProjector`
     plus the delivered recovery theorem at the indicator function —
     both paths pinned to the same matrix, plus an f-dependence fence
     refuting any degenerate implementation.

  2. **Eigenvector action at a non-basis vector** (Section B): the
     action theorem instantiated at `v₀ + v₁` (linearity inherited),
     and the action on the concrete vector `![1, 1]` computed by two
     independent routes (the pinned matrix; the expansion theorem with
     sign-cancelling eigenbasis coefficients).

  3. **Repeated-eigenvalue boundary case** (Section C): on `2 • 1`
     (every vector an eigenvector — the eigenspace is
     two-dimensional, so *any* orthonormal basis is a legal choice),
     `f(2 • 1) = f 2 • 1` proved by two independent routes: the entry
     form plus completeness (no basis choice anywhere) and the raw
     unitary-conjugation definition (no completeness anywhere).

  4. **The complex-half elaboration witness** (Section D): Mathlib's
     `cfc` instantiated at `𝕜 = ℂ` on a genuinely complex Hermitian
     matrix, at the identity function — the Step-0 API-split verdict's
     artifact, unblocking the gated magnetic-Laplacian consumer.

  5. **The Tikhonov reconciliation** (Section E, 2026-08-25,
      `proposals/hermitian-calculus-consumer-tikhonov-heat.md`): on the
      `Tikhonov_QA` `K₂` fixture, the calculus at `tikhonovShrinkage 1`
      pinned to `!![2/3, 1/3; 1/3, 2/3]` entrywise sign-free (the
      master lemma `fc_lapK2_calc` at arbitrary `f`), the minimizer
      reconciliation witnessed numerically (the calculus routes
      `![1,0]` to the hand-solved `![2/3, 1/3]`), the normal equation
      by two independent routes (calculus algebra vs the pinned
      hand-solved system) plus a raw matrix-arithmetic check, the
      kernel-mode action instantiation, and the **fence** at `π = -2`:
      the junk shrinkage at the spectral point `2 = -π` makes the
      hypothesis-free normal equation provably false.

  6. **The Heat reconciliation** (Section F, 2026-08-25, the Heat half
      of the same proposal): on the same `K₂` fixture, the heat kernel
      through the equality theorem is the closed form
      `!![(1±e^{-2t})/2]` — computed by **two independent routes**
      (Mathlib's `cfc` through the equality theorem vs the
      `Heat.lean` series engine `heatKernel_mulVec_eq_sum` with the
      Section-E sign-free outer-product pins), the semigroup law at
      times `1, 2` by **two independent routes** (the new
      calculus-algebra semigroup vs the delivered
      `heatKernel_mul_heatKernel` commute route) plus a raw
      closed-form product check, the time-zero identity through the
      calculus, eigenmode decay through the calculus action interface
      (both modes), and the **nontriviality fence**: the kernel at
      `t = 1` is provably not the identity — diffusion moves mass.

  QA never proves, validates, or certifies any axiom: this file
  contains no `sorry`/`admit`, and the bridge it exercises consumes
  none (Mathlib's calculus is proved upstream).

  All fixtures are `Fin 2`; the public theorems are size- and
  weight-general.
-/

import Scaffold.Mathlib.GraphTheory.FunctionalCalculus
import Scaffold.QA.SpectralGraph.Band_QA
import Scaffold.QA.SpectralGraph.Tikhonov_QA
import Mathlib.LinearAlgebra.Matrix.HermitianFunctionalCalculus

open scoped BigOperators Matrix
open SpectralGraphTheory

namespace SpectralGraphTheory.QA

/-!
## Section A: two API paths to one value on `diag13`
-/

/-- **Path A — the calculus/filter-sum route, for arbitrary `f`.**
The calculus output on the diagonal fixture is the diagonal matrix of
`f` at the eigenvalues, computed entrywise from `spectralCalc_apply`
and the `Band_QA` eigenbasis pins (eigenvalues exactly `{1, 3}`,
eigenvectors sign-independently along the coordinate axes; every
outer-product summand `vᵢa * vᵢb` is sign-free, so no basis choice
enters the computation at any point). -/
theorem fc_diag13_calc (f : ℝ → ℝ) :
    spectralCalc diag13 diag13_symm f = !![f 1, 0; 0, f 3] := by
  have hsum33 : eigvalOf diag13 diag13_symm 0 = 3 →
      eigvalOf diag13 diag13_symm 1 = 3 → False := by
    intro h0 h1
    have hs := diag13_sum
    rw [h0, h1] at hs
    norm_num at hs
  have hsum11 : eigvalOf diag13 diag13_symm 0 = 1 →
      eigvalOf diag13 diag13_symm 1 = 1 → False := by
    intro h0 h1
    have hs := diag13_sum
    rw [h0, h1] at hs
    norm_num at hs
  ext a b
  rw [spectralCalc_apply diag13 diag13_symm f a b]
  fin_cases a <;> fin_cases b
  · -- entry (0, 0)
    show (∑ i, f (eigvalOf diag13 diag13_symm i)
          * eigvecOf diag13 diag13_symm i (0 : Fin 2)
          * eigvecOf diag13 diag13_symm i 0)
      = (!![f 1, 0; 0, f 3] : Matrix (Fin 2) (Fin 2) ℝ) 0 0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
    rcases diag13_eigvalOf_mem 0 with e0 | e0 <;>
      rcases diag13_eigvalOf_mem 1 with e1 | e1
    · exact (hsum11 e0 e1).elim
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_one 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_three 1 e1
      rw [e0, e1, p1]
      linear_combination f 1 * q0
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_three 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_one 1 e1
      rw [e0, e1, p0]
      linear_combination f 1 * q1
    · exact (hsum33 e0 e1).elim
  · -- entry (0, 1)
    show (∑ i, f (eigvalOf diag13 diag13_symm i)
          * eigvecOf diag13 diag13_symm i (0 : Fin 2)
          * eigvecOf diag13 diag13_symm i 1)
      = (!![f 1, 0; 0, f 3] : Matrix (Fin 2) (Fin 2) ℝ) 0 1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
    rcases diag13_eigvalOf_mem 0 with e0 | e0 <;>
      rcases diag13_eigvalOf_mem 1 with e1 | e1
    · exact (hsum11 e0 e1).elim
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_one 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_three 1 e1
      rw [e0, e1, p0, p1]
      ring
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_three 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_one 1 e1
      rw [e0, e1, p0, p1]
      ring
    · exact (hsum33 e0 e1).elim
  · -- entry (1, 0)
    show (∑ i, f (eigvalOf diag13 diag13_symm i)
          * eigvecOf diag13 diag13_symm i (1 : Fin 2)
          * eigvecOf diag13 diag13_symm i 0)
      = (!![f 1, 0; 0, f 3] : Matrix (Fin 2) (Fin 2) ℝ) 1 0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
    rcases diag13_eigvalOf_mem 0 with e0 | e0 <;>
      rcases diag13_eigvalOf_mem 1 with e1 | e1
    · exact (hsum11 e0 e1).elim
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_one 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_three 1 e1
      rw [e0, e1, p0, p1]
      ring
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_three 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_one 1 e1
      rw [e0, e1, p0, p1]
      ring
    · exact (hsum33 e0 e1).elim
  · -- entry (1, 1)
    show (∑ i, f (eigvalOf diag13 diag13_symm i)
          * eigvecOf diag13 diag13_symm i (1 : Fin 2)
          * eigvecOf diag13 diag13_symm i 1)
      = (!![f 1, 0; 0, f 3] : Matrix (Fin 2) (Fin 2) ℝ) 1 1
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.tail_cons, Matrix.of_apply]
    rcases diag13_eigvalOf_mem 0 with e0 | e0 <;>
      rcases diag13_eigvalOf_mem 1 with e1 | e1
    · exact (hsum11 e0 e1).elim
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_one 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_three 1 e1
      rw [e0, e1, p0]
      linear_combination f 3 * q1
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_three 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_one 1 e1
      rw [e0, e1, p1]
      linear_combination f 3 * q0
    · exact (hsum33 e0 e1).elim

/-- The concrete instantiation at the squaring function: the calculus
squares the spectrum, `1 ↦ 1` and `3 ↦ 9`, entrywise pinned. -/
theorem fc_diag13_sq :
    spectralCalc diag13 diag13_symm (fun x => x * x) = !![1, 0; 0, 9] := by
  have h := fc_diag13_calc (fun x => x * x)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons] at h ⊢
  convert h using 2; norm_num

/-- The zero function maps to the zero matrix — the calculus's
additive/multiplicative unit edge, pinned on the fixture. -/
theorem fc_diag13_zero :
    spectralCalc diag13 diag13_symm (fun _ => (0 : ℝ)) = 0 := by
  have h := fc_diag13_calc (fun _ => (0 : ℝ))
  have hz : (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  calc spectralCalc diag13 diag13_symm (fun _ => (0 : ℝ))
      = (!![0, 0; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) := by
        simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.tail_cons] using h
    _ = 0 := hz

/-- **Path B — the shelf's hand-built projector route.** At the
indicator of `(· ≤ 2)`, the calculus output equals the pinned
`spectralProjector diag13 2 = !![1, 0; 0, 0]` (a `Band_QA` value
proved from the threshold lemmas, independent of the calculus), via
the delivered recovery theorem. -/
theorem fc_diag13_indicator_projectorRoute :
    spectralCalc diag13 diag13_symm (fun x => if x ≤ 2 then 1 else 0)
      = !![1, 0; 0, 0] := by
  rw [spectralCalc_indicator_eq_spectralProjector,
    spectralProjector_diag13_eq 2 (by norm_num) (by norm_num)]

/-- **The join of the two paths**: path A at the same indicator
function computes the same matrix by pure eigenbasis arithmetic
(`fc_diag13_calc` instantiated), agreeing with path B's projector
route — two independent API paths to one value. -/
theorem fc_diag13_twoPaths_join :
    spectralCalc diag13 diag13_symm (fun x => if x ≤ 2 then 1 else 0)
      = !![1, 0; 0, 0] := by
  have h := fc_diag13_calc (fun x => if x ≤ 2 then 1 else 0)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons] at h ⊢
  convert h using 3 <;> norm_num [(by norm_num : (2 : ℝ) < 3)]

/-- **The f-dependence fence**: the calculus output genuinely depends
on `f` — the identity function and the squaring function give
different operators (entry `(1, 1)`: `3 ≠ 9`). Refutes, in proved
form, any degenerate implementation returning `M`, `0`, or any
`f`-independent value on this fixture. -/
theorem fc_diag13_depends_on_f :
    spectralCalc diag13 diag13_symm (fun x => x)
      ≠ spectralCalc diag13 diag13_symm (fun x => x * x) := by
  intro hcon
  have h1 : spectralCalc diag13 diag13_symm (fun x => x) = !![1, 0; 0, 3] :=
    by
      have h := fc_diag13_calc (fun x => x)
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.tail_cons] at h ⊢
      exact h
  rw [h1, fc_diag13_sq] at hcon
  have : (!![1, 0; 0, 3] : Matrix (Fin 2) (Fin 2) ℝ) 1 1
      = (!![1, 0; 0, 9] : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    rw [hcon]
  simp only [Matrix.cons_val_one, Matrix.head_cons] at this
  norm_num at this


/-!
## Section B: the eigenvector action at a non-basis vector
-/

/-- **Linearity inherited at a non-basis vector** (the proposal's QA
obligation 2, generic form): the action theorem at the sum of two
eigenbasis vectors — the calculus acts on the combination component by
component, exactly as linearity demands. -/
theorem fc_action_add {V : Type} [Fintype V] [DecidableEq V]
    (M : Matrix V V ℝ) (hM : M.IsSymm) (f : ℝ → ℝ) (i j : V) :
    spectralCalc M hM f *ᵥ (eigvecOf M hM i + eigvecOf M hM j)
      = f (eigvalOf M hM i) • eigvecOf M hM i
        + f (eigvalOf M hM j) • eigvecOf M hM j := by
  rw [Matrix.mulVec_add, spectralCalc_mulVec_eigvecOf M hM f i,
    spectralCalc_mulVec_eigvecOf M hM f j]

/-- **Route 1 — the pinned matrix acting raw**: the squared calculus on
`diag13` sends `![1, 1]` (a genuine combination of the two eigenbasis
vectors — each is a signed coordinate unit vector) to `![1, 9]`,
computed from `fc_diag13_sq` by literal matrix–vector arithmetic. -/
theorem fc_diag13_action_sq_route1 :
    spectralCalc diag13 diag13_symm (fun x => x * x) *ᵥ ![1, 1]
      = (![1, 9] : Fin 2 → ℝ) := by
  rw [fc_diag13_sq]
  funext a
  fin_cases a <;>
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply] <;>
    norm_num

/-- **Route 2 — the expansion theorem with sign-cancelling
coefficients**: the same vector computed from
`spectralCalc_mulVec_apply` and the eigenbasis pins alone (the
coefficient `v ⬝ᵥ ![1, 1]` and the entry `v a` carry opposite-signed
copies of the same unknown sign `σ`, whose product is `1` by the
normalization pin — no basis choice survives). -/
theorem fc_diag13_action_sq_route2 :
    spectralCalc diag13 diag13_symm (fun x => x * x) *ᵥ ![1, 1]
      = (![1, 9] : Fin 2 → ℝ) := by
  have hsum33 : eigvalOf diag13 diag13_symm 0 = 3 →
      eigvalOf diag13 diag13_symm 1 = 3 → False := by
    intro h0 h1
    have hs := diag13_sum
    rw [h0, h1] at hs
    norm_num at hs
  have hsum11 : eigvalOf diag13 diag13_symm 0 = 1 →
      eigvalOf diag13 diag13_symm 1 = 1 → False := by
    intro h0 h1
    have hs := diag13_sum
    rw [h0, h1] at hs
    norm_num at hs
  funext a
  rw [spectralCalc_mulVec_apply diag13 diag13_symm (fun x => x * x)
    (![1, 1] : Fin 2 → ℝ) a]
  have hdot : ∀ i : Fin 2,
      Matrix.dotProduct (eigvecOf diag13 diag13_symm i) (![1, 1] : Fin 2 → ℝ)
        = eigvecOf diag13 diag13_symm i 0 + eigvecOf diag13 diag13_symm i 1 := by
    intro i
    simp only [Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  simp only [hdot]
  fin_cases a
  · show (∑ i, eigvalOf diag13 diag13_symm i * eigvalOf diag13 diag13_symm i
          * (eigvecOf diag13 diag13_symm i 0 + eigvecOf diag13 diag13_symm i 1)
          * eigvecOf diag13 diag13_symm i (0 : Fin 2))
      = (![1, 9] : Fin 2 → ℝ) 0
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.head_cons]
    rcases diag13_eigvalOf_mem 0 with e0 | e0 <;>
      rcases diag13_eigvalOf_mem 1 with e1 | e1
    · exact (hsum11 e0 e1).elim
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_one 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_three 1 e1
      rw [e0, e1, p0, p1]
      linear_combination q0
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_three 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_one 1 e1
      rw [e0, e1, p0, p1]
      linear_combination q1
    · exact (hsum33 e0 e1).elim
  · show (∑ i, eigvalOf diag13 diag13_symm i * eigvalOf diag13 diag13_symm i
          * (eigvecOf diag13 diag13_symm i 0 + eigvecOf diag13 diag13_symm i 1)
          * eigvecOf diag13 diag13_symm i (1 : Fin 2))
      = (![1, 9] : Fin 2 → ℝ) 1
    simp only [Fin.sum_univ_two, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons]
    rcases diag13_eigvalOf_mem 0 with e0 | e0 <;>
      rcases diag13_eigvalOf_mem 1 with e1 | e1
    · exact (hsum11 e0 e1).elim
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_one 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_three 1 e1
      rw [e0, e1, p0, p1]
      linear_combination (9 : ℝ) * q1
    · obtain ⟨p0, q0⟩ := eigvecOf_diag13_three 0 e0
      obtain ⟨p1, q1⟩ := eigvecOf_diag13_one 1 e1
      rw [e0, e1, p0, p1]
      linear_combination (9 : ℝ) * q0
    · exact (hsum33 e0 e1).elim

/-!
## Section C: the repeated-eigenvalue boundary case
-/

/-- The fixture: the scalar matrix `2 • 1` on `Fin 2` — every vector is
an eigenvector, the eigenspace is the full two-dimensional space, so
*any* orthonormal basis is a legal spectral-theorem choice. The
boundary case the proposal's QA obligation 3 names. -/
def rep2 : Matrix (Fin 2) (Fin 2) ℝ := (2 : ℝ) • 1

theorem rep2_symm : rep2.IsSymm := by
  show rep2ᵀ = rep2
  rw [rep2, Matrix.transpose_smul, Matrix.transpose_one]

/-- The eigenvalue listing is constantly `2`, derived from the spectral
theorem's conjugation identity (the scalar matrix commutes through the
unitary): `U* * (2 • 1) * U = 2 • 1` forces `diagonal λ = 2 • 1`. -/
theorem eigvalOf_rep2 (i : Fin 2) : eigvalOf rep2 rep2_symm i = 2 := by
  have hconj :=
    (isHermitian_of_isSymm rep2_symm).star_mul_self_mul_eq_diagonal
  have hscalar :
      star ((isHermitian_of_isSymm rep2_symm).eigenvectorUnitary :
          Matrix (Fin 2) (Fin 2) ℝ) * rep2
        * ((isHermitian_of_isSymm rep2_symm).eigenvectorUnitary :
          Matrix (Fin 2) (Fin 2) ℝ)
      = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    show star ((isHermitian_of_isSymm rep2_symm).eigenvectorUnitary :
        Matrix (Fin 2) (Fin 2) ℝ)
        * ((2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      * ((isHermitian_of_isSymm rep2_symm).eigenvectorUnitary :
        Matrix (Fin 2) (Fin 2) ℝ)
      = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
    rw [mul_smul_comm, smul_mul_assoc, Matrix.mul_one]
    congr 1
    exact unitary.coe_star_mul_self
      (isHermitian_of_isSymm rep2_symm).eigenvectorUnitary
  rw [hscalar] at hconj
  have hent : Matrix.diagonal (RCLike.ofReal ∘
      (isHermitian_of_isSymm rep2_symm).eigenvalues)
      = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := hconj.symm
  have hii : (2 : ℝ)
      = RCLike.ofReal ((isHermitian_of_isSymm rep2_symm).eigenvalues i) := by
    have he := congrFun (congrFun hent i) i
    rw [Matrix.diagonal_apply_eq, Function.comp_apply,
      Matrix.smul_apply, Matrix.one_apply, if_pos (rfl : i = i),
      smul_eq_mul, mul_one] at he
    exact he.symm
  exact hii.symm

/-- **Route A — entry form plus completeness** (no basis choice
anywhere): `f(2 • 1) = f 2 • 1`, the sum collapsing through
`eigvecOf_complete` (`∑ i, vᵢa * vᵢb = if a = b then 1 else 0`). -/
theorem fc_rep2_routeA (f : ℝ → ℝ) :
    spectralCalc rep2 rep2_symm f = f 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext a b
  rw [spectralCalc_apply rep2 rep2_symm f a b]
  have hsum : ∑ x, f (eigvalOf rep2 rep2_symm x)
        * eigvecOf rep2 rep2_symm x a * eigvecOf rep2 rep2_symm x b
      = f 2 * (if a = b then 1 else 0) := by
    have hcongr : ∑ x, f (eigvalOf rep2 rep2_symm x)
          * eigvecOf rep2 rep2_symm x a * eigvecOf rep2 rep2_symm x b
        = f 2 * ∑ x, (eigvecOf rep2 rep2_symm x a
            * eigvecOf rep2 rep2_symm x b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [eigvalOf_rep2 x]; ring
    rw [hcongr, eigvecOf_complete]
  rw [hsum]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]

/-- **Route B — the raw unitary-conjugation definition** (no
completeness anywhere): the calculus output computed directly from the
`cfc` definition, the diagonal being the constant `f 2` and the scalar
collapsing through the unitary law `U * star U = 1`. -/
theorem fc_rep2_routeB (f : ℝ → ℝ) :
    spectralCalc rep2 rep2_symm f = f 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  show ((isHermitian_of_isSymm rep2_symm).cfc f) = _
  rw [Matrix.IsHermitian.cfc]
  have hd : Matrix.diagonal (RCLike.ofReal ∘ f ∘
      (isHermitian_of_isSymm rep2_symm).eigenvalues)
      = (f 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Function.comp_apply, Function.comp_apply,
        show ((isHermitian_of_isSymm rep2_symm).eigenvalues i)
          = eigvalOf rep2 rep2_symm i from rfl,
        eigvalOf_rep2 i, Matrix.smul_apply, Matrix.one_apply, if_pos rfl,
        smul_eq_mul, mul_one]
      rfl
    · simp only [Matrix.diagonal_apply_ne _ h, Matrix.smul_apply,
        Matrix.one_apply, if_neg h, smul_zero]
  rw [hd, mul_smul_comm, Matrix.mul_one, smul_mul_assoc]
  congr 1
  exact unitary.coe_mul_star_self
    (isHermitian_of_isSymm rep2_symm).eigenvectorUnitary

/-- The concrete instantiation at `f = (· + 1)`: both routes give the
scalar matrix `3`, pinned entrywise raw. -/
theorem fc_rep2_three :
    spectralCalc rep2 rep2_symm (fun x => x + 1)
      = (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  have h2 : (fun x => x + 1) 2 = (3 : ℝ) := by norm_num
  rw [fc_rep2_routeA (fun x => x + 1)]
  exact congrArg (fun t => t • (1 : Matrix (Fin 2) (Fin 2) ℝ)) h2

/-!
## Section D: the complex-half elaboration witness
-/

/-- The genuinely complex Hermitian fixture `[[0, i], [-i, 0]]`
(`star i = -i` makes it Hermitian) — the Step-0 API-split verdict's
artifact: Mathlib's `cfc` at `𝕜 = ℂ`, evaluated at the identity
function through the generic calculus's `cfc_id'`. This unblocks the
gated magnetic-Laplacian consumer's precondition (the complex half
confirmed working). -/
def fcM2c : Matrix (Fin 2) (Fin 2) ℂ := !![0, Complex.I; -Complex.I, 0]

theorem fcM2c_herm : Matrix.IsHermitian fcM2c := by
  show fcM2cᴴ = fcM2c
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [fcM2c, star_trivial]

theorem fcM2c_cfc_id :
    fcM2c_herm.cfc (fun x => x) = fcM2c := by
  rw [← Matrix.IsHermitian.cfc_eq]
  exact cfc_id' ℝ fcM2c fcM2c_herm

/-!
## Section E: the Tikhonov reconciliation (the first consumer)

`proposals/hermitian-calculus-consumer-tikhonov-heat.md` (2026-08-25):
the eigenbasis-defined Tikhonov minimizer is the calculus at the
shrinkage function `π ↦ π/(λ+π)`. All witnesses live on the
`Tikhonov_QA` `K₂` fixture (`adjK2`, Laplacian spectrum `{0, 2}`,
hand-solved minimizer `![2/3, 1/3]` at `π = 1`, signal `![1, 0]`), so
the calculus instance is pinned against a value computed by plain
Gaussian elimination in an earlier, independent delivery.
-/

section TikhonovReconciliation

open Scaffold.Mathlib.GraphTheory.Tikhonov.QA

/-- The kernel-mode eigenvector's squared first coordinate: constancy
plus unit norm forces `1/2`. -/
theorem fc_lapK2_sq_zero {i : Fin 2}
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 0) :
    eigvecOf (laplacian adjK2) lapK2_symmetric i 0
      * eigvecOf (laplacian adjK2) lapK2_symmetric i 0 = 1 / 2 := by
  have hEq := lapK2_eigvecOf_eq_of_eq_zero hi
  have hnorm := eigvecOf_inner (laplacian adjK2) lapK2_symmetric i i
  rw [if_pos rfl] at hnorm
  simp only [Matrix.dotProduct, Fin.sum_univ_two] at hnorm
  rw [← hEq] at hnorm
  linarith

/-- **Kernel-mode outer products are sign-free**: a constant unit
eigenvector contributes `1/2` to every entry of the eigenbasis
expansion — no basis-orientation sign survives. -/
theorem fc_lapK2_outer_zero {i : Fin 2}
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 0) (a b : Fin 2) :
    eigvecOf (laplacian adjK2) lapK2_symmetric i a
      * eigvecOf (laplacian adjK2) lapK2_symmetric i b = 1 / 2 := by
  have hEq := lapK2_eigvecOf_eq_of_eq_zero hi
  have hsq := fc_lapK2_sq_zero hi
  fin_cases a <;> fin_cases b
  · exact hsq
  · show eigvecOf (laplacian adjK2) lapK2_symmetric i 0
        * eigvecOf (laplacian adjK2) lapK2_symmetric i 1 = 1 / 2
    rw [← hEq]
    exact hsq
  · show eigvecOf (laplacian adjK2) lapK2_symmetric i 1
        * eigvecOf (laplacian adjK2) lapK2_symmetric i 0 = 1 / 2
    rw [← hEq]
    exact hsq
  · show eigvecOf (laplacian adjK2) lapK2_symmetric i 1
        * eigvecOf (laplacian adjK2) lapK2_symmetric i 1 = 1 / 2
    rw [← hEq]
    exact hsq

/-- The `λ = 2` eigenvector is anticonstant (its two coordinates are
negatives of each other) — from the eigen-action at coordinate `0`. -/
theorem fc_lapK2_anticonst {i : Fin 2}
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 2) :
    eigvecOf (laplacian adjK2) lapK2_symmetric i 1
      = -eigvecOf (laplacian adjK2) lapK2_symmetric i 0 := by
  have hev := lapK2_mulVec_eigvecOf i
  rw [hi] at hev
  have h0 := congrFun hev 0
  simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Pi.smul_apply, smul_eq_mul] at h0
  rw [show laplacian adjK2 0 0 = (1 : ℝ) from by simp [lapK2_apply],
      show laplacian adjK2 0 1 = (-1 : ℝ) from by simp [lapK2_apply]] at h0
  simp only [one_mul, neg_mul, one_mul] at h0
  linarith

/-- The `λ = 2` eigenvector's squared first coordinate is `1/2`
(anticonstancy plus unit norm). -/
theorem fc_lapK2_sq_two {i : Fin 2}
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 2) :
    eigvecOf (laplacian adjK2) lapK2_symmetric i 0
      * eigvecOf (laplacian adjK2) lapK2_symmetric i 0 = 1 / 2 := by
  have hanti := fc_lapK2_anticonst hi
  have hnorm := eigvecOf_inner (laplacian adjK2) lapK2_symmetric i i
  rw [if_pos rfl] at hnorm
  simp only [Matrix.dotProduct, Fin.sum_univ_two] at hnorm
  rw [hanti] at hnorm
  nlinarith [hnorm]

/-- **`λ = 2` outer products are sign-determined**: `+1/2` on the
diagonal, `-1/2` off it (both basis-orientation signs cancel). -/
theorem fc_lapK2_outer_two {i : Fin 2}
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 2) (a b : Fin 2) :
    eigvecOf (laplacian adjK2) lapK2_symmetric i a
      * eigvecOf (laplacian adjK2) lapK2_symmetric i b
      = if a = b then 1 / 2 else -(1 / 2) := by
  have hanti := fc_lapK2_anticonst hi
  have hsq := fc_lapK2_sq_two hi
  fin_cases a <;> fin_cases b
  · rw [if_pos rfl]
    exact hsq
  · show eigvecOf (laplacian adjK2) lapK2_symmetric i 0
        * eigvecOf (laplacian adjK2) lapK2_symmetric i 1
        = if (0 : Fin 2) = 1 then 1 / 2 else -(1 / 2)
    rw [hanti, if_neg (by decide)]
    linear_combination -hsq
  · show eigvecOf (laplacian adjK2) lapK2_symmetric i 1
        * eigvecOf (laplacian adjK2) lapK2_symmetric i 0
        = if (1 : Fin 2) = 0 then 1 / 2 else -(1 / 2)
    rw [hanti, if_neg (by decide)]
    linear_combination -hsq
  · show eigvecOf (laplacian adjK2) lapK2_symmetric i 1
        * eigvecOf (laplacian adjK2) lapK2_symmetric i 1
        = if (1 : Fin 2) = 1 then 1 / 2 else -(1 / 2)
    rw [hanti, if_pos rfl]
    linear_combination hsq

/-- **The calculus on the `K₂` Laplacian, entrywise and sign-free**:
for any `f`, `f(L)` is the `±`-mixture `((f 0 ± f 2))/2` — the
kernel mode contributing `f 0 / 2` everywhere, the `λ = 2` mode
`± f 2 / 2`. No basis-orientation choice enters at any point (the
`fc_lapK2_outer_*` pins are sign-free). -/
theorem fc_lapK2_calc (f : ℝ → ℝ) :
    spectralCalc (laplacian adjK2) lapK2_symmetric f
      = !![(f 0 + f 2) / 2, (f 0 - f 2) / 2; (f 0 - f 2) / 2, (f 0 + f 2) / 2] := by
  have hsum00 : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 0 →
      eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 0 → False := by
    intro h0 h1
    have hs := lapK2_eigvalOf_sum
    simp only [Fin.sum_univ_two] at hs
    rw [h0, h1] at hs
    norm_num at hs
  have hsum22 : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 2 →
      eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 2 → False := by
    intro h0 h1
    have hs := lapK2_eigvalOf_sum
    simp only [Fin.sum_univ_two] at hs
    rw [h0, h1] at hs
    norm_num at hs
  have hcase : (eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 0 ∧
        eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 2) ∨
      (eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 2 ∧
        eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 0) := by
    rcases lapK2_eigvalOf_two 0 with e0 | e0
    · rcases lapK2_eigvalOf_two 1 with e1 | e1
      · exact (hsum00 e0 e1).elim
      · exact Or.inl ⟨e0, e1⟩
    · rcases lapK2_eigvalOf_two 1 with e1 | e1
      · exact Or.inr ⟨e0, e1⟩
      · exact (hsum22 e0 e1).elim
  ext a b
  rw [spectralCalc_apply (laplacian adjK2) lapK2_symmetric f a b]
  fin_cases a <;> fin_cases b
  · -- entry (0,0)
    show (∑ i, f (eigvalOf (laplacian adjK2) lapK2_symmetric i)
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 0
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 0)
      = ((f 0 + f 2) / 2)
    simp only [Fin.sum_univ_two]
    rcases hcase with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have oz := fc_lapK2_outer_zero e0 0 0
      have ot := fc_lapK2_outer_two e1 0 0
      rw [if_pos rfl] at ot
      rw [e0, e1, mul_assoc, oz, mul_assoc, ot]
      ring
    · have ot := fc_lapK2_outer_two e0 0 0
      have oz := fc_lapK2_outer_zero e1 0 0
      rw [if_pos rfl] at ot
      rw [e0, e1, mul_assoc, ot, mul_assoc, oz]
      ring
  · -- entry (0,1)
    show (∑ i, f (eigvalOf (laplacian adjK2) lapK2_symmetric i)
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 0
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 1)
      = ((f 0 - f 2) / 2)
    simp only [Fin.sum_univ_two]
    rcases hcase with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have oz := fc_lapK2_outer_zero e0 0 1
      have ot := fc_lapK2_outer_two e1 0 1
      rw [if_neg (by decide)] at ot
      rw [e0, e1, mul_assoc, oz, mul_assoc, ot]
      ring
    · have ot := fc_lapK2_outer_two e0 0 1
      have oz := fc_lapK2_outer_zero e1 0 1
      rw [if_neg (by decide)] at ot
      rw [e0, e1, mul_assoc, ot, mul_assoc, oz]
      ring
  · -- entry (1,0)
    show (∑ i, f (eigvalOf (laplacian adjK2) lapK2_symmetric i)
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 1
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 0)
      = ((f 0 - f 2) / 2)
    simp only [Fin.sum_univ_two]
    rcases hcase with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have oz := fc_lapK2_outer_zero e0 1 0
      have ot := fc_lapK2_outer_two e1 1 0
      rw [if_neg (by decide)] at ot
      rw [e0, e1, mul_assoc, oz, mul_assoc, ot]
      ring
    · have ot := fc_lapK2_outer_two e0 1 0
      have oz := fc_lapK2_outer_zero e1 1 0
      rw [if_neg (by decide)] at ot
      rw [e0, e1, mul_assoc, ot, mul_assoc, oz]
      ring
  · -- entry (1,1)
    show (∑ i, f (eigvalOf (laplacian adjK2) lapK2_symmetric i)
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 1
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 1)
      = ((f 0 + f 2) / 2)
    simp only [Fin.sum_univ_two]
    rcases hcase with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have oz := fc_lapK2_outer_zero e0 1 1
      have ot := fc_lapK2_outer_two e1 1 1
      rw [if_pos rfl] at ot
      rw [e0, e1, mul_assoc, oz, mul_assoc, ot]
      ring
    · have ot := fc_lapK2_outer_two e0 1 1
      have oz := fc_lapK2_outer_zero e1 1 1
      rw [if_pos rfl] at ot
      rw [e0, e1, mul_assoc, ot, mul_assoc, oz]
      ring

/-- **The Tikhonov calculus instance on `K₂`, pinned**: at `π = 1`
the filter matrix is `!![2/3, 1/3; 1/3, 2/3]` — the shrinkage factors
`1` (kernel) and `1/3` (`λ = 2`) mixed sign-free. -/
theorem fc_lapK2_tikhonov_calc :
    spectralCalc (laplacian adjK2) lapK2_symmetric (tikhonovShrinkage 1)
      = !![2 / 3, 1 / 3; 1 / 3, 2 / 3] := by
  rw [fc_lapK2_calc]
  norm_num [tikhonovShrinkage]

/-- **The reconciliation witnessed numerically**: through the equality
theorem and the pinned filter matrix, the calculus routes the signal
`![1, 0]` to `![2/3, 1/3]` — exactly the hand-solved Gaussian value
that `Tikhonov_QA.tik_K2_eq` pinned for the eigenbasis minimizer in
the original delivery. Two constructions, one number. -/
theorem fc_lapK2_reconcile :
    tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0] = ![2 / 3, 1 / 3] := by
  rw [tikhonovMinimizer_eq_spectralCalc_mulVec, fc_lapK2_tikhonov_calc]
  funext a
  fin_cases a <;>
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply] <;>
    norm_num

/-- **The normal equation, calculus route**: composing the equality
theorem with the matrix-level calculus normal equation (and the
`mulVec` conversions) re-derives
`tikhonovMinimizer_add_smul_one_mulVec`'s exact statement through
Mathlib's calculus algebra — no eigenbasis expansion anywhere in the
chain. -/
theorem fc_lapK2_normal_calculus :
    (laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      *ᵥ tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0]
      = (1 : ℝ) • ![1, 0] := by
  have hM := add_smul_one_mul_spectralCalc_tikhonovShrinkage adjK2
    adjK2_symmetric adjK2_nonneg (by norm_num : (0 : ℝ) < 1)
  -- entrywise associativity (the pin has no matrix-level mulVec
  -- associativity lemma in the needed orientation)
  have hassoc : (laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      *ᵥ (spectralCalc (laplacian adjK2) lapK2_symmetric
          (tikhonovShrinkage 1) *ᵥ ![1, 0])
      = ((laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      * spectralCalc (laplacian adjK2) lapK2_symmetric
          (tikhonovShrinkage 1)) *ᵥ ![1, 0] := by
    funext a
    simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.mul_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  rw [tikhonovMinimizer_eq_spectralCalc_mulVec adjK2 adjK2_symmetric 1 ![1, 0],
    hassoc, hM, Matrix.smul_mulVec_assoc, Matrix.one_mulVec]

/-- **The normal equation, hand route**: the same statement through
`Tikhonov_QA`'s pinned minimizer and hand-solved system — the two
routes to one statement, both proved, independently. -/
theorem fc_lapK2_normal_hand :
    (laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      *ᵥ tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0]
      = (1 : ℝ) • ![1, 0] := by
  rw [tik_K2_eq]
  exact normal_K2

/-- **The raw independent check of the calculus normal equation on
`K₂`**: `(L + 1•1) * f(L) = 1` by literal matrix arithmetic on the
pinned filter matrix and the pinned Laplacian entries — no theorem
consumed except the entry pins. -/
theorem fc_lapK2_normal_raw :
    (laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      * spectralCalc (laplacian adjK2) lapK2_symmetric (tikhonovShrinkage 1)
      = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [fc_lapK2_tikhonov_calc]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, lapK2_apply, Fin.sum_univ_two] <;>
    norm_num

/-- **The kernel-mode action instantiation**: the filter fixes the
kernel eigenvector exactly (factor `1` at `λ = 0`) — mean
preservation seen through the calculus action interface. -/
theorem fc_lapK2_kernel_action {i : Fin 2}
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 0) :
    spectralCalc (laplacian adjK2) lapK2_symmetric (tikhonovShrinkage 1)
      *ᵥ eigvecOf (laplacian adjK2) lapK2_symmetric i
      = eigvecOf (laplacian adjK2) lapK2_symmetric i := by
  have hone : tikhonovShrinkage 1 0 = 1 :=
    (tikhonovShrinkage_eq_one_iff (by norm_num : (1 : ℝ) ≠ 0)).mpr rfl
  rw [spectralCalc_mulVec_eigvecOf, hi, hone, one_smul]

/-- The junk shrinkage values at `π = -2`: at the spectral point
`λ = 2 = -π` the factor is the junk `0`; at `λ = 0` it is exactly
`1`. These are the values that break the normal equation off the PSD
regime. -/
theorem fc_lapK2_shrink_neg_two_zero : tikhonovShrinkage (-2 : ℝ) 0 = 1 := by
  norm_num [tikhonovShrinkage]

theorem fc_lapK2_shrink_neg_two_two : tikhonovShrinkage (-2 : ℝ) 2 = 0 := by
  norm_num [tikhonovShrinkage]

/-- **The fence: the filter matrix at `π = -2`** (computed through
the sign-free master lemma): the junk factor `0` at `λ = 2` kills the
anticonstant mode, leaving the pure kernel average `1/2` in every
entry. -/
theorem fc_lapK2_fence_matrix :
    spectralCalc (laplacian adjK2) lapK2_symmetric (tikhonovShrinkage (-2))
      = !![1 / 2, 1 / 2; 1 / 2, 1 / 2] := by
  rw [fc_lapK2_calc]
  norm_num [fc_lapK2_shrink_neg_two_zero, fc_lapK2_shrink_neg_two_two]

/-- **The fence: the hypothesis-free normal equation is false.** At
`π = -2` (a spectral point of `K₂`'s Laplacian, `2 = -π`), the
product `(L + π•1) * f(L)` is the all-`(-1)` matrix, not `(-2) • 1`:
the junk division at the spectral point breaks the pointwise identity
`shrink π λ · (λ + π) = π` exactly there. The `0 < π` hypothesis of
`add_smul_one_mul_spectralCalc_tikhonovShrinkage` (through PSD) is
load-bearing, not decorative. -/
theorem fc_lapK2_fence_not_normal :
    ¬ ((laplacian adjK2 + (-2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))
      * spectralCalc (laplacian adjK2) lapK2_symmetric
          (tikhonovShrinkage (-2))
      = (-2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  intro hcon
  have h01 := congrFun (congrFun hcon 0) 1
  rw [fc_lapK2_fence_matrix] at h01
  simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons,
    Matrix.of_apply, lapK2_apply] at h01
  norm_num at h01

end TikhonovReconciliation

/-!
## Section F: the Heat reconciliation (the second consumer)

The Heat half of `proposals/hermitian-calculus-consumer-tikhonov-heat.md`
(2026-08-25): the matrix-exponential heat kernel is the calculus at the
exponential family. All witnesses live on the same `Tikhonov_QA` `K₂`
fixture (`adjK2`, Laplacian spectrum `{0, 2}`) as Section E, so the two
consumer reconciliations are pinned against one shared, independently
delivered eigenbasis. The two routes under test are genuinely
independent proof stacks: Mathlib's `cfc` (via the equality theorem)
against the `Heat.lean` entrywise exponential-series engine — the
reconciliation the parent proposal's Step-0 pricing predicted would
carry mathematical content.
-/

section HeatReconciliation

open Scaffold.Mathlib.GraphTheory.Tikhonov.QA

/-- **The calculus on the `K₂` Laplacian at the exponential family,
entrywise and sign-free** (the Section-E master lemma instantiated at
`f = (x ↦ e^{-t·x})`): the decay factors `1` (kernel) and `e^{-2t}`
(`λ = 2`) mixed sign-free into `!![(1 ± e^{-2t})/2]`. -/
theorem fc_heat_K2_calc (t : ℝ) :
    spectralCalc (laplacian adjK2) lapK2_symmetric (fun x => Real.exp (-(t * x)))
      = !![(1 + Real.exp (-(2 * t))) / 2, (1 - Real.exp (-(2 * t))) / 2;
           (1 - Real.exp (-(2 * t))) / 2, (1 + Real.exp (-(2 * t))) / 2] := by
  have h0 : Real.exp (-(t * (0 : ℝ))) = 1 := by simp
  have h2 : Real.exp (-(t * (2 : ℝ))) = Real.exp (-(2 * t)) := by congr 1; ring
  rw [fc_lapK2_calc]
  simp only [h0, h2]

/-- **Route 1 — the calculus route**: through the equality theorem
`heatKernel_eq_spectralCalc_exp`, the matrix-exponential heat kernel is
the closed form `!![(1 ± e^{-2t})/2]` at every time. This is the `cfc`
side of the reconciliation. -/
theorem fc_heat_K2_calculus_route (t : ℝ) :
    heatKernel adjK2 t
      = !![(1 + Real.exp (-(2 * t))) / 2, (1 - Real.exp (-(2 * t))) / 2;
           (1 - Real.exp (-(2 * t))) / 2, (1 + Real.exp (-(2 * t))) / 2] := by
  rw [heatKernel_eq_spectralCalc_exp adjK2 adjK2_symmetric t, fc_heat_K2_calc]

/-- **Route 2 — the series-engine route**: the same closed form, at the
action level on the signal `![1, 0]`, computed from
`heatKernel_mulVec_eq_sum` (`Heat.lean`'s entrywise exponential-series
machinery — no `cfc` anywhere) and the Section-E sign-free
outer-product pins. Two independent proof stacks, one vector. -/
theorem fc_heat_K2_series_route (t : ℝ) :
    heatKernel adjK2 t *ᵥ (![1, 0] : Fin 2 → ℝ)
      = ![(1 + Real.exp (-(2 * t))) / 2, (1 - Real.exp (-(2 * t))) / 2] := by
  have hsum00 : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 0 →
      eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 0 → False := by
    intro h0 h1
    have hs := lapK2_eigvalOf_sum
    simp only [Fin.sum_univ_two] at hs
    rw [h0, h1] at hs
    norm_num at hs
  have hsum22 : eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 2 →
      eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 2 → False := by
    intro h0 h1
    have hs := lapK2_eigvalOf_sum
    simp only [Fin.sum_univ_two] at hs
    rw [h0, h1] at hs
    norm_num at hs
  have hcase : (eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 0 ∧
        eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 2) ∨
      (eigvalOf (laplacian adjK2) lapK2_symmetric 0 = 2 ∧
        eigvalOf (laplacian adjK2) lapK2_symmetric 1 = 0) := by
    rcases lapK2_eigvalOf_two 0 with e0 | e0
    · rcases lapK2_eigvalOf_two 1 with e1 | e1
      · exact (hsum00 e0 e1).elim
      · exact Or.inl ⟨e0, e1⟩
    · rcases lapK2_eigvalOf_two 1 with e1 | e1
      · exact Or.inr ⟨e0, e1⟩
      · exact (hsum22 e0 e1).elim
  have hdot : ∀ i : Fin 2,
      Matrix.dotProduct (eigvecOf (laplacian adjK2) lapK2_symmetric i)
        (![1, 0] : Fin 2 → ℝ)
      = eigvecOf (laplacian adjK2) lapK2_symmetric i 0 := by
    intro i
    simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.tail_cons, mul_one,
      mul_zero, add_zero]
  have hz : Real.exp (-(t * (0 : ℝ))) = 1 := by simp
  have ht : Real.exp (-(t * (2 : ℝ))) = Real.exp (-(2 * t)) := by congr 1; ring
  funext a
  rw [heatKernel_mulVec_eq_sum adjK2 adjK2_symmetric t (![1, 0] : Fin 2 → ℝ)]
  simp only [hdot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  fin_cases a
  · show (∑ i, Real.exp (-(t * eigvalOf (laplacian adjK2) lapK2_symmetric i))
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 0
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 0)
        = ((1 + Real.exp (-(2 * t))) / 2)
    simp only [Fin.sum_univ_two]
    rcases hcase with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have oz := fc_lapK2_outer_zero e0 0 0
      have ot := fc_lapK2_outer_two e1 0 0
      rw [if_pos rfl] at ot
      rw [e0, e1, hz, ht, mul_assoc, oz, mul_assoc, ot]
      ring
    · have ot := fc_lapK2_outer_two e0 0 0
      have oz := fc_lapK2_outer_zero e1 0 0
      rw [if_pos rfl] at ot
      rw [e0, e1, hz, ht, mul_assoc, ot, mul_assoc, oz]
      ring
  · show (∑ i, Real.exp (-(t * eigvalOf (laplacian adjK2) lapK2_symmetric i))
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 0
          * eigvecOf (laplacian adjK2) lapK2_symmetric i 1)
        = ((1 - Real.exp (-(2 * t))) / 2)
    simp only [Fin.sum_univ_two]
    rcases hcase with ⟨e0, e1⟩ | ⟨e0, e1⟩
    · have oz := fc_lapK2_outer_zero e0 0 1
      have ot := fc_lapK2_outer_two e1 0 1
      rw [if_neg (by decide)] at ot
      rw [e0, e1, hz, ht, mul_assoc, oz, mul_assoc, ot]
      ring
    · have ot := fc_lapK2_outer_two e0 0 1
      have oz := fc_lapK2_outer_zero e1 0 1
      rw [if_neg (by decide)] at ot
      rw [e0, e1, hz, ht, mul_assoc, ot, mul_assoc, oz]
      ring

/-- **The semigroup through the calculus route** (the substantive
reconciliation layer at QA scale): flowing `1` then `2` equals flowing
`3`, through the equality theorem pair and the calculus-algebra
semigroup — no eigenbasis, no `Matrix.exp_add_of_commute`. -/
theorem fc_heat_K2_semigroup_calculus :
    heatKernel adjK2 1 * heatKernel adjK2 2 = heatKernel adjK2 3 := by
  rw [heatKernel_mul_heatKernel_of_spectralCalc adjK2 adjK2_symmetric 1 2]
  norm_num

/-- **The semigroup through the delivered commute route**: the same
statement through `Heat.lean`'s hypothesis-free
`heatKernel_mul_heatKernel` (`Matrix.exp_add_of_commute`). Two
independent proof technologies, one semigroup law. -/
theorem fc_heat_K2_semigroup_commute :
    heatKernel adjK2 1 * heatKernel adjK2 2 = heatKernel adjK2 3 := by
  rw [heatKernel_mul_heatKernel adjK2 1 2]
  norm_num

/-- **The semigroup pinned to the number both routes deliver**: the
product at times `1, 2` is the closed form at time `3` — entries
`(1 ± e^{-6})/2` with `e^{-2}·e^{-4} = e^{-6}` waiting inside. -/
theorem fc_heat_K2_semigroup_pin :
    heatKernel adjK2 1 * heatKernel adjK2 2
      = !![(1 + Real.exp (-(6 : ℝ))) / 2, (1 - Real.exp (-(6 : ℝ))) / 2;
           (1 - Real.exp (-(6 : ℝ))) / 2, (1 + Real.exp (-(6 : ℝ))) / 2] := by
  rw [fc_heat_K2_semigroup_calculus, fc_heat_K2_calculus_route]
  norm_num

/-- **The raw closed-form product check** (no heat or calculus theorems
consumed): `CF(1) * CF(2) = CF(3)` by literal matrix arithmetic, the
only scalar input being `Real.exp_add` at `e^{-2}·e^{-4} = e^{-6}` —
the closed-form family closes under multiplication, independently of
how any of its members were computed. -/
theorem fc_heat_K2_semigroup_raw :
    (!![(1 + Real.exp (-(2 : ℝ))) / 2, (1 - Real.exp (-(2 : ℝ))) / 2;
        (1 - Real.exp (-(2 : ℝ))) / 2, (1 + Real.exp (-(2 : ℝ))) / 2]
        : Matrix (Fin 2) (Fin 2) ℝ)
      * !![(1 + Real.exp (-(4 : ℝ))) / 2, (1 - Real.exp (-(4 : ℝ))) / 2;
        (1 - Real.exp (-(4 : ℝ))) / 2, (1 + Real.exp (-(4 : ℝ))) / 2]
      = !![(1 + Real.exp (-(6 : ℝ))) / 2, (1 - Real.exp (-(6 : ℝ))) / 2;
        (1 - Real.exp (-(6 : ℝ))) / 2, (1 + Real.exp (-(6 : ℝ))) / 2] := by
  have h24 : Real.exp (-(2 : ℝ)) * Real.exp (-(4 : ℝ)) = Real.exp (-(6 : ℝ)) := by
    rw [← Real.exp_add]
    norm_num
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b
  · show (1 + Real.exp (-(2 : ℝ))) / 2 * ((1 + Real.exp (-(4 : ℝ))) / 2)
        + (1 - Real.exp (-(2 : ℝ))) / 2 * ((1 - Real.exp (-(4 : ℝ))) / 2)
        = (1 + Real.exp (-(6 : ℝ))) / 2
    linear_combination h24 / 2
  · show (1 + Real.exp (-(2 : ℝ))) / 2 * ((1 - Real.exp (-(4 : ℝ))) / 2)
        + (1 - Real.exp (-(2 : ℝ))) / 2 * ((1 + Real.exp (-(4 : ℝ))) / 2)
        = (1 - Real.exp (-(6 : ℝ))) / 2
    linear_combination -(h24) / 2
  · show (1 - Real.exp (-(2 : ℝ))) / 2 * ((1 + Real.exp (-(4 : ℝ))) / 2)
        + (1 + Real.exp (-(2 : ℝ))) / 2 * ((1 - Real.exp (-(4 : ℝ))) / 2)
        = (1 - Real.exp (-(6 : ℝ))) / 2
    linear_combination -(h24) / 2
  · show (1 - Real.exp (-(2 : ℝ))) / 2 * ((1 - Real.exp (-(4 : ℝ))) / 2)
        + (1 + Real.exp (-(2 : ℝ))) / 2 * ((1 + Real.exp (-(4 : ℝ))) / 2)
        = (1 + Real.exp (-(6 : ℝ))) / 2
    linear_combination h24 / 2

/-- **Time zero through the calculus**: the equality theorem at `t = 0`
collapses to the identity matrix — the calculus preserves the
delivered `heatKernel_zero`, the two constructions agreeing at the
semigroup unit. -/
theorem fc_heat_K2_zero_calculus :
    heatKernel adjK2 0 = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [fc_heat_K2_calculus_route]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply, Matrix.one_apply] <;>
    norm_num [Real.exp_zero]

/-- **The DC mode is fixed** (eigenmode decay through the calculus
action interface, kernel mode): the calculus at the exponential family
acts as the identity on the constant mode — mean preservation seen
through `cfc`, mirroring Section E's kernel action. -/
theorem fc_heat_K2_kernel_action {i : Fin 2} (t : ℝ)
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 0) :
    spectralCalc (laplacian adjK2) lapK2_symmetric (fun x => Real.exp (-(t * x)))
      *ᵥ eigvecOf (laplacian adjK2) lapK2_symmetric i
      = eigvecOf (laplacian adjK2) lapK2_symmetric i := by
  rw [spectralCalc_mulVec_eigvecOf, hi]
  have h1 : Real.exp (-(t * (0 : ℝ))) = 1 := by simp
  rw [h1, one_smul]

/-- **The anticonstant mode decays** (eigenmode decay through the
calculus action interface, `λ = 2` mode): the calculus damps the
oscillating mode by exactly `e^{-2t}` — the calculus-side mirror of
the delivered series-route `heatKernel_mulVec_eigvecOf`. -/
theorem fc_heat_K2_mode_two_action {i : Fin 2} (t : ℝ)
    (hi : eigvalOf (laplacian adjK2) lapK2_symmetric i = 2) :
    spectralCalc (laplacian adjK2) lapK2_symmetric (fun x => Real.exp (-(t * x)))
      *ᵥ eigvecOf (laplacian adjK2) lapK2_symmetric i
      = Real.exp (-(2 * t)) • eigvecOf (laplacian adjK2) lapK2_symmetric i := by
  rw [spectralCalc_mulVec_eigvecOf, hi]
  have h2 : Real.exp (-(t * (2 : ℝ))) = Real.exp (-(2 * t)) := by rw [mul_comm]
  rw [h2]

/-- **The nontriviality fence**: the heat kernel at `t = 1` is provably
not the identity — entry `(0, 1)` is `(1 - e^{-2})/2 > 0` since
`e^{-2} < 1`. Diffusion moves mass (while conserving it, per the
delivered `heatKernel_mulVec_onesVec`). This refutes, in proved form,
any degenerate reading of the equality theorem that collapses the
exponential family to a constant — e.g. a junk calculus evaluating
`f` only at the kernel eigenvalue `0` would return exactly `1`. -/
theorem fc_heat_K2_not_one :
    heatKernel adjK2 1 ≠ (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  intro hcon
  have h01 := congrFun (congrFun hcon 0) 1
  rw [fc_heat_K2_calculus_route] at h01
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.of_apply, Matrix.one_apply] at h01
  norm_num at h01
  have hlt : Real.exp (-(2 : ℝ)) < 1 := by
    have := Real.exp_lt_exp.mpr (by norm_num : -(2 : ℝ) < (0 : ℝ))
    rwa [Real.exp_zero] at this
  linarith

end HeatReconciliation

/-!
## Section G: the resolvent identity on `K₂`

The consumer stub's priced follow-on (2026-08-25): the Tikhonov filter
*is* `π • (L + π•1)⁻¹`, witnessed on the same `K₂` fixture as
Sections E/F by two independent routes — the matrix-algebra route
(through the shelf resolvent program's invertibility supplier, its
first functional-calculus consumer) and the calculus route (through
`cfc_inv`) — pinned to the same concrete matrix as Section E's
eigenbasis instance, joined to the hand-solved Gaussian minimizer, and
fenced at the `π = -2` degeneration where both the shrinkage division
and the shifted inverse go junk.
-/

section ResolventIdentity

open Scaffold.Mathlib.GraphTheory.Tikhonov.QA
open Scaffold.Mathlib.Analysis.OperatorTheory.Resolvent

/-- Avoidance at `π = 1` holds on `K₂`: every spectral point is `0` or
`2` (Section E's eigenvalue pins), so `x + 1` is `1` or `3`. This is
the general-symmetric theorems' hypothesis in the PSD regime. -/
theorem fc_res_lapK2_avoid_one :
    ∀ x ∈ spectrum ℝ (laplacian adjK2), x + 1 ≠ 0 := by
  intro x hx
  rw [Matrix.IsHermitian.eigenvalues_eq_spectrum_real
    (isHermitian_of_isSymm lapK2_symmetric)] at hx
  obtain ⟨i, hi⟩ := hx
  have hi' : eigvalOf (laplacian adjK2) lapK2_symmetric i = x := hi
  rw [← hi']
  rcases lapK2_eigvalOf_two i with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- Avoidance at `π = -2` **fails**, and the failure is spectral:
`2 = -π` is an eigenvalue of `K₂`'s Laplacian — proved here, not
asserted, so the fence below exhibits the exact broken hypothesis. -/
theorem fc_res_lapK2_avoid_neg2_fails :
    ¬ ∀ x ∈ spectrum ℝ (laplacian adjK2), x + (-2 : ℝ) ≠ 0 := by
  intro h
  have hex : ∃ i, eigvalOf (laplacian adjK2) lapK2_symmetric i = 2 := by
    rcases lapK2_eigvalOf_two 0 with h0 | h0
    · rcases lapK2_eigvalOf_two 1 with h1 | h1
      · exfalso
        have hs := lapK2_eigvalOf_sum
        simp only [Fin.sum_univ_two] at hs
        rw [h0, h1] at hs
        norm_num at hs
      · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  obtain ⟨i, hi⟩ := hex
  have h2 : (2 : ℝ) ∈ spectrum ℝ (laplacian adjK2) := by
    rw [Matrix.IsHermitian.eigenvalues_eq_spectrum_real
      (isHermitian_of_isSymm lapK2_symmetric)]
    exact ⟨i, hi⟩
  exact h 2 h2 (by norm_num)

/-- The shifted Laplacian at `π = 1` and its raw inverse: `L + 1•1 =
!![2, -1; -1, 2]` with determinant `3`, so the inverse is
`!![2/3, 1/3; 1/3, 2/3]` — computed by the right-inverse criterion on
literal matrix arithmetic, no theorem about Laplacians involved. -/
theorem fc_res_K2_inv :
    (laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹
      = !![2 / 3, 1 / 3; 1 / 3, 2 / 3] := by
  have hshift : laplacian adjK2
      + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![2, -1; -1, 2] := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      lapK2_apply]
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hshift]
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i <;> fin_cases j
  <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- **Route A pinned**: the headline (matrix-algebra route — the
normal equation plus the shelf resolvent program's invertibility
supplier) delivers `π • (L + π•1)⁻¹` at `π = 1`, and the raw inverse
of the previous lemma makes it the concrete matrix
`!![2/3, 1/3; 1/3, 2/3]` — *the same matrix Section E pinned for the
calculus instance* `fc_lapK2_tikhonov_calc` via the sign-free master
lemma: three constructions, one operator. -/
theorem fc_res_K2_routeA_pin :
    spectralCalc (laplacian adjK2) lapK2_symmetric (tikhonovShrinkage 1)
      = !![2 / 3, 1 / 3; 1 / 3, 2 / 3] := by
  rw [spectralCalc_tikhonovShrinkage_eq_smul_inv adjK2 adjK2_symmetric
    adjK2_nonneg (by norm_num : (0 : ℝ) < 1), one_smul, fc_res_K2_inv]

/-- **Route B pinned**: the general-symmetric identity (calculus route
— `cfc_inv` through the additive layer, no matrix inverse or
determinant anywhere) instantiated at the same fixture through the
proved avoidance of `fc_res_lapK2_avoid_one` delivers the same
concrete matrix. The two proof technologies agree on one number; a
wrong `cfc_inv` specialization, a wrong junk-inverse alignment
(`Matrix.nonsing_inv_eq_ring_inverse`), or a wrong additive layer
breaks this pin while route A stands. -/
theorem fc_res_K2_routeB_pin :
    spectralCalc (laplacian adjK2) lapK2_symmetric (tikhonovShrinkage 1)
      = !![2 / 3, 1 / 3; 1 / 3, 2 / 3] := by
  rw [spectralCalc_tikhonovShrinkage_eq_smul_inv_of_forall_add_ne_zero
    _ _ fc_res_lapK2_avoid_one, one_smul, fc_res_K2_inv]

/-- The invertibility supplier witnessed: through the shelf resolvent
program's spectral-gap-free theorem (form-PSD plus `0 < π`), with no
eigenvalue computed. -/
theorem fc_res_K2_det_unit_supplier :
    IsUnit (laplacian adjK2
      + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det :=
  isUnit_det_add_smul_one_of_quadForm_nonneg
    (laplacian_psd adjK2 adjK2_symmetric adjK2_nonneg)
    (by norm_num : (0 : ℝ) < 1)

/-- The same determinant, raw: the shift is `!![2, -1; -1, 2]]` with
determinant exactly `3` — the supplier's conclusion checked by literal
arithmetic. -/
theorem fc_res_K2_det_eq_three :
    (laplacian adjK2 + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).det = 3 := by
  have hshift : laplacian adjK2
      + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![2, -1; -1, 2] := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      lapK2_apply]
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hshift]
  norm_num [Matrix.det_fin_two]

/-- **The minimizer in resolvent form, and its numeric value**: the
consumer corollary exhibits `x* = π • ((L + π•1)⁻¹ *ᵥ y)` — the
textbook shifted-inverse solve — and at `y = ![1, 0]` the raw inverse
of `fc_res_K2_inv` routes it to `![2/3, 1/3]`, exactly the hand-solved
Gaussian value `tik_K2_eq` pinned in the original Tikhonov delivery
(and Section E's `fc_lapK2_reconcile`). Two constructions of the
minimizer, one number. -/
theorem fc_res_K2_minimizer_pin :
    (1 : ℝ) • ((laplacian adjK2
        + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ *ᵥ ![1, 0])
      = ![2 / 3, 1 / 3] := by
  rw [one_smul, fc_res_K2_inv]
  funext a
  fin_cases a
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply]
    norm_num
  · simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.tail_cons, Matrix.of_apply]
    norm_num

theorem fc_res_K2_minimizer :
    tikhonovMinimizer adjK2 adjK2_symmetric 1 ![1, 0]
      = (1 : ℝ) • ((laplacian adjK2
          + (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ *ᵥ ![1, 0]) :=
  tikhonovMinimizer_eq_smul_inv_mulVec adjK2 adjK2_symmetric adjK2_nonneg
    (by norm_num : (0 : ℝ) < 1) ![1, 0]

/-- The singular case at `π = -2`: the shifted Laplacian
`!![-1, -1; -1, -1]]` has determinant `0`, so the matrix inverse is
the junk zero matrix (`Ring.inverse 0 = 0` through `Matrix.inv_def`). -/
theorem fc_res_K2_singular_inv :
    (laplacian adjK2
      + (-2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹ = 0 := by
  have hmat : laplacian adjK2
      + (-2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, -1; -1, -1] := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      lapK2_apply]
    fin_cases i <;> fin_cases j <;> norm_num
  rw [hmat, Matrix.inv_def]
  norm_num [Matrix.det_fin_two, Ring.inverse_zero]

/-- **The fence: the resolvent identity is false at `π = -2`.** Both
junk surfaces collide at the degeneration: the filter matrix is the
pure kernel average `!![1/2, 1/2; 1/2, 1/2]]` (Section E's
`fc_lapK2_fence_matrix` — the shrinkage is the junk `0` at the
spectral point `2 = -π`), while `(-2) • (L - 2•1)⁻¹` is `0` (the
singular inverse of the previous lemma). Entry `(0, 0)`: `1/2 ≠ 0`.
For the headline `spectralCalc_tikhonovShrinkage_eq_smul_inv` this
isolates exactly `hπ` (symmetry and nonnegativity hold on `K₂`,
`¬(0 < -2)` by `norm_num`); for the general
`..._of_forall_add_ne_zero` it isolates exactly the avoidance
hypothesis (symmetry holds; `fc_res_lapK2_avoid_neg2_fails` proves the
failure spectral). The delivered normal-equation fence
`fc_lapK2_fence_not_normal` fences the general *normal equation's*
only other hypothesis the same way. -/
theorem fc_res_K2_fence_not_inv :
    ¬ (spectralCalc (laplacian adjK2) lapK2_symmetric (tikhonovShrinkage (-2))
      = (-2 : ℝ)
          • (laplacian adjK2
              + (-2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))⁻¹) := by
  intro hcon
  have h00 := congrFun (congrFun hcon 0) 0
  rw [fc_lapK2_fence_matrix, fc_res_K2_singular_inv] at h00
  simp only [Matrix.smul_apply, Matrix.zero_apply, smul_zero,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.of_apply] at h00
  norm_num at h00

end ResolventIdentity

end SpectralGraphTheory.QA
