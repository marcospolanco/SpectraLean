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

  QA never proves, validates, or certifies any axiom: this file
  contains no `sorry`/`admit`, and the bridge it exercises consumes
  none (Mathlib's calculus is proved upstream).

  All fixtures are `Fin 2`; the public theorems are size- and
  weight-general.
-/

import Scaffold.Mathlib.GraphTheory.FunctionalCalculus
import Scaffold.QA.SpectralGraph.Band_QA
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

end SpectralGraphTheory.QA
