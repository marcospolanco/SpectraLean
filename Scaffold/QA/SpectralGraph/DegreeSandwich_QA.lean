/-
Copyright 2024 Scaffold Contributors

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Scaffold.Mathlib.GraphTheory.VariationalTransfer
import Scaffold.QA.SpectralGraph.Fiedler_QA
import Scaffold.QA.SpectralGraph.IrregularCheeger_QA

/-!
# QA for the degree eigenvalue sandwich

The QA obligations of the degree sandwich family delivered in
`GraphTheory.VariationalTransfer` (2026-08-29):

- the **P₃ instances**: the exact pin `λ₂ (L_sym P₃) = 1` by two
  independent raw computations (the `≤` side at the eigenpair witness
  `![1, 0, -1]`, the `≥` side by the degree-weighted zero-sum
  constraint algebra), the upper side of the sandwich **attained at
  equality** (`1 = λ₂ / dmin` at `dmin = 1` — a wrong constant on the
  engine's `dmin` half breaks exactly this pin), the lower-side
  instance at the true ceiling `dmax = 2` (values `1/2 ≤ 1`, the
  bracket's honest slack), the engine at a **non-second index**
  (`k = 2`: `3/2 ≤ 2` through the trace-route pins on both spectra),
  and the **wrong-constant pairing fence** (the upper side with `dmax`
  in `dmin`'s place is refuted: `1 ≤ 1/2` is false);
- the **K₂ regular squeeze**: at `dmin = dmax = 1` both sides collapse
  to `2 ≤ 2` — attained on both ends (combinatorial `λ₂ = 2` by the
  kernel-plus-trace route, normalized `λ₂ = 2` joined to the delivered
  `icEdge_normLap_secondEval`);
- the **`dmin = 0` fence**: on `K₂ ⊕` an isolated vertex (degrees
  `(1, 1, 0)` — the degree-floor hypothesis `∀ i, 0 ≤ deg` still
  holds, only the `0 < dmin` guard fails) the un-guarded upper-side
  statement reads `λ₂ (L_sym) ≤ lambda2 / 0`, and `λ₂ (L_sym) = 1`
  (pinned by two raw computations) against `lambda2 / 0 = 0`: refuted.
  This exhibits the junk-instantiation failure mode the engine's
  positive-degree hypothesis fences (the engine itself excludes the
  fixture).

Fixtures are declared under fresh names rather than imported from the
QA files that inspired them (the repository convention; `path3Adj` and
`cheegerEdgeAdj` are reused through module imports where their pins live).
Everything here is proved; no `sorry`, no `admit`, no axiom contact
beyond the standard three.
-/

/-!
# QA spike: the degree eigenvalue sandwich
-/

open scoped Matrix
namespace SpectralGraphTheory.QA

/-! ## The `P₃` fixture stack -/

theorem dsP3_deg (i : Fin 3) :
    deg path3Adj i = if (i : ℕ) = 1 then 2 else 1 := by
  fin_cases i <;> rw [deg, Fin.sum_univ_three] <;> norm_num [path3Adj]

theorem dsP3_pos_deg (i : Fin 3) : 0 < deg path3Adj i := by
  rw [dsP3_deg i]
  by_cases h : (i : ℕ) = 1 <;> simp [h]

theorem dsP3_degMin (i : Fin 3) : (1 : ℝ) ≤ deg path3Adj i := by
  rw [dsP3_deg i]
  by_cases h : (i : ℕ) = 1 <;> simp [h]

theorem dsP3_degMax (i : Fin 3) : deg path3Adj i ≤ (2 : ℝ) := by
  rw [dsP3_deg i]
  by_cases h : (i : ℕ) = 1 <;> simp [h]

theorem dsP3_kernelVec :
    degreeSqrt path3Adj *ᵥ (onesVec : Fin 3 → ℝ) = ![1, Real.sqrt 2, 1] := by
  funext i
  fin_cases i <;>
    simp [degreeSqrt_mulVec, dsP3_deg, Matrix.mulVec_diagonal,
      Real.sqrt_one, onesVec]

/-- Entry form of the normalized Laplacian (any adjacency): the generic
unfold used by every raw computation below. -/
theorem dsP3_normLap_entry (i j : Fin 3) :
    normalizedLaplacian path3Adj i j
      = (if i = j then (1 : ℝ) else 0)
        - (Real.sqrt (deg path3Adj i))⁻¹ * path3Adj i j
          * (Real.sqrt (deg path3Adj j))⁻¹ := by
  simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
    Matrix.diagonal_apply]

/-- The raw quadratic form of `L_sym(P₃)` at any vector. -/
theorem dsP3_normLap_quadForm (x : Fin 3 → ℝ) :
    quadForm (normalizedLaplacian path3Adj) x
      = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2
        - 2 * (Real.sqrt 2)⁻¹ * (x 1) * ((x 0) + (x 2)) := by
  have hsq : ∀ i : Fin 3, Real.sqrt (deg path3Adj i)
      = if (i : ℕ) = 1 then Real.sqrt 2 else 1 := by
    intro i
    rw [dsP3_deg i]
    by_cases h : (i : ℕ) = 1 <;> simp [h]
  have hA : ∀ i j : Fin 3, path3Adj i j
      = if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then (1 : ℝ) else 0 :=
    fun i j => rfl
  simp only [quadForm, Matrix.dotProduct, Matrix.mulVec, Fin.sum_univ_three,
    dsP3_normLap_entry, hsq, hA, Real.sqrt_one]
  simp (config := {decide := true})
  ring

theorem dsP3_inv_sqrt_two : (Real.sqrt 2)⁻¹ * Real.sqrt 2 = 1 :=
  inv_mul_cancel₀ (by positivity)

/-- **`λ₂ (L_sym P₃) ≥ 1`, the hard side by raw computation.** Every
degree-weighted zero-sum test vector has Rayleigh quotient at least
`1`: the cross terms collapse through the constraint `x 0 + x 2 =
-√2 · x 1`, leaving `q = ‖x‖² + 2 · x 1²`. -/
theorem dsP3_normLap_ge_one :
    1 ≤ secondEval (normalizedLaplacian path3Adj)
        (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
        (by norm_num) := by
  have hpsd := normalizedLaplacian_psd path3Adj path3Adj_symmetric
    path3Adj_nonneg dsP3_pos_deg
  have hwne : degreeSqrt path3Adj *ᵥ (onesVec : Fin 3 → ℝ) ≠ 0 := by
    rw [dsP3_kernelVec]
    intro h
    have h1 := congrFun h 1
    simp at h1
  rw [secondEval_variational_of_ker
    (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
    hpsd hwne
    (normalizedLaplacian_mulVec_degreeSqrt_onesVec path3Adj dsP3_pos_deg)
    (by norm_num)]
  refine le_csInf ?_ ?_
  · refine ⟨rayleigh (normalizedLaplacian path3Adj) ![1, 0, -1],
      ![1, 0, -1], by
        intro h
        have h0 := congrFun h 0
        simp at h0, ?_, rfl⟩
    simp only [Matrix.dotProduct, Fin.sum_univ_three, dsP3_kernelVec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      onesVec]
    norm_num
  · rintro r ⟨x, hx0, hxorth, rfl⟩
    have hcon : (x 0) + Real.sqrt 2 * (x 1) + (x 2) = 0 := by
      have h1 : (x 0) + (x 1) * Real.sqrt 2 + (x 2) = 0 := by
        simpa [Matrix.dotProduct, Fin.sum_univ_three, dsP3_kernelVec,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          onesVec] using hxorth
      have h2 : Real.sqrt 2 * (x 1) = (x 1) * Real.sqrt 2 := mul_comm _ _
      linarith
    have hs : Matrix.dotProduct x x = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
      simp [Matrix.dotProduct, Fin.sum_univ_three]
      ring
    have hq := dsP3_normLap_quadForm x
    have hx02 : (x 0) + (x 2) = -(Real.sqrt 2) * (x 1) := by linarith
    have hdot : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
    have hsumpos : 0 < (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
      rw [← hs]; exact hdot
    rw [rayleigh, if_neg hx0, hq, hx02, hs]
    have hkey : ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2)
        - 2 * (Real.sqrt 2)⁻¹ * (x 1) * (-(Real.sqrt 2) * (x 1))
        = ((x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2) + 2 * (x 1) ^ 2 :=
      by linear_combination 2 * (x 1) ^ 2 * dsP3_inv_sqrt_two
    rw [hkey, one_le_div hsumpos]
    nlinarith [sq_nonneg (x 1)]

/-- The eigenvector witness: `![1, 0, -1]` has Rayleigh quotient
exactly `1` and is orthogonal to the kernel vector — the `≤` side. -/
theorem dsP3_normLap_le_one :
    secondEval (normalizedLaplacian path3Adj)
        (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
        (by norm_num) ≤ 1 := by
  have hpsd := normalizedLaplacian_psd path3Adj path3Adj_symmetric
    path3Adj_nonneg dsP3_pos_deg
  have hwne : degreeSqrt path3Adj *ᵥ (onesVec : Fin 3 → ℝ) ≠ 0 := by
    rw [dsP3_kernelVec]
    intro h
    have h1 := congrFun h 1
    simp at h1
  have hw : (![1, 0, -1] : Fin 3 → ℝ) ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    simp at h0
  have horth : Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ)
      (degreeSqrt path3Adj *ᵥ (onesVec : Fin 3 → ℝ)) = 0 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_three, dsP3_kernelVec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      onesVec]
    norm_num
  have hmain := secondEval_le_rayleigh_of_ker
    (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
    hpsd hwne
    (normalizedLaplacian_mulVec_degreeSqrt_onesVec path3Adj dsP3_pos_deg)
    (by norm_num) hw horth
  have hq : quadForm (normalizedLaplacian path3Adj) (![1, 0, -1] : Fin 3 → ℝ)
      = 2 := by
    rw [dsP3_normLap_quadForm]
    norm_num
  have hdot : Matrix.dotProduct (![1, 0, -1] : Fin 3 → ℝ)
      (![1, 0, -1] : Fin 3 → ℝ) = 2 := by
    simp only [Matrix.dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    norm_num
  rw [rayleigh, if_neg hw, hq, hdot] at hmain
  norm_num at hmain
  exact hmain

/-- **The exact pin: `λ₂ (L_sym P₃) = 1`.** Both sides by independent
raw computation (the `≤` side at the eigenpair witness, the `≥` side
by the constraint algebra). -/
theorem dsP3_normLap_secondEval_eq_one :
    secondEval (normalizedLaplacian path3Adj)
        (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
        (by norm_num) = 1 :=
  le_antisymm dsP3_normLap_le_one dsP3_normLap_ge_one

/-! ## The spectrum tails (trace route) -/

theorem dsP3_normLap_evals_zero :
    evals (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
      ⟨0, by norm_num⟩ = 0 :=
  normalizedLaplacian_evals_zero path3Adj path3Adj_symmetric path3Adj_nonneg
    dsP3_pos_deg (by norm_num)

theorem dsP3_normLap_trace :
    (normalizedLaplacian path3Adj).trace = 3 := by
  have hdiag : ∀ i : Fin 3,
      (normalizedLaplacian path3Adj) i i = 1 := by
    intro i
    rw [dsP3_normLap_entry i i]
    have hA : path3Adj i i = 0 := by
      simp only [path3Adj, Matrix.of_apply]
      have hne : ¬((i : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (i : ℕ)) := by
        omega
      simp [hne]
    rw [if_pos rfl, hA, mul_zero, zero_mul, sub_zero]
  rw [show (normalizedLaplacian path3Adj).trace
      = ∑ i, (normalizedLaplacian path3Adj) i i from rfl,
    Finset.sum_congr rfl fun i _ => hdiag i]
  simp

theorem dsP3_normLap_evals_two :
    evals (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
      (2 : Fin 3) = 2 := by
  have hsum := evals_sum_eq_trace
    (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
  rw [dsP3_normLap_trace] at hsum
  have h2 : ∑ i : Fin 3,
      evals (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric) i = 3 :=
    hsum
  simp only [Fin.sum_univ_three] at h2
  have h0 : evals (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
      (0 : Fin 3) = 0 := dsP3_normLap_evals_zero
  have h1 : evals (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
      (1 : Fin 3) = 1 := dsP3_normLap_secondEval_eq_one
  linarith

theorem dsP3_lap_evals_two :
    evals (laplacian_symmetric path3Adj path3Adj_symmetric) (2 : Fin 3) = 3 := by
  have hsum := evals_sum_eq_trace
    (laplacian_symmetric path3Adj path3Adj_symmetric)
  rw [path3_trace] at hsum
  have h2 : ∑ i : Fin 3,
      evals (laplacian_symmetric path3Adj path3Adj_symmetric) i = 4 := hsum
  simp only [Fin.sum_univ_three] at h2
  have h0 : evals (laplacian_symmetric path3Adj path3Adj_symmetric)
      (0 : Fin 3) = 0 := path3_evals_zero_QA
  have h1 : evals (laplacian_symmetric path3Adj path3Adj_symmetric)
      (1 : Fin 3) = 1 := path3_lambda2_eq_one_QA
  linarith

/-! ## The sandwich instances on `P₃` -/

/-- The upper side instantiated at the true degree floor `dmin = 1`. -/
theorem dsP3_upper_instance_QA :
    secondEval (normalizedLaplacian path3Adj)
        (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
        (by norm_num)
      ≤ lambda2 path3Adj path3Adj_symmetric (by norm_num) / (1 : ℝ) :=
  secondEval_normalizedLaplacian_le_div path3Adj path3Adj_symmetric
    path3Adj_nonneg dsP3_pos_deg 1 dsP3_degMin one_pos (by norm_num)

/-- **The upper side is attained at equality on `P₃`:**
`λ₂(L_sym) = 1 = λ₂(L)/dmin` — a wrong constant on the `dmin` side of
the engine breaks exactly this equality. -/
theorem dsP3_upper_tight_QA :
    secondEval (normalizedLaplacian path3Adj)
        (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
        (by norm_num)
      = lambda2 path3Adj path3Adj_symmetric (by norm_num) / (1 : ℝ) := by
  rw [dsP3_normLap_secondEval_eq_one, path3_lambda2_eq_one_QA]
  norm_num

/-- **The wrong-constant pairing fence:** the upper side with `dmax`
in place of `dmin` is refuted on `P₃` — `1 ≤ 1/2` is false, so the
`dmin`/`dmax` pairing cannot be swapped. -/
theorem dsP3_wrongConstant_refuted_QA :
    ¬ (secondEval (normalizedLaplacian path3Adj)
        (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
        (by norm_num)
      ≤ lambda2 path3Adj path3Adj_symmetric (by norm_num) / (2 : ℝ)) := by
  rw [dsP3_normLap_secondEval_eq_one, path3_lambda2_eq_one_QA]
  norm_num

/-- The lower side instantiated at the true degree ceiling `dmax = 2`
(joined values: `1/2 ≤ 1` — slack, the bracket's honest width). -/
theorem dsP3_lower_instance_QA :
    lambda2 path3Adj path3Adj_symmetric (by norm_num) / (2 : ℝ)
      ≤ secondEval (normalizedLaplacian path3Adj)
          (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
          (by norm_num) :=
  div_le_secondEval_normalizedLaplacian path3Adj path3Adj_symmetric
    path3Adj_nonneg dsP3_pos_deg 2 dsP3_degMax (by norm_num)

/-- The engine at a non-second index: `k = 2` on `P₃`, joined to the
trace-route pins (`3/2 ≤ 2`). -/
theorem dsP3_engine_k2_QA :
    evals (laplacian_symmetric path3Adj path3Adj_symmetric) (2 : Fin 3) / (2 : ℝ)
      ≤ evals (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
          (2 : Fin 3) :=
  div_le_evals_normalizedLaplacian path3Adj path3Adj_symmetric
    path3Adj_nonneg dsP3_pos_deg 2 dsP3_degMax (2 : Fin 3)

theorem dsP3_engine_k2_values_QA :
    evals (laplacian_symmetric path3Adj path3Adj_symmetric) (2 : Fin 3) = 3
      ∧ evals (normalizedLaplacian_symmetric path3Adj path3Adj_symmetric)
          (2 : Fin 3) = 2 :=
  ⟨dsP3_lap_evals_two, dsP3_normLap_evals_two⟩

/-! ## The `K₂` regular squeeze -/

theorem dsK2_degMin (i : Fin 2) : (1 : ℝ) ≤ deg cheegerEdgeAdj i := by
  rw [cheegerEdgeAdj_regular i]

theorem dsK2_degMax (i : Fin 2) : deg cheegerEdgeAdj i ≤ (1 : ℝ) := by
  rw [cheegerEdgeAdj_regular i]

/-- The combinatorial `λ₂ (K₂) = 2`, kernel-plus-trace route (both
degrees `1`). -/
theorem dsK2_lambda2_eq_two :
    lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2) = 2 := by
  have h0 : evals (laplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric) (0 : Fin 2)
      = 0 :=
    laplacian_evals_zero cheegerEdgeAdj cheegerEdgeAdj_symmetric cheegerEdgeAdj_nonneg
      (by norm_num)
  have hsum := evals_sum_eq_trace
    (laplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
  have htrace : (laplacian cheegerEdgeAdj).trace = 2 := by
    have hdiag : ∀ i : Fin 2, (laplacian cheegerEdgeAdj) i i = 1 := by
      intro i
      rw [laplacian, Matrix.sub_apply, degreeMatrix_diagonal,
        cheegerEdgeAdj_regular i]
      simp [cheegerEdgeAdj]
    rw [show (laplacian cheegerEdgeAdj).trace = ∑ i, (laplacian cheegerEdgeAdj) i i from rfl,
      Finset.sum_congr rfl fun i _ => hdiag i]
    simp [Fin.sum_univ_two]
  rw [htrace] at hsum
  have h2 : ∑ i : Fin 2,
      evals (laplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric) i = 2 := hsum
  simp only [Fin.sum_univ_two] at h2
  have h1 : lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2)
      = evals (laplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric) (1 : Fin 2) := rfl
  linarith

/-- **The regular squeeze, lower side:** on the `1`-regular `K₂` the
bracket collapses to `2 ≤ 2` — attained. -/
theorem dsK2_squeeze_lower_QA :
    lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2) / (1 : ℝ)
      ≤ secondEval (normalizedLaplacian cheegerEdgeAdj)
          (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          (le_refl 2) :=
  div_le_secondEval_normalizedLaplacian cheegerEdgeAdj cheegerEdgeAdj_symmetric
    cheegerEdgeAdj_nonneg (fun i => by rw [cheegerEdgeAdj_regular i]; norm_num) 1 dsK2_degMax
    (le_refl 2)

theorem dsK2_squeeze_lower_tight_QA :
    lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2) / (1 : ℝ)
      = secondEval (normalizedLaplacian cheegerEdgeAdj)
          (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
          (le_refl 2) := by
  rw [dsK2_lambda2_eq_two, icEdge_normLap_secondEval]
  norm_num

/-- **The regular squeeze, upper side:** `2 ≤ 2` — attained. -/
theorem dsK2_squeeze_upper_QA :
    secondEval (normalizedLaplacian cheegerEdgeAdj)
        (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        (le_refl 2)
      ≤ lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2) / (1 : ℝ) :=
  secondEval_normalizedLaplacian_le_div cheegerEdgeAdj cheegerEdgeAdj_symmetric
    cheegerEdgeAdj_nonneg (fun i => by rw [cheegerEdgeAdj_regular i]; norm_num) 1 dsK2_degMin
    one_pos (le_refl 2)

theorem dsK2_squeeze_upper_tight_QA :
    secondEval (normalizedLaplacian cheegerEdgeAdj)
        (normalizedLaplacian_symmetric cheegerEdgeAdj cheegerEdgeAdj_symmetric)
        (le_refl 2)
      = lambda2 cheegerEdgeAdj cheegerEdgeAdj_symmetric (le_refl 2) / (1 : ℝ) := by
  rw [dsK2_lambda2_eq_two, icEdge_normLap_secondEval]
  norm_num

/-! ## The `dmin = 0` fence: the isolated vertex -/

/-- The `K₂ ⊕ isolated vertex` fixture: degrees `(1, 1, 0)` — the
single edge `0`–`1` plus an isolated third vertex. -/
def dsIsoAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if ((i : ℕ) = 0 ∧ (j : ℕ) = 1) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 0) then 1 else 0

theorem dsIsoAdj_symmetric : dsIsoAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp (config := {decide := true}) [Matrix.transpose_apply, dsIsoAdj]

theorem dsIsoAdj_nonneg (i j : Fin 3) : 0 ≤ dsIsoAdj i j := by
  by_cases h : ((i : ℕ) = 0 ∧ (j : ℕ) = 1) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 0)
  · simp [dsIsoAdj, h]
  · simp [dsIsoAdj, h]

theorem dsIsoAdj_deg (i : Fin 3) :
    deg dsIsoAdj i = if (i : ℕ) = 0 ∨ (i : ℕ) = 1 then 1 else 0 := by
  fin_cases i <;>
    simp only [deg, Fin.sum_univ_three, Matrix.of_apply, dsIsoAdj] <;>
    norm_num

theorem dsIsoAdj_degMin_zero (i : Fin 3) : (0 : ℝ) ≤ deg dsIsoAdj i := by
  rw [dsIsoAdj_deg i]
  by_cases h : (i : ℕ) = 0 ∨ (i : ℕ) = 1 <;> simp [h]

/-- The normalized Laplacian of the fixture, entrywise: the isolated
vertex contributes `D^{-1/2}`-junk zeroes, leaving the `K₂` block and
a unit diagonal entry. -/
theorem dsIsoAdj_normLap_eq (i j : Fin 3) :
    normalizedLaplacian dsIsoAdj i j
      = if (i : ℕ) = 0 ∧ (j : ℕ) = 1 ∨ (i : ℕ) = 1 ∧ (j : ℕ) = 0 then
          (if (i : ℕ) = (j : ℕ) then 0 else -1)
        else if (i : ℕ) = (j : ℕ) then 1 else 0 := by
  have hentry : ∀ i j : Fin 3,
      normalizedLaplacian dsIsoAdj i j
        = (if i = j then (1 : ℝ) else 0)
          - (Real.sqrt (deg dsIsoAdj i))⁻¹ * dsIsoAdj i j
            * (Real.sqrt (deg dsIsoAdj j))⁻¹ := by
    intro i j
    simp only [normalizedLaplacian, Matrix.sub_apply, Matrix.one_apply,
      Matrix.diagonal_mul, Matrix.mul_diagonal, degreeInvSqrt,
      Matrix.diagonal_apply]
  have hsq : ∀ i : Fin 3, Real.sqrt (deg dsIsoAdj i)
      = if (i : ℕ) = 0 ∨ (i : ℕ) = 1 then 1 else 0 := by
    intro i
    rw [dsIsoAdj_deg i]
    by_cases h : (i : ℕ) = 0 ∨ (i : ℕ) = 1 <;> simp [h]
  rw [hentry i j, hsq i, hsq j]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, dsIsoAdj, Real.sqrt_one] <;>
    simp (config := {decide := true})

/-- The raw quadratic form of the fixture's normalized Laplacian. -/
theorem dsIsoAdj_normLap_quadForm (x : Fin 3 → ℝ) :
    quadForm (normalizedLaplacian dsIsoAdj) x
      = ((x 0) - (x 1)) ^ 2 + (x 2) ^ 2 := by
  have hrow : ∀ x : Fin 3 → ℝ,
      (normalizedLaplacian dsIsoAdj *ᵥ x) 0 = (x 0) - (x 1)
      ∧ (normalizedLaplacian dsIsoAdj *ᵥ x) 1 = (x 1) - (x 0)
      ∧ (normalizedLaplacian dsIsoAdj *ᵥ x) 2 = (x 2) := by
    intro x
    refine ⟨?_, ?_, ?_⟩ <;>
      simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
        dsIsoAdj_normLap_eq] <;>
      simp (config := {decide := true }) <;> ring
  simp only [quadForm, Matrix.dotProduct, Fin.sum_univ_three]
  obtain ⟨r0, r1, r2⟩ := hrow x
  rw [r0, r1, r2]
  ring

theorem dsIsoAdj_kernelVec :
    degreeSqrt dsIsoAdj *ᵥ (onesVec : Fin 3 → ℝ) = ![1, 1, 0] := by
  funext i
  fin_cases i <;>
    simp [degreeSqrt_mulVec, dsIsoAdj_deg, Matrix.mulVec_diagonal,
      Real.sqrt_one, onesVec]

/-- **`λ₂ (L_sym) = 1` on the fixture**, both sides by raw
computation: the `≤` side at the isolated vertex's unit vector (the
`(2,2)` entry is `1`), the `≥` side by the constraint algebra (every
vector orthogonal to the kernel vector `(1, 1, 0)` has
`q = (x 0 - x 1)² + x 2² ≥ ‖x‖²` because `x 1 = -x 0`). -/
theorem dsIsoAdj_normLap_secondEval_eq_one :
    secondEval (normalizedLaplacian dsIsoAdj)
        (normalizedLaplacian_symmetric dsIsoAdj dsIsoAdj_symmetric)
        (by norm_num) = 1 := by
  have hposdeg : ∀ i, 0 ≤ deg dsIsoAdj i := dsIsoAdj_degMin_zero
  have hpsd : ∀ x : Fin 3 → ℝ, 0 ≤ quadForm (normalizedLaplacian dsIsoAdj) x :=
    fun x => by
      rw [dsIsoAdj_normLap_quadForm]
      exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hwne : degreeSqrt dsIsoAdj *ᵥ (onesVec : Fin 3 → ℝ) ≠ 0 := by
    rw [dsIsoAdj_kernelVec]
    intro h
    have h1 := congrFun h 0
    simp at h1
  have hker : normalizedLaplacian dsIsoAdj *ᵥ
      (degreeSqrt dsIsoAdj *ᵥ (onesVec : Fin 3 → ℝ)) = 0 := by
    rw [dsIsoAdj_kernelVec]
    funext i
    fin_cases i <;>
      simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_three,
        dsIsoAdj_normLap_eq] <;>
      simp (config := {decide := true})
  -- ≤ 1 at the isolated vertex's unit vector
  have hle : secondEval (normalizedLaplacian dsIsoAdj)
      (normalizedLaplacian_symmetric dsIsoAdj dsIsoAdj_symmetric)
      (by norm_num) ≤ 1 := by
    have hw : (![0, 0, 1] : Fin 3 → ℝ) ≠ 0 := by
      intro h
      have h2 := congrFun h 2
      simp at h2
    have horth : Matrix.dotProduct (![0, 0, 1] : Fin 3 → ℝ)
        (degreeSqrt dsIsoAdj *ᵥ (onesVec : Fin 3 → ℝ)) = 0 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_three, dsIsoAdj_kernelVec,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        onesVec]
      norm_num
    have hmain := secondEval_le_rayleigh_of_ker
      (normalizedLaplacian_symmetric dsIsoAdj dsIsoAdj_symmetric)
      hpsd hwne hker (by norm_num) hw horth
    have hq : quadForm (normalizedLaplacian dsIsoAdj)
        (![0, 0, 1] : Fin 3 → ℝ) = 1 := by
      rw [dsIsoAdj_normLap_quadForm]
      norm_num
    have hdot : Matrix.dotProduct (![0, 0, 1] : Fin 3 → ℝ)
        (![0, 0, 1] : Fin 3 → ℝ) = 1 := by
      simp only [Matrix.dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      norm_num
    rw [rayleigh, if_neg hw, hq, hdot] at hmain
    norm_num at hmain
    exact hmain
  -- ≥ 1 by the constraint algebra
  have hge : 1 ≤ secondEval (normalizedLaplacian dsIsoAdj)
      (normalizedLaplacian_symmetric dsIsoAdj dsIsoAdj_symmetric)
      (by norm_num) := by
    rw [secondEval_variational_of_ker
      (normalizedLaplacian_symmetric dsIsoAdj dsIsoAdj_symmetric)
      hpsd hwne hker (by norm_num)]
    refine le_csInf ?_ ?_
    · refine ⟨rayleigh (normalizedLaplacian dsIsoAdj) ![0, 0, 1],
        ![0, 0, 1], by
          intro h
          have h2 := congrFun h 2
          simp at h2, ?_, rfl⟩
      simp only [Matrix.dotProduct, Fin.sum_univ_three,
        dsIsoAdj_kernelVec, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, onesVec]
      norm_num
    · rintro r ⟨x, hx0, hxorth, rfl⟩
      have hcon : (x 0) + (x 1) = 0 := by
        simpa [Matrix.dotProduct, Fin.sum_univ_three, dsIsoAdj_kernelVec,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          onesVec] using hxorth
      have hs : Matrix.dotProduct x x = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
        simp [Matrix.dotProduct, Fin.sum_univ_three]
        ring
      have hq := dsIsoAdj_normLap_quadForm x
      have hdot : 0 < Matrix.dotProduct x x := dotProduct_self_pos hx0
      have hsumpos : 0 < (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
        rw [← hs]; exact hdot
      rw [rayleigh, if_neg hx0, hq, hs, one_le_div hsumpos]
      nlinarith [sq_nonneg ((x 0) + (x 1)), sq_nonneg (x 2),
        sq_nonneg (x 0), sq_nonneg (x 1)]
  exact le_antisymm hle hge

/-- **The `0 < dmin` guard is load-bearing:** at `dmin = 0` — which
still satisfies the degree-floor hypothesis `∀ i, 0 ≤ deg` on this
fixture — the upper side's statement would read `λ₂(L_sym) ≤
lambda2 / 0`, and `lambda2 / 0 = 0` while `λ₂(L_sym) = 1`: refuted.
(The engine's own positive-degree hypothesis excludes the fixture;
this fence exhibits the failure mode that guard fences.) -/
theorem dsIsoAdj_upper_dmin_zero_refuted_QA :
    ¬ (secondEval (normalizedLaplacian dsIsoAdj)
        (normalizedLaplacian_symmetric dsIsoAdj dsIsoAdj_symmetric)
        (by norm_num)
      ≤ lambda2 dsIsoAdj dsIsoAdj_symmetric (by norm_num) / (0 : ℝ)) := by
  intro h
  rw [dsIsoAdj_normLap_secondEval_eq_one, div_zero] at h
  exact absurd h (by norm_num)

end SpectralGraphTheory.QA
