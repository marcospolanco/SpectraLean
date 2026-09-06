/-
  PrimitiveConvergence_QA.lean

  Purpose
  -------
  Adversarial fence audit for `Scaffold.Mathlib.LinearAlgebra.
  PrimitiveConvergence` — the direct-import-coverage consumption
  survey's pick (2026-09-05,
  `proposals/adversarial-fences-primitive-convergence-family.md`):
  the primitive-mixing convergence engine of the directed axis (4
  transitive non-QA consumers: `Mixing`, `Oversmoothing`,
  `DirectedMixing`, the `EmpiricalStationary` capstone), 802 lines
  and ~24 theorems with zero prior fence coverage anywhere. Three
  `Fin 2` fixtures: the docstring's own directed 2-cycle (nonnegative,
  row-stochastic, irreducible, NOT primitive — its oscillation is the
  non-convergence breaker for the convergence trio), the signed
  row-stochastic matrix (`hnn` breaker with `hrow` genuine), and the
  non-stochastic nonneg diagonal (`hrow` breaker with `hnn` genuine).

  The π-clause deferral closure (2026-09-05, same day, the proposal's
  deferral-closure record) added the `PiClauseFences` section: the
  convergence trio's stationarity/mass clauses fenced at the
  strictly-positive fixture through the explicit power decomposition,
  with the signed-π clause classified entangled through the
  stationary-space pin. The remainder closure (2026-09-06) added the
  `CancellationFences` section: the signed-cancellation walk quartet
  plus the positive-clause tail, with the convergence trio's own
  `hnn`/`hrow` clauses classified in the proposal (truth-removable
  through Perron; no admissible fixture).

  All proofs are real Lean proofs (no `sorry`/`admit`). QA does not
  prove the remaining axioms; it checks interfaces and degenerate
  cases.

  Scoreboard: ../docs/5_QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.LinearAlgebra.PrimitiveConvergence
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.SpecificLimits.Basic

open Scaffold.LinearAlgebra
open scoped Matrix Topology

namespace Scaffold.LinearAlgebra.QA

section PrimitiveConvergenceFences

/-!
## The primitive-convergence family's adversarial fence audit

The direct-import-coverage survey's pick (2026-09-05): this shelf at 4
transitive non-QA consumers (`Mixing`, `Oversmoothing`,
`DirectedMixing`, the `EmpiricalStationary` capstone) with zero fence
coverage anywhere. Three `Fin 2` fixtures: the docstring's own directed
2-cycle (nonnegative, row-stochastic, irreducible, NOT primitive — its
oscillation is the non-convergence breaker for the convergence trio),
the signed row-stochastic matrix (`hnn` breaker), and the
non-stochastic nonneg diagonal (`hrow` breaker).
-/

/-- The directed 2-cycle: the docstring's own example of an irreducible
but non-primitive row-stochastic matrix. -/
def pcvCycle : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

/-- The signed row-stochastic matrix: `hnn` breaker with `hrow`
genuine. -/
def pcvSigned : Matrix (Fin 2) (Fin 2) ℝ := !![2, -1; -1, 2]

/-- The non-stochastic nonneg diagonal: `hrow` breaker with `hnn`
genuine. -/
def pcvDiag : Matrix (Fin 2) (Fin 2) ℝ := !![2, 0; 0, 0]

theorem pcvCycle_sq : pcvCycle * pcvCycle = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, pcvCycle, Fin.sum_univ_two]

theorem pcvCycle_pow_even (n : ℕ) : pcvCycle ^ (2 * n) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add, ih,
      show pcvCycle ^ 2 = 1 from by rw [pow_two]; exact pcvCycle_sq]
    simp

theorem pcvCycle_pow_odd (n : ℕ) : pcvCycle ^ (2 * n + 1) = pcvCycle := by
  rw [pow_add, pcvCycle_pow_even, pow_one]
  simp

theorem pcvCycle_nonneg : ∀ i j, 0 ≤ pcvCycle i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pcvCycle]

theorem pcvCycle_row : ∀ i, ∑ j, pcvCycle i j = 1 := by
  intro i
  fin_cases i <;> simp [pcvCycle, Fin.sum_univ_two]

theorem pcvSigned_row : ∀ i, ∑ j, pcvSigned i j = 1 := by
  intro i
  fin_cases i <;> norm_num [pcvSigned, Fin.sum_univ_two]

theorem pcvDiag_nonneg : ∀ i j, 0 ≤ pcvDiag i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pcvDiag]

theorem pcvSigned_mulVec : pcvSigned *ᵥ (![1, -1] : Fin 2 → ℝ) = ![3, -3] := by
  funext k
  fin_cases k <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, pcvSigned, Fin.sum_univ_two]

theorem pcvDiag_mulVec : pcvDiag *ᵥ (![1, 0] : Fin 2 → ℝ) = ![2, 0] := by
  funext k
  fin_cases k <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, pcvDiag, Fin.sum_univ_two]

theorem pcvCycle_mulVec : pcvCycle *ᵥ (![1, 0] : Fin 2 → ℝ) = ![0, 1] := by
  funext k
  fin_cases k <;>
    norm_num [Matrix.mulVec, Matrix.dotProduct, pcvCycle, Fin.sum_univ_two]

theorem pcv_entrySup_eq (y : Fin 2 → ℝ) : entrySup y = max (y 0) (y 1) := by
  refine le_antisymm ?_ ?_
  · refine (Finset.sup'_le_iff Finset.univ_nonempty (fun i => y i)).mpr ?_
    intro i _
    fin_cases i <;> simp
  · rcases le_total (y 0) (y 1) with h | h
    · rw [max_eq_right h]; exact Finset.le_sup' _ (Finset.mem_univ 1)
    · rw [max_eq_left h]; exact Finset.le_sup' _ (Finset.mem_univ 0)

theorem pcv_entryInf_eq (y : Fin 2 → ℝ) : entryInf y = min (y 0) (y 1) := by
  refine le_antisymm ?_ ?_
  · rcases le_total (y 0) (y 1) with h | h
    · rw [min_eq_left h]; exact Finset.inf'_le _ (Finset.mem_univ 0)
    · rw [min_eq_right h]; exact Finset.inf'_le _ (Finset.mem_univ 1)
  · refine (Finset.le_inf'_iff Finset.univ_nonempty (fun i => y i)).mpr ?_
    intro i _
    fin_cases i <;> simp

/-- The cycle is not primitive: every even power is the identity
(off-diagonal zeros), every odd power the swap (diagonal zeros). -/
theorem pcvCycle_not_primitive : ¬ pcvCycle.IsPrimitive := by
  rintro ⟨k, hk0, hpos⟩
  rcases Nat.even_or_odd k with ⟨n, rfl⟩ | ⟨n, hn⟩
  · have h01 := hpos 0 1
    have h01 := hpos 0 1
    rw [show n + n = 2 * n from by ring, pcvCycle_pow_even] at h01
    simp [Matrix.one_apply] at h01
  · have h00 := hpos 0 0
    rw [hn, pcvCycle_pow_odd] at h00
    simp [pcvCycle] at h00


/-- The uniform stationary distribution of the cycle (every kept
stationarity clause of the convergence fences is genuine at it). -/
noncomputable def pcvHalf : Fin 2 → ℝ := ![1 / 2, 1 / 2]

theorem pcvHalf_nonneg : ∀ i, 0 ≤ pcvHalf i := by
  intro i; fin_cases i <;> simp [pcvHalf]

theorem pcvHalf_sum : ∑ i, pcvHalf i = 1 := by
  norm_num [pcvHalf, Fin.sum_univ_two]

theorem pcvHalf_stationary : pcvHalf ᵥ* pcvCycle = pcvHalf := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, pcvHalf, pcvCycle,
      Fin.sum_univ_two]

theorem pcv_vecMul_e0_cycle : (![1, 0] : Fin 2 → ℝ) ᵥ* pcvCycle = ![0, 1] := by
  funext j
  fin_cases j <;>
    norm_num [Matrix.vecMul, Matrix.dotProduct, pcvCycle, Fin.sum_univ_two]

theorem pcv_tendsto_double : Filter.Tendsto (fun n : ℕ => 2 * n) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun _ hx => by omega⟩

theorem pcv_tendsto_odd : Filter.Tendsto (fun n : ℕ => 2 * n + 1) Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_atTop.mpr fun b => ⟨b + 1, fun _ hx => by omega⟩

/-- The oscillation engine: the `(0,0)` entry of the cycle's powers
alternates `1, 0, 1, 0…`, so it converges to nothing. -/
theorem pcv_entry_no_limit (c : ℝ) :
    ¬ Filter.Tendsto (fun t : ℕ => (pcvCycle ^ t) 0 0) Filter.atTop (𝓝 c) := by
  intro h
  have hEven : Filter.Tendsto (fun n : ℕ => (pcvCycle ^ (2 * n)) 0 0)
      Filter.atTop (𝓝 c) := h.comp pcv_tendsto_double
  have hOdd : Filter.Tendsto (fun n : ℕ => (pcvCycle ^ (2 * n + 1)) 0 0)
      Filter.atTop (𝓝 c) := h.comp pcv_tendsto_odd
  have hEqE : (fun n : ℕ => (pcvCycle ^ (2 * n)) 0 0) = fun _ => (1 : ℝ) := by
    funext n
    rw [pcvCycle_pow_even]
    simp
  have hEqO : (fun n : ℕ => (pcvCycle ^ (2 * n + 1)) 0 0) = fun _ => (0 : ℝ) := by
    funext n
    rw [pcvCycle_pow_odd]
    simp [pcvCycle]
  rw [hEqE] at hEven
  rw [hEqO] at hOdd
  have h1 : c = 1 := tendsto_nhds_unique hEven tendsto_const_nhds
  have h0 : c = 0 := tendsto_nhds_unique hOdd tendsto_const_nhds
  rw [h0] at h1
  norm_num at h1

theorem pcv_vec_no_limit (c : Fin 2 → ℝ) :
    ¬ Filter.Tendsto (fun t : ℕ => pcvCycle ^ t *ᵥ (![1, 0] : Fin 2 → ℝ))
      Filter.atTop (𝓝 c) := by
  intro h
  have hcomp : Filter.Tendsto (fun t : ℕ => (pcvCycle ^ t *ᵥ (![1, 0] : Fin 2 → ℝ)) 0)
      Filter.atTop (𝓝 (c 0)) :=
    ((continuous_apply (0 : Fin 2)).tendsto c).comp h
  have hEq : (fun t : ℕ => (pcvCycle ^ t *ᵥ (![1, 0] : Fin 2 → ℝ)) 0)
      = fun t : ℕ => (pcvCycle ^ t) 0 0 := by
    funext t
    simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
    ring
  rw [hEq] at hcomp
  exact pcv_entry_no_limit _ hcomp

theorem pcv_vecMul_no_limit (c : Fin 2 → ℝ) :
    ¬ Filter.Tendsto (fun t : ℕ => (![1, 0] : Fin 2 → ℝ) ᵥ* pcvCycle ^ t)
      Filter.atTop (𝓝 c) := by
  intro h
  have hcomp : Filter.Tendsto
      (fun t : ℕ => ((![1, 0] : Fin 2 → ℝ) ᵥ* pcvCycle ^ t) 0) Filter.atTop (𝓝 (c 0)) :=
    ((continuous_apply (0 : Fin 2)).tendsto c).comp h
  have hEq : (fun t : ℕ => ((![1, 0] : Fin 2 → ℝ) ᵥ* pcvCycle ^ t) 0)
      = fun t : ℕ => (pcvCycle ^ t) 0 0 := by
    funext t
    simp only [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one, smul_eq_mul]
    ring
  rw [hEq] at hcomp
  exact pcv_entry_no_limit _ hcomp

theorem pcvDiag_reach_zero (b : Fin 2) :
    Relation.ReflTransGen (fun a b => 0 < pcvDiag a b) 0 b → b = 0 := by
  intro h
  induction h with
  | refl => rfl
  | @tail b c _ hstep ih =>
    have hb : b = 0 := ih
    rw [hb] at hstep
    fin_cases c
    · rfl
    · simp [pcvDiag] at hstep

/-- **Fence: `pow_mulVec_one`'s `hrow`.** At the non-stochastic nonneg
diagonal with `t = 1`: `diag(2,0) *ᵥ 1 = ![2,0] ≠ 1`. -/
theorem pcvFence_pow_mulVec_row
    (h : (pcvDiag ^ (1 : ℕ)) *ᵥ (1 : Fin 2 → ℝ) = (1 : Fin 2 → ℝ)) : False := by
  have h1 := congrFun h 1
  rw [pow_one] at h1
  norm_num [Matrix.mulVec, Matrix.dotProduct, pcvDiag, Fin.sum_univ_two] at h1

/-- **Fence: `mulVec_le_entrySup`'s `hnn`.** At the signed
row-stochastic matrix: `M *ᵥ (1,-1) = (3,-3)` escapes `entrySup`. -/
theorem pcvFence_le_entrySup_nn
    (h : (pcvSigned *ᵥ (![1, -1] : Fin 2 → ℝ)) 0 ≤ entrySup (![1, -1] : Fin 2 → ℝ)) :
    False := by
  rw [pcvSigned_mulVec, pcv_entrySup_eq] at h
  norm_num at h

/-- **Fence: `mulVec_le_entrySup`'s `hrow`.** At the non-stochastic
nonneg diagonal: `diag(2,0) *ᵥ (1,0) = (2,0)` escapes `entrySup (1,0)`. -/
theorem pcvFence_le_entrySup_row
    (h : (pcvDiag *ᵥ (![1, 0] : Fin 2 → ℝ)) 0 ≤ entrySup (![1, 0] : Fin 2 → ℝ)) :
    False := by
  rw [pcvDiag_mulVec, pcv_entrySup_eq] at h
  norm_num at h

/-- **Fence: `entryInf_le_mulVec`'s `hnn`.** -/
theorem pcvFence_entryInf_mulVec_nn
    (h : entryInf (![1, -1] : Fin 2 → ℝ) ≤ (pcvSigned *ᵥ (![1, -1] : Fin 2 → ℝ)) 1) :
    False := by
  rw [pcvSigned_mulVec, pcv_entryInf_eq] at h
  norm_num at h

/-- **Fence: `entryInf_le_mulVec`'s `hrow`.** At the diagonal with
`y = (-1,2)`: `entryInf y = -1` exceeds the image entry `-2`. -/
theorem pcvFence_entryInf_mulVec_row
    (h : entryInf (![-1, 2] : Fin 2 → ℝ) ≤ (pcvDiag *ᵥ (![-1, 2] : Fin 2 → ℝ)) 0) :
    False := by
  rw [pcv_entryInf_eq] at h
  have hp : (pcvDiag *ᵥ (![-1, 2] : Fin 2 → ℝ)) 0 = -2 := by
    norm_num [Matrix.mulVec, Matrix.dotProduct, pcvDiag, Fin.sum_univ_two]
  rw [hp] at h
  norm_num at h

/-- **Fence: `entryInf_le_dotProduct`'s `hwnn`.** The signed weight
`(2,-1)` (mass-one, one negative entry) against `y = (0,1)`. -/
theorem pcvFence_entryInf_dot_nn
    (h : entryInf (![1, 0] : Fin 2 → ℝ)
      ≤ (![2, -1] : Fin 2 → ℝ) ⬝ᵥ (![0, 1] : Fin 2 → ℝ)) : False := by
  rw [pcv_entryInf_eq] at h
  norm_num [Matrix.dotProduct, Fin.sum_univ_two] at h

/-- **Fence: `entryInf_le_dotProduct`'s `hwsum`.** The zero weight
(mass zero, nonnegative) against `y = (1,2)`. -/
theorem pcvFence_entryInf_dot_sum
    (h : entryInf (![1, 2] : Fin 2 → ℝ)
      ≤ (![0, 0] : Fin 2 → ℝ) ⬝ᵥ (![1, 2] : Fin 2 → ℝ)) : False := by
  rw [pcv_entryInf_eq] at h
  norm_num [Matrix.dotProduct, Fin.sum_univ_two] at h

/-- **Fence: `dotProduct_le_entrySup`'s `hwnn`.** -/
theorem pcvFence_dot_entrySup_nn
    (h : (![2, -1] : Fin 2 → ℝ) ⬝ᵥ (![1, 0] : Fin 2 → ℝ)
      ≤ entrySup (![1, 0] : Fin 2 → ℝ)) : False := by
  rw [pcv_entrySup_eq] at h
  norm_num [Matrix.dotProduct, Fin.sum_univ_two] at h

/-- **Fence: `dotProduct_le_entrySup`'s `hwsum`.** The mass-two weight
`(2,0)` against `y = (1,0)`. -/
theorem pcvFence_dot_entrySup_sum
    (h : (![2, 0] : Fin 2 → ℝ) ⬝ᵥ (![1, 0] : Fin 2 → ℝ)
      ≤ entrySup (![1, 0] : Fin 2 → ℝ)) : False := by
  rw [pcv_entrySup_eq] at h
  norm_num [Matrix.dotProduct, Fin.sum_univ_two] at h

/-- **Fence: `entryRange_mulVec_le`'s `hnn`.** The signed action
expands the range `2 → 6`. -/
theorem pcvFence_range_nn
    (h : entryRange (pcvSigned *ᵥ (![1, -1] : Fin 2 → ℝ))
      ≤ entryRange (![1, -1] : Fin 2 → ℝ)) : False := by
  rw [pcvSigned_mulVec] at h
  simp only [entryRange, pcv_entrySup_eq, pcv_entryInf_eq] at h
  norm_num at h

/-- **Fence: `entryRange_mulVec_le`'s `hrow`.** The diagonal doubles
the range `1 → 2` on `y = (1,0)`. -/
theorem pcvFence_range_row
    (h : entryRange (pcvDiag *ᵥ (![1, 0] : Fin 2 → ℝ))
      ≤ entryRange (![1, 0] : Fin 2 → ℝ)) : False := by
  rw [pcvDiag_mulVec] at h
  simp only [entryRange, pcv_entrySup_eq, pcv_entryInf_eq] at h
  norm_num at h

/-- **Fence: `entryRange_mulVec_le_of_pos_entries`'s `hrow`.** At the
diagonal with `δ = 0` (the `hle` clause genuine): the range doubles
against the claimed factor `1`. -/
theorem pcvFence_doeblin_row
    (h : entryRange (pcvDiag *ᵥ (![1, 0] : Fin 2 → ℝ))
      ≤ (1 - (2 : ℝ) * 0) * entryRange (![1, 0] : Fin 2 → ℝ)) : False := by
  rw [pcvDiag_mulVec] at h
  simp only [entryRange, pcv_entrySup_eq, pcv_entryInf_eq] at h
  norm_num at h

/-- **Fence: `entryRange_mulVec_le_of_pos_entries`'s `hle`.** At the
cycle with the inflated `δ = 1`: the claimed factor is `-1` against
the nonnegative range. -/
theorem pcvFence_doeblin_le
    (h : entryRange (pcvCycle *ᵥ (![1, 0] : Fin 2 → ℝ))
      ≤ (1 - (2 : ℝ) * 1) * entryRange (![1, 0] : Fin 2 → ℝ)) : False := by
  rw [pcvCycle_mulVec] at h
  simp only [entryRange, pcv_entrySup_eq, pcv_entryInf_eq] at h
  norm_num at h

/-- **Fence: `pow_nonneg_entries`'s `hnn`.** -/
theorem pcvFence_pow_nn (h : ∀ (t : ℕ) (i j : Fin 2), 0 ≤ (pcvSigned ^ t) i j) : False :=
  absurd (h 1 0 1) (by
    norm_num [pow_one, pcvSigned])

/-- **Fence: `pow_row_sum`'s `hrow`.** -/
theorem pcvFence_pow_row (h : ∀ (t : ℕ) (i : Fin 2), ∑ j, (pcvDiag ^ t) i j = 1) : False :=
  absurd (h 1 0) (by
    norm_num [pow_one, pcvDiag, Fin.sum_univ_two])

/-- **Fence: `vecMul_pow_eq_of_vecMul_eq`'s `h`.** The basis vector is
not stationary for the cycle: `e₀ ᵥ* cycle = e₁`. -/
theorem pcvFence_vecMul (h : (![1, 0] : Fin 2 → ℝ) ᵥ* pcvCycle ^ (1 : ℕ) = (![1, 0] : Fin 2 → ℝ)) :
    False := by
  rw [pow_one, pcv_vecMul_e0_cycle] at h
  have := congrFun h 0
  norm_num at this

/-- **Fence: `exists_pos_le_of_finite`'s `h`.** A function with a zero
member on a one-element index: no positive `δ` bounds it. -/
theorem pcvFence_pos_le (h : ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ (Finset.univ : Finset (Fin 1)),
    δ ≤ (![0] : Fin 1 → ℝ) i) : False := by
  obtain ⟨δ, hδpos, hδle⟩ := h
  have := hδle 0 (Finset.mem_univ 0)
  simp at this
  linarith

/-- **Fence: `entryRange_pow_mul_le`'s `hle`.** The inflated `δ = 1`
at `m = q = 1` on the cycle. -/
theorem pcvFence_pow_range_le
    (h : ∀ y : Fin 2 → ℝ, entryRange ((pcvCycle ^ (1 * 1)) *ᵥ y)
      ≤ (1 - (2 : ℝ) * 1) ^ 1 * entryRange y) : False := by
  have := h (![1, 0] : Fin 2 → ℝ)
  rw [one_mul, pow_one, pcvCycle_mulVec] at this
  simp only [entryRange, pcv_entrySup_eq, pcv_entryInf_eq] at this
  norm_num at this

/-- **Fence: `entryRange_pow_mul_le`'s `hrow`.** The diagonal at
`m = q = 1`, `δ = 0`: the range doubles against the claimed factor
`1`. -/
theorem pcvFence_pow_range_row
    (h : ∀ y : Fin 2 → ℝ, entryRange ((pcvDiag ^ (1 * 1)) *ᵥ y)
      ≤ (1 - (2 : ℝ) * 0) ^ 1 * entryRange y) : False := by
  have := h (![1, 0] : Fin 2 → ℝ)
  rw [one_mul, pow_one, pcvDiag_mulVec] at this
  simp only [entryRange, pcv_entrySup_eq, pcv_entryInf_eq] at this
  norm_num at this

/-- **Fence: `primitive_power_tendsto`'s `hprim`** — the headline. At
the docstring's own directed 2-cycle (nonnegative, row-stochastic,
irreducible, with the genuine stationary `pcvHalf`), the powers
oscillate and converge to nothing. -/
theorem pcvFence_power_tendsto_prim
    (h : Filter.Tendsto (fun t : ℕ => pcvCycle ^ t *ᵥ (![1, 0] : Fin 2 → ℝ))
      Filter.atTop (𝓝 ((pcvHalf ⬝ᵥ (![1, 0] : Fin 2 → ℝ)) • (1 : Fin 2 → ℝ)))) : False :=
  pcv_vec_no_limit _ h

/-- **Fence: `primitive_entrywise_tendsto`'s `hprim`.** The `(0,0)`
entry oscillates `1, 0, 1, 0…`. -/
theorem pcvFence_entrywise_prim
    (h : Filter.Tendsto (fun t : ℕ => (pcvCycle ^ t) 0 0) Filter.atTop (𝓝 (pcvHalf 0))) : False :=
  pcv_entry_no_limit _ h

/-- **Fence: `primitive_vecMul_tendsto`'s `hprim`.** The row action of
the powers on `e₀` oscillates. -/
theorem pcvFence_vecMul_prim
    (h : Filter.Tendsto (fun t : ℕ => (![1, 0] : Fin 2 → ℝ) ᵥ* pcvCycle ^ t)
      Filter.atTop (𝓝 pcvHalf)) : False :=
  pcv_vecMul_no_limit _ h

/-- **Fence: `isPrimitive_of_pos`'s `h`.** The cycle has zero entries,
so strict positivity fails, and primitivity fails with it. -/
theorem pcvFence_of_pos (h : pcvCycle.IsPrimitive) : False :=
  pcvCycle_not_primitive h

/-- **Fence: `isIrreducible_of_isPrimitive`'s `hprim`.** The diagonal
is nonnegative (kept clause genuine) but not irreducible: no positive
step leaves vertex `0`. -/
theorem pcvFence_irr_prim (h : pcvDiag.IsIrreducible) : False := by
  have this := pcvDiag_reach_zero 1 (h 0 1)
  norm_num at this

/-- The kept `hreach` clause is genuine at the cycle. -/
theorem pcvCycle_reach : ∀ u v : Fin 2, ∃ a : ℕ, 0 < (pcvCycle ^ a) u v := by
  intro u v
  rcases eq_or_ne u v with rfl | hne
  · exact ⟨0, by simp⟩
  · exact ⟨1, by
      fin_cases u <;> fin_cases v <;>
        first
        | (exact absurd rfl hne)
        | norm_num [pow_one, pcvCycle]⟩

/-- The kept `htwo` clause is genuine at the cycle. -/
theorem pcvCycle_two : ∀ v : Fin 2, ∃ z : Fin 2, 0 < pcvCycle v z ∧ 0 < pcvCycle z v := by
  intro v
  fin_cases v
  · exact ⟨1, by norm_num [pcvCycle], by norm_num [pcvCycle]⟩
  · exact ⟨0, by norm_num [pcvCycle], by norm_num [pcvCycle]⟩

/-- **Fence: `isPrimitive_of_pow_pos_of_odd_loop`'s `hodd`.** The cycle
is bipartite: no odd power has a positive diagonal, yet every other
clause is genuine and the conclusion (primitivity) fails. -/
theorem pcvFence_odd_loop (h : pcvCycle.IsPrimitive) : False :=
  pcvCycle_not_primitive h

end PrimitiveConvergenceFences

section PiClauseFences

/-!
## The convergence trio's π-clause deferrals, closed

The audit's priced follow-up ("feasible at `π` NOT stationary — the
conclusion's limit is then wrong even where powers converge"): the
strictly-positive fixture `pcvPos` — primitive by `isPrimitive_of_pos`,
symmetric, with the explicit power decomposition
`P ^ t = (1/2 + r_t/2, 1/2 − r_t/2; 1/2 − r_t/2, 1/2 + r_t/2)` where
`r_t = (1/2)^t` (the two-idempotent spectral decomposition evaluated
entrywise) — so the ACTUAL limit of `P ^ t *ᵥ x` is the averaging
vector `![(x₀+x₁)/2, (x₀+x₁)/2]`. The claimed limit `(π ⬝ᵥ x) • 1`
at a non-stationary or wrong-mass `π` differs from it, and
`tendsto_nhds_unique` turns the difference into the kill. The `hπnn`
clause carries an entanglement classification: the fixture's
stationary space is `span (1,1)` by linear algebra
(`pcvPos_stationary_eq`), so no signed mass-one stationary vector
exists there — and in general primitivity forces a strictly positive
one-dimensional stationary space (Perron), so the clause cannot be
broken without breaking `hπstat` or `hπsum` too.
-/

/-- The strictly-positive row-stochastic fixture (doubly stochastic,
symmetric). -/
noncomputable def pcvPos : Matrix (Fin 2) (Fin 2) ℝ := !![3 / 4, 1 / 4; 1 / 4, 3 / 4]

theorem pcvPos_apply (i j : Fin 2) :
    pcvPos i j = if i = j then 3 / 4 else 1 / 4 := by
  fin_cases i <;> fin_cases j <;> simp [pcvPos]

theorem pcvPos_nonneg : ∀ i j, 0 ≤ pcvPos i j := by
  intro i j
  rw [pcvPos_apply]
  by_cases h : i = j <;> simp only [h] <;> norm_num

theorem pcvPos_pos : ∀ i j, 0 < pcvPos i j := by
  intro i j
  rw [pcvPos_apply]
  by_cases h : i = j <;> simp only [h] <;> norm_num

theorem pcvPos_row : ∀ i, ∑ j, pcvPos i j = 1 := by
  intro i
  fin_cases i <;> simp [pcvPos, Fin.sum_univ_two] <;> norm_num

theorem pcvPos_primitive : pcvPos.IsPrimitive :=
  isPrimitive_of_pos pcvPos pcvPos_pos

theorem pcvHalf_stationary_pos : pcvHalf ᵥ* pcvPos = pcvHalf := by
  funext j
  fin_cases j <;>
    simp [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, pcvHalf, pcvPos] <;>
    norm_num

theorem pcv_e0_vecMul_pos : (![1, 0] : Fin 2 → ℝ) ᵥ* pcvPos = ![3 / 4, 1 / 4] := by
  funext j
  fin_cases j <;>
    simp [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, pcvPos]

theorem pcv_ones_vecMul_pos : (![1, 1] : Fin 2 → ℝ) ᵥ* pcvPos = (![1, 1] : Fin 2 → ℝ) := by
  funext j
  fin_cases j <;>
    simp [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, pcvPos] <;> norm_num

theorem pcv_e0_not_stationary : (![1, 0] : Fin 2 → ℝ) ᵥ* pcvPos ≠ (![1, 0] : Fin 2 → ℝ) := by
  intro h
  have h0 := congrFun h 0
  rw [pcv_e0_vecMul_pos] at h0
  norm_num at h0

/-- **The entanglement classification's pin:** every mass-one
stationary vector of the fixture is the uniform one (the stationary
space is `span (1,1)` by two-by-two linear algebra). -/
theorem pcvPos_stationary_eq (π : Fin 2 → ℝ) (h : π ᵥ* pcvPos = π)
    (hsum : ∑ i, π i = 1) : π = pcvHalf := by
  have h1 := congrFun h 0
  simp [Matrix.vecMul, Matrix.dotProduct, Fin.sum_univ_two, pcvPos] at h1
  have h0 : π 0 = π 1 := by linarith
  have hsum2 : π 0 + π 1 = 1 := by simpa [Fin.sum_univ_two] using hsum
  have hhalf : π 0 = 1 / 2 := by linarith
  funext j
  fin_cases j
  · simpa [pcvHalf] using hhalf
  · simpa [pcvHalf, ← h0] using hhalf

/-- **The power decomposition, evaluated entrywise:** the two-idempotent
spectral decomposition `P = A + (1/2)·B` with `A = (1/2)J`,
`B = I − (1/2)J` (both idempotent, cross-products zero) gives
`P ^ t = A + (1/2)^t · B`, here spelled out entrywise. -/
theorem pcvPos_pow (t : ℕ) : pcvPos ^ t =
    !![1 / 2 + ((1 : ℝ) / 2) ^ t / 2, 1 / 2 - ((1 : ℝ) / 2) ^ t / 2;
       1 / 2 - ((1 : ℝ) / 2) ^ t / 2, 1 / 2 + ((1 : ℝ) / 2) ^ t / 2] := by
  induction t with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_zero, Matrix.one_apply] <;> norm_num
  | succ t ih =>
    ext i j
    rw [pow_succ, ih]
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, pcvPos,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] <;>
      field_simp <;> ring

theorem pcv_half_decay : Filter.Tendsto (fun t : ℕ => ((1 : ℝ) / 2) ^ t)
    Filter.atTop (𝓝 0) := by
  have h2 : Filter.Tendsto (fun t : ℕ => (2 : ℝ) ^ t) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hinv : Filter.Tendsto (fun t : ℕ => ((2 : ℝ) ^ t)⁻¹) Filter.atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h2
  have heq : (fun t : ℕ => ((1 : ℝ) / 2) ^ t) = fun t : ℕ => ((2 : ℝ) ^ t)⁻¹ := by
    funext t
    rw [div_pow]
    field_simp
  rw [heq]
  exact hinv

/-- **The actual limit:** `P ^ t *ᵥ x` converges to the averaging
vector. -/
theorem pcvPos_tendsto (x : Fin 2 → ℝ) :
    Filter.Tendsto (fun t : ℕ => pcvPos ^ t *ᵥ x) Filter.atTop
      (𝓝 ![(x 0 + x 1) / 2, (x 0 + x 1) / 2]) := by
  have hEq : (fun t : ℕ => pcvPos ^ t *ᵥ x)
      = fun t : ℕ => ![(x 0 + x 1) / 2 + ((1 : ℝ) / 2) ^ t * ((x 0 - x 1) / 2),
          (x 0 + x 1) / 2 - ((1 : ℝ) / 2) ^ t * ((x 0 - x 1) / 2)] := by
    funext t
    rw [pcvPos_pow]
    funext k
    fin_cases k <;>
      simp only [Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] <;>
      field_simp <;> ring
  rw [hEq, tendsto_pi_nhds]
  intro j
  fin_cases j
  · have hcore : Filter.Tendsto
        (fun t : ℕ => ((1 : ℝ) / 2) ^ t * ((x 0 - x 1) / 2)) Filter.atTop
        (𝓝 (0 * ((x 0 - x 1) / 2))) :=
      pcv_half_decay.mul tendsto_const_nhds
    have hc : Filter.Tendsto (fun _ : ℕ => (x 0 + x 1) / 2) Filter.atTop
        (𝓝 ((x 0 + x 1) / 2)) := tendsto_const_nhds
    simpa only [zero_mul, add_zero] using hc.add hcore
  · have hcore : Filter.Tendsto
        (fun t : ℕ => ((1 : ℝ) / 2) ^ t * ((x 0 - x 1) / 2)) Filter.atTop
        (𝓝 (0 * ((x 0 - x 1) / 2))) :=
      pcv_half_decay.mul tendsto_const_nhds
    have hc : Filter.Tendsto (fun _ : ℕ => (x 0 + x 1) / 2) Filter.atTop
        (𝓝 ((x 0 + x 1) / 2)) := tendsto_const_nhds
    simpa only [zero_mul, sub_zero] using hc.sub hcore

theorem pcvPos_entry_tendsto :
    Filter.Tendsto (fun t : ℕ => (pcvPos ^ t) 0 0) Filter.atTop (𝓝 (1 / 2 : ℝ)) := by
  have hEq : (fun t : ℕ => (pcvPos ^ t) 0 0)
      = fun t : ℕ => 1 / 2 + ((1 : ℝ) / 2) ^ t * (1 / 2) := by
    funext t
    rw [pcvPos_pow]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons]
    try field_simp
    try ring
  rw [hEq]
  have hcore : Filter.Tendsto (fun t : ℕ => ((1 : ℝ) / 2) ^ t * (1 / 2))
      Filter.atTop (𝓝 (0 * (1 / 2 : ℝ))) :=
    pcv_half_decay.mul tendsto_const_nhds
  have hc : Filter.Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) Filter.atTop
      (𝓝 ((1 / 2 : ℝ))) := tendsto_const_nhds
  simpa only [zero_mul, add_zero] using hc.add hcore

theorem pcvPos_pow_symm_apply (t : ℕ) (i j : Fin 2) :
    (pcvPos ^ t) i j = (pcvPos ^ t) j i := by
  have hT : (pcvPos ^ t)ᵀ = pcvPos ^ t := by
    rw [Matrix.transpose_pow]
    congr 1
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.transpose_apply, pcvPos]
  have hflip : (pcvPos ^ t) j i = (pcvPos ^ t)ᵀ i j :=
    (Matrix.transpose_apply (pcvPos ^ t) i j).symm
  rw [hflip, hT]

theorem pcv_e0_vecMul_pow (t : ℕ) :
    (![1, 0] : Fin 2 → ℝ) ᵥ* pcvPos ^ t = pcvPos ^ t *ᵥ (![1, 0] : Fin 2 → ℝ) := by
  funext j
  simp only [Matrix.vecMul, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one, one_mul, mul_one,
    zero_mul, add_zero]
  have hz : (pcvPos ^ t) j 1 * 0 = 0 := by ring
  rw [hz, add_zero]
  exact pcvPos_pow_symm_apply t 0 j

theorem pcv_two_vecMul_pow (t : ℕ) :
    (![2, 0] : Fin 2 → ℝ) ᵥ* pcvPos ^ t = (2 : ℝ) • (pcvPos ^ t *ᵥ (![1, 0] : Fin 2 → ℝ)) := by
  funext j
  simp only [Matrix.vecMul, Matrix.mulVec, Matrix.dotProduct, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one, one_mul, mul_one,
    zero_mul, add_zero, Pi.smul_apply, smul_eq_mul]
  have hz : (pcvPos ^ t) j 1 * 0 = 0 := by ring
  rw [hz, add_zero]
  exact congrArg (fun z => 2 * z) (pcvPos_pow_symm_apply t 0 j)

/-- **Fence: `primitive_power_tendsto`'s `hπstat`.** At the
strictly-positive primitive fixture with the NON-stationary mass-one
`π = e₀`: the powers genuinely converge (to the averaging vector), but
the claimed limit is `(π ⬝ᵥ x) • 1`, which differs — the dropped
stationarity clause is what pins the limit. -/
theorem pcvFence_power_stat
    (h : Filter.Tendsto (fun t : ℕ => pcvPos ^ t *ᵥ (![1, 0] : Fin 2 → ℝ))
      Filter.atTop (𝓝 (((![1, 0] : Fin 2 → ℝ) ⬝ᵥ (![1, 0] : Fin 2 → ℝ)) •
        (1 : Fin 2 → ℝ)))) : False := by
  have hActual := pcvPos_tendsto (![1, 0] : Fin 2 → ℝ)
  have hlim := tendsto_nhds_unique h hActual
  have h0 := congrFun hlim 0
  simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one, one_mul, zero_mul, add_zero,
    Pi.smul_apply, smul_eq_mul, one_smul, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one] at h0
  norm_num at h0

/-- **Fence: `primitive_power_tendsto`'s `hπsum`.** At the stationary
`π = (1,1)` of mass `2`: every other clause genuine, the mass clause
dropped — the claimed limit doubles. -/
theorem pcvFence_power_sum
    (h : Filter.Tendsto (fun t : ℕ => pcvPos ^ t *ᵥ (![1, 0] : Fin 2 → ℝ))
      Filter.atTop (𝓝 (((![1, 1] : Fin 2 → ℝ) ⬝ᵥ (![1, 0] : Fin 2 → ℝ)) •
        (1 : Fin 2 → ℝ)))) : False := by
  have hActual := pcvPos_tendsto (![1, 0] : Fin 2 → ℝ)
  have hlim := tendsto_nhds_unique h hActual
  have h0 := congrFun hlim 0
  simp only [Matrix.dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one, one_mul,
    Pi.smul_apply, smul_eq_mul, one_smul, Matrix.cons_val_zero,
    Matrix.head_cons, Matrix.cons_val_one] at h0
  norm_num at h0

/-- **Fence: `primitive_entrywise_tendsto`'s `hπstat`.** The `(0,0)`
entry genuinely converges (to `1/2`), the claimed limit at the
non-stationary `e₀` is `1`. -/
theorem pcvFence_entrywise_stat
    (h : Filter.Tendsto (fun t : ℕ => (pcvPos ^ t) 0 0) Filter.atTop
      (𝓝 ((![1, 0] : Fin 2 → ℝ) 0))) : False := by
  have hlim := tendsto_nhds_unique h pcvPos_entry_tendsto
  simp only [Matrix.cons_val_zero] at hlim
  norm_num at hlim

/-- **Fence: `primitive_vecMul_tendsto`'s `hπstat`.** -/
theorem pcvFence_vecMul_stat
    (h : Filter.Tendsto (fun t : ℕ => (![1, 0] : Fin 2 → ℝ) ᵥ* pcvPos ^ t)
      Filter.atTop (𝓝 (![1, 0] : Fin 2 → ℝ))) : False := by
  simp only [pcv_e0_vecMul_pow] at h
  have hActual := pcvPos_tendsto (![1, 0] : Fin 2 → ℝ)
  have hlim := tendsto_nhds_unique h hActual
  have h0 := congrFun hlim 0
  simp only [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one] at h0
  norm_num at h0

/-- **Fence: `primitive_vecMul_tendsto`'s `hνsum`.** At the
mass-two `ν = (2,0)` with the genuine stationary `pcvHalf`: the row
action genuinely converges, but to `(1,1)`, not to `π`. -/
theorem pcvFence_vecMul_nusum
    (h : Filter.Tendsto (fun t : ℕ => (![2, 0] : Fin 2 → ℝ) ᵥ* pcvPos ^ t)
      Filter.atTop (𝓝 pcvHalf)) : False := by
  simp only [pcv_two_vecMul_pow] at h
  have hT := pcvPos_tendsto (![1, 0] : Fin 2 → ℝ)
  have hval : ![((![1, 0] : Fin 2 → ℝ) 0 + (![1, 0] : Fin 2 → ℝ) 1) / 2,
      ((![1, 0] : Fin 2 → ℝ) 0 + (![1, 0] : Fin 2 → ℝ) 1) / 2] = ![1 / 2, 1 / 2] := by
    simp [Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  rw [hval] at hT
  have hActual : Filter.Tendsto
      (fun t : ℕ => (2 : ℝ) • (pcvPos ^ t *ᵥ (![1, 0] : Fin 2 → ℝ))) Filter.atTop
      (𝓝 ((2 : ℝ) • ![1 / 2, 1 / 2])) :=
    hT.const_smul (2 : ℝ)
  have hlim := tendsto_nhds_unique h hActual
  have h0 := congrFun hlim 0
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.head_cons,
    pcvHalf] at h0
  norm_num at h0

end PiClauseFences

section CancellationFences

/-!
## The signed-cancellation walk quartet + the positive-clause tail

The audit's remaining priced deferral, closed: positive power-entries
arising through negative-product cancellation — the `hnn` clauses of
the walk layer, fenced at four fixtures designed so the kept clauses
stay genuine — plus the cheap positive-clause fences the original
audit's cull never reached. The convergence trio's own `hnn`/`hrow`
clauses are classified in the proposal (truth-removable through
Perron; no admissible fixture through strict-contraction propagation).
-/

/-- The cancellation fixture for `reachable_of_pow_pos`: the
`(0,1)`-entry of the square is `1·(-2) + (-2)·(-2) = 2 > 0`, pure
negative-product arithmetic, while the only positive single-edge is
the loop `0 → 0`. -/
def pcvCxl : Matrix (Fin 2) (Fin 2) ℝ := !![1, -2; 0, -2]

theorem pcvCxl_sq01 : (pcvCxl ^ 2) 0 1 = 2 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, pcvCxl,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  ring

/-- The kept clause of the `hnn` fence is genuine: the power-entry
positivity hypothesis holds at `(k, i, j) = (2, 0, 1)`. -/
theorem pcvCxl_pow_pos : 0 < (pcvCxl ^ 2) 0 1 := by
  rw [pcvCxl_sq01]
  norm_num

theorem pcvCxl_reach_stays (b : Fin 2) :
    Relation.ReflTransGen (fun a b => 0 < pcvCxl a b) 0 b → b = 0 := by
  intro h
  induction h with
  | refl => rfl
  | @tail b c _ hstep ih =>
    have hb : b = 0 := ih
    rw [hb] at hstep
    fin_cases c
    · rfl
    · exact absurd hstep (by
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons, pcvCxl]
        norm_num)

/-- **Fence: `reachable_of_pow_pos`'s `hnn`.** The conclusion's
reachability fails at `(0, 1)` although the power-entry positivity
hypothesis is genuine: the positivity is pure cancellation, and no
positive step ever leaves vertex `0`. -/
theorem pcvFence_reachable_nn
    (h : Relation.ReflTransGen (fun a b => 0 < pcvCxl a b) 0 1) : False := by
  exact absurd (pcvCxl_reach_stays 1 h) (by decide)

/-- The no-positive-edges fixture for `isIrreducible_of_isPrimitive`:
every off-loop entry is negative, yet the square is strictly positive
— primitivity genuine, irreducibility failing. -/
def pcvAllNeg : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; -1, -1]

set_option linter.unnecessarySeqFocus false in
theorem pcvAllNeg_sq : pcvAllNeg ^ 2 = !![1, 1; 1, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, pcvAllNeg] <;> norm_num

theorem pcvAllNeg_primitive : pcvAllNeg.IsPrimitive := by
  refine ⟨2, by norm_num, ?_⟩
  intro i j
  rw [pcvAllNeg_sq]
  fin_cases i <;> fin_cases j <;> norm_num

theorem pcvAllNeg_reach_eq (i j : Fin 2) :
    Relation.ReflTransGen (fun a b => 0 < pcvAllNeg a b) i j → i = j := by
  intro h
  induction h with
  | refl => rfl
  | @tail b c _ hstep _ =>
    exact absurd hstep (by
      fin_cases b <;> fin_cases c <;>
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
          Matrix.cons_val_fin_one, pcvAllNeg] <;>
        norm_num)

/-- **Fence: `isIrreducible_of_isPrimitive`'s `hnn`.** Primitivity is
genuine (`P²` strictly positive through cancellation), every other
clause genuine, yet irreducibility fails: no positive single-edge
exists at all. -/
theorem pcvFence_irr_nn (h : pcvAllNeg.IsIrreducible) : False := by
  have h01 := pcvAllNeg_reach_eq 0 1 (h 0 1)
  exact absurd h01 (by decide)

/-- The quench fixture for `pow_entry_pos_of_pos`: both kept
power-entry hypotheses genuine (`M 0 0 = 1`, `M 0 1 = 1`), the
conclusion killed by the `-2` diagonal. -/
def pcvQch : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, -2]

theorem pcvQch_h1 : 0 < pcvQch 0 0 := by norm_num [pcvQch]
theorem pcvQch_h2 : 0 < pcvQch 0 1 := by norm_num [pcvQch]

theorem pcvQch_sq01 : (pcvQch ^ 2) 0 1 = -1 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, pcvQch,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  ring

/-- **Fence: `pow_entry_pos_of_pos`'s `hnn`.** -/
theorem pcvFence_pep_nn (h : 0 < (pcvQch ^ (1 + 1)) 0 1) : False := by
  rw [pcvQch_sq01] at h
  norm_num at h

/-- The split fixtures for `pow_entry_pos_of_pos`'s own clauses:
`h1` genuine / `h2` broken, and the mirror. -/
def pcvElo : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
def pcvEhi : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

theorem pcvElo_h2 : 0 < pcvElo 1 0 := by norm_num [pcvElo]
theorem pcvEhi_h1 : 0 < pcvEhi 0 0 := by norm_num [pcvEhi]

theorem pcvElo_sq00 : (pcvElo ^ 2) 0 0 = 0 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, pcvElo,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  ring

theorem pcvEhi_sq01 : (pcvEhi ^ 2) 0 1 = 0 := by
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, pcvEhi,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one]
  ring

/-- **Fence: `pow_entry_pos_of_pos`'s `h1`** (at `i = 0`, `k = 1`,
`j = 0`, `a = b = 1`: the kept `h2` genuine, the dropped `h1` failing
since `M 0 1 = 0`). -/
theorem pcvFence_pep_h1 (h : 0 < (pcvElo ^ (1 + 1)) 0 0) : False := by
  rw [pcvElo_sq00] at h
  norm_num at h

/-- **Fence: `pow_entry_pos_of_pos`'s `h2`** (at `i = 0`, `k = 0`,
`j = 1`: the kept `h1` genuine, the dropped `h2` failing since
`M 0 1 = 0`). -/
theorem pcvFence_pep_h2 (h : 0 < (pcvEhi ^ (1 + 1)) 0 1) : False := by
  rw [pcvEhi_sq01] at h
  norm_num at h

/-- The bounce-cancellation fixture: every kept clause genuine
(`M 0 1 = M 1 2 = M 2 1 = 1`), the `(M³) 0 1`-entry quenched to
`-1` by the `-2` rider. -/
def pcvBnc : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, -2; 0, 0, 1; 0, 1, 1]

theorem pcvBnc_h1 : 0 < pcvBnc 0 1 := by norm_num [pcvBnc]
theorem pcvBnc_hz1 : 0 < pcvBnc 1 2 := by norm_num [pcvBnc]
theorem pcvBnc_hz2 : 0 < pcvBnc 2 1 := by norm_num [pcvBnc]

theorem pcvBnc_cu01 : (pcvBnc ^ 3) 0 1 = -1 := by
  simp only [pow_three, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    pcvBnc, Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one,
    Matrix.cons_val_two]
  norm_num

/-- **Fence: `pow_entry_pos_bounce`'s `hnn`.** -/
theorem pcvFence_bnc_nn (h : 0 < (pcvBnc ^ (1 + 2 * 1)) 0 1) : False := by
  have hEq : (1 + 2 * 1) = 3 := by norm_num
  rw [hEq, pcvBnc_cu01] at h
  norm_num at h

/-- The `hz1`-degenerate bounce fixture: the kept `h1`/`hz2` genuine,
the dropped `hz1` failing (`M 1 2 = 0`), and the cube entry zero. -/
def pcvDgA : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 0; 0, 1, 0]

theorem pcvDgA_h1 : 0 < pcvDgA 0 1 := by norm_num [pcvDgA]
theorem pcvDgA_hz2 : 0 < pcvDgA 2 1 := by norm_num [pcvDgA]

theorem pcvDgA_cu01 : (pcvDgA ^ 3) 0 1 = 0 := by
  simp only [pow_three, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    pcvDgA, Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- **Fence: `pow_entry_pos_bounce`'s `hz1`.** -/
theorem pcvFence_bnc_hz1 (h : 0 < (pcvDgA ^ (1 + 2 * 1)) 0 1) : False := by
  have hEq : (1 + 2 * 1) = 3 := by norm_num
  rw [hEq, pcvDgA_cu01] at h
  norm_num at h

/-- The `hz2`-degenerate bounce fixture. -/
def pcvDgB : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 0, 0, 1; 0, 0, 0]

theorem pcvDgB_h1 : 0 < pcvDgB 0 1 := by norm_num [pcvDgB]
theorem pcvDgB_hz1 : 0 < pcvDgB 1 2 := by norm_num [pcvDgB]

theorem pcvDgB_cu01 : (pcvDgB ^ 3) 0 1 = 0 := by
  simp only [pow_three, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    pcvDgB, Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- **Fence: `pow_entry_pos_bounce`'s `hz2`.** -/
theorem pcvFence_bnc_hz2 (h : 0 < (pcvDgB ^ (1 + 2 * 1)) 0 1) : False := by
  have hEq : (1 + 2 * 1) = 3 := by norm_num
  rw [hEq, pcvDgB_cu01] at h
  norm_num at h

/-- The `h1`-degenerate bounce fixture. -/
def pcvDgC : Matrix (Fin 3) (Fin 3) ℝ := !![0, 0, 0; 0, 0, 1; 0, 1, 0]

theorem pcvDgC_hz1 : 0 < pcvDgC 1 2 := by norm_num [pcvDgC]
theorem pcvDgC_hz2 : 0 < pcvDgC 2 1 := by norm_num [pcvDgC]

theorem pcvDgC_cu01 : (pcvDgC ^ 3) 0 1 = 0 := by
  simp only [pow_three, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
    pcvDgC, Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons,
    Matrix.cons_val_one, Matrix.cons_val_two]
  norm_num

/-- **Fence: `pow_entry_pos_bounce`'s `h1`.** -/
theorem pcvFence_bnc_h1 (h : 0 < (pcvDgC ^ (1 + 2 * 1)) 0 1) : False := by
  have hEq : (1 + 2 * 1) = 3 := by norm_num
  rw [hEq, pcvDgC_cu01] at h
  norm_num at h

/-- The odd-loop supplier's `hreach` fixture: every kept clause genuine
(nonnegative, every vertex in a positive 2-cycle, odd returns
everywhere), yet `(0, 2)` is reachable by no power — nothing but `2`
enters column `2`. -/
def pcvSnk : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, 0; 1, 1, 0; 0, 1, 1]

theorem pcvSnk_nonneg : ∀ i j, 0 ≤ pcvSnk i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [pcvSnk]

theorem pcvSnk_two : ∀ v : Fin 3, ∃ z : Fin 3, 0 < pcvSnk v z ∧ 0 < pcvSnk z v := by
  intro v
  fin_cases v
  · exact ⟨1, by norm_num [pcvSnk], by norm_num [pcvSnk]⟩
  · exact ⟨1, by norm_num [pcvSnk], by norm_num [pcvSnk]⟩
  · exact ⟨2, by norm_num [pcvSnk], by norm_num [pcvSnk]⟩

theorem pcvSnk_odd : ∀ v : Fin 3, ∃ t : ℕ, Odd t ∧ 0 < (pcvSnk ^ t) v v := by
  intro v
  fin_cases v
  · refine ⟨3, by decide, ?_⟩
    simp only [pow_three, pow_two, Matrix.mul_apply, Fin.sum_univ_three,
      pcvSnk, Matrix.of_apply, Matrix.cons_val_zero, Matrix.head_cons,
      Matrix.cons_val_one, Matrix.cons_val_two]
    norm_num
  · exact ⟨1, by norm_num, by norm_num [pow_one, pcvSnk]⟩
  · exact ⟨1, by norm_num, by norm_num [pow_one, pcvSnk]⟩

theorem pcvSnk_pow_02 : ∀ a : ℕ, 1 ≤ a → (pcvSnk ^ a) 0 2 = 0 := by
  intro a
  induction a with
  | zero => omega
  | succ a ih =>
    by_cases ha : a = 0
    · subst ha
      norm_num [pow_one, pcvSnk]
    · have h1a : 1 ≤ a := by omega
      have hstep : (pcvSnk ^ (a + 1)) 0 2
          = ∑ x : Fin 3, (pcvSnk ^ a) 0 x * pcvSnk x 2 := by
        rw [pow_succ]
        simp only [Matrix.mul_apply]
      rw [hstep, Fin.sum_univ_three, ih h1a]
      norm_num [pcvSnk]

theorem pcvSnk_not_primitive : ¬ pcvSnk.IsPrimitive := by
  rintro ⟨k, hk0, hpos⟩
  have h02 := hpos 0 2
  rw [pcvSnk_pow_02 k (Nat.pos_of_ne_zero (by omega : k ≠ 0))] at h02
  norm_num at h02

/-- The dropped `hreach` clause genuinely fails at `(0, 2)`. -/
theorem pcvSnk_not_reach : ¬ ∃ a : ℕ, 0 < (pcvSnk ^ a) 0 2 := by
  rintro ⟨a, ha⟩
  rcases Nat.eq_zero_or_pos a with rfl | hpos
  · simp at ha
  · rw [pcvSnk_pow_02 a hpos] at ha
    norm_num at ha

/-- **Fence: `isPrimitive_of_pow_pos_of_odd_loop`'s `hreach`.** Every
kept clause genuine (`hnn`, `htwo`, `hodd`), the reachability clause
dropped, the primitivity conclusion failing. -/
theorem pcvFence_odd_reach (h : pcvSnk.IsPrimitive) : False :=
  pcvSnk_not_primitive h

end CancellationFences

end Scaffold.LinearAlgebra.QA
