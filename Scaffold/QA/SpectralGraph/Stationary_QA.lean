/-
  Stationary_QA.lean

  Purpose
  -------
  QA lemmas for `Scaffold.Mathlib.GraphTheory.Stationary`: the
  stationary/kernel structure of the walk and normalized Laplacians,
  instantiated at the concrete three-vertex path (degrees 1, 2, 1) and
  with one fully computed entry.

  All proofs are real Lean proofs (no `sorry`/`admit`). These are
  theorems, not axioms; QA checks the interfaces where the arithmetic
  is evaluated.

  Scoreboard: ../QA_SCOREBOARD.md
-/

import Scaffold.Mathlib.GraphTheory.Stationary
import Mathlib.Data.Matrix.Notation

open scoped BigOperators Matrix

namespace SpectralGraphTheory.QA

/-!
## The three-vertex path `0 — 1 — 2` (reused fixture)
-/

/-- Adjacency of the path `0 — 1 — 2` on `Fin 3`: symmetric, unit
weights, degrees (1, 2, 1). -/
def pathAdj : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of !![0, 1, 0; 1, 0, 1; 0, 1, 0]

theorem pathAdj_isSymm : pathAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [pathAdj]

theorem pathAdj_deg_zero : deg pathAdj 0 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_one : deg pathAdj 1 = 2 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_two : deg pathAdj 2 = 1 := by
  simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem pathAdj_deg_pos (i : Fin 3) : 0 < deg pathAdj i := by
  fin_cases i <;>
    simp only [deg, pathAdj, Matrix.of_apply, Fin.sum_univ_three] <;>
    norm_num

/-!
## Kernel and stationarity
-/

/-- The normalized-Laplacian kernel theorem instantiated at the path:
`L_sym *ᵥ √deg = 0` with `√deg = (1, √2, 1)`. -/
theorem path_normalized_kernel_QA :
    normalizedLaplacian pathAdj
      *ᵥ (fun i => Real.sqrt (deg pathAdj i)) = 0 :=
  normalizedLaplacian_mulVec_sqrtDeg_eq_zero pathAdj pathAdj_isSymm
    pathAdj_deg_pos

/-- The stationarity theorem instantiated at the path: the degree
vector `(1, 2, 1)` is stationary for the adjoint walk. -/
theorem path_walk_stationary_QA :
    (walkTransitionMatrix pathAdj)ᵀ *ᵥ (deg pathAdj) = deg pathAdj :=
  walkTransitionMatrix_transpose_mulVec_deg pathAdj pathAdj_isSymm
    pathAdj_deg_pos

/-- One kernel entry fully computed: `(L_sym *ᵥ √deg) 1 = 0` — the
center row contracts `√2` to itself through the two `1/√2` edges. -/
theorem path_normalized_kernel_entry_QA :
    (normalizedLaplacian pathAdj
      *ᵥ (fun i => Real.sqrt (deg pathAdj i))) 1 = 0 := by
  have h := normalizedLaplacian_mulVec_sqrtDeg_eq_zero pathAdj
    pathAdj_isSymm pathAdj_deg_pos
  rw [h]
  rfl

/-- Row sums in vector form instantiated at the path: the walk's
adjoint fixes the degree vector because `A *ᵥ 1 = deg` computes with
row sums `(1, 2, 1)`. -/
theorem path_mulVec_one_eq_deg_QA :
    pathAdj *ᵥ (fun _ => (1 : ℝ)) = deg pathAdj :=
  mulVec_one_eq_deg pathAdj

/-!
## Conservation of mass at both fixtures
-/

/-- Conservation of mass, irregular case: the walk Laplacian of the
path kills the constant vector. -/
theorem path_walkLaplacian_kernel_QA :
    walkLaplacian pathAdj *ᵥ (fun _ => (1 : ℝ)) = 0 :=
  walkLaplacian_mulVec_one_eq_zero pathAdj pathAdj_deg_pos

/-- The adjacency matrix of the single edge on `Fin 2` (symmetric,
1-regular). -/
def edgeAdj2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 1; 1, 0]

theorem edgeAdj2_deg (i : Fin 2) : deg edgeAdj2 i = 1 := by
  fin_cases i <;>
    simp only [deg, edgeAdj2, Matrix.of_apply, Fin.sum_univ_two] <;>
    norm_num

/-- Conservation of mass, regular case: the walk Laplacian of the edge
kills the constant vector — total probability is preserved by each step
of the walk. -/
theorem edge_randomWalkLaplacian_kernel_QA :
    randomWalkLaplacian edgeAdj2 1 *ᵥ (fun _ => (1 : ℝ)) = 0 :=
  randomWalkLaplacian_mulVec_one_eq_zero edgeAdj2 1 edgeAdj2_deg one_pos

/-!
## Reversibility: detailed balance

The proposal's two prescribed witnesses: a positive check on the
irregular path fixture (every balance identity computed through the
theorems *and* by raw literal arithmetic on `P = D⁻¹A` and
`π = deg/vol`), and a negative check on an asymmetric weight matrix
where the hypothesis-free balance statement is refuted and the symmetry
hypothesis is provably violated at the same entry pair.
-/

/-- The path's total volume is `4` (degrees `1 + 2 + 1`), computed
independently of the balance theorems — the stationary measure of the
fixture is `π = (1/4, 1/2, 1/4)`. -/
theorem path_vol_QA :
    vol pathAdj (Finset.univ : Finset (Fin 3)) = 4 := by
  rw [vol, Fin.sum_univ_three, pathAdj_deg_zero, pathAdj_deg_one,
    pathAdj_deg_two]
  norm_num
/-- Detailed balance (degree-measure form) instantiated at every index
pair of the path, through the theorem. -/
theorem path_detailed_balance_QA (i j : Fin 3) :
    deg pathAdj i * walkTransitionMatrix pathAdj i j
      = deg pathAdj j * walkTransitionMatrix pathAdj j i :=
  walk_detailed_balance pathAdj pathAdj_isSymm pathAdj_deg_pos i j

/-- Both balance sides at the pair `(0, 1)` computed by raw literal
arithmetic on the definitions — `deg 0 * P 0 1 = 1 * 1 = 1` and
`deg 1 * P 1 0 = 2 * (1/2) = 1` — agreeing with the common adjacency
entry `A 0 1 = 1`. -/
theorem path_detailed_balance_raw_QA :
    deg pathAdj 0 * walkTransitionMatrix pathAdj 0 1 = 1
      ∧ deg pathAdj 1 * walkTransitionMatrix pathAdj 1 0 = 1 := by
  constructor
  · simp only [walkTransitionMatrix_apply, deg, pathAdj, Matrix.of_apply,
      Fin.sum_univ_three]
    norm_num
  · simp only [walkTransitionMatrix_apply, deg, pathAdj, Matrix.of_apply,
      Fin.sum_univ_three]
    norm_num

/-- Detailed balance in the stationary-measure form instantiated at
every index pair of the path, through the theorem. -/
theorem path_detailed_balance_measure_QA (i j : Fin 3) :
    deg pathAdj i / vol pathAdj (Finset.univ : Finset (Fin 3)) * walkTransitionMatrix pathAdj i j
      = deg pathAdj j / vol pathAdj (Finset.univ : Finset (Fin 3))
          * walkTransitionMatrix pathAdj j i :=
  walk_detailed_balance_measure pathAdj pathAdj_isSymm pathAdj_deg_pos i j

/-- The stationary-measure balance at `(0, 1)` by raw literal
arithmetic: `π 0 * P 0 1 = (1/4) * 1 = 1/4` and
`π 1 * P 1 0 = (1/2) * (1/2) = 1/4` — both equal the common value
`A 0 1 / vol = 1/4`. -/
theorem path_detailed_balance_measure_raw_QA :
    deg pathAdj 0 / vol pathAdj (Finset.univ : Finset (Fin 3))
        * walkTransitionMatrix pathAdj 0 1 = 1 / 4
      ∧ deg pathAdj 1 / vol pathAdj (Finset.univ : Finset (Fin 3))
        * walkTransitionMatrix pathAdj 1 0 = 1 / 4 := by
  rw [path_vol_QA]
  constructor
  · simp only [walkTransitionMatrix_apply, deg, pathAdj, Matrix.of_apply,
      Fin.sum_univ_three]
    norm_num
  · simp only [walkTransitionMatrix_apply, deg, pathAdj, Matrix.of_apply,
      Fin.sum_univ_three]
    norm_num

/-- The matrix packaging instantiated at the path: the degree-weighted
transition matrix `D * P` is symmetric. -/
theorem path_symmetrized_isSymm_QA :
    (Matrix.diagonal (deg pathAdj) * walkTransitionMatrix pathAdj).IsSymm :=
  diagonal_deg_mul_walkTransitionMatrix_isSymm pathAdj pathAdj_isSymm
    pathAdj_deg_pos

/-- The symmetrized matrix's off-diagonal entries computed raw:
`(D * P) 0 1 = deg 0 * P 0 1 = 1` and `(D * P) 1 0 = deg 1 * P 1 0 = 1`
— the two flows `1 → 2` and `2 → 1` carry equal degree-weighted mass,
which is exactly reversibility. -/
theorem path_symmetrized_entries_QA :
    (Matrix.diagonal (deg pathAdj) * walkTransitionMatrix pathAdj) 0 1 = 1
      ∧ (Matrix.diagonal (deg pathAdj) * walkTransitionMatrix pathAdj) 1 0
        = 1 := by
  constructor
  · rw [Matrix.diagonal_mul]
    exact path_detailed_balance_raw_QA.1
  · rw [Matrix.diagonal_mul]
    exact path_detailed_balance_raw_QA.2

/-- The edge's adjacency is symmetric. -/
theorem edgeAdj2_isSymm : edgeAdj2.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [edgeAdj2]

/-- Uniform-measure detailed balance instantiated at the single edge —
the regular-case interface, through the theorem. -/
theorem edge_uniform_balance_QA (i j : Fin 2) :
    ((Fintype.card (Fin 2) : ℝ)⁻¹) * transitionMatrix edgeAdj2 1 i j
      = ((Fintype.card (Fin 2) : ℝ)⁻¹) * transitionMatrix edgeAdj2 1 j i :=
  transitionMatrix_detailed_balance_uniform edgeAdj2 edgeAdj2_isSymm 1 i j

/-!
### The negative witness: asymmetry breaks detailed balance
-/

/-- The asymmetric weight matrix of the directed two-network: edge
`0 → 1` of weight `2`, edge `1 → 0` of weight `1`. Both degrees are
positive (`2` and `1`), so the walk is well-defined — but `A` is not
symmetric, and detailed balance fails. -/
def asymAdj2 : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of !![0, 2; 1, 0]

theorem asymAdj2_deg_zero : deg asymAdj2 0 = 2 := by
  simp only [deg, asymAdj2, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

theorem asymAdj2_deg_one : deg asymAdj2 1 = 1 := by
  simp only [deg, asymAdj2, Matrix.of_apply, Fin.sum_univ_two]
  norm_num

theorem asymAdj2_deg_pos (i : Fin 2) : 0 < deg asymAdj2 i := by
  fin_cases i <;> simp [asymAdj2_deg_zero, asymAdj2_deg_one]

/-- The fixture is provably *not* symmetric at the pair where balance
fails: `A 0 1 = 2 ≠ 1 = A 1 0`. -/
theorem asymAdj2_not_isSymm : ¬ asymAdj2.IsSymm := by
  intro h
  have hne := h.apply 0 1
  simp only [asymAdj2, Matrix.of_apply] at hne
  norm_num at hne

/-- The hypothesis-free detailed balance statement is **refuted** at the
asymmetric fixture: `deg 0 * P 0 1 = 2 * 1 = 2` while
`deg 1 * P 1 0 = 1 * 1 = 1`. The symmetry hypothesis of
`walk_detailed_balance` is load-bearing, not decorative. -/
theorem asym_detailed_balance_refuted_QA :
    ¬ (deg asymAdj2 0 * walkTransitionMatrix asymAdj2 0 1
        = deg asymAdj2 1 * walkTransitionMatrix asymAdj2 1 0) := by
  simp only [walkTransitionMatrix_apply, deg, asymAdj2, Matrix.of_apply,
    Fin.sum_univ_two]
  norm_num

end SpectralGraphTheory.QA
