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

/-! ### AdversarialFences: the adversarial fence audit
(`proposals/adversarial-fences-stationary-family.md`, 2026-09-05)

The audit method's twentieth application: a hypothesis-necessity pass
over the stationary family — 4 transitive non-QA consumers (`Mixing`,
`Oversmoothing`, `DirectedMixing`, the `EmpiricalStationary` capstone;
this run's reverse-import walk), whose 259-line QA carried one
free-form negative witness never reconciled into the fence discipline.
Thirteen hypothesis-form fences; the shelf is all-proved, so these are
theorem-instantiation fences (no `-- @refutes` tags, nothing admitted
consumed):

- **`hA`** (six statements) at the delivered `asymAdj2`: the kill
  mechanism is clean — `Pᵀ *ᵥ deg` computes *column* sums against the
  degree (row-sum) vector; detailed balance reduces to symmetry of
  `A` itself. The degree-measure fence's proof consumes the delivered
  free-form witness `asym_detailed_balance_refuted_QA`, reconciling it
  into the discipline.
- **`hd`** (the degree-measure statements: kernel, stationarity,
  balance) at the new signed canceling-zero-degree triangle
  `stNegAdj = !![0, 1, −1; 1, 0, 0; −1, 0, 0]]` — a symmetric row
  summing to zero through `+1/−1` edges: the junk `√0 = √(−1) = 0`
  collapses `degreeInvSqrt` to `diag(0, 1, 0)` (kernel kill), and the
  junk `0⁻¹ = 0` zeroes the zero-degree vertex's contribution on the
  adjoint side (stationarity and balance kills). Nonnegative
  zero-degree rows are inert; signs are what make them load-bearing.
- **`hd`** (the stationary-measure and symmetrized twins) at the
  volume-nonzero variant `stVolAdj` — the first triangle's vol `0`
  would junk-collapse both sides of the division.
- **`hd`/`hdpos`** (regular mass conservation) at the delivered
  `edgeAdj2` at the wrong claimed degree `d = 2` and at the genuinely
  `0`-regular zero matrix (the `d = 0` junk corner).
- **`hd`** (irregular mass conservation) at the zero matrix: the walk
  Laplacian of an edgeless graph is the identity, which does not kill
  constants.

Plus five proved strengthening companions: the kernel statement
*without* symmetry (P4 truth-removable — the shelf proof never consumes
`hA`), stationarity and detailed balance at `deg ≠ 0`, and both mass
conservations at `deg ≠ 0` / `d ≠ 0` (the last transferring the
random-walk audit's own `d = 0`-corner finding to its consumer).
Non-fenceable: `mulVec_one_eq_deg` carries no hypotheses. -/

section AdversarialFences

/-! #### Fixture 1: `stNegAdj = !![0, 1, −1; 1, 0, 0; −1, 0, 0]]` —
the signed canceling-zero-degree triangle (degrees `(0, 1, −1)`) -/

/-- The signed canceling-zero-degree triangle: symmetric, vertex `0`'s
row sums to zero through a `+1/−1` pair — the `hd` breaker for the
kernel, stationarity, and degree-measure balance statements. -/
def stNegAdj : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, -1; 1, 0, 0; -1, 0, 0]

theorem stNegAdj_00 : stNegAdj 0 0 = 0 := rfl
theorem stNegAdj_01 : stNegAdj 0 1 = 1 := rfl
theorem stNegAdj_02 : stNegAdj 0 2 = -1 := rfl
theorem stNegAdj_10 : stNegAdj 1 0 = 1 := rfl
theorem stNegAdj_11 : stNegAdj 1 1 = 0 := rfl
theorem stNegAdj_12 : stNegAdj 1 2 = 0 := rfl
theorem stNegAdj_20 : stNegAdj 2 0 = -1 := rfl
theorem stNegAdj_21 : stNegAdj 2 1 = 0 := rfl
theorem stNegAdj_22 : stNegAdj 2 2 = 0 := rfl

theorem stNegAdj_isSymm : stNegAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [stNegAdj_00, stNegAdj_01, stNegAdj_02, stNegAdj_10, stNegAdj_11,
      stNegAdj_12, stNegAdj_20, stNegAdj_21, stNegAdj_22]

theorem stNegAdj_deg_zero : deg stNegAdj 0 = 0 := by
  simp only [deg, Fin.sum_univ_three, stNegAdj_00, stNegAdj_01,
    stNegAdj_02]
  norm_num

theorem stNegAdj_deg_one : deg stNegAdj 1 = 1 := by
  simp only [deg, Fin.sum_univ_three, stNegAdj_10, stNegAdj_11,
    stNegAdj_12]
  norm_num

theorem stNegAdj_deg_two : deg stNegAdj 2 = -1 := by
  simp only [deg, Fin.sum_univ_three, stNegAdj_20, stNegAdj_21,
    stNegAdj_22]
  norm_num

/-- Isolation: the dropped clause genuinely fails (vertex `0`). -/
theorem stNegAdj_not_deg_pos : ¬ (∀ i, 0 < deg stNegAdj i) := by
  intro h
  have h0 := h 0
  rw [stNegAdj_deg_zero] at h0
  linarith

/-- The zero-volume pin — the reason the stationary-measure and
symmetrized twins need the variant fixture below: at vol `0` both
sides of the measure division junk-collapse. -/
theorem stNegAdj_vol : vol stNegAdj (Finset.univ : Finset (Fin 3)) = 0 := by
  rw [vol, Fin.sum_univ_three, stNegAdj_deg_zero, stNegAdj_deg_one,
    stNegAdj_deg_two]
  norm_num

/-- The junk-√ pins: `√0 = 0`, `√1 = 1`, and the junk `√(−1) = 0`. -/
theorem stNegAdj_sqrt_zero : Real.sqrt (deg stNegAdj 0) = 0 := by
  rw [stNegAdj_deg_zero]
  exact Real.sqrt_zero

theorem stNegAdj_sqrt_one : Real.sqrt (deg stNegAdj 1) = 1 := by
  rw [stNegAdj_deg_one]
  exact Real.sqrt_one

theorem stNegAdj_sqrt_two : Real.sqrt (deg stNegAdj 2) = 0 := by
  rw [stNegAdj_deg_two]
  exact Real.sqrt_eq_zero_of_nonpos (by norm_num)

/-- The junk-√ collapse: `degreeInvSqrt` degenerates to
`diag(0, 1, 0)` (`√0 = √(−1) = 0` junk, `0⁻¹ = 0` junk). -/
theorem stNegAdj_degreeInvSqrt_eq :
    degreeInvSqrt stNegAdj = Matrix.diagonal (![0, 1, 0] : Fin 3 → ℝ) := by
  ext i j
  simp only [degreeInvSqrt, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;>
    simp [stNegAdj_sqrt_zero, stNegAdj_sqrt_one, stNegAdj_sqrt_two]

/-- The congruence collapses to zero at this fixture, so the normalized
Laplacian is the identity. -/
theorem stNegAdj_TAT_eq_zero :
    degreeInvSqrt stNegAdj * stNegAdj * degreeInvSqrt stNegAdj = 0 := by
  rw [stNegAdj_degreeInvSqrt_eq]
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    simp [stNegAdj_00, stNegAdj_01, stNegAdj_02, stNegAdj_10, stNegAdj_11,
      stNegAdj_12, stNegAdj_20, stNegAdj_21, stNegAdj_22]

/-- The kernel kill: `(L_sym *ᵥ √deg) 1 = 1 ≠ 0` — the kernel vector
survives on the positive-degree vertex while the whole congruence term
is junk-zero. -/
theorem stNegAdj_normLap_kernel_entry_one :
    (normalizedLaplacian stNegAdj
      *ᵥ (fun i => Real.sqrt (deg stNegAdj i))) 1 = 1 := by
  rw [normalizedLaplacian, Matrix.sub_mulVec, stNegAdj_TAT_eq_zero,
    Matrix.zero_mulVec, sub_zero, Matrix.one_mulVec]
  simp [stNegAdj_deg_one]

/-- **Fence (`hd` clause of `normalizedLaplacian_mulVec_sqrtDeg_eq_zero`).**
Dropping positive degrees is refuted at the symmetric signed triangle:
the junk square roots collapse the congruence to zero (`L_sym = 1`)
while the kernel vector's positive-degree entry survives. -/
theorem normalizedLaplacian_mulVec_sqrtDeg_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsSymm →
        normalizedLaplacian A *ᵥ (fun i => Real.sqrt (deg A i)) = 0) := by
  intro h
  have h0 := h stNegAdj stNegAdj_isSymm
  have e1 := congrFun h0 1
  rw [stNegAdj_normLap_kernel_entry_one] at e1
  simp only [Pi.zero_apply] at e1
  norm_num at e1

/-- Every `P j 1` entry is zero at this fixture — the zero-degree
vertex's contribution `A 0 1 = 1` is junk-zeroed (`0⁻¹ = 0`) and the
other rows have genuine zero adjacency into column `1`. -/
theorem stNegAdj_P_apply_one (j : Fin 3) :
    walkTransitionMatrix stNegAdj j 1 = 0 := by
  rw [walkTransitionMatrix_apply]
  fin_cases j
  · show (deg stNegAdj 0)⁻¹ * stNegAdj 0 1 = 0
    rw [stNegAdj_deg_zero, stNegAdj_01]
    norm_num
  · show (deg stNegAdj 1)⁻¹ * stNegAdj 1 1 = 0
    rw [stNegAdj_deg_one, stNegAdj_11]
    norm_num
  · show (deg stNegAdj 2)⁻¹ * stNegAdj 2 1 = 0
    rw [stNegAdj_deg_two, stNegAdj_21]
    norm_num

/-- The stationarity kill: `(Pᵀ *ᵥ deg) 1 = 0 ≠ 1 = deg 1` — column `1`
sums to zero over the nonzero-degree rows while the genuine row sum is
`1`. -/
theorem stNegAdj_transpose_mulVec_deg_one :
    ((walkTransitionMatrix stNegAdj)ᵀ *ᵥ (deg stNegAdj)) 1 = 0 := by
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_three, stNegAdj_P_apply_one]
  norm_num

/-- **Fence (`hd` clause of `walkTransitionMatrix_transpose_mulVec_deg`).**
Dropping positive degrees is refuted at the same fixture, on the
adjoint side: the junk `0⁻¹ = 0` zeroes the zero-degree vertex's
column contribution, so the adjoint product sees column sums over
nonzero-degree rows only — `0 ≠ 1` at the vertex whose genuine degree
counts the zeroed edge. -/
theorem walkTransitionMatrix_transpose_mulVec_deg_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsSymm →
        (walkTransitionMatrix A)ᵀ *ᵥ (deg A) = deg A) := by
  intro h
  have h0 := h stNegAdj stNegAdj_isSymm
  have e1 := congrFun h0 1
  rw [stNegAdj_transpose_mulVec_deg_one, stNegAdj_deg_one] at e1
  norm_num at e1

/-- The balance kill pair `(0, 1)`: `deg 0 * P 0 1 = 0` (junk-zeroed
row factor) against `deg 1 * P 1 0 = 1` (genuine). -/
theorem stNegAdj_balance_zero_one :
    deg stNegAdj 0 * walkTransitionMatrix stNegAdj 0 1 = 0
      ∧ deg stNegAdj 1 * walkTransitionMatrix stNegAdj 1 0 = 1 := by
  constructor
  · rw [walkTransitionMatrix_apply, stNegAdj_deg_zero, stNegAdj_01]
    norm_num
  · rw [walkTransitionMatrix_apply, stNegAdj_deg_one, stNegAdj_10]
    norm_num

/-- **Fence (`hd` clause of `walk_detailed_balance`).** Dropping
positive degrees is refuted at the same fixture, pair `(0,1)`: the
zero-degree side collapses through the junk row factor while the other
side is the genuine `A 1 0 = 1`. -/
theorem walk_detailed_balance_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsSymm → ∀ i j,
        deg A i * walkTransitionMatrix A i j
          = deg A j * walkTransitionMatrix A j i) := by
  intro h
  have h0 := h stNegAdj stNegAdj_isSymm 0 1
  rw [stNegAdj_balance_zero_one.1, stNegAdj_balance_zero_one.2] at h0
  norm_num at h0

/-! #### Fixture 2: `stVolAdj = !![0, 1, −1; 1, 0, 2; −1, 2, 0]]` —
the volume-nonzero variant (degrees `(0, 3, 1)`, vol `4`) -/

/-- The volume-nonzero variant of the signed triangle: same
canceling-zero-degree vertex, but the volume is `4 ≠ 0` so the
stationary-measure division and the symmetrized-matrix statements do
not junk-collapse on both sides. -/
def stVolAdj : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1, -1; 1, 0, 2; -1, 2, 0]

theorem stVolAdj_01 : stVolAdj 0 1 = 1 := rfl
theorem stVolAdj_10 : stVolAdj 1 0 = 1 := rfl
theorem stVolAdj_12 : stVolAdj 1 2 = 2 := rfl
theorem stVolAdj_21 : stVolAdj 2 1 = 2 := rfl

theorem stVolAdj_isSymm : stVolAdj.IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [stVolAdj]

theorem stVolAdj_deg_zero : deg stVolAdj 0 = 0 := by
  simp only [deg, stVolAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem stVolAdj_deg_one : deg stVolAdj 1 = 3 := by
  simp only [deg, stVolAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem stVolAdj_deg_two : deg stVolAdj 2 = 1 := by
  simp only [deg, stVolAdj, Matrix.of_apply, Fin.sum_univ_three]
  norm_num

theorem stVolAdj_vol : vol stVolAdj (Finset.univ : Finset (Fin 3)) = 4 := by
  rw [vol, Fin.sum_univ_three, stVolAdj_deg_zero, stVolAdj_deg_one,
    stVolAdj_deg_two]
  norm_num

/-- Isolation: the dropped clause genuinely fails (vertex `0`). -/
theorem stVolAdj_not_deg_pos : ¬ (∀ i, 0 < deg stVolAdj i) := by
  intro h
  have h0 := h 0
  rw [stVolAdj_deg_zero] at h0
  linarith

/-- The kill entries at the pair `(0,1)`: `P 0 1 = 0⁻¹ · 1 = 0` (junk)
against `P 1 0 = 3⁻¹ · 1 = 1/3` (genuine). -/
theorem stVolAdj_P_01 : walkTransitionMatrix stVolAdj 0 1 = 0 := by
  rw [walkTransitionMatrix_apply, stVolAdj_deg_zero, stVolAdj_01]
  norm_num

theorem stVolAdj_P_10 : walkTransitionMatrix stVolAdj 1 0 = 1 / 3 := by
  rw [walkTransitionMatrix_apply, stVolAdj_deg_one, stVolAdj_10]
  norm_num

/-- **Fence (`hd` clause of `walk_detailed_balance_measure`).** Dropping
positive degrees is refuted at the volume-nonzero variant, pair
`(0,1)`: `0 ≠ 1/4` — the zero-degree side collapses while the other
carries `π 1 * P 1 0 = (3/4)(1/3)`. -/
theorem walk_detailed_balance_measure_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsSymm → ∀ i j,
        deg A i / vol A (Finset.univ : Finset (Fin 3))
            * walkTransitionMatrix A i j
          = deg A j / vol A (Finset.univ : Finset (Fin 3))
            * walkTransitionMatrix A j i) := by
  intro h
  have h0 := h stVolAdj stVolAdj_isSymm 0 1
  rw [stVolAdj_P_01, stVolAdj_P_10, stVolAdj_deg_zero, stVolAdj_deg_one,
    stVolAdj_vol] at h0
  norm_num at h0

/-- **Fence (`hd` clause of
`diagonal_deg_mul_walkTransitionMatrix_isSymm`).** Dropping positive
degrees is refuted at the same fixture: `(D * P) 0 1 = 0` (the
zero-degree row factor) against `(D * P) 1 0 = 3 · (1/3) = 1`. -/
theorem diagonal_deg_mul_walkTransitionMatrix_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsSymm →
        (Matrix.diagonal (deg A) * walkTransitionMatrix A).IsSymm) := by
  intro h
  have h0 := h stVolAdj stVolAdj_isSymm
  have e01 := h0.apply 0 1
  simp only [Matrix.diagonal_mul] at e01
  rw [stVolAdj_P_01, stVolAdj_P_10, stVolAdj_deg_zero, stVolAdj_deg_one]
    at e01
  norm_num at e01

/-! #### The delivered `asymAdj2` — the six `hA` fences
(degrees `(2, 1)` positive, so every kept `hd` clause is genuine) -/

theorem asymAdj2_00 : asymAdj2 0 0 = 0 := rfl
theorem asymAdj2_01 : asymAdj2 0 1 = 2 := rfl
theorem asymAdj2_10 : asymAdj2 1 0 = 1 := rfl
theorem asymAdj2_11 : asymAdj2 1 1 = 0 := rfl

theorem asymAdj2_P_00 : walkTransitionMatrix asymAdj2 0 0 = 0 := by
  rw [walkTransitionMatrix_apply, asymAdj2_deg_zero, asymAdj2_00]
  norm_num

theorem asymAdj2_P_01 : walkTransitionMatrix asymAdj2 0 1 = 1 := by
  rw [walkTransitionMatrix_apply, asymAdj2_deg_zero, asymAdj2_01]
  norm_num

theorem asymAdj2_P_10 : walkTransitionMatrix asymAdj2 1 0 = 1 := by
  rw [walkTransitionMatrix_apply, asymAdj2_deg_one, asymAdj2_10]
  norm_num

theorem asymAdj2_P_11 : walkTransitionMatrix asymAdj2 1 1 = 0 := by
  rw [walkTransitionMatrix_apply, asymAdj2_deg_one, asymAdj2_11]
  norm_num

/-- The stationarity kill at the asymmetric fixture:
`(Pᵀ *ᵥ deg) 0 = 1 ≠ 2 = deg 0` — the adjoint product computes
*column* sums `(1, 2)` against the row-sum degree vector `(2, 1)`. -/
theorem asymAdj2_transpose_mulVec_deg_zero_eq_one :
    ((walkTransitionMatrix asymAdj2)ᵀ *ᵥ (deg asymAdj2)) 0 = 1 := by
  simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.transpose_apply,
    Fin.sum_univ_two, asymAdj2_P_00, asymAdj2_P_10, asymAdj2_deg_zero,
    asymAdj2_deg_one]
  norm_num

/-- **Fence (`hA` clause of `walkTransitionMatrix_transpose_mulVec_deg`).**
Dropping symmetry is refuted at `asymAdj2` with degrees positive: the
adjoint-walk product computes column sums, which differ from the row
sums exactly on asymmetric input. -/
theorem walkTransitionMatrix_transpose_mulVec_deg_hA_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ), (∀ i, 0 < deg A i) →
        (walkTransitionMatrix A)ᵀ *ᵥ (deg A) = deg A) := by
  intro h
  have h0 := h asymAdj2 asymAdj2_deg_pos
  have e0 := congrFun h0 0
  rw [asymAdj2_transpose_mulVec_deg_zero_eq_one, asymAdj2_deg_zero] at e0
  norm_num at e0

/-- **Fence (`hA` clause of `walk_detailed_balance`) — reconciles the
delivered free-form witness.** The dropped statement is exactly the
delivered `asym_detailed_balance_refuted_QA` instance at `(0,1)`. -/
theorem walk_detailed_balance_hA_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ), (∀ i, 0 < deg A i) → ∀ i j,
        deg A i * walkTransitionMatrix A i j
          = deg A j * walkTransitionMatrix A j i) := by
  intro h
  exact asym_detailed_balance_refuted_QA (h asymAdj2 asymAdj2_deg_pos 0 1)

theorem asymAdj2_vol : vol asymAdj2 (Finset.univ : Finset (Fin 2)) = 3 := by
  rw [vol, Fin.sum_univ_two, asymAdj2_deg_zero, asymAdj2_deg_one]
  norm_num

/-- The measure-balance kill pair at `(0,1)`: `2/3` against `1/3`. -/
theorem asymAdj2_measure_sides :
    deg asymAdj2 0 / vol asymAdj2 (Finset.univ : Finset (Fin 2))
        * walkTransitionMatrix asymAdj2 0 1 = 2 / 3
      ∧ deg asymAdj2 1 / vol asymAdj2 (Finset.univ : Finset (Fin 2))
        * walkTransitionMatrix asymAdj2 1 0 = 1 / 3 := by
  rw [asymAdj2_vol, asymAdj2_P_01, asymAdj2_P_10, asymAdj2_deg_zero,
    asymAdj2_deg_one]
  norm_num

/-- **Fence (`hA` clause of `walk_detailed_balance_measure`).** Same
mechanism through the common volume division: `2/3 ≠ 1/3`. -/
theorem walk_detailed_balance_measure_hA_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ), (∀ i, 0 < deg A i) → ∀ i j,
        deg A i / vol A (Finset.univ : Finset (Fin 2))
            * walkTransitionMatrix A i j
          = deg A j / vol A (Finset.univ : Finset (Fin 2))
            * walkTransitionMatrix A j i) := by
  intro h
  have h0 := h asymAdj2 asymAdj2_deg_pos 0 1
  rw [asymAdj2_measure_sides.1, asymAdj2_measure_sides.2] at h0
  norm_num at h0

/-- **Fence (`hA` clause of
`diagonal_deg_mul_walkTransitionMatrix_isSymm`).** The matrix
packaging of the balance kill: `(D * P) 0 1 = 2 ≠ 1 = (D * P) 1 0`. -/
theorem diagonal_deg_mul_walkTransitionMatrix_hA_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ), (∀ i, 0 < deg A i) →
        (Matrix.diagonal (deg A) * walkTransitionMatrix A).IsSymm) := by
  intro h
  have h0 := h asymAdj2 asymAdj2_deg_pos
  have e01 := h0.apply 0 1
  simp only [Matrix.diagonal_mul] at e01
  rw [asymAdj2_P_10, asymAdj2_P_01, asymAdj2_deg_one, asymAdj2_deg_zero]
    at e01
  norm_num at e01

theorem asymAdj2_transitionMatrix_one_01 :
    transitionMatrix asymAdj2 1 0 1 = 2 := by
  simp only [transitionMatrix, Matrix.smul_apply, smul_eq_mul, inv_one,
    one_mul, asymAdj2]
  norm_num

theorem asymAdj2_transitionMatrix_one_10 :
    transitionMatrix asymAdj2 1 1 0 = 1 := by
  simp only [transitionMatrix, Matrix.smul_apply, smul_eq_mul, inv_one,
    one_mul, asymAdj2]
  norm_num

/-- **Fence (`hA` clause of `transitionMatrix_detailed_balance_uniform`).**
The regular cone's only hypothesis, dropped: at `d = 1` the transition
matrix is the adjacency itself and `(1/2) · 2 = 1 ≠ 1/2 = (1/2) · 1`. -/
theorem transitionMatrix_detailed_balance_uniform_hA_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ) (i j : Fin 2),
        (Fintype.card (Fin 2) : ℝ)⁻¹ * transitionMatrix A d i j
          = (Fintype.card (Fin 2) : ℝ)⁻¹ * transitionMatrix A d j i) := by
  intro h
  have h0 := h asymAdj2 1 0 1
  rw [asymAdj2_transitionMatrix_one_01, asymAdj2_transitionMatrix_one_10,
    Fintype.card_fin] at h0
  norm_num at h0

/-! #### The delivered `edgeAdj2` at the wrong claimed degree — the
regular mass-conservation `hd` fence -/

/-- Isolation: the dropped clause genuinely fails — `edgeAdj2` is
`1`-regular, not `2`-regular. -/
theorem edgeAdj2_not_two_regular : ¬ (∀ i, deg edgeAdj2 i = 2) := by
  intro h
  have h0 := h 0
  rw [edgeAdj2_deg] at h0
  norm_num at h0

/-- The kill: at the wrong claimed degree `d = 2` the walk Laplacian's
`0`-entry on constants is `1 − 2⁻¹ = 1/2 ≠ 0`. -/
theorem edgeAdj2_Lrw_two_mulVec_one_zero :
    (randomWalkLaplacian edgeAdj2 2 *ᵥ (fun _ => (1 : ℝ))) 0 = 1 / 2 := by
  simp only [randomWalkLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec,
    transitionMatrix, Matrix.smul_apply, smul_eq_mul, Matrix.mulVec,
    Matrix.dotProduct, mul_one, Fin.sum_univ_two, edgeAdj2]
  norm_num

/-- **Fence (`hd` clause of `randomWalkLaplacian_mulVec_one_eq_zero`).**
Dropping regularity is refuted at the delivered edge at the wrong
claimed degree `d = 2`, with `0 < d` genuine. -/
theorem randomWalkLaplacian_mulVec_one_eq_zero_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ), 0 < d →
        randomWalkLaplacian A d *ᵥ (fun _ => (1 : ℝ)) = 0) := by
  intro h
  have h0 := h edgeAdj2 2 two_pos
  have e0 := congrFun h0 0
  rw [edgeAdj2_Lrw_two_mulVec_one_zero] at e0
  simp only [Pi.zero_apply] at e0
  norm_num at e0

/-! #### `stZeroAdj = 0` — the genuinely `0`-regular zero matrix (the
`d = 0` junk corner and the edgeless walk Laplacian) -/

/-- The genuinely `0`-regular zero matrix on `Fin 2`. -/
def stZeroAdj : Matrix (Fin 2) (Fin 2) ℝ := 0

theorem stZeroAdj_deg (i : Fin 2) : deg stZeroAdj i = 0 := by
  simp [deg, stZeroAdj]

theorem stZeroAdj_randomWalkLaplacian_zero :
    randomWalkLaplacian stZeroAdj 0 = 1 := by
  simp [randomWalkLaplacian, transitionMatrix, stZeroAdj]

/-- **Fence (`hdpos` clause of `randomWalkLaplacian_mulVec_one_eq_zero`).**
Dropping `0 < d` is refuted at the genuinely `0`-regular zero matrix —
the same junk corner the random-walk audit found for the row-sum
theorem, here on its mass-conservation consumer: `L_rw = 1 − 0⁻¹ • 0
= 1` does not kill constants. -/
theorem randomWalkLaplacian_mulVec_one_eq_zero_hdpos_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ) (d : ℝ), (∀ i, deg A i = d) →
        randomWalkLaplacian A d *ᵥ (fun _ => (1 : ℝ)) = 0) := by
  intro h
  have h0 := h stZeroAdj 0 stZeroAdj_deg
  have e0 := congrFun h0 0
  rw [stZeroAdj_randomWalkLaplacian_zero, Matrix.one_mulVec] at e0
  simp only [Pi.zero_apply] at e0
  norm_num at e0

theorem stZeroAdj_walkLaplacian_eq_one : walkLaplacian stZeroAdj = 1 := by
  simp [walkLaplacian, walkTransitionMatrix, stZeroAdj]

/-- **Fence (`hd` clause of `walkLaplacian_mulVec_one_eq_zero`).**
Dropping positive degrees is refuted at the zero matrix — the mildest
possible fixture: the walk Laplacian of an edgeless graph is the
identity, which does not kill constants. -/
theorem walkLaplacian_mulVec_one_eq_zero_hd_fence_QA :
    ¬ (∀ (A : Matrix (Fin 2) (Fin 2) ℝ),
        walkLaplacian A *ᵥ (fun _ => (1 : ℝ)) = 0) := by
  intro h
  have h0 := h stZeroAdj
  have e0 := congrFun h0 0
  rw [stZeroAdj_walkLaplacian_eq_one, Matrix.one_mulVec] at e0
  simp only [Pi.zero_apply] at e0
  norm_num at e0

/-! #### The strengthening companions

Five proved strengthenings recording the pricing findings: the kernel
statement never needed symmetry (P4 truth-removable), and the
positivity clauses on degrees are secretly nonzeroness clauses —
the shelf proofs' own routes close with `0 < deg` weakened to
`deg ≠ 0` (and `0 < d` to `d ≠ 0` for the regular consumer,
transferring the random-walk audit's finding to this shelf). -/

/-- **Strengthening (the kernel statement, symmetry-free).** The shelf
proof of `normalizedLaplacian_mulVec_sqrtDeg_eq_zero` never consumes
`hA` — its `hA` clause is P4 truth-removable, and this companion makes
that machine-checked: the same proof (row sums plus the two
`hd`-only cancellations) closes without it. -/
theorem normalizedLaplacian_mulVec_sqrtDeg_eq_zero_of_pos_deg {V : Type}
    [Fintype V] [DecidableEq V] (A : WAdj (V := V))
    (hd : ∀ i, 0 < deg A i) :
    normalizedLaplacian A *ᵥ (fun i => Real.sqrt (deg A i)) = 0 := by
  have hT1 : degreeInvSqrt A *ᵥ (fun i => Real.sqrt (deg A i))
      = fun _ => (1 : ℝ) := by
    funext i
    have hsingle : ∀ x : V, (if i = x then (Real.sqrt (deg A i))⁻¹ else 0)
          * Real.sqrt (deg A x)
        = if i = x then (Real.sqrt (deg A i))⁻¹ * Real.sqrt (deg A x)
          else 0 := fun x => by split <;> simp
    simp only [degreeInvSqrt, Matrix.mulVec, Matrix.dotProduct,
      Matrix.diagonal_apply]
    rw [Finset.sum_congr rfl (fun x _ => hsingle x), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i), inv_mul_cancel₀
        (Real.sqrt_ne_zero'.mpr (hd i))]
  have hT2 : degreeInvSqrt A *ᵥ (fun i => deg A i)
      = fun i => Real.sqrt (deg A i) := by
    funext i
    have hsingle : ∀ x : V, (if i = x then (Real.sqrt (deg A i))⁻¹ else 0)
        * deg A x
        = if i = x then (Real.sqrt (deg A i))⁻¹ * deg A x else 0 :=
      fun x => by split <;> simp
    simp only [degreeInvSqrt, Matrix.mulVec, Matrix.dotProduct,
      Matrix.diagonal_apply]
    rw [Finset.sum_congr rfl (fun x _ => hsingle x), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i), inv_mul_eq_div,
      div_eq_iff (Real.sqrt_ne_zero'.mpr (hd i)),
      Real.mul_self_sqrt (le_of_lt (hd i))]
  have hkey : (degreeInvSqrt A * A * degreeInvSqrt A)
      *ᵥ (fun i => Real.sqrt (deg A i))
      = fun i => Real.sqrt (deg A i) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT1,
      mulVec_one_eq_deg, hT2]
  rw [normalizedLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec, hkey,
    sub_self]

/-- **Strengthening (stationarity at `deg ≠ 0`).** The shelf proof's
own route with `0 < deg` weakened to `deg ≠ 0`. -/
theorem walkTransitionMatrix_transpose_mulVec_deg_of_deg_ne_zero
    {V : Type} [Fintype V] [DecidableEq V] (A : WAdj (V := V))
    (hA : A.IsSymm) (hd : ∀ i, deg A i ≠ 0) :
    (walkTransitionMatrix A)ᵀ *ᵥ (deg A) = deg A := by
  have hT : (walkTransitionMatrix A)ᵀ
      = A * Matrix.diagonal (fun i => (deg A i)⁻¹) := by
    rw [walkTransitionMatrix, Matrix.transpose_mul,
      Matrix.diagonal_transpose, hA.eq]
  have hdinv : Matrix.diagonal (fun i => (deg A i)⁻¹) *ᵥ (deg A)
      = fun _ => (1 : ℝ) := by
    funext i
    have hsingle : ∀ x : V, (if i = x then (deg A i)⁻¹ else 0) * deg A x
        = if i = x then (deg A i)⁻¹ * deg A x else 0 :=
      fun x => by split <;> simp
    simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.diagonal_apply]
    rw [Finset.sum_congr rfl (fun x _ => hsingle x), Finset.sum_ite_eq,
      if_pos (Finset.mem_univ i), inv_mul_cancel₀ (hd i)]
  rw [hT, ← Matrix.mulVec_mulVec, hdinv, mulVec_one_eq_deg]

/-- **Strengthening (detailed balance at `deg ≠ 0`).** The shelf
proof's own route with the strictness weakened to nonzeroness. -/
theorem walk_detailed_balance_of_deg_ne_zero {V : Type} [Fintype V]
    [DecidableEq V] (A : WAdj (V := V)) (hA : A.IsSymm)
    (hd : ∀ i, deg A i ≠ 0) (i j : V) :
    deg A i * walkTransitionMatrix A i j
      = deg A j * walkTransitionMatrix A j i := by
  have hL : deg A i * ((deg A i)⁻¹ * A i j) = A i j := by
    rw [← mul_assoc, mul_inv_cancel₀ (hd i), one_mul]
  have hR : deg A j * ((deg A j)⁻¹ * A j i) = A j i := by
    rw [← mul_assoc, mul_inv_cancel₀ (hd j), one_mul]
  rw [walkTransitionMatrix_apply, walkTransitionMatrix_apply, hL, hR]
  exact hA.apply j i

/-- **Strengthening (irregular mass conservation at `deg ≠ 0`).** Direct
row-sum computation: `(L_walk *ᵥ 1) i = 1 − (deg i)⁻¹ · Σ_j A i j`. -/
theorem walkLaplacian_mulVec_one_eq_zero_of_deg_ne_zero {V : Type}
    [Fintype V] [DecidableEq V] (A : WAdj (V := V))
    (hd : ∀ i, deg A i ≠ 0) :
    walkLaplacian A *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hrow : ∀ i, ∑ j, walkTransitionMatrix A i j = 1 := by
    intro i
    simp only [walkTransitionMatrix_apply, ← Finset.mul_sum, deg]
    exact inv_mul_cancel₀ (hd i)
  have hP : walkTransitionMatrix A *ᵥ (fun _ => (1 : ℝ))
      = fun _ => (1 : ℝ) := by
    funext i
    simp only [Matrix.mulVec, Matrix.dotProduct, mul_one]
    exact hrow i
  rw [walkLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec, hP, sub_self]

/-- **Strengthening (regular mass conservation at `d ≠ 0`).** The same
`d = 0`-corner finding the random-walk audit recorded for the row-sum
theorem, transferred to its consumer here: the shelf proof's route
closes with `0 < d` weakened to `d ≠ 0`. -/
theorem randomWalkLaplacian_mulVec_one_eq_zero_of_ne_zero {V : Type}
    [Fintype V] [DecidableEq V] (A : WAdj (V := V)) (d : ℝ)
    (hd : ∀ i, deg A i = d) (hdz : d ≠ 0) :
    randomWalkLaplacian A d *ᵥ (fun _ => (1 : ℝ)) = 0 := by
  have hrow : ∀ i, ∑ j, transitionMatrix A d i j = 1 := by
    intro i
    simp only [transitionMatrix, Matrix.smul_apply, smul_eq_mul,
      ← Finset.mul_sum]
    rw [← deg, hd i, inv_mul_cancel₀ hdz]
  have hP : transitionMatrix A d *ᵥ (fun _ => (1 : ℝ))
      = fun _ => (1 : ℝ) := by
    funext i
    simp only [Matrix.mulVec, Matrix.dotProduct, mul_one]
    exact hrow i
  rw [randomWalkLaplacian, Matrix.sub_mulVec, Matrix.one_mulVec, hP,
    sub_self]

end AdversarialFences

end SpectralGraphTheory.QA
